#!/usr/bin/env python3
"""audit.py — the coverage-and-assumptions table for every paper claim, produced by Lean itself.
Copyright (C) Dave Goel 2026--now. All rights reserved.
## version 2.21 — 29 October 2026: a row whose docstring says RETIRED (proved; the paper no longer states it) is counted
##   apart, like a LEAN-ONLY HELPER; the trust note says so.
## version 2.11 — 28 October 2026: a row that assumes C13m says C13m is proved in Lean given the computer check C13c
##   (GIVEN_NOTE), not that C13m is itself a computer check; summary counts unchanged.
## version 2.01 — 28 October 2026: a stated claim X with a row `X_proved` in Statements counts as proved (it leaves the
##   not-proved table and is no assumption); a stated def that is only a row's conclusion is no assumption; full claim
##   text (no cut); box-part status as the delta review asks; C13b and C13m_hand_step are proved, C13m is GIVEN C13c.
## version 1.91 — 28 October 2026: writes the copyright line; runs from the repository root with plain `lake build`.

For every `theorem` in HVFalse/Paper/Statements.lean this script asks Lean (`#print axioms`) which axioms the proof
depends on, and classifies it:
  PROVED            only Lean's three standard axioms (propext, Classical.choice, Quot.sound)
  PROVED-FROM-CITED standard axioms plus P18.Cited.* axioms (the paper's cited results) — listed by name
  PROVED-FROM-TEXTBOOK            standard axioms plus uncited textbook facts only (P18.Cited.Textbook.*)
  PROVED-FROM-CITED-AND-TEXTBOOK  cited results AND at least one uncited textbook fact
  ... GIVEN <defs>   suffix: the statement takes a STATED, UNPROVED claim of Paper/ComputerChecked.lean (a computer check,
                     or C13m, which is proved given one) as a hypothesis — proved only given that claim; counted apart
  ... (LEAN-ONLY HELPER) suffix: a true fact Lean needs that is not a claim of the paper (docstring says so); counted apart
  PROVED-FROM-TEMP  uses a P18.Cited.Temp.* axiom: a fact the paper PROVES that Lean has not proved yet — NOT done
  OPEN              depends on sorryAx (a proof gap somewhere below it)
  VIOLATION         any other axiom (forbidden; fails loudly)
Usage: scripts/audit.py            (writes AUDIT.md, exits 1 on any VIOLATION)
       scripts/audit.py --test     (self-test of the parser)
"""
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

PROJECT = Path(__file__).resolve().parent.parent
STATEMENTS = PROJECT / "HVFalse" / "Paper" / "Statements.lean"
COMPUTER = PROJECT / "HVFalse" / "Paper" / "ComputerChecked.lean"
COMPUTER_STATUS = "NOT PROVED (computer-checked)"
BOX_STATUS = ("COMPUTER CERTIFICATE ONLY ((eq:two) at the certified values: the box checks plus the certificate's short "
              "hand arguments (i)-(iii), l.527-543, and L(p) < sec² on each cell, l.586; NOT proved in Lean)")
NUMERICAL_STATUS = "NUMERICAL ONLY (the paper says: numerical, not certified)"
GIVEN_C13C_STATUS = "NOT PROVED by itself; PROVED GIVEN C13c (row C13m_given_C13c; C13c is checked by computer)"
PROVED_SUFFIX = "_proved"  # a Statements row `X_proved : X` proves the stated claim X
SPECIAL_STATUS = {
    "C13m_explicit_violates": GIVEN_C13C_STATUS,
}
COMPUTER_GIVEN_NOTE = "NOT PROVED in Lean: a computer check"
GIVEN_NOTE = {  # a stated claim that is not itself a computer check: what a row assuming it rests on
    "C13m_explicit_violates": "proved in Lean given the computer check C13c_explicit_integral: row C13m_given_C13c",
}
AUDIT_LEAN = PROJECT / "HVFalse" / "Audit.lean"
AUDIT_MD = PROJECT / "AUDIT.md"
AUDIT_NOTES = PROJECT / "AUDIT_NOTES.md"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
NAMESPACE = "P18.Paper"
TRUST_NOTE = ("**Trust.** A row is conditional on exactly the axioms listed in its last column (PROVED rows on none). "
              "Cited results of other papers live in HVFalse/Cited/ (one file per source; each axiom's docstring quotes its "
              "source verbatim); the line above lists the ones actually used. "
              "Uncited TEXTBOOK facts would live in namespace P18.Cited.Textbook and rows using them would say TEXTBOOK; "
              "none is used (Demailly (4.24) and the instance of (5.11) the paper needs are proved in Lean). A row whose "
              "status says GIVEN <names> takes the named STATED claims of HVFalse/Paper/ComputerChecked.lean (checked by "
              "computer; NOT proved in Lean) as explicit hypotheses of its statement: Lean "
              "proves only the implication, and the summary counts these rows apart from the proved ones. A row marked "
              "LEAN-ONLY HELPER is a true fact Lean needs, not a claim of the paper; it is counted apart too. A row marked "
              "RETIRED is proved but is no longer a claim of the paper (its sentence was removed); it is counted apart too. "
              "A PROVED-FROM-TEMP row would rest on a placeholder for a fact the paper proves (namespace P18.Cited.Temp); "
              "such rows are NOT counted as proved.")
HELPER_MARK = "LEAN-ONLY HELPER"
RETIRED_MARK = "RETIRED"
SCOPE_NOTE = ("**Scope.** Every (HV) row is stated on all of L^p(T) (`HVIneqLp`, HVFalse/Defs/HVLp.lean): P₊f and P₋f "
              "are named by their Fourier coefficients (C01c: they exist; C01d: they are unique). C01b links (HV) on L^p "
              "to (HV) on trigonometric polynomials (density + the cited [HV2000] bound), so every failure is witnessed by "
              "a trigonometric polynomial. Prop. explicit (Prop. 8): z, w ∈ H^p (C13b_explicit_hardy_proved) and the hand step "
              "to 'so f violates (HV)' (C13m_hand_step_proved) are proved, so the violation rests on the computer "
              "certificate C13c alone (C13m_given_C13c).")


def parse_statements(text):
    """Return [(name, doc, signature)] for every top-level theorem, in file order (signature = text up to `:=`)."""
    items = []
    # A docstring body never contains "-/", so a private lemma's docstring cannot attach to the next public theorem.
    for block in re.finditer(r"(/--((?:(?!-/).)*)-/\s*)?^theorem\s+(\w+)(.*?):=", text, re.S | re.M):
        doc = " ".join((block.group(2) or "").split())
        items.append((block.group(3), doc, block.group(4)))
    return items


def parse_computer_checked(text):
    """Return [(name, doc_first_line)] for every `def NAME : Prop` (a stated, computer-checked, unproved claim)."""
    return [(block.group(3), " ".join((block.group(2) or "").split()))
            for block in re.finditer(r"(/--((?:(?!-/).)*)-/\s*)?^def\s+(\w+)\s*:\s*Prop", text, re.S | re.M)]


def given_defs(signature, stated_names):
    """The stated defs a row takes as hypotheses. A def that occurs only after the last `→` is the row's conclusion,
    not an assumption; in a reduction row `(h : boxes) : claim` only the box parts are assumed."""
    hypotheses = signature.rsplit("→", 1)[0] if "→" in signature else signature
    named = [d for d in stated_names if re.search(rf"\b{d}\b", hypotheses)]
    boxes = [d for d in named if d.endswith("_boxes")]
    return boxes or named


def given_kind(defs):
    """What the assumed stated claims rest on: a computer check (the hand steps of Prop. 8 are proved)."""
    assert defs, "given_kind needs at least one assumed stated claim"
    return "A COMPUTER CHECK"


def given_note(defs):
    """The parenthesis after `GIVEN <defs>`: what the assumed stated claims rest on, each distinct note once."""
    return "; ".join(dict.fromkeys(GIVEN_NOTE.get(d, COMPUTER_GIVEN_NOTE) for d in defs))


def row_status(axioms, doc, signature, stated_names):
    """(row status, summary group) of one Statements row."""
    status = classify(axioms)
    if not status.startswith("PROVED"):
        return status, status
    defs = given_defs(signature, stated_names)
    if defs:
        kind = given_kind(defs)
        return f"{status} GIVEN {', '.join(defs)} ({given_note(defs)})", f"{status} GIVEN {kind}"
    if HELPER_MARK in doc:
        return f"{status} ({HELPER_MARK}, not a paper claim)", f"{status} ({HELPER_MARK})"
    if RETIRED_MARK in doc:
        return f"{status} ({RETIRED_MARK}, not a paper claim)", f"{status} ({RETIRED_MARK})"
    return status, status


def computer_status(name):
    """A `*_boxes` def is the pure box-inequality part of a claim whose reduction to it is a PROVED row; C13m is not a
    computer claim itself (it is PROVED GIVEN the computer check C13c)."""
    if name in SPECIAL_STATUS:
        return SPECIAL_STATUS[name]
    return BOX_STATUS if name.endswith("_boxes") else COMPUTER_STATUS


def status_counts(items):
    """Counts of the stated claims by status (box parts are counted apart)."""
    return Counter(computer_status(name) for name, _ in items if not name.endswith("_boxes"))


def unproved_stated(computer, row_names):
    """The stated claims that no Statements row `X_proved` proves."""
    rows = set(row_names)
    return [(name, doc) for name, doc in computer if f"{name}{PROVED_SUFFIX}" not in rows]


def render_computer(items):
    rows = ["| # | Lean name (a `def … : Prop` in HVFalse/Paper/ComputerChecked.lean) | Paper claim | Status |", "|---|---|---|---|"]
    rows += [f"| {idx} | `{name}` | {doc.replace('|', chr(92) + '|')} | {computer_status(name)} |" for idx, (name, doc) in enumerate(items, 1)]
    return "\n".join(rows)


def write_audit_lean(names):
    lines = ["-- GENERATED by scripts/audit.py — do not edit.", "-- Copyright (C) Dave Goel 2026--now. All rights reserved.", "import HVFalse.Paper.Statements",
             "import HVFalse.Paper.ComputerChecked", ""]
    lines += [f"#print axioms {NAMESPACE}.{name}" for name in names]
    content = "\n".join(lines) + "\n"
    # Rewrite only on change: an identical rewrite leaves Lake's (content-hash) build fresh but makes the source
    # newer than its olean, and a kernel re-check that compares timestamps then refuses the run as stale.
    if not AUDIT_LEAN.exists() or AUDIT_LEAN.read_text() != content:
        AUDIT_LEAN.write_text(content)


def run_lean():
    proc = subprocess.run(["lake", "build", "HVFalse.Audit"], cwd=PROJECT, capture_output=True, text=True)
    if proc.returncode != 0:
        sys.exit("AUDIT FAILED: Lean reported an error:\n" + proc.stdout + proc.stderr)
    return proc.stdout + proc.stderr


def parse_axioms(output, names):
    """Map each theorem name to its set of axioms, from `#print axioms` output."""
    result = {}
    pattern = re.compile(r"'([\w.]+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", re.S)
    for match in pattern.finditer(output):
        full = match.group(1)
        short = full.removeprefix(NAMESPACE + ".")
        axioms = {a.strip() for a in (match.group(2) or "").replace("\n", " ").split(",") if a.strip()}
        result[short] = axioms
    missing = [n for n in names if n not in result]
    if missing:
        sys.exit(f"AUDIT FAILED: no #print axioms output for {missing}")
    return result


def classify(axioms):
    forbidden = {name for name in axioms - STANDARD - {"sorryAx"}
                 if not name.startswith("P18.Cited.")}
    if forbidden:
        return "VIOLATION"
    if "sorryAx" in axioms:
        return "OPEN"
    if any(a.startswith("P18.Cited.Temp.") for a in axioms):
        return "PROVED-FROM-TEMP"
    extra = axioms - STANDARD
    if not extra:
        return "PROVED"
    if all(a.startswith("P18.Cited.") for a in extra):
        textbook = {a for a in extra if a.startswith("P18.Cited.Textbook.")}
        if textbook == extra:
            return "PROVED-FROM-TEXTBOOK"
        if textbook:
            return "PROVED-FROM-CITED-AND-TEXTBOOK"
        return "PROVED-FROM-CITED"
    return "VIOLATION"


def render(items, axioms_by_name, stated_names):
    rows = ["| # | Lean name | Paper claim | Status | Cited axioms used |", "|---|---|---|---|---|"]
    counts = {}
    for idx, (name, doc, signature) in enumerate(items, 1):
        axioms = axioms_by_name[name]
        status, group = row_status(axioms, doc, signature, stated_names)
        counts[group] = counts.get(group, 0) + 1
        cited = ", ".join(sorted(a.removeprefix("P18.Cited.") for a in axioms if a.startswith("P18.Cited.")))
        cell = doc.replace("|", "\\|")  # absolute-value bars in docstrings must not split the Markdown table
        rows.append(f"| {idx} | `{name}` | {cell} | {status} | {cited or '—'} |")
    summary = ", ".join(f"{k}: {v}" for k, v in sorted(counts.items()))
    return summary, "\n".join(rows), counts


def used_axioms_line(axioms_by_name):
    """One line naming every non-standard axiom that some claim depends on (the whole trust surface)."""
    used = sorted({a for axioms in axioms_by_name.values() for a in axioms - STANDARD - {"sorryAx"}})
    return "**Assumptions used anywhere** (besides Lean's standard axioms): " + (", ".join(f"`{a}`" for a in used) or "none") + "."


def main_audit():
    items = parse_statements(STATEMENTS.read_text())
    names = [n for n, _, _ in items]
    write_audit_lean(names)
    axioms_by_name = parse_axioms(run_lean(), names)
    computer = unproved_stated(parse_computer_checked(COMPUTER.read_text()), names)
    summary, table, counts = render(items, axioms_by_name, [name for name, _ in computer])
    n_box = sum(1 for name, _ in computer if name.endswith("_boxes"))
    n_helper = sum(count for group, count in counts.items() if HELPER_MARK in group)
    n_retired = sum(count for group, count in counts.items() if RETIRED_MARK in group)
    summary += "".join(f", {status}: {count}" for status, count in sorted(status_counts(computer).items()))
    summary += f" (+ {n_box} box parts)"
    table += ("\n\n**Stated exactly in Lean, NOT proved in Lean** (Lean type-checks each statement; the proof is absent; "
              "the Status column says why: checked by computer, or numerical only):\n\n"
              + render_computer(computer))
    notes = AUDIT_NOTES.read_text() if AUDIT_NOTES.exists() else ""
    AUDIT_MD.write_text(f"# AUDIT — every claim of the paper, as Lean sees it\n\nCopyright (C) Dave Goel 2026--now. All rights reserved.\n\nGenerated by scripts/audit.py from "
                        f"`#print axioms`. Summary: {summary}.\n\n{used_axioms_line(axioms_by_name)}\n\n"
                        f"{TRUST_NOTE}\n\n{SCOPE_NOTE}\n\n{table}\n\n{notes}")
    print(f"AUDIT: {len(items) + len(computer) - n_box - n_helper - n_retired} paper claims (+ {n_helper} Lean-only helpers, "
          f"{n_retired} retired rows). "
          f"{summary}. Table: {AUDIT_MD}")
    if counts.get("VIOLATION"):
        sys.exit("AUDIT FAILED: a forbidden axiom appears (VIOLATION rows).")


def main_test():
    sample = ("/-- **Lemma 9.9**: hello. -/\ntheorem foo : True := trivial\ntheorem bar : True := sorry\n"
              "/-- C1. CONDITIONAL: on h. -/\ntheorem qux : True := trivial\n"
              "/-- glue -/\nprivate theorem g : True := trivial\n/-- C2. own. -/\ntheorem own : True := trivial\n")
    assert [(n, d) for n, d, _ in parse_statements(sample)] == [("foo", "**Lemma 9.9**: hello."), ("bar", ""),
                                        ("qux", "C1. CONDITIONAL: on h."), ("own", "C2. own.")], parse_statements(sample)
    assert parse_statements("theorem r (h : Paper.X_boxes) : Paper.X := h\n")[0][2] == " (h : Paper.X_boxes) : Paper.X "
    out = ("'P18.Paper.foo' depends on axioms: [propext,\n P18.Cited.x]\n"
           "'P18.Paper.bar' depends on axioms: [sorryAx]\n'P18.Paper.baz' does not depend on any axioms\n")
    got = parse_axioms(out, ["foo", "bar", "baz"])
    assert classify(got["foo"]) == "PROVED-FROM-CITED"
    assert classify(got["bar"]) == "OPEN"
    assert classify(got["baz"]) == "PROVED"
    assert classify({"propext", "evil"}) == "VIOLATION"
    assert classify({"sorryAx", "evil"}) == "VIOLATION"
    assert classify({"P18.Cited.Temp.y", "evil"}) == "VIOLATION"
    assert classify({"sorryAx", "P18.Cited.Temp.y", "evil"}) == "VIOLATION"
    assert classify({"propext", "P18.Cited.x", "P18.Cited.Temp.y"}) == "PROVED-FROM-TEMP"
    assert classify({"propext", "P18.Cited.Textbook.t", "P18.Cited.x"}) == "PROVED-FROM-CITED-AND-TEXTBOOK"
    assert classify({"propext", "P18.Cited.Textbook.t"}) == "PROVED-FROM-TEXTBOOK"
    stated = ["X_claim", "X_boxes", "C13m_explicit_violates"]
    summary, table, counts = render(
        [("red", "d", " : X_boxes → X_claim "), ("full", "d", " (h : X_claim) : True "),
         ("viol", "d", " (h : C13m_explicit_violates) : False "), ("given", "d", " : X_claim → C13m_explicit_violates "),
         ("help", "C5, LEAN-ONLY HELPER, x", " : True "), ("own", "d", " : X_claimed "),
         ("ret", "C6, RETIRED, not a claim", " : True ")],
        {n: {"propext"} for n in ["red", "full", "viol", "given", "help", "own", "ret"]}, stated)
    assert "PROVED GIVEN X_boxes (NOT PROVED in Lean: a computer check)" in table, table
    assert "PROVED GIVEN X_claim (NOT PROVED" in table, table
    assert "| `given` | d | PROVED GIVEN X_claim (NOT PROVED in Lean: a computer check) |" in table, table
    assert ("| `viol` | d | PROVED GIVEN C13m_explicit_violates (proved in Lean given the computer check "
            "C13c_explicit_integral: row C13m_given_C13c) |") in table, table
    assert given_note(["X_claim", "C13m_explicit_violates", "X_boxes"]) == (
        "NOT PROVED in Lean: a computer check; " + GIVEN_NOTE["C13m_explicit_violates"])
    assert counts == {"PROVED GIVEN A COMPUTER CHECK": 4, "PROVED (LEAN-ONLY HELPER)": 1, "PROVED": 1,
                      "PROVED (RETIRED)": 1}, counts
    assert "| `ret` | C6, RETIRED, not a claim | PROVED (RETIRED, not a paper claim) |" in table, table
    assert unproved_stated([("A", "d"), ("B", "d")], ["A_proved", "B_other"]) == [("B", "d")]
    long_doc = "/-- " + "x" * 900 + " -/\ntheorem long : True := trivial\n"
    assert len(parse_statements(long_doc)[0][1]) == 900, "the claim text must not be cut"
    _, _, counts = render([("o", "d", " : True ")], {"o": {"sorryAx"}}, stated)
    assert counts == {"OPEN": 1}, counts
    cc = parse_computer_checked("/-- C9. big. -/\ndef C9_big : Prop :=\n  True\ntheorem t : True := trivial\n")
    assert cc == [("C9_big", "C9. big.")], cc
    assert COMPUTER_STATUS in render_computer(cc)
    assert BOX_STATUS in render_computer([("X_boxes", "d")])
    assert GIVEN_C13C_STATUS in render_computer([("C13m_explicit_violates", "d")])
    counts = status_counts([("C13m_explicit_violates", "d"), ("C9_big", "d"), ("X_boxes", "d")])
    assert counts == Counter({GIVEN_C13C_STATUS: 1, COMPUTER_STATUS: 1}), counts
    line = used_axioms_line({"a": {"propext", "P18.Cited.x"}, "b": {"sorryAx", "P18.Cited.Textbook.t"}})
    assert line.endswith("`P18.Cited.Textbook.t`, `P18.Cited.x`."), line
    print("PASS: audit.py self-test")


def main():
    if sys.argv[1:] == ["--test"]:
        main_test()
    elif not sys.argv[1:]:
        main_audit()
    else:
        sys.exit("Usage: scripts/audit.py [--test]")


if __name__ == "__main__":
    main()
