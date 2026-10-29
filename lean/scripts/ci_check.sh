#!/usr/bin/env bash
# ci_check.sh - the check GitHub runs for this folder: source policy, then scripts/audit.py, then the audit's verdicts.
# Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
set -euo pipefail

# forbid WHAT RG_ARGS...: fail if rg finds a match; an rg error fails too (never a silent pass).
forbid() {
    local what=$1 status=0
    shift
    rg "$@" || status=$?
    case $status in
        0) echo "ERROR: $what (lines above)." >&2; exit 1 ;;
        1) ;;
        *) echo "ERROR: rg failed (exit $status) while checking: $what." >&2; exit 2 ;;
    esac
}

forbid "sorry or admit in a Lean source" -n -w --glob '*.lean' --glob '!.lake/**' 'sorry|admit' .
forbid "an axiom outside HVFalse/Cited/" -n --glob '*.lean' --glob '!.lake/**' --glob '!HVFalse/Cited/**' \
    '^\s*((private|protected|noncomputable)\s+)*axiom\s' .
python3 scripts/audit.py
forbid "an OPEN, VIOLATION or PROVED-FROM-TEMP row in AUDIT.md" -n '[|] (OPEN|VIOLATION|PROVED-FROM-TEMP)( [^|]*)? [|]' AUDIT.md
