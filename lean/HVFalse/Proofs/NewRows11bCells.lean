/-
  HVFalse/Proofs/NewRows11bCells.lean - GENERATED certificates for U13 (Remark after Prop. 11, "16%")
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  pt_k: rational enclosure of Ssec at the cell end p_k = cellLeft k (k = 0..140), by NewRows11.Ssec_encl.
  cell_i: 16/100 · W(p_a) ≤ cellLevel i - 2e-6 - p_a/(p_a-1) with W(p) = Ssec p - p/(p-1), p_a = cellLeft i (i < 140).
  Do not edit by hand: re-run the script.
-/
import HVFalse.Proofs.NewRows11

open Real

namespace P18

namespace NewRows11bCells

/-- One cell: lower bound of the level through `Ssec p_b ≥ Slo`, upper bound of `Ssec p_a ≤ Shi`. -/
theorem cell_of_bounds {i : ℕ} {pl pr κ Slo Shi : ℝ} (hl : cellLeft i = pl) (hr : cellRight i = pr)
    (hk : cellKappa i = κ) (hκ : 0 ≤ κ) (hSr : Slo ≤ Ssec pr) (hSl : Ssec pl ≤ Shi)
    (hfin : 16 / 100 * (Shi - pl / (pl - 1)) ≤ pr / (pr - 1) + κ * (Slo - pr / (pr - 1)) - 2 / 10 ^ 6 - pl / (pl - 1)) :
    16 / 100 * (Ssec (cellLeft i) - cellLeft i / (cellLeft i - 1)) ≤
      cellLevel i - 2 / 10 ^ 6 - cellLeft i / (cellLeft i - 1) := by
  unfold cellLevel
  rw [hl, hr, hk]
  nlinarith [mul_le_mul_of_nonneg_left hSr hκ]

theorem pt_0 : 1 / (19134171619 / 50000000000 : ℝ) ^ 2 ≤ Ssec (4 / 3 : ℝ) ∧ Ssec (4 / 3 : ℝ) ≤ 1 / (7653668647 / 20000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (117809724509 / 100000000000 : ℝ)) (θhi := (11780972451 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_1 : 1 / (19336119527 / 50000000000 : ℝ) ^ 2 ≤ Ssec (4577 / 3420 : ℝ) ∧ Ssec (4577 / 3420 : ℝ) ≤ 1 / (9668059763 / 25000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (117372152887 / 100000000000 : ℝ)) (θhi := (14671519111 / 12500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_2 : 1 / (19536206711 / 50000000000 : ℝ) ^ 2 ≤ Ssec (2297 / 1710 : ℝ) ∧ Ssec (2297 / 1710 : ℝ) ≤ 1 / (1953620671 / 5000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (116937819713 / 100000000000 : ℝ)) (θhi := (58468909857 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_3 : 1 / (4933613513 / 12500000000 : ℝ) ^ 2 ≤ Ssec (1537 / 1140 : ℝ) ∧ Ssec (1537 / 1140 : ℝ) ≤ 1 / (19734454051 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (11650668917 / 10000000000 : ℝ)) (θhi := (116506689171 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_4 : 1 / (7972352873 / 20000000000 : ℝ) ^ 2 ≤ Ssec (1157 / 855 : ℝ) ∧ Ssec (1157 / 855 : ℝ) ≤ 1 / (39861764363 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (29019681491 / 25000000000 : ℝ)) (θhi := (23215745193 / 20000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_5 : 1 / (40251022973 / 100000000000 : ℝ) ^ 2 ≤ Ssec (929 / 684 : ℝ) ∧ Ssec (929 / 684 : ℝ) ≤ 1 / (40251022971 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (2891347383 / 2500000000 : ℝ)) (θhi := (115653895321 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_6 : 1 / (20318362103 / 50000000000 : ℝ) ^ 2 ≤ Ssec (259 / 190 : ℝ) ∧ Ssec (259 / 190 : ℝ) ≤ 1 / (10159181051 / 25000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (115232162969 / 100000000000 : ℝ)) (θhi := (11523216297 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_7 : 1 / (41018907857 / 100000000000 : ℝ) ^ 2 ≤ Ssec (4679 / 3420 : ℝ) ∧ Ssec (4679 / 3420 : ℝ) ≤ 1 / (8203781571 / 20000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (5740674757 / 5000000000 : ℝ)) (θhi := (114813495141 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_8 : 1 / (8279522647 / 20000000000 : ℝ) ^ 2 ≤ Ssec (1174 / 855 : ℝ) ∧ Ssec (1174 / 855 : ℝ) ≤ 1 / (41397613233 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (14299732319 / 12500000000 : ℝ)) (θhi := (114397858553 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_9 : 1 / (41772879177 / 100000000000 : ℝ) ^ 2 ≤ Ssec (1571 / 1140 : ℝ) ∧ Ssec (1571 / 1140 : ℝ) ≤ 1 / (1670915167 / 4000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (113985220403 / 100000000000 : ℝ)) (θhi := (28496305101 / 25000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_10 : 1 / (8428948809 / 20000000000 : ℝ) ^ 2 ≤ Ssec (473 / 342 : ℝ) ∧ Ssec (473 / 342 : ℝ) ≤ 1 / (42144744043 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (28393887091 / 25000000000 : ℝ)) (θhi := (22715109673 / 20000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_11 : 1 / (42513245739 / 100000000000 : ℝ) ^ 2 ≤ Ssec (4747 / 3420 : ℝ) ∧ Ssec (4747 / 3420 : ℝ) ≤ 1 / (42513245737 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (113168810567 / 100000000000 : ℝ)) (θhi := (14146101321 / 12500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_12 : 1 / (42878421693 / 100000000000 : ℝ) ^ 2 ≤ Ssec (397 / 285 : ℝ) ∧ Ssec (397 / 285 : ℝ) ≤ 1 / (42878421691 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (112764975601 / 100000000000 : ℝ)) (θhi := (56382487801 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_13 : 1 / (43240308889 / 100000000000 : ℝ) ^ 2 ≤ Ssec (4781 / 3420 : ℝ) ∧ Ssec (4781 / 3420 : ℝ) ≤ 1 / (43240308887 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (8989121 / 8000000 : ℝ)) (θhi := (112364012501 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_14 : 1 / (8719788771 / 20000000000 : ℝ) ^ 2 ≤ Ssec (2399 / 1710 : ℝ) ∧ Ssec (2399 / 1710 : ℝ) ≤ 1 / (43598943853 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (55982945369 / 50000000000 : ℝ)) (θhi := (111965890739 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_15 : 1 / (43954362673 / 100000000000 : ℝ) ^ 2 ≤ Ssec (107 / 76 : ℝ) ∧ Ssec (107 / 76 : ℝ) ≤ 1 / (43954362671 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (5578529011 / 5000000000 : ℝ)) (θhi := (111570580221 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_16 : 1 / (22153300491 / 50000000000 : ℝ) ^ 2 ≤ Ssec (1208 / 855 : ℝ) ∧ Ssec (1208 / 855 : ℝ) ≤ 1 / (2215330049 / 5000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (4447122051 / 4000000000 : ℝ)) (θhi := (27794512819 / 25000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_17 : 1 / (11163923497 / 25000000000 : ℝ) ^ 2 ≤ Ssec (4849 / 3420 : ℝ) ∧ Ssec (4849 / 3420 : ℝ) ≤ 1 / (22327846993 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (110788274647 / 100000000000 : ℝ)) (θhi := (13848534331 / 12500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_18 : 1 / (45001676463 / 100000000000 : ℝ) ^ 2 ≤ Ssec (811 / 570 : ℝ) ∧ Ssec (811 / 570 : ℝ) ≤ 1 / (45001676461 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (6900076343 / 6250000000 : ℝ)) (θhi := (110401221489 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_19 : 1 / (1417018211 / 3125000000 : ℝ) ^ 2 ≤ Ssec (257 / 180 : ℝ) ∧ Ssec (257 / 180 : ℝ) ≤ 1 / (181378331 / 400000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (22003372671 / 20000000000 : ℝ)) (θhi := (27504215839 / 25000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_20 : 1 / (2284222339 / 5000000000 : ℝ) ^ 2 ≤ Ssec (245 / 171 : ℝ) ∧ Ssec (245 / 171 : ℝ) ≤ 1 / (22842223389 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (27408793049 / 25000000000 : ℝ)) (θhi := (109635172197 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_21 : 1 / (46021302051 / 100000000000 : ℝ) ^ 2 ≤ Ssec (1639 / 1140 : ℝ) ∧ Ssec (1639 / 1140 : ℝ) ≤ 1 / (46021302049 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (2185122407 / 2000000000 : ℝ)) (θhi := (109256120351 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_22 : 1 / (23177590831 / 50000000000 : ℝ) ^ 2 ≤ Ssec (2467 / 1710 : ℝ) ∧ Ssec (2467 / 1710 : ℝ) ≤ 1 / (2317759083 / 5000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (21775936107 / 20000000000 : ℝ)) (θhi := (13609960067 / 12500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_23 : 1 / (23343059149 / 50000000000 : ℝ) ^ 2 ≤ Ssec (4951 / 3420 : ℝ) ∧ Ssec (4951 / 3420 : ℝ) ≤ 1 / (5835764787 / 12500000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (54252912923 / 50000000000 : ℝ)) (θhi := (108505825847 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_24 : 1 / (9402828849 / 20000000000 : ℝ) ^ 2 ≤ Ssec (138 / 95 : ℝ) ∧ Ssec (138 / 95 : ℝ) ≤ 1 / (11753536061 / 25000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (108134529743 / 100000000000 : ℝ)) (θhi := (6758408109 / 6250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_25 : 1 / (47339291391 / 100000000000 : ℝ) ^ 2 ≤ Ssec (997 / 684 : ℝ) ∧ Ssec (997 / 684 : ℝ) ≤ 1 / (4733929139 / 10000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (2155315321 / 2000000000 : ℝ)) (θhi := (107765766051 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_26 : 1 / (11915397807 / 25000000000 : ℝ) ^ 2 ≤ Ssec (2501 / 1710 : ℝ) ∧ Ssec (2501 / 1710 : ℝ) ≤ 1 / (23830795613 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (107399508949 / 100000000000 : ℝ)) (θhi := (2147990179 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_27 : 1 / (23990537431 / 50000000000 : ℝ) ^ 2 ≤ Ssec (1673 / 1140 : ℝ) ∧ Ssec (1673 / 1140 : ℝ) ≤ 1 / (2399053743 / 5000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (107035732967 / 100000000000 : ℝ)) (θhi := (13379466621 / 12500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_28 : 1 / (6037221627 / 12500000000 : ℝ) ^ 2 ≤ Ssec (1259 / 855 : ℝ) ∧ Ssec (1259 / 855 : ℝ) ≤ 1 / (24148886507 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (106674412979 / 100000000000 : ℝ)) (θhi := (5333720649 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_29 : 1 / (759558063 / 1562500000 : ℝ) ^ 2 ≤ Ssec (5053 / 3420 : ℝ) ∧ Ssec (5053 / 3420 : ℝ) ≤ 1 / (4861171603 / 10000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (26578881049 / 25000000000 : ℝ)) (θhi := (106315524197 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_30 : 1 / (1223073347 / 2500000000 : ℝ) ^ 2 ≤ Ssec (169 / 114 : ℝ) ∧ Ssec (169 / 114 : ℝ) ≤ 1 / (24461466939 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (52979521081 / 50000000000 : ℝ)) (θhi := (105959042163 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_31 : 1 / (24615728079 / 50000000000 : ℝ) ^ 2 ≤ Ssec (5087 / 3420 : ℝ) ∧ Ssec (5087 / 3420 : ℝ) ≤ 1 / (12307864039 / 25000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (26401235687 / 25000000000 : ℝ)) (θhi := (105604942749 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_32 : 1 / (49537312101 / 100000000000 : ℝ) ^ 2 ≤ Ssec (1276 / 855 : ℝ) ∧ Ssec (1276 / 855 : ℝ) ≤ 1 / (49537312099 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (26313300537 / 25000000000 : ℝ)) (θhi := (105253202149 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_33 : 1 / (49840530583 / 100000000000 : ℝ) ^ 2 ≤ Ssec (569 / 380 : ℝ) ∧ Ssec (569 / 380 : ℝ) ≤ 1 / (49840530581 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (26225949217 / 25000000000 : ℝ)) (θhi := (104903796869 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_34 : 1 / (1253528503 / 2500000000 : ℝ) ^ 2 ≤ Ssec (2569 / 1710 : ℝ) ∧ Ssec (2569 / 1710 : ℝ) ≤ 1 / (25070570059 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (104556703729 / 100000000000 : ℝ)) (θhi := (10455670373 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_35 : 1 / (25219584439 / 50000000000 : ℝ) ^ 2 ≤ Ssec (1031 / 684 : ℝ) ∧ Ssec (1031 / 684 : ℝ) ≤ 1 / (12609792219 / 25000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (104211899857 / 100000000000 : ℝ)) (θhi := (52105949929 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_36 : 1 / (12683661169 / 25000000000 : ℝ) ^ 2 ≤ Ssec (431 / 285 : ℝ) ∧ Ssec (431 / 285 : ℝ) ≤ 1 / (25367322337 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (25967340669 / 25000000000 : ℝ)) (θhi := (103869362677 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_37 : 1 / (51027594989 / 100000000000 : ℝ) ^ 2 ≤ Ssec (5189 / 3420 : ℝ) ∧ Ssec (5189 / 3420 : ℝ) ≤ 1 / (51027594987 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (10352906991 / 10000000000 : ℝ)) (θhi := (103529069911 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_38 : 1 / (25659023477 / 50000000000 : ℝ) ^ 2 ≤ Ssec (137 / 90 : ℝ) ∧ Ssec (137 / 90 : ℝ) ≤ 1 / (6414755869 / 12500000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (10319099957 / 10000000000 : ℝ)) (θhi := (103190999571 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_39 : 1 / (51606027373 / 100000000000 : ℝ) ^ 2 ≤ Ssec (1741 / 1140 : ℝ) ∧ Ssec (1741 / 1140 : ℝ) ≤ 1 / (51606027371 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (25713782489 / 25000000000 : ℝ)) (θhi := (102855129957 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_40 : 1 / (51891562719 / 100000000000 : ℝ) ^ 2 ≤ Ssec (262 / 171 : ℝ) ∧ Ssec (262 / 171 : ℝ) ≤ 1 / (51891562717 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (102521439649 / 100000000000 : ℝ)) (θhi := (2050428793 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_41 : 1 / (26087339569 / 50000000000 : ℝ) ^ 2 ≤ Ssec (5257 / 3420 : ℝ) ∧ Ssec (5257 / 3420 : ℝ) ≤ 1 / (1630458723 / 3125000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (51094953753 / 50000000000 : ℝ)) (θhi := (102189907507 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_42 : 1 / (26227701227 / 50000000000 : ℝ) ^ 2 ≤ Ssec (293 / 190 : ℝ) ∧ Ssec (293 / 190 : ℝ) ≤ 1 / (52455402453 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (101860512659 / 100000000000 : ℝ)) (θhi := (5093025633 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_43 : 1 / (52733758177 / 100000000000 : ℝ) ^ 2 ≤ Ssec (5291 / 3420 : ℝ) ∧ Ssec (5291 / 3420 : ℝ) ≤ 1 / (2109350327 / 4000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (12691654313 / 12500000000 : ℝ)) (θhi := (20306646901 / 20000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_44 : 1 / (26504885749 / 50000000000 : ℝ) ^ 2 ≤ Ssec (1327 / 855 : ℝ) ∧ Ssec (1327 / 855 : ℝ) ≤ 1 / (6626221437 / 12500000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (50604026353 / 50000000000 : ℝ)) (θhi := (101208052707 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_45 : 1 / (26641733651 / 50000000000 : ℝ) ^ 2 ≤ Ssec (355 / 228 : ℝ) ∧ Ssec (355 / 228 : ℝ) ≤ 1 / (53283467301 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (20176989437 / 20000000000 : ℝ)) (θhi := (50442473593 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_46 : 1 / (6694358771 / 12500000000 : ℝ) ^ 2 ≤ Ssec (2671 / 1710 : ℝ) ∧ Ssec (2671 / 1710 : ℝ) ≤ 1 / (26777435083 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (100563898121 / 100000000000 : ℝ)) (θhi := (50281949061 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_47 : 1 / (53824004371 / 100000000000 : ℝ) ^ 2 ≤ Ssec (5359 / 3420 : ℝ) ∧ Ssec (5359 / 3420 : ℝ) ≤ 1 / (53824004369 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (50122442971 / 50000000000 : ℝ)) (θhi := (100244885943 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_48 : 1 / (54090893893 / 100000000000 : ℝ) ^ 2 ≤ Ssec (448 / 285 : ℝ) ∧ Ssec (448 / 285 : ℝ) ≤ 1 / (54090893891 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (3997115653 / 4000000000 : ℝ)) (θhi := (49963945663 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_49 : 1 / (27177781209 / 50000000000 : ℝ) ^ 2 ≤ Ssec (5393 / 3420 : ℝ) ∧ Ssec (5393 / 3420 : ℝ) ≤ 1 / (3397222651 / 6250000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (9961289519 / 10000000000 : ℝ)) (θhi := (99612895191 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_50 : 1 / (54618033341 / 100000000000 : ℝ) ^ 2 ≤ Ssec (541 / 342 : ℝ) ∧ Ssec (541 / 342 : ℝ) ≤ 1 / (54618033339 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (99299878699 / 100000000000 : ℝ)) (θhi := (992998787 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_51 : 1 / (13719582443 / 25000000000 : ℝ) ^ 2 ≤ Ssec (603 / 380 : ℝ) ∧ Ssec (603 / 380 : ℝ) ≤ 1 / (5487832977 / 10000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (98988823247 / 100000000000 : ℝ)) (θhi := (6186801453 / 6250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_52 : 1 / (55136474537 / 100000000000 : ℝ) ^ 2 ≤ Ssec (1361 / 855 : ℝ) ∧ Ssec (1361 / 855 : ℝ) ≤ 1 / (11027294907 / 20000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (98679710463 / 100000000000 : ℝ)) (θhi := (385467619 / 390625000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_53 : 1 / (6924061273 / 12500000000 : ℝ) ^ 2 ≤ Ssec (5461 / 3420 : ℝ) ∧ Ssec (5461 / 3420 : ℝ) ≤ 1 / (27696245091 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (19674504441 / 20000000000 : ℝ)) (θhi := (49186261103 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_54 : 1 / (11129279797 / 20000000000 : ℝ) ^ 2 ≤ Ssec (913 / 570 : ℝ) ∧ Ssec (913 / 570 : ℝ) ≤ 1 / (55646398983 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (19613448111 / 20000000000 : ℝ)) (θhi := (24516810139 / 25000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_55 : 1 / (55898222941 / 100000000000 : ℝ) ^ 2 ≤ Ssec (1099 / 684 : ℝ) ∧ Ssec (1099 / 684 : ℝ) ≤ 1 / (55898222939 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (48881923909 / 50000000000 : ℝ)) (θhi := (97763847819 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_56 : 1 / (11229596757 / 20000000000 : ℝ) ^ 2 ≤ Ssec (1378 / 855 : ℝ) ∧ Ssec (1378 / 855 : ℝ) ≤ 1 / (7018497973 / 12500000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (97462326517 / 100000000000 : ℝ)) (θhi := (48731163259 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_57 : 1 / (28197851493 / 50000000000 : ℝ) ^ 2 ≤ Ssec (97 / 60 : ℝ) ∧ Ssec (97 / 60 : ℝ) ≤ 1 / (7049462873 / 12500000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (97162659389 / 100000000000 : ℝ)) (θhi := (9716265939 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_58 : 1 / (56641401749 / 100000000000 : ℝ) ^ 2 ≤ Ssec (2773 / 1710 : ℝ) ∧ Ssec (2773 / 1710 : ℝ) ≤ 1 / (14160350437 / 25000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (12108103673 / 12500000000 : ℝ)) (θhi := (19372965877 / 20000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_59 : 1 / (28442550513 / 50000000000 : ℝ) ^ 2 ≤ Ssec (5563 / 3420 : ℝ) ∧ Ssec (5563 / 3420 : ℝ) ≤ 1 / (1777659407 / 3125000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (96568819659 / 100000000000 : ℝ)) (θhi := (4828440983 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_60 : 1 / (57126821511 / 100000000000 : ℝ) ^ 2 ≤ Ssec (31 / 19 : ℝ) ∧ Ssec (31 / 19 : ℝ) ≤ 1 / (57126821509 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (96274613577 / 100000000000 : ℝ)) (θhi := (48137306789 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_61 : 1 / (57366583647 / 100000000000 : ℝ) ^ 2 ≤ Ssec (5597 / 3420 : ℝ) ∧ Ssec (5597 / 3420 : ℝ) ≤ 1 / (11473316729 / 20000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (5998887169 / 6250000000 : ℝ)) (θhi := (19196438941 / 20000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_62 : 1 / (57604407631 / 100000000000 : ℝ) ^ 2 ≤ Ssec (2807 / 1710 : ℝ) ∧ Ssec (2807 / 1710 : ℝ) ≤ 1 / (57604407629 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (19138309361 / 20000000000 : ℝ)) (θhi := (47845773403 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_63 : 1 / (7230039177 / 12500000000 : ℝ) ^ 2 ≤ Ssec (1877 / 1140 : ℝ) ∧ Ssec (1877 / 1140 : ℝ) ≤ 1 / (28920156707 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (47701326919 / 50000000000 : ℝ)) (θhi := (95402653839 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_64 : 1 / (7259290089 / 12500000000 : ℝ) ^ 2 ≤ Ssec (1412 / 855 : ℝ) ∧ Ssec (1412 / 855 : ℝ) ≤ 1 / (5807432071 / 10000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (47557749979 / 50000000000 : ℝ)) (θhi := (95115499959 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_65 : 1 / (58306448993 / 100000000000 : ℝ) ^ 2 ≤ Ssec (1133 / 684 : ℝ) ∧ Ssec (1133 / 684 : ℝ) ≤ 1 / (58306448991 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (23707517377 / 25000000000 : ℝ)) (θhi := (94830069509 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_66 : 1 / (7317089687 / 12500000000 : ℝ) ^ 2 ≤ Ssec (947 / 570 : ℝ) ∧ Ssec (947 / 570 : ℝ) ≤ 1 / (29268358747 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (94546347019 / 100000000000 : ℝ)) (θhi := (4727317351 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_67 : 1 / (58765145227 / 100000000000 : ℝ) ^ 2 ≤ Ssec (5699 / 3420 : ℝ) ∧ Ssec (5699 / 3420 : ℝ) ≤ 1 / (2350605809 / 4000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (94264317207 / 100000000000 : ℝ)) (θhi := (11783039651 / 12500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_68 : 1 / (14747937741 / 25000000000 : ℝ) ^ 2 ≤ Ssec (1429 / 855 : ℝ) ∧ Ssec (1429 / 855 : ℝ) ≤ 1 / (58991750963 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (93983964969 / 100000000000 : ℝ)) (θhi := (9398396497 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_69 : 1 / (2960827663 / 5000000000 : ℝ) ^ 2 ≤ Ssec (637 / 380 : ℝ) ∧ Ssec (637 / 380 : ℝ) ≤ 1 / (29608276629 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (93705275381 / 100000000000 : ℝ)) (θhi := (46852637691 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_70 : 1 / (59439570441 / 100000000000 : ℝ) ^ 2 ≤ Ssec (575 / 342 : ℝ) ∧ Ssec (575 / 342 : ℝ) ≤ 1 / (1485989261 / 2500000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (46714116849 / 50000000000 : ℝ)) (θhi := (93428233699 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_71 : 1 / (2983041031 / 5000000000 : ℝ) ^ 2 ≤ Ssec (5767 / 3420 : ℝ) ∧ Ssec (5767 / 3420 : ℝ) ≤ 1 / (29830410309 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (45484778 / 48828125 : ℝ)) (θhi := (18630565069 / 20000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_72 : 1 / (29940160843 / 50000000000 : ℝ) ^ 2 ≤ Ssec (482 / 285 : ℝ) ∧ Ssec (482 / 285 : ℝ) ≤ 1 / (14970080421 / 25000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (1160987949 / 1250000000 : ℝ)) (θhi := (92879035921 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_73 : 1 / (60098091319 / 100000000000 : ℝ) ^ 2 ≤ Ssec (5801 / 3420 : ℝ) ∧ Ssec (5801 / 3420 : ℝ) ≤ 1 / (60098091317 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (92606851191 / 100000000000 : ℝ)) (θhi := (11575856399 / 12500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_74 : 1 / (12062829397 / 20000000000 : ℝ) ^ 2 ≤ Ssec (2909 / 1710 : ℝ) ∧ Ssec (2909 / 1710 : ℝ) ≤ 1 / (60314146983 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (23084064273 / 25000000000 : ℝ)) (θhi := (92336257093 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_75 : 1 / (7566063243 / 12500000000 : ℝ) ^ 2 ≤ Ssec (389 / 228 : ℝ) ∧ Ssec (389 / 228 : ℝ) ≤ 1 / (60528505943 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (92067239719 / 100000000000 : ℝ)) (θhi := (2301680993 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_76 : 1 / (1898162039 / 3125000000 : ℝ) ^ 2 ≤ Ssec (77 / 45 : ℝ) ∧ Ssec (77 / 45 : ℝ) ≤ 1 / (60741185247 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (22949946333 / 25000000000 : ℝ)) (θhi := (91799785333 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_77 : 1 / (15238050437 / 25000000000 : ℝ) ^ 2 ≤ Ssec (5869 / 3420 : ℝ) ∧ Ssec (5869 / 3420 : ℝ) ≤ 1 / (30476100873 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (22883470087 / 25000000000 : ℝ)) (θhi := (91533880349 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_78 : 1 / (61161572093 / 100000000000 : ℝ) ^ 2 ≤ Ssec (327 / 190 : ℝ) ∧ Ssec (327 / 190 : ℝ) ≤ 1 / (15290393023 / 25000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (45634755671 / 50000000000 : ℝ)) (θhi := (91269511343 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_79 : 1 / (12273862547 / 20000000000 : ℝ) ^ 2 ≤ Ssec (5903 / 3420 : ℝ) ∧ Ssec (5903 / 3420 : ℝ) ≤ 1 / (61369312733 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (18201333009 / 20000000000 : ℝ)) (θhi := (45503332523 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_80 : 1 / (61575439931 / 100000000000 : ℝ) ^ 2 ≤ Ssec (296 / 171 : ℝ) ∧ Ssec (296 / 171 : ℝ) ≤ 1 / (61575439929 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (45372664169 / 50000000000 : ℝ)) (θhi := (90745328339 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_81 : 1 / (30889984873 / 50000000000 : ℝ) ^ 2 ≤ Ssec (1979 / 1140 : ℝ) ∧ Ssec (1979 / 1140 : ℝ) ≤ 1 / (3861248109 / 6250000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (90485488253 / 100000000000 : ℝ)) (θhi := (45242744127 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_82 : 1 / (30991459027 / 50000000000 : ℝ) ^ 2 ≤ Ssec (2977 / 1710 : ℝ) ∧ Ssec (2977 / 1710 : ℝ) ≤ 1 / (15495729513 / 25000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (22556782993 / 25000000000 : ℝ)) (θhi := (90227131973 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_83 : 1 / (31092150271 / 50000000000 : ℝ) ^ 2 ≤ Ssec (5971 / 3420 : ℝ) ∧ Ssec (5971 / 3420 : ℝ) ≤ 1 / (62184300541 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (4498512341 / 5000000000 : ℝ)) (θhi := (89970246821 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_84 : 1 / (31192066357 / 50000000000 : ℝ) ^ 2 ≤ Ssec (499 / 285 : ℝ) ∧ Ssec (499 / 285 : ℝ) ≤ 1 / (7798016589 / 12500000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (89714820267 / 100000000000 : ℝ)) (θhi := (22428705067 / 25000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_85 : 1 / (62582429887 / 100000000000 : ℝ) ^ 2 ≤ Ssec (1201 / 684 : ℝ) ∧ Ssec (1201 / 684 : ℝ) ≤ 1 / (12516485977 / 20000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (89460839927 / 100000000000 : ℝ)) (θhi := (11182604991 / 12500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_86 : 1 / (62779207203 / 100000000000 : ℝ) ^ 2 ≤ Ssec (3011 / 1710 : ℝ) ∧ Ssec (3011 / 1710 : ℝ) ≤ 1 / (62779207201 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (1784165871 / 2000000000 : ℝ)) (θhi := (89208293551 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_87 : 1 / (31487239811 / 50000000000 : ℝ) ^ 2 ≤ Ssec (671 / 380 : ℝ) ∧ Ssec (671 / 380 : ℝ) ≤ 1 / (3148723981 / 5000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (22239292257 / 25000000000 : ℝ)) (θhi := (88957169029 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_88 : 1 / (63168261931 / 100000000000 : ℝ) ^ 2 ≤ Ssec (1514 / 855 : ℝ) ∧ Ssec (1514 / 855 : ℝ) ≤ 1 / (63168261929 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (44353727193 / 50000000000 : ℝ)) (θhi := (88707454387 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_89 : 1 / (63360568743 / 100000000000 : ℝ) ^ 2 ≤ Ssec (6073 / 3420 : ℝ) ∧ Ssec (6073 / 3420 : ℝ) ≤ 1 / (63360568741 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (11057392223 / 12500000000 : ℝ)) (θhi := (17691827557 / 20000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_90 : 1 / (63551414501 / 100000000000 : ℝ) ^ 2 ≤ Ssec (203 / 114 : ℝ) ∧ Ssec (203 / 114 : ℝ) ≤ 1 / (63551414499 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (44106103757 / 50000000000 : ℝ)) (θhi := (17642441503 / 20000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_91 : 1 / (31870406739 / 50000000000 : ℝ) ^ 2 ≤ Ssec (6107 / 3420 : ℝ) ∧ Ssec (6107 / 3420 : ℝ) ≤ 1 / (15935203369 / 25000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (87966651999 / 100000000000 : ℝ)) (θhi := (21991663 / 25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_92 : 1 / (63928779781 / 100000000000 : ℝ) ^ 2 ≤ Ssec (1531 / 855 : ℝ) ∧ Ssec (1531 / 855 : ℝ) ≤ 1 / (63928779779 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (87722459791 / 100000000000 : ℝ)) (θhi := (5482653737 / 6250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_93 : 1 / (32057663677 / 50000000000 : ℝ) ^ 2 ≤ Ssec (2047 / 1140 : ℝ) ∧ Ssec (2047 / 1140 : ℝ) ≤ 1 / (64115327353 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (87479619567 / 100000000000 : ℝ)) (θhi := (5467476223 / 6250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_94 : 1 / (64300469979 / 100000000000 : ℝ) ^ 2 ≤ Ssec (3079 / 1710 : ℝ) ∧ Ssec (3079 / 1710 : ℝ) ≤ 1 / (64300469977 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (8723812013 / 10000000000 : ℝ)) (θhi := (87238120131 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_95 : 1 / (32242110637 / 50000000000 : ℝ) ^ 2 ≤ Ssec (65 / 36 : ℝ) ∧ Ssec (65 / 36 : ℝ) ≤ 1 / (8060527659 / 12500000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (86997950407 / 100000000000 : ℝ)) (θhi := (10874743801 / 12500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_96 : 1 / (12933318941 / 20000000000 : ℝ) ^ 2 ≤ Ssec (172 / 95 : ℝ) ∧ Ssec (172 / 95 : ℝ) ≤ 1 / (4041662169 / 6250000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (17351819889 / 20000000000 : ℝ)) (θhi := (43379549723 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_97 : 1 / (64847603579 / 100000000000 : ℝ) ^ 2 ≤ Ssec (6209 / 3420 : ℝ) ∧ Ssec (6209 / 3420 : ℝ) ≤ 1 / (64847603577 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (21630389103 / 25000000000 : ℝ)) (θhi := (86521556413 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_98 : 1 / (1300545221 / 2000000000 : ℝ) ^ 2 ≤ Ssec (3113 / 1710 : ℝ) ∧ Ssec (3113 / 1710 : ℝ) ≤ 1 / (8128407631 / 12500000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (43142655297 / 50000000000 : ℝ)) (θhi := (17257062119 / 20000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_99 : 1 / (32602790059 / 50000000000 : ℝ) ^ 2 ≤ Ssec (2081 / 1140 : ℝ) ∧ Ssec (2081 / 1140 : ℝ) ≤ 1 / (16301395029 / 25000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (17210070279 / 20000000000 : ℝ)) (θhi := (21512587849 / 25000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_100 : 1 / (16345643409 / 25000000000 : ℝ) ^ 2 ≤ Ssec (313 / 171 : ℝ) ∧ Ssec (313 / 171 : ℝ) ≤ 1 / (13076514727 / 20000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (21454167083 / 25000000000 : ℝ)) (θhi := (85816668333 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_101 : 1 / (6555825431 / 10000000000 : ℝ) ^ 2 ≤ Ssec (6277 / 3420 : ℝ) ∧ Ssec (6277 / 3420 : ℝ) ≤ 1 / (16389563577 / 25000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (85584251037 / 100000000000 : ℝ)) (θhi := (42792125519 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_102 : 1 / (8216579337 / 12500000000 : ℝ) ^ 2 ≤ Ssec (1049 / 570 : ℝ) ∧ Ssec (1049 / 570 : ℝ) ≤ 1 / (13146526939 / 20000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (85353089253 / 100000000000 : ℝ)) (θhi := (42676544627 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_103 : 1 / (6590572721 / 10000000000 : ℝ) ^ 2 ≤ Ssec (6311 / 3420 : ℝ) ∧ Ssec (6311 / 3420 : ℝ) ≤ 1 / (8238215901 / 12500000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (17024634567 / 20000000000 : ℝ)) (θhi := (21280793209 / 25000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_104 : 1 / (16519386031 / 25000000000 : ℝ) ^ 2 ≤ Ssec (1582 / 855 : ℝ) ∧ Ssec (1582 / 855 : ℝ) ≤ 1 / (33038772061 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (16978898349 / 20000000000 : ℝ)) (θhi := (42447245873 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_105 : 1 / (6624809757 / 10000000000 : ℝ) ^ 2 ≤ Ssec (141 / 76 : ℝ) ∧ Ssec (141 / 76 : ℝ) ≤ 1 / (2070253049 / 3125000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (42333518027 / 50000000000 : ℝ)) (θhi := (16933407211 / 20000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_106 : 1 / (33208699771 / 50000000000 : ℝ) ^ 2 ≤ Ssec (3181 / 1710 : ℝ) ∧ Ssec (3181 / 1710 : ℝ) ≤ 1 / (66417399541 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (42220397969 / 50000000000 : ℝ)) (θhi := (84440795939 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_107 : 1 / (8323182737 / 12500000000 : ℝ) ^ 2 ≤ Ssec (6379 / 3420 : ℝ) ∧ Ssec (6379 / 3420 : ℝ) ≤ 1 / (33292730947 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (84215761681 / 100000000000 : ℝ)) (θhi := (42107880841 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_108 : 1 / (33376148177 / 50000000000 : ℝ) ^ 2 ≤ Ssec (533 / 285 : ℝ) ∧ Ssec (533 / 285 : ℝ) ≤ 1 / (2086009261 / 3125000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (16798384733 / 20000000000 : ℝ)) (θhi := (41995961833 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_109 : 1 / (33458957253 / 50000000000 : ℝ) ^ 2 ≤ Ssec (6413 / 3420 : ℝ) ∧ Ssec (6413 / 3420 : ℝ) ≤ 1 / (8364739313 / 12500000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (41884636189 / 50000000000 : ℝ)) (θhi := (83769272379 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_110 : 1 / (262040343 / 390625000 : ℝ) ^ 2 ≤ Ssec (643 / 342 : ℝ) ∧ Ssec (643 / 342 : ℝ) ≤ 1 / (33541163903 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (10443474801 / 12500000000 : ℝ)) (θhi := (83547798409 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_111 : 1 / (16811386897 / 25000000000 : ℝ) ^ 2 ≤ Ssec (2149 / 1140 : ℝ) ∧ Ssec (2149 / 1140 : ℝ) ≤ 1 / (33622773793 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (2083187311 / 2500000000 : ℝ)) (θhi := (83327492441 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_112 : 1 / (33703792523 / 50000000000 : ℝ) ^ 2 ≤ Ssec (1616 / 855 : ℝ) ∧ Ssec (1616 / 855 : ℝ) ≤ 1 / (16851896261 / 25000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (4155417263 / 5000000000 : ℝ)) (θhi := (83108345261 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_113 : 1 / (13513690251 / 20000000000 : ℝ) ^ 2 ≤ Ssec (6481 / 3420 : ℝ) ∧ Ssec (6481 / 3420 : ℝ) ≤ 1 / (67568451253 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (82890347749 / 100000000000 : ℝ)) (θhi := (331561391 / 400000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_114 : 1 / (16932039291 / 25000000000 : ℝ) ^ 2 ≤ Ssec (19 / 10 : ℝ) ∧ Ssec (19 / 10 : ℝ) ≤ 1 / (33864078581 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (82673490883 / 100000000000 : ℝ)) (θhi := (20668372721 / 25000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_115 : 1 / (67887642901 / 100000000000 : ℝ) ^ 2 ≤ Ssec (381 / 200 : ℝ) ∧ Ssec (381 / 200 : ℝ) ≤ 1 / (678876429 / 1000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (41228250047 / 50000000000 : ℝ)) (θhi := (16491300019 / 20000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_116 : 1 / (13609195299 / 20000000000 : ℝ) ^ 2 ≤ Ssec (191 / 100 : ℝ) ∧ Ssec (191 / 100 : ℝ) ≤ 1 / (68045976493 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (82240645381 / 100000000000 : ℝ)) (θhi := (41120322691 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_117 : 1 / (8525396089 / 12500000000 : ℝ) ^ 2 ≤ Ssec (383 / 200 : ℝ) ∧ Ssec (383 / 200 : ℝ) ≤ 1 / (6820316871 / 10000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (10253239731 / 12500000000 : ℝ)) (θhi := (82025917849 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_118 : 1 / (68359230203 / 100000000000 : ℝ) ^ 2 ≤ Ssec (48 / 25 : ℝ) ∧ Ssec (48 / 25 : ℝ) ≤ 1 / (68359230201 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (81812308687 / 100000000000 : ℝ)) (θhi := (5113269293 / 6250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_119 : 1 / (68514171497 / 100000000000 : ℝ) ^ 2 ≤ Ssec (77 / 40 : ℝ) ∧ Ssec (77 / 40 : ℝ) ≤ 1 / (8564271437 / 12500000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (2549994037 / 3125000000 : ℝ)) (θhi := (16319961837 / 20000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_120 : 1 / (68668003007 / 100000000000 : ℝ) ^ 2 ≤ Ssec (193 / 100 : ℝ) ∧ Ssec (193 / 100 : ℝ) ≤ 1 / (13733600601 / 20000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (40694205357 / 50000000000 : ℝ)) (θhi := (16277682143 / 20000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_121 : 1 / (4301295939 / 6250000000 : ℝ) ^ 2 ≤ Ssec (387 / 200 : ℝ) ∧ Ssec (387 / 200 : ℝ) ≤ 1 / (34410367511 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (81178104743 / 100000000000 : ℝ)) (θhi := (10147263093 / 12500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_122 : 1 / (68972377729 / 100000000000 : ℝ) ^ 2 ≤ Ssec (97 / 50 : ℝ) ∧ Ssec (97 / 50 : ℝ) ≤ 1 / (68972377727 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (10121110353 / 12500000000 : ℝ)) (θhi := (3238755313 / 4000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_123 : 1 / (69122941187 / 100000000000 : ℝ) ^ 2 ≤ Ssec (389 / 200 : ℝ) ∧ Ssec (389 / 200 : ℝ) ≤ 1 / (13824588237 / 20000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (20190184149 / 25000000000 : ℝ)) (θhi := (80760736597 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_124 : 1 / (8659054419 / 12500000000 : ℝ) ^ 2 ≤ Ssec (39 / 20 : ℝ) ∧ Ssec (39 / 20 : ℝ) ≤ 1 / (1385448707 / 2000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (10069207223 / 12500000000 : ℝ)) (θhi := (16110731557 / 20000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_125 : 1 / (13884174013 / 20000000000 : ℝ) ^ 2 ≤ Ssec (391 / 200 : ℝ) ∧ Ssec (391 / 200 : ℝ) ≤ 1 / (4338804379 / 6250000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (80347638199 / 100000000000 : ℝ)) (θhi := (401738191 / 500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_126 : 1 / (69568255061 / 100000000000 : ℝ) ^ 2 ≤ Ssec (49 / 25 : ℝ) ∧ Ssec (49 / 25 : ℝ) ≤ 1 / (69568255059 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (40071334867 / 50000000000 : ℝ)) (θhi := (16028533947 / 20000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_127 : 1 / (17428649991 / 25000000000 : ℝ) ^ 2 ≤ Ssec (393 / 200 : ℝ) ∧ Ssec (393 / 200 : ℝ) ≤ 1 / (34857299981 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (39969372183 / 50000000000 : ℝ)) (θhi := (79938744367 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_128 : 1 / (69859914291 / 100000000000 : ℝ) ^ 2 ≤ Ssec (197 / 100 : ℝ) ∧ Ssec (197 / 100 : ℝ) ≤ 1 / (6985991429 / 10000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (9966981769 / 12500000000 : ℝ)) (θhi := (79735854153 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_129 : 1 / (35002103729 / 50000000000 : ℝ) ^ 2 ≤ Ssec (79 / 40 : ℝ) ∧ Ssec (79 / 40 : ℝ) ≤ 1 / (2187631483 / 3125000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (7953399123 / 10000000000 : ℝ)) (θhi := (79533991231 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_130 : 1 / (17536872193 / 25000000000 : ℝ) ^ 2 ≤ Ssec (99 / 50 : ℝ) ∧ Ssec (99 / 50 : ℝ) ≤ 1 / (7014748877 / 10000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (79333147817 / 100000000000 : ℝ)) (θhi := (39666573909 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_131 : 1 / (8772003053 / 12500000000 : ℝ) ^ 2 ≤ Ssec (1981 / 1000 : ℝ) ∧ Ssec (1981 / 1000 : ℝ) ≤ 1 / (35088012211 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (79293100797 / 100000000000 : ℝ)) (θhi := (39646550399 / 50000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_132 : 1 / (17551130011 / 25000000000 : ℝ) ^ 2 ≤ Ssec (991 / 500 : ℝ) ∧ Ssec (991 / 500 : ℝ) ≤ 1 / (35102260021 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (79253094187 / 100000000000 : ℝ)) (θhi := (19813273547 / 25000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_133 : 1 / (8779121963 / 12500000000 : ℝ) ^ 2 ≤ Ssec (1983 / 1000 : ℝ) ∧ Ssec (1983 / 1000 : ℝ) ≤ 1 / (70232975703 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (79213127927 / 100000000000 : ℝ)) (θhi := (9901640991 / 12500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_134 : 1 / (70261391479 / 100000000000 : ℝ) ^ 2 ≤ Ssec (248 / 125 : ℝ) ∧ Ssec (248 / 125 : ℝ) ≤ 1 / (70261391477 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (15834640391 / 20000000000 : ℝ)) (θhi := (19793300489 / 25000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_135 : 1 / (70289767439 / 100000000000 : ℝ) ^ 2 ≤ Ssec (397 / 200 : ℝ) ∧ Ssec (397 / 200 : ℝ) ≤ 1 / (70289767437 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (79133316211 / 100000000000 : ℝ)) (θhi := (19783329053 / 25000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_136 : 1 / (35159051829 / 50000000000 : ℝ) ^ 2 ≤ Ssec (993 / 500 : ℝ) ∧ Ssec (993 / 500 : ℝ) ≤ 1 / (8789762957 / 12500000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (39546735317 / 50000000000 : ℝ)) (θhi := (15818694127 / 20000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_137 : 1 / (4396650013 / 6250000000 : ℝ) ^ 2 ≤ Ssec (1987 / 1000 : ℝ) ∧ Ssec (1987 / 1000 : ℝ) ≤ 1 / (35173200103 / 50000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (79053665163 / 100000000000 : ℝ)) (θhi := (19763416291 / 25000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_138 : 1 / (70374657161 / 100000000000 : ℝ) ^ 2 ≤ Ssec (497 / 250 : ℝ) ∧ Ssec (497 / 250 : ℝ) ≤ 1 / (1759366429 / 2500000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (39506949869 / 50000000000 : ℝ)) (θhi := (79013899739 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_139 : 1 / (7040287459 / 10000000000 : ℝ) ^ 2 ≤ Ssec (1989 / 1000 : ℝ) ∧ Ssec (1989 / 1000 : ℝ) ≤ 1 / (70402874589 / 100000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (39487087149 / 50000000000 : ℝ)) (θhi := (78974174299 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem pt_140 : 1 / (35215526283 / 50000000000 : ℝ) ^ 2 ≤ Ssec (199 / 100 : ℝ) ∧ Ssec (199 / 100 : ℝ) ≤ 1 / (14086210513 / 20000000000 : ℝ) ^ 2 :=
  NewRows11.Ssec_encl (θlo := (78934488783 / 100000000000 : ℝ)) (θhi := (4933405549 / 6250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem cell_0 : 16 / 100 * (Ssec (cellLeft 0) - cellLeft 0 / (cellLeft 0 - 1)) ≤
    cellLevel 0 - 2 / 10 ^ 6 - cellLeft 0 / (cellLeft 0 - 1) :=
  cell_of_bounds (pl := (4 / 3 : ℝ)) (pr := (4577 / 3420 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_1.1 pt_0.2 (by norm_num)

theorem cell_1 : 16 / 100 * (Ssec (cellLeft 1) - cellLeft 1 / (cellLeft 1 - 1)) ≤
    cellLevel 1 - 2 / 10 ^ 6 - cellLeft 1 / (cellLeft 1 - 1) :=
  cell_of_bounds (pl := (4577 / 3420 : ℝ)) (pr := (2297 / 1710 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_2.1 pt_1.2 (by norm_num)

theorem cell_2 : 16 / 100 * (Ssec (cellLeft 2) - cellLeft 2 / (cellLeft 2 - 1)) ≤
    cellLevel 2 - 2 / 10 ^ 6 - cellLeft 2 / (cellLeft 2 - 1) :=
  cell_of_bounds (pl := (2297 / 1710 : ℝ)) (pr := (1537 / 1140 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_3.1 pt_2.2 (by norm_num)

theorem cell_3 : 16 / 100 * (Ssec (cellLeft 3) - cellLeft 3 / (cellLeft 3 - 1)) ≤
    cellLevel 3 - 2 / 10 ^ 6 - cellLeft 3 / (cellLeft 3 - 1) :=
  cell_of_bounds (pl := (1537 / 1140 : ℝ)) (pr := (1157 / 855 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_4.1 pt_3.2 (by norm_num)

theorem cell_4 : 16 / 100 * (Ssec (cellLeft 4) - cellLeft 4 / (cellLeft 4 - 1)) ≤
    cellLevel 4 - 2 / 10 ^ 6 - cellLeft 4 / (cellLeft 4 - 1) :=
  cell_of_bounds (pl := (1157 / 855 : ℝ)) (pr := (929 / 684 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_5.1 pt_4.2 (by norm_num)

theorem cell_5 : 16 / 100 * (Ssec (cellLeft 5) - cellLeft 5 / (cellLeft 5 - 1)) ≤
    cellLevel 5 - 2 / 10 ^ 6 - cellLeft 5 / (cellLeft 5 - 1) :=
  cell_of_bounds (pl := (929 / 684 : ℝ)) (pr := (259 / 190 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_6.1 pt_5.2 (by norm_num)

theorem cell_6 : 16 / 100 * (Ssec (cellLeft 6) - cellLeft 6 / (cellLeft 6 - 1)) ≤
    cellLevel 6 - 2 / 10 ^ 6 - cellLeft 6 / (cellLeft 6 - 1) :=
  cell_of_bounds (pl := (259 / 190 : ℝ)) (pr := (4679 / 3420 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_7.1 pt_6.2 (by norm_num)

theorem cell_7 : 16 / 100 * (Ssec (cellLeft 7) - cellLeft 7 / (cellLeft 7 - 1)) ≤
    cellLevel 7 - 2 / 10 ^ 6 - cellLeft 7 / (cellLeft 7 - 1) :=
  cell_of_bounds (pl := (4679 / 3420 : ℝ)) (pr := (1174 / 855 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_8.1 pt_7.2 (by norm_num)

theorem cell_8 : 16 / 100 * (Ssec (cellLeft 8) - cellLeft 8 / (cellLeft 8 - 1)) ≤
    cellLevel 8 - 2 / 10 ^ 6 - cellLeft 8 / (cellLeft 8 - 1) :=
  cell_of_bounds (pl := (1174 / 855 : ℝ)) (pr := (1571 / 1140 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_9.1 pt_8.2 (by norm_num)

theorem cell_9 : 16 / 100 * (Ssec (cellLeft 9) - cellLeft 9 / (cellLeft 9 - 1)) ≤
    cellLevel 9 - 2 / 10 ^ 6 - cellLeft 9 / (cellLeft 9 - 1) :=
  cell_of_bounds (pl := (1571 / 1140 : ℝ)) (pr := (473 / 342 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_10.1 pt_9.2 (by norm_num)

theorem cell_10 : 16 / 100 * (Ssec (cellLeft 10) - cellLeft 10 / (cellLeft 10 - 1)) ≤
    cellLevel 10 - 2 / 10 ^ 6 - cellLeft 10 / (cellLeft 10 - 1) :=
  cell_of_bounds (pl := (473 / 342 : ℝ)) (pr := (4747 / 3420 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_11.1 pt_10.2 (by norm_num)

theorem cell_11 : 16 / 100 * (Ssec (cellLeft 11) - cellLeft 11 / (cellLeft 11 - 1)) ≤
    cellLevel 11 - 2 / 10 ^ 6 - cellLeft 11 / (cellLeft 11 - 1) :=
  cell_of_bounds (pl := (4747 / 3420 : ℝ)) (pr := (397 / 285 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_12.1 pt_11.2 (by norm_num)

theorem cell_12 : 16 / 100 * (Ssec (cellLeft 12) - cellLeft 12 / (cellLeft 12 - 1)) ≤
    cellLevel 12 - 2 / 10 ^ 6 - cellLeft 12 / (cellLeft 12 - 1) :=
  cell_of_bounds (pl := (397 / 285 : ℝ)) (pr := (4781 / 3420 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_13.1 pt_12.2 (by norm_num)

theorem cell_13 : 16 / 100 * (Ssec (cellLeft 13) - cellLeft 13 / (cellLeft 13 - 1)) ≤
    cellLevel 13 - 2 / 10 ^ 6 - cellLeft 13 / (cellLeft 13 - 1) :=
  cell_of_bounds (pl := (4781 / 3420 : ℝ)) (pr := (2399 / 1710 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_14.1 pt_13.2 (by norm_num)

theorem cell_14 : 16 / 100 * (Ssec (cellLeft 14) - cellLeft 14 / (cellLeft 14 - 1)) ≤
    cellLevel 14 - 2 / 10 ^ 6 - cellLeft 14 / (cellLeft 14 - 1) :=
  cell_of_bounds (pl := (2399 / 1710 : ℝ)) (pr := (107 / 76 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_15.1 pt_14.2 (by norm_num)

theorem cell_15 : 16 / 100 * (Ssec (cellLeft 15) - cellLeft 15 / (cellLeft 15 - 1)) ≤
    cellLevel 15 - 2 / 10 ^ 6 - cellLeft 15 / (cellLeft 15 - 1) :=
  cell_of_bounds (pl := (107 / 76 : ℝ)) (pr := (1208 / 855 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_16.1 pt_15.2 (by norm_num)

theorem cell_16 : 16 / 100 * (Ssec (cellLeft 16) - cellLeft 16 / (cellLeft 16 - 1)) ≤
    cellLevel 16 - 2 / 10 ^ 6 - cellLeft 16 / (cellLeft 16 - 1) :=
  cell_of_bounds (pl := (1208 / 855 : ℝ)) (pr := (4849 / 3420 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_17.1 pt_16.2 (by norm_num)

theorem cell_17 : 16 / 100 * (Ssec (cellLeft 17) - cellLeft 17 / (cellLeft 17 - 1)) ≤
    cellLevel 17 - 2 / 10 ^ 6 - cellLeft 17 / (cellLeft 17 - 1) :=
  cell_of_bounds (pl := (4849 / 3420 : ℝ)) (pr := (811 / 570 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_18.1 pt_17.2 (by norm_num)

theorem cell_18 : 16 / 100 * (Ssec (cellLeft 18) - cellLeft 18 / (cellLeft 18 - 1)) ≤
    cellLevel 18 - 2 / 10 ^ 6 - cellLeft 18 / (cellLeft 18 - 1) :=
  cell_of_bounds (pl := (811 / 570 : ℝ)) (pr := (257 / 180 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_19.1 pt_18.2 (by norm_num)

theorem cell_19 : 16 / 100 * (Ssec (cellLeft 19) - cellLeft 19 / (cellLeft 19 - 1)) ≤
    cellLevel 19 - 2 / 10 ^ 6 - cellLeft 19 / (cellLeft 19 - 1) :=
  cell_of_bounds (pl := (257 / 180 : ℝ)) (pr := (245 / 171 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_20.1 pt_19.2 (by norm_num)

theorem cell_20 : 16 / 100 * (Ssec (cellLeft 20) - cellLeft 20 / (cellLeft 20 - 1)) ≤
    cellLevel 20 - 2 / 10 ^ 6 - cellLeft 20 / (cellLeft 20 - 1) :=
  cell_of_bounds (pl := (245 / 171 : ℝ)) (pr := (1639 / 1140 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_21.1 pt_20.2 (by norm_num)

theorem cell_21 : 16 / 100 * (Ssec (cellLeft 21) - cellLeft 21 / (cellLeft 21 - 1)) ≤
    cellLevel 21 - 2 / 10 ^ 6 - cellLeft 21 / (cellLeft 21 - 1) :=
  cell_of_bounds (pl := (1639 / 1140 : ℝ)) (pr := (2467 / 1710 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_22.1 pt_21.2 (by norm_num)

theorem cell_22 : 16 / 100 * (Ssec (cellLeft 22) - cellLeft 22 / (cellLeft 22 - 1)) ≤
    cellLevel 22 - 2 / 10 ^ 6 - cellLeft 22 / (cellLeft 22 - 1) :=
  cell_of_bounds (pl := (2467 / 1710 : ℝ)) (pr := (4951 / 3420 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_23.1 pt_22.2 (by norm_num)

theorem cell_23 : 16 / 100 * (Ssec (cellLeft 23) - cellLeft 23 / (cellLeft 23 - 1)) ≤
    cellLevel 23 - 2 / 10 ^ 6 - cellLeft 23 / (cellLeft 23 - 1) :=
  cell_of_bounds (pl := (4951 / 3420 : ℝ)) (pr := (138 / 95 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_24.1 pt_23.2 (by norm_num)

theorem cell_24 : 16 / 100 * (Ssec (cellLeft 24) - cellLeft 24 / (cellLeft 24 - 1)) ≤
    cellLevel 24 - 2 / 10 ^ 6 - cellLeft 24 / (cellLeft 24 - 1) :=
  cell_of_bounds (pl := (138 / 95 : ℝ)) (pr := (997 / 684 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_25.1 pt_24.2 (by norm_num)

theorem cell_25 : 16 / 100 * (Ssec (cellLeft 25) - cellLeft 25 / (cellLeft 25 - 1)) ≤
    cellLevel 25 - 2 / 10 ^ 6 - cellLeft 25 / (cellLeft 25 - 1) :=
  cell_of_bounds (pl := (997 / 684 : ℝ)) (pr := (2501 / 1710 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_26.1 pt_25.2 (by norm_num)

theorem cell_26 : 16 / 100 * (Ssec (cellLeft 26) - cellLeft 26 / (cellLeft 26 - 1)) ≤
    cellLevel 26 - 2 / 10 ^ 6 - cellLeft 26 / (cellLeft 26 - 1) :=
  cell_of_bounds (pl := (2501 / 1710 : ℝ)) (pr := (1673 / 1140 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_27.1 pt_26.2 (by norm_num)

theorem cell_27 : 16 / 100 * (Ssec (cellLeft 27) - cellLeft 27 / (cellLeft 27 - 1)) ≤
    cellLevel 27 - 2 / 10 ^ 6 - cellLeft 27 / (cellLeft 27 - 1) :=
  cell_of_bounds (pl := (1673 / 1140 : ℝ)) (pr := (1259 / 855 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_28.1 pt_27.2 (by norm_num)

theorem cell_28 : 16 / 100 * (Ssec (cellLeft 28) - cellLeft 28 / (cellLeft 28 - 1)) ≤
    cellLevel 28 - 2 / 10 ^ 6 - cellLeft 28 / (cellLeft 28 - 1) :=
  cell_of_bounds (pl := (1259 / 855 : ℝ)) (pr := (5053 / 3420 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_29.1 pt_28.2 (by norm_num)

theorem cell_29 : 16 / 100 * (Ssec (cellLeft 29) - cellLeft 29 / (cellLeft 29 - 1)) ≤
    cellLevel 29 - 2 / 10 ^ 6 - cellLeft 29 / (cellLeft 29 - 1) :=
  cell_of_bounds (pl := (5053 / 3420 : ℝ)) (pr := (169 / 114 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_30.1 pt_29.2 (by norm_num)

theorem cell_30 : 16 / 100 * (Ssec (cellLeft 30) - cellLeft 30 / (cellLeft 30 - 1)) ≤
    cellLevel 30 - 2 / 10 ^ 6 - cellLeft 30 / (cellLeft 30 - 1) :=
  cell_of_bounds (pl := (169 / 114 : ℝ)) (pr := (5087 / 3420 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_31.1 pt_30.2 (by norm_num)

theorem cell_31 : 16 / 100 * (Ssec (cellLeft 31) - cellLeft 31 / (cellLeft 31 - 1)) ≤
    cellLevel 31 - 2 / 10 ^ 6 - cellLeft 31 / (cellLeft 31 - 1) :=
  cell_of_bounds (pl := (5087 / 3420 : ℝ)) (pr := (1276 / 855 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_32.1 pt_31.2 (by norm_num)

theorem cell_32 : 16 / 100 * (Ssec (cellLeft 32) - cellLeft 32 / (cellLeft 32 - 1)) ≤
    cellLevel 32 - 2 / 10 ^ 6 - cellLeft 32 / (cellLeft 32 - 1) :=
  cell_of_bounds (pl := (1276 / 855 : ℝ)) (pr := (569 / 380 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_33.1 pt_32.2 (by norm_num)

theorem cell_33 : 16 / 100 * (Ssec (cellLeft 33) - cellLeft 33 / (cellLeft 33 - 1)) ≤
    cellLevel 33 - 2 / 10 ^ 6 - cellLeft 33 / (cellLeft 33 - 1) :=
  cell_of_bounds (pl := (569 / 380 : ℝ)) (pr := (2569 / 1710 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_34.1 pt_33.2 (by norm_num)

theorem cell_34 : 16 / 100 * (Ssec (cellLeft 34) - cellLeft 34 / (cellLeft 34 - 1)) ≤
    cellLevel 34 - 2 / 10 ^ 6 - cellLeft 34 / (cellLeft 34 - 1) :=
  cell_of_bounds (pl := (2569 / 1710 : ℝ)) (pr := (1031 / 684 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_35.1 pt_34.2 (by norm_num)

theorem cell_35 : 16 / 100 * (Ssec (cellLeft 35) - cellLeft 35 / (cellLeft 35 - 1)) ≤
    cellLevel 35 - 2 / 10 ^ 6 - cellLeft 35 / (cellLeft 35 - 1) :=
  cell_of_bounds (pl := (1031 / 684 : ℝ)) (pr := (431 / 285 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_36.1 pt_35.2 (by norm_num)

theorem cell_36 : 16 / 100 * (Ssec (cellLeft 36) - cellLeft 36 / (cellLeft 36 - 1)) ≤
    cellLevel 36 - 2 / 10 ^ 6 - cellLeft 36 / (cellLeft 36 - 1) :=
  cell_of_bounds (pl := (431 / 285 : ℝ)) (pr := (5189 / 3420 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_37.1 pt_36.2 (by norm_num)

theorem cell_37 : 16 / 100 * (Ssec (cellLeft 37) - cellLeft 37 / (cellLeft 37 - 1)) ≤
    cellLevel 37 - 2 / 10 ^ 6 - cellLeft 37 / (cellLeft 37 - 1) :=
  cell_of_bounds (pl := (5189 / 3420 : ℝ)) (pr := (137 / 90 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_38.1 pt_37.2 (by norm_num)

theorem cell_38 : 16 / 100 * (Ssec (cellLeft 38) - cellLeft 38 / (cellLeft 38 - 1)) ≤
    cellLevel 38 - 2 / 10 ^ 6 - cellLeft 38 / (cellLeft 38 - 1) :=
  cell_of_bounds (pl := (137 / 90 : ℝ)) (pr := (1741 / 1140 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_39.1 pt_38.2 (by norm_num)

theorem cell_39 : 16 / 100 * (Ssec (cellLeft 39) - cellLeft 39 / (cellLeft 39 - 1)) ≤
    cellLevel 39 - 2 / 10 ^ 6 - cellLeft 39 / (cellLeft 39 - 1) :=
  cell_of_bounds (pl := (1741 / 1140 : ℝ)) (pr := (262 / 171 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_40.1 pt_39.2 (by norm_num)

theorem cell_40 : 16 / 100 * (Ssec (cellLeft 40) - cellLeft 40 / (cellLeft 40 - 1)) ≤
    cellLevel 40 - 2 / 10 ^ 6 - cellLeft 40 / (cellLeft 40 - 1) :=
  cell_of_bounds (pl := (262 / 171 : ℝ)) (pr := (5257 / 3420 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_41.1 pt_40.2 (by norm_num)

theorem cell_41 : 16 / 100 * (Ssec (cellLeft 41) - cellLeft 41 / (cellLeft 41 - 1)) ≤
    cellLevel 41 - 2 / 10 ^ 6 - cellLeft 41 / (cellLeft 41 - 1) :=
  cell_of_bounds (pl := (5257 / 3420 : ℝ)) (pr := (293 / 190 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_42.1 pt_41.2 (by norm_num)

theorem cell_42 : 16 / 100 * (Ssec (cellLeft 42) - cellLeft 42 / (cellLeft 42 - 1)) ≤
    cellLevel 42 - 2 / 10 ^ 6 - cellLeft 42 / (cellLeft 42 - 1) :=
  cell_of_bounds (pl := (293 / 190 : ℝ)) (pr := (5291 / 3420 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_43.1 pt_42.2 (by norm_num)

theorem cell_43 : 16 / 100 * (Ssec (cellLeft 43) - cellLeft 43 / (cellLeft 43 - 1)) ≤
    cellLevel 43 - 2 / 10 ^ 6 - cellLeft 43 / (cellLeft 43 - 1) :=
  cell_of_bounds (pl := (5291 / 3420 : ℝ)) (pr := (1327 / 855 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_44.1 pt_43.2 (by norm_num)

theorem cell_44 : 16 / 100 * (Ssec (cellLeft 44) - cellLeft 44 / (cellLeft 44 - 1)) ≤
    cellLevel 44 - 2 / 10 ^ 6 - cellLeft 44 / (cellLeft 44 - 1) :=
  cell_of_bounds (pl := (1327 / 855 : ℝ)) (pr := (355 / 228 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_45.1 pt_44.2 (by norm_num)

theorem cell_45 : 16 / 100 * (Ssec (cellLeft 45) - cellLeft 45 / (cellLeft 45 - 1)) ≤
    cellLevel 45 - 2 / 10 ^ 6 - cellLeft 45 / (cellLeft 45 - 1) :=
  cell_of_bounds (pl := (355 / 228 : ℝ)) (pr := (2671 / 1710 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_46.1 pt_45.2 (by norm_num)

theorem cell_46 : 16 / 100 * (Ssec (cellLeft 46) - cellLeft 46 / (cellLeft 46 - 1)) ≤
    cellLevel 46 - 2 / 10 ^ 6 - cellLeft 46 / (cellLeft 46 - 1) :=
  cell_of_bounds (pl := (2671 / 1710 : ℝ)) (pr := (5359 / 3420 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_47.1 pt_46.2 (by norm_num)

theorem cell_47 : 16 / 100 * (Ssec (cellLeft 47) - cellLeft 47 / (cellLeft 47 - 1)) ≤
    cellLevel 47 - 2 / 10 ^ 6 - cellLeft 47 / (cellLeft 47 - 1) :=
  cell_of_bounds (pl := (5359 / 3420 : ℝ)) (pr := (448 / 285 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_48.1 pt_47.2 (by norm_num)

theorem cell_48 : 16 / 100 * (Ssec (cellLeft 48) - cellLeft 48 / (cellLeft 48 - 1)) ≤
    cellLevel 48 - 2 / 10 ^ 6 - cellLeft 48 / (cellLeft 48 - 1) :=
  cell_of_bounds (pl := (448 / 285 : ℝ)) (pr := (5393 / 3420 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_49.1 pt_48.2 (by norm_num)

theorem cell_49 : 16 / 100 * (Ssec (cellLeft 49) - cellLeft 49 / (cellLeft 49 - 1)) ≤
    cellLevel 49 - 2 / 10 ^ 6 - cellLeft 49 / (cellLeft 49 - 1) :=
  cell_of_bounds (pl := (5393 / 3420 : ℝ)) (pr := (541 / 342 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_50.1 pt_49.2 (by norm_num)

theorem cell_50 : 16 / 100 * (Ssec (cellLeft 50) - cellLeft 50 / (cellLeft 50 - 1)) ≤
    cellLevel 50 - 2 / 10 ^ 6 - cellLeft 50 / (cellLeft 50 - 1) :=
  cell_of_bounds (pl := (541 / 342 : ℝ)) (pr := (603 / 380 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_51.1 pt_50.2 (by norm_num)

theorem cell_51 : 16 / 100 * (Ssec (cellLeft 51) - cellLeft 51 / (cellLeft 51 - 1)) ≤
    cellLevel 51 - 2 / 10 ^ 6 - cellLeft 51 / (cellLeft 51 - 1) :=
  cell_of_bounds (pl := (603 / 380 : ℝ)) (pr := (1361 / 855 : ℝ)) (κ := (9 / 10 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_52.1 pt_51.2 (by norm_num)

theorem cell_52 : 16 / 100 * (Ssec (cellLeft 52) - cellLeft 52 / (cellLeft 52 - 1)) ≤
    cellLevel 52 - 2 / 10 ^ 6 - cellLeft 52 / (cellLeft 52 - 1) :=
  cell_of_bounds (pl := (1361 / 855 : ℝ)) (pr := (5461 / 3420 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_53.1 pt_52.2 (by norm_num)

theorem cell_53 : 16 / 100 * (Ssec (cellLeft 53) - cellLeft 53 / (cellLeft 53 - 1)) ≤
    cellLevel 53 - 2 / 10 ^ 6 - cellLeft 53 / (cellLeft 53 - 1) :=
  cell_of_bounds (pl := (5461 / 3420 : ℝ)) (pr := (913 / 570 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_54.1 pt_53.2 (by norm_num)

theorem cell_54 : 16 / 100 * (Ssec (cellLeft 54) - cellLeft 54 / (cellLeft 54 - 1)) ≤
    cellLevel 54 - 2 / 10 ^ 6 - cellLeft 54 / (cellLeft 54 - 1) :=
  cell_of_bounds (pl := (913 / 570 : ℝ)) (pr := (1099 / 684 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_55.1 pt_54.2 (by norm_num)

theorem cell_55 : 16 / 100 * (Ssec (cellLeft 55) - cellLeft 55 / (cellLeft 55 - 1)) ≤
    cellLevel 55 - 2 / 10 ^ 6 - cellLeft 55 / (cellLeft 55 - 1) :=
  cell_of_bounds (pl := (1099 / 684 : ℝ)) (pr := (1378 / 855 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_56.1 pt_55.2 (by norm_num)

theorem cell_56 : 16 / 100 * (Ssec (cellLeft 56) - cellLeft 56 / (cellLeft 56 - 1)) ≤
    cellLevel 56 - 2 / 10 ^ 6 - cellLeft 56 / (cellLeft 56 - 1) :=
  cell_of_bounds (pl := (1378 / 855 : ℝ)) (pr := (97 / 60 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_57.1 pt_56.2 (by norm_num)

theorem cell_57 : 16 / 100 * (Ssec (cellLeft 57) - cellLeft 57 / (cellLeft 57 - 1)) ≤
    cellLevel 57 - 2 / 10 ^ 6 - cellLeft 57 / (cellLeft 57 - 1) :=
  cell_of_bounds (pl := (97 / 60 : ℝ)) (pr := (2773 / 1710 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_58.1 pt_57.2 (by norm_num)

theorem cell_58 : 16 / 100 * (Ssec (cellLeft 58) - cellLeft 58 / (cellLeft 58 - 1)) ≤
    cellLevel 58 - 2 / 10 ^ 6 - cellLeft 58 / (cellLeft 58 - 1) :=
  cell_of_bounds (pl := (2773 / 1710 : ℝ)) (pr := (5563 / 3420 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_59.1 pt_58.2 (by norm_num)

theorem cell_59 : 16 / 100 * (Ssec (cellLeft 59) - cellLeft 59 / (cellLeft 59 - 1)) ≤
    cellLevel 59 - 2 / 10 ^ 6 - cellLeft 59 / (cellLeft 59 - 1) :=
  cell_of_bounds (pl := (5563 / 3420 : ℝ)) (pr := (31 / 19 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_60.1 pt_59.2 (by norm_num)

theorem cell_60 : 16 / 100 * (Ssec (cellLeft 60) - cellLeft 60 / (cellLeft 60 - 1)) ≤
    cellLevel 60 - 2 / 10 ^ 6 - cellLeft 60 / (cellLeft 60 - 1) :=
  cell_of_bounds (pl := (31 / 19 : ℝ)) (pr := (5597 / 3420 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_61.1 pt_60.2 (by norm_num)

theorem cell_61 : 16 / 100 * (Ssec (cellLeft 61) - cellLeft 61 / (cellLeft 61 - 1)) ≤
    cellLevel 61 - 2 / 10 ^ 6 - cellLeft 61 / (cellLeft 61 - 1) :=
  cell_of_bounds (pl := (5597 / 3420 : ℝ)) (pr := (2807 / 1710 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_62.1 pt_61.2 (by norm_num)

theorem cell_62 : 16 / 100 * (Ssec (cellLeft 62) - cellLeft 62 / (cellLeft 62 - 1)) ≤
    cellLevel 62 - 2 / 10 ^ 6 - cellLeft 62 / (cellLeft 62 - 1) :=
  cell_of_bounds (pl := (2807 / 1710 : ℝ)) (pr := (1877 / 1140 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_63.1 pt_62.2 (by norm_num)

theorem cell_63 : 16 / 100 * (Ssec (cellLeft 63) - cellLeft 63 / (cellLeft 63 - 1)) ≤
    cellLevel 63 - 2 / 10 ^ 6 - cellLeft 63 / (cellLeft 63 - 1) :=
  cell_of_bounds (pl := (1877 / 1140 : ℝ)) (pr := (1412 / 855 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_64.1 pt_63.2 (by norm_num)

theorem cell_64 : 16 / 100 * (Ssec (cellLeft 64) - cellLeft 64 / (cellLeft 64 - 1)) ≤
    cellLevel 64 - 2 / 10 ^ 6 - cellLeft 64 / (cellLeft 64 - 1) :=
  cell_of_bounds (pl := (1412 / 855 : ℝ)) (pr := (1133 / 684 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_65.1 pt_64.2 (by norm_num)

theorem cell_65 : 16 / 100 * (Ssec (cellLeft 65) - cellLeft 65 / (cellLeft 65 - 1)) ≤
    cellLevel 65 - 2 / 10 ^ 6 - cellLeft 65 / (cellLeft 65 - 1) :=
  cell_of_bounds (pl := (1133 / 684 : ℝ)) (pr := (947 / 570 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_66.1 pt_65.2 (by norm_num)

theorem cell_66 : 16 / 100 * (Ssec (cellLeft 66) - cellLeft 66 / (cellLeft 66 - 1)) ≤
    cellLevel 66 - 2 / 10 ^ 6 - cellLeft 66 / (cellLeft 66 - 1) :=
  cell_of_bounds (pl := (947 / 570 : ℝ)) (pr := (5699 / 3420 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_67.1 pt_66.2 (by norm_num)

theorem cell_67 : 16 / 100 * (Ssec (cellLeft 67) - cellLeft 67 / (cellLeft 67 - 1)) ≤
    cellLevel 67 - 2 / 10 ^ 6 - cellLeft 67 / (cellLeft 67 - 1) :=
  cell_of_bounds (pl := (5699 / 3420 : ℝ)) (pr := (1429 / 855 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_68.1 pt_67.2 (by norm_num)

theorem cell_68 : 16 / 100 * (Ssec (cellLeft 68) - cellLeft 68 / (cellLeft 68 - 1)) ≤
    cellLevel 68 - 2 / 10 ^ 6 - cellLeft 68 / (cellLeft 68 - 1) :=
  cell_of_bounds (pl := (1429 / 855 : ℝ)) (pr := (637 / 380 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_69.1 pt_68.2 (by norm_num)

theorem cell_69 : 16 / 100 * (Ssec (cellLeft 69) - cellLeft 69 / (cellLeft 69 - 1)) ≤
    cellLevel 69 - 2 / 10 ^ 6 - cellLeft 69 / (cellLeft 69 - 1) :=
  cell_of_bounds (pl := (637 / 380 : ℝ)) (pr := (575 / 342 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_70.1 pt_69.2 (by norm_num)

theorem cell_70 : 16 / 100 * (Ssec (cellLeft 70) - cellLeft 70 / (cellLeft 70 - 1)) ≤
    cellLevel 70 - 2 / 10 ^ 6 - cellLeft 70 / (cellLeft 70 - 1) :=
  cell_of_bounds (pl := (575 / 342 : ℝ)) (pr := (5767 / 3420 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_71.1 pt_70.2 (by norm_num)

theorem cell_71 : 16 / 100 * (Ssec (cellLeft 71) - cellLeft 71 / (cellLeft 71 - 1)) ≤
    cellLevel 71 - 2 / 10 ^ 6 - cellLeft 71 / (cellLeft 71 - 1) :=
  cell_of_bounds (pl := (5767 / 3420 : ℝ)) (pr := (482 / 285 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_72.1 pt_71.2 (by norm_num)

theorem cell_72 : 16 / 100 * (Ssec (cellLeft 72) - cellLeft 72 / (cellLeft 72 - 1)) ≤
    cellLevel 72 - 2 / 10 ^ 6 - cellLeft 72 / (cellLeft 72 - 1) :=
  cell_of_bounds (pl := (482 / 285 : ℝ)) (pr := (5801 / 3420 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_73.1 pt_72.2 (by norm_num)

theorem cell_73 : 16 / 100 * (Ssec (cellLeft 73) - cellLeft 73 / (cellLeft 73 - 1)) ≤
    cellLevel 73 - 2 / 10 ^ 6 - cellLeft 73 / (cellLeft 73 - 1) :=
  cell_of_bounds (pl := (5801 / 3420 : ℝ)) (pr := (2909 / 1710 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_74.1 pt_73.2 (by norm_num)

theorem cell_74 : 16 / 100 * (Ssec (cellLeft 74) - cellLeft 74 / (cellLeft 74 - 1)) ≤
    cellLevel 74 - 2 / 10 ^ 6 - cellLeft 74 / (cellLeft 74 - 1) :=
  cell_of_bounds (pl := (2909 / 1710 : ℝ)) (pr := (389 / 228 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_75.1 pt_74.2 (by norm_num)

theorem cell_75 : 16 / 100 * (Ssec (cellLeft 75) - cellLeft 75 / (cellLeft 75 - 1)) ≤
    cellLevel 75 - 2 / 10 ^ 6 - cellLeft 75 / (cellLeft 75 - 1) :=
  cell_of_bounds (pl := (389 / 228 : ℝ)) (pr := (77 / 45 : ℝ)) (κ := (4 / 5 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_76.1 pt_75.2 (by norm_num)

theorem cell_76 : 16 / 100 * (Ssec (cellLeft 76) - cellLeft 76 / (cellLeft 76 - 1)) ≤
    cellLevel 76 - 2 / 10 ^ 6 - cellLeft 76 / (cellLeft 76 - 1) :=
  cell_of_bounds (pl := (77 / 45 : ℝ)) (pr := (5869 / 3420 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_77.1 pt_76.2 (by norm_num)

theorem cell_77 : 16 / 100 * (Ssec (cellLeft 77) - cellLeft 77 / (cellLeft 77 - 1)) ≤
    cellLevel 77 - 2 / 10 ^ 6 - cellLeft 77 / (cellLeft 77 - 1) :=
  cell_of_bounds (pl := (5869 / 3420 : ℝ)) (pr := (327 / 190 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_78.1 pt_77.2 (by norm_num)

theorem cell_78 : 16 / 100 * (Ssec (cellLeft 78) - cellLeft 78 / (cellLeft 78 - 1)) ≤
    cellLevel 78 - 2 / 10 ^ 6 - cellLeft 78 / (cellLeft 78 - 1) :=
  cell_of_bounds (pl := (327 / 190 : ℝ)) (pr := (5903 / 3420 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_79.1 pt_78.2 (by norm_num)

theorem cell_79 : 16 / 100 * (Ssec (cellLeft 79) - cellLeft 79 / (cellLeft 79 - 1)) ≤
    cellLevel 79 - 2 / 10 ^ 6 - cellLeft 79 / (cellLeft 79 - 1) :=
  cell_of_bounds (pl := (5903 / 3420 : ℝ)) (pr := (296 / 171 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_80.1 pt_79.2 (by norm_num)

theorem cell_80 : 16 / 100 * (Ssec (cellLeft 80) - cellLeft 80 / (cellLeft 80 - 1)) ≤
    cellLevel 80 - 2 / 10 ^ 6 - cellLeft 80 / (cellLeft 80 - 1) :=
  cell_of_bounds (pl := (296 / 171 : ℝ)) (pr := (1979 / 1140 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_81.1 pt_80.2 (by norm_num)

theorem cell_81 : 16 / 100 * (Ssec (cellLeft 81) - cellLeft 81 / (cellLeft 81 - 1)) ≤
    cellLevel 81 - 2 / 10 ^ 6 - cellLeft 81 / (cellLeft 81 - 1) :=
  cell_of_bounds (pl := (1979 / 1140 : ℝ)) (pr := (2977 / 1710 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_82.1 pt_81.2 (by norm_num)

theorem cell_82 : 16 / 100 * (Ssec (cellLeft 82) - cellLeft 82 / (cellLeft 82 - 1)) ≤
    cellLevel 82 - 2 / 10 ^ 6 - cellLeft 82 / (cellLeft 82 - 1) :=
  cell_of_bounds (pl := (2977 / 1710 : ℝ)) (pr := (5971 / 3420 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_83.1 pt_82.2 (by norm_num)

theorem cell_83 : 16 / 100 * (Ssec (cellLeft 83) - cellLeft 83 / (cellLeft 83 - 1)) ≤
    cellLevel 83 - 2 / 10 ^ 6 - cellLeft 83 / (cellLeft 83 - 1) :=
  cell_of_bounds (pl := (5971 / 3420 : ℝ)) (pr := (499 / 285 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_84.1 pt_83.2 (by norm_num)

theorem cell_84 : 16 / 100 * (Ssec (cellLeft 84) - cellLeft 84 / (cellLeft 84 - 1)) ≤
    cellLevel 84 - 2 / 10 ^ 6 - cellLeft 84 / (cellLeft 84 - 1) :=
  cell_of_bounds (pl := (499 / 285 : ℝ)) (pr := (1201 / 684 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_85.1 pt_84.2 (by norm_num)

theorem cell_85 : 16 / 100 * (Ssec (cellLeft 85) - cellLeft 85 / (cellLeft 85 - 1)) ≤
    cellLevel 85 - 2 / 10 ^ 6 - cellLeft 85 / (cellLeft 85 - 1) :=
  cell_of_bounds (pl := (1201 / 684 : ℝ)) (pr := (3011 / 1710 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_86.1 pt_85.2 (by norm_num)

theorem cell_86 : 16 / 100 * (Ssec (cellLeft 86) - cellLeft 86 / (cellLeft 86 - 1)) ≤
    cellLevel 86 - 2 / 10 ^ 6 - cellLeft 86 / (cellLeft 86 - 1) :=
  cell_of_bounds (pl := (3011 / 1710 : ℝ)) (pr := (671 / 380 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_87.1 pt_86.2 (by norm_num)

theorem cell_87 : 16 / 100 * (Ssec (cellLeft 87) - cellLeft 87 / (cellLeft 87 - 1)) ≤
    cellLevel 87 - 2 / 10 ^ 6 - cellLeft 87 / (cellLeft 87 - 1) :=
  cell_of_bounds (pl := (671 / 380 : ℝ)) (pr := (1514 / 855 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_88.1 pt_87.2 (by norm_num)

theorem cell_88 : 16 / 100 * (Ssec (cellLeft 88) - cellLeft 88 / (cellLeft 88 - 1)) ≤
    cellLevel 88 - 2 / 10 ^ 6 - cellLeft 88 / (cellLeft 88 - 1) :=
  cell_of_bounds (pl := (1514 / 855 : ℝ)) (pr := (6073 / 3420 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_89.1 pt_88.2 (by norm_num)

theorem cell_89 : 16 / 100 * (Ssec (cellLeft 89) - cellLeft 89 / (cellLeft 89 - 1)) ≤
    cellLevel 89 - 2 / 10 ^ 6 - cellLeft 89 / (cellLeft 89 - 1) :=
  cell_of_bounds (pl := (6073 / 3420 : ℝ)) (pr := (203 / 114 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_90.1 pt_89.2 (by norm_num)

theorem cell_90 : 16 / 100 * (Ssec (cellLeft 90) - cellLeft 90 / (cellLeft 90 - 1)) ≤
    cellLevel 90 - 2 / 10 ^ 6 - cellLeft 90 / (cellLeft 90 - 1) :=
  cell_of_bounds (pl := (203 / 114 : ℝ)) (pr := (6107 / 3420 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_91.1 pt_90.2 (by norm_num)

theorem cell_91 : 16 / 100 * (Ssec (cellLeft 91) - cellLeft 91 / (cellLeft 91 - 1)) ≤
    cellLevel 91 - 2 / 10 ^ 6 - cellLeft 91 / (cellLeft 91 - 1) :=
  cell_of_bounds (pl := (6107 / 3420 : ℝ)) (pr := (1531 / 855 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_92.1 pt_91.2 (by norm_num)

theorem cell_92 : 16 / 100 * (Ssec (cellLeft 92) - cellLeft 92 / (cellLeft 92 - 1)) ≤
    cellLevel 92 - 2 / 10 ^ 6 - cellLeft 92 / (cellLeft 92 - 1) :=
  cell_of_bounds (pl := (1531 / 855 : ℝ)) (pr := (2047 / 1140 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_93.1 pt_92.2 (by norm_num)

theorem cell_93 : 16 / 100 * (Ssec (cellLeft 93) - cellLeft 93 / (cellLeft 93 - 1)) ≤
    cellLevel 93 - 2 / 10 ^ 6 - cellLeft 93 / (cellLeft 93 - 1) :=
  cell_of_bounds (pl := (2047 / 1140 : ℝ)) (pr := (3079 / 1710 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_94.1 pt_93.2 (by norm_num)

theorem cell_94 : 16 / 100 * (Ssec (cellLeft 94) - cellLeft 94 / (cellLeft 94 - 1)) ≤
    cellLevel 94 - 2 / 10 ^ 6 - cellLeft 94 / (cellLeft 94 - 1) :=
  cell_of_bounds (pl := (3079 / 1710 : ℝ)) (pr := (65 / 36 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_95.1 pt_94.2 (by norm_num)

theorem cell_95 : 16 / 100 * (Ssec (cellLeft 95) - cellLeft 95 / (cellLeft 95 - 1)) ≤
    cellLevel 95 - 2 / 10 ^ 6 - cellLeft 95 / (cellLeft 95 - 1) :=
  cell_of_bounds (pl := (65 / 36 : ℝ)) (pr := (172 / 95 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_96.1 pt_95.2 (by norm_num)

theorem cell_96 : 16 / 100 * (Ssec (cellLeft 96) - cellLeft 96 / (cellLeft 96 - 1)) ≤
    cellLevel 96 - 2 / 10 ^ 6 - cellLeft 96 / (cellLeft 96 - 1) :=
  cell_of_bounds (pl := (172 / 95 : ℝ)) (pr := (6209 / 3420 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_97.1 pt_96.2 (by norm_num)

theorem cell_97 : 16 / 100 * (Ssec (cellLeft 97) - cellLeft 97 / (cellLeft 97 - 1)) ≤
    cellLevel 97 - 2 / 10 ^ 6 - cellLeft 97 / (cellLeft 97 - 1) :=
  cell_of_bounds (pl := (6209 / 3420 : ℝ)) (pr := (3113 / 1710 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_98.1 pt_97.2 (by norm_num)

theorem cell_98 : 16 / 100 * (Ssec (cellLeft 98) - cellLeft 98 / (cellLeft 98 - 1)) ≤
    cellLevel 98 - 2 / 10 ^ 6 - cellLeft 98 / (cellLeft 98 - 1) :=
  cell_of_bounds (pl := (3113 / 1710 : ℝ)) (pr := (2081 / 1140 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_99.1 pt_98.2 (by norm_num)

theorem cell_99 : 16 / 100 * (Ssec (cellLeft 99) - cellLeft 99 / (cellLeft 99 - 1)) ≤
    cellLevel 99 - 2 / 10 ^ 6 - cellLeft 99 / (cellLeft 99 - 1) :=
  cell_of_bounds (pl := (2081 / 1140 : ℝ)) (pr := (313 / 171 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_100.1 pt_99.2 (by norm_num)

theorem cell_100 : 16 / 100 * (Ssec (cellLeft 100) - cellLeft 100 / (cellLeft 100 - 1)) ≤
    cellLevel 100 - 2 / 10 ^ 6 - cellLeft 100 / (cellLeft 100 - 1) :=
  cell_of_bounds (pl := (313 / 171 : ℝ)) (pr := (6277 / 3420 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_101.1 pt_100.2 (by norm_num)

theorem cell_101 : 16 / 100 * (Ssec (cellLeft 101) - cellLeft 101 / (cellLeft 101 - 1)) ≤
    cellLevel 101 - 2 / 10 ^ 6 - cellLeft 101 / (cellLeft 101 - 1) :=
  cell_of_bounds (pl := (6277 / 3420 : ℝ)) (pr := (1049 / 570 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_102.1 pt_101.2 (by norm_num)

theorem cell_102 : 16 / 100 * (Ssec (cellLeft 102) - cellLeft 102 / (cellLeft 102 - 1)) ≤
    cellLevel 102 - 2 / 10 ^ 6 - cellLeft 102 / (cellLeft 102 - 1) :=
  cell_of_bounds (pl := (1049 / 570 : ℝ)) (pr := (6311 / 3420 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_103.1 pt_102.2 (by norm_num)

theorem cell_103 : 16 / 100 * (Ssec (cellLeft 103) - cellLeft 103 / (cellLeft 103 - 1)) ≤
    cellLevel 103 - 2 / 10 ^ 6 - cellLeft 103 / (cellLeft 103 - 1) :=
  cell_of_bounds (pl := (6311 / 3420 : ℝ)) (pr := (1582 / 855 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_104.1 pt_103.2 (by norm_num)

theorem cell_104 : 16 / 100 * (Ssec (cellLeft 104) - cellLeft 104 / (cellLeft 104 - 1)) ≤
    cellLevel 104 - 2 / 10 ^ 6 - cellLeft 104 / (cellLeft 104 - 1) :=
  cell_of_bounds (pl := (1582 / 855 : ℝ)) (pr := (141 / 76 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_105.1 pt_104.2 (by norm_num)

theorem cell_105 : 16 / 100 * (Ssec (cellLeft 105) - cellLeft 105 / (cellLeft 105 - 1)) ≤
    cellLevel 105 - 2 / 10 ^ 6 - cellLeft 105 / (cellLeft 105 - 1) :=
  cell_of_bounds (pl := (141 / 76 : ℝ)) (pr := (3181 / 1710 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_106.1 pt_105.2 (by norm_num)

theorem cell_106 : 16 / 100 * (Ssec (cellLeft 106) - cellLeft 106 / (cellLeft 106 - 1)) ≤
    cellLevel 106 - 2 / 10 ^ 6 - cellLeft 106 / (cellLeft 106 - 1) :=
  cell_of_bounds (pl := (3181 / 1710 : ℝ)) (pr := (6379 / 3420 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_107.1 pt_106.2 (by norm_num)

theorem cell_107 : 16 / 100 * (Ssec (cellLeft 107) - cellLeft 107 / (cellLeft 107 - 1)) ≤
    cellLevel 107 - 2 / 10 ^ 6 - cellLeft 107 / (cellLeft 107 - 1) :=
  cell_of_bounds (pl := (6379 / 3420 : ℝ)) (pr := (533 / 285 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_108.1 pt_107.2 (by norm_num)

theorem cell_108 : 16 / 100 * (Ssec (cellLeft 108) - cellLeft 108 / (cellLeft 108 - 1)) ≤
    cellLevel 108 - 2 / 10 ^ 6 - cellLeft 108 / (cellLeft 108 - 1) :=
  cell_of_bounds (pl := (533 / 285 : ℝ)) (pr := (6413 / 3420 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_109.1 pt_108.2 (by norm_num)

theorem cell_109 : 16 / 100 * (Ssec (cellLeft 109) - cellLeft 109 / (cellLeft 109 - 1)) ≤
    cellLevel 109 - 2 / 10 ^ 6 - cellLeft 109 / (cellLeft 109 - 1) :=
  cell_of_bounds (pl := (6413 / 3420 : ℝ)) (pr := (643 / 342 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_110.1 pt_109.2 (by norm_num)

theorem cell_110 : 16 / 100 * (Ssec (cellLeft 110) - cellLeft 110 / (cellLeft 110 - 1)) ≤
    cellLevel 110 - 2 / 10 ^ 6 - cellLeft 110 / (cellLeft 110 - 1) :=
  cell_of_bounds (pl := (643 / 342 : ℝ)) (pr := (2149 / 1140 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_111.1 pt_110.2 (by norm_num)

theorem cell_111 : 16 / 100 * (Ssec (cellLeft 111) - cellLeft 111 / (cellLeft 111 - 1)) ≤
    cellLevel 111 - 2 / 10 ^ 6 - cellLeft 111 / (cellLeft 111 - 1) :=
  cell_of_bounds (pl := (2149 / 1140 : ℝ)) (pr := (1616 / 855 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_112.1 pt_111.2 (by norm_num)

theorem cell_112 : 16 / 100 * (Ssec (cellLeft 112) - cellLeft 112 / (cellLeft 112 - 1)) ≤
    cellLevel 112 - 2 / 10 ^ 6 - cellLeft 112 / (cellLeft 112 - 1) :=
  cell_of_bounds (pl := (1616 / 855 : ℝ)) (pr := (6481 / 3420 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_113.1 pt_112.2 (by norm_num)

theorem cell_113 : 16 / 100 * (Ssec (cellLeft 113) - cellLeft 113 / (cellLeft 113 - 1)) ≤
    cellLevel 113 - 2 / 10 ^ 6 - cellLeft 113 / (cellLeft 113 - 1) :=
  cell_of_bounds (pl := (6481 / 3420 : ℝ)) (pr := (19 / 10 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_114.1 pt_113.2 (by norm_num)

theorem cell_114 : 16 / 100 * (Ssec (cellLeft 114) - cellLeft 114 / (cellLeft 114 - 1)) ≤
    cellLevel 114 - 2 / 10 ^ 6 - cellLeft 114 / (cellLeft 114 - 1) :=
  cell_of_bounds (pl := (19 / 10 : ℝ)) (pr := (381 / 200 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_115.1 pt_114.2 (by norm_num)

theorem cell_115 : 16 / 100 * (Ssec (cellLeft 115) - cellLeft 115 / (cellLeft 115 - 1)) ≤
    cellLevel 115 - 2 / 10 ^ 6 - cellLeft 115 / (cellLeft 115 - 1) :=
  cell_of_bounds (pl := (381 / 200 : ℝ)) (pr := (191 / 100 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_116.1 pt_115.2 (by norm_num)

theorem cell_116 : 16 / 100 * (Ssec (cellLeft 116) - cellLeft 116 / (cellLeft 116 - 1)) ≤
    cellLevel 116 - 2 / 10 ^ 6 - cellLeft 116 / (cellLeft 116 - 1) :=
  cell_of_bounds (pl := (191 / 100 : ℝ)) (pr := (383 / 200 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_117.1 pt_116.2 (by norm_num)

theorem cell_117 : 16 / 100 * (Ssec (cellLeft 117) - cellLeft 117 / (cellLeft 117 - 1)) ≤
    cellLevel 117 - 2 / 10 ^ 6 - cellLeft 117 / (cellLeft 117 - 1) :=
  cell_of_bounds (pl := (383 / 200 : ℝ)) (pr := (48 / 25 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_118.1 pt_117.2 (by norm_num)

theorem cell_118 : 16 / 100 * (Ssec (cellLeft 118) - cellLeft 118 / (cellLeft 118 - 1)) ≤
    cellLevel 118 - 2 / 10 ^ 6 - cellLeft 118 / (cellLeft 118 - 1) :=
  cell_of_bounds (pl := (48 / 25 : ℝ)) (pr := (77 / 40 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_119.1 pt_118.2 (by norm_num)

theorem cell_119 : 16 / 100 * (Ssec (cellLeft 119) - cellLeft 119 / (cellLeft 119 - 1)) ≤
    cellLevel 119 - 2 / 10 ^ 6 - cellLeft 119 / (cellLeft 119 - 1) :=
  cell_of_bounds (pl := (77 / 40 : ℝ)) (pr := (193 / 100 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_120.1 pt_119.2 (by norm_num)

theorem cell_120 : 16 / 100 * (Ssec (cellLeft 120) - cellLeft 120 / (cellLeft 120 - 1)) ≤
    cellLevel 120 - 2 / 10 ^ 6 - cellLeft 120 / (cellLeft 120 - 1) :=
  cell_of_bounds (pl := (193 / 100 : ℝ)) (pr := (387 / 200 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_121.1 pt_120.2 (by norm_num)

theorem cell_121 : 16 / 100 * (Ssec (cellLeft 121) - cellLeft 121 / (cellLeft 121 - 1)) ≤
    cellLevel 121 - 2 / 10 ^ 6 - cellLeft 121 / (cellLeft 121 - 1) :=
  cell_of_bounds (pl := (387 / 200 : ℝ)) (pr := (97 / 50 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_122.1 pt_121.2 (by norm_num)

theorem cell_122 : 16 / 100 * (Ssec (cellLeft 122) - cellLeft 122 / (cellLeft 122 - 1)) ≤
    cellLevel 122 - 2 / 10 ^ 6 - cellLeft 122 / (cellLeft 122 - 1) :=
  cell_of_bounds (pl := (97 / 50 : ℝ)) (pr := (389 / 200 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_123.1 pt_122.2 (by norm_num)

theorem cell_123 : 16 / 100 * (Ssec (cellLeft 123) - cellLeft 123 / (cellLeft 123 - 1)) ≤
    cellLevel 123 - 2 / 10 ^ 6 - cellLeft 123 / (cellLeft 123 - 1) :=
  cell_of_bounds (pl := (389 / 200 : ℝ)) (pr := (39 / 20 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_124.1 pt_123.2 (by norm_num)

theorem cell_124 : 16 / 100 * (Ssec (cellLeft 124) - cellLeft 124 / (cellLeft 124 - 1)) ≤
    cellLevel 124 - 2 / 10 ^ 6 - cellLeft 124 / (cellLeft 124 - 1) :=
  cell_of_bounds (pl := (39 / 20 : ℝ)) (pr := (391 / 200 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_125.1 pt_124.2 (by norm_num)

theorem cell_125 : 16 / 100 * (Ssec (cellLeft 125) - cellLeft 125 / (cellLeft 125 - 1)) ≤
    cellLevel 125 - 2 / 10 ^ 6 - cellLeft 125 / (cellLeft 125 - 1) :=
  cell_of_bounds (pl := (391 / 200 : ℝ)) (pr := (49 / 25 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_126.1 pt_125.2 (by norm_num)

theorem cell_126 : 16 / 100 * (Ssec (cellLeft 126) - cellLeft 126 / (cellLeft 126 - 1)) ≤
    cellLevel 126 - 2 / 10 ^ 6 - cellLeft 126 / (cellLeft 126 - 1) :=
  cell_of_bounds (pl := (49 / 25 : ℝ)) (pr := (393 / 200 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_127.1 pt_126.2 (by norm_num)

theorem cell_127 : 16 / 100 * (Ssec (cellLeft 127) - cellLeft 127 / (cellLeft 127 - 1)) ≤
    cellLevel 127 - 2 / 10 ^ 6 - cellLeft 127 / (cellLeft 127 - 1) :=
  cell_of_bounds (pl := (393 / 200 : ℝ)) (pr := (197 / 100 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_128.1 pt_127.2 (by norm_num)

theorem cell_128 : 16 / 100 * (Ssec (cellLeft 128) - cellLeft 128 / (cellLeft 128 - 1)) ≤
    cellLevel 128 - 2 / 10 ^ 6 - cellLeft 128 / (cellLeft 128 - 1) :=
  cell_of_bounds (pl := (197 / 100 : ℝ)) (pr := (79 / 40 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_129.1 pt_128.2 (by norm_num)

theorem cell_129 : 16 / 100 * (Ssec (cellLeft 129) - cellLeft 129 / (cellLeft 129 - 1)) ≤
    cellLevel 129 - 2 / 10 ^ 6 - cellLeft 129 / (cellLeft 129 - 1) :=
  cell_of_bounds (pl := (79 / 40 : ℝ)) (pr := (99 / 50 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_130.1 pt_129.2 (by norm_num)

theorem cell_130 : 16 / 100 * (Ssec (cellLeft 130) - cellLeft 130 / (cellLeft 130 - 1)) ≤
    cellLevel 130 - 2 / 10 ^ 6 - cellLeft 130 / (cellLeft 130 - 1) :=
  cell_of_bounds (pl := (99 / 50 : ℝ)) (pr := (1981 / 1000 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_131.1 pt_130.2 (by norm_num)

theorem cell_131 : 16 / 100 * (Ssec (cellLeft 131) - cellLeft 131 / (cellLeft 131 - 1)) ≤
    cellLevel 131 - 2 / 10 ^ 6 - cellLeft 131 / (cellLeft 131 - 1) :=
  cell_of_bounds (pl := (1981 / 1000 : ℝ)) (pr := (991 / 500 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_132.1 pt_131.2 (by norm_num)

theorem cell_132 : 16 / 100 * (Ssec (cellLeft 132) - cellLeft 132 / (cellLeft 132 - 1)) ≤
    cellLevel 132 - 2 / 10 ^ 6 - cellLeft 132 / (cellLeft 132 - 1) :=
  cell_of_bounds (pl := (991 / 500 : ℝ)) (pr := (1983 / 1000 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_133.1 pt_132.2 (by norm_num)

theorem cell_133 : 16 / 100 * (Ssec (cellLeft 133) - cellLeft 133 / (cellLeft 133 - 1)) ≤
    cellLevel 133 - 2 / 10 ^ 6 - cellLeft 133 / (cellLeft 133 - 1) :=
  cell_of_bounds (pl := (1983 / 1000 : ℝ)) (pr := (248 / 125 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_134.1 pt_133.2 (by norm_num)

theorem cell_134 : 16 / 100 * (Ssec (cellLeft 134) - cellLeft 134 / (cellLeft 134 - 1)) ≤
    cellLevel 134 - 2 / 10 ^ 6 - cellLeft 134 / (cellLeft 134 - 1) :=
  cell_of_bounds (pl := (248 / 125 : ℝ)) (pr := (397 / 200 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_135.1 pt_134.2 (by norm_num)

theorem cell_135 : 16 / 100 * (Ssec (cellLeft 135) - cellLeft 135 / (cellLeft 135 - 1)) ≤
    cellLevel 135 - 2 / 10 ^ 6 - cellLeft 135 / (cellLeft 135 - 1) :=
  cell_of_bounds (pl := (397 / 200 : ℝ)) (pr := (993 / 500 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_136.1 pt_135.2 (by norm_num)

theorem cell_136 : 16 / 100 * (Ssec (cellLeft 136) - cellLeft 136 / (cellLeft 136 - 1)) ≤
    cellLevel 136 - 2 / 10 ^ 6 - cellLeft 136 / (cellLeft 136 - 1) :=
  cell_of_bounds (pl := (993 / 500 : ℝ)) (pr := (1987 / 1000 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_137.1 pt_136.2 (by norm_num)

theorem cell_137 : 16 / 100 * (Ssec (cellLeft 137) - cellLeft 137 / (cellLeft 137 - 1)) ≤
    cellLevel 137 - 2 / 10 ^ 6 - cellLeft 137 / (cellLeft 137 - 1) :=
  cell_of_bounds (pl := (1987 / 1000 : ℝ)) (pr := (497 / 250 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_138.1 pt_137.2 (by norm_num)

theorem cell_138 : 16 / 100 * (Ssec (cellLeft 138) - cellLeft 138 / (cellLeft 138 - 1)) ≤
    cellLevel 138 - 2 / 10 ^ 6 - cellLeft 138 / (cellLeft 138 - 1) :=
  cell_of_bounds (pl := (497 / 250 : ℝ)) (pr := (1989 / 1000 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_139.1 pt_138.2 (by norm_num)

theorem cell_139 : 16 / 100 * (Ssec (cellLeft 139) - cellLeft 139 / (cellLeft 139 - 1)) ≤
    cellLevel 139 - 2 / 10 ^ 6 - cellLeft 139 / (cellLeft 139 - 1) :=
  cell_of_bounds (pl := (1989 / 1000 : ℝ)) (pr := (199 / 100 : ℝ)) (κ := (13 / 20 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num)
    pt_140.1 pt_139.2 (by norm_num)

/-- All 140 cells: `16/100 · W(p_a) ≤ cellLevel i - 2e-6 - p_a/(p_a-1)`. -/
theorem cells_16 : ∀ i : ℕ, i < 140 →
    16 / 100 * (Ssec (cellLeft i) - cellLeft i / (cellLeft i - 1)) ≤
      cellLevel i - 2 / 10 ^ 6 - cellLeft i / (cellLeft i - 1) := by
  intro i hi
  interval_cases i
  · exact cell_0
  · exact cell_1
  · exact cell_2
  · exact cell_3
  · exact cell_4
  · exact cell_5
  · exact cell_6
  · exact cell_7
  · exact cell_8
  · exact cell_9
  · exact cell_10
  · exact cell_11
  · exact cell_12
  · exact cell_13
  · exact cell_14
  · exact cell_15
  · exact cell_16
  · exact cell_17
  · exact cell_18
  · exact cell_19
  · exact cell_20
  · exact cell_21
  · exact cell_22
  · exact cell_23
  · exact cell_24
  · exact cell_25
  · exact cell_26
  · exact cell_27
  · exact cell_28
  · exact cell_29
  · exact cell_30
  · exact cell_31
  · exact cell_32
  · exact cell_33
  · exact cell_34
  · exact cell_35
  · exact cell_36
  · exact cell_37
  · exact cell_38
  · exact cell_39
  · exact cell_40
  · exact cell_41
  · exact cell_42
  · exact cell_43
  · exact cell_44
  · exact cell_45
  · exact cell_46
  · exact cell_47
  · exact cell_48
  · exact cell_49
  · exact cell_50
  · exact cell_51
  · exact cell_52
  · exact cell_53
  · exact cell_54
  · exact cell_55
  · exact cell_56
  · exact cell_57
  · exact cell_58
  · exact cell_59
  · exact cell_60
  · exact cell_61
  · exact cell_62
  · exact cell_63
  · exact cell_64
  · exact cell_65
  · exact cell_66
  · exact cell_67
  · exact cell_68
  · exact cell_69
  · exact cell_70
  · exact cell_71
  · exact cell_72
  · exact cell_73
  · exact cell_74
  · exact cell_75
  · exact cell_76
  · exact cell_77
  · exact cell_78
  · exact cell_79
  · exact cell_80
  · exact cell_81
  · exact cell_82
  · exact cell_83
  · exact cell_84
  · exact cell_85
  · exact cell_86
  · exact cell_87
  · exact cell_88
  · exact cell_89
  · exact cell_90
  · exact cell_91
  · exact cell_92
  · exact cell_93
  · exact cell_94
  · exact cell_95
  · exact cell_96
  · exact cell_97
  · exact cell_98
  · exact cell_99
  · exact cell_100
  · exact cell_101
  · exact cell_102
  · exact cell_103
  · exact cell_104
  · exact cell_105
  · exact cell_106
  · exact cell_107
  · exact cell_108
  · exact cell_109
  · exact cell_110
  · exact cell_111
  · exact cell_112
  · exact cell_113
  · exact cell_114
  · exact cell_115
  · exact cell_116
  · exact cell_117
  · exact cell_118
  · exact cell_119
  · exact cell_120
  · exact cell_121
  · exact cell_122
  · exact cell_123
  · exact cell_124
  · exact cell_125
  · exact cell_126
  · exact cell_127
  · exact cell_128
  · exact cell_129
  · exact cell_130
  · exact cell_131
  · exact cell_132
  · exact cell_133
  · exact cell_134
  · exact cell_135
  · exact cell_136
  · exact cell_137
  · exact cell_138
  · exact cell_139

end NewRows11bCells

end P18
