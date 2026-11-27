import OMAReductions.R_OeisA262446_conjecture_2_R1
import Mathlib

/-! A finite certificate for the seven singleton counts based on triangular prime counts. -/
open Finset

namespace A262446Finite

private def table : Array ℕ := #[0, 1, 2, 4, 5, 6, 8, 10, 12, 14, 16, 19, 22, 24,
  27, 30, 33, 36, 39, 43, 47, 50, 54, 59, 62, 66, 70, 75,
  79, 84, 90, 94, 99, 102, 108, 115, 121, 126, 131, 137, 142, 149,
  154, 161, 167, 174, 180, 189, 193, 200, 205, 217, 220, 226, 235, 242,
  251, 259, 267, 274, 282, 290, 297, 306, 313, 324, 329, 338, 348, 358,
  367, 375, 381, 393, 403, 414, 423, 431, 440, 446, 457, 467, 478, 487,
  500, 510, 522, 531, 542, 552, 564, 574, 587, 596, 607, 618, 630, 640,
  650, 662, 676, 686, 697, 708, 721, 734, 747, 758, 775, 783, 796, 809,
  824, 836, 847, 859, 873, 887, 903, 914, 928, 938, 950, 968, 982, 994,
  1007, 1022, 1035, 1049, 1061, 1077, 1094, 1108, 1124, 1138, 1152, 1170, 1184, 1199,
  1218, 1231, 1246, 1262, 1277, 1290, 1308, 1322, 1337, 1354, 1369, 1383, 1398, 1411,
  1430, 1446, 1463, 1480, 1500, 1519, 1532, 1553, 1570, 1586, 1602, 1619, 1637, 1655,
  1670, 1683, 1701, 1720, 1743, 1757, 1776, 1800, 1816, 1837, 1857, 1876, 1891, 1908,
  1926, 1943, 1962, 1981, 2000, 2021, 2039, 2057, 2080, 2101, 2122, 2137, 2152, 2169,
  2188, 2213, 2230, 2250, 2272, 2293, 2313, 2331, 2352, 2373, 2394, 2417, 2438, 2460,
  2484, 2503, 2524, 2547, 2565, 2591, 2609, 2631, 2654, 2680, 2700, 2721, 2738, 2760,
  2781, 2803, 2825, 2847, 2869, 2893, 2915, 2939, 2963, 2984, 3004, 3022, 3053, 3074,
  3095, 3124, 3148, 3169, 3195, 3217, 3238, 3259, 3282, 3302, 3330, 3352, 3380, 3402,
  3424, 3447, 3476, 3503, 3525, 3553, 3578, 3607, 3633, 3653, 3679, 3707, 3732, 3754,
  3780, 3801, 3829, 3854, 3879, 3908, 3935, 3960, 3990, 4010, 4034, 4059, 4086, 4112,
  4141, 4166, 4196, 4221, 4242, 4266, 4295, 4324, 4353, 4381, 4411, 4445, 4473, 4502,
  4522, 4550, 4572, 4604, 4632, 4661, 4687, 4714, 4739, 4765, 4794, 4822, 4849, 4874,
  4905, 4935, 4963, 4990, 5022, 5051, 5081, 5110, 5142, 5172, 5197, 5224, 5255, 5289,
  5319, 5349, 5375, 5406]

private def cut (i : ℕ) : ℕ := Nat.triangular i + 2

private def fastPrime (p : ℕ) : Prop := 2 ≤ p ∧ p.minFac = p

private instance (p : ℕ) : Decidable (fastPrime p) :=
  inferInstanceAs (Decidable (2 ≤ p ∧ p.minFac = p))

private def step (i : ℕ) : ℕ := ((Ico (cut i) (cut (i + 1))).filter fastPrime).card

private theorem b_succ (i : ℕ) : OeisA262446.b (i + 1) = OeisA262446.b i + step i := by
  unfold OeisA262446.b Nat.primeCounting Nat.primeCounting'
  simp only [Nat.count_eq_card_filter_range]
  change ((range (cut (i + 1))).filter Nat.Prime).card =
    ((range (cut i)).filter Nat.Prime).card + step i
  have hstep : cut i ≤ cut (i + 1) := by
    have hh := Nat.div_le_div_right (c := 2)
      (Nat.mul_le_mul (Nat.le_succ i) (Nat.le_succ (i + 1)))
    exact Nat.add_le_add_right hh 2
  have hUnion : range (cut i) ∪ Ico (cut i) (cut (i + 1)) = range (cut (i + 1)) := by
    ext x
    simp only [mem_union, mem_range, mem_Ico]
    omega
  have hd : Disjoint ((range (cut i)).filter Nat.Prime)
      ((Ico (cut i) (cut (i + 1))).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro x h hx
    have h1 := mem_range.mp (mem_filter.mp h).1
    have h2 := (mem_Ico.mp (mem_filter.mp hx).1).1
    omega
  rw [← hUnion, filter_union, card_union_of_disjoint hd]
  congr 1
  exact congrArg Finset.card (filter_congr fun n _ => Nat.prime_def_minFac)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
private theorem step_cert : ∀ i : Fin 325, table[i.val + 1]! = table[i.val]! + step i.val := by
  decide +kernel

private theorem table_eq (i : ℕ) (hi : i ≤ 325) : OeisA262446.b i = table[i]! := by
  induction i with
  | zero => decide +kernel
  | succ i ih =>
    rw [b_succ, ih (by omega)]
    exact (step_cert ⟨i, by omega⟩).symm

private def count (n : ℕ) : ℕ :=
  ∑ k ∈ Ico 1 n, ((Ico (k + 1) n).filter (fun m => table[n]! = table[k]! + table[m]!)).card

private theorem a_eq (n : ℕ) (hn : n ≤ 325) : OeisA262446.a n = count n := by
  unfold OeisA262446.a count
  apply sum_congr rfl
  intro k hk
  rw [table_eq n hn, table_eq k (by have := (mem_Ico.mp hk).2; omega)]
  exact congrArg Finset.card (filter_congr fun m hm => by
    rw [table_eq m (by have := (mem_Ico.mp hm).2; omega)])

set_option maxRecDepth 22000 in
set_option maxHeartbeats 0 in
theorem ones (n : ℕ) (hn : n ∈ ({4, 6, 11, 21, 54, 253, 325} : Finset ℕ)) :
    OeisA262446.a n = 1 := by
  simp only [mem_insert, mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rw [a_eq _ (by decide)]; decide +kernel

end A262446Finite

theorem OMA.solution : OMA.R_OeisA262446_conjecture_2_R1.H1 := A262446Finite.ones