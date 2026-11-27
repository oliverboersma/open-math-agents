import OMAReductions.R_Erdos422_erdos_422_variants_well_defined_R1
import Mathlib

/-! Build the Hofstadter Q sequence by storing its previously computed entries. -/

namespace HofstadterCheckedPrefix

private def read (a : Array ℕ) (i : ℕ) : ℕ := a[i]?.getD 0

private def next (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  if n ≤ 2 then 1 else
    let u := a (n - 1)
    let v := a (n - 2)
    if 0 < u ∧ u < n ∧ 0 < v ∧ v < n then a (n - u) + a (n - v) else 0

private def table : ℕ → Array ℕ
  | 0 => #[]
  | n + 1 => let a := table n; a.push (next n (read a))

private theorem prefix_size (n : ℕ) : (table n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [table, Array.size_push, ih]

private def q (n : ℕ) : ℕ := read (table (n+1)) n

private theorem read_prefix {n i : ℕ} (hi : i < n) : read (table n) i = q i := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : i < n
      · have hi' : i < (table n).size := by simpa only [prefix_size] using h
        rw [← ih h]
        unfold read
        simp only [table, Array.getElem?_push, if_neg hi'.ne]
      · have hei : i = n := by omega
        subst n
        rfl

private theorem q_eq_next (n : ℕ) : q n = next n (read (table n)) := by
  unfold q read
  rw [table, Array.getElem?_push, prefix_size, if_pos rfl, Option.getD_some]
  rfl

private theorem q_recurrence (n : ℕ) (hn : 2 < n) :
    q n = if 0 < q (n - 1) ∧ q (n - 1) < n ∧ 0 < q (n - 2) ∧ q (n - 2) < n then
      q (n - q (n - 1)) + q (n - q (n - 2)) else 0 := by
  rw [q_eq_next, next, if_neg (by omega),
    read_prefix (by omega : n - 1 < n), read_prefix (by omega : n - 2 < n)]
  dsimp only
  split
  · rw [read_prefix, read_prefix] <;> omega
  · rfl

private def checkedBlocks : Array (Array ℕ) := #[
  #[1, 1, 1, 2, 3, 3, 4, 5, 5, 6, 6, 6, 8, 8, 8, 10, 9, 10, 11, 11, 12, 12, 12, 12, 16, 14, 14, 16, 16, 16, 16, 20],
  #[17, 17, 20, 21, 19, 20, 22, 21, 22, 23, 23, 24, 24, 24, 24, 24, 32, 24, 25, 30, 28, 26, 30, 30, 28, 32, 30, 32, 32, 32, 32, 40],
  #[33, 31, 38, 35, 33, 39, 40, 37, 38, 40, 39, 40, 39, 42, 40, 41, 43, 44, 43, 43, 46, 44, 45, 47, 47, 46, 48, 48, 48, 48, 48, 48],
  #[64, 41, 52, 54, 56, 48, 54, 54, 50, 60, 52, 54, 58, 60, 53, 60, 60, 52, 62, 66, 55, 62, 68, 62, 58, 72, 58, 61, 78, 57, 71, 68],
  #[64, 63, 73, 63, 71, 72, 72, 80, 61, 71, 77, 65, 80, 71, 69, 77, 75, 73, 77, 79, 76, 80, 79, 75, 82, 77, 80, 80, 78, 83, 83, 78],
  #[85, 82, 85, 84, 84, 88, 83, 87, 88, 87, 86, 90, 88, 87, 92, 90, 91, 92, 92, 94, 92, 93, 94, 94, 96, 94, 96, 96, 96, 96, 96, 96],
  #[128, 72, 96, 115, 100, 84, 114, 110, 93, 106, 124, 82, 101, 111, 108, 118, 104, 108, 106, 114, 104, 114, 109, 100, 109, 120, 112, 108, 118, 106, 105, 130],
  #[110, 114, 115, 112, 107, 120, 114, 122, 121, 120, 114, 138, 110, 122, 119, 120, 130, 132, 113, 133, 123, 118, 125, 121, 129, 122, 136, 129, 116, 149, 137, 120],
  #[123, 143, 146, 107, 139, 138, 139, 135, 120, 146, 135, 143, 129, 151, 133, 135, 136, 148, 148, 136, 144, 143, 152, 129, 139, 151, 140, 148, 136, 151, 159, 125],
  #[147, 153, 148, 154, 152, 136, 152, 155, 146, 144, 162, 151, 157, 154, 149, 160, 155, 152, 155, 162, 154, 159, 153, 165, 157, 154, 168, 161, 156, 160, 168, 153],
  #[169, 170, 159, 161, 172, 161, 168, 161, 172, 171, 161, 171, 172, 167, 172, 172, 168, 175, 170, 171, 173, 174, 175, 175, 174, 176, 174, 177, 182, 175, 178, 178],
  #[184, 177, 178, 184, 180, 179, 186, 179, 185, 185, 184, 186, 184, 187, 188, 186, 186, 188, 190, 187, 188, 190, 192, 188, 192, 190, 192, 192, 192, 192, 192, 192],
  #[256, 135, 202, 210, 188, 200, 220, 186, 196, 202, 242, 149, 201, 229, 171, 193, 238, 188, 193, 206, 228, 202, 193, 220, 196, 210, 202, 214, 220, 182, 217, 234],
  #[204, 208, 215, 215, 222, 218, 194, 231, 186, 216, 236, 210, 240, 204, 211, 230, 230, 164, 234, 241, 239, 214, 220, 222, 230, 222, 222, 212, 226, 228, 230, 228],
  #[230, 214, 228, 252, 203, 242, 233, 219, 252, 230, 215, 243, 238, 242, 228, 244, 228, 228, 238, 240, 221, 249, 228, 238, 237, 248, 237, 231, 238, 245, 250, 234],
  #[239, 234, 262, 228, 228, 286, 239, 235, 271, 249, 240, 242, 252, 261, 233, 253, 268, 243, 234, 269, 257, 244, 264, 227, 273, 273, 240, 257, 258, 245, 262, 257],
  #[256]]

private def checkedValue (n : ℕ) : ℕ :=
  read (checkedBlocks[n / 32]?.getD #[]) (n % 32)


set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem checkedValues_ok : (List.range 513).all (fun n =>
    decide (0 < checkedValue n ∧ checkedValue n = next n checkedValue)) = true := by
  decide +kernel

private theorem checkedValue_spec (n : ℕ) (hn : n < 513) :
    0 < checkedValue n ∧ checkedValue n = next n checkedValue :=
  of_decide_eq_true (List.all_eq_true.mp checkedValues_ok n (List.mem_range.mpr hn))

private theorem q_checked (n : ℕ) (hn : n < 513) : q n = checkedValue n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [(checkedValue_spec n hn).2]
      by_cases hbase : n ≤ 2
      · rw [q_eq_next, next, next, if_pos hbase, if_pos hbase]
      · rw [q_recurrence n (by omega), next, if_neg hbase]
        rw [ih (n-1) (by omega) (by omega), ih (n-2) (by omega) (by omega)]
        dsimp only
        split
        · rw [ih (n - _) (by omega) (by omega), ih (n - _) (by omega) (by omega)]
        · rfl


theorem main :
    ∃ q : ℕ → ℕ, q 1 = 1 ∧ q 2 = 1 ∧
      (∀ n : ℕ, 2 < n → q n =
        if 0 < q (n - 1) ∧ q (n - 1) < n ∧ 0 < q (n - 2) ∧ q (n - 2) < n then
          q (n - q (n - 1)) + q (n - q (n - 2)) else 0) ∧
      (∀ n : ℕ, 0 < n → n ≤ 512 → 0 < q n) := by
  refine ⟨q, by decide, by decide, q_recurrence, ?_⟩
  intro n _ hn
  rw [q_checked n (by omega)]
  exact (checkedValue_spec n (by omega)).1

end HofstadterCheckedPrefix

theorem OMA.solution : OMA.R_Erdos422_erdos_422_variants_well_defined_R1.H1 :=
  HofstadterCheckedPrefix.main