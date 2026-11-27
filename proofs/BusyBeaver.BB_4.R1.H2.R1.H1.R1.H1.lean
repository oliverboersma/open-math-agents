import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1

/-! LOOP1: a repeated blank-tape configuration within 107 steps implies nonhalting. -/
-- Credit: @pageman

open Turing Turing.BusyBeaver

namespace OMA.BB4Loop1

theorem joinSteps (M : Machine (Fin 2) (Fin 4)) {a b c : Cfg (Fin 2) (Fin 4)} {n k : ℕ}
    (h : M.multiStep a n = some b) (g : M.multiStep b k = some c) :
    M.multiStep a (n + k) = some c := by
  unfold Machine.multiStep at *
  rw [Nat.add_comm n k, Function.iterate_add_apply, h, g]

theorem period_live (M : Machine (Fin 2) (Fin 4)) {c : Cfg (Fin 2) (Fin 4)} {i j : ℕ}
    (hij : i < j) (hi : M.multiStep (Machine.init []) i = some c)
    (hj : M.multiStep (Machine.init []) j = some c) :
    ∀ t : ℕ, M.multiStep (Machine.init []) (i + t * (j - i)) = some c := by
  have hseg : M.multiStep c (j - i) = some c := by
    have hij' : i + (j - i) = j := Nat.add_sub_of_le (Nat.le_of_lt hij)
    unfold Machine.multiStep at hi hj ⊢
    have step := Function.iterate_add_apply (fun x => x.bind M.step) (j - i) i (some (Machine.init []))
    -- iterate (j-i+i) = iterate i ∘ iterate (j-i) wait - add_comm order
    -- We need iterate (i+(j-i)) (some init) = iterate (j-i) (iterate i (some init))
    have reorder : (fun x => x.bind M.step)^[i + (j - i)] (some (Machine.init [])) =
        (fun x => x.bind M.step)^[j - i] ((fun x => x.bind M.step)^[i] (some (Machine.init []))) := by
      rw [Nat.add_comm, Function.iterate_add_apply]
    have hj' : (fun x => x.bind M.step)^[j] (some (Machine.init [])) = some c := hj
    have : (fun x => x.bind M.step)^[i + (j - i)] (some (Machine.init [])) = some c := by
      simpa [hij'] using hj'
    have hi' : (fun x => x.bind M.step)^[i] (some (Machine.init [])) = some c := hi
    simpa [reorder, hi'] using this
  intro t
  induction t with
  | zero => simpa using hi
  | succ t ih =>
    have : i + (t + 1) * (j - i) = i + t * (j - i) + (j - i) := by ring
    rw [this]
    exact joinSteps M ih hseg

theorem cycle_never_halts (M : Machine (Fin 2) (Fin 4)) {c : Cfg (Fin 2) (Fin 4)} {i j : ℕ}
    (hij : i < j) (hi : M.multiStep (Machine.init []) i = some c)
    (hj : M.multiStep (Machine.init []) j = some c) : ¬ M.IsHalting := by
  intro halts
  obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
  let t := k + 1
  have live := period_live M hij hi hj t
  have hge : k + 1 ≤ i + t * (j - i) := by
    have : 1 ≤ j - i := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hij)
    have : t ≤ t * (j - i) := Nat.le_mul_of_pos_right t this
    omega
  have hnone := Machine.multiStep_eq_none_mono hk hge
  rw [live] at hnone
  cases hnone

end OMA.BB4Loop1

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1.H1 := by
  intro M _hFirst
  rintro ⟨i, j, hij, _hjle, c, hi, _hs1, hj, _hs2⟩
  exact OMA.BB4Loop1.cycle_never_halts M hij hi hj
