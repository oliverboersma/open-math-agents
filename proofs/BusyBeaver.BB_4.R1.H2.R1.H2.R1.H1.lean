import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1
open Turing Turing.BusyBeaver

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1.H1 := by
  rintro M _ ⟨i,j,hij,_,c,hi,_,hj,_⟩ hhalt
  obtain ⟨n,hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hhalt
  let F (x : Option (Cfg (Fin 2) (Fin 4))) := x.bind M.step
  let start : Option (Cfg (Fin 2) (Fin 4)) := some (Machine.init [])
  change F^[i] start = some c at hi
  change F^[j] start = some c at hj
  let d := j-i
  have hd : 0 < d := Nat.sub_pos_of_lt hij
  have loop : F^[d] (some c) = some c := by
    rw [← hi, ← Function.iterate_add_apply, show d+i=j by dsimp [d]; omega]
    exact hj.trans hi.symm
  have returns (r : ℕ) : F^[d*r+i] start = some c := by
    induction r with
    | zero => simpa using hi
    | succ r ih =>
      rw [show d*(r+1)+i = d+(d*r+i) by ring, Function.iterate_add_apply, ih, loop]
  have far : n+1 ≤ d*(n+1)+i := by
    have := Nat.le_mul_of_pos_left (n+1) hd
    omega
  have hnone := Machine.multiStep_eq_none_mono (M:=M) hn far
  change F^[d*(n+1)+i] start = none at hnone
  rw [returns] at hnone
  contradiction
