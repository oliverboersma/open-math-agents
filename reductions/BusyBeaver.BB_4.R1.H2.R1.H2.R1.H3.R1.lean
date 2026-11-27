import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1

/-! Read the initial rightward sweep into fresh blank cells. A halting survivor must
turn left before revisiting a state. Name the states in order of first encounter.
Only sweeps of lengths one, two and three remain. The conjugacy and blank-tail
invariant adapt the first-transition normalization of @Halldon. -/
namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1
open Turing Turing.BusyBeaver

private theorem closed_right (M : Machine (Fin 2) (Fin 4)) (S : Finset (Fin 4))
    (start : 0 ∈ S) (closed : ∀ q ∈ S, ∃ r ∈ S, ∃ a,
      M q 0 = some (some r, Stmt.write a Dir.right)) : ¬ M.IsHalting := by
  let blank := ListBlank.mk ([] : List (Fin 2))
  have trace (n : ℕ) : ∃ q ∈ S, ∃ t : Tape (Fin 2),
      M.multiStep (Machine.init []) n = some ⟨some q,t⟩ ∧ t.head = 0 ∧ t.right = blank := by
    induction n with
    | zero => exact ⟨0,start,Tape.mk₁ [],rfl,rfl,rfl⟩
    | succ n ih =>
      obtain ⟨q,hq,t,ht,hb,hr⟩ := ih
      obtain ⟨r,hr',a,h⟩ := closed q hq
      refine ⟨r,hr',(t.write a).move .right,?_,?_,?_⟩
      · simp [Machine.multiStep_succ,ht,Machine.step,hb,h]
      · simp [Tape.write,Tape.move,hr,blank]
      · simp [Tape.write,Tape.move,hr,blank]
  intro halts
  obtain ⟨n,hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
  obtain ⟨_,_,_,ht,_,_⟩ := trace (n+1)
  rw [Machine.HaltsAfter,ht] at hn
  contradiction

private theorem advance (M : Machine (Fin 2) (Fin 4)) {n : ℕ} {q r : Fin 4} {a : Fin 2}
    (arrived : ∃ t : Tape (Fin 2), M.multiStep (Machine.init []) n = some ⟨some q,t⟩ ∧
      t.head = 0 ∧ t.right = ListBlank.mk []) (move : M q 0 = some (some r,Stmt.write a .right)) :
    ∃ t : Tape (Fin 2), M.multiStep (Machine.init []) (n+1) = some ⟨some r,t⟩ ∧
      t.head = 0 ∧ t.right = ListBlank.mk [] := by
  obtain ⟨t,ht,hb,hr⟩ := arrived
  refine ⟨(t.write a).move .right,?_,?_,?_⟩
  · simp [Machine.multiStep_succ,ht,Machine.step,hb,move]
  · simp [Tape.write,Tape.move,hr]
  · simp [Tape.write,Tape.move,hr]

private theorem inspect_blank (M : Machine (Fin 2) (Fin 4)) {n : ℕ} {q : Fin 4}
    (arrived : ∃ t : Tape (Fin 2), M.multiStep (Machine.init []) n = some ⟨some q,t⟩ ∧
      t.head = 0 ∧ t.right = ListBlank.mk []) (hn : n+2 ≤ 107)
    (late : ¬ M.HaltsAfter (Machine.init []) 107) :
    ∃ r a d, M q 0 = some (some r,Stmt.write a d) := by
  obtain ⟨t,ht,hb,_⟩ := arrived
  cases h : M q 0 with
  | none =>
    exfalso
    apply late
    change M.multiStep (Machine.init []) 108 = none
    apply Machine.multiStep_eq_none_mono (n := n+1) _ (by omega)
    simp [Machine.multiStep_succ,ht,Machine.step,hb,h]
  | some cmd =>
    obtain ⟨s,a,d⟩ := cmd
    cases s with
    | none =>
      exfalso
      apply late
      change M.multiStep (Machine.init []) 108 = none
      apply Machine.multiStep_eq_none_mono (n := n+2) _ (by omega)
      rw [show n+2=n+1+1 by omega,Machine.multiStep_succ,Machine.multiStep_succ,ht]
      simp [Machine.step,hb,h]
    | some r => exact ⟨r,a,d,rfl⟩

private theorem normalize (M : Machine (Fin 2) (Fin 4)) (q : Fin 4) (a : Fin 2) (d : Dir)
    (first : M 0 0 = some (some 1, Stmt.write 1 .right))
    (second : M 1 0 = some (some q, Stmt.write a d)) :
    ∃ (N : Machine (Fin 2) (Fin 4)) (r : Fin 4), r.val ≤ 2 ∧
      N 0 0 = some (some 1, Stmt.write 1 .right) ∧ N 1 0 = some (some r, Stmt.write a d) ∧
      ∀ n, N.HaltsAfter (Machine.init []) n ↔ M.HaltsAfter (Machine.init []) n := by
  classical
  let e : Fin 4 ≃ Fin 4 := if q = 3 then Equiv.swap 2 3 else Equiv.refl _
  have h0 : e 0 = 0 := by unfold e; split <;> decide
  have h1 : e 1 = 1 := by unfold e; split <;> decide
  have hr : (e q).val ≤ 2 := by fin_cases q <;> decide
  let N : Machine (Fin 2) (Fin 4) := fun s b =>
    (M (e.symm s) b).map fun (r,z) => (r.map e,z)
  let image (c : Cfg (Fin 2) (Fin 4)) : Cfg (Fin 2) (Fin 4) := ⟨c.q.map e,c.tape⟩
  have step (c) : N.step (image c) = (M.step c).map image := by
    obtain ⟨s,t⟩ := c
    cases s with
    | none => rfl
    | some s =>
      simp only [Machine.step,image,Option.map_some,N,Equiv.symm_apply_apply]
      cases h : M s t.head with
      | none => rfl
      | some cmd => rcases cmd with ⟨r,z⟩; rfl
  have start : image (Machine.init []) = Machine.init [] := by
    simp [image,Machine.init,h0]
  have trace (n) : N.multiStep (image (Machine.init [])) n =
      (M.multiStep (Machine.init []) n).map image := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Machine.multiStep_succ,Machine.multiStep_succ,ih]
      cases h : M.multiStep (Machine.init []) n with
      | none => rfl
      | some c => exact step c
  refine ⟨N,e q,hr,?_,?_,?_⟩
  · simp [N,e.symm_apply_eq.mpr h0.symm,first,h1]
  · simp [N,e.symm_apply_eq.mpr h1.symm,second]
  · intro n
    unfold Machine.HaltsAfter
    conv_lhs => rw [← start,trace]
    exact Option.map_eq_none_iff


def H1 : Prop := ∀ (M : Machine (Fin 2) (Fin 4))
    (a : Fin 2) (q : Fin 4), q.val ≤ 2 →
    M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
    M 1 0 = some (some q, Stmt.write a Dir.left) →
    M.IsHalting → M.HaltsAfter (Machine.init []) 107

def H2 : Prop := ∀ (M : Machine (Fin 2) (Fin 4))
    (a b : Fin 2) (q : Fin 4),
    M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
    M 1 0 = some (some 2, Stmt.write a Dir.right) →
    M 2 0 = some (some q, Stmt.write b Dir.left) →
    M.IsHalting → M.HaltsAfter (Machine.init []) 107

def H3 : Prop := ∀ (M : Machine (Fin 2) (Fin 4))
    (a b c : Fin 2) (q : Fin 4),
    M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
    M 1 0 = some (some 2, Stmt.write a Dir.right) →
    M 2 0 = some (some 3, Stmt.write b Dir.right) →
    M 3 0 = some (some q, Stmt.write c Dir.left) →
    M.IsHalting → M.HaltsAfter (Machine.init []) 107


theorem main : H1 → H2 → H3 → OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1.H3 := by
  intro one two three M first early _ halts
  have late := early 107 (by decide)
  have init (P : Machine (Fin 2) (Fin 4)) : ∃ t : Tape (Fin 2),
      P.multiStep (Machine.init []) 0 = some ⟨some 0,t⟩ ∧
      t.head = 0 ∧ t.right = ListBlank.mk [] := ⟨Tape.mk₁ [],rfl,rfl,rfl⟩
  obtain ⟨q,a,d,second⟩ := inspect_blank M (advance M (init M) first) (by decide) late
  obtain ⟨N,r,hr,f,s,timing⟩ := normalize M q a d first second
  have nh : N.IsHalting := by
    obtain ⟨n,hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
    exact (Machine.isHalting_iff_exists_haltsAt N).mpr ⟨n,(timing n).mpr hn⟩
  have nl : ¬ N.HaltsAfter (Machine.init []) 107 := fun h => late ((timing _).mp h)
  cases d with
  | left => exact nl (one N a r hr f s nh)
  | right =>
    by_cases old : r ∈ ({0,1} : Finset (Fin 4))
    · apply closed_right N {0,1} (by decide) _ nh
      intro i hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact ⟨1,by decide,1,f⟩
      · exact ⟨r,old,a,s⟩
    have eq : r = 2 := by fin_cases r <;> first | rfl | exact False.elim (old (by decide)) | norm_num at hr
    subst r
    have reached := advance N (advance N (init N) f) s
    obtain ⟨v,b,dir,c⟩ := inspect_blank N reached (by decide) nl
    cases dir with
    | left => exact nl (two N a b v f s c nh)
    | right =>
      by_cases old' : v ∈ ({0,1,2} : Finset (Fin 4))
      · apply closed_right N {0,1,2} (by decide) _ nh
        intro i hi
        simp only [Finset.mem_insert,Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl
        · exact ⟨1,by decide,1,f⟩
        · exact ⟨2,by decide,a,s⟩
        · exact ⟨v,old',b,c⟩
      have eq : v = 3 := by fin_cases v <;> first | rfl | exact False.elim (old' (by decide))
      subst v
      obtain ⟨w,z,dir',last⟩ := inspect_blank N (advance N reached c) (by decide) nl
      cases dir' with
      | left => exact nl (three N a b z w f s c last nh)
      | right =>
        apply closed_right N Finset.univ (Finset.mem_univ _) _ nh
        intro i _
        fin_cases i
        · exact ⟨1,Finset.mem_univ _,1,f⟩
        · exact ⟨2,Finset.mem_univ _,a,s⟩
        · exact ⟨3,Finset.mem_univ _,b,c⟩
        · exact ⟨w,Finset.mem_univ _,z,last⟩

end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1
