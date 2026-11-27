import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1
import Mathlib

/-! It suffices to search machines with a single missing transition. For every
missing row of an arbitrary machine, fill all its other missing rows with live
commands. If the original run is live after 107 steps, every such completion
follows the same prefix. Their regular invariants can then be intersected. -/
-- Credit: @marcusbuffett
namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1
open Turing Turing.BusyBeaver

/-- The finite search over single-hole tables. The three unrestricted one-symbol
rows have sixteen choices each, so the total number of cases is 524288. -/
def H1 : Prop := ∀ (a b c : Fin 2) (q h : Fin 4) (u : Fin 4 → Fin 4 × Stmt (Fin 2)),
  let v : Fin 4 → Fin 4 × Stmt (Fin 2) :=
    ![(1,.write 1 .right),(2,.write a .right),(3,.write b .right),(q,.write c .left)]
  let N : Machine (Fin 2) (Fin 4) := fun r s =>
    if s=0 then some (some (v r).1,(v r).2) else if r=h then none else some (some (u r).1,(u r).2)
  (∃ r T,N.multiStep (Machine.init []) 107 = some ⟨some r,T⟩) →
  ∃ (n m : ℕ) (x : Fin n) (y : Fin m) (L : Fin 2 → Fin n → Fin n)
      (R : Fin 2 → Fin m → Fin m) (S : Fin 4 → Fin 2 → Fin n → Fin m → Bool),
      L 0 x=x ∧ R 0 y=y ∧ S 0 0 x y=true ∧
      ∀ q a s t i j, S q a (L s i) (R t j)=true →
        ∃ r w d, N q a=some (some r,Stmt.write w d) ∧
          (match d with
           | .left => S r s i (R w (R t j))
           | .right => S r t (L w (L s i)) j) = true

/-- Simultaneous finite readers for the intersection of a family of live transition
relations; the family is allowed to be empty when the original machine is total. -/
def H2 : Prop :=
  let cert (M : Machine (Fin 2) (Fin 4)) : Prop := ∃ (n m : ℕ) (x : Fin n) (y : Fin m) (L : Fin 2 → Fin n → Fin n)
      (R : Fin 2 → Fin m → Fin m) (S : Fin 4 → Fin 2 → Fin n → Fin m → Bool),
      L 0 x=x ∧ R 0 y=y ∧ S 0 0 x y=true ∧
      ∀ q a s t i j, S q a (L s i) (R t j)=true →
        ∃ r w d, M q a=some (some r,Stmt.write w d) ∧
          (match d with
           | .left => S r s i (R w (R t j))
           | .right => S r t (L w (L s i)) j) = true
  ∀ (I : Type) [Fintype I] (F : I → Machine (Fin 2) (Fin 4)) (M : Machine (Fin 2) (Fin 4)),
    (∀ i, cert (F i)) →
    (∀ q a, (∀ i, ∃ r st, F i q a = some (some r,st)) →
      ∃ r st, M q a = some (some r,st) ∧ ∀ i,F i q a = some (some r,st)) → cert M

lemma transfer (M N : Machine (Fin 2) (Fin 4))
    (ext : ∀ q a r st,M q a=some (some r,st) → N q a=some (some r,st))
    (k : ℕ) (r : Fin 4) (T : Tape (Fin 2))
    (run : M.multiStep (Machine.init []) k = some ⟨some r,T⟩) :
    N.multiStep (Machine.init []) k = some ⟨some r,T⟩ := by
  induction k generalizing r T with
  | zero => exact run
  | succ k ih =>
    rw [Machine.multiStep_succ] at run ⊢
    cases e : M.multiStep (Machine.init []) k with
    | none => simp [e] at run
    | some conf =>
      obtain ⟨_ | p,t⟩ := conf
      · simp [e,Machine.step] at run
      · rw [ih p t e]
        cases cmd : M p t.head with
        | none => simp [e,Machine.step,cmd] at run
        | some val =>
          obtain ⟨_ | s,st⟩ := val
          · simp [e,Machine.step,cmd] at run
          · simpa only [e,Option.bind_some,Machine.step,cmd,ext _ _ _ _ cmd,Option.map_some] using run

theorem main : H1 → H2 → OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1.H1 := by
  intro single intersect M a b c q e₀ e₁ e₂ e₃
  by_cases early : M.HaltsAfter (Machine.init []) 107
  · exact Or.inl early
  apply Or.inr
  apply Or.inr
  classical
  obtain ⟨p,T,alive⟩ := M.exists_of_not_haltsAfter _ _ early
  let v : Fin 4 → Fin 4 × Stmt (Fin 2) :=
    ![(1,.write 1 .right),(2,.write a .right),(3,.write b .right),(q,.write c .left)]
  have ev (r : Fin 4) : M r 0=some (some (v r).1,(v r).2) := by
    fin_cases r <;> assumption
  let I := {h : Fin 4 // ¬∃ r st, M h 1 = some (some r,st)}
  have fill (r : Fin 4) : ∃ u : Fin 4 × Stmt (Fin 2), ∀ p st,M r 1=some (some p,st) → (p,st)=u := by
    by_cases live : ∃ p st,M r 1=some (some p,st)
    · obtain ⟨p,st,h⟩ := live
      exact ⟨(p,st),fun s t ht => by simpa only [h,Option.some.injEq,Prod.mk.injEq] using ht.symm⟩
    · exact ⟨(0,.write 0 .right),fun p st ht => (live ⟨p,st,ht⟩).elim⟩
  choose u hu using fill
  let F (h : I) : Machine (Fin 2) (Fin 4) := fun r s =>
    if s=0 then some (some (v r).1,(v r).2) else if r=h.1 then none else some (some (u r).1,(u r).2)
  have ext (h : I) (r : Fin 4) (s : Fin 2) (p : Fin 4) (st : Stmt (Fin 2))
      (e : M r s=some (some p,st)) : F h r s=some (some p,st) := by
    fin_cases s
    · exact (ev r).symm.trans e
    · have hr : r≠h.1 := fun eq => h.2 ⟨p,st,eq ▸ e⟩
      have he := hu r p st e
      simp [F,hr,←he]
  apply intersect I F M
  · intro h
    apply single a b c q h.1 u
    exact ⟨p,T,transfer M (F h) (ext h) 107 p T alive⟩
  · intro r s every
    have live : ∃ p st, M r s=some (some p,st) := by
      fin_cases s
      · exact ⟨_,_,ev r⟩
      · by_contra miss
        obtain ⟨p,st,hp⟩ := every (⟨r,miss⟩ : I)
        simp [F] at hp
    obtain ⟨p,st,e⟩ := live
    exact ⟨p,st,e,fun h => ext h r s p st e⟩

end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1

