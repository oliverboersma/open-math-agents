import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1
import Mathlib

/-! After four specified blank instructions, a finite automaton on each half-tape
can certify divergence. Independently exploring the partial transition tables to
depth 107 and propagating finite windows on both sides leaves four exceptional
tables for direct analysis. Digits in base 17 encode the eight entries in
state-major order. Digit 16 is the absent entry; the other digits encode the
next state, write bit and direction (right has low bit 1). -/
-- Credit: @marcusbuffett
namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1
open Turing Turing.BusyBeaver

/-- Finite certificate search. A regular invariant can be specified by two
finite transition tables reading the left and right halves from infinity. -/
def H1 : Prop :=
  let entry (z : ℕ) (r : Fin 4) (s : Fin 2) : Option (Option (Fin 4) × Stmt (Fin 2)) :=
    let k := z / 17^(2*r.val+s.val) % 17
    if k=16 then none else some (some (Fin.ofNat 4 (k/4)),
      .write (Fin.ofNat 2 (k/2)) (if k%2=0 then .left else .right))
  ∀ (M : Machine (Fin 2) (Fin 4)) (a b c : Fin 2) (q : Fin 4),
    M 0 0 = some (some 1,Stmt.write 1 .right) →
    M 1 0 = some (some 2,Stmt.write a .right) →
    M 2 0 = some (some 3,Stmt.write b .right) →
    M 3 0 = some (some q,Stmt.write c .left) →
    M.HaltsAfter (Machine.init []) 107 ∨
    (∃ z ∈ ([1790187557,6207529726,6221728296,6810924734] : List ℕ),
      ∀ r s cmd, entry z r s=some cmd → M r s=some cmd) ∨
    ∃ (n m : ℕ) (x : Fin n) (y : Fin m) (L : Fin 2 → Fin n → Fin n)
      (R : Fin 2 → Fin m → Fin m) (S : Fin 4 → Fin 2 → Fin n → Fin m → Bool),
      L 0 x=x ∧ R 0 y=y ∧ S 0 0 x y=true ∧
      ∀ q a s t i j, S q a (L s i) (R t j)=true →
        ∃ r w d, M q a=some (some r,Stmt.write w d) ∧
          (match d with
           | .left => S r s i (R w (R t j))
           | .right => S r t (L w (L s i)) j) = true

/-- The four remaining partial machines, with all seven live rows specified. -/
def H2 : Prop :=
  let entry (z : ℕ) (r : Fin 4) (s : Fin 2) : Option (Option (Fin 4) × Stmt (Fin 2)) :=
    let k := z / 17^(2*r.val+s.val) % 17
    if k=16 then none else some (some (Fin.ofNat 4 (k/4)),
      .write (Fin.ofNat 2 (k/2)) (if k%2=0 then .left else .right))
  ∀ z ∈ ([1790187557,6207529726,6221728296,6810924734] : List ℕ),
    ¬ Machine.IsHalting (entry z)

theorem reader {X : Type} (f : Fin 2 → X → X) (x : X) (blank : f 0 x=x) :
    ∃ g : ListBlank (Fin 2) → X, g (ListBlank.mk [])=x ∧
      ∀ (a : Fin 2) (l : ListBlank (Fin 2)),g (ListBlank.cons a l) = f a (g l) := by
  have zeros (m : ℕ) : (List.replicate m (0 : Fin 2)).foldr f x=x := by
    induction m with
    | zero => rfl
    | succ m ih => simp [List.replicate_succ,ih,blank]
  let g (l : ListBlank (Fin 2)) := l.liftOn (fun a => a.foldr f x) (by
    rintro a _ ⟨i,rfl⟩
    simp [List.foldr_append,zeros])
  refine ⟨g,rfl,?_⟩
  intro a l
  induction l using ListBlank.induction_on with | h l => rfl

theorem certified (M : Machine (Fin 2) (Fin 4))
    {X Y : Type} (x : X) (y : Y) (L : Fin 2 → X → X) (R : Fin 2 → Y → Y)
    (S : Fin 4 → Fin 2 → X → Y → Bool)
    (hl : L 0 x=x) (hr : R 0 y=y) (start : S 0 0 x y=true)
    (closed : ∀ q a s t i j, S q a (L s i) (R t j)=true →
        ∃ r w d, M q a=some (some r,Stmt.write w d) ∧
          (match d with
           | .left => S r s i (R w (R t j))
           | .right => S r t (L w (L s i)) j) = true) : ¬ M.IsHalting := by
  obtain ⟨fl,bl,cl⟩ := reader L x hl
  obtain ⟨fr,br,cr⟩ := reader R y hr
  have decompL (s : ListBlank (Fin 2)) : L s.head (fl s.tail)=fl s :=
    (cl _ _).symm.trans (congrArg fl (ListBlank.cons_head_tail s))
  have decompR (s : ListBlank (Fin 2)) : R s.head (fr s.tail)=fr s :=
    (cr _ _).symm.trans (congrArg fr (ListBlank.cons_head_tail s))
  have run (n : ℕ) : ∃ q t, M.multiStep (Machine.init []) n = some ⟨some q,t⟩ ∧
      S q t.head (fl t.left) (fr t.right)=true := by
    induction n with
    | zero =>
      refine ⟨0,Tape.mk₁ [],rfl,?_⟩
      change S 0 0 (fl (ListBlank.mk [])) (fr (ListBlank.mk []))=true
      simpa only [bl,br] using start
    | succ n ih =>
      obtain ⟨q,t,ht,hs⟩ := ih
      obtain ⟨r,w,d,move,next⟩ := closed q t.head t.left.head t.right.head (fl t.left.tail) (fr t.right.tail) (by
        rwa [decompL,decompR])
      refine ⟨r,(t.write w).move d,?_,?_⟩
      · simp [Machine.multiStep_succ,ht,Machine.step,move]
      · cases d <;> simp only [decompL,decompR] at next <;> simpa [Tape.move,Tape.write,cl,cr] using next
  intro hh
  obtain ⟨n,hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hh
  obtain ⟨_,_,he,_⟩ := run (n+1)
  rw [Machine.HaltsAfter,he] at hn
  contradiction

private theorem extension (M N : Machine (Fin 2) (Fin 4))
    (incl : ∀ r s cmd,N r s = some cmd → M r s=some cmd)
    (never : ¬ N.IsHalting) : ¬ M.IsHalting := by
  have alive (i : ℕ) : N.multiStep (Machine.init []) i ≠ none := by
    cases i with
    | zero => simp [Machine.multiStep]
    | succ i => exact fun h => never ((Machine.isHalting_iff_exists_haltsAt N).mpr ⟨i,h⟩)
  have agree (i : ℕ) : N.multiStep (Machine.init []) i = M.multiStep (Machine.init []) i := by
    induction i with
    | zero => rfl
    | succ i ih =>
      have ha := alive (i+1)
      rw [Machine.multiStep_succ] at ha ⊢
      rw [Machine.multiStep_succ,←ih]
      cases h : N.multiStep (Machine.init []) i with
      | none => rfl
      | some c =>
        obtain ⟨q,t⟩ := c
        cases q with
        | none => rfl
        | some q =>
          cases he : N q t.head with
          | none => simp [h,Machine.step,he] at ha
          | some cmd => simp [Machine.step,he,incl _ _ _ he]
  intro hM
  obtain ⟨n,hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hM
  exact alive (n+1) ((agree _).trans hn)

theorem main : H1 → H2 → OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1.H3 := by
  intro classify hard M a b c q hA hB hC hD halts
  rcases classify M a b c q hA hB hC hD with done | ⟨z,hz,extendsTable⟩ | ⟨_,_,x,y,L,R,S,hl,hr,hs,hc⟩
  · exact done
  · exact (extension M _ extendsTable (hard z hz) halts).elim
  · exact (certified M x y L R S hl hr hs hc halts).elim

end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1
