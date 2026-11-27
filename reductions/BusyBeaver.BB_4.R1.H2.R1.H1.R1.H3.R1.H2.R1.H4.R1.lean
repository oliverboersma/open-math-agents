import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1
import Mathlib

/-! Blank-tape classification for the prefix 0RB, 1LC. The search branches only
when a row is read for the first time. Of 49,860 partial tables surviving
107 steps after exact-cycle and total-table pruning, 2,183 survive the
one-sided cylinder test. A depth-20 backward search removes 1,454. For 585
more, bounded left and right word languages close under every transition.
Two finite readers that track runs or small one-sided automata cover another
91. The 53 listed exceptions remain for direct analysis. The search motivates
the classification in H1; H1 and H2 are independent proof obligations. -/
-- Credit: @marcusbuffett for the finite-reader soundness theorem.
namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1_H4_R1
open Turing Turing.BusyBeaver

/-- Classify each surviving partial table by a bounded backward certificate,
a pair of finite tape readers, or its concrete transition table. -/
def H1 : Prop :=
  let A := Fin 2
  let Q := Fin 4
  let entry (z : ℕ) : Machine A Q := fun r s =>
    let k := z / 17^(2*r.val+s.val) % 17
    if k=16 then none else some (some (Fin.ofNat 4 (k/4)),
      .write (Fin.ofNat 2 (k/2)) (if k%2=0 then .left else .right))
  ∀ M : Machine A Q,
  let run := M.multiStep (Machine.init [])
  M 0 0=some (some 1,.write 0 .right) →
  M 1 0=some (some 2,.write 1 .left) →
  (∃ q t,run 107=some ⟨some q,t⟩) →
  (∀ q a,(∃ i < 107,∃ t : Tape A,
    run i=some ⟨some q,t⟩ ∧ t.head=a) ↔
    ∃ q' z,M q a=some (some q',z)) →
  (∀ q a,M q a=none ∨ ∃ q' z,M q a=some (some q',z)) →
  (∀ i p q a (side : Bool)
      (w : List A) f,0<p → i+p≤107 →
    let c := fun t : ListBlank A =>
      let free := w.foldr ListBlank.cons t
      (⟨some q,if side then ⟨a,free,f⟩ else ⟨a,f,free⟩⟩ : Cfg A Q)
    (∃ t,run i=some (c t)) →
    ¬ ∀ t,∃ u,M.multiStep (c t) p=some (c u)) →
  (∃ k ≤ 20,∀ u v,M.multiStep u k=some v → (M.step v).isSome) ∨
  (∃ z ∈ ([192926630,394870650,515740378,1336417724,1408830431,1627390098,
  1689441169,2446657396,2452336858,2460855813,2460855983,2930234279,
  3133858477,3267241361,3267325035,3267408318,3267408386,3268076724,
  3268179812,3268243766,3325136085,3330584823,3330638645,3475567181,
  3475567351,3672067699,3673413691,3673413861,4079576433,4093775003,
  4100731862,4498257380,4684022874,4953712200,4972106404,4972170205,
  5435078199,5439716071,5439804454,5440806757,5453953928,5537278425,
  5792616725,6328050068,6695802976,6734875946,6734876082,6734876116,
  6745900956,6746235074,6775658997,6778655859,6852444036]),M=entry z) ∨
    ∃ (n m : ℕ) (x : Fin n) (y : Fin m) (L : A → Fin n → Fin n)
      (R : A → Fin m → Fin m) (S : Q → A → Fin n → Fin m → Bool),
      L 0 x=x ∧ R 0 y=y ∧ S 0 0 x y=true ∧
      ∀ q a s t i j,S q a (L s i) (R t j)=true →
        ∃ r w d,M q a=some (some r,Stmt.write w d) ∧
          (match d with
           | .left => S r s i (R w (R t j))
           | .right => S r t (L w (L s i)) j)=true

/-- Nontermination of the residual concrete tables, in state-major base 17.
Digits 0–15 encode four times the new state plus twice the write bit plus
the direction bit. Digit 16 is undefined. -/
def H2 : Prop :=
  let entry (z : ℕ) (r : Fin 4) (s : Fin 2) : Option (Option (Fin 4) × Stmt (Fin 2)) :=
    let k := z / 17^(2*r.val+s.val) % 17
    if k=16 then none else some (some (Fin.ofNat 4 (k/4)),
      .write (Fin.ofNat 2 (k/2)) (if k%2=0 then .left else .right))
  ∀ z ∈ ([192926630, 394870650, 515740378, 1336417724, 1408830431, 1627390098,
       1689441169, 2446657396, 2452336858, 2460855813, 2460855983, 2930234279,
       3133858477, 3267241361, 3267325035, 3267408318, 3267408386, 3268076724,
       3268179812, 3268243766, 3325136085, 3330584823, 3330638645, 3475567181,
       3475567351, 3672067699, 3673413691, 3673413861, 4079576433, 4093775003,
       4100731862, 4498257380, 4684022874, 4953712200, 4972106404, 4972170205,
       5435078199, 5439716071, 5439804454, 5440806757, 5453953928, 5537278425,
       5792616725, 6328050068, 6695802976, 6734875946, 6734876082, 6734876116,
       6745900956, 6746235074, 6775658997, 6778655859, 6852444036] : List ℕ), ¬ Machine.IsHalting (entry z)

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

theorem backward (M : Machine (Fin 2) (Fin 4))
    (live : ∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q,t⟩)
    (k : ℕ) (bound : k ≤ 20)
    (safe : ∀ u v, M.multiStep u k=some v → (M.step v).isSome) : ¬ M.IsHalting := by
  obtain ⟨q,t,hl⟩ := live
  have alive (n : ℕ) : M.multiStep (Machine.init []) n ≠ none := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hsmall : n ≤ 107
      · intro hn
        have h := (Machine.multiStep_eq_none_mono hn hsmall).symm.trans hl
        contradiction
      · let a := n-1-k
        obtain ⟨u,hu⟩ := Option.ne_none_iff_exists'.mp (ih a (by dsimp [a]; omega))
        obtain ⟨v,hv⟩ := Option.ne_none_iff_exists'.mp (ih (n-1) (by omega))
        have hku : M.multiStep u k = some v := by
          unfold Machine.multiStep at hu hv ⊢
          rw [show n-1=k+a by dsimp [a]; omega,Function.iterate_add_apply,hu] at hv
          exact hv
        have hs := safe u v hku
        rw [show n=(n-1)+1 by omega,Machine.multiStep_succ,hv]
        exact Option.isSome_iff_ne_none.mp hs
  intro halt
  obtain ⟨n,hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halt
  exact alive _ hn

theorem main : H1 → H2 → OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1.H4 := by
  intro classify residual M hA hB live used clean missing loopfree
  rcases classify M hA hB live used clean loopfree with
    ⟨k,hk,safe⟩ | ⟨z,hz,rfl⟩ | ⟨_,_,x,y,L,R,S,hl,hr,hs,hc⟩
  · exact backward M live k hk safe
  · exact residual z hz
  · exact certified M x y L R S hl hr hs hc

end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1_H4_R1
