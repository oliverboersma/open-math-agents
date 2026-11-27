import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2
import Mathlib


/-!
# Three regular matchings with an abelian normal subgroup of index eleven

Every normalized regular matching graph over a finite odd-order group with an abelian
normal subgroup of index eleven contains a simple 4-, 8-, 16-, or 32-cycle. Extra
ambient edges are allowed. For noncommuting shifts with three distinct quotient
images the proof gives a simple 32-cycle without an odd-order or finiteness assumption.

The quotient has two types of three-element subsets after translation, scaling and
relabeling. They have representatives {0,1,2} and {0,1,3}. The quotient theta paths
of lengths (2,2,12) or (2,4,10) lift to a simple cycle when their three endpoints
in the other fiber are distinct. The translation orbit is an eleven-term sequence
in an arbitrary abelian group. Explicit sums of translated endpoint equations force
the sequence to be constant if both orientations fail. The common carry of the
extension is retained throughout, allowing nonsplit extensions.

The commuting case uses the merged OMA reduction PR 5246. The coincident-image case
uses the earlier abelian-normal rectangle. The original cubic and regular branches
come from @JamesSlash (PR 592) and PR 5820. The odd-order residual is PR 6558 and
the minimal index-three restriction is PR 7326. Codex, gpt-6.2-astra.
-/


/- A uniform translation cover of a theta with path lengths 2, 4 and 10.
The abstract theta result applies whenever the two endpoint displacements commute.
The matching graph corollary uses a 15-vertex theta in an abelian quotient.
Codex, gpt-6.2-astra, Erdős problem 64. -/

namespace HaarMetaTheta
open SimpleGraph

/-- A square-free commutator walk on a weighted 2-, 4-, 10-edge theta.
The embedding hypothesis says that the fifteen distinct quotient vertices have
disjoint fibers. In each fiber the group coordinate acts freely. -/
theorem theta32 {D V : Type*} [Group D] (a b : D) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (comm : Commute a b) (G : SimpleGraph V) (ι : (Fin 15 × D) ↪ V)
    :
    let tail : Fin 16 → Fin 15 := ![0,2,0,3,4,5,0,6,7,8,9,10,11,12,13,14]
    let head : Fin 16 → Fin 15 := ![2,1,3,4,5,1,6,7,8,9,10,11,12,13,14,1]
    let weight : Fin 16 → Fin 3 := ![0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,2]
    (∀ (e : Fin 16) (g : D), G.Adj (ι (tail e,g))
      (ι (head e,g * (![1,a,b] : Fin 3 → D) (weight e)))) → cycleGraph 32 ⊑ G := by
  intro tail head weight edges
  let path32 : Fin 32 → Fin 15 × Fin 4 := ![(0,0),(2,0),(1,1),(5,1),(4,1),(3,1),(0,1),(6,1),(7,1),(8,1),(9,1),(10,1),(11,1),(12,1),(13,1),(14,1),(1,3),(2,2),(0,2),(3,2),(4,2),(5,2),(1,2),(14,0),(13,0),(12,0),(11,0),(10,0),(9,0),(8,0),(7,0),(6,0)]
  let h : Fin 4 → D := ![1,a,b,a*b]
  let v (p : Fin 15 × Fin 4) := ι (p.1,h p.2)
  have distinct (i j : Fin 4) (ne : i ≠ j) (avoid : ¬ (i=0 ∧ j=3) ∧ ¬ (i=3 ∧ j=0)) :
      h i ≠ h j := by
    fin_cases i <;> fin_cases j <;> simp_all [h,comm.eq] <;> (intro eq; first | exact ha eq.symm | exact hb eq.symm | exact hab eq.symm)
  have sep : ∀ (i j : Fin 32), i ≠ j → (path32 i).1=(path32 j).1 →
      (path32 i).2 ≠ (path32 j).2 ∧
        ¬ ((path32 i).2=0 ∧ (path32 j).2=3) ∧ ¬ ((path32 i).2=3 ∧ (path32 j).2=0) := by
    dsimp only [path32]
    decide
  have vi : Function.Injective (fun i => v (path32 i)) := by
    intro i j eq
    by_contra ne
    have hh := ι.injective eq
    have z := sep i j ne (congrArg (fun z : Fin 15 × D => z.1) hh)
    exact distinct _ _ z.1 z.2 (congrArg (fun z : Fin 15 × D => z.2) hh)
  let step (u w : Fin 15 × Fin 4) : Prop :=
    ∃ e : Fin 16, u.1=tail e ∧ w.1=head e ∧
    ((weight e=0 ∧ w.2=u.2) ∨
      (weight e=1 ∧ ((u.2=0 ∧ w.2=1) ∨ (u.2=2 ∧ w.2=3))) ∨
      (weight e=2 ∧ ((u.2=0 ∧ w.2=2) ∨ (u.2=1 ∧ w.2=3))))
  have advance (u w : Fin 15 × Fin 4) (hh : step u w) : G.Adj (v u) (v w) := by
    obtain ⟨e,hu,hw,sw⟩ := hh
    have val : h w.2 = h u.2 * (![1,a,b] : Fin 3 → D) (weight e) := by
      rcases sw with ⟨z,q⟩ | ⟨z,⟨m,n⟩|⟨m,n⟩⟩ | ⟨z,⟨m,n⟩|⟨m,n⟩⟩
      · simp [z,q]
      all_goals simp [z,m,n,h,comm.eq]
    change G.Adj (ι (u.1,h u.2)) (ι (w.1,h w.2))
    rw [hu,hw,val]
    exact edges e _
  have walk : ∀ i j : Fin 32, (cycleGraph 32).Adj i j →
    step (path32 i) (path32 j) ∨ step (path32 j) (path32 i) := by
    dsimp only [step,path32,tail,head,weight]
    decide
  exact ⟨⟨⟨fun i => v (path32 i),fun {i j} edge =>
    (walk i j edge).elim (advance _ _) (fun hh => (advance _ _ hh).symm)⟩,vi⟩⟩

end HaarMetaTheta


namespace HaarCyclicEleven
open SimpleGraph


/-- In a nonconstant eleven-term orbit, the three endpoints are distinct in at
least one of the two orientations. The integer combinations cancel explicitly. -/
theorem some_distinct {V : Type*} [AddCommGroup V] (v : Fin 11 → V)
    (T : V →+ V) (rotate : ∀ i : Fin 11,T (v i)=v (i+1)) (ne : v 0 ≠ v 1) :
    let finish (o : Bool) : Fin 3 → V := if o then ![0,-v 8 + v 9,-v 1 + v 2 - v 3 + v 10] else ![0,v 0 - v 10,v 5 - v 6 + v 7 - v 9]
    ∃ o : Bool, Function.Injective (finish o) := by
  intro finish
  have move (i : Fin 11) : T (v i) = v ((![1,2,3,4,5,6,7,8,9,10,0] : Fin 11 → Fin 11) i) := by
    rw [rotate]
    exact congrArg v (by fin_cases i <;> decide)
  have h001 : finish false 0 ≠ finish false 1 := by
    intro hz
    have z0 : 0 = v 0 - v 10 := hz
    have z1 : 0 = v 1 - v 0 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z0
    apply ne
    linear_combination (norm := abel) z1
  have h012 : finish false 1 ≠ finish false 2 := by
    intro hz
    have z0 : v 0 - v 10 = v 5 - v 6 + v 7 - v 9 := hz
    have z1 : v 1 - v 0 = v 6 - v 7 + v 8 - v 10 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z0
    have z2 : v 2 - v 1 = v 7 - v 8 + v 9 - v 0 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z1
    have z3 : v 3 - v 2 = v 8 - v 9 + v 10 - v 1 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z2
    have z4 : v 4 - v 3 = v 9 - v 10 + v 0 - v 2 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z3
    have z5 : v 5 - v 4 = v 10 - v 0 + v 1 - v 3 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z4
    have z6 : v 6 - v 5 = v 0 - v 1 + v 2 - v 4 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z5
    have z7 : v 7 - v 6 = v 1 - v 2 + v 3 - v 5 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z6
    have z8 : v 8 - v 7 = v 2 - v 3 + v 4 - v 6 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z7
    have z9 : v 9 - v 8 = v 3 - v 4 + v 5 - v 7 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z8
    apply ne
    linear_combination (norm := abel) -z0 - z1 - z6 - z7 + z9
  have h101 : finish true 0 ≠ finish true 1 := by
    intro hz
    have z0 : 0 = -v 8 + v 9 := hz
    have z1 : 0 = -v 9 + v 10 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z0
    have z2 : 0 = -v 10 + v 0 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z1
    have z3 : 0 = -v 0 + v 1 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z2
    apply ne
    linear_combination (norm := abel) z3
  have h112 : finish true 1 ≠ finish true 2 := by
    intro hz
    have z0 : -v 8 + v 9 = -v 1 + v 2 - v 3 + v 10 := hz
    have z1 : -v 9 + v 10 = -v 2 + v 3 - v 4 + v 0 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z0
    have z2 : -v 10 + v 0 = -v 3 + v 4 - v 5 + v 1 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z1
    have z3 : -v 0 + v 1 = -v 4 + v 5 - v 6 + v 2 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z2
    have z4 : -v 1 + v 2 = -v 5 + v 6 - v 7 + v 3 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z3
    have z5 : -v 2 + v 3 = -v 6 + v 7 - v 8 + v 4 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z4
    have z6 : -v 3 + v 4 = -v 7 + v 8 - v 9 + v 5 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z5
    have z7 : -v 4 + v 5 = -v 8 + v 9 - v 10 + v 6 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z6
    have z8 : -v 5 + v 6 = -v 9 + v 10 - v 0 + v 7 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z7
    have z9 : -v 6 + v 7 = -v 10 + v 0 - v 1 + v 8 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z8
    apply ne
    linear_combination (norm := abel) -z3 - z4 + z6 - z8 - z9
  have alternatives : finish false 0 ≠ finish false 2 ∨ finish true 0 ≠ finish true 2 := by
    by_contra! h
    obtain ⟨hz, hw⟩ := h
    have z0 : 0 = v 5 - v 6 + v 7 - v 9 := hz
    have z1 : 0 = v 6 - v 7 + v 8 - v 10 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z0
    have z2 : 0 = v 7 - v 8 + v 9 - v 0 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z1
    have z3 : 0 = v 8 - v 9 + v 10 - v 1 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z2
    have z4 : 0 = v 9 - v 10 + v 0 - v 2 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T z3
    have w0 : 0 = -v 1 + v 2 - v 3 + v 10 := hw
    have w1 : 0 = -v 2 + v 3 - v 4 + v 0 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T w0
    have w2 : 0 = -v 3 + v 4 - v 5 + v 1 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T w1
    have w3 : 0 = -v 4 + v 5 - v 6 + v 2 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T w2
    have w4 : 0 = -v 5 + v 6 - v 7 + v 3 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val] using congrArg T w3
    apply ne
    linear_combination (norm := abel) -z0 - z4 - w0 - w4
  rcases alternatives with h | h
  · refine ⟨false,?_⟩
    intro i j eq
    fin_cases i <;> fin_cases j <;> first | rfl | exact (h001 eq).elim | exact (h001 eq.symm).elim | exact (h012 eq).elim | exact (h012 eq.symm).elim | exact (h eq).elim | exact (h eq.symm).elim
  · refine ⟨true,?_⟩
    intro i j eq
    fin_cases i <;> fin_cases j <;> first | rfl | exact (h101 eq).elim | exact (h101 eq.symm).elim | exact (h112 eq).elim | exact (h112 eq.symm).elim | exact (h eq).elim | exact (h eq.symm).elim

end HaarCyclicEleven

namespace HaarCyclicEleven
open SimpleGraph

/-- Coordinates of a cyclic extension with generator a advancing by 1 and b
advancing by 3. The element c is the carry a^11, so nonsplit extensions are allowed.
A nonconstant orbit of the translation b a^(-3) forces a simple 32-cycle. -/
theorem coordinates32 {V X : Type*} [AddCommGroup V] (v : Fin 11 → V) (c : V)
    (T : V →+ V) (rotate : ∀ i : Fin 11,T (v i)=v (i+1)) (ne : v 0 ≠ v 1)
    (G : SimpleGraph X) (ι : (Bool × Fin 11 × V) ↪ X)
    (h0 : ∀ (i : Fin 11) (u : V), G.Adj (ι (false,i,u)) (ι (true,i,u)))
    (ha : ∀ (i : Fin 11) (u : V), G.Adj (ι (false,i,u))
      (ι (true,i+1,u+(if i.val+1 ≥ 11 then c else 0))))
    (hb : ∀ (i : Fin 11) (u : V), G.Adj (ι (false,i,u))
      (ι (true,i+3,u+v i+(if i.val+3 ≥ 11 then c else 0)))) :
    cycleGraph 32 ⊑ G := by
  let finish (o : Bool) : Fin 3 → V := if o then ![0,-v 8 + v 9,-v 1 + v 2 - v 3 + v 10] else ![0,v 0 - v 10,v 5 - v 6 + v 7 - v 9]
  let loc (o : Bool) : Fin 15 → Bool × Fin 11 :=
    if o then ![(true,0),(true,1),(false,0),(false,8),(true,9),(false,9),(false,10),(true,2),(false,2),(true,5),(false,5),(true,6),(false,3),(true,4),(false,1)] else ![(false,0),(false,10),(true,0),(true,3),(false,2),(true,2),(true,1),(false,9),(true,9),(false,6),(true,6),(false,5),(true,8),(false,7),(true,10)]
  let levels (o : Bool) :
    Fin 15 → V := if o then ![0,-v 8 + v 9,0,(-v 8 - c),(-v 8 - c),(-v 8 - c),(0 - c),v 10,v 10,v 2 + v 10,v 2 + v 10,v 2 + v 10,v 2 - v 3 + v 10,v 2 - v 3 + v 10,-v 1 + v 2 - v 3 + v 10] else ![0,(v 0 - v 10 - c),0,v 0,v 0,v 0,0,(-v 9 - c),(-v 9 - c),(-v 6 - v 9 - c),(-v 6 - v 9 - c),(-v 6 - v 9 - c),(v 5 - v 6 - v 9 - c),(v 5 - v 6 - v 9 - c),(v 5 - v 6 + v 7 - v 9 - c)]
  obtain ⟨o,distinct⟩ := some_distinct v T rotate ne
  let x : Multiplicative V := Multiplicative.ofAdd (finish o 0-finish o 1)
  let y : Multiplicative V := Multiplicative.ofAdd (finish o 2-finish o 1)
  have hx : x ≠ 1 := by
    intro e
    have eq : finish o 0-finish o 1=0 := congrArg Multiplicative.toAdd e
    exact (by decide : (0 : Fin 3) ≠ 1) (distinct (sub_eq_zero.mp eq))
  have hy : y ≠ 1 := by
    intro e
    have eq : finish o 2-finish o 1=0 := congrArg Multiplicative.toAdd e
    exact (by decide : (2 : Fin 3) ≠ 1) (distinct (sub_eq_zero.mp eq))
  have hxy : x ≠ y := by
    intro e
    have eq : finish o 0-finish o 1 = finish o 2-finish o 1 := congrArg Multiplicative.toAdd e
    exact (by decide : (0 : Fin 3) ≠ 2) (distinct (sub_left_inj.mp eq))
  have inject : Function.Injective (loc o) := by
    cases o <;> change ∀ i j : Fin 15, _ → i=j <;> dsimp only [loc] <;> decide
  let φ : (Fin 15 × Multiplicative V) ↪ X := {
    toFun z := ι ((loc o z.1).1,(loc o z.1).2,z.2.toAdd + levels o z.1)
    inj' := by
      rintro ⟨i,g⟩ ⟨j,h⟩ eq
      have q := ι.injective eq
      have same := congrArg (fun u : Bool × Fin 11 × V => (u.1,u.2.1)) q
      have ij := inject (show loc o i=loc o j from same)
      subst j
      have val := congrArg (fun u : Bool × Fin 11 × V => u.2.2) q
      exact Prod.ext rfl (Multiplicative.toAdd.injective (add_right_cancel val)) }
  apply HaarMetaTheta.theta32 x y hx hy hxy (Commute.all _ _) G φ
  intro e g
  cases o <;> fin_cases e
  · change G.Adj (ι (false,0,(g.toAdd + (0)))) (ι (true,0,(g.toAdd + 0 + (0))))
    have id : (g.toAdd + 0 + (0)) = (g.toAdd + (0)) := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,0,(g.toAdd + (0)))) (ι (true,0,q))) id).mpr (h0 0 (g.toAdd + (0)))
  · change G.Adj (ι (true,0,(g.toAdd + (0)))) (ι (false,10,(g.toAdd + (0 - (v 0 - v 10)) + ((v 0 - v 10 - c)))))
    have id : (g.toAdd + (0)) = (g.toAdd + (0 - (v 0 - v 10)) + ((v 0 - v 10 - c))) + c := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,0,q)) (ι (false,10,(g.toAdd + (0 - (v 0 - v 10)) + ((v 0 - v 10 - c)))))) id).mpr (ha 10 (g.toAdd + (0 - (v 0 - v 10)) + ((v 0 - v 10 - c)))).symm
  · change G.Adj (ι (false,0,(g.toAdd + (0)))) (ι (true,3,(g.toAdd + 0 + (v 0))))
    have id : (g.toAdd + 0 + (v 0)) = (g.toAdd + (0)) + v 0 + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,0,(g.toAdd + (0)))) (ι (true,3,q))) id).mpr (hb 0 (g.toAdd + (0)))
  · change G.Adj (ι (true,3,(g.toAdd + (v 0)))) (ι (false,2,(g.toAdd + 0 + (v 0))))
    have id : (g.toAdd + (v 0)) = (g.toAdd + 0 + (v 0)) + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,3,q)) (ι (false,2,(g.toAdd + 0 + (v 0))))) id).mpr (ha 2 (g.toAdd + 0 + (v 0))).symm
  · change G.Adj (ι (false,2,(g.toAdd + (v 0)))) (ι (true,2,(g.toAdd + 0 + (v 0))))
    have id : (g.toAdd + 0 + (v 0)) = (g.toAdd + (v 0)) := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,2,(g.toAdd + (v 0)))) (ι (true,2,q))) id).mpr (h0 2 (g.toAdd + (v 0)))
  · change G.Adj (ι (true,2,(g.toAdd + (v 0)))) (ι (false,10,(g.toAdd + 0 + ((v 0 - v 10 - c)))))
    have id : (g.toAdd + (v 0)) = (g.toAdd + 0 + ((v 0 - v 10 - c))) + v 10 + c := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,2,q)) (ι (false,10,(g.toAdd + 0 + ((v 0 - v 10 - c)))))) id).mpr (hb 10 (g.toAdd + 0 + ((v 0 - v 10 - c)))).symm
  · change G.Adj (ι (false,0,(g.toAdd + (0)))) (ι (true,1,(g.toAdd + 0 + (0))))
    have id : (g.toAdd + 0 + (0)) = (g.toAdd + (0)) + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,0,(g.toAdd + (0)))) (ι (true,1,q))) id).mpr (ha 0 (g.toAdd + (0)))
  · change G.Adj (ι (true,1,(g.toAdd + (0)))) (ι (false,9,(g.toAdd + 0 + ((-v 9 - c)))))
    have id : (g.toAdd + (0)) = (g.toAdd + 0 + ((-v 9 - c))) + v 9 + c := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,1,q)) (ι (false,9,(g.toAdd + 0 + ((-v 9 - c)))))) id).mpr (hb 9 (g.toAdd + 0 + ((-v 9 - c)))).symm
  · change G.Adj (ι (false,9,(g.toAdd + ((-v 9 - c))))) (ι (true,9,(g.toAdd + 0 + ((-v 9 - c)))))
    have id : (g.toAdd + 0 + ((-v 9 - c))) = (g.toAdd + ((-v 9 - c))) := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,9,(g.toAdd + ((-v 9 - c))))) (ι (true,9,q))) id).mpr (h0 9 (g.toAdd + ((-v 9 - c))))
  · change G.Adj (ι (true,9,(g.toAdd + ((-v 9 - c))))) (ι (false,6,(g.toAdd + 0 + ((-v 6 - v 9 - c)))))
    have id : (g.toAdd + ((-v 9 - c))) = (g.toAdd + 0 + ((-v 6 - v 9 - c))) + v 6 + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,9,q)) (ι (false,6,(g.toAdd + 0 + ((-v 6 - v 9 - c)))))) id).mpr (hb 6 (g.toAdd + 0 + ((-v 6 - v 9 - c)))).symm
  · change G.Adj (ι (false,6,(g.toAdd + ((-v 6 - v 9 - c))))) (ι (true,6,(g.toAdd + 0 + ((-v 6 - v 9 - c)))))
    have id : (g.toAdd + 0 + ((-v 6 - v 9 - c))) = (g.toAdd + ((-v 6 - v 9 - c))) := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,6,(g.toAdd + ((-v 6 - v 9 - c))))) (ι (true,6,q))) id).mpr (h0 6 (g.toAdd + ((-v 6 - v 9 - c))))
  · change G.Adj (ι (true,6,(g.toAdd + ((-v 6 - v 9 - c))))) (ι (false,5,(g.toAdd + 0 + ((-v 6 - v 9 - c)))))
    have id : (g.toAdd + ((-v 6 - v 9 - c))) = (g.toAdd + 0 + ((-v 6 - v 9 - c))) + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,6,q)) (ι (false,5,(g.toAdd + 0 + ((-v 6 - v 9 - c)))))) id).mpr (ha 5 (g.toAdd + 0 + ((-v 6 - v 9 - c)))).symm
  · change G.Adj (ι (false,5,(g.toAdd + ((-v 6 - v 9 - c))))) (ι (true,8,(g.toAdd + 0 + ((v 5 - v 6 - v 9 - c)))))
    have id : (g.toAdd + 0 + ((v 5 - v 6 - v 9 - c))) = (g.toAdd + ((-v 6 - v 9 - c))) + v 5 + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,5,(g.toAdd + ((-v 6 - v 9 - c))))) (ι (true,8,q))) id).mpr (hb 5 (g.toAdd + ((-v 6 - v 9 - c))))
  · change G.Adj (ι (true,8,(g.toAdd + ((v 5 - v 6 - v 9 - c))))) (ι (false,7,(g.toAdd + 0 + ((v 5 - v 6 - v 9 - c)))))
    have id : (g.toAdd + ((v 5 - v 6 - v 9 - c))) = (g.toAdd + 0 + ((v 5 - v 6 - v 9 - c))) + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,8,q)) (ι (false,7,(g.toAdd + 0 + ((v 5 - v 6 - v 9 - c)))))) id).mpr (ha 7 (g.toAdd + 0 + ((v 5 - v 6 - v 9 - c)))).symm
  · change G.Adj (ι (false,7,(g.toAdd + ((v 5 - v 6 - v 9 - c))))) (ι (true,10,(g.toAdd + 0 + ((v 5 - v 6 + v 7 - v 9 - c)))))
    have id : (g.toAdd + 0 + ((v 5 - v 6 + v 7 - v 9 - c))) = (g.toAdd + ((v 5 - v 6 - v 9 - c))) + v 7 + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,7,(g.toAdd + ((v 5 - v 6 - v 9 - c))))) (ι (true,10,q))) id).mpr (hb 7 (g.toAdd + ((v 5 - v 6 - v 9 - c))))
  · change G.Adj (ι (true,10,(g.toAdd + ((v 5 - v 6 + v 7 - v 9 - c))))) (ι (false,10,(g.toAdd + (v 5 - v 6 + v 7 - v 9 - (v 0 - v 10)) + ((v 0 - v 10 - c)))))
    have id : (g.toAdd + ((v 5 - v 6 + v 7 - v 9 - c))) = (g.toAdd + (v 5 - v 6 + v 7 - v 9 - (v 0 - v 10)) + ((v 0 - v 10 - c))) := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,10,q)) (ι (false,10,(g.toAdd + (v 5 - v 6 + v 7 - v 9 - (v 0 - v 10)) + ((v 0 - v 10 - c)))))) id).mpr (h0 10 (g.toAdd + (v 5 - v 6 + v 7 - v 9 - (v 0 - v 10)) + ((v 0 - v 10 - c)))).symm
  · change G.Adj (ι (true,0,(g.toAdd + (0)))) (ι (false,0,(g.toAdd + 0 + (0))))
    have id : (g.toAdd + (0)) = (g.toAdd + 0 + (0)) := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,0,q)) (ι (false,0,(g.toAdd + 0 + (0))))) id).mpr (h0 0 (g.toAdd + 0 + (0))).symm
  · change G.Adj (ι (false,0,(g.toAdd + (0)))) (ι (true,1,(g.toAdd + (0 - (-v 8 + v 9)) + (-v 8 + v 9))))
    have id : (g.toAdd + (0 - (-v 8 + v 9)) + (-v 8 + v 9)) = (g.toAdd + (0)) + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,0,(g.toAdd + (0)))) (ι (true,1,q))) id).mpr (ha 0 (g.toAdd + (0)))
  · change G.Adj (ι (true,0,(g.toAdd + (0)))) (ι (false,8,(g.toAdd + 0 + ((-v 8 - c)))))
    have id : (g.toAdd + (0)) = (g.toAdd + 0 + ((-v 8 - c))) + v 8 + c := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,0,q)) (ι (false,8,(g.toAdd + 0 + ((-v 8 - c)))))) id).mpr (hb 8 (g.toAdd + 0 + ((-v 8 - c)))).symm
  · change G.Adj (ι (false,8,(g.toAdd + ((-v 8 - c))))) (ι (true,9,(g.toAdd + 0 + ((-v 8 - c)))))
    have id : (g.toAdd + 0 + ((-v 8 - c))) = (g.toAdd + ((-v 8 - c))) + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,8,(g.toAdd + ((-v 8 - c))))) (ι (true,9,q))) id).mpr (ha 8 (g.toAdd + ((-v 8 - c))))
  · change G.Adj (ι (true,9,(g.toAdd + ((-v 8 - c))))) (ι (false,9,(g.toAdd + 0 + ((-v 8 - c)))))
    have id : (g.toAdd + ((-v 8 - c))) = (g.toAdd + 0 + ((-v 8 - c))) := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,9,q)) (ι (false,9,(g.toAdd + 0 + ((-v 8 - c)))))) id).mpr (h0 9 (g.toAdd + 0 + ((-v 8 - c)))).symm
  · change G.Adj (ι (false,9,(g.toAdd + ((-v 8 - c))))) (ι (true,1,(g.toAdd + 0 + (-v 8 + v 9))))
    have id : (g.toAdd + 0 + (-v 8 + v 9)) = (g.toAdd + ((-v 8 - c))) + v 9 + c := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,9,(g.toAdd + ((-v 8 - c))))) (ι (true,1,q))) id).mpr (hb 9 (g.toAdd + ((-v 8 - c))))
  · change G.Adj (ι (true,0,(g.toAdd + (0)))) (ι (false,10,(g.toAdd + 0 + ((0 - c)))))
    have id : (g.toAdd + (0)) = (g.toAdd + 0 + ((0 - c))) + c := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,0,q)) (ι (false,10,(g.toAdd + 0 + ((0 - c)))))) id).mpr (ha 10 (g.toAdd + 0 + ((0 - c)))).symm
  · change G.Adj (ι (false,10,(g.toAdd + ((0 - c))))) (ι (true,2,(g.toAdd + 0 + (v 10))))
    have id : (g.toAdd + 0 + (v 10)) = (g.toAdd + ((0 - c))) + v 10 + c := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,10,(g.toAdd + ((0 - c))))) (ι (true,2,q))) id).mpr (hb 10 (g.toAdd + ((0 - c))))
  · change G.Adj (ι (true,2,(g.toAdd + (v 10)))) (ι (false,2,(g.toAdd + 0 + (v 10))))
    have id : (g.toAdd + (v 10)) = (g.toAdd + 0 + (v 10)) := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,2,q)) (ι (false,2,(g.toAdd + 0 + (v 10))))) id).mpr (h0 2 (g.toAdd + 0 + (v 10))).symm
  · change G.Adj (ι (false,2,(g.toAdd + (v 10)))) (ι (true,5,(g.toAdd + 0 + (v 2 + v 10))))
    have id : (g.toAdd + 0 + (v 2 + v 10)) = (g.toAdd + (v 10)) + v 2 + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,2,(g.toAdd + (v 10)))) (ι (true,5,q))) id).mpr (hb 2 (g.toAdd + (v 10)))
  · change G.Adj (ι (true,5,(g.toAdd + (v 2 + v 10)))) (ι (false,5,(g.toAdd + 0 + (v 2 + v 10))))
    have id : (g.toAdd + (v 2 + v 10)) = (g.toAdd + 0 + (v 2 + v 10)) := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,5,q)) (ι (false,5,(g.toAdd + 0 + (v 2 + v 10))))) id).mpr (h0 5 (g.toAdd + 0 + (v 2 + v 10))).symm
  · change G.Adj (ι (false,5,(g.toAdd + (v 2 + v 10)))) (ι (true,6,(g.toAdd + 0 + (v 2 + v 10))))
    have id : (g.toAdd + 0 + (v 2 + v 10)) = (g.toAdd + (v 2 + v 10)) + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,5,(g.toAdd + (v 2 + v 10)))) (ι (true,6,q))) id).mpr (ha 5 (g.toAdd + (v 2 + v 10)))
  · change G.Adj (ι (true,6,(g.toAdd + (v 2 + v 10)))) (ι (false,3,(g.toAdd + 0 + (v 2 - v 3 + v 10))))
    have id : (g.toAdd + (v 2 + v 10)) = (g.toAdd + 0 + (v 2 - v 3 + v 10)) + v 3 + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,6,q)) (ι (false,3,(g.toAdd + 0 + (v 2 - v 3 + v 10))))) id).mpr (hb 3 (g.toAdd + 0 + (v 2 - v 3 + v 10))).symm
  · change G.Adj (ι (false,3,(g.toAdd + (v 2 - v 3 + v 10)))) (ι (true,4,(g.toAdd + 0 + (v 2 - v 3 + v 10))))
    have id : (g.toAdd + 0 + (v 2 - v 3 + v 10)) = (g.toAdd + (v 2 - v 3 + v 10)) + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,3,(g.toAdd + (v 2 - v 3 + v 10)))) (ι (true,4,q))) id).mpr (ha 3 (g.toAdd + (v 2 - v 3 + v 10)))
  · change G.Adj (ι (true,4,(g.toAdd + (v 2 - v 3 + v 10)))) (ι (false,1,(g.toAdd + 0 + (-v 1 + v 2 - v 3 + v 10))))
    have id : (g.toAdd + (v 2 - v 3 + v 10)) = (g.toAdd + 0 + (-v 1 + v 2 - v 3 + v 10)) + v 1 + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,4,q)) (ι (false,1,(g.toAdd + 0 + (-v 1 + v 2 - v 3 + v 10))))) id).mpr (hb 1 (g.toAdd + 0 + (-v 1 + v 2 - v 3 + v 10))).symm
  · change G.Adj (ι (false,1,(g.toAdd + (-v 1 + v 2 - v 3 + v 10)))) (ι (true,1,(g.toAdd + (-v 1 + v 2 - v 3 + v 10 - (-v 8 + v 9)) + (-v 8 + v 9))))
    have id : (g.toAdd + (-v 1 + v 2 - v 3 + v 10 - (-v 8 + v 9)) + (-v 8 + v 9)) = (g.toAdd + (-v 1 + v 2 - v 3 + v 10)) := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,1,(g.toAdd + (-v 1 + v 2 - v 3 + v 10)))) (ι (true,1,q))) id).mpr (h0 1 (g.toAdd + (-v 1 + v 2 - v 3 + v 10)))

end HaarCyclicEleven


/- A uniform translation cover of a theta with path lengths 2, 2 and 12.
The abstract theta result applies whenever the two endpoint displacements commute.
The matching graph corollary uses a 15-vertex theta in an abelian quotient.
Codex, gpt-6.2-astra, Erdős problem 64. -/

namespace HaarThetaProgression
open SimpleGraph

/-- A square-free commutator walk on a weighted 2-, 2-, 12-edge theta.
The embedding hypothesis says that the fifteen distinct quotient vertices have
disjoint fibers. In each fiber the group coordinate acts freely. -/
theorem theta32 {D V : Type*} [Group D] (a b : D) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (comm : Commute a b) (G : SimpleGraph V) (ι : (Fin 15 × D) ↪ V)
    :
    let tail : Fin 16 → Fin 15 := ![0,2,0,3,0,4,5,6,7,8,9,10,11,12,13,14]
    let head : Fin 16 → Fin 15 := ![2,1,3,1,4,5,6,7,8,9,10,11,12,13,14,1]
    let weight : Fin 16 → Fin 3 := ![0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,2]
    (∀ (e : Fin 16) (g : D), G.Adj (ι (tail e,g))
      (ι (head e,g * (![1,a,b] : Fin 3 → D) (weight e)))) → cycleGraph 32 ⊑ G := by
  intro tail head weight edges
  let path32 : Fin 32 → Fin 15 × Fin 4 := ![(0,0),(2,0),(1,1),(3,1),(0,1),(4,1),(5,1),(6,1),(7,1),(8,1),(9,1),(10,1),(11,1),(12,1),(13,1),(14,1),(1,3),(2,2),(0,2),(3,2),(1,2),(14,0),(13,0),(12,0),(11,0),(10,0),(9,0),(8,0),(7,0),(6,0),(5,0),(4,0)]
  let h : Fin 4 → D := ![1,a,b,a*b]
  let v (p : Fin 15 × Fin 4) := ι (p.1,h p.2)
  have distinct (i j : Fin 4) (ne : i ≠ j) (avoid : ¬ (i=0 ∧ j=3) ∧ ¬ (i=3 ∧ j=0)) :
      h i ≠ h j := by
    fin_cases i <;> fin_cases j <;> simp_all [h,comm.eq] <;> (intro eq; first | exact ha eq.symm | exact hb eq.symm | exact hab eq.symm)
  have sep : ∀ (i j : Fin 32), i ≠ j → (path32 i).1=(path32 j).1 →
      (path32 i).2 ≠ (path32 j).2 ∧
        ¬ ((path32 i).2=0 ∧ (path32 j).2=3) ∧ ¬ ((path32 i).2=3 ∧ (path32 j).2=0) := by
    dsimp only [path32]
    decide
  have vi : Function.Injective (fun i => v (path32 i)) := by
    intro i j eq
    by_contra ne
    have hh := ι.injective eq
    have z := sep i j ne (congrArg (fun z : Fin 15 × D => z.1) hh)
    exact distinct _ _ z.1 z.2 (congrArg (fun z : Fin 15 × D => z.2) hh)
  let step (u w : Fin 15 × Fin 4) : Prop :=
    ∃ e : Fin 16, u.1=tail e ∧ w.1=head e ∧
    ((weight e=0 ∧ w.2=u.2) ∨
      (weight e=1 ∧ ((u.2=0 ∧ w.2=1) ∨ (u.2=2 ∧ w.2=3))) ∨
      (weight e=2 ∧ ((u.2=0 ∧ w.2=2) ∨ (u.2=1 ∧ w.2=3))))
  have advance (u w : Fin 15 × Fin 4) (hh : step u w) : G.Adj (v u) (v w) := by
    obtain ⟨e,hu,hw,sw⟩ := hh
    have val : h w.2 = h u.2 * (![1,a,b] : Fin 3 → D) (weight e) := by
      rcases sw with ⟨z,q⟩ | ⟨z,⟨m,n⟩|⟨m,n⟩⟩ | ⟨z,⟨m,n⟩|⟨m,n⟩⟩
      · simp [z,q]
      all_goals simp [z,m,n,h,comm.eq]
    change G.Adj (ι (u.1,h u.2)) (ι (w.1,h w.2))
    rw [hu,hw,val]
    exact edges e _
  have walk : ∀ i j : Fin 32, (cycleGraph 32).Adj i j →
    step (path32 i) (path32 j) ∨ step (path32 j) (path32 i) := by
    dsimp only [step,path32,tail,head,weight]
    decide
  exact ⟨⟨⟨fun i => v (path32 i),fun {i j} edge =>
    (walk i j edge).elim (advance _ _) (fun hh => (advance _ _ hh).symm)⟩,vi⟩⟩

end HaarThetaProgression


namespace HaarElevenProgression
open SimpleGraph

/-- The same orientation works for every nonconstant translation orbit. The carry c
is fixed by the shift, so taking a difference of shifted endpoint relations cancels it. -/
theorem separated {V : Type*} [AddCommGroup V] (c : V) (v : Fin 11 → V)
    (T : V →+ V) (rotate : ∀ i : Fin 11,T (v i)=v (i+1)) (fixed : T c=c) (ne : v 0 ≠ v 1) :
    let finish : Fin 3 → V := ![-c,-v 10 - c,v 0 + v 2 + v 5 + v 8]
    Function.Injective (finish) := by
  intro finish
  have move (i : Fin 11) : T (v i) = v ((![1,2,3,4,5,6,7,8,9,10,0] : Fin 11 → Fin 11) i) := by
    rw [rotate]
    exact congrArg v (by fin_cases i <;> decide)
  have h01 : finish 0 ≠ finish 1 := by
    intro h
    have z0 : -c = -v 10 - c := h
    have z1 : -c = -v 0 - c := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z0
    have z2 : -c = -v 1 - c := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z1
    apply ne
    linear_combination (norm := abel) z1 - z2
  have h12 : finish 1 ≠ finish 2 := by
    intro h
    have z0 : -v 10 - c = v 0 + v 2 + v 5 + v 8 := h
    have z1 : -v 0 - c = v 1 + v 3 + v 6 + v 9 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z0
    have z2 : -v 1 - c = v 2 + v 4 + v 7 + v 10 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z1
    have z3 : -v 2 - c = v 3 + v 5 + v 8 + v 0 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z2
    have z4 : -v 3 - c = v 4 + v 6 + v 9 + v 1 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z3
    have z5 : -v 4 - c = v 5 + v 7 + v 10 + v 2 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z4
    have z6 : -v 5 - c = v 6 + v 8 + v 0 + v 3 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z5
    have z7 : -v 6 - c = v 7 + v 9 + v 1 + v 4 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z6
    have z8 : -v 7 - c = v 8 + v 10 + v 2 + v 5 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z7
    have z9 : -v 8 - c = v 9 + v 0 + v 3 + v 6 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z8
    apply ne
    linear_combination (norm := abel) z4 - z5 + z8 - z9
  have h02 : finish 0 ≠ finish 2 := by
    intro h
    have z0 : -c = v 0 + v 2 + v 5 + v 8 := h
    have z1 : -c = v 1 + v 3 + v 6 + v 9 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z0
    have z2 : -c = v 2 + v 4 + v 7 + v 10 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z1
    have z3 : -c = v 3 + v 5 + v 8 + v 0 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z2
    have z4 : -c = v 4 + v 6 + v 9 + v 1 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z3
    have z5 : -c = v 5 + v 7 + v 10 + v 2 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z4
    have z6 : -c = v 6 + v 8 + v 0 + v 3 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z5
    have z7 : -c = v 7 + v 9 + v 1 + v 4 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z6
    have z8 : -c = v 8 + v 10 + v 2 + v 5 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z7
    have z9 : -c = v 9 + v 0 + v 3 + v 6 := by
      simpa only [map_add,map_sub,map_neg,map_zero,move,Matrix.cons_val,fixed] using congrArg T z8
    apply ne
    linear_combination (norm := abel) z1 - z9
  intro i j eq
  fin_cases i <;> fin_cases j <;> first | rfl | exact (h01 eq).elim | exact (h01 eq.symm).elim | exact (h02 eq).elim | exact (h02 eq.symm).elim | exact (h12 eq).elim | exact (h12 eq.symm).elim

theorem coordinates32 {V X : Type*} [AddCommGroup V] (v : Fin 11 → V) (c : V)
    (T : V →+ V) (rotate : ∀ i : Fin 11,T (v i)=v (i+1)) (fixed : T c=c) (ne : v 0 ≠ v 1)
    (G : SimpleGraph X) (ι : (Bool × Fin 11 × V) ↪ X)
    (h0 : ∀ (i : Fin 11) (u : V), G.Adj (ι (false,i,u)) (ι (true,i,u)))
    (ha : ∀ (i : Fin 11) (u : V), G.Adj (ι (false,i,u))
      (ι (true,i+1,u+(if i.val+1 ≥ 11 then c else 0))))
    (hb : ∀ (i : Fin 11) (u : V), G.Adj (ι (false,i,u))
      (ι (true,i+2,u+v i+(if i.val+2 ≥ 11 then c else 0)))) :
    cycleGraph 32 ⊑ G := by
  let finish : Fin 3 → V := ![-c,-v 10 - c,v 0 + v 2 + v 5 + v 8]
  let loc : Fin 15 → Bool × Fin 11 := ![(false,0),(false,10),(true,0),(true,1),(true,2),(false,2),(true,4),(false,4),(true,5),(false,5),(true,7),(false,7),(true,8),(false,8),(true,10)]
  let levels : Fin 15 → V := ![0,-v 10 - c,0,0,v 0,v 0,v 0 + v 2,v 0 + v 2,v 0 + v 2,v 0 + v 2,v 0 + v 2 + v 5,v 0 + v 2 + v 5,v 0 + v 2 + v 5,v 0 + v 2 + v 5,v 0 + v 2 + v 5 + v 8]
  have distinct := separated c v T rotate fixed ne
  let x : Multiplicative V := Multiplicative.ofAdd (finish 0-finish 1)
  let y : Multiplicative V := Multiplicative.ofAdd (finish 2-finish 1)
  have hx : x ≠ 1 := by
    intro e
    have eq : finish 0-finish 1=0 := congrArg Multiplicative.toAdd e
    exact (by decide : (0 : Fin 3) ≠ 1) (distinct (sub_eq_zero.mp eq))
  have hy : y ≠ 1 := by
    intro e
    have eq : finish 2-finish 1=0 := congrArg Multiplicative.toAdd e
    exact (by decide : (2 : Fin 3) ≠ 1) (distinct (sub_eq_zero.mp eq))
  have hxy : x ≠ y := by
    intro e
    have eq : finish 0-finish 1 = finish 2-finish 1 := congrArg Multiplicative.toAdd e
    exact (by decide : (0 : Fin 3) ≠ 2) (distinct (sub_left_inj.mp eq))
  have inject : Function.Injective (loc) := by
    change ∀ i j : Fin 15, _ → i=j; dsimp only [loc]; decide
  let φ : (Fin 15 × Multiplicative V) ↪ X := {
    toFun z := ι ((loc z.1).1,(loc z.1).2,z.2.toAdd + levels z.1)
    inj' := by
      rintro ⟨i,g⟩ ⟨j,h⟩ eq
      have q := ι.injective eq
      have same := congrArg (fun u : Bool × Fin 11 × V => (u.1,u.2.1)) q
      have ij := inject (show loc i=loc j from same)
      subst j
      have val := congrArg (fun u : Bool × Fin 11 × V => u.2.2) q
      exact Prod.ext rfl (Multiplicative.toAdd.injective (add_right_cancel val)) }
  apply HaarThetaProgression.theta32 x y hx hy hxy (Commute.all _ _) G φ
  intro e g
  fin_cases e
  · change G.Adj (ι (false,0,(g.toAdd + (0)))) (ι (true,0,(g.toAdd + 0 + (0))))
    have id : (g.toAdd + 0 + (0)) = (g.toAdd + (0)) := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,0,(g.toAdd + (0)))) (ι (true,0,q))) id).mpr (h0 0 (g.toAdd + (0)))
  · change G.Adj (ι (true,0,(g.toAdd + (0)))) (ι (false,10,(g.toAdd + (-c - (-v 10 - c)) + (-v 10 - c))))
    have id : (g.toAdd + (0)) = (g.toAdd + (-c - (-v 10 - c)) + (-v 10 - c)) + c := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,0,q)) (ι (false,10,(g.toAdd + (-c - (-v 10 - c)) + (-v 10 - c))))) id).mpr (ha 10 (g.toAdd + (-c - (-v 10 - c)) + (-v 10 - c))).symm
  · change G.Adj (ι (false,0,(g.toAdd + (0)))) (ι (true,1,(g.toAdd + 0 + (0))))
    have id : (g.toAdd + 0 + (0)) = (g.toAdd + (0)) + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,0,(g.toAdd + (0)))) (ι (true,1,q))) id).mpr (ha 0 (g.toAdd + (0)))
  · change G.Adj (ι (true,1,(g.toAdd + (0)))) (ι (false,10,(g.toAdd + 0 + (-v 10 - c))))
    have id : (g.toAdd + (0)) = (g.toAdd + 0 + (-v 10 - c)) + v 10 + c := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,1,q)) (ι (false,10,(g.toAdd + 0 + (-v 10 - c))))) id).mpr (hb 10 (g.toAdd + 0 + (-v 10 - c))).symm
  · change G.Adj (ι (false,0,(g.toAdd + (0)))) (ι (true,2,(g.toAdd + 0 + (v 0))))
    have id : (g.toAdd + 0 + (v 0)) = (g.toAdd + (0)) + v 0 + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,0,(g.toAdd + (0)))) (ι (true,2,q))) id).mpr (hb 0 (g.toAdd + (0)))
  · change G.Adj (ι (true,2,(g.toAdd + (v 0)))) (ι (false,2,(g.toAdd + 0 + (v 0))))
    have id : (g.toAdd + (v 0)) = (g.toAdd + 0 + (v 0)) := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,2,q)) (ι (false,2,(g.toAdd + 0 + (v 0))))) id).mpr (h0 2 (g.toAdd + 0 + (v 0))).symm
  · change G.Adj (ι (false,2,(g.toAdd + (v 0)))) (ι (true,4,(g.toAdd + 0 + (v 0 + v 2))))
    have id : (g.toAdd + 0 + (v 0 + v 2)) = (g.toAdd + (v 0)) + v 2 + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,2,(g.toAdd + (v 0)))) (ι (true,4,q))) id).mpr (hb 2 (g.toAdd + (v 0)))
  · change G.Adj (ι (true,4,(g.toAdd + (v 0 + v 2)))) (ι (false,4,(g.toAdd + 0 + (v 0 + v 2))))
    have id : (g.toAdd + (v 0 + v 2)) = (g.toAdd + 0 + (v 0 + v 2)) := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,4,q)) (ι (false,4,(g.toAdd + 0 + (v 0 + v 2))))) id).mpr (h0 4 (g.toAdd + 0 + (v 0 + v 2))).symm
  · change G.Adj (ι (false,4,(g.toAdd + (v 0 + v 2)))) (ι (true,5,(g.toAdd + 0 + (v 0 + v 2))))
    have id : (g.toAdd + 0 + (v 0 + v 2)) = (g.toAdd + (v 0 + v 2)) + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,4,(g.toAdd + (v 0 + v 2)))) (ι (true,5,q))) id).mpr (ha 4 (g.toAdd + (v 0 + v 2)))
  · change G.Adj (ι (true,5,(g.toAdd + (v 0 + v 2)))) (ι (false,5,(g.toAdd + 0 + (v 0 + v 2))))
    have id : (g.toAdd + (v 0 + v 2)) = (g.toAdd + 0 + (v 0 + v 2)) := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,5,q)) (ι (false,5,(g.toAdd + 0 + (v 0 + v 2))))) id).mpr (h0 5 (g.toAdd + 0 + (v 0 + v 2))).symm
  · change G.Adj (ι (false,5,(g.toAdd + (v 0 + v 2)))) (ι (true,7,(g.toAdd + 0 + (v 0 + v 2 + v 5))))
    have id : (g.toAdd + 0 + (v 0 + v 2 + v 5)) = (g.toAdd + (v 0 + v 2)) + v 5 + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,5,(g.toAdd + (v 0 + v 2)))) (ι (true,7,q))) id).mpr (hb 5 (g.toAdd + (v 0 + v 2)))
  · change G.Adj (ι (true,7,(g.toAdd + (v 0 + v 2 + v 5)))) (ι (false,7,(g.toAdd + 0 + (v 0 + v 2 + v 5))))
    have id : (g.toAdd + (v 0 + v 2 + v 5)) = (g.toAdd + 0 + (v 0 + v 2 + v 5)) := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,7,q)) (ι (false,7,(g.toAdd + 0 + (v 0 + v 2 + v 5))))) id).mpr (h0 7 (g.toAdd + 0 + (v 0 + v 2 + v 5))).symm
  · change G.Adj (ι (false,7,(g.toAdd + (v 0 + v 2 + v 5)))) (ι (true,8,(g.toAdd + 0 + (v 0 + v 2 + v 5))))
    have id : (g.toAdd + 0 + (v 0 + v 2 + v 5)) = (g.toAdd + (v 0 + v 2 + v 5)) + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,7,(g.toAdd + (v 0 + v 2 + v 5)))) (ι (true,8,q))) id).mpr (ha 7 (g.toAdd + (v 0 + v 2 + v 5)))
  · change G.Adj (ι (true,8,(g.toAdd + (v 0 + v 2 + v 5)))) (ι (false,8,(g.toAdd + 0 + (v 0 + v 2 + v 5))))
    have id : (g.toAdd + (v 0 + v 2 + v 5)) = (g.toAdd + 0 + (v 0 + v 2 + v 5)) := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,8,q)) (ι (false,8,(g.toAdd + 0 + (v 0 + v 2 + v 5))))) id).mpr (h0 8 (g.toAdd + 0 + (v 0 + v 2 + v 5))).symm
  · change G.Adj (ι (false,8,(g.toAdd + (v 0 + v 2 + v 5)))) (ι (true,10,(g.toAdd + 0 + (v 0 + v 2 + v 5 + v 8))))
    have id : (g.toAdd + 0 + (v 0 + v 2 + v 5 + v 8)) = (g.toAdd + (v 0 + v 2 + v 5)) + v 8 + 0 := by abel
    exact (congrArg (fun q : V => G.Adj (ι (false,8,(g.toAdd + (v 0 + v 2 + v 5)))) (ι (true,10,q))) id).mpr (hb 8 (g.toAdd + (v 0 + v 2 + v 5)))
  · change G.Adj (ι (true,10,(g.toAdd + (v 0 + v 2 + v 5 + v 8)))) (ι (false,10,(g.toAdd + (v 0 + v 2 + v 5 + v 8 - (-v 10 - c)) + (-v 10 - c))))
    have id : (g.toAdd + (v 0 + v 2 + v 5 + v 8)) = (g.toAdd + (v 0 + v 2 + v 5 + v 8 - (-v 10 - c)) + (-v 10 - c)) := by abel
    exact (congrArg (fun q : V => G.Adj (ι (true,10,q)) (ι (false,10,(g.toAdd + (v 0 + v 2 + v 5 + v 8 - (-v 10 - c)) + (-v 10 - c))))) id).mpr (h0 10 (g.toAdd + (v 0 + v 2 + v 5 + v 8 - (-v 10 - c)) + (-v 10 - c))).symm

end HaarElevenProgression

namespace HaarCyclicEleven
open SimpleGraph

/-- If the two nonidentity shifts project to t and t³, where t has order 11,
an abelian kernel and noncommuting shifts force a simple 32-cycle. -/
theorem index_eleven_ratio {A Q : Type*} [Group A] [Group Q] (f : A →* Q)
    (abelian : ∀ g h : f.ker, g*h=h*g) (a b : A)
    (d : ℕ) (dsmall : d=2 ∨ d=3) (order : orderOf (f a)=11) (image : f b=(f a)^d) (nc : ¬ Commute a b)
    (G : SimpleGraph (Bool × A)) (h0 : ∀ x,G.Adj (false,x) (true,x))
    (ha : ∀ x,G.Adj (false,x) (true,x*a)) (hb : ∀ x,G.Adj (false,x) (true,x*b)) :
    cycleGraph 32 ⊑ G := by
  classical
  let K := f.ker
  let : CommGroup K := { (inferInstance : Group K) with mul_comm := abelian }
  have a11 : f (a^11) = 1 := by rw [map_pow,← order,pow_orderOf_eq_one]
  let c : K := ⟨a^11,a11⟩
  let n : K := ⟨b*(a^d)⁻¹,by change f _=1; simp [image]⟩
  have bform : (n:A)*a^d = b := by dsimp [n]; group
  let T : K →* K := {
    toFun g := ⟨a*(g:A)*a⁻¹, by change f _=1; simp [show f g = 1 from g.property]⟩
    map_one' := Subtype.ext (by change a*1*a⁻¹=1; group)
    map_mul' g h := Subtype.ext (by change a*((g:A)*h)*a⁻¹=(a*g*a⁻¹)*(a*h*a⁻¹);group) }
  let v (i : Fin 11) : Additive K := Additive.ofMul
    (⟨a^i.val*(n:A)*(a^i.val)⁻¹,by change f _=1; simp [show f n=1 from n.property]⟩ : K)
  have cn : a^11*(n:A)=(n:A)*a^11 := congrArg Subtype.val (abelian c n)
  have rot (i : Fin 11) : MonoidHom.toAdditive T (v i)=v (i+1) := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    change a*(a^i.val*(n:A)*(a^i.val)⁻¹)*a⁻¹=a^(i+1).val*(n:A)*(a^(i+1).val)⁻¹
    by_cases lt : i.val+1<11
    · have val : (i+1).val=i.val+1 := by
        change (i.val+1)%11=i.val+1
        exact Nat.mod_eq_of_lt lt
      rw [val,pow_succ']
      group
    · have val : i.val=10 := by have := i.isLt; omega
      have zero : (i+1).val=0 := by change (i.val+1)%11=0; rw [val]
      rw [val,zero,pow_zero]
      calc a*(a^10*(n:A)*(a^10)⁻¹)*a⁻¹ = a^11*(n:A)*(a^11)⁻¹ := by group
           _ = _ := by rw [cn]; group
  have ne : v 0 ≠ v 1 := by
    intro eq
    have neqc := congrArg (fun z : Additive K => (z.toMul : A)) eq
    change a^0*(n:A)*(a^0)⁻¹=a^1*(n:A)*(a^1)⁻¹ at neqc
    have an : a*(n:A) = (n:A)*a := by
      simp only [pow_zero,pow_one,inv_one,one_mul,mul_one] at neqc
      calc a*(n:A) = (a*(n:A)*a⁻¹)*a := by group
           _ = _ := by rw [← neqc]
    apply nc
    change a*b=b*a
    rw [← bform]
    calc a*((n:A)*a^d) = (a*n)*a^d := by group
         _ = ((n:A)*a^d)*a := by rw [an]; group
  let ι : (Bool × Fin 11 × Additive K) ↪ (Bool × A) := {
    toFun z := (z.1,(z.2.2.toMul:A)*a^z.2.1.val)
    inj' := by
      rintro ⟨s,i,u⟩ ⟨t,j,w⟩ eq
      have ss := congrArg (fun z : Bool × A => z.1) eq
      have gg := congrArg (fun z : Bool × A => z.2) eq
      change (u.toMul:A)*a^i.val=(w.toMul:A)*a^j.val at gg
      have same : (f a)^i.val=(f a)^j.val := by
        simpa only [map_mul,map_pow,show f u.toMul=1 from u.toMul.property,
          show f w.toMul=1 from w.toMul.property,one_mul] using congrArg f gg
      have ij : i=j := Fin.ext (pow_injOn_Iio_orderOf (x:=f a)
        (show i.val < orderOf (f a) by rw [order];exact i.isLt)
        (show j.val < orderOf (f a) by rw [order];exact j.isLt) same)
      subst j
      exact Prod.ext ss (Prod.ext rfl (Additive.toMul.injective (Subtype.ext (mul_right_cancel gg)))) }
  let carry (i : Fin 11) (s : ℕ) : Additive K :=
    if i.val+s ≥ 11 then Additive.ofMul c else 0
  have advance (i : Fin 11) (s : ℕ) (small : s=1 ∨ s=2 ∨ s=3) :
      ((carry i s).toMul:A)*a^(i+(Fin.ofNat 11 s)).val = a^i.val*a^s := by
    have ev : (if i.val+s ≥ 11 then 11 else 0) + (i+(Fin.ofNat 11 s)).val = i.val+s := by
      rcases small with rfl|rfl|rfl <;> fin_cases i <;> decide
    have ca : ((carry i s).toMul : A) = a^(if i.val+s ≥ 11 then 11 else 0) := by
      by_cases hi : i.val+s ≥ 11 <;> simp [carry,hi,c]
    rw [ca,←pow_add,ev,pow_add]
  have hzero (i : Fin 11) (u : Additive K) : G.Adj (ι (false,i,u)) (ι (true,i,u)) := h0 _
  have hone (i : Fin 11) (u : Additive K) : G.Adj (ι (false,i,u))
      (ι (true,i+1,u+(if i.val+1 ≥ 11 then Additive.ofMul c else 0))) := by
    change G.Adj (false,(u.toMul:A)*a^i.val) (true,((u.toMul:A)*(carry i 1).toMul)*a^(i+1).val)
    have eq : ((u.toMul:A)*(carry i 1).toMul)*a^(i+1).val=((u.toMul:A)*a^i.val)*a := by
      rw [mul_assoc,show (i+1).val=(i+(Fin.ofNat 11 1)).val from rfl, advance i 1 (.inl rfl),pow_one,mul_assoc]
    rw [eq]
    exact ha _
  have hd (i : Fin 11) (u : Additive K) : G.Adj (ι (false,i,u))
      (ι (true,i+Fin.ofNat 11 d,u+v i+(if i.val+d ≥ 11 then Additive.ofMul c else 0))) := by
    change G.Adj (false,(u.toMul:A)*a^i.val)
      (true,(((u.toMul:A)*(a^i.val*(n:A)*(a^i.val)⁻¹))*(carry i d).toMul)*a^(i+Fin.ofNat 11 d).val)
    have eq : (((u.toMul:A)*(a^i.val*(n:A)*(a^i.val)⁻¹))*(carry i d).toMul)*a^(i+Fin.ofNat 11 d).val =
        ((u.toMul:A)*a^i.val)*b := by
      rw [mul_assoc,advance i d (.inr dsmall),← bform]
      group
    rw [eq]
    exact hb _
  rcases dsmall with rfl|rfl
  · have fixed : MonoidHom.toAdditive T (Additive.ofMul c) = Additive.ofMul c := by
      apply Additive.ofMul.injective
      apply Subtype.ext
      change a*a^11*a⁻¹=a^11
      group
    exact HaarElevenProgression.coordinates32 v (Additive.ofMul c) (MonoidHom.toAdditive T)
      rot fixed ne G ι hzero hone hd
  · exact coordinates32 v (Additive.ofMul c) (MonoidHom.toAdditive T) rot ne G ι hzero hone hd
end HaarCyclicEleven

namespace HaarCyclicEleven
open SimpleGraph

/-- Up to choosing the base label and reordering the other two, every triple of
distinct residues modulo eleven has ratio two or three. -/
private theorem orient : ∀ a b : ZMod 11, a≠0 → b≠0 → a≠b →
    ∃ i j k : Fin 3, i≠j ∧ i≠k ∧ j≠k ∧
      let s : Fin 3 → ZMod 11 := ![0,a,b]
      (s k-s i=2 • (s j-s i) ∨ s k-s i=3 • (s j-s i)) := by decide

/-- Every noncommuting pair whose three normalized shifts stay distinct modulo
an abelian normal kernel with cyclic quotient of order eleven forces C32. -/
theorem index_eleven_right {A : Type*} [Group A] (f : A →* Multiplicative (ZMod 11))
    (abelian : ∀ g h : f.ker, g*h=h*g) (a b : A)
    (fa : f a ≠ 1) (fb : f b ≠ 1) (fab : f a ≠ f b) (nc : ¬ Commute a b)
    (G : SimpleGraph (Bool × A)) (h0 : ∀ x,G.Adj (false,x) (true,x))
    (ha : ∀ x,G.Adj (false,x) (true,x*a)) (hb : ∀ x,G.Adj (false,x) (true,x*b)) :
    cycleGraph 32 ⊑ G := by
  let S : Fin 3 → A := ![1,a,b]
  have distinct : Function.Injective (fun i => f (S i)) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [S] at h <;> first | rfl | exact (fa h).elim | exact (fa h.symm).elim | exact (fb h).elim | exact (fb h.symm).elim | exact (fab h).elim | exact (fab h.symm).elim
  obtain ⟨i,j,k,ij,ik,jk,rel⟩ := orient (f a).toAdd (f b).toAdd
    (fun h => fa (Multiplicative.toAdd.injective h))
    (fun h => fb (Multiplicative.toAdd.injective h))
    (fun h => fab (Multiplicative.toAdd.injective h))
  let U (l : Fin 3) := S l*(S i)⁻¹
  have ui : U i=1 := mul_inv_cancel _
  have all (l : Fin 3) : l=i ∨ l=j ∨ l=k := by
    have check : ∀ i j k l : Fin 3, i≠j → i≠k → j≠k → l=i ∨ l=j ∨ l=k := by decide
    exact check i j k l ij ik jk
  have nc' : ¬ Commute (U j) (U k) := by
    intro cm
    have pair (l m : Fin 3) : Commute (U l) (U m) := by
      rcases all l with rfl | rfl | rfl <;> rcases all m with rfl | rfl | rfl <;>
        first | rw [ui]; simp | exact Commute.refl _ | exact cm | exact cm.symm
    have eq (l : Fin 3) : S l=U l*(U 0)⁻¹ := by dsimp [U,S]; group
    apply nc
    change Commute (S 1) (S 2)
    rw [eq 1,eq 2]
    exact ((pair 1 2).mul_right (pair 1 0).inv_right).mul_left
      ((pair 0 2).inv_left.mul_right (Commute.refl _))
  have fig (l : Fin 3) :
      (f (S l)).toAdd = (![0,(f a).toAdd,(f b).toAdd] : Fin 3 → ZMod 11) l := by
    fin_cases l <;> simp [S]
  have uval (l : Fin 3) :
      (f (U l)).toAdd=(f (S l)).toAdd-(f (S i)).toAdd := by
    change (f (S l*(S i)⁻¹)).toAdd = _
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv,sub_eq_add_neg]
  have fx : f (U j) ≠ 1 := by
    intro eq
    have z : (f (U j)).toAdd=0 := congrArg Multiplicative.toAdd eq
    rw [uval] at z
    exact ij ((distinct (Multiplicative.toAdd.injective (sub_eq_zero.mp z))).symm)
  have ord : orderOf (f (U j))=11 := by
    have dv := orderOf_dvd_natCard (f (U j))
    have card : Nat.card (Multiplicative (ZMod 11))=11 := by change Nat.card (ZMod 11)=11; simp
    rw [card] at dv
    exact ((Nat.dvd_prime (by decide : Nat.Prime 11)).mp dv).resolve_left
      (fun e => fx (orderOf_eq_one_iff.mp e))
  obtain ⟨d,small,r⟩ : ∃ d : ℕ, (d=2 ∨ d=3) ∧ f (U k)=(f (U j))^d := by
    rcases rel with h|h
    · refine ⟨2,.inl rfl,Multiplicative.toAdd.injective ?_⟩
      simpa only [toAdd_pow,uval,fig] using h
    · refine ⟨3,.inr rfl,Multiplicative.toAdd.injective ?_⟩
      simpa only [toAdd_pow,uval,fig] using h
  let e : (Bool × A) ↪ (Bool × A) := {
    toFun z := (z.1,if z.1 then z.2*S i else z.2)
    inj' := by
      rintro ⟨s,x⟩ ⟨t,y⟩ eq
      have st := congrArg (fun z : Bool × A => z.1) eq
      change s=t at st
      subst t
      cases s <;> simpa using eq }
  have label (l : Fin 3) (x : A) : G.Adj (false,x) (true,x*S l) := by
    fin_cases l
    · simpa [S] using h0 x
    · exact ha x
    · exact hb x
  have lifted (l : Fin 3) (x : A) : (G.comap e).Adj (false,x) (true,x*U l) := by
    change G.Adj (false,x) (true,(x*(S l*(S i)⁻¹))*S i)
    simpa [mul_assoc] using label l x
  have down := index_eleven_ratio f abelian (U j) (U k) d small ord r nc' (G.comap e)
    (fun x => label i x) (lifted j) (lifted k)
  exact down.trans (isContained_iff_exists_le_comap.mpr ⟨e,le_rfl⟩)

end HaarCyclicEleven


namespace HaarOddRectangle

open SimpleGraph

theorem stencil {A T : Type*} [Group A] (a b c : A) (ba : b*a=c*b)
    (nc : ¬Commute a b) (G : SimpleGraph (Bool × A)) (h0 : ∀ x,G.Adj (false,x) (true,x))
    (ha : ∀ x,G.Adj (false,x) (true,x*a)) (hb : ∀ x,G.Adj (false,x) (true,x*b))
    (v : T → A) (inj : Function.Injective v) (central : ∀ i,Commute a (v i))
    (L U : T → T → Prop) (low : ∀ i j,L i j → v j=v i*a) (high : ∀ i j,U i j → v j=v i*c)
    {n : ℕ} (p : Fin n → Bool × Bool × T) (distinct : Function.Injective p)
    :
    let forward (v w : Bool × Bool × T) : Prop :=
      v.1=false ∧ w.1=true ∧ ((v.2=w.2) ∨ (v.2.1=false ∧ w.2.1=true ∧ v.2.2=w.2.2) ∨
        (v.2.1=false ∧ w.2.1=false ∧ L v.2.2 w.2.2) ∨ (v.2.1=true ∧ w.2.1=true ∧ U v.2.2 w.2.2))
    (∀ i j,(cycleGraph n).Adj i j → forward (p i) (p j) ∨ forward (p j) (p i)) →
    cycleGraph n ⊑ G := by
  intro forward edges
  let g (q : Bool × T) := if q.1 then v q.2*b else v q.2
  have disjoint (i j : T) : v i*b≠v j := by
    intro eq
    have bval : b=(v i)⁻¹ * v j := by rw [←eq]; simp
    exact nc (bval ▸ (central i).inv_right.mul_right (central j))
  have injective : Function.Injective g := by
    rintro ⟨u,i⟩ ⟨w,j⟩ eq
    cases u <;> cases w
    · exact Prod.ext rfl (inj eq)
    · exact (disjoint j i eq.symm).elim
    · exact (disjoint i j eq).elim
    · exact Prod.ext rfl (inj (mul_right_cancel eq))
  let f (z : Bool × Bool × T) := (z.1,g z.2)
  have oriented (z w : Bool × Bool × T) (e : forward z w) : G.Adj (f z) (f w) := by
    obtain ⟨s,t,i⟩ := z
    obtain ⟨q,r,j⟩ := w
    obtain ⟨rfl,rfl,eq|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,hl⟩|⟨rfl,rfl,hu⟩⟩ := e
    · change G.Adj (false,g (t,i)) (true,g (r,j))
      change (t,i)=(r,j) at eq
      rw [eq]
      exact h0 _
    · exact hb _
    · simpa [f,g, low _ _ hl] using ha (v i)
    · simpa [f,g, high _ _ hu,mul_assoc,ba] using ha (v i*b)
  let h : cycleGraph n →g G := ⟨fun i => f (p i),fun {i j} h =>
    (edges i j h).elim (oriented _ _) (fun e => (oriented _ _ e).symm)⟩
  exact ⟨h.toCopy (fun i j eq => distinct (Prod.ext (congrArg (fun z : Bool × A => z.1) eq) (injective (congrArg (fun z : Bool × A => z.2) eq))))⟩

theorem odd_square {A : Type*} [Group A] [Finite A] (h : Odd (Nat.card A)) (a : A) :
    ∃ m : ℕ,(a^2)^m=a := by
  obtain ⟨k,hk⟩ := h
  refine ⟨k+1,?_⟩
  rw [←pow_mul,show 2*(k+1)=Nat.card A+1 by omega,pow_succ,pow_card_eq_one',one_mul]

theorem triangle {A : Type*} [Group A] (c : A) (c1 : c≠1) (c2 : c^2≠1) :
    Function.Injective (![1,c,c^2] : Fin 3 → A) := by
  have d : c^2≠c := by
    intro eq
    exact c1 (by simpa [sq] using eq)
  intro i j eq
  fin_cases i <;> fin_cases j <;> first | rfl | exact (c1 eq).elim | exact (c1 eq.symm).elim | exact (c2 eq).elim | exact (c2 eq.symm).elim | exact (d eq).elim | exact (d eq.symm).elim

theorem rectangle {A : Type*} [Group A] (a b c : A) (ba : b*a=c*b)
    (nc : ¬Commute a b) (ac : Commute a c)
    (G : SimpleGraph (Bool × A)) (h0 : ∀ x,G.Adj (false,x) (true,x))
    (ha : ∀ x,G.Adj (false,x) (true,x*a)) (hb : ∀ x,G.Adj (false,x) (true,x*b))
    (c1 : c≠1) (c2 : c^2≠1) (h : ∀ k : ℤ,-2≤k → k≤2 → a≠c^k) : cycleGraph 16 ⊑ G := by
  let t (i : Fin 3) := c^(i:ℕ)
  have ti : Function.Injective t := by
    have eq : t=(![1,c,c^2] : Fin 3 → A) := by funext i; fin_cases i <;> simp [t]
    exact eq ▸ triangle c c1 c2
  have dj (i j : Fin 3) : t i ≠ a*t j := by
    intro eq
    have anti : (t i)*(t j)⁻¹ = a := by rw [eq,mul_inv_cancel_right]
    apply h ((i.val:ℤ)-(j.val:ℤ)) (by omega) (by omega)
    simpa [t,zpow_sub] using anti.symm
  let v (z : Bool × Fin 3) := if z.1 then a*t z.2 else t z.2
  have vi : Function.Injective v := by
    rintro ⟨r,i⟩ ⟨s,j⟩ eq
    cases r <;> cases s
    · exact Prod.ext rfl (ti eq)
    · exact (dj _ _ eq).elim
    · exact (dj _ _ eq.symm).elim
    · exact Prod.ext rfl (ti (mul_left_cancel eq))
  have cen (i : Bool × Fin 3) : Commute a (v i) := by
    obtain ⟨r,i⟩ := i
    cases r
    · exact ac.pow_right _
    · exact (Commute.refl a).mul_right (ac.pow_right _)
  let L (u w : Bool × Fin 3) := u.1=false ∧ w.1=true ∧ u.2=w.2
  let U (u w : Bool × Fin 3) := u.1=w.1 ∧ w.2.val=u.2.val+1
  have low (i j : Bool × Fin 3) (e : L i j) : v j=v i*a := by
    obtain ⟨r,k⟩ := i
    obtain ⟨s,l⟩ := j
    obtain ⟨rfl,rfl,rfl⟩ := e
    exact (ac.pow_right _).eq
  have high (i j : Bool × Fin 3) (e : U i j) : v j=v i*c := by
    obtain ⟨r,k⟩ := i
    obtain ⟨s,l⟩ := j
    obtain ⟨rfl,h⟩ := e
    change l.val=k.val+1 at h
    cases r <;> simp [v,t,h,pow_succ,mul_assoc]
  let p : Fin 16 → Bool × Bool × Bool × Fin 3 := ![
    (false,false,false,0),(true,false,true,0),(false,false,true,0),(true,true,true,0),
    (false,true,true,0),(true,true,true,1),(false,true,true,1),(true,true,true,2),
    (false,false,true,2),(true,false,true,2),(false,false,false,2),(true,true,false,2),
    (false,true,false,1),(true,true,false,1),(false,true,false,0),(true,true,false,0)]
  apply stencil a b c ba nc G h0 ha hb v vi cen L U low high p
  · change ∀ i j,p i=p j → i=j
    dsimp only [p]
    decide
  · dsimp only [p,L,U]
    decide

theorem short {A : Type*} [Group A] (a b c : A) (ba : b*a=c*b)
    (nc : ¬Commute a b) (ac : Commute a c)
    (G : SimpleGraph (Bool × A)) (h0 : ∀ x,G.Adj (false,x) (true,x))
    (ha : ∀ x,G.Adj (false,x) (true,x*a)) (hb : ∀ x,G.Adj (false,x) (true,x*b))
    (c1 : c≠1) (c2 : c^2≠1) (eq : a=c^2 ∨ a=(c^2)⁻¹) : cycleGraph 8 ⊑ G := by
  let v : Fin 3 → A := ![1,c,c^2]
  have vi : Function.Injective v := triangle c c1 c2
  have cen (i : Fin 3) : Commute a (v i) := by
    fin_cases i
    · exact Commute.one_right a
    · exact ac
    · exact ac.pow_right 2
  let U (i j : Fin 3) := (i=0 ∧ j=1) ∨ (i=1 ∧ j=2)
  have high (i j : Fin 3) (e : U i j) : v j=v i*c := by
    rcases e with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact (one_mul c).symm
    · exact sq c
  rcases eq with f|f
  · let L (i j : Fin 3) := i=0 ∧ j=2
    have low (i j : Fin 3) (e : L i j) : v j=v i*a := by
      obtain ⟨rfl,rfl⟩ := e
      change c^2=1*a
      simp [f]
    let p : Fin 8 → Bool × Bool × Fin 3 := ![
      (false,false,0),(true,false,2),(false,false,2),(true,true,2),
      (false,true,1),(true,true,1),(false,true,0),(true,true,0)]
    apply stencil a b c ba nc G h0 ha hb v vi cen L U low high p
    · change ∀ i j,p i=p j → i=j
      dsimp only [p]
      decide
    · dsimp only [p,L,U]
      decide
  · let L (i j : Fin 3) := i=2 ∧ j=0
    have low (i j : Fin 3) (e : L i j) : v j=v i*a := by
      obtain ⟨rfl,rfl⟩ := e
      change 1=c^2*a
      simp [f]
    let p : Fin 8 → Bool × Bool × Fin 3 := ![
      (false,false,2),(true,false,0),(false,false,0),(true,true,0),
      (false,true,0),(true,true,1),(false,true,1),(true,true,2)]
    apply stencil a b c ba nc G h0 ha hb v vi cen L U low high p
    · change ∀ i j,p i=p j → i=j
      dsimp only [p]
      decide
    · dsimp only [p,L,U]
      decide

theorem regular_right {A : Type*} [Group A] [Finite A] (odd : Odd (Nat.card A))
    (a b : A) (nc : ¬Commute a b) (localComm : Commute a (b*a*b⁻¹))
    (G : SimpleGraph (Bool × A)) (h0 : ∀ x,G.Adj (false,x) (true,x))
    (ha : ∀ x,G.Adj (false,x) (true,x*a)) (hb : ∀ x,G.Adj (false,x) (true,x*b)) :
    cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  let c := b*a*b⁻¹
  have ba : b*a=c*b := by simp [c]
  have a1 : a≠1 := by rintro rfl; exact nc (Commute.one_left _)
  have c1 : c≠1 := by
    intro eq
    exact a1 (mul_left_cancel (a:=b) (by simpa [eq] using ba : b*a=b*1))
  have c2 : c^2≠1 := by
    intro eq
    obtain ⟨m,hm⟩ := odd_square odd c
    apply c1
    simpa [eq] using hm.symm
  by_cases h : ∀ k : ℤ,-2≤k → k≤2 → a≠c^k
  · exact .inr (rectangle a b c ba nc localComm G h0 ha hb c1 c2 h)
  push Not at h
  obtain ⟨k,min,max,f⟩ := h
  interval_cases k
  · exact .inl (short a b c ba nc localComm G h0 ha hb c1 c2 (.inr (by simpa using f)))
  · have e : a=c⁻¹ := by simpa using f
    have rev : c=a⁻¹ := by simp [e]
    have s : SemiconjBy b a a⁻¹ := by simpa [SemiconjBy,rev] using ba
    have t : SemiconjBy b a⁻¹ a := by simpa using s.zpow_right (-1)
    have two : Commute (b^2) a := by simpa only [sq,Commute] using t.mul_left s
    obtain ⟨m,hm⟩ := odd_square odd b
    exact (nc (hm ▸ (two.pow_left m).symm)).elim
  · exact (a1 (by simpa using f)).elim
  · exact (nc (by change a*b=b*a; simpa [show a=c by simpa using f] using ba.symm)).elim
  · exact .inl (short a b c ba nc localComm G h0 ha hb c1 c2 (.inl (by simpa using f)))

theorem abelian_normal_right {A : Type*} [Group A] [Finite A] (odd : Odd (Nat.card A))
    (a b : A) (nc : ¬Commute a b) (N : Subgroup A) [hn : N.Normal] [IsMulCommutative N]
    (coset : a ∈ N ∨ b ∈ N ∨ b*a⁻¹ ∈ N) (G : SimpleGraph (Bool × A))
    (h0 : ∀ x,G.Adj (false,x) (true,x)) (ha : ∀ x,G.Adj (false,x) (true,x*a))
    (hb : ∀ x,G.Adj (false,x) (true,x*b)) : cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  have commuteConj (u v : A) (mem : u∈N) : Commute u (v*u*v⁻¹) :=
    setLike_mul_comm mem (hn.conj_mem _ mem _)
  rcases coset with aN|bN|dN
  · exact regular_right odd a b nc (commuteConj _ b aN) G h0 ha hb
  · exact regular_right odd b a (fun h => nc h.symm) (commuteConj _ a bN) G h0 hb ha
  · let d := b*a⁻¹
    have ds : ¬Commute d a⁻¹ := by
      intro h
      have da : Commute d a := by simpa using h.inv_right
      have ba : Commute (d*a) a := da.mul_left (Commute.refl _)
      exact nc (by simpa [d] using ba.symm)
    let f : (Bool × A) ↪ (Bool × A) := {
      toFun z := (z.1,if z.1 then z.2*a else z.2)
      inj' := by
        rintro ⟨r,x⟩ ⟨s,y⟩ eq
        cases r <;> cases s <;> simp_all }
    have hzero (x : A) : (G.comap f).Adj (false,x) (true,x) := ha x
    have hd (x : A) : (G.comap f).Adj (false,x) (true,x*d) := by
      change G.Adj (false,x) (true,x*d*a)
      simpa [d,mul_assoc] using hb x
    have hs (x : A) : (G.comap f).Adj (false,x) (true,x*a⁻¹) := by
      change G.Adj (false,x) (true,x*a⁻¹*a)
      simpa using h0 x
    have lift : G.comap f ⊑ G := ⟨(SimpleGraph.Embedding.comap f G).toCopy⟩
    exact (regular_right odd d a⁻¹ ds (commuteConj _ a⁻¹ dN) (G.comap f) hzero hd hs).imp
      (fun h => h.trans lift) (fun h => h.trans lift)

theorem abelian_normal_left {A : Type*} [Group A] [Finite A] (odd : Odd (Nat.card A))
    (a b : A) (nc : ¬Commute a b) (N : Subgroup A) [N.Normal] [IsMulCommutative N]
    (coset : a ∈ N ∨ b ∈ N ∨ b*a⁻¹ ∈ N) (G : SimpleGraph (Bool × A))
    (h0 : ∀ x,G.Adj (false,x) (true,x)) (ha : ∀ x,G.Adj (false,x) (true,a*x))
    (hb : ∀ x,G.Adj (false,x) (true,b*x)) : cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  let f : (Bool × A) ↪ (Bool × A) := {
    toFun v := (!v.1,v.2⁻¹)
    inj' := by
      rintro ⟨s,x⟩ ⟨t,y⟩ eq
      have b := congrArg Prod.fst eq
      have z := congrArg Prod.snd eq
      exact Prod.ext (by simpa using b) (inv_injective z) }
  have hzero (x : A) : (G.comap f).Adj (false,x) (true,x) := (h0 x⁻¹).symm
  have hra (x : A) : (G.comap f).Adj (false,x) (true,x*a) := by
    change G.Adj (true,x⁻¹) (false,(x*a)⁻¹)
    simpa [mul_assoc] using (ha ((x*a)⁻¹)).symm
  have hrb (x : A) : (G.comap f).Adj (false,x) (true,x*b) := by
    change G.Adj (true,x⁻¹) (false,(x*b)⁻¹)
    simpa [mul_assoc] using (hb ((x*b)⁻¹)).symm
  have lift : G.comap f ⊑ G := ⟨(SimpleGraph.Embedding.comap f G).toCopy⟩
  exact (abelian_normal_right odd a b nc N coset (G.comap f) hzero hra hrb).imp
    (fun h => h.trans lift) (fun h => h.trans lift)


end HaarOddRectangle

/- Sharp short cycles over an abelian normal subgroup of index eleven. -/
namespace HaarCyclicEleven
open SimpleGraph

/-- Every three-shift Haar graph on a finite odd-order group with an abelian normal
subgroup of index eleven has a simple cycle of length 4, 8, 16, or 32. -/
theorem abelian_index_eleven_left {A : Type*} [Group A] [Finite A] (odd : Odd (Nat.card A))
    (N : Subgroup A) [N.Normal] [IsMulCommutative N] (idx : N.index=11)
    (a b : A) (an : a≠1) (bn : b≠1) (ab : a≠b)
    (G : SimpleGraph (Bool × A)) (h0 : ∀ x,G.Adj (false,x) (true,x))
    (ha : ∀ x,G.Adj (false,x) (true,a*x)) (hb : ∀ x,G.Adj (false,x) (true,b*x)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  classical
  by_cases cm : Commute a b
  · let p := Equiv.mulLeft a
    let q := Equiv.mulLeft b
    have sep (x : A) : p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x := by simpa [p,q] using And.intro an (And.intro bn ab)
    have commute (x : A) : p (q x) = q (p x) := by
      change a*(b*x)=b*(a*x); rw [← mul_assoc,cm.eq,mul_assoc]
    obtain h|h|h := OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.LocalCommutation.near0 G p q sep
      h0 ha hb 1 (commute _) (commute _) (commute _) (commute _)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  by_cases collision : a ∈ N ∨ b ∈ N ∨ b*a⁻¹ ∈ N
  · rcases HaarOddRectangle.abelian_normal_left odd a b cm N collision G h0 ha hb with h|h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  push Not at collision
  have card : Nat.card (A ⧸ N)=11 := N.index_eq_card.symm.trans idx
  have zcard : Nat.card (Multiplicative (ZMod 11))=11 := by change Nat.card (ZMod 11)=11; simp
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let e := mulEquivOfPrimeCardEq card zcard
  let f := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have ker : f.ker=N := (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
  have abelian (x y : f.ker) : x*y=y*x := by
    have hx : (x : A) ∈ N := ker ▸ x.property
    have hy : (y : A) ∈ N := ker ▸ y.property
    apply Subtype.ext
    change (x:A)*(y:A)=(y:A)*(x:A)
    exact congrArg (fun z : N => (z:A))
      ((inferInstance : IsMulCommutative N).is_comm.comm (⟨x,hx⟩ : N) (⟨y,hy⟩ : N))
  have fx : f a ≠ 1 := fun h => collision.1 (ker ▸ (show a ∈ f.ker from h))
  have fy : f b ≠ 1 := fun h => collision.2.1 (ker ▸ (show b ∈ f.ker from h))
  have fxy : f a ≠ f b := by
    intro eq
    have id : f (b*a⁻¹) = 1 := by rw [map_mul,map_inv,eq,mul_inv_cancel]
    exact collision.2.2 (ker ▸ (show b*a⁻¹ ∈ f.ker from id))
  let t : (Bool × A) ↪ (Bool × A) := {
    toFun v := (!v.1,v.2⁻¹)
    inj' := by
      rintro ⟨s,x⟩ ⟨u,y⟩ eq
      have b := congrArg Prod.fst eq
      have z := congrArg Prod.snd eq
      exact Prod.ext (by simpa using b) (inv_injective z) }
  have hzero (x : A) : (G.comap t).Adj (false,x) (true,x) := (h0 x⁻¹).symm
  have hra (x : A) : (G.comap t).Adj (false,x) (true,x*a) := by
    change G.Adj (true,x⁻¹) (false,(x*a)⁻¹)
    simpa [mul_assoc] using (ha ((x*a)⁻¹)).symm
  have hrb (x : A) : (G.comap t).Adj (false,x) (true,x*b) := by
    change G.Adj (true,x⁻¹) (false,(x*b)⁻¹)
    simpa [mul_assoc] using (hb ((x*b)⁻¹)).symm
  exact .inr (.inr (.inr ((index_eleven_right f abelian a b fx fy fxy cm (G.comap t) hzero hra hrb).trans
    (isContained_iff_exists_le_comap.mpr ⟨t,le_rfl⟩))))
end HaarCyclicEleven


/-
# Free orbits in the odd generated permutation case

PR 6375 isolates odd generated groups in the matching presentation from PR 5246
and @JamesSlash's PR 592. We use the orbit embedding of PR 5820 at a single
point whose stabilizer is trivial. Other orbits may have nontrivial stabilizers.
An abelian normal subgroup of index eleven then forces a 4-, 8-, 16- or 32-cycle
in the embedded regular matching graph. Codex, gpt-6.2-astra.
-/

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1
open SimpleGraph

/-- Odd actions in which the generated group has a nonidentity stabilizer element at every point. -/
def H1 : Prop :=
  ∀ (X : Type) [Fintype X] [Nonempty X] (p q : Equiv.Perm X),
    (∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) →
    Fintype.card X ≤ 3 * {x : X | p (q x) ≠ q (p x)}.ncard →
    Odd (Nat.card (Subgroup.closure ({p,q} : Set (Equiv.Perm X)))) →
    (∀ x : X, ∃ g ∈ Subgroup.closure ({p,q} : Set (Equiv.Perm X)), g ≠ 1 ∧ g x=x) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × X =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=p u.2 ∨ v.2=q u.2))

/-- Two-generated odd groups with no abelian normal subgroup of index eleven. -/
def H2 : Prop :=
  ∀ (A : Type) [Group A] [Fintype A] (a b : A),
    Subgroup.closure ({a,b} : Set A)=⊤ → a≠1 → b≠1 → a≠b → Odd (Nat.card A) →
    (∀ N : Subgroup A, N.Normal → IsMulCommutative N → N.index≠11) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2.H1 := by
  intro nonfree regular X _ _ p q separated density odd
  classical
  let K := Subgroup.closure ({p,q} : Set (Equiv.Perm X))
  by_cases allFixed : ∀ x : X, ∃ g ∈ K, g ≠ 1 ∧ g x=x
  · exact nonfree X p q separated density odd allFixed
  obtain ⟨z,free⟩ := not_forall.mp allFixed
  let a : K := ⟨p,Subgroup.subset_closure (by simp)⟩
  let b : K := ⟨q,Subgroup.subset_closure (by simp)⟩
  let ev (g : K) := (g : Equiv.Perm X) z
  have an : a≠1 := fun h => (separated z).1 (congrArg ev h)
  have bn : b≠1 := fun h => (separated z).2.1 (congrArg ev h)
  have ab : a≠b := fun h => (separated z).2.2 (congrArg ev h)
  let R := SimpleGraph.fromRel (fun u v : Bool × K =>
    u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))
  have cyc : ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ R := by
    by_cases absent : ∀ N : Subgroup K, N.Normal → IsMulCommutative N → N.index≠11
    · have gen : Subgroup.closure ({a,b} : Set K)=⊤ := by
        apply Subgroup.map_injective (f := K.subtype) Subtype.coe_injective
        rw [MonoidHom.map_closure,←MonoidHom.range_eq_map,Subgroup.subtype_range,Set.image_pair]
        rfl
      exact regular K a b gen an bn ab odd absent
    · push Not at absent
      obtain ⟨N,normal,comm,idx⟩ := absent
      obtain h|h|h|h := HaarCyclicEleven.abelian_index_eleven_left odd N idx a b an bn ab R
        (fun x => ⟨by simp,Or.inl ⟨rfl,rfl,Or.inl rfl⟩⟩)
        (fun x => ⟨by simp,Or.inl ⟨rfl,rfl,Or.inr (Or.inl rfl)⟩⟩)
        (fun x => ⟨by simp,Or.inl ⟨rfl,rfl,Or.inr (Or.inr rfl)⟩⟩)
      · exact ⟨2,by decide,h⟩
      · exact ⟨3,by decide,h⟩
      · exact ⟨4,by decide,h⟩
      · exact ⟨5,by decide,h⟩
  obtain ⟨k,hk,cycle⟩ := cyc
  have inj : Function.Injective ev := by
    intro g h eq
    have trivial : h⁻¹*g=1 := by
      by_contra ne
      apply free
      refine ⟨↑(h⁻¹*g),(h⁻¹*g).property,fun t => ne (Subtype.ext t),?_⟩
      change h.val.symm (ev g)=z
      rw [eq]
      exact h.val.symm_apply_apply _
    exact (inv_mul_eq_one.mp trivial).symm
  let j : Bool × K ↪ Bool × X := (Function.Embedding.refl Bool).prodMap ⟨ev,inj⟩
  have edge (s t : Bool × K) (hs : s.1=false) (ht : t.1=true)
      (he : t.2=s.2 ∨ t.2=a*s.2 ∨ t.2=b*s.2) :
      (j s).1=false ∧ (j t).1=true ∧
      ((j t).2=(j s).2 ∨ (j t).2=p (j s).2 ∨ (j t).2=q (j s).2) := by
    refine ⟨hs,ht,?_⟩
    rcases he with h|h|h
    · exact Or.inl (congrArg ev h)
    · exact Or.inr (Or.inl (congrArg ev h))
    · exact Or.inr (Or.inr (congrArg ev h))
  refine ⟨k,hk,cycle.trans (isContained_iff_exists_le_comap.mpr ⟨j,?_⟩)⟩
  intro s t h
  refine ⟨fun eq => h.1 (j.injective eq),?_⟩
  rcases h.2 with ⟨hs,ht,he⟩|⟨ht,hs,he⟩
  · exact Or.inl (edge s t hs ht he)
  · exact Or.inr (edge t s ht hs he)

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1
