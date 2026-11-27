import OMAReductions.R_Erdos107_erdos_107_R1_H1_R1

/-!
Decompose the classical seventeen-point convex hexagon theorem into a geometric
change of coordinates and a finite problem about Boolean orientation signs.
The distinguished vertex labelled zero has positive orientations after the
projective normalization. Within a chosen six-set a different anchor, its
least vertex, suffices to check its ten anchored four-subsets.

Szekeres and Peters established the seventeen-point result by exhaustive
enumeration (ANZIAM Journal 48 (2006), 151–164). Filip Marić gave a SAT-based
formalization in Isabelle/HOL. The SAT approach to convex and empty hexagons is
also studied by Subercaseaux, Nawrocki, Gallicchio, Codel, Carneiro and Heule
(ITP 2024). This reduction uses the orientation encoding of the upstream
reduction by zarnab222-dev and gives an independent elementary parity argument.
-/

namespace OMA.R_Erdos107_erdos_107_R1_H1_R1_H2_R1

private theorem separated (u v w z : Bool)
    (h : (u=v ∧ v=w) ∨ (u=v ∧ w=z) ∨ (v=w ∧ w=z)) :
    (u=v ∧ w=z) ↔ ((u.xor v).xor w).xor z=false := by
  revert h
  cases u <;> cases v <;> cases w <;> cases z <;> decide

private theorem five (p q r s t u a b c d : Bool) :
    let xor4 (v w x y : Bool) := ((v.xor w).xor x).xor y
    xor4 a b c d = xor4 (xor4 p q s a) (xor4 p r t b) (xor4 q r u c) (xor4 s t u d) := by
  dsimp only
  have cancel (u v : Bool) : u.xor (u.xor v)=v := by cases u <;> cases v <;> decide
  simp only [Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]
  simp only [cancel]

/-- Geometric normalization and transfer of four-point convexity under relabelling. -/
def H1 : Prop :=
  let C := Fin 17 → Fin 17 → Fin 17 → Bool
  let packet (o : C) : Prop := ∀ a b c d, a<b → b<c → c<d →
    (o a b c=o a b d ∧ o a b d=o a c d) ∨
    (o a b c=o a b d ∧ o a c d=o b c d) ∨
    (o a b d=o a c d ∧ o a c d=o b c d)
  let even (o : C) (a b c d : Fin 17) : Prop :=
    (((o a b c).xor (o a b d)).xor (o a c d)).xor (o b c d) = false
  let allEven (o : C) (T : Finset (Fin 17)) : Prop :=
    ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T, a<b → b<c → c<d → even o a b c d
  ∀ o : C,
    (∃ x y : Fin 17 → ℤ, StrictMono x ∧
      ∀ a b c, a<b → b<c →
        let D := (x b-x a)*(y c-y a)-(y b-y a)*(x c-x a)
        D≠0 ∧ o a b c=decide (0<D)) →
    ∃ g : C, ∃ π : Equiv.Perm (Fin 17), packet g ∧
      (∀ b c, 0<b → b<c → g 0 b c=true) ∧
      ∀ S : Finset (Fin 17), allEven g S → allEven o (S.map π.toEmbedding)

/-- A finite, coordinate-free search. Only ten anchored parity tests are required. -/
def H2 : Prop :=
  let C := Fin 17 → Fin 17 → Fin 17 → Bool
  let packet (o : C) : Prop := ∀ a b c d, a<b → b<c → c<d →
    (o a b c=o a b d ∧ o a b d=o a c d) ∨
    (o a b c=o a b d ∧ o a c d=o b c d) ∨
    (o a b d=o a c d ∧ o a c d=o b c d)
  let even (o : C) (a b c d : Fin 17) : Prop :=
    (((o a b c).xor (o a b d)).xor (o a c d)).xor (o b c d) = false
  ∀ g : C, packet g → (∀ b c, 0<b → b<c → g 0 b c=true) →
    ∃ S : Finset (Fin 17), S.card=6 ∧ ∃ v ∈ S, (∀ a ∈ S, v≤a) ∧
      ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, v<a → a<b → b<c → even g v a b c

theorem main : H1 → H2 → OMA.R_Erdos107_erdos_107_R1_H1_R1.H2 := by
  intro normalize finite o polygon mono realized _
  obtain ⟨g,π,packet,apex,transfer⟩ := normalize o realized
  obtain ⟨S,hS,v,_,lo,test⟩ := finite g packet apex
  refine ⟨S.map π.toEmbedding,by simpa using hS,?_⟩
  intro a ha b hb c hc d hd ab bc cd
  apply (separated _ _ _ _ (mono a b c d ab bc cd)).2
  apply transfer S ?_ a ha b hb c hc d hd ab bc cd
  intro a ha b hb c hc d hd ab bc cd
  rcases (lo a ha).eq_or_lt with rfl|va
  · exact test b hb c hc d hd ab bc cd
  have h₁ := test a ha b hb c hc va ab bc
  have h₂ := test a ha b hb d hd va ab (bc.trans cd)
  have h₃ := test a ha c hc d hd va (ab.trans bc) cd
  have h₄ := test b hb c hc d hd (va.trans ab) bc cd
  dsimp only at h₁ h₂ h₃ h₄ ⊢
  have boundary := five (g v a b) (g v a c) (g v a d) (g v b c) (g v b d) (g v c d)
    (g a b c) (g a b d) (g a c d) (g b c d)
  dsimp only at boundary
  rw [h₁,h₂,h₃,h₄] at boundary
  exact boundary

end OMA.R_Erdos107_erdos_107_R1_H1_R1_H2_R1
