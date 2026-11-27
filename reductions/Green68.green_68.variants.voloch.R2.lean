import FormalConjectures.GreensOpenProblems.«68»
import Mathlib

/-!
A reduction along the envelope argument in Voloch, Arcs in projective planes
 over prime fields, J. Geometry 38 (1990), 198--200.
H1 isolates Segre's envelope construction and its exceptional components.
H2 is the point bound obtained from the quadratic Veronese embedding and
Stöhr--Voloch. The numerical elimination keeps the sharper constant 8/9.
The small configurations are handled by interpolation, without a hypothesis.
The monomial-index construction below extends @marcusbuffett's proof of
R1.H2, PR 6061. The interpolation and numerical elimination are proved here.
-/

namespace OMA.R_Green68_green_68_variants_voloch_R2
open Green68 MvPolynomial Module Submodule Finset
open scoped Classical

private lemma quad_dim (K : Type) [Field K] :
    Module.finrank K (restrictTotalDegree (Fin 2) K 2) = 6 := by
  classical
  let E := {s : Fin 2 →₀ ℕ // s.sum (fun _ e ↦ e) ≤ 2}
  let T := {v : Fin 3 × Fin 3 // v.1.val + v.2.val ≤ 2}
  have bound (s : E) : s.val 0 + s.val 1 ≤ 2 := by
    have h := s.property
    rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl), Fin.sum_univ_two] at h
    exact h
  let f (s : E) : T := ⟨(⟨s.val 0, by have := bound s; omega⟩,
    ⟨s.val 1, by have := bound s; omega⟩), bound s⟩
  have inj : Function.Injective f := by
    intro x y he
    have h0 := congrArg (fun z : T ↦ z.val.1.val) he
    have h1 := congrArg (fun z : T ↦ z.val.2.val) he
    apply Subtype.ext
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have surj : Function.Surjective f := by
    intro y
    let s : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![y.val.1.val, y.val.2.val]
    have hs : s.sum (fun _ e ↦ e) ≤ 2 := by
      rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl), Fin.sum_univ_two]
      exact y.property
    refine ⟨⟨s, hs⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> rfl
  let : Finite E := Finite.of_injective f inj
  let := Fintype.ofFinite E
  let basis : Basis E K (restrictTotalDegree (Fin 2) K 2) := basisRestrictSupport K _
  rw [Module.finrank_eq_card_basis basis]
  exact (Fintype.card_congr (Equiv.ofBijective f ⟨inj, surj⟩)).trans (by decide)

private lemma conic_of_card_le_five (K : Type) [Field K]
    (A : Finset (Fin 2 → K)) (hA : A.card ≤ 5) :
    ∃ F : MvPolynomial (Fin 2) K, F ≠ 0 ∧ F.totalDegree ≤ 2 ∧
      ∀ a ∈ A, eval a F = 0 := by
  classical
  let U := restrictTotalDegree (Fin 2) K 2
  let ev : U →ₗ[K] (A → K) :=
    LinearMap.pi fun a : A => (aeval a.val).toLinearMap.comp U.subtype
  have hk : LinearMap.ker ev ≠ ⊥ := by
    intro hk
    have h := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hk)
    rw [show Module.finrank K U = 6 from quad_dim K] at h
    simp only [Module.finrank_pi, Fintype.card_coe] at h
    omega
  obtain ⟨u, hu, hn⟩ := (Submodule.ne_bot_iff _).mp hk
  refine ⟨u.val, fun h => hn (Subtype.ext h),
    (mem_restrictTotalDegree _ _ _).mp u.property, ?_⟩
  intro a ha
  exact congrFun hu ⟨a, ha⟩

/-- The geometric envelope step. The finite set Z lists each projective
point once, by normalizing its first nonzero coordinate to one. -/
def H1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ A : Finset (Fin 2 → ZMod p),
    MeetsLinesInAtMost 2 A → 6 ≤ A.card →
    (¬ ∃ Q : MvPolynomial (Fin 2) (ZMod p),
      Q ≠ 0 ∧ Q.totalDegree ≤ 2 ∧ ∀ a ∈ A, eval a Q = 0) →
    A.card ≤ p + 2 ∧
      (4 * A.card ≤ 3 * p + 5 ∨ A.card ≤ 4 * (p + 2 - A.card) ∨
        ∃ (n : ℕ) (F : MvPolynomial (Fin 3) (ZMod p)),
          3 ≤ n ∧ n ≤ 2 * (p + 2 - A.card) ∧ F.IsHomogeneous n ∧
          Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) F) ∧
          let Z := (univ : Finset (Fin 3 → ZMod p)).filter fun v =>
            (v 0 = 1 ∨ (v 0 = 0 ∧ v 1 = 1) ∨
              (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 1)) ∧ eval v F = 0
          A.card * n ≤ 2 * Z.card)

/-- The plane-curve point bound coming from Stöhr--Voloch and the quadratic
Veronese embedding. It applies independently of any arc or its envelope. -/
def H2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (n : ℕ)
    (F : MvPolynomial (Fin 3) (ZMod p)),
    3 ≤ n → 2 * n ≤ p → F.IsHomogeneous n →
    Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) F) →
    let Z := (univ : Finset (Fin 3 → ZMod p)).filter fun v =>
      (v 0 = 1 ∨ (v 0 = 0 ∧ v 1 = 1) ∨
        (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 1)) ∧ eval v F = 0
    5 * Z.card ≤ 10 * n * (n - 3) + 2 * n * (p + 5)

theorem main : H1 → H2 → type_of% @Green68.green_68.variants.voloch := by
  intro envelope points p _ hp A harc hsize
  by_cases hsmall : A.card ≤ 5
  · exact conic_of_card_le_five (ZMod p) A hsmall
  by_contra hconic
  obtain ⟨hcard, hcases⟩ := envelope p hp A harc (by omega) hconic
  have hp4 : 4 ≤ p := by omega
  have large : 44 * p + 40 < 45 * A.card := by
    have : (44 : ℝ) * p + 40 < 45 * A.card := by linarith
    exact_mod_cast this
  rcases hcases with hlow | hlow | ⟨n, F, hn, hnt, hhom, hirr, hinc⟩
  · omega
  · omega
  by_cases ht : 4 * (p + 2 - A.card) ≤ p
  · have hnp : 2 * n ≤ p := by omega
    have hcount := points p hp n F hn hnp hhom hirr
    dsimp only at hinc hcount
    have hcancel : 5 * A.card ≤ 20 * (n - 3) + 4 * (p + 5) := by
      nlinarith
    omega
  · omega

end OMA.R_Green68_green_68_variants_voloch_R2
