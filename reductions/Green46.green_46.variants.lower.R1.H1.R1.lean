import OMAReductions.R_Green46_green_46_variants_lower_R1

/-!
# Rounding the sieve for primes

Ford, Green, Konyagin, Maynard and Tao, *Long gaps between primes*,
JAMS 31 (2018), Section 4.3, Corollary 4 and Theorem 4.
The first hypothesis selects a good small-prime sieve and records the
finite distributions of its large-prime edges after exceptional vertices
have been discarded. The second is the finite covering consequence of
the hypergraph theorem. At most one prime larger than x/2 divides a given
nonzero vertex difference of size less than x²/4. Together with sparsity
this proves the codegree estimate needed for rounding. The union of the
exceptional vertices and the uncovered good vertices bounds the final
number of survivors.

The parent reduction by chris01-dev is PR 2548. Credit: @ZedingZhang.
-/

namespace OMA.R_Green46_green_46_variants_lower_R1_H1_R1

open Finset Filter Real
open scoped Classical

private lemma one_large_prime {x q r p s : ℕ} (qr : q < r) (short : 4*r < x*x)
    (pp : p.Prime) (sp : s.Prime) (lp : x < 2*p) (ls : x < 2*s)
    (dp : q ≡ r [MOD p]) (ds : q ≡ r [MOD s]) : p = s := by
  by_contra different
  have cp := (Nat.coprime_primes pp sp).mpr different
  have prod := cp.mul_dvd_of_dvd_of_dvd ((Nat.modEq_iff_dvd' qr.le).mp dp)
    ((Nat.modEq_iff_dvd' qr.le).mp ds)
  have bound := (Nat.le_of_dvd (Nat.sub_pos_of_lt qr) prod).trans (Nat.sub_le r q)
  have hx : x*x < (2*p)*(2*s) := lt_of_le_of_lt
    (Nat.mul_le_mul_right x lp.le) (Nat.mul_lt_mul_of_pos_left ls (by omega))
  nlinarith

private lemma pair_weight (P : Finset ℕ) (E : ℕ → Finset (Finset ℕ))
    (w : ℕ → Finset ℕ → ℝ) {x q r : ℕ} (qr : q < r) (short : 4*r < x*x)
    (large : ∀ p ∈ P, p.Prime ∧ x < 2*p)
    (labels : ∀ p ∈ P, ∀ e ∈ E p, ∃ a : ℕ, ∀ v ∈ e, v ≡ a [MOD p])
    (pos : ∀ p ∈ P, ∀ e ∈ E p, 0 ≤ w p e)
    {ε : ℝ} (hε : 0 ≤ ε)
    (sparse : ∀ p ∈ P, (∑ e ∈ (E p).filter (q ∈ ·), w p e) ≤ ε) :
    (∑ p ∈ P, ∑ e ∈ (E p).filter (fun e => q ∈ e ∧ r ∈ e), w p e) ≤ ε := by
  classical
  let J (p : ℕ) := (E p).filter (fun e => q ∈ e ∧ r ∈ e)
  change (∑ p ∈ P, ∑ e ∈ J p, w p e) ≤ ε
  have empty (p : ℕ) (hp : p ∈ P) (incompatible : ¬ q ≡ r [MOD p]) : J p = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro e he both
    obtain ⟨a, ha⟩ := labels p hp e he
    exact incompatible ((ha q both.1).trans (ha r both.2).symm)
  by_cases ex : ∃ p ∈ P, q ≡ r [MOD p]
  · obtain ⟨p, hp, hmod⟩ := ex
    have only : (∑ s ∈ P, ∑ e ∈ J s, w s e) = ∑ e ∈ J p, w p e := by
      apply Finset.sum_eq_single p
      · intro s hs hne
        have no : ¬ q ≡ r [MOD s] := fun h =>
          hne (one_large_prime qr short (large s hs).1 (large p hp).1
            (large s hs).2 (large p hp).2 h hmod)
        simp [empty s hs no]
      · intro h
        exact (h hp).elim
    rw [only]
    apply le_trans _ (sparse p hp)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      obtain ⟨he', hq, _⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨he', hq⟩
    · intro e he _
      exact pos p hp e (Finset.mem_filter.mp he).1
  · have zero : (∑ p ∈ P, ∑ e ∈ J p, w p e) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have no : ¬ q ≡ r [MOD p] := fun h => ex ⟨p, hp, h⟩
      simp [empty p hp no]
    simpa only [zero] using hε

/-- The good small-prime sieve and the finite laws of its congruence edges. -/
def H1 : Prop :=
  ∃ c K : ℝ, 0<c ∧ 3≤K ∧ ∀ᶠ x : ℕ in atTop,
    let X : ℝ := x
    let U := log (log X)
    let y := c*X*log X*log U/U
    let z := X^(log U/(4*U))
    let P := (Ioc (x/2) x).filter Nat.Prime
    ∃ a : ℕ → ℕ,
    let Q := (Ioc x ⌊y⌋₊).filter (fun q => q.Prime ∧
      ∀ p : ℕ, p.Prime → p ∉ P → log X^20 < p → (p:ℝ) ≤ z → ¬q ≡ a p [MOD p])
    ∃ (V : Finset ℕ) (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ) (C : ℝ),
      V ⊆ Q ∧ (∀ r ∈ V, 4*r < x*x) ∧ U^3 ≤ V.card ∧ (V.card:ℝ) ≤ K*X*U/log X ∧
      ((Q\V).card:ℝ) ≤ K*X/log X ∧ 3≤C ∧ C≤K ∧
      (∀ p ∈ P, ∀ e ∈ E p, e ⊆ V ∧ (e.card:ℝ) ≤ √(log X) ∧
        ∃ b : ℕ, ∀ q ∈ e, q ≡ b [MOD p]) ∧
      (∀ p ∈ P, (∑ e ∈ E p, w p e)=1 ∧ ∀ e ∈ E p, 0≤w p e) ∧
      (∀ p ∈ P, ∀ q ∈ V, (∑ e ∈ (E p).filter (q ∈ ·), w p e) ≤ X^(-3/5:ℝ)) ∧
      (∀ q ∈ V, |(∑ p ∈ P, ∑ e ∈ (E p).filter (q ∈ ·), w p e)-C| ≤ 1/U^2)

/-- A deterministic selection from a sparse, nearly regular finite hypergraph. -/
def H2 : Prop :=
  ∀ K : ℝ, 3≤K → ∃ D : ℝ, 0<D ∧ ∀ᶠ x : ℕ in atTop,
    let X : ℝ := x
    let U := log (log X)
    ∀ (P V : Finset ℕ) (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ) (C : ℝ),
      P.card ≤ x → U^3 ≤ V.card → 3≤C → C≤K →
      (∀ p ∈ P, ∀ e ∈ E p, e ⊆ V ∧ (e.card:ℝ) ≤ √(log X)) →
      (∀ p ∈ P, (∑ e ∈ E p, w p e)=1 ∧ ∀ e ∈ E p, 0≤w p e) →
      (∀ p ∈ P, ∀ q ∈ V, (∑ e ∈ (E p).filter (q ∈ ·), w p e) ≤ X^(-3/5:ℝ)) →
      (∀ q ∈ V, |(∑ p ∈ P, ∑ e ∈ (E p).filter (q ∈ ·), w p e)-C| ≤ 1/U^2) →
      (∀ q ∈ V, ∀ r ∈ V, q<r →
        (∑ p ∈ P, ∑ e ∈ (E p).filter (fun e => q ∈ e ∧ r ∈ e), w p e) ≤ X^(-3/5:ℝ)) →
      ∃ f : ℕ → Finset ℕ, (∀ p ∈ P, f p = ∅ ∨ f p ∈ E p) ∧
        ((V\P.biUnion f).card:ℝ) ≤ D*V.card/U

theorem main : H1 → H2 → OMA.R_Green46_green_46_variants_lower_R1.H1 := by
  classical
  intro model rounding
  obtain ⟨c, K, hc, hK, good⟩ := model
  obtain ⟨D, hD, round⟩ := rounding K hK
  refine ⟨c, hc, K+D*K, ?_⟩
  filter_upwards [good, round, OMA.R_Green46_green_46_variants_lower_R1.ev_log 1,
    OMA.R_Green46_green_46_variants_lower_R1.ev_log2 1] with x hg hr hlog hlog₂
  let X : ℝ := x
  let U := log (log X)
  let y := c*X*log X*log U/U
  let z := X^(log U/(4*U))
  let P := (Ioc (x/2) x).filter Nat.Prime
  obtain ⟨a, V, E, w, C, _, small, big, vupper, exceptional, hC, hCK, edges, prob, sparse, degrees⟩ := hg
  let Q := (Ioc x ⌊y⌋₊).filter (fun q => q.Prime ∧
    ∀ p : ℕ, p.Prime → p ∉ P → log X^20 < p → (p:ℝ) ≤ z → ¬q ≡ a p [MOD p])
  have large (p : ℕ) (hp : p ∈ P) : p.Prime ∧ x < 2*p := by
    obtain ⟨hm, pr⟩ := Finset.mem_filter.mp hp
    have lower := (Finset.mem_Ioc.mp hm).1
    exact ⟨pr, by omega⟩
  have psize : P.card ≤ x := by
    have le := Finset.card_le_card (Finset.filter_subset Nat.Prime (Ioc (x/2) x))
    simpa [P] using le.trans (show (Ioc (x/2) x).card ≤ x by simp)
  obtain ⟨f, choices, leftover⟩ := hr P V E w C psize big hC hCK
    (fun p hp e he => ⟨(edges p hp e he).1, (edges p hp e he).2.1⟩) prob sparse degrees
    (fun q hq r hr' qr => pair_weight P E w qr (small r hr') large
      (fun p hp e he => (edges p hp e he).2.2) (fun p hp => (prob p hp).2)
      (Real.rpow_nonneg (Nat.cast_nonneg x) _) (fun p hp => sparse p hp q hq))
  let b (p : ℕ) : ℕ := if hp : p ∈ P then
    if he : f p ∈ E p then Classical.choose ((edges p hp (f p) he).2.2) else 0 else a p
  have chosen (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ f p) : q ≡ b p [MOD p] := by
    rcases choices p hp with hem | he
    · simp [hem] at hq
    · simpa only [b, dif_pos hp, dif_pos he] using
        (Classical.choose_spec ((edges p hp (f p) he).2.2)) q hq
  refine ⟨b, ?_⟩
  let T : Set ℕ := {q | q.Prime ∧ x < q ∧ (q:ℝ) ≤ y ∧ ∀ p : ℕ, p.Prime →
    (log X^20 < p ∧ (p:ℝ) ≤ z ∨ x < 2*p ∧ p ≤ x) → ¬q ≡ b p [MOD p]}
  change (T.ncard:ℝ) ≤ (K+D*K)*X/log X
  have contained : T ⊆ (↑((Q\V) ∪ (V\P.biUnion f)) : Set ℕ) := by
    intro q hq
    obtain ⟨prime, low, high, missed⟩ := hq
    have inQ : q ∈ Q := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨low, Nat.le_floor high⟩, prime, ?_⟩
      intro p pp hp lo hi hit
      apply missed p pp (Or.inl ⟨lo,hi⟩)
      simpa only [b, dif_neg hp] using hit
    by_cases hv : q ∈ V
    · refine Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hv, ?_⟩))
      intro hu
      obtain ⟨p, hp, inc⟩ := Finset.mem_biUnion.mp hu
      have endp := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
      exact missed p (large p hp).1 (Or.inr ⟨(large p hp).2, endp⟩) (chosen p hp q inc)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨inQ,hv⟩))
  have count : T.ncard ≤ (Q\V).card + (V\P.biUnion f).card := by
    have le := Set.ncard_le_ncard contained (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at le
    exact le.trans (Finset.card_union_le _ _)
  have countR : (T.ncard:ℝ) ≤ ((Q\V).card:ℝ) + ((V\P.biUnion f).card:ℝ) := by exact_mod_cast count
  change ((Q\V).card:ℝ) ≤ K*X/log X at exceptional
  change (V.card:ℝ) ≤ K*X*U/log X at vupper
  change ((V\P.biUnion f).card:ℝ) ≤ D*V.card/U at leftover
  have hU : 0 < U := lt_of_lt_of_le zero_lt_one hlog₂
  have lx : 0 < log X := lt_of_lt_of_le zero_lt_one hlog
  calc
    (T.ncard:ℝ) ≤ K*X/log X + D*V.card/U := countR.trans (add_le_add exceptional leftover)
    _ ≤ K*X/log X + D*(K*X*U/log X)/U := by gcongr
    _ = (K+D*K)*X/log X := by field_simp

end OMA.R_Green46_green_46_variants_lower_R1_H1_R1
