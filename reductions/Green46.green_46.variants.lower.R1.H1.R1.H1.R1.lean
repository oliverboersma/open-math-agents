import OMAReductions.R_Green46_green_46_variants_lower_R1_H1_R1

/-! Ford, Green, Konyagin, Maynard and Tao, Long gaps between primes, Theorem 4,
equations (4.30)–(4.32). The good small-prime sieve gives finite laws of integer
translates of one tuple. After exceptional primes have been removed, distinct
translates may define the same edge, so their probabilities must be added. -/

namespace OMA.R_Green46_green_46_variants_lower_R1_H1_R1_H1_R1

open Finset Filter Real
open scoped Classical

/-- The conditional integer-shift laws in FGKMT, Theorem 4, after fixing a good sieve. -/
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
    ∃ (H : Finset ℕ) (T : ℕ → Finset ℤ) (μ : ℕ → ℤ → ℝ) (C : ℝ),
      let hit (p q : ℕ) (t : ℤ) := ∃ h ∈ H, (q : ℤ) = t + (h : ℤ)*p
      let mass (p q : ℕ) := ∑ t ∈ (T p).filter (hit p q), μ p t
      40*c*X*U/log X ≤ Q.card ∧ (Q.card:ℝ) ≤ K*X*U/log X ∧
      (H.card:ℝ) ≤ √(log X) ∧ 3 ≤ C ∧ C ≤ K ∧
      (∀ p ∈ P, (∑ t ∈ T p, μ p t) = 1 ∧ ∀ t ∈ T p, 0 ≤ μ p t) ∧
      (∀ p ∈ P, ∀ q ∈ Q, mass p q ≤ X^(-3/5:ℝ)) ∧
      (((Q.filter (fun q => 1/U^2 < |(∑ p ∈ P, mass p q)-C|)).card:ℝ) ≤ X/log X)

/-- Push the finite laws of integer shifts forward to the induced hypergraph on surviving vertices. -/
def H2 : Prop :=
  ∀ (P V H : Finset ℕ) (T : ℕ → Finset ℤ) (μ : ℕ → ℤ → ℝ),
    (∀ p ∈ P, 0 < p) →
    (∀ p ∈ P, (∑ t ∈ T p, μ p t) = 1 ∧ ∀ t ∈ T p, 0 ≤ μ p t) →
    ∃ (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ),
      (∀ p ∈ P, ∀ e ∈ E p, e ⊆ V ∧ e.card ≤ H.card ∧
        ∃ b : ℕ, ∀ q ∈ e, q ≡ b [MOD p]) ∧
      (∀ p ∈ P, (∑ e ∈ E p, w p e)=1 ∧ ∀ e ∈ E p, 0 ≤ w p e) ∧
      (∀ p ∈ P, ∀ q ∈ V, (∑ e ∈ (E p).filter (q ∈ ·), w p e) =
        ∑ t ∈ (T p).filter (fun t => ∃ h ∈ H, (q : ℤ) = t + (h : ℤ)*p), μ p t)

/-- Size estimates at the two scales used to discard exceptional vertices. -/
def H3 : Prop :=
  ∀ c : ℝ, 0 < c → ∀ᶠ x : ℕ in atTop,
    let X : ℝ := x
    let U := log (log X)
    4*(c*X*log X*log U/U) < X*X ∧
      U^3 + X/log X ≤ 40*c*X*U/log X

theorem main : H1 → H2 → H3 → OMA.R_Green46_green_46_variants_lower_R1_H1_R1.H1 := by
  classical
  intro model push growth
  obtain ⟨c,K,hc,hK,model⟩ := model
  refine ⟨c,K,hc,hK,?_⟩
  filter_upwards [model, growth c hc, OMA.R_Green46_green_46_variants_lower_R1.ev_log 1] with x hx hg hlog
  let X : ℝ := x
  let U := log (log X)
  let y := c*X*log X*log U/U
  let z := X^(log U/(4*U))
  let P := (Ioc (x/2) x).filter Nat.Prime
  obtain ⟨a,H,T,μ,C,ql,qu,hs,cmin,cmax,law,sparse,exc⟩ := hx
  refine ⟨a,?_⟩
  let Q := (Ioc x ⌊y⌋₊).filter (fun q => q.Prime ∧
    ∀ p : ℕ, p.Prime → p ∉ P → log X^20 < p → (p:ℝ) ≤ z → ¬q ≡ a p [MOD p])
  let mass (p q : ℕ) := ∑ t ∈ (T p).filter (fun t => ∃ h ∈ H, (q : ℤ) = t + (h : ℤ)*p), μ p t
  let B := Q.filter (fun q => 1/U^2 < |(∑ p ∈ P, mass p q)-C|)
  let V := Q \ B
  have vsub : V ⊆ Q := sdiff_subset
  have bsub : B ⊆ Q := filter_subset _ _
  have partition : V.card + B.card = Q.card := card_sdiff_add_card_eq_card bsub
  have partR : (V.card : ℝ) + B.card = Q.card := by exact_mod_cast partition
  have short (q : ℕ) (hq : q ∈ V) : 4*q < x*x := by
    have hy : 0 ≤ y := by
      by_contra! h
      have upper := (mem_Ioc.mp (mem_filter.mp (vsub hq)).1).2
      change q ≤ ⌊y⌋₊ at upper
      rw [Nat.floor_of_nonpos h.le] at upper
      have lower := (mem_Ioc.mp (mem_filter.mp (vsub hq)).1).1
      omega
    have bound : (q:ℝ) ≤ y := (Nat.le_floor_iff hy).mp (mem_Ioc.mp (mem_filter.mp (vsub hq)).1).2
    have shortR : 4*(q:ℝ) < (x:ℝ)*x := (mul_le_mul_of_nonneg_left bound (by norm_num : (0:ℝ) ≤ 4)).trans_lt hg.1
    exact_mod_cast shortR
  have ids : Q \ V = B := Finset.sdiff_sdiff_eq_self bsub
  change (B.card : ℝ) ≤ X/log X at exc
  change 40*c*X*U/log X ≤ Q.card at ql
  have large := hg.2
  change U^3 + X/log X ≤ 40*c*X*U/log X at large
  obtain ⟨E,w,edge,prob,hit⟩ := push P V H T μ
    (fun p hp => (mem_filter.mp hp).2.pos) law
  refine ⟨V,E,w,C,vsub,short,by linarith,
    (Nat.cast_le.mpr (card_le_card vsub)).trans qu,?_,cmin,cmax,?_,prob,?_,?_⟩
  · rw [ids]
    have h : 0 ≤ X/log X := div_nonneg (Nat.cast_nonneg _) (by linarith)
    exact exc.trans (by calc
      X/log X ≤ K*(X/log X) := le_mul_of_one_le_left h (by linarith)
      _ = K*X/log X := by ring)
  · intro p hp e he
    obtain ⟨sub,card,label⟩ := edge p hp e he
    exact ⟨sub,(Nat.cast_le.mpr card).trans hs,label⟩
  · intro p hp q hq
    rw [hit p hp q hq]
    exact sparse p hp q (vsub hq)
  · intro q hq
    have outside := (mem_sdiff.mp hq).2
    have good : |(∑ p ∈ P, mass p q)-C| ≤ 1/U^2 := by
      by_contra! bad
      exact outside (mem_filter.mpr ⟨vsub hq,bad⟩)
    have eq : (∑ p ∈ P, ∑ e ∈ (E p).filter (q ∈ ·), w p e) = ∑ p ∈ P, mass p q :=
      Finset.sum_congr rfl (fun p hp => hit p hp q hq)
    change |(∑ p ∈ P, ∑ e ∈ (E p).filter (q ∈ ·), w p e)-C| ≤ 1/U^2
    rwa [eq]

end OMA.R_Green46_green_46_variants_lower_R1_H1_R1_H1_R1
