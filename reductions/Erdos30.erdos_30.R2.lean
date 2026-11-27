import FormalConjectures.ErdosProblems.«30»

-- Reduction Erdos30.erdos_30.R2 of Erdős Problem 30
-- Credit: @ubuwaits

/-!
# Adding comparable square-root lengths

Write F(n) for the largest number of Sidon marks in an interval of length n².
The hypotheses compare F(a+b) with F(a)+F(b) when a ≤ b ≤ 2a.
One asks for a construction and the other for an upper bound. Neither requires
a prime near a prescribed integer. Iterating the comparison on a balanced
binary tree gives a uniform estimate at every multiple of a base length.
Lindström's bound and Ruzsa's construction at arbitrarily large primes then
fix the coefficient of the linear term in F. The construction comparison
controls the excess F(n) − n, and the reverse comparison controls the
deficit n − F(n). The converse proves that both comparisons are necessary.

The finite proofs of Lindström's inequality and Ruzsa's construction below
are reused from this repository's accepted proofs of the Lindström variant
(GitHub contributor michielkosters) and the asymptotic-equivalence variant
(GitHub contributor ldy985), respectively. The two elementary extremal-value
lemmas are from the first reduction (GitHub contributor kenanwienberg).
-/

namespace OMA.R_Erdos30_erdos_30_R2

open Filter
open scoped Asymptotics

/-- Two optimal rulers at comparable square lengths can be matched by a
single ruler at the combined square length, with subpolynomial loss. -/
def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ a b : ℕ, K ≤ a → a ≤ b → b ≤ 2 * a →
    (Erdos30.h (a ^ 2) : ℝ) + Erdos30.h (b ^ 2) ≤
      Erdos30.h ((a + b) ^ 2) + (a : ℝ) ^ δ

/-- A ruler at the combined square length has at most the total capacity
of the two smaller square lengths plus a subpolynomial error. -/
def H2 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ a b : ℕ, K ≤ a → a ≤ b → b ≤ 2 * a →
    (Erdos30.h ((a + b) ^ 2) : ℝ) ≤
      Erdos30.h (a ^ 2) + (Erdos30.h (b ^ 2) : ℝ) + (a : ℝ) ^ δ

lemma card_le_h {N : ℕ} {A : Finset ℕ} (hS : IsSidon (A : Set ℕ))
    (hA : A ⊆ Finset.Icc 1 N) : A.card ≤ Erdos30.h N := by
  unfold Erdos30.h Finset.maxSidonSubsetCard
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA, hS⟩)

lemma h_mono {M N : ℕ} (hMN : M ≤ N) : Erdos30.h M ≤ Erdos30.h N := by
  unfold Erdos30.h Finset.maxSidonSubsetCard
  apply Finset.sup_mono
  intro B hB
  rw [Finset.mem_filter, Finset.mem_powerset] at hB ⊢
  exact ⟨hB.1.trans (Finset.Icc_subset_Icc_right hMN), hB.2⟩

/-- Ruzsa's construction: for a prime `q + 1`, the `q` integers `1 + i + q * k_i`, `i < q`, where
`k_i` is chosen so that the number is `≡ 1 + g ^ i (mod q + 1)` for a primitive root `g`, form a
Sidon set inside `{1, …, (q + 1) q}`. -/
theorem ruzsa_succ (q : ℕ) (hp : (q + 1).Prime) : ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 ((q + 1) * q) ∧ IsSidon (A : Set ℕ) ∧ A.card = q := by
  have : Fact (q + 1).Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ : ∃ g : (ZMod (q + 1))ˣ, orderOf g = q := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (q + 1))ˣ)
    refine ⟨g, ?_⟩
    rw [hg, Nat.card_eq_fintype_card, ZMod.card_units (q + 1)]
    simp
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ZMod (q + 1), ∀ i, u i = ((g ^ i : (ZMod (q + 1))ˣ) : ZMod (q + 1)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ → ℕ, ∀ i, k i = (i + (q + 1) - (u i).val) % (q + 1) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, ∀ i, f i = 1 + i + q * k i := ⟨_, fun _ => rfl⟩
  have hk_lt : ∀ i, k i < q + 1 := fun i => by
    rw [hk]
    exact Nat.mod_lt _ (Nat.succ_pos q)
  have hqcast : ((q : ℕ) : ZMod (q + 1)) = -1 := by
    have h0 : ((q + 1 : ℕ) : ZMod (q + 1)) = 0 := ZMod.natCast_self (q + 1)
    push_cast at h0
    linear_combination h0
  have hkcast : ∀ i, ((k i : ℕ) : ZMod (q + 1)) = (i : ZMod (q + 1)) - u i := by
    intro i
    have hval : (u i).val ≤ i + (q + 1) := (ZMod.val_lt (u i)).le.trans (Nat.le_add_left _ _)
    have h0 : ((q + 1 : ℕ) : ZMod (q + 1)) = 0 := ZMod.natCast_self (q + 1)
    rw [hk, ZMod.natCast_mod, Nat.cast_sub hval, Nat.cast_add, h0, ZMod.natCast_zmod_val]
    ring
  have hfcast : ∀ i, ((f i : ℕ) : ZMod (q + 1)) = 1 + u i := by
    intro i
    rw [hf]
    push_cast
    rw [hqcast, hkcast]
    ring
  have hu_inj : ∀ a b, a < q → b < q → u a = u b → a = b := by
    intro a b ha hb hab
    rw [hu, hu] at hab
    have h1 : g ^ a = g ^ b := Units.ext hab
    have h2 : a ≡ b [MOD orderOf g] := pow_eq_pow_iff_modEq.1 h1
    rw [hg] at h2
    exact Nat.ModEq.eq_of_lt_of_lt h2 ha hb
  have hf_mod : ∀ i, f i % q = (1 + i) % q := by
    intro i
    rw [hf]
    exact Nat.add_mul_mod_self_left _ _ _
  refine ⟨(Finset.range q).image f, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    have hi' := Finset.mem_range.1 hi
    have hki := hk_lt i
    rw [Finset.mem_Icc, hf]
    refine ⟨by omega, ?_⟩
    have h1 : q * k i ≤ q * q := Nat.mul_le_mul_left q (by omega)
    have h2 : (q + 1) * q = q * q + q := by ring
    omega
  · intro x hx y hy z hz w hw hsum
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hz)
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hw)
    have ha' := Finset.mem_range.1 ha
    have hb' := Finset.mem_range.1 hb
    have hc' := Finset.mem_range.1 hc
    have hd' := Finset.mem_range.1 hd
    -- the sum of the exponents is determined modulo q
    have hmod : a + c ≡ b + d [MOD q] := by
      have e : a + c + q * (k a + k c + 0) + 2 = b + d + q * (k b + k d + 0) + 2 := by
        have := hsum
        rw [hf a, hf b, hf c, hf d] at this
        simp only [Nat.mul_add, Nat.add_zero]
        omega
      have e' : a + c + q * (k a + k c + 0) = b + d + q * (k b + k d + 0) := by omega
      have e2 := congrArg (· % q) e'
      simp only [Nat.add_mul_mod_self_left] at e2
      exact e2
    have hgpow : g ^ (a + c) = g ^ (b + d) := pow_eq_pow_iff_modEq.2 (by rw [hg]; exact hmod)
    have hprod : u a * u c = u b * u d := by
      rw [hu, hu, hu, hu, ← Units.val_mul, ← Units.val_mul, ← pow_add, ← pow_add, hgpow]
    have hadd : u a + u c = u b + u d := by
      have e := congrArg (Nat.cast : ℕ → ZMod (q + 1)) hsum
      rw [Nat.cast_add, Nat.cast_add, hfcast, hfcast, hfcast, hfcast] at e
      linear_combination e
    have hzero : (u a - u b) * (u a - u d) = 0 := by
      linear_combination (u a) * hadd - hprod
    rcases mul_eq_zero.1 hzero with h | h
    · have hab : a = b := hu_inj a b ha' hb' (sub_eq_zero.1 h)
      have hcd : c = d := by
        apply hu_inj c d hc' hd'
        rw [hab] at hadd
        exact add_left_cancel hadd
      exact Or.inl ⟨by rw [hab], by rw [hcd]⟩
    · have had : a = d := hu_inj a d ha' hd' (sub_eq_zero.1 h)
      have hcb : c = b := by
        apply hu_inj c b hc' hb'
        rw [had] at hadd
        have : u d + u c = u d + u b := by rw [hadd]; ring
        exact add_left_cancel this
      exact Or.inr ⟨by rw [had], by rw [hcb]⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have hi' : i < q := Finset.mem_range.1 (Finset.mem_coe.1 hi)
    have hj' : j < q := Finset.mem_range.1 (Finset.mem_coe.1 hj)
    have h1 : (1 + i) % q = (1 + j) % q := by rw [← hf_mod, ← hf_mod, hij]
    have h2 : (1 + i) ≡ (1 + j) [MOD q] := h1
    have h3 : i ≡ j [MOD q] := Nat.ModEq.add_left_cancel' 1 h2
    exact Nat.ModEq.eq_of_lt_of_lt h3 hi' hj'

theorem ruzsa (p : ℕ) (hp : p.Prime) : ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 (p * (p - 1)) ∧ IsSidon (A : Set ℕ) ∧ A.card = p - 1 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  simpa using ruzsa_succ q hp

lemma oma_sum_ge_of_pos (D : Finset ℕ) (hD : ∀ x ∈ D, 1 ≤ x) :
    D.card * (D.card + 1) ≤ 2 * ∑ x ∈ D, x := by
  let e := D.orderIsoOfFin rfl
  have hge : ∀ i : ℕ, (hi : i < D.card) → i + 1 ≤ (e ⟨i, hi⟩ : ℕ) := by
    intro i
    induction i with
    | zero =>
      intro hi
      exact hD _ (e ⟨0, hi⟩).2
    | succ i ih =>
      intro hi
      have hi' : i < D.card := by omega
      have hprev := ih hi'
      have hlt : (e ⟨i, hi'⟩ : ℕ) < (e ⟨i + 1, hi⟩ : ℕ) :=
        e.strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))
      omega
  have hsum_eq : ∑ x ∈ D, x = ∑ i : Fin D.card, (e i : ℕ) := by
    rw [← Finset.sum_coe_sort D (fun x => x)]
    exact (Fintype.sum_equiv e.toEquiv (fun i => (e i : ℕ)) (fun x : ↥D => (x : ℕ)) (fun _ => rfl)).symm
  rw [hsum_eq]
  have hle : ∑ i : Fin D.card, (i.val + 1) ≤ ∑ i : Fin D.card, (e i : ℕ) :=
    Finset.sum_le_sum fun i _ => hge i.val i.isLt
  have hid : 2 * ∑ i : Fin D.card, (i.val + 1) = D.card * (D.card + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i + 1)]
    have : 2 * ∑ i ∈ Finset.range D.card, (i + 1) = D.card * (D.card + 1) := by
      induction D.card with
      | zero => simp
      | succ m ihm =>
        rw [Finset.sum_range_succ, mul_add, ihm]
        ring
    exact this
  omega

lemma oma_sidon_lindstrom (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (hS : IsSidon (A : Set ℕ)) :
    (A.card : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 := by
  by_cases hN0 : N = 0
  · subst hN0
    have hAe : A = ∅ := Finset.subset_empty.mp (by simpa using hA)
    simp [hAe]
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  have hNreal : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hNpos
  set k := A.card
  set u : ℝ := (N : ℝ) ^ (4⁻¹ : ℝ)
  set r : ℕ := Nat.floor u + 1
  have hu_nonneg : 0 ≤ u := by positivity
  have hr_gt : u < (r : ℝ) := by
    have := Nat.lt_floor_add_one u
    push_cast [r]
    exact this
  have hr_le : (r : ℝ) ≤ u + 1 := by
    have := Nat.floor_le hu_nonneg
    push_cast [r]
    linarith
  have hr_pos : 1 ≤ r := by omega
  by_cases hkr : k ≤ r
  · have h1 : (k : ℝ) ≤ (r : ℝ) := Nat.cast_le.mpr hkr
    have h2 : (0 : ℝ) ≤ (N : ℝ).sqrt := Real.sqrt_nonneg _
    linarith
  have hrk : r < k := by omega
  let e := A.orderIsoOfFin rfl
  let a : Fin k → ℕ := fun i => (e i : ℕ)
  have ha_mono : StrictMono a := fun i j hij => e.strictMono hij
  have ha_mem : ∀ i : Fin k, a i ∈ A := fun i => (e i).2
  have ha_le : ∀ i : Fin k, a i ≤ N := fun i => (Finset.mem_Icc.mp (hA (ha_mem i))).2
  let P : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 r).biUnion fun d => (Finset.range (k - d)).image fun j => (d, j)
  have hP_mem : ∀ p ∈ P, 1 ≤ p.1 ∧ p.1 ≤ r ∧ p.2 + p.1 < k := by
    intro ⟨d, j⟩ hp
    simp only [P, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image, Finset.mem_range] at hp
    rcases hp with ⟨d', ⟨hd1, hd2⟩, j', hj', heq⟩
    rcases Prod.ext_iff.mp heq with ⟨rfl, rfl⟩
    exact ⟨hd1, hd2, by omega⟩
  let diffFn : ℕ × ℕ → ℕ := fun p =>
    if h : p.2 + p.1 < k then a ⟨p.2 + p.1, h⟩ - a ⟨p.2, by omega⟩ else 0
  have hdiff_inj : Set.InjOn diffFn (P : Set (ℕ × ℕ)) := by
    intro ⟨d₁, j₁⟩ h1 ⟨d₂, j₂⟩ h2 heq
    have hm1 := hP_mem (d₁, j₁) (Finset.mem_coe.mp h1)
    have hm2 := hP_mem (d₂, j₂) (Finset.mem_coe.mp h2)
    have hlt1 : a ⟨j₁, by omega⟩ < a ⟨j₁ + d₁, hm1.2.2⟩ :=
      ha_mono (Fin.mk_lt_mk.mpr (by omega))
    have hlt2 : a ⟨j₂, by omega⟩ < a ⟨j₂ + d₂, hm2.2.2⟩ :=
      ha_mono (Fin.mk_lt_mk.mpr (by omega))
    simp only [diffFn, dif_pos hm1.2.2, dif_pos hm2.2.2] at heq
    have hpair := Finset.IsSidon.eq_of_tsub hS
      (ha_mem ⟨j₁ + d₁, hm1.2.2⟩) (ha_mem ⟨j₁, by omega⟩)
      (ha_mem ⟨j₂ + d₂, hm2.2.2⟩) (ha_mem ⟨j₂, by omega⟩)
      hlt1 hlt2 heq
    have hj_eq : j₁ = j₂ := by
      have := ha_mono.injective hpair.2
      exact congrArg Fin.val this
    have hjd_eq : j₁ + d₁ = j₂ + d₂ := by
      have := ha_mono.injective hpair.1
      exact congrArg Fin.val this
    ext <;> omega
  let D : Finset ℕ := P.image diffFn
  have hD_card : D.card = P.card := Finset.card_image_of_injOn hdiff_inj
  have hD_pos : ∀ x ∈ D, 1 ≤ x := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨⟨d, j⟩, hp, rfl⟩
    have hm := hP_mem (d, j) hp
    have hlt : a ⟨j, by omega⟩ < a ⟨j + d, hm.2.2⟩ :=
      ha_mono (Fin.mk_lt_mk.mpr (by omega))
    simp only [diffFn, dif_pos hm.2.2]
    omega
  have hP_card : P.card = r * k - r * (r + 1) / 2 := by
    have hdisj : (Finset.Icc 1 r : Set ℕ).PairwiseDisjoint fun d =>
        (Finset.range (k - d)).image fun j => (d, j) := by
      intro d₁ _ d₂ _ hne
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro ⟨a₁, b₁⟩ h1 h2
      simp only [Finset.mem_image] at h1 h2
      rcases h1 with ⟨_, _, e1⟩
      rcases h2 with ⟨_, _, e2⟩
      have := congrArg Prod.fst (e1.trans e2.symm)
      exact hne this
    dsimp [P]
    rw [Finset.card_biUnion hdisj]
    have hterm : ∀ d ∈ Finset.Icc 1 r,
        ((Finset.range (k - d)).image fun j => (d, j)).card = k - d := by
      intro d _
      rw [Finset.card_image_of_injective]
      · exact Finset.card_range _
      · intro j₁ j₂ h; exact congrArg Prod.snd h
    rw [Finset.sum_congr rfl hterm]
    have hsum_d : ∑ d ∈ Finset.Icc 1 r, (k - d) = r * k - ∑ d ∈ Finset.Icc 1 r, d := by
      have h1 : ∑ d ∈ Finset.Icc 1 r, (k - d) + ∑ d ∈ Finset.Icc 1 r, d =
          ∑ d ∈ Finset.Icc 1 r, k := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun d hd => ?_
        have hdle : d ≤ k := by
          have := (Finset.mem_Icc.mp hd).2
          omega
        exact Nat.sub_add_cancel hdle
      have h2 : ∑ _d ∈ Finset.Icc 1 r, k = r * k := by
        simp [Nat.card_Icc]
      omega
    have htri : 2 * ∑ d ∈ Finset.Icc 1 r, d = r * (r + 1) := by
      induction r with
      | zero => simp
      | succ m ihm =>
        rw [Finset.sum_Icc_succ_top (by omega), mul_add, ihm]
        ring
    rw [hsum_d, show ∑ d ∈ Finset.Icc 1 r, d = r * (r + 1) / 2 by omega]
  have h_lower := oma_sum_ge_of_pos D hD_pos
  rw [hD_card] at h_lower
  have hsum_D_eq : ∑ x ∈ D, x = ∑ p ∈ P, diffFn p := Finset.sum_image (fun x hx y hy h => hdiff_inj hx hy h)
  have h_upper_nat : ∑ p ∈ P, diffFn p ≤ (r * (r + 1) / 2) * N := by
    have hdisj : (Finset.Icc 1 r : Set ℕ).PairwiseDisjoint fun d =>
        (Finset.range (k - d)).image fun j => (d, j) := by
      intro d₁ _ d₂ _ hne
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro ⟨a₁, b₁⟩ h1 h2
      simp only [Finset.mem_image] at h1 h2
      rcases h1 with ⟨_, _, e1⟩
      rcases h2 with ⟨_, _, e2⟩
      exact hne (congrArg Prod.fst (e1.trans e2.symm))
    dsimp [P]
    rw [Finset.sum_biUnion hdisj]
    have h_each : ∀ d ∈ Finset.Icc 1 r,
        ∑ p ∈ (Finset.range (k - d)).image (fun j => (d, j)), diffFn p ≤ d * N := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdr : d ≤ r := (Finset.mem_Icc.mp hd).2
      have hdk : d < k := by omega
      rw [Finset.sum_image (fun j₁ _ j₂ _ h => congrArg Prod.snd h)]
      let a' : ℕ → ℝ := fun i => if h : i < k then (a ⟨i, h⟩ : ℝ) else 0
      have hcast_sum : ((∑ j ∈ Finset.range (k - d), diffFn (d, j) : ℕ) : ℝ) =
          ∑ j ∈ Finset.range (k - d), (a' (j + d) - a' j) := by
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        have hjd : j + d < k := by omega
        have hj' : j < k := by omega
        have hle : a ⟨j, hj'⟩ ≤ a ⟨j + d, hjd⟩ :=
          (ha_mono.monotone (Fin.mk_le_mk.mpr (by omega)))
        simp only [diffFn, a', dif_pos hjd, dif_pos hj']
        exact Nat.cast_sub hle
      have htele : ∑ j ∈ Finset.range (k - d), (a' (j + d) - a' j) ≤ (d : ℝ) * (N : ℝ) := by
        rw [Finset.sum_sub_distrib]
        have hshift : ∑ j ∈ Finset.range (k - d), a' (j + d) = ∑ i ∈ Finset.Ico d k, a' i := by
          refine Finset.sum_bij (fun j _ => j + d) ?_ ?_ ?_ ?_
          · intro j hj; rw [Finset.mem_range] at hj; rw [Finset.mem_Ico]; omega
          · intro j₁ _ j₂ _ h; omega
          · intro i hi; rw [Finset.mem_Ico] at hi; exact ⟨i - d, Finset.mem_range.mpr (by omega), by omega⟩
          · intro _ _; rfl
        rw [hshift]
        have hsplit1 : ∑ i ∈ Finset.Ico d k, a' i =
            ∑ i ∈ (Finset.Ico d k) ∩ (Finset.range (k - d)), a' i +
            ∑ i ∈ (Finset.Ico d k) \ (Finset.range (k - d)), a' i :=
          (Finset.sum_inter_add_sum_sdiff _ _ _).symm
        have hsplit2 : ∑ i ∈ Finset.range (k - d), a' i =
            ∑ i ∈ (Finset.range (k - d)) ∩ (Finset.Ico d k), a' i +
            ∑ i ∈ (Finset.range (k - d)) \ (Finset.Ico d k), a' i :=
          (Finset.sum_inter_add_sum_sdiff _ _ _).symm
        rw [hsplit1, hsplit2, Finset.inter_comm (Finset.range (k - d)) (Finset.Ico d k)]
        have hnonneg : 0 ≤ ∑ i ∈ (Finset.range (k - d)) \ (Finset.Ico d k), a' i := by
          refine Finset.sum_nonneg fun i _ => ?_
          dsimp [a']; split_ifs <;> positivity
        have hsub_ico : (Finset.Ico d k) \ (Finset.range (k - d)) ⊆ Finset.Ico (k - d) k := by
          intro x hx
          simp only [Finset.mem_sdiff, Finset.mem_Ico, Finset.mem_range] at hx ⊢
          omega
        have hcard_le : ((Finset.Ico d k) \ (Finset.range (k - d))).card ≤ d := by
          have := Finset.card_le_card hsub_ico
          rw [Nat.card_Ico] at this
          omega
        have hbound : ∑ i ∈ (Finset.Ico d k) \ (Finset.range (k - d)), a' i ≤
            ((Finset.Ico d k) \ (Finset.range (k - d))).card * (N : ℝ) := by
          calc ∑ i ∈ (Finset.Ico d k) \ (Finset.range (k - d)), a' i
            _ ≤ ∑ _i ∈ (Finset.Ico d k) \ (Finset.range (k - d)), (N : ℝ) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hik : i < k := (Finset.mem_Ico.mp (Finset.mem_sdiff.mp hi).1).2
              simp only [a', dif_pos hik]
              exact_mod_cast ha_le ⟨i, hik⟩
            _ = _ := by simp
        have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        have hcard_r : (((Finset.Ico d k) \ (Finset.range (k - d))).card : ℝ) ≤ (d : ℝ) :=
          Nat.cast_le.mpr hcard_le
        nlinarith
      exact_mod_cast hcast_sum.symm ▸ htele
    calc ∑ d ∈ Finset.Icc 1 r, ∑ p ∈ (Finset.range (k - d)).image (fun j => (d, j)), diffFn p
      _ ≤ ∑ d ∈ Finset.Icc 1 r, d * N := Finset.sum_le_sum h_each
      _ = (∑ d ∈ Finset.Icc 1 r, d) * N := (Finset.sum_mul _ _ _).symm
      _ = (r * (r + 1) / 2) * N := by
        congr 1
        have htri : 2 * ∑ d ∈ Finset.Icc 1 r, d = r * (r + 1) := by
          induction r with
          | zero => simp
          | succ m ihm =>
            rw [Finset.sum_Icc_succ_top (by omega), mul_add, ihm]
            ring
        omega
  have hineq_nat : P.card * (P.card + 1) ≤ r * (r + 1) * N := by
    have h1 : P.card * (P.card + 1) ≤ 2 * (r * (r + 1) / 2 * N) := by linarith
    have heven : 2 ∣ r * (r + 1) := Nat.even_mul_succ_self r |>.two_dvd
    have h2 : 2 * (r * (r + 1) / 2 * N) = r * (r + 1) * N := by
      rw [← mul_assoc, Nat.mul_div_cancel' heven]
    linarith
  have hP_real : (P.card : ℝ) = (r : ℝ) * (k : ℝ) - (r : ℝ) * ((r : ℝ) + 1) / 2 := by
    have heven : 2 ∣ r * (r + 1) := Nat.even_mul_succ_self r |>.two_dvd
    have hle : r * (r + 1) / 2 ≤ r * k := by
      have : r * (r + 1) ≤ 2 * (r * k) := by
        nlinarith [show r + 1 ≤ k by omega]
      exact Nat.div_le_of_le_mul this
    rw [hP_card, Nat.cast_sub hle, Nat.cast_div heven (by norm_num)]
    push_cast
    ring
  have hineq_real : (P.card : ℝ) ^ 2 ≤ (r : ℝ) * ((r : ℝ) + 1) * (N : ℝ) := by
    have h1 : (P.card : ℝ) * ((P.card : ℝ) + 1) ≤ (r : ℝ) * ((r : ℝ) + 1) * (N : ℝ) := by
      exact_mod_cast hineq_nat
    have hPnn : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
    nlinarith
  by_contra! hgt
  have hu2 : u ^ 2 = (N : ℝ).sqrt := by
    dsimp [u]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hNreal.le]
    norm_num
  have hu4 : u ^ 4 = (N : ℝ) := by
    calc u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ = ((N : ℝ).sqrt) ^ 2 := by rw [hu2]
      _ = (N : ℝ) := Real.sq_sqrt hNreal.le
  have hr_pos_r : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
  have hP_gt : (r : ℝ) * ((N : ℝ).sqrt + u / 2) < (P.card : ℝ) := by
    rw [hP_real]
    nlinarith
  have hsqrt_nn : 0 ≤ (N : ℝ).sqrt := Real.sqrt_nonneg _
  have hP_sq_gt : (r : ℝ) ^ 2 * ((N : ℝ) + u * (N : ℝ).sqrt + u ^ 2 / 4) < (P.card : ℝ) ^ 2 := by
    have hpos_lhs : 0 ≤ (r : ℝ) * ((N : ℝ).sqrt + u / 2) := by positivity
    have h1 : ((r : ℝ) * ((N : ℝ).sqrt + u / 2)) ^ 2 < (P.card : ℝ) ^ 2 := by
      nlinarith
    have h2 : ((r : ℝ) * ((N : ℝ).sqrt + u / 2)) ^ 2 =
        (r : ℝ) ^ 2 * ((N : ℝ) + u * (N : ℝ).sqrt + u ^ 2 / 4) := by
      have : ((N : ℝ).sqrt) ^ 2 = (N : ℝ) := Real.sq_sqrt hNreal.le
      calc ((r : ℝ) * ((N : ℝ).sqrt + u / 2)) ^ 2
        _ = (r : ℝ) ^ 2 * (((N : ℝ).sqrt) ^ 2 + u * (N : ℝ).sqrt + u ^ 2 / 4) := by ring
        _ = (r : ℝ) ^ 2 * ((N : ℝ) + u * (N : ℝ).sqrt + u ^ 2 / 4) := by rw [this]
    linarith
  have h_gap : (r : ℝ) * ((r : ℝ) + 1) * (N : ℝ) <
      (r : ℝ) ^ 2 * ((N : ℝ) + u * (N : ℝ).sqrt + u ^ 2 / 4) := by
    have hu_pos : 0 < u := Real.rpow_pos_of_pos hNreal _
    have hsqrt_pos : 0 < (N : ℝ).sqrt := Real.sqrt_pos.mpr hNreal
    have hru : (N : ℝ) < (r : ℝ) * u * (N : ℝ).sqrt := by
      have hNeq : (N : ℝ) = u * u * (N : ℝ).sqrt := by
        calc (N : ℝ) = ((N : ℝ).sqrt) ^ 2 := (Real.sq_sqrt hNreal.le).symm
          _ = (N : ℝ).sqrt * (N : ℝ).sqrt := sq _
          _ = u ^ 2 * (N : ℝ).sqrt := by rw [hu2]
          _ = u * u * (N : ℝ).sqrt := by ring
      nlinarith
    have : 0 ≤ (r : ℝ) ^ 2 * (u ^ 2 / 4) := by positivity
    nlinarith
  linarith

theorem lindstrom_bound : ∀ N : ℕ, (Erdos30.h N : ℝ) ≤ Real.sqrt N + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 := by
  intro N
  dsimp [Erdos30.h, Finset.maxSidonSubsetCard]
  have hsup : ((Finset.Icc 1 N).powerset.filter fun B : Finset ℕ => IsSidon (B : Set ℕ)).sup
      Finset.card ≤ Nat.floor ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
    refine Finset.sup_le fun B hB => ?_
    rw [Finset.mem_filter, Finset.mem_powerset] at hB
    have hle := oma_sidon_lindstrom N B hB.1 hB.2
    exact Nat.le_floor hle
  have hle_real : ((Finset.maxSidonSubsetCard (Finset.Icc 1 N) : ℕ) : ℝ) ≤
      (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 := by
    have h1 := Nat.cast_le (α := ℝ).mpr hsup
    have h2 : (Nat.floor ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) : ℝ) ≤
        (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 :=
      Nat.floor_le (by positivity)
    exact h1.trans h2
  exact_mod_cast hle_real

/-- Splitting an integer multiplier into nearly equal halves pays a total error
proportional to the multiplier, uniformly in the depth of the splitting tree. -/
lemma multiple_upper (F : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hhalf : δ ≤ 1 / 2)
    {K n : ℕ} (hn : K ≤ n)
    (step : ∀ a b : ℕ, K ≤ a → a ≤ b → b ≤ 2 * a →
      F (a + b) - F a - F b ≤ (a : ℝ) ^ δ) (k : ℕ) (hk : 1 ≤ k) :
    F (k * n) - (k : ℝ) * F n ≤ 4 * ((k : ℝ) - (k : ℝ) ^ δ) * (n : ℝ) ^ δ := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hone : k = 1
    · simp [hone]
    let a := k / 2
    let b := k - a
    have ha : 1 ≤ a := by dsimp [a]; omega
    have hab : a ≤ b := by dsimp [a,b]; omega
    have hb : b ≤ 2 * a := by dsimp [a,b]; omega
    have hsum : a + b = k := by dsimp [a,b]; omega
    have hak : a < k := by omega
    have hbk : b < k := by omega
    have A := ih a hak ha
    have B := ih b hbk (ha.trans hab)
    have hscaled := step (a * n) (b * n)
      (hn.trans (by simpa using Nat.mul_le_mul_right n ha))
      (Nat.mul_le_mul_right n hab)
      (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_right n hb)
    rw [← Nat.add_mul, hsum, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg n)] at hscaled
    have hreal : (a : ℝ) + b = k := by exact_mod_cast hsum
    have hkle : (k : ℝ) ≤ 3 * a := by
      have hh : (b : ℝ) ≤ 2 * a := by exact_mod_cast hb
      linarith
    have hthree : (3 : ℝ) ^ δ ≤ 7 / 4 := by
      calc (3 : ℝ) ^ δ ≤ 3 ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hhalf
        _ = Real.sqrt 3 := (Real.sqrt_eq_rpow 3).symm
        _ ≤ 7 / 4 := by rw [Real.sqrt_le_iff]; norm_num
    have hpow : (k : ℝ) ^ δ ≤ (7 / 4) * (a : ℝ) ^ δ := by
      calc (k : ℝ) ^ δ ≤ (3 * (a : ℝ)) ^ δ :=
            Real.rpow_le_rpow (Nat.cast_nonneg k) hkle hδ
        _ = (3 : ℝ) ^ δ * (a : ℝ) ^ δ := Real.mul_rpow (by norm_num) (Nat.cast_nonneg a)
        _ ≤ _ := mul_le_mul_of_nonneg_right hthree (by positivity)
    have hmono : (a : ℝ) ^ δ ≤ (b : ℝ) ^ δ :=
      Real.rpow_le_rpow (Nat.cast_nonneg a) (by exact_mod_cast hab) hδ
    have hcoeff : (a : ℝ) ^ δ + 4 * ((a : ℝ) - (a : ℝ) ^ δ) +
        4 * ((b : ℝ) - (b : ℝ) ^ δ) ≤ 4 * ((k : ℝ) - (k : ℝ) ^ δ) := by linarith
    have heq : F (k * n) - (k : ℝ) * F n =
        (F (k * n) - F (a * n) - F (b * n)) +
        (F (a * n) - (a : ℝ) * F n) + (F (b * n) - (b : ℝ) * F n) := by
      rw [← hreal]
      ring
    rw [heq]
    exact (add_le_add (add_le_add hscaled A) B).trans (by
      simpa only [add_mul] using mul_le_mul_of_nonneg_right hcoeff
        (Real.rpow_nonneg (Nat.cast_nonneg n) δ))

lemma square_upper (m : ℕ) : (Erdos30.h (m ^ 2) : ℝ) ≤ m + Real.sqrt m + 1 := by
  have h := lindstrom_bound (m ^ 2)
  push_cast at h
  rw [Real.sqrt_sq (Nat.cast_nonneg m)] at h
  have heq : ((m : ℝ) ^ 2) ^ (4⁻¹ : ℝ) = Real.sqrt m := by
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg m), Real.sqrt_eq_rpow]
    norm_num
  rwa [heq] at h

lemma prime_lower (p : ℕ) (hp : p.Prime) : p ≤ (Erdos30.h (p ^ 2) : ℝ) + 1 := by
  obtain ⟨A, hA, hS, hcard⟩ := ruzsa p hp
  have hsub : p * (p - 1) ≤ p ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_left p (Nat.sub_le p 1)
  have h := (card_le_h hS hA).trans (h_mono hsub)
  rw [hcard] at h
  have hp1 := hp.one_le
  exact_mod_cast (show p ≤ Erdos30.h (p ^ 2) + 1 by omega)

/-- An estimate at every multiple identifies the slope using only unbounded
primes. The prime in the lower-bound argument may be arbitrarily far away. -/
lemma lower_from_multiples {n : ℕ} (hn : 1 ≤ n) {E : ℝ}
    (hrep : ∀ k : ℕ, 1 ≤ k →
      (Erdos30.h ((k * n) ^ 2) : ℝ) - k * (Erdos30.h (n ^ 2) : ℝ) ≤ k * E) :
    (n : ℝ) - Erdos30.h (n ^ 2) ≤ E := by
  by_contra! hbad
  let g : ℝ := (n : ℝ) - (Erdos30.h (n ^ 2) : ℝ) - E
  have hg : 0 < g := by dsimp [g]; linarith
  obtain ⟨T, hT⟩ := exists_nat_gt (((n : ℝ) + 1) / g)
  obtain ⟨p, hpT, hp⟩ := Nat.exists_infinite_primes (T * n)
  let k := p / n + 1
  have hk : 1 ≤ k := Nat.le_add_left 1 (p / n)
  have hTk : T ≤ k := by
    have := (Nat.le_div_iff_mul_le (by omega : 0 < n)).2 hpT
    dsimp [k]
    omega
  have hklarge : (n : ℝ) + 1 < (k : ℝ) * g :=
    (div_lt_iff₀ hg).mp (hT.trans_le (by exact_mod_cast hTk))
  have hprod : k * n = p / n * n + n := by dsimp [k]; ring
  have hpk : p ≤ k * n := by
    have hmod := Nat.mod_lt p (by omega : 0 < n)
    have hdiv := Nat.mod_add_div p n
    rw [Nat.mul_comm n (p / n)] at hdiv
    omega
  have hkp : k * n ≤ p + n := by rw [hprod]; exact Nat.add_le_add_right (Nat.div_mul_le_self p n) n
  have hkpR : (k : ℝ) * n ≤ (p : ℝ) + n := by exact_mod_cast hkp
  have hmono := h_mono (Nat.pow_le_pow_left hpk 2)
  have hmonoR : (Erdos30.h (p ^ 2) : ℝ) ≤ Erdos30.h ((k * n) ^ 2) := by exact_mod_cast hmono
  have hlow := prime_lower p hp
  have hrep' := hrep k hk
  dsimp [g] at hklarge
  linarith

/-- Gluing bounds the positive deviation because an excess at the base length
would propagate to a contradiction with Lindström's estimate. -/
lemma upper_from_multiples {n : ℕ} {E : ℝ}
    (hrep : ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) * Erdos30.h (n ^ 2) - Erdos30.h ((k * n) ^ 2) ≤ k * E) :
    (Erdos30.h (n ^ 2) : ℝ) - n ≤ E := by
  by_contra! hbad
  let g : ℝ := (Erdos30.h (n ^ 2) : ℝ) - n - E
  have hg : 0 < g := by dsimp [g]; linarith
  obtain ⟨t, ht⟩ := exists_nat_gt (max (((n : ℝ) + 2) / g) 1)
  have ht1 : (1 : ℝ) < t := (le_max_right _ _).trans_lt ht
  have htpos : 0 < t := by exact_mod_cast (by linarith : (0 : ℝ) < t)
  have htlarge : (n : ℝ) + 2 < (t : ℝ) * g :=
    (div_lt_iff₀ hg).mp ((le_max_left _ _).trans_lt ht)
  have hstrict := mul_lt_mul_of_pos_left htlarge (by positivity : 0 < (t : ℝ))
  have hlow := hrep (t ^ 2) (Nat.succ_le_of_lt (pow_pos htpos _))
  have hup := square_upper (t ^ 2 * n)
  push_cast at hlow hup
  rw [Real.sqrt_mul (sq_nonneg (t : ℝ)), Real.sqrt_sq (Nat.cast_nonneg t)] at hup
  have hsqrt : Real.sqrt n ≤ (n : ℝ) + 1 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]
  have hsm := mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg t)
  dsimp [g] at hstrict
  linarith

lemma linear_multiple_bound (F : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hhalf : δ ≤ 1 / 2)
    {K n : ℕ} (hn : K ≤ n)
    (step : ∀ a b : ℕ, K ≤ a → a ≤ b → b ≤ 2 * a →
      F (a + b) - F a - F b ≤ (a : ℝ) ^ δ) (k : ℕ) (hk : 1 ≤ k) :
    F (k * n) - (k : ℝ) * F n ≤ k * (4 * (n : ℝ) ^ δ) := by
  refine (multiple_upper F hδ hhalf hn step k hk).trans ?_
  have hkδ : 0 ≤ (k : ℝ) ^ δ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hc : 4 * ((k : ℝ) - (k : ℝ) ^ δ) ≤ (k : ℝ) * 4 := by linarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc
    (Real.rpow_nonneg (Nat.cast_nonneg n) δ)

/-- The construction hypothesis alone yields the upper bound at squares. -/
lemma square_upper_of_gluing (h1 : H1) {δ : ℝ} (hδ : 0 < δ) (hhalf : δ ≤ 1 / 2) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
      (Erdos30.h (n ^ 2) : ℝ) - n ≤ 4 * (n : ℝ) ^ δ := by
  obtain ⟨K, hK⟩ := h1 δ hδ
  let F : ℕ → ℝ := fun n ↦ -(Erdos30.h (n ^ 2) : ℝ)
  have step : ∀ a b : ℕ, K ≤ a → a ≤ b → b ≤ 2 * a →
      F (a + b) - F a - F b ≤ (a : ℝ) ^ δ := by
    intro a b ha hab hba
    dsimp [F]
    linarith [hK a b ha hab hba]
  refine ⟨K, fun n hn ↦ upper_from_multiples ?_⟩
  intro k hk
  have h := linear_multiple_bound F hδ.le hhalf hn step k hk
  dsimp [F] at h
  linarith

/-- The splitting hypothesis alone yields the lower bound at squares. -/
lemma square_lower_of_splitting (h2 : H2) {δ : ℝ} (hδ : 0 < δ) (hhalf : δ ≤ 1 / 2) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
      (n : ℝ) - Erdos30.h (n ^ 2) ≤ 4 * (n : ℝ) ^ δ := by
  obtain ⟨K, hK⟩ := h2 δ hδ
  let F : ℕ → ℝ := fun n ↦ (Erdos30.h (n ^ 2) : ℝ)
  have step : ∀ a b : ℕ, K ≤ a → a ≤ b → b ≤ 2 * a →
      F (a + b) - F a - F b ≤ (a : ℝ) ^ δ := by
    intro a b ha hab hba
    dsimp [F]
    linarith [hK a b ha hab hba]
  refine ⟨max 1 K, fun n hn ↦ lower_from_multiples ((le_max_left _ _).trans hn) ?_⟩
  intro k hk
  exact linear_multiple_bound F hδ.le hhalf ((le_max_right _ _).trans hn) step k hk

lemma square_error (h1 : H1) (h2 : H2) {δ : ℝ} (hδ : 0 < δ) (hhalf : δ ≤ 1 / 2) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
      |(Erdos30.h (n ^ 2) : ℝ) - n| ≤ 4 * (n : ℝ) ^ δ := by
  obtain ⟨U, hU⟩ := square_upper_of_gluing h1 hδ hhalf
  obtain ⟨L, hL⟩ := square_lower_of_splitting h2 hδ hhalf
  refine ⟨max U L, fun n hn ↦ abs_le.mpr ⟨?_, hU n ((le_max_left _ _).trans hn)⟩⟩
  linarith [hL n ((le_max_right _ _).trans hn)]

/-- Conversely, the claimed asymptotic estimate gives both finite comparisons.
Thus their common error scale introduces no stronger conjecture. -/
theorem comparisons_of_target (h : type_of% @Erdos30.erdos_30) : H1 ∧ H2 := by
  have both : ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ a b : ℕ, K ≤ a → a ≤ b → b ≤ 2 * a →
      |(Erdos30.h ((a + b) ^ 2) : ℝ) - Erdos30.h (a ^ 2) - Erdos30.h (b ^ 2)| ≤
        (a : ℝ) ^ δ := by
    intro δ hδ
    obtain ⟨C, hC, hc⟩ := Asymptotics.isBigO_iff'.mp (h (δ / 4) (by positivity))
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hc
    have hlim : Tendsto (fun a : ℕ ↦ (a : ℝ) ^ (δ / 2)) atTop atTop :=
      (tendsto_rpow_atTop (by positivity : 0 < δ / 2)).comp tendsto_natCast_atTop_atTop
    obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp
      (hlim.eventually_ge_atTop (3 * C * (3 : ℝ) ^ (δ / 2)))
    refine ⟨max M L, fun a b hKa hab hba ↦ ?_⟩
    have hs : ∀ u : ℕ, a ≤ u → u ≤ 3 * a →
        |(Erdos30.h (u ^ 2) : ℝ) - u| ≤ C * (3 : ℝ) ^ (δ / 2) * (a : ℝ) ^ (δ / 2) := by
      intro u hau hua
      have huM : M ≤ u ^ 2 := (le_max_left M L).trans
        (hKa.trans (hau.trans (by simpa [sq] using Nat.le_mul_self u)))
      have hsq := hM (u ^ 2) huM
      simp only [Real.norm_eq_abs, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg u),
        abs_of_nonneg (Real.rpow_nonneg (sq_nonneg (u : ℝ)) _)] at hsq
      rw [← Real.rpow_natCast_mul (Nat.cast_nonneg u)] at hsq
      have he : (2 : ℝ) * (δ / 4) = δ / 2 := by ring
      norm_num only [Nat.cast_ofNat] at hsq
      rw [he] at hsq
      have hpow : (u : ℝ) ^ (δ / 2) ≤ (3 * (a : ℝ)) ^ (δ / 2) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hua) (by positivity)
      rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg a)] at hpow
      exact hsq.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpow hC.le)
    have hA := abs_le.mp (hs a le_rfl (by omega))
    have hB := abs_le.mp (hs b hab (by omega))
    have hS := abs_le.mp (hs (a + b) (by omega) (by omega))
    push_cast at hS
    have hcoeff := hL a ((le_max_right M L).trans hKa)
    change 3 * C * (3 : ℝ) ^ (δ / 2) ≤ (a : ℝ) ^ (δ / 2) at hcoeff
    have herr := mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (Nat.cast_nonneg a) (δ / 2))
    rw [← Real.rpow_add_of_nonneg (Nat.cast_nonneg a) (by positivity) (by positivity),
      show δ / 2 + δ / 2 = δ by ring] at herr
    rw [abs_le]
    constructor <;> linarith
  constructor
  · intro δ hδ
    obtain ⟨K, hK⟩ := both δ hδ
    refine ⟨K, fun a b ha hab hba ↦ ?_⟩
    linarith [(abs_le.mp (hK a b ha hab hba)).1]
  · intro δ hδ
    obtain ⟨K, hK⟩ := both δ hδ
    refine ⟨K, fun a b ha hab hba ↦ ?_⟩
    linarith [(abs_le.mp (hK a b ha hab hba)).2]

theorem main : H1 → H2 → type_of% @Erdos30.erdos_30 := by
  intro h1 h2 ε hε
  let δ : ℝ := min ε (1 / 2)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  obtain ⟨K, hK⟩ := square_error h1 h2 hδ (min_le_right _ _)
  apply Asymptotics.IsBigO.of_bound 5
  rw [Filter.eventually_atTop]
  refine ⟨max (K ^ 2) 2, fun N hN ↦ ?_⟩
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  let m := Nat.sqrt N
  have hm : K ≤ m := Nat.le_sqrt.mpr (by simpa [sq] using (le_max_left (K ^ 2) 2).trans hN)
  have hs : m ^ 2 ≤ N := by simpa [m, sq] using Nat.sqrt_le N
  have ht : N < (m + 1) ^ 2 := by simpa [m, sq] using Nat.lt_succ_sqrt N
  have hmN : m + 1 ≤ N := by
    by_contra! h
    have : N * N ≤ m * m := Nat.mul_le_mul (by omega) (by omega)
    rw [sq] at hs
    nlinarith
  have hreal : (m : ℝ) ≤ Real.sqrt N := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast hs
  have hreal' : Real.sqrt (N : ℝ) < (m : ℝ) + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    exact_mod_cast ht
  have hlo := h_mono hs
  have hhi := h_mono ht.le
  have hloR : (Erdos30.h (m ^ 2) : ℝ) ≤ Erdos30.h N := by exact_mod_cast hlo
  have hhiR : (Erdos30.h N : ℝ) ≤ Erdos30.h ((m + 1) ^ 2) := by exact_mod_cast hhi
  have hl := (abs_le.mp (hK m hm)).1
  have hu := (abs_le.mp (hK (m + 1) (by omega))).2
  push_cast at hu
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpow : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
  have hpow' : ((m : ℝ) + 1) ^ δ ≤ (N : ℝ) ^ ε :=
    (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmN) hδ.le).trans
      (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_left _ _))
  have hpow : (m : ℝ) ^ δ ≤ (N : ℝ) ^ ε :=
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith : (m : ℝ) ≤ m + 1) hδ.le).trans hpow'
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) ε)]
  rw [abs_le]
  constructor <;> linarith

end OMA.R_Erdos30_erdos_30_R2
