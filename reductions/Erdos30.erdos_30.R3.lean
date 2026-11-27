import FormalConjectures.ErdosProblems.«30»

-- Reduction Erdos30.erdos_30.R3 of Erdős Problem 30
-- Credit: @ubuwaits

/-!
# Doubling the square-root length of a Sidon ruler

Write F(m) for the maximum size of a Sidon subset of [1,m²]. The two
hypotheses bound the two signs of F(2m) − 2F(m). For each m, R2 requested a
comparison with every b between m and 2m. Here the single choice b = m suffices.

After j doublings the error, divided by 2ʲ, is at most 4m^δ for δ ≤ 1/2.
An initially excessive value of F(m) then contradicts Lindström's upper
bound at a large dyadic multiple. An initially deficient value would force
the same proportional deficit along the entire dyadic sequence. But the
ratios 3ⁱ/2ʲ are dense in the positive reals, and Bose's Sidon sets give
F(2ʲm) ≥ 3ⁱ whenever 3ⁱ ≤ 2ʲm. This determines the limiting slope along
each such sequence using only one family of finite fields.

The finite Bose construction is from the first reduction by kenanwienberg.
The finite Lindström bound is from the accepted proof by michielkosters as
included in R2. The final interpolation between squares follows R2.
-/

namespace OMA.R_Erdos30_erdos_30_R3

open Filter Set
open scoped Asymptotics

/-- Doubling can supply twice as many marks up to a subpolynomial loss. -/
def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ m : ℕ, K ≤ m →
    2 * (Erdos30.h (m ^ 2) : ℝ) ≤ Erdos30.h ((2 * m) ^ 2) + (m : ℝ) ^ δ

/-- Doubling can supply at most twice as many marks up to a subpolynomial gain. -/
def H2 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ m : ℕ, K ≤ m →
    (Erdos30.h ((2 * m) ^ 2) : ℝ) ≤ 2 * Erdos30.h (m ^ 2) + (m : ℝ) ^ δ

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

/-- Bose's theorem (1942): for every prime power `q`, there exists a Sidon set of size `q`
contained in `{1, ..., q ^ 2 - 1}`, hence `q ≤ Erdos30.h (q ^ 2 - 1)`. -/
theorem bose_sidon {q : ℕ} (hq : IsPrimePow q) : q ≤ Erdos30.h (q ^ 2 - 1) := by
  classical
  rw [isPrimePow_nat_iff] at hq
  obtain ⟨p, r, hp, hr, hpr⟩ := hq
  have : Fact p.Prime := ⟨hp⟩
  let L := GaloisField p (2 * r)
  let : Fintype L := Fintype.ofFinite (GaloisField p (2 * r))
  have h2r : 2 * r ≠ 0 := by omega
  have hcardL : Nat.card L = q ^ 2 := by
    rw [GaloisField.card p (2 * r) h2r, ← hpr, ← pow_mul, mul_comm]
  have hq2 : 2 ≤ q := by
    rw [← hpr]
    exact le_trans hp.two_le (Nat.le_self_pow hr.ne' p)
  have hcardU : Nat.card Lˣ = q ^ 2 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcardL]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Lˣ)
  have hord : orderOf g = q ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcardU]
  have hg_pow_ne : (g : L) ^ q ≠ (g : L) := by
    intro heq
    have h1 : g ^ (q - 1) = 1 := by
      apply Units.ext
      have hmul : (g : L) ^ (q - 1) * (g : L) = 1 * (g : L) := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega), heq, one_mul]
      exact mul_right_cancel₀ g.ne_zero (by simpa using hmul)
    have hdvd : orderOf g ∣ q - 1 := orderOf_dvd_of_pow_eq_one h1
    have hle : orderOf g ≤ q - 1 := Nat.le_of_dvd (by omega) hdvd
    rw [hord] at hle
    have hq_sq : 1 ≤ q ^ 2 := by nlinarith
    have hle' : q ^ 2 ≤ q := by omega
    nlinarith
  have hadd_pow : ∀ x y : L, (x + y) ^ q = x ^ q + y ^ q := by
    intro x y
    rw [← hpr, add_pow_char_pow]
  let F : Finset L := insert 0 ((Finset.range (q - 1)).image fun k ↦ (((g ^ (q + 1)) ^ k : Lˣ) : L))
  have hF_fix : ∀ c ∈ F, c ^ q = c := by
    intro c hc
    rw [Finset.mem_insert, Finset.mem_image] at hc
    rcases hc with rfl | ⟨k, _, rfl⟩
    · exact zero_pow (by omega)
    · have hbase : (g ^ (q + 1)) ^ q = g ^ (q + 1) := by
        rw [← pow_mul]
        have hexp : (q + 1) * q = (q ^ 2 - 1) + (q + 1) := by
          zify [show 1 ≤ q ^ 2 by nlinarith]
          ring
        rw [hexp, pow_add, ← hord, pow_orderOf_eq_one, one_mul]
      have hpow : ((g ^ (q + 1)) ^ k) ^ q = (g ^ (q + 1)) ^ k := by
        rw [← pow_mul, mul_comm k q, pow_mul, hbase]
      exact_mod_cast congrArg Units.val hpow
  have hF_card : F.card = q := by
    have h0 : (0 : L) ∉ (Finset.range (q - 1)).image fun k ↦ (((g ^ (q + 1)) ^ k : Lˣ) : L) := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro k _ hk
      exact Units.ne_zero _ hk
    rw [Finset.card_insert_of_notMem h0, Finset.card_image_of_injOn]
    · rw [Finset.card_range]
      omega
    · intro k₁ hk₁ k₂ hk₂ heq
      rw [Finset.mem_coe, Finset.mem_range] at hk₁ hk₂
      wlog hle : k₁ ≤ k₂ generalizing k₁ k₂
      · exact (this hk₂ hk₁ heq.symm (by omega)).symm
      have hu : (g ^ (q + 1)) ^ k₁ = (g ^ (q + 1)) ^ k₂ := Units.ext heq
      have h1 : g ^ ((q + 1) * (k₂ - k₁)) = 1 := by
        rw [pow_mul]
        have hmul : (g ^ (q + 1)) ^ k₁ * (g ^ (q + 1)) ^ (k₂ - k₁) = (g ^ (q + 1)) ^ k₁ * 1 := by
          rw [← pow_add, Nat.add_sub_cancel' hle, mul_one, hu]
        exact mul_left_cancel hmul
      have hdvd : q ^ 2 - 1 ∣ (q + 1) * (k₂ - k₁) := by
        rw [← hord]
        exact orderOf_dvd_of_pow_eq_one h1
      have hfac : q ^ 2 - 1 = (q + 1) * (q - 1) := by
        zify [show 1 ≤ q by omega, show 1 ≤ q ^ 2 by nlinarith]
        ring
      rw [hfac] at hdvd
      have hdvd' : q - 1 ∣ k₂ - k₁ := (Nat.mul_dvd_mul_iff_left (by omega)).mp hdvd
      have hzero : k₂ - k₁ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' (by omega)
      omega
  have hne_zero : ∀ c ∈ F, (g : L) + c ≠ 0 := by
    intro c hc hzero
    have h1 : ((g : L) + c) ^ q = 0 := by rw [hzero, zero_pow (by omega)]
    rw [hadd_pow, hF_fix c hc] at h1
    apply hg_pow_ne
    linear_combination h1 - hzero
  have hex_log : ∀ c ∈ F, ∃ a ∈ Finset.Icc 1 (q ^ 2 - 1), (g : L) ^ a = (g : L) + c := by
    intro c hc
    let u : Lˣ := Units.mk0 ((g : L) + c) (hne_zero c hc)
    obtain ⟨m, hm⟩ := hg u
    have hpos : 0 < orderOf g := by
      rw [hord]
      have : 4 ≤ q ^ 2 := by nlinarith
      omega
    have hfin : ∃ k : ℕ, k < orderOf g ∧ g ^ k = u := by
      refine ⟨(m % (orderOf g : ℤ)).toNat, ?_, ?_⟩
      · have hlt := Int.emod_lt_of_pos m (Int.natCast_pos.mpr hpos)
        have hnn := Int.emod_nonneg m (Int.natCast_ne_zero.mpr hpos.ne')
        omega
      · have hnn := Int.emod_nonneg m (Int.natCast_ne_zero.mpr hpos.ne')
        rw [← zpow_natCast, Int.toNat_of_nonneg hnn, zpow_mod_orderOf]
        exact hm
    obtain ⟨k, hk, hgk⟩ := hfin
    rw [hord] at hk
    by_cases hk0 : k = 0
    · refine ⟨q ^ 2 - 1, Finset.mem_Icc.mpr ⟨by rw [← hord]; omega, le_rfl⟩, ?_⟩
      have hu1 : u = 1 := by rw [← hgk, hk0, pow_zero]
      have hg1 : g ^ (q ^ 2 - 1) = 1 := by rw [← hord, pow_orderOf_eq_one]
      have := congrArg Units.val (hg1.trans hu1.symm)
      simpa [u] using this
    · refine ⟨k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      have := congrArg Units.val hgk
      simpa [u] using this
  let f : L → ℕ := fun c ↦ if hc : c ∈ F then Classical.choose (hex_log c hc) else 0
  have hf_mem : ∀ c ∈ F, f c ∈ Finset.Icc 1 (q ^ 2 - 1) := by
    intro c hc
    simp only [f, dif_pos hc]
    exact (Classical.choose_spec (hex_log c hc)).1
  have hf_pow : ∀ c ∈ F, (g : L) ^ f c = (g : L) + c := by
    intro c hc
    simp only [f, dif_pos hc]
    exact (Classical.choose_spec (hex_log c hc)).2
  let A : Finset ℕ := F.image f
  have hA_sub : A ⊆ Finset.Icc 1 (q ^ 2 - 1) := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨c, hc, rfl⟩ := ha
    exact hf_mem c hc
  have hA_card : A.card = q := by
    rw [Finset.card_image_of_injOn, hF_card]
    intro c₁ hc₁ c₂ hc₂ heq
    have h1 := hf_pow c₁ hc₁
    have h2 := hf_pow c₂ hc₂
    rw [heq] at h1
    exact add_left_cancel (h1.symm.trans h2)
  have hA_sidon : IsSidon (A : Set ℕ) := by
    intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ hsum
    simp only [A, Finset.mem_coe, Finset.mem_image] at ha₁ hb₁ ha₂ hb₂
    obtain ⟨c₁, hc₁, rfl⟩ := ha₁
    obtain ⟨d₁, hd₁, rfl⟩ := hb₁
    obtain ⟨c₂, hc₂, rfl⟩ := ha₂
    obtain ⟨d₂, hd₂, rfl⟩ := hb₂
    have hprod : ((g : L) + c₁) * ((g : L) + c₂) = ((g : L) + d₁) * ((g : L) + d₂) := by
      rw [← hf_pow c₁ hc₁, ← hf_pow c₂ hc₂, ← hf_pow d₁ hd₁, ← hf_pow d₂ hd₂,
        ← pow_add, ← pow_add, hsum]
    have hlin : (c₁ + c₂) * (g : L) + c₁ * c₂ = (d₁ + d₂) * (g : L) + d₁ * d₂ := by
      linear_combination hprod
    have hlin_q : (c₁ + c₂) * (g : L) ^ q + c₁ * c₂ = (d₁ + d₂) * (g : L) ^ q + d₁ * d₂ := by
      have h := congrArg (fun x : L ↦ x ^ q) hlin
      simp only [hadd_pow, mul_pow, hF_fix c₁ hc₁, hF_fix c₂ hc₂, hF_fix d₁ hd₁, hF_fix d₂ hd₂] at h
      exact h
    have hdiff : (c₁ + c₂ - (d₁ + d₂)) * ((g : L) ^ q - (g : L)) = 0 := by
      linear_combination hlin_q - hlin
    have hsum_c : c₁ + c₂ = d₁ + d₂ := by
      rcases mul_eq_zero.mp hdiff with h | h
      · exact sub_eq_zero.mp h
      · exact (hg_pow_ne (sub_eq_zero.mp h)).elim
    have hprod_c : c₁ * c₂ = d₁ * d₂ := by
      linear_combination hlin - (g : L) * hsum_c
    have hquad : (c₁ - d₁) * (c₁ - d₂) = 0 := by
      linear_combination c₁ * hsum_c - hprod_c
    rcases mul_eq_zero.mp hquad with h | h
    · have h1 : c₁ = d₁ := sub_eq_zero.mp h
      have h2 : c₂ = d₂ := by linear_combination hsum_c - h1
      exact Or.inl ⟨congrArg f h1, congrArg f h2⟩
    · have h1 : c₁ = d₂ := sub_eq_zero.mp h
      have h2 : c₂ = d₁ := by linear_combination hsum_c - h1
      exact Or.inr ⟨congrArg f h1, congrArg f h2⟩
  calc
    q = A.card := hA_card.symm
    _ ≤ Erdos30.h (q ^ 2 - 1) := card_le_h hA_sidon hA_sub

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

lemma square_upper (m : ℕ) : (Erdos30.h (m ^ 2) : ℝ) ≤ m + Real.sqrt m + 1 := by
  have h := lindstrom_bound (m ^ 2)
  push_cast at h
  rw [Real.sqrt_sq (Nat.cast_nonneg m)] at h
  have heq : ((m : ℝ) ^ 2) ^ (4⁻¹ : ℝ) = Real.sqrt m := by
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg m), Real.sqrt_eq_rpow]
    norm_num
  rwa [heq] at h

lemma irrational_log_three_two : Irrational (Real.log 3 / Real.log 2) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rintro ⟨q, hq⟩
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  rw [Rat.cast_def, div_eq_div_iff hd.ne' h2.ne'] at hq
  have hn : (0 : ℝ) < q.num := by
    by_contra! h
    have := mul_nonpos_of_nonpos_of_nonneg h h2.le
    nlinarith [mul_pos h3 hd]
  have hi : 0 ≤ q.num := by exact_mod_cast hn.le
  have hh : Real.log ((3 : ℝ) ^ q.den) = Real.log ((2 : ℝ) ^ q.num.toNat) := by
    rw [Real.log_pow, Real.log_pow]
    have hc : (q.num.toNat : ℝ) = q.num := by
      exact_mod_cast Int.toNat_of_nonneg hi
    rw [hc]
    linarith
  have hp := Real.log_injOn_pos (by positivity : 0 < (3 : ℝ) ^ q.den)
    (by positivity : 0 < (2 : ℝ) ^ q.num.toNat) hh
  have hnat : (3 : ℕ) ^ q.den = 2 ^ q.num.toNat := by exact_mod_cast hp
  have hdvd : 3 ∣ (3 : ℕ) ^ q.den := dvd_pow_self 3 q.den_ne_zero
  rw [hnat] at hdvd
  have hf := Nat.prime_three.dvd_of_dvd_pow hdvd
  norm_num at hf

/-- An interval of positive real slopes contains 3ⁱ/2ʲ with i and j natural. -/
lemma power_ratio_between {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ i j : ℕ, 0 < i ∧ a * (2 : ℝ) ^ j < 3 ^ i ∧ (3 : ℝ) ^ i < b * 2 ^ j := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let : Fact (0 < Real.log 2) := ⟨h2⟩
  have hb : 0 < b := ha.trans hab
  have hd : DenseRange (fun n : ℕ ↦ n • (Real.log 3 : AddCircle (Real.log 2))) :=
    denseRange_zsmul_iff_nsmul.mp (AddCircle.denseRange_zsmul_coe_iff.mpr irrational_log_three_two)
  obtain ⟨t, ht⟩ := exists_nat_gt (max (Real.log b / Real.log 3) 0)
  have htpos : 0 < t := by exact_mod_cast (le_max_right _ _).trans_lt ht
  have htb := (div_lt_iff₀ h3).mp ((le_max_left _ _).trans_lt ht)
  let l := Real.log a - t * Real.log 3
  let u := Real.log b - t * Real.log 3
  have hlu : l < u := sub_lt_sub_right (Real.log_lt_log ha hab) _
  let Q := (fun x : ℝ ↦ (x : AddCircle (Real.log 2)))
  have hop : IsOpen (Q '' Ioo l u) :=
    QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  obtain ⟨n, x, hx, hxn⟩ := hd.exists_mem_open hop ((nonempty_Ioo.mpr hlu).image Q)
  have heq : ((n • Real.log 3 - x : ℝ) : AddCircle (Real.log 2)) = 0 := by
    rw [AddCircle.coe_sub, AddCircle.coe_nsmul, sub_eq_zero]
    exact hxn.symm
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff _).mp heq
  rw [zsmul_eq_mul, nsmul_eq_mul] at hz
  have hx0 : x < 0 := lt_trans hx.2 (by dsimp [u]; linarith)
  have hzpos : (0 : ℝ) < z := by
    by_contra! h
    have hn := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) h3.le
    have hz' := mul_nonpos_of_nonpos_of_nonneg h h2.le
    linarith
  have hzcast : (z.toNat : ℝ) = z := by
    exact_mod_cast Int.toNat_of_nonneg (by exact_mod_cast hzpos.le)
  refine ⟨n + t, z.toNat, by omega, ?_, ?_⟩
  · apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul ha.ne' (by positivity), Real.log_pow, Real.log_pow, hzcast, Nat.cast_add]
    have hxl := hx.1
    dsimp [l] at hxl
    linarith
  · apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (ha.trans hab).ne' (by positivity), Real.log_pow, Real.log_pow,
      hzcast, Nat.cast_add]
    have hxu := hx.2
    dsimp [u] at hxu
    linarith

/-- Every square-root length has a sequence of dyadic multiples on which
the Bose construction comes arbitrarily close to one mark per unit of root length. -/
lemma lower_on_dyadic_ray {n : ℕ} {c : ℝ} (hc : 0 < c) (hcn : c < n) :
    ∃ j : ℕ, c * (2 : ℝ) ^ j < Erdos30.h (((2 : ℕ) ^ j * n) ^ 2) := by
  obtain ⟨i, j, hi, hlo, hup⟩ := power_ratio_between hc hcn
  have hq : IsPrimePow ((3 : ℕ) ^ i) := by
    rw [isPrimePow_nat_iff]
    exact ⟨3, i, Nat.prime_three, hi, rfl⟩
  have hle : (3 : ℕ) ^ i ≤ 2 ^ j * n := by
    exact_mod_cast (by simpa [mul_comm] using hup.le : (3 : ℝ) ^ i ≤ 2 ^ j * n)
  have hfit : ((3 : ℕ) ^ i) ^ 2 - 1 ≤ (2 ^ j * n) ^ 2 :=
    (Nat.sub_le _ _).trans (Nat.pow_le_pow_left hle _)
  have hsize := (bose_sidon hq).trans
    (h_mono hfit)
  exact ⟨j, hlo.trans_le (by exact_mod_cast hsize)⟩

/-- The sum of the successive doubling errors is bounded independently
of the number of doublings after division by the final multiplier. -/
lemma iterate_doubling (F : ℕ → ℝ) {δ : ℝ} (hhalf : δ ≤ 1 / 2)
    {K m : ℕ} (hm : K ≤ m)
    (step : ∀ x : ℕ, K ≤ x → F (2 * x) - 2 * F x ≤ (x : ℝ) ^ δ) (j : ℕ) :
    F (2 ^ j * m) - (2 : ℝ) ^ j * F m ≤
      4 * ((2 : ℝ) ^ j - ((2 : ℝ) ^ j) ^ δ) * (m : ℝ) ^ δ := by
  induction j with
  | zero => simp
  | succ j ih =>
    let k := (2 : ℕ) ^ j
    have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by dsimp [k]; positivity)
    have hs := step (k * m) (hm.trans (by simpa using Nat.mul_le_mul_right m hk))
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg k) (Nat.cast_nonneg m)] at hs
    have htwo : (2 : ℝ) ^ δ ≤ 7 / 4 := by
      calc (2 : ℝ) ^ δ ≤ 2 ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hhalf
        _ = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm
        _ ≤ 7 / 4 := by rw [Real.sqrt_le_iff]; norm_num
    have hkm : 0 ≤ (k : ℝ) ^ δ * (m : ℝ) ^ δ := by positivity
    have hc := mul_le_mul_of_nonneg_right htwo hkm
    have hcast : (k : ℝ) = (2 : ℝ) ^ j := by simp [k]
    rw [← hcast] at ih
    change F (k * m) - (k : ℝ) * F m ≤ _ at ih
    simp only [pow_succ', ← hcast, Nat.mul_assoc, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2)
      (Nat.cast_nonneg k)]
    change F (2 * (k * m)) - 2 * k * F m ≤ _
    linarith

lemma linear_doubling (F : ℕ → ℝ) {δ : ℝ} (hhalf : δ ≤ 1 / 2)
    {K m : ℕ} (hm : K ≤ m)
    (step : ∀ x : ℕ, K ≤ x → F (2 * x) - 2 * F x ≤ (x : ℝ) ^ δ) (j : ℕ) :
    F (2 ^ j * m) - (2 : ℝ) ^ j * F m ≤ (2 : ℝ) ^ j * (4 * (m : ℝ) ^ δ) := by
  have h := iterate_doubling F hhalf hm step j
  have hpos : 0 ≤ ((2 : ℝ) ^ j) ^ δ * (m : ℝ) ^ δ := by positivity
  linarith

lemma upper_from_doubling {m : ℕ} {E : ℝ}
    (hr : ∀ j : ℕ, (2 : ℝ) ^ j * Erdos30.h (m ^ 2) - Erdos30.h ((2 ^ j * m) ^ 2) ≤
      (2 : ℝ) ^ j * E) : (Erdos30.h (m ^ 2) : ℝ) - m ≤ E := by
  by_contra! hbad
  let g := (Erdos30.h (m ^ 2) : ℝ) - m - E
  have hg : 0 < g := by dsimp [g]; linarith
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (max (((m : ℝ) + 2) / g) 1)
    (by norm_num : 1 < (2 : ℝ))
  let t := (2 : ℕ) ^ j
  have ht : max (((m : ℝ) + 2) / g) 1 < (t : ℝ) := by simpa [t] using hj
  have ht1 := (le_max_right _ _).trans_lt ht
  have htlarge := (div_lt_iff₀ hg).mp ((le_max_left _ _).trans_lt ht)
  have hstrict := mul_lt_mul_of_pos_left htlarge (by positivity : 0 < (t : ℝ))
  have hlow := hr (j * 2)
  rw [pow_mul, pow_mul] at hlow
  change (2 ^ j : ℝ) ^ 2 * _ - Erdos30.h ((t ^ 2 * m) ^ 2) ≤ _ at hlow
  have htcast : (t : ℝ) = 2 ^ j := by simp [t]
  rw [← htcast] at hlow
  have hup := square_upper (t ^ 2 * m)
  push_cast at hup
  rw [Real.sqrt_mul (sq_nonneg (t : ℝ)), Real.sqrt_sq (Nat.cast_nonneg t)] at hup
  have hsqrt : Real.sqrt m ≤ (m : ℝ) + 1 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith [sq_nonneg (m : ℝ), Nat.cast_nonneg (α := ℝ) m]
  have hsm := mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg t)
  dsimp [g] at hstrict
  linarith

lemma lower_from_doubling {m : ℕ} (hm : 0 < m) {E : ℝ}
    (hr : ∀ j : ℕ, (Erdos30.h ((2 ^ j * m) ^ 2) : ℝ) - (2 : ℝ) ^ j * Erdos30.h (m ^ 2) ≤
      (2 : ℝ) ^ j * E) : (m : ℝ) - Erdos30.h (m ^ 2) ≤ E := by
  by_contra! hbad
  let c := max ((Erdos30.h (m ^ 2) : ℝ) + E) ((m : ℝ) / 2)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : 0 < c := (by positivity : (0 : ℝ) < m / 2).trans_le (le_max_right _ _)
  have hcm : c < m := max_lt (by linarith) (by linarith)
  obtain ⟨j, hj⟩ := lower_on_dyadic_ray hc hcm
  have hl := mul_le_mul_of_nonneg_right (le_max_left ((Erdos30.h (m ^ 2) : ℝ) + E)
    ((m : ℝ) / 2)) (by positivity : (0 : ℝ) ≤ 2 ^ j)
  change _ ≤ c * _ at hl
  linarith [hr j]

lemma square_excess (h1 : H1) {δ : ℝ} (hδ : 0 < δ) (hhalf : δ ≤ 1 / 2) :
    ∃ K : ℕ, ∀ m : ℕ, K ≤ m → (Erdos30.h (m ^ 2) : ℝ) - m ≤ 4 * (m : ℝ) ^ δ := by
  obtain ⟨K, hK⟩ := h1 δ hδ
  refine ⟨K, fun m hm ↦ upper_from_doubling (fun j ↦ ?_)⟩
  have h := linear_doubling (fun x ↦ -(Erdos30.h (x ^ 2) : ℝ)) hhalf hm
    (fun x hx ↦ by linarith [hK x hx]) j
  linarith

lemma square_deficit (h2 : H2) {δ : ℝ} (hδ : 0 < δ) (hhalf : δ ≤ 1 / 2) :
    ∃ K : ℕ, ∀ m : ℕ, K ≤ m → (m : ℝ) - Erdos30.h (m ^ 2) ≤ 4 * (m : ℝ) ^ δ := by
  obtain ⟨K, hK⟩ := h2 δ hδ
  refine ⟨K + 1, fun m hm ↦ lower_from_doubling (by omega) (fun j ↦ ?_)⟩
  exact linear_doubling (fun x ↦ (Erdos30.h (x ^ 2) : ℝ)) hhalf (by omega : K ≤ m)
    (fun x hx ↦ by linarith [hK x hx]) j

lemma square_error (h1 : H1) (h2 : H2) {δ : ℝ} (hδ : 0 < δ) (hhalf : δ ≤ 1 / 2) :
    ∃ K : ℕ, ∀ m : ℕ, K ≤ m →
      |(Erdos30.h (m ^ 2) : ℝ) - m| ≤ 4 * (m : ℝ) ^ δ := by
  obtain ⟨A, hA⟩ := square_excess h1 hδ hhalf
  obtain ⟨B, hB⟩ := square_deficit h2 hδ hhalf
  refine ⟨max A B, fun m hm ↦ abs_le.mpr ⟨?_, hA m ((le_max_left _ _).trans hm)⟩⟩
  linarith [hB m ((le_max_right _ _).trans hm)]

theorem doubling_of_target (h : type_of% @Erdos30.erdos_30) : H1 ∧ H2 := by
  have both : ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ m : ℕ, K ≤ m →
      |(Erdos30.h ((2 * m) ^ 2) : ℝ) - 2 * Erdos30.h (m ^ 2)| ≤ (m : ℝ) ^ δ := by
    intro δ hδ
    let s := δ / 2
    have hs : 0 < s := by dsimp [s]; positivity
    obtain ⟨C, hC, hc⟩ := Asymptotics.isBigO_iff'.mp (h (δ / 4) (by positivity))
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hc
    have hsquare : ∀ u : ℕ, M ≤ u → |(Erdos30.h (u ^ 2) : ℝ) - u| ≤ C * (u : ℝ) ^ s := by
      intro u hu
      have hh := hM (u ^ 2) (hu.trans (by simpa [sq] using Nat.le_mul_self u))
      simp only [Real.norm_eq_abs, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg u),
        abs_of_nonneg (Real.rpow_nonneg (sq_nonneg (u : ℝ)) _)] at hh
      rw [← Real.rpow_natCast_mul (Nat.cast_nonneg u)] at hh
      norm_num only [Nat.cast_ofNat] at hh
      rwa [show (2 : ℝ) * (δ / 4) = s by dsimp [s]; ring] at hh
    have hlim : Tendsto (fun m : ℕ ↦ (m : ℝ) ^ s) atTop atTop :=
      (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
    obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp
      (hlim.eventually_ge_atTop (C * ((2 : ℝ) ^ s + 2)))
    refine ⟨max M L, fun m hm ↦ ?_⟩
    have hM' := (le_max_left M L).trans hm
    have ha := abs_le.mp (hsquare m hM')
    have hb := abs_le.mp (hsquare (2 * m) (by omega))
    push_cast at hb
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg m)] at hb
    have hc' : C * ((2 : ℝ) ^ s + 2) ≤ (m : ℝ) ^ s := hL m ((le_max_right _ _).trans hm)
    have hcoef := mul_le_mul_of_nonneg_right hc' (Real.rpow_nonneg (Nat.cast_nonneg m) s)
    rw [← Real.rpow_add_of_nonneg (Nat.cast_nonneg m) hs.le hs.le,
      show s + s = δ by dsimp [s]; ring] at hcoef
    rw [abs_le]
    constructor <;> linarith
  constructor
  · intro δ hδ
    obtain ⟨K, hK⟩ := both δ hδ
    refine ⟨K, fun m hm ↦ ?_⟩
    linarith [(abs_le.mp (hK m hm)).1]
  · intro δ hδ
    obtain ⟨K, hK⟩ := both δ hδ
    refine ⟨K, fun m hm ↦ ?_⟩
    linarith [(abs_le.mp (hK m hm)).2]

/-- Interpolation between consecutive squares, as in the second reduction. -/
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

theorem target_iff_doubling : (type_of% @Erdos30.erdos_30) ↔ H1 ∧ H2 :=
  ⟨doubling_of_target, fun h ↦ main h.1 h.2⟩

end OMA.R_Erdos30_erdos_30_R3
