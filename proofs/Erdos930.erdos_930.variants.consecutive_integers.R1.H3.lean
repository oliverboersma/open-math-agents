import OMAReductions.R_Erdos930_erdos_930_variants_consecutive_integers_R1

/-!
Erdős–Selfridge, Lemma 2. For each small prime, delete one index of maximal valuation. The remaining powers divide the differences from that index on either side. Their products are bounded in valuation by two factorials whose product divides the desired factorial.
-/

open Finset

private lemma mappedVal {k b p : ℕ} (S : Finset (Fin k)) (a : Fin k → ℕ)
    (f : Fin k → ℕ) (hmap : ∀ i ∈ S, f i < b)
    (hinj : Set.InjOn f (S : Set (Fin k)))
    (hle : ∀ i ∈ S, (a i).factorization p ≤ (f i + 1).factorization p) :
    ∑ i ∈ S, (a i).factorization p ≤ b.factorial.factorization p := by
  rw [Nat.factorial_eq_prod_range_add_one, Nat.factorization_prod_apply (fun i _ => by omega)]
  calc
    _ ≤ ∑ i ∈ S, (f i + 1).factorization p := sum_le_sum hle
    _ = ∑ j ∈ S.image f, (j + 1).factorization p := by rw [sum_image hinj]
    _ ≤ _ := sum_le_sum_of_subset (by simpa [image_subset_iff, mem_range] using hmap)

private theorem trimCoefficients (n k : ℕ) (a : Fin k → ℕ) (hk : 0 < k)
    (hdiv : ∀ i, a i ∣ n+1+i.val) (hsmooth : ∀ i p, p.Prime → p ∣ a i → p < k) :
    ∃ T : Finset (Fin k), k - k.primesBelow.card ≤ T.card ∧
      (∏ i ∈ T, a i) ∣ (k-1).factorial := by
  classical
  have hne (i : Fin k) : a i ≠ 0 := by
    intro he
    have hd := hdiv i
    simp [he] at hd
  have maxEx (p : ℕ) : ∃ j : Fin k, ∀ i, (a i).factorization p ≤ (a j).factorization p := by
    obtain ⟨j, _, hj⟩ := exists_max_image univ (fun i => (a i).factorization p)
      (show (univ : Finset (Fin k)).Nonempty from ⟨⟨0,hk⟩, mem_univ _⟩)
    exact ⟨j, fun i => hj i (mem_univ _)⟩
  choose j hj using maxEx
  let T := univ \ k.primesBelow.image j
  refine ⟨T, ?_, ?_⟩
  · have := card_image_le (s := k.primesBelow) (f := j)
    simp only [T, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
    omega
  apply (Nat.factorization_le_iff_dvd (prod_ne_zero_iff.mpr (fun i _ => hne i))
    (Nat.factorial_ne_zero _)).mp
  intro p
  rw [Nat.factorization_prod_apply (fun i _ => hne i)]
  by_cases hp : p ∈ k.primesBelow
  · have hP := Nat.prime_of_mem_primesBelow hp
    let x := j p
    have hx (i : Fin k) (hi : i ∈ T) : i.val ≠ x.val := by
      intro he
      exact (mem_sdiff.mp hi).2 (mem_image.mpr ⟨p, hp, (Fin.ext he).symm⟩)
    have hd (i : Fin k) : p^((a i).factorization p) ∣ n+1+i.val :=
      ((hP.pow_dvd_iff_le_factorization (hne i)).mpr le_rfl).trans (hdiv i)
    have hm (i : Fin k) : p^((a i).factorization p) ∣ n+1+x.val :=
      ((hP.pow_dvd_iff_le_factorization (hne x)).mpr (hj p i)).trans (hdiv x)
    rw [← sum_filter_add_sum_filter_not T (fun i => i.val < x.val)]
    have left : ∑ i ∈ T.filter (fun i => i.val < x.val), (a i).factorization p ≤
        x.val.factorial.factorization p := by
      apply mappedVal _ _ (fun i => x.val-i.val-1)
      · intro i hi
        have := (mem_filter.mp hi).2
        omega
      · intro i hi t ht he
        have := (mem_filter.mp hi).2
        have := (mem_filter.mp ht).2
        apply Fin.ext
        dsimp at he
        omega
      · intro i hi
        have hl := (mem_filter.mp hi).2
        apply (hP.pow_dvd_iff_le_factorization (by omega)).mp
        convert Nat.dvd_sub (hm i) (hd i) using 1 <;> omega
    have right : ∑ i ∈ T.filter (fun i => ¬ i.val < x.val), (a i).factorization p ≤
        (k-1-x.val).factorial.factorization p := by
      have hlt (i : Fin k) (hi : i ∈ T.filter (fun i => ¬ i.val < x.val)) : x.val < i.val := by
        have him := mem_filter.mp hi
        have := hx i him.1
        omega
      apply mappedVal _ _ (fun i => i.val-x.val-1)
      · intro i hi
        have := hlt i hi
        have := i.isLt
        omega
      · intro i hi t ht he
        have := hlt i hi
        have := hlt t ht
        apply Fin.ext
        dsimp at he
        omega
      · intro i hi
        have := hlt i hi
        apply (hP.pow_dvd_iff_le_factorization (by omega)).mp
        convert Nat.dvd_sub (hd i) (hm i) using 1 <;> omega
    refine (Nat.add_le_add left right).trans ?_
    have hf := (Nat.factorization_le_iff_dvd (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero (k-1))).mpr (Nat.factorial_mul_factorial_dvd_factorial
      (show x.val ≤ k-1 by have := x.isLt; omega)) p
    simpa [Nat.factorization_mul, Nat.factorial_ne_zero] using hf
  · have hz (i : Fin k) : (a i).factorization p = 0 := by
      by_contra he
      have hmem : p ∈ (a i).primeFactors := by simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using he
      have hP := Nat.prime_of_mem_primeFactors hmem
      exact hp (Nat.mem_primesBelow.mpr ⟨hsmooth i p hP (Nat.dvd_of_mem_primeFactors hmem), hP⟩)
    simp [hz]


theorem OMA.solution : OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1.H3 := trimCoefficients
