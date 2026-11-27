import OMAStatements.S_oeis_a379181

namespace OMA_oeis_a379181

open OMA.S_oeis_a379181 Finset Filter

lemma digitWord_lt_ten (k : ℕ) : ∀ d ∈ digitWord k, d < 10 := by
  intro d hd
  by_cases hk : k = 0
  · subst hk
    simp [digitWord] at hd
    omega
  · simp only [digitWord, hk, ↓reduceIte, List.mem_reverse] at hd
    exact Nat.digits_lt_base (by norm_num) hd

lemma ofDigits_digitWord_reverse (k : ℕ) :
    Nat.ofDigits 10 (digitWord k).reverse = k := by
  by_cases hk : k = 0
  · subst hk
    simp [digitWord]
  · simp [digitWord, hk, Nat.ofDigits_digits]

lemma digitWord_injective : Function.Injective digitWord := by
  intro a b hab
  have h := congrArg (fun w => Nat.ofDigits 10 w.reverse) hab
  simpa only [ofDigits_digitWord_reverse] using h

lemma one_le_term {n : ℕ} (hn : 1 ≤ n) : 1 ≤ term n := by
  let l : List ℕ := List.replicate n 1
  let k : ℕ := Nat.ofDigits 10 l
  have hdig : Nat.digits 10 k = l := by
    apply Nat.digits_ofDigits 10 (by norm_num) l
    · intro x hx
      rw [List.mem_replicate] at hx
      omega
    · intro hne
      have hmem : l.getLast hne ∈ l := List.getLast_mem hne
      rw [List.mem_replicate] at hmem
      omega
  have hk_ne : k ≠ 0 := by
    intro hk0
    rw [hk0, Nat.digits_zero] at hdig
    have hlen := congrArg List.length hdig
    simp [l] at hlen
    omega
  have hword : digitWord k = l := by
    simp [digitWord, hk_ne, hdig, l]
  have hk_lt : k < 10 ^ n := by
    have h := Nat.lt_base_pow_length_digits (b := 10) (m := k) (by norm_num)
    simpa [hdig, l] using h
  have hlen : (digitWord k).length = n := by
    simp [hword, l]
  have hqual : qualifies (digitWord k) = true := by
    rw [hword]
    simp only [qualifies, List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
    refine ⟨1, by omega, ?_, ?_⟩
    · simp only [uniqueMode, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
        decide_eq_true_eq]
      intro d _
      by_cases hd : d = 1
      · exact Or.inl hd
      · right
        have hcount_d : l.count d = 0 := by
          rw [List.count_eq_zero]
          simp [l, hd]
        have hcount_1 : l.count 1 = n := by
          simp [l]
        omega
    · simp [l]
  have hmem : k ∈ (Finset.range (10 ^ n)).filter fun m =>
      (digitWord m).length = n ∧ qualifies (digitWord m) = true := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hk_lt, hlen, hqual⟩
  exact Finset.card_pos.mpr ⟨k, hmem⟩

def toTuple (n k : ℕ) (i : Fin n) : Fin 10 :=
  if h : i.val < (digitWord k).length then
    ⟨(digitWord k)[i.val], digitWord_lt_ten k _ (List.getElem_mem h)⟩
  else
    0

lemma ofFn_toTuple {n k : ℕ} (hlen : (digitWord k).length = n) :
    List.ofFn (fun i : Fin n => (toTuple n k i).val) = digitWord k := by
  refine List.ext_getElem ?_ ?_
  · simp [hlen]
  · intro i hi₁ hi₂
    have hi : i < (digitWord k).length := hi₂
    simp [toTuple, hi]

lemma sum_toTuple {n k : ℕ} (hlen : (digitWord k).length = n) :
    ∑ i : Fin n, (toTuple n k i).val = (digitWord k).sum := by
  rw [← ofFn_toTuple hlen]
  exact (List.sum_ofFn).symm

def highTuples (n : ℕ) : Finset (Fin n → Fin 10) :=
  Finset.univ.filter fun f => 5 * n ≤ ∑ i : Fin n, (f i).val

def lowTuples (n : ℕ) : Finset (Fin n → Fin 10) :=
  Finset.univ.filter fun f => ∑ i : Fin n, (f i).val ≤ 4 * n

def flipTuple {n : ℕ} (f : Fin n → Fin 10) : Fin n → Fin 10 :=
  fun i => ⟨9 - (f i).val, by omega⟩

lemma flipTuple_involutive {n : ℕ} : Function.Involutive (@flipTuple n) := by
  intro f
  funext i
  ext
  have hi : (f i).val < 10 := (f i).isLt
  simp [flipTuple]
  omega

lemma sum_flipTuple_add {n : ℕ} (f : Fin n → Fin 10) :
    (∑ i : Fin n, (flipTuple f i).val) + (∑ i : Fin n, (f i).val) = 9 * n := by
  rw [← Finset.sum_add_distrib]
  have hpt : ∀ i : Fin n, (flipTuple f i).val + (f i).val = 9 := by
    intro i
    have hi : (f i).val < 10 := (f i).isLt
    simp [flipTuple]
    omega
  simp [hpt, mul_comm]

lemma card_lowTuples_le_highTuples (n : ℕ) : (lowTuples n).card ≤ (highTuples n).card := by
  refine Finset.card_le_card_of_injOn flipTuple ?_ ?_
  · intro f hf
    simp only [lowTuples, highTuples, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and] at hf ⊢
    have hsum := sum_flipTuple_add f
    omega
  · intro f₁ _ f₂ _ h
    exact flipTuple_involutive.injective h

lemma term_le_two_mul_highTuples (n : ℕ) : term n ≤ 2 * (highTuples n).card := by
  let S := (Finset.range (10 ^ n)).filter fun k =>
    (digitWord k).length = n ∧ qualifies (digitWord k) = true
  have hmaps : Set.MapsTo (toTuple n) (S : Set ℕ)
      ((highTuples n ∪ lowTuples n : Finset _) : Set _) := by
    intro k hk
    simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨_, hlen, hqual⟩ := hk
    simp only [qualifies, List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hqual
    obtain ⟨m, hm, _, hsum⟩ := hqual
    rw [hlen] at hsum
    have htsum : ∑ i : Fin n, (toTuple n k i).val = m * n := by
      rw [sum_toTuple hlen, hsum]
    simp only [Finset.mem_coe, Finset.mem_union, highTuples, lowTuples,
      Finset.mem_filter, Finset.mem_univ, true_and, htsum]
    by_cases h5 : 5 ≤ m
    · exact Or.inl (Nat.mul_le_mul_right n h5)
    · exact Or.inr (Nat.mul_le_mul_right n (by omega))
  have hinj : Set.InjOn (toTuple n) (S : Set ℕ) := by
    intro k₁ hk₁ k₂ hk₂ heq
    simp only [S, Finset.mem_coe, Finset.mem_filter] at hk₁ hk₂
    have h1 := ofFn_toTuple hk₁.2.1
    have h2 := ofFn_toTuple hk₂.2.1
    rw [heq] at h1
    exact digitWord_injective (h1.symm.trans h2)
  have hle : S.card ≤ (highTuples n ∪ lowTuples n).card :=
    Finset.card_le_card_of_injOn (toTuple n) hmaps hinj
  have hunion : (highTuples n ∪ lowTuples n).card ≤ (highTuples n).card + (lowTuples n).card :=
    Finset.card_union_le _ _
  have hlow := card_lowTuples_le_highTuples n
  change S.card ≤ 2 * (highTuples n).card
  omega

lemma sum_eleven_tenths_le :
    (∑ d : Fin 10, (11 / 10 : ℝ) ^ d.val) ≤ (11 / 10 : ℝ) ^ 5 * (99 / 10 : ℝ) := by
  simp [Fin.sum_univ_succ]
  norm_num

lemma card_highTuples_le (n : ℕ) :
    ((highTuples n).card : ℝ) ≤ (99 / 10 : ℝ) ^ n := by
  let t : ℝ := 11 / 10
  have ht1 : (1 : ℝ) ≤ t := by norm_num [t]
  have htpos : (0 : ℝ) < t := by norm_num [t]
  have hpow_pos : (0 : ℝ) < t ^ (5 * n) := pow_pos htpos _
  have h1 : ((highTuples n).card : ℝ) * t ^ (5 * n) ≤
      ∑ f ∈ highTuples n, ∏ i : Fin n, t ^ (f i).val := by
    calc
      ((highTuples n).card : ℝ) * t ^ (5 * n)
          = ∑ _f ∈ highTuples n, t ^ (5 * n) := by simp
      _ ≤ ∑ f ∈ highTuples n, t ^ (∑ i : Fin n, (f i).val) := by
          refine Finset.sum_le_sum fun f hf => ?_
          have hge : 5 * n ≤ ∑ i : Fin n, (f i).val := (Finset.mem_filter.mp hf).2
          exact pow_le_pow_right₀ ht1 hge
      _ = ∑ f ∈ highTuples n, ∏ i : Fin n, t ^ (f i).val := by
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [Finset.prod_pow_eq_pow_sum]
  have h2 : ∑ f ∈ highTuples n, ∏ i : Fin n, t ^ (f i).val ≤
      ∑ f : Fin n → Fin 10, ∏ i : Fin n, t ^ (f i).val := by
    refine Finset.sum_le_univ_sum_of_nonneg fun f => ?_
    exact Finset.prod_nonneg fun i _ => pow_nonneg htpos.le _
  have h3 : (∑ f : Fin n → Fin 10, ∏ i : Fin n, t ^ (f i).val) =
      (∑ d : Fin 10, t ^ d.val) ^ n := by
    rw [← Fintype.prod_sum (fun (_ : Fin n) (d : Fin 10) => t ^ d.val)]
    simp
  have h4 : (∑ d : Fin 10, t ^ d.val) ^ n ≤ (t ^ 5 * (99 / 10 : ℝ)) ^ n := by
    refine pow_le_pow_left₀ ?_ sum_eleven_tenths_le n
    exact Finset.sum_nonneg fun d _ => pow_nonneg htpos.le _
  have h5 : (t ^ 5 * (99 / 10 : ℝ)) ^ n = (99 / 10 : ℝ) ^ n * t ^ (5 * n) := by
    rw [mul_pow, ← pow_mul, mul_comm]
  have hcomb : ((highTuples n).card : ℝ) * t ^ (5 * n) ≤
      (99 / 10 : ℝ) ^ n * t ^ (5 * n) :=
    h1.trans (h2.trans (h3.le.trans (h4.trans h5.le)))
  exact le_of_mul_le_mul_right hcomb hpow_pos

lemma term_le_exp (n : ℕ) : (term n : ℝ) ≤ 2 * (99 / 10 : ℝ) ^ n := by
  have hnat : (term n : ℝ) ≤ 2 * ((highTuples n).card : ℝ) := by
    exact_mod_cast term_le_two_mul_highTuples n
  have hhi := card_highTuples_le n
  linarith

lemma bernoulli_199_198 : ∀ r : ℕ, 1 + (r : ℝ) / 198 ≤ (199 / 198 : ℝ) ^ r
  | 0 => by norm_num
  | r + 1 => by
      have ih := bernoulli_199_198 r
      have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      push_cast
      rw [pow_succ]
      nlinarith

end OMA_oeis_a379181

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a379181.main) := by
  intro hmain
  have hev : ∀ᶠ n in Filter.atTop,
      (995 / 100 : ℝ) <
        (OMA.S_oeis_a379181.term (n + 1) : ℝ) / (OMA.S_oeis_a379181.term n : ℝ) :=
    hmain.eventually (Ioi_mem_nhds (by norm_num))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  let N : ℕ := max N₀ 1
  have hN1 : 1 ≤ N := le_max_right N₀ 1
  have hstep : ∀ n ≥ N,
      (995 / 100 : ℝ) * (OMA.S_oeis_a379181.term n : ℝ) ≤
        (OMA.S_oeis_a379181.term (n + 1) : ℝ) := by
    intro n hn
    have hlt : (995 / 100 : ℝ) <
        (OMA.S_oeis_a379181.term (n + 1) : ℝ) / (OMA.S_oeis_a379181.term n : ℝ) :=
      hN₀ n (le_trans (le_max_left N₀ 1) hn)
    have hpos : (0 : ℝ) < (OMA.S_oeis_a379181.term n : ℝ) := by
      have h1 : 1 ≤ OMA.S_oeis_a379181.term n := OMA_oeis_a379181.one_le_term (by omega)
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
    exact (le_div_iff₀ hpos).mp hlt.le
  have hlower : ∀ r : ℕ, (995 / 100 : ℝ) ^ r ≤ (OMA.S_oeis_a379181.term (N + r) : ℝ) := by
    intro r
    induction r with
    | zero =>
        simp only [pow_zero, add_zero]
        exact_mod_cast OMA_oeis_a379181.one_le_term hN1
    | succ r ih =>
        calc
          (995 / 100 : ℝ) ^ (r + 1)
              = (995 / 100 : ℝ) * (995 / 100 : ℝ) ^ r := by rw [pow_succ']
          _ ≤ (995 / 100 : ℝ) * (OMA.S_oeis_a379181.term (N + r) : ℝ) := by
              exact mul_le_mul_of_nonneg_left ih (by norm_num)
          _ ≤ (OMA.S_oeis_a379181.term (N + r + 1) : ℝ) := hstep (N + r) (by omega)
          _ = (OMA.S_oeis_a379181.term (N + (r + 1)) : ℝ) := by rw [add_assoc]
  let C : ℝ := 2 * (99 / 10 : ℝ) ^ N
  obtain ⟨r, hr⟩ := exists_nat_gt (198 * C)
  have hlow := hlower r
  have hup : (OMA.S_oeis_a379181.term (N + r) : ℝ) ≤ C * (99 / 10 : ℝ) ^ r := by
    have h := OMA_oeis_a379181.term_le_exp (N + r)
    rw [pow_add] at h
    dsimp only [C]
    linarith
  have hratio : (199 / 198 : ℝ) ^ r ≤ C := by
    have hpos : (0 : ℝ) < (99 / 10 : ℝ) ^ r := by positivity
    have h1 : (995 / 100 : ℝ) ^ r ≤ C * (99 / 10 : ℝ) ^ r := hlow.trans hup
    have h2 : (995 / 100 : ℝ) ^ r = (199 / 198 : ℝ) ^ r * (99 / 10 : ℝ) ^ r := by
      rw [← mul_pow]
      congr 1
      norm_num
    rw [h2] at h1
    exact le_of_mul_le_mul_right h1 hpos
  have hbern := OMA_oeis_a379181.bernoulli_199_198 r
  linarith
