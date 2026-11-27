import OMAStatements.S_oeis_a111108

theorem OMA_A (n : ℕ) : OMA.S_oeis_a111108.A001333 n = ((1 + Zsqrtd.sqrtd : Zsqrtd 2) ^ n).re := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [OMA.S_oeis_a111108.A001333]
    | 1, _ => simp [OMA.S_oeis_a111108.A001333]
    | k + 2, ih =>
      have h1 := ih (k + 1) (by omega)
      have h0 := ih k (by omega)
      have hz : (1 + Zsqrtd.sqrtd : Zsqrtd 2) ^ (k + 2) = 2 * (1 + Zsqrtd.sqrtd) ^ (k + 1) + (1 + Zsqrtd.sqrtd) ^ k := by
        have : (1 + Zsqrtd.sqrtd : Zsqrtd 2) ^ 2 = 2 * (1 + Zsqrtd.sqrtd) + 1 := by
          ext <;> simp [pow_two]
        calc (1 + Zsqrtd.sqrtd : Zsqrtd 2) ^ (k + 2) = (1 + Zsqrtd.sqrtd) ^ k * (1 + Zsqrtd.sqrtd) ^ 2 := by ring
          _ = _ := by rw [this]; ring
      rw [hz]
      simp [OMA.S_oeis_a111108.A001333, h1, h0]

theorem OMA_im (m : ℕ) : ((2:Zsqrtd 2)^m).im = 0 := by
  induction m with
  | zero => simp
  | succ k ihk => simp [pow_succ, ihk]

theorem OMA.solution : type_of% @OMA.S_oeis_a111108.main := by
  intro p hp h2
  have hodd : Odd p := hp.odd_of_ne_two h2
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (1 : Zsqrtd 2) Zsqrtd.sqrtd
  have hre0 : ((Zsqrtd.sqrtd : Zsqrtd 2) ^ p).re = 0 := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm, pow_succ, pow_mul]
    have : (Zsqrtd.sqrtd : Zsqrtd 2) ^ 2 = 2 := by ext <;> simp [pow_two]
    have h2m : ((2:Zsqrtd 2)^m).im = 0 := OMA_im m
    rw [this]
    simp [h2m]
  have hA : OMA.S_oeis_a111108.A001333 p = 1 + p * (2 * r.im) := by
    rw [OMA_A, hr]
    simp [hre0]
    ring
  have hf : ((-2 : ℤ)) ^ (p - 1) ≡ 1 [ZMOD p] :=
    Int.ModEq.pow_card_sub_one_eq_one hp (by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm h2)
      simpa [Int.gcd, Nat.Coprime] using this)
  have hd : (p : ℤ) ∣ (-2 : ℤ) ^ (p - 1) - 1 := (Int.modEq_iff_dvd.mp hf.symm)
  unfold OMA.S_oeis_a111108.a
  rw [hA]
  obtain ⟨c, hc⟩ := hd
  exact ⟨2 * r.im - c, by linarith⟩
