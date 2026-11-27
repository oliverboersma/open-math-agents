import OMAStatements.S_oeis_a342992

/-!
A342992: every `n ≥ 1` not divisible by 5 has a positive multiple whose decimal digits are all
prime. The multiple built here only uses the digits 2 and 3.

Write `n = 2 ^ a * u` with `u` odd, so `u` is coprime to 10.
* `two_pow_block`: by induction on `a` there is a block of `a` digits 2/3 whose value is divisible
  by `2 ^ a` (prepend 2 or 3 according to the parity of the current quotient).
* `odd_part`: with `e = φ(u)` we have `10 ^ e = 1` in `ZMod u`. The blocks `M2 = 2 2 ... 2` and
  `M3 = 2 ... 2 3` of length `e` differ by 1, so `i` copies of `M3` followed by `u - i` copies of
  `M2` have value `i` modulo `u`. Choosing `i` suitably makes `B + 10 ^ a * value` divisible by `u`.
The concatenation is divisible by `2 ^ a` and by `u`, hence by `n`, and `Nat.digits_ofDigits`
identifies its digits.
-/

namespace OMA.A342992Proof

/-- `j` copies of the block `M`, concatenated. -/
def rep (M : List ℕ) : ℕ → List ℕ
  | 0 => []
  | j + 1 => M ++ rep M j

lemma rep_mem (M : List ℕ) (hM : ∀ d ∈ M, d = 2 ∨ d = 3) :
    ∀ j, ∀ d ∈ rep M j, d = 2 ∨ d = 3 := by
  intro j
  induction j with
  | zero =>
    intro d hd
    simp [rep] at hd
  | succ j ih =>
    intro d hd
    rw [rep, List.mem_append] at hd
    rcases hd with hd | hd
    · exact hM d hd
    · exact ih d hd

lemma rep_length (M : List ℕ) : ∀ j, (rep M j).length = j * M.length := by
  intro j
  induction j with
  | zero => simp [rep]
  | succ j ih =>
    rw [rep, List.length_append, ih]
    ring

lemma rep_val (u : ℕ) (M : List ℕ) (hM : (10 : ZMod u) ^ M.length = 1) :
    ∀ j, ((Nat.ofDigits 10 (rep M j) : ℕ) : ZMod u) =
      (j : ZMod u) * ((Nat.ofDigits 10 M : ℕ) : ZMod u) := by
  intro j
  induction j with
  | zero => simp [rep]
  | succ j ih =>
    have h10 : ((10 : ℕ) : ZMod u) = 10 := by norm_num
    have hj : ((j + 1 : ℕ) : ZMod u) = (j : ZMod u) + 1 := by push_cast; ring
    rw [hj, rep, Nat.ofDigits_append, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, ih, h10, hM]
    ring

/-- A block of `a` digits `2`/`3` whose value is divisible by `2 ^ a`. -/
lemma two_pow_block : ∀ a : ℕ, ∃ L : List ℕ, L.length = a ∧ (∀ d ∈ L, d = 2 ∨ d = 3) ∧
    2 ^ a ∣ Nat.ofDigits 10 L := by
  intro a
  induction a with
  | zero => exact ⟨[], rfl, by simp, by simp⟩
  | succ a ih =>
    obtain ⟨L, hlen, hdig, t, ht⟩ := ih
    have h5 : Odd (5 ^ a) := Odd.pow ⟨2, rfl⟩
    obtain ⟨q, hq⟩ := h5
    rcases Nat.even_or_odd t with ⟨s, hs⟩ | ⟨s, hs⟩
    · refine ⟨L ++ [2], by simp [hlen], ?_, ?_⟩
      · intro d hd
        rw [List.mem_append, List.mem_singleton] at hd
        rcases hd with hd | hd
        · exact hdig d hd
        · exact Or.inl hd
      · refine ⟨s + 5 ^ a, ?_⟩
        rw [Nat.ofDigits_append, Nat.ofDigits_singleton, hlen, ht, hs,
          show (10 : ℕ) = 2 * 5 from rfl, Nat.mul_pow]
        ring
    · refine ⟨L ++ [3], by simp [hlen], ?_, ?_⟩
      · intro d hd
        rw [List.mem_append, List.mem_singleton] at hd
        rcases hd with hd | hd
        · exact hdig d hd
        · exact Or.inr hd
      · refine ⟨s + 3 * q + 2, ?_⟩
        rw [Nat.ofDigits_append, Nat.ofDigits_singleton, hlen, ht, hs,
          show (10 : ℕ) = 2 * 5 from rfl, Nat.mul_pow, hq]
        ring

/-- For `u` coprime to 10 and any `B`, `a`, some nonempty block `X` of digits `2`/`3`
satisfies `u ∣ B + 10 ^ a * ofDigits X`. -/
lemma odd_part (u a B : ℕ) (hupos : 0 < u) (hc10 : Nat.Coprime 10 u) :
    ∃ X : List ℕ, X ≠ [] ∧ (∀ d ∈ X, d = 2 ∨ d = 3) ∧
      ((B + 10 ^ a * Nat.ofDigits 10 X : ℕ) : ZMod u) = 0 := by
  have hne : NeZero u := ⟨by omega⟩
  obtain ⟨e', he'⟩ : ∃ e', Nat.totient u = e' + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.totient_pos.mpr hupos).ne'
  have hten : ((10 : ℕ) : ZMod u) = 10 := by norm_num
  have h10 : (10 : ZMod u) ^ (e' + 1) = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff (10 ^ Nat.totient u) 1 u).mpr
      (Nat.ModEq.pow_totient hc10)
    rw [he', Nat.cast_pow, hten, Nat.cast_one] at h
    exact h
  obtain ⟨M2, hM2⟩ : ∃ M2 : List ℕ, M2 = 2 :: List.replicate e' 2 := ⟨_, rfl⟩
  obtain ⟨M3, hM3⟩ : ∃ M3 : List ℕ, M3 = 3 :: List.replicate e' 2 := ⟨_, rfl⟩
  have hM2len : M2.length = e' + 1 := by rw [hM2]; simp
  have hM3len : M3.length = e' + 1 := by rw [hM3]; simp
  have hM2dig : ∀ d ∈ M2, d = 2 ∨ d = 3 := by
    intro d hd
    rw [hM2, List.mem_cons] at hd
    rcases hd with hd | hd
    · exact Or.inl hd
    · exact Or.inl (List.eq_of_mem_replicate hd)
  have hM3dig : ∀ d ∈ M3, d = 2 ∨ d = 3 := by
    intro d hd
    rw [hM3, List.mem_cons] at hd
    rcases hd with hd | hd
    · exact Or.inr hd
    · exact Or.inl (List.eq_of_mem_replicate hd)
  have hv : Nat.ofDigits 10 M3 = Nat.ofDigits 10 M2 + 1 := by
    rw [hM2, hM3, Nat.ofDigits_cons, Nat.ofDigits_cons]
    ring
  have hM2pow : (10 : ZMod u) ^ M2.length = 1 := by rw [hM2len]; exact h10
  have hM3pow : (10 : ZMod u) ^ M3.length = 1 := by rw [hM3len]; exact h10
  have hc10a : Nat.Coprime (10 ^ a) u := Nat.Coprime.pow_left a hc10
  have hinv := ZMod.coe_mul_inv_eq_one (10 ^ a) hc10a
  obtain ⟨z, hz⟩ : ∃ z : ZMod u, z = -(B : ZMod u) * ((10 ^ a : ℕ) : ZMod u)⁻¹ := ⟨_, rfl⟩
  have hzi : ((z.val : ℕ) : ZMod u) = z := ZMod.natCast_zmod_val z
  have hilt : z.val < u := ZMod.val_lt z
  obtain ⟨k, hk⟩ : ∃ k, u - z.val = k + 1 := ⟨u - z.val - 1, by omega⟩
  have e1 := rep_val u M3 hM3pow z.val
  have e2 := rep_val u M2 hM2pow (u - z.val)
  have e3 : ((10 : ℕ) : ZMod u) ^ (rep M3 z.val).length = 1 := by
    rw [rep_length, hM3len, pow_mul', hten, h10, one_pow]
  have e4 : ((u - z.val : ℕ) : ZMod u) = -(z.val : ZMod u) := by
    rw [Nat.cast_sub hilt.le, ZMod.natCast_self, zero_sub]
  have e5 : ((Nat.ofDigits 10 M3 : ℕ) : ZMod u) = ((Nat.ofDigits 10 M2 : ℕ) : ZMod u) + 1 := by
    rw [hv, Nat.cast_add, Nat.cast_one]
  have hX : ((Nat.ofDigits 10 (rep M3 z.val ++ rep M2 (u - z.val)) : ℕ) : ZMod u) = z := by
    rw [Nat.ofDigits_append, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, e1, e2, e3, e4, e5]
    linear_combination hzi
  refine ⟨rep M3 z.val ++ rep M2 (u - z.val), ?_, ?_, ?_⟩
  · rw [hk, rep, hM2]
    simp
  · intro d hd
    rw [List.mem_append] at hd
    rcases hd with hd | hd
    · exact rep_mem M3 hM3dig _ d hd
    · exact rep_mem M2 hM2dig _ d hd
  · rw [Nat.cast_add, Nat.cast_mul, hX, hz]
    linear_combination (-(B : ZMod u)) * hinv

end OMA.A342992Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a342992.main := by
  intro n hn h5
  obtain ⟨a, u, hodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
  have hupos : 0 < u := hodd.pos
  have h5u : ¬ 5 ∣ u := fun h => h5 (Dvd.dvd.mul_left h _)
  have hc2 : Nat.Coprime 2 u :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd.not_two_dvd_nat
  have hc5 : Nat.Coprime 5 u := (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h5u
  have hc10 : Nat.Coprime 10 u := Nat.Coprime.mul_left hc2 hc5
  obtain ⟨L0, hlen0, hdig0, hdvd0⟩ := OMA.A342992Proof.two_pow_block a
  obtain ⟨X, hXne, hXdig, hXval⟩ :=
    OMA.A342992Proof.odd_part u a (Nat.ofDigits 10 L0) hupos hc10
  have hval : Nat.ofDigits 10 (L0 ++ X) = Nat.ofDigits 10 L0 + 10 ^ a * Nat.ofDigits 10 X := by
    rw [Nat.ofDigits_append, hlen0]
  have hu : u ∣ Nat.ofDigits 10 (L0 ++ X) := by
    rw [hval]
    exact (ZMod.natCast_eq_zero_iff _ u).mp hXval
  have h2 : 2 ^ a ∣ Nat.ofDigits 10 (L0 ++ X) := by
    rw [hval]
    exact dvd_add hdvd0 (Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (by norm_num) a) _)
  have hn_dvd : 2 ^ a * u ∣ Nat.ofDigits 10 (L0 ++ X) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow_left a hc2) h2 hu
  have hLdig : ∀ d ∈ L0 ++ X, d = 2 ∨ d = 3 := by
    intro d hd
    rw [List.mem_append] at hd
    rcases hd with hd | hd
    · exact hdig0 d hd
    · exact hXdig d hd
  have hLne : L0 ++ X ≠ [] := by
    intro h
    exact hXne (List.append_eq_nil_iff.mp h).2
  have hdigits : Nat.digits 10 (Nat.ofDigits 10 (L0 ++ X)) = L0 ++ X := by
    refine Nat.digits_ofDigits 10 (by norm_num) _ ?_ ?_
    · intro l hl
      rcases hLdig l hl with rfl | rfl <;> norm_num
    · intro hne
      have h := hLdig _ (List.getLast_mem hne)
      omega
  have hvalpos : 0 < Nat.ofDigits 10 (L0 ++ X) := by
    rcases Nat.eq_zero_or_pos (Nat.ofDigits 10 (L0 ++ X)) with h0 | h0
    · rw [h0, Nat.digits_zero] at hdigits
      exact absurd hdigits.symm hLne
    · exact h0
  refine ⟨Nat.ofDigits 10 (L0 ++ X) / (2 ^ a * u), ?_, ?_⟩
  · exact Nat.div_pos (Nat.le_of_dvd hvalpos hn_dvd) (Nat.pos_of_ne_zero (by omega))
  · rw [Nat.div_mul_cancel hn_dvd]
    intro d hd
    rw [hdigits] at hd
    rcases hLdig d hd with rfl | rfl <;> decide
