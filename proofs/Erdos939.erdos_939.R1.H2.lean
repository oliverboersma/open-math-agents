import OMAReductions.R_Erdos939_erdos_939_R1

/-! The construction below is from @ldy985’s accepted submission #928,
formalizing the binomial construction reported by Liam Price. This file
specializes its membership theorem to one prime for each exponent.

Construction: with `X = q ^ r`, `Y = B ^ r` (`B = (2 ^ (r + 1))!`, `q > B` prime),
`(X + Y) ^ r = (X - Y) ^ r + ∑_{j odd} 2 * C(r, j) * X ^ (r - j) * Y ^ j`.
Every summand is `r`-full; some odd terms are split into two pieces to get exactly
`r - 2` summands. Varying `q` gives infinitely many sets. -/

namespace OMA.O12

open Finset

lemma full_of (r u w : ℕ) (hu : u ≠ 0) (hw : 0 < w)
    (h : ∀ p, p.Prime → p ∣ w → p ∣ u) : r.Full (u ^ r * w) := by
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  have hpu : p ∣ u := by
    rcases (Nat.Prime.dvd_mul hp').1 hd with h1 | h1
    · exact hp'.dvd_of_dvd_pow h1
    · exact h p hp' h1
  exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hpu r) w

lemma binom_id (x y : ℤ) (r : ℕ) :
    (x + y) ^ r = (x - y) ^ r + ∑ l ∈ range ((r + 1) / 2),
      2 * (r.choose (2 * l + 1) : ℤ) * x ^ (r - (2 * l + 1)) * y ^ (2 * l + 1) := by
  have h1 : (y + x) ^ r = ∑ m ∈ range (r + 1), y ^ m * x ^ (r - m) * (r.choose m : ℤ) :=
    add_pow y x r
  have h2 : (-y + x) ^ r = ∑ m ∈ range (r + 1), (-y) ^ m * x ^ (r - m) * (r.choose m : ℤ) :=
    add_pow (-y) x r
  have hodd : ∑ m ∈ range (r + 1), (y ^ m * x ^ (r - m) * (r.choose m : ℤ) -
      (-y) ^ m * x ^ (r - m) * (r.choose m : ℤ))
      = ∑ m ∈ (range (r + 1)).filter Odd, 2 * (r.choose m : ℤ) * x ^ (r - m) * y ^ m := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    split_ifs with hm
    · rw [hm.neg_pow]; ring
    · rw [(Nat.not_odd_iff_even.mp hm).neg_pow]; ring
  have himg : (range (r + 1)).filter Odd = (range ((r + 1) / 2)).image (fun l => 2 * l + 1) := by
    ext m
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hm, l, rfl⟩
      exact ⟨l, by omega, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨by omega, ⟨l, rfl⟩⟩
  have key : ∑ m ∈ range (r + 1), (y ^ m * x ^ (r - m) * (r.choose m : ℤ) -
      (-y) ^ m * x ^ (r - m) * (r.choose m : ℤ)) = ∑ l ∈ range ((r + 1) / 2),
      2 * (r.choose (2 * l + 1) : ℤ) * x ^ (r - (2 * l + 1)) * y ^ (2 * l + 1) := by
    rw [hodd, himg, Finset.sum_image (fun a _ b _ hab => by omega)]
  rw [← key, Finset.sum_sub_distrib, ← h1, ← h2]
  ring

/-- the common factor of the pieces with odd index `2 * l + 1` -/
def Z (r q B l : ℕ) : ℕ := (q ^ (r - (2 * l + 1)) * B ^ (2 * l + 1)) ^ r

/-- coefficient of the main piece -/
def c0 (r k l : ℕ) : ℕ := 2 * r.choose (2 * l + 1) - (if l < k then 1 else 0)

def val (r q B k : ℕ) (x : ℕ × ℕ) : ℕ := (if x.2 = 0 then c0 r k x.1 else 1) * Z r q B x.1

def Idx (h k : ℕ) : Finset (ℕ × ℕ) := (range h ×ˢ {0}) ∪ (range k ×ˢ {1})

def Sset (r q B h k : ℕ) : Finset ℕ :=
  insert ((q ^ r - B ^ r) ^ r) ((Idx h k).image (val r q B k))

lemma mem_Idx {h k : ℕ} {x : ℕ × ℕ} : x ∈ Idx h k ↔ (x.1 < h ∧ x.2 = 0) ∨ (x.1 < k ∧ x.2 = 1) := by
  unfold Idx
  simp only [mem_union, mem_product, mem_range, mem_singleton]

lemma choose_two_le {r j : ℕ} (h1 : 1 ≤ j) (h2 : j < r) : 2 ≤ r.choose j := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [Nat.choose_succ_succ']
  have := Nat.choose_pos (show j' ≤ r' by omega)
  have := Nat.choose_pos (show j' + 1 ≤ r' by omega)
  omega

theorem main (r : ℕ) (hr : 6 ≤ r) (q : ℕ) (hq : q.Prime) (hqB : (2 ^ (r + 1)).factorial < q) :
    Sset r q (2 ^ (r + 1)).factorial ((r + 1) / 2) (r - 3 - (r + 1) / 2) ∈
      Erdos939.Erdos939Sums r ∧
    ∑ s ∈ Sset r q (2 ^ (r + 1)).factorial ((r + 1) / 2) (r - 3 - (r + 1) / 2), s
      = (q ^ r + ((2 ^ (r + 1)).factorial) ^ r) ^ r := by
  set B := (2 ^ (r + 1)).factorial with hBdef
  set h := (r + 1) / 2 with hh
  set k := r - 3 - (r + 1) / 2 with hk
  have := Fact.mk hq
  have hB : 0 < B := Nat.factorial_pos _
  have hNB : 2 ^ (r + 1) ≤ B := Nat.self_le_factorial _
  have hq0 : 0 < q := hq.pos
  have hqndB : ¬ q ∣ B := Nat.not_dvd_of_pos_of_lt hB hqB
  have hr0 : r ≠ 0 := by omega
  have hle : B ^ r < q ^ r := Nat.pow_lt_pow_left hqB hr0
  -- primes of small coefficients divide B
  have hsmall : ∀ c, 0 < c → c ≤ 2 ^ (r + 1) → ∀ p, p.Prime → p ∣ c → p ∣ B := by
    intro c hc hcle p hp hpc
    exact Nat.dvd_factorial hp.pos (le_trans (Nat.le_of_dvd hc hpc) hcle)
  -- coefficients
  have hcoef : ∀ x ∈ Idx h k, 0 < (if x.2 = 0 then c0 r k x.1 else 1) ∧
      (if x.2 = 0 then c0 r k x.1 else 1) ≤ 2 ^ (r + 1) := by
    intro x hx
    rw [mem_Idx] at hx
    have hC1 := Nat.choose_pos (show 2 * x.1 + 1 ≤ r by omega)
    have hC2 := Nat.choose_le_two_pow r (2 * x.1 + 1)
    have h2 : 2 * 2 ^ r = 2 ^ (r + 1) := by ring
    split_ifs with he
    · unfold c0
      split_ifs <;> omega
    · constructor
      · omega
      · exact Nat.one_le_two_pow
  -- the key coprimality fact
  have hcop : ∀ p, p.Prime → p ∣ q ^ r - B ^ r → p ∣ q * B → False := by
    intro p hp hp1 hp2
    have hpq : p ∣ q := by
      rcases (Nat.Prime.dvd_mul hp).1 hp2 with h3 | h3
      · exact h3
      · have : p ∣ q ^ r - B ^ r + B ^ r := dvd_add hp1 (dvd_pow h3 hr0)
        rw [Nat.sub_add_cancel hle.le] at this
        exact hp.dvd_of_dvd_pow this
    have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
    rw [hpq'] at hp1
    have : q ∣ q ^ r - B ^ r + B ^ r := by rw [Nat.sub_add_cancel hle.le]; exact dvd_pow_self q hr0
    have hB' : q ∣ B ^ r := (Nat.dvd_add_right hp1).mp this
    exact hqndB (hq.dvd_of_dvd_pow hB')
  -- valuation
  have hZpos : ∀ l, 0 < Z r q B l := fun l => by
    unfold Z; exact pow_pos (mul_pos (pow_pos hq0 _) (pow_pos hB _)) _
  have hval : ∀ x ∈ Idx h k, padicValNat q (val r q B k x) = r * (r - (2 * x.1 + 1)) := by
    intro x hx
    obtain ⟨hc1, hc2⟩ := hcoef x hx
    have hqc : ¬ q ∣ (if x.2 = 0 then c0 r k x.1 else 1) :=
      Nat.not_dvd_of_pos_of_lt hc1 (lt_of_le_of_lt hc2 (lt_of_le_of_lt hNB hqB))
    unfold val Z
    rw [padicValNat.mul hc1.ne' (pow_pos (mul_pos (pow_pos hq0 _) (pow_pos hB _)) _).ne',
      padicValNat.pow, padicValNat.mul (pow_pos hq0 _).ne' (pow_pos hB _).ne',
      padicValNat.prime_pow, padicValNat.pow, padicValNat.eq_zero_of_not_dvd hqc,
      padicValNat.eq_zero_of_not_dvd hqndB]
    ring
  have hinj : Set.InjOn (val r q B k) (Idx h k) := by
    rintro ⟨x1, x2⟩ hx ⟨y1, y2⟩ hy hxy
    have hv := hval _ hx
    rw [hxy, hval _ hy] at hv
    have hx' := mem_Idx.mp hx
    have hy' := mem_Idx.mp hy
    simp only at hv hx' hy'
    have h1 : r - (2 * y1 + 1) = r - (2 * x1 + 1) := Nat.eq_of_mul_eq_mul_left (by omega) hv
    have h1' : x1 = y1 := by omega
    subst h1'
    have hZ := hZpos x1
    simp only [val] at hxy
    have hc := Nat.eq_of_mul_eq_mul_right hZ hxy
    rcases hx' with ⟨_, rfl⟩ | ⟨hl, rfl⟩ <;> rcases hy' with ⟨_, rfl⟩ | ⟨hl', rfl⟩
    · rfl
    · have hC := choose_two_le (r := r) (j := 2 * x1 + 1) (by omega) (by omega)
      simp only [c0, if_pos hl', Nat.one_ne_zero, ↓reduceIte] at hc
      omega
    · have hC := choose_two_le (r := r) (j := 2 * x1 + 1) (by omega) (by omega)
      simp only [c0, if_pos hl, Nat.one_ne_zero, ↓reduceIte] at hc
      omega
    · rfl
  have hmemB : ∀ x ∈ Idx h k, B ∣ val r q B k x := by
    intro x hx
    unfold val Z
    apply Dvd.dvd.mul_left
    apply dvd_pow _ hr0
    exact Dvd.dvd.mul_left (dvd_pow_self B (by omega)) _
  have hB2 : 2 ≤ B := le_trans (by
    have : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    rw [pow_succ]; omega) hNB
  have hnot : (q ^ r - B ^ r) ^ r ∉ (Idx h k).image (val r q B k) := by
    intro hmem
    obtain ⟨x, hx, hxv⟩ := mem_image.mp hmem
    obtain ⟨p, hp, hpB⟩ := Nat.exists_prime_and_dvd (show B ≠ 1 by omega)
    have : p ∣ (q ^ r - B ^ r) ^ r := hxv ▸ dvd_trans hpB (hmemB x hx)
    exact hcop p hp (hp.dvd_of_dvd_pow this) (Dvd.dvd.mul_left hpB q)
  -- the sum
  have hsum : ∑ s ∈ Sset r q B h k, s = (q ^ r + B ^ r) ^ r := by
    unfold Sset
    rw [sum_insert hnot, sum_image hinj]
    have hdisj : Disjoint (range h ×ˢ ({0} : Finset ℕ)) (range k ×ˢ ({1} : Finset ℕ)) := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      simp only [mem_product, mem_range, mem_singleton] at h1 h2
      omega
    unfold Idx
    rw [sum_union hdisj, sum_product, sum_product]
    simp only [sum_singleton, val, if_true, one_ne_zero, if_false, one_mul]
    have hfilt : ∑ l ∈ range k, Z r q B l = ∑ l ∈ range h, (if l < k then Z r q B l else 0) := by
      rw [← Finset.sum_filter]
      congr 1
      ext l
      simp only [mem_filter, mem_range]
      omega
    rw [hfilt, ← sum_add_distrib]
    have hterm : ∀ l ∈ range h, c0 r k l * Z r q B l + (if l < k then Z r q B l else 0)
        = 2 * r.choose (2 * l + 1) * Z r q B l := by
      intro l hl
      rw [mem_range] at hl
      have hC1 := Nat.choose_pos (show 2 * l + 1 ≤ r by omega)
      unfold c0
      split_ifs with hlk
      · have e : 2 * r.choose (2 * l + 1) - 1 + 1 = 2 * r.choose (2 * l + 1) := by omega
        calc (2 * r.choose (2 * l + 1) - 1) * Z r q B l + Z r q B l
            = (2 * r.choose (2 * l + 1) - 1 + 1) * Z r q B l := by ring
          _ = _ := by rw [e]
      · simp
    rw [sum_congr rfl hterm]
    have hZ : ∀ l, Z r q B l = (q ^ r) ^ (r - (2 * l + 1)) * (B ^ r) ^ (2 * l + 1) := by
      intro l; unfold Z; ring
    simp only [hZ]
    have key := binom_id ((q : ℤ) ^ r) ((B : ℤ) ^ r) r
    zify [hle.le]
    rw [key, ← hh]
    congr 1
    apply sum_congr rfl
    intro l _
    ring
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hsum⟩
  · -- card
    unfold Sset
    rw [card_insert_of_notMem hnot, card_image_of_injOn hinj]
    have hdisj : Disjoint (range h ×ˢ ({0} : Finset ℕ)) (range k ×ˢ ({1} : Finset ℕ)) := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      simp only [mem_product, mem_range, mem_singleton] at h1 h2
      omega
    unfold Idx
    rw [card_union_of_disjoint hdisj, card_product, card_product, card_range, card_range,
      card_singleton, card_singleton]
    omega
  · -- coprime
    show (Sset r q B h k).gcd id = 1
    have h00 : ((0 : ℕ), (0 : ℕ)) ∈ Idx h k := mem_Idx.mpr (Or.inl ⟨by omega, rfl⟩)
    have hg1 : (Sset r q B h k).gcd id ∣ (q ^ r - B ^ r) ^ r :=
      Finset.gcd_dvd (mem_insert_self _ _)
    have hg2 : (Sset r q B h k).gcd id ∣ val r q B k (0, 0) :=
      Finset.gcd_dvd (mem_insert_of_mem (mem_image_of_mem _ h00))
    have hcp : Nat.Coprime ((q ^ r - B ^ r) ^ r) (val r q B k (0, 0)) := by
      apply Nat.coprime_of_dvd
      intro p hp hp1 hp2
      have hp1' := hp.dvd_of_dvd_pow hp1
      obtain ⟨hc1, hc2⟩ := hcoef (0, 0) h00
      unfold val Z at hp2
      rcases (Nat.Prime.dvd_mul hp).1 hp2 with h3 | h3
      · exact hcop p hp hp1' (Dvd.dvd.mul_left (hsmall _ hc1 hc2 p hp h3) q)
      · have h4 := hp.dvd_of_dvd_pow h3
        rcases (Nat.Prime.dvd_mul hp).1 h4 with h5 | h5
        · exact hcop p hp hp1' (Dvd.dvd.mul_right (hp.dvd_of_dvd_pow h5) B)
        · exact hcop p hp hp1' (Dvd.dvd.mul_left (hp.dvd_of_dvd_pow h5) q)
    have := Nat.dvd_gcd hg1 hg2
    rw [hcp] at this
    exact Nat.dvd_one.mp this
  · -- the sum is full
    rw [hsum, ← mul_one ((q ^ r + B ^ r) ^ r)]
    apply full_of r _ 1 (by positivity) one_pos
    intro p hp hp1
    exact absurd (Nat.le_of_dvd one_pos hp1) (by have := hp.two_le; omega)
  · intro s hs
    unfold Sset at hs
    rcases mem_insert.mp hs with rfl | hs
    · refine ⟨pow_pos (Nat.sub_pos_of_lt hle) _, ?_⟩
      rw [← mul_one ((q ^ r - B ^ r) ^ r)]
      apply full_of r _ 1 (Nat.sub_pos_of_lt hle).ne' one_pos
      intro p hp hp1
      exact absurd (Nat.le_of_dvd one_pos hp1) (by have := hp.two_le; omega)
    · obtain ⟨x, hx, rfl⟩ := mem_image.mp hs
      obtain ⟨hc1, hc2⟩ := hcoef x hx
      have hx' := mem_Idx.mp hx
      refine ⟨Nat.mul_pos hc1 (hZpos _), ?_⟩
      rw [show val r q B k x = (q ^ (r - (2 * x.1 + 1)) * B ^ (2 * x.1 + 1)) ^ r *
          (if x.2 = 0 then c0 r k x.1 else 1) from by unfold val Z; ring]
      refine full_of r (q ^ (r - (2 * x.1 + 1)) * B ^ (2 * x.1 + 1))
        (if x.2 = 0 then c0 r k x.1 else 1)
        (mul_pos (pow_pos hq0 _) (pow_pos hB _)).ne' hc1 ?_
      intro p hp hpc
      exact Dvd.dvd.mul_left (dvd_pow (hsmall _ hc1 hc2 p hp hpc) (by omega)) _

end OMA.O12

theorem OMA.solution : OMA.R_Erdos939_erdos_939_R1.H2 := by
  intro r hr
  obtain ⟨q, hqgt, hq⟩ := Nat.exists_infinite_primes ((2 ^ (r + 1)).factorial + 1)
  exact ⟨_, (OMA.O12.main r hr q hq (by omega)).1⟩
