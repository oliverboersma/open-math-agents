import FormalConjectures.OEIS.«17666»

/-!
# Practical denominators and odd multiply-perfect numbers

Coleman's conjecture in OEIS A017666 is equivalent to the nonexistence of an
odd multiply-perfect number greater than one. The two hypotheses separate the
perfect case from larger integer abundancy indices. The proof constructs the
practical component by adjoining prime powers and proves that its complementary
factor must divide its own divisor sum. The classical practical-component
construction is described in Pollack and Thompson, Practical pretenders,
Publ. Math. Debrecen 82 (2013), Section 2.
-/

namespace OMA.R_OeisA17666_conjecture_R1

open OeisA17666 ArithmeticFunction
open scoped ArithmeticFunction.sigma

def H1 : Prop := ∀ b : ℕ, 1 < b → Odd b → σ 1 b ≠ 2 * b

def H2 : Prop := ∀ b k : ℕ, 1 < b → Odd b → 3 ≤ k → σ 1 b ≠ k * b

lemma covered_digit_split {m a b p : ℕ} (hp : 0 < p) (hg : p ≤ a + 1)
    (hm : m ≤ a + p * b) : ∃ x ≤ a, ∃ y ≤ b, m = x + p * y := by
  by_cases h : m / p ≤ b
  · have hr := Nat.mod_lt m hp
    have he := Nat.div_add_mod m p
    exact ⟨m % p, by omega, m / p, h, by omega⟩
  · have hle := Nat.mul_le_mul_left p (show b ≤ m / p by omega)
    have he := Nat.mul_div_le m p
    exact ⟨m - p * b, by omega, b, le_rfl, by omega⟩

lemma covered_union_image (A B : Finset ℕ) {p : ℕ} (hp : 0 < p)
    (hd : Disjoint A (B.image (p * ·))) (hg : p ≤ (∑ a ∈ A, a) + 1)
    (hA : ∀ x, x ≤ ∑ a ∈ A, a → x ∈ subsetSums (A : Set ℕ))
    (hB : ∀ x, x ≤ ∑ b ∈ B, b → x ∈ subsetSums (B : Set ℕ)) :
    ∀ m, m ≤ ∑ d ∈ A ∪ (B.image (p * ·)), d →
      m ∈ subsetSums ((A ∪ (B.image (p * ·)) : Finset ℕ) : Set ℕ) := by
  have hsum (s : Finset ℕ) : (∑ d ∈ s.image (p * ·), d) = p * ∑ i ∈ s, i := by
    rw [Finset.sum_image, Finset.mul_sum]
    intro u hu v hv he
    exact Nat.mul_left_cancel hp he
  intro m hm
  rw [Finset.sum_union hd, hsum] at hm
  obtain ⟨x, hx, y, hy, he⟩ := covered_digit_split hp hg hm
  obtain ⟨s, hs, es⟩ := hA x hx
  obtain ⟨t, ht, et⟩ := hB y hy
  have hs' : s ⊆ A := hs
  have ht' : t.image (p * ·) ⊆ B.image (p * ·) := Finset.image_subset_image ht
  refine ⟨s ∪ t.image (p * ·), ?_, ?_⟩
  · exact Finset.union_subset_union hs' ht'
  · rw [Finset.sum_union (hd.mono hs' ht'), hsum, ← es, ← et]
    exact he

lemma practical_prime_layer {c p : ℕ} (hc : 0 < c) (hp : p.Prime) (e : ℕ) :
    (c * p ^ (e + 1)).divisors =
      c.divisors ∪ ((c * p ^ e).divisors.image (p * ·)) := by
  have hn : c * p ^ (e + 1) ≠ 0 := Nat.mul_ne_zero hc.ne' (pow_ne_zero _ hp.ne_zero)
  have hn' : c * p ^ e ≠ 0 := Nat.mul_ne_zero hc.ne' (pow_ne_zero _ hp.ne_zero)
  have he : c * p ^ (e + 1) = p * (c * p ^ e) := by rw [pow_succ]; ac_rfl
  ext d
  simp only [Finset.mem_union, Nat.mem_divisors, hn, hn', hc.ne', ne_eq,
    not_false_eq_true, and_true, Finset.mem_image]
  constructor
  · intro h
    by_cases hpd : p ∣ d
    · obtain ⟨u, rfl⟩ := hpd
      rw [he] at h
      exact Or.inr ⟨u, Nat.dvd_of_mul_dvd_mul_left hp.pos h, rfl⟩
    · exact Or.inl (((hp.coprime_iff_not_dvd.mpr hpd).symm.pow_right _).dvd_of_dvd_mul_right h)
  · rintro (h | ⟨u, hu, rfl⟩)
    · exact dvd_mul_of_dvd_left h _
    · rw [he]
      exact Nat.mul_dvd_mul_left p hu

lemma cover_mul_prime_pow {c p : ℕ} (hc : 0 < c) (hp : p.Prime) (hcp : c.Coprime p)
    (hgap : p ≤ (∑ d ∈ c.divisors, d) + 1)
    (hcover : ∀ m, m ≤ ∑ d ∈ c.divisors, d → m ∈ subsetSums (c.divisors : Set ℕ))
    (e : ℕ) : ∀ m, m ≤ ∑ d ∈ (c * p ^ e).divisors, d →
      m ∈ subsetSums ((c * p ^ e).divisors : Set ℕ) := by
  induction e with
  | zero => simpa using hcover
  | succ e ih =>
    rw [practical_prime_layer hc hp e]
    apply covered_union_image _ _ hp.pos _ hgap hcover ih
    apply Finset.disjoint_left.mpr
    intro d hd hdp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hdp
    exact (hp.coprime_iff_not_dvd.mp hcp.symm)
      ((dvd_mul_right p t).trans (Nat.mem_divisors.mp hd).1)

theorem whole_le_sigma {c : ℕ} (hc : 0 < c) : c ≤ σ 1 c := by
  rw [ArithmeticFunction.sigma_one_apply]
  exact Finset.single_le_sum (f := fun i : ℕ => i) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors.mpr ⟨dvd_rfl, hc.ne'⟩)

theorem coprime_to_tail {c b t : ℕ} (ht : 0 < t) (hbound : t ≤ σ 1 c + 1)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ b → σ 1 c + 1 < p) : t.Coprime b := by
  by_contra h
  obtain ⟨p, hp, hpt, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact (not_lt_of_ge ((Nat.le_of_dvd ht hpt).trans hbound)) (hrough p hp hpb)

theorem practical_divisor_dvd_prefix {c b d : ℕ} (hc : 0 < c)
    (hd : OeisA5153.A d) (hdiv : d ∣ c * b)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ b → σ 1 c + 1 < p) : d ∣ c := by
  have small (t : ℕ) (ht : 0 < t) (hsize : t ≤ σ 1 c + 1) (htd : t ∣ d) : t ∣ c :=
    (coprime_to_tail ht hsize hrough).dvd_of_dvd_mul_right (htd.trans hdiv)
  by_contra h
  have hsize : σ 1 c + 1 ≤ d := by
    by_contra! hdsmall
    exact h (small d hd.1 (by omega) dvd_rfl)
  obtain ⟨S, hS, hsum⟩ := hd.2 _ hsize
  have hsub : S ⊆ c.divisors := by
    intro x hx
    have hxdiv := Nat.mem_divisors.mp (hS hx)
    have hxle : x ≤ ∑ i ∈ S, i := Finset.single_le_sum (f := fun i : ℕ => i) (fun _ _ => Nat.zero_le _) hx
    exact Nat.mem_divisors.mpr ⟨small x (Nat.pos_of_dvd_of_pos hxdiv.1 hd.1) (hsum ▸ hxle) hxdiv.1, hc.ne'⟩
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun i : ℕ => i) (by intros; omega)
  rw [← ArithmeticFunction.sigma_one_apply] at hle
  omega

theorem odd_obstruction {n c b : ℕ} (hn : 0 < n) (hncb : n = c * b)
    (hb : 1 < b) (hcop : c.Coprime b) (hd : OeisA5153.A (a n))
    (hrough : ∀ p : ℕ, p.Prime → p ∣ b → σ 1 c + 1 < p) : Odd b ∧ b ∣ σ 1 b := by
  have hc : 0 < c := by by_contra! hz; simp_all
  have hsig := whole_le_sigma hc
  have ha : a n = n / n.gcd (σ 1 n) := by simp [a, hn.ne', ArithmeticFunction.sigma_one_apply]
  have hmul : a n * n.gcd (σ 1 n) = n := by rw [ha, Nat.div_mul_cancel (Nat.gcd_dvd_left n _)]
  have hdvd : a n ∣ n := ⟨_, hmul.symm⟩
  have hdc := practical_divisor_dvd_prefix hc hd (hncb ▸ hdvd) hrough
  have hbcop := (Nat.Coprime.coprime_dvd_left hdc hcop).symm
  have hbg : b ∣ n.gcd (σ 1 n) := by
    apply hbcop.dvd_of_dvd_mul_left
    rw [hmul, hncb]
    exact dvd_mul_left _ _
  have hbs := hbg.trans (Nat.gcd_dvd_right n (σ 1 n))
  rw [hncb, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop] at hbs
  have hsbcop := (coprime_to_tail (hc.trans_le hsig) (Nat.le_succ _) hrough).symm
  refine ⟨?_, hsbcop.dvd_of_dvd_mul_left hbs⟩
  apply Nat.not_even_iff_odd.mp
  intro h
  have := hrough 2 Nat.prime_two (even_iff_two_dvd.mp h)
  omega

theorem component_from_cover
    {n : ℕ} (hn : 0 < n) (hnot : ¬ OeisA5153.A n)
    (b c : ℕ) (hcb : n = c * b) (hcop : c.Coprime b)
    (hcover : ∀ m, m ≤ ∑ d ∈ c.divisors, d → m ∈ subsetSums (c.divisors : Set ℕ)) :
    ∃ u v : ℕ, n = u * v ∧ 1 < v ∧ u.Coprime v ∧
      ∀ p : ℕ, p.Prime → p ∣ v → σ 1 u + 1 < p := by
  induction b using Nat.strong_induction_on generalizing c with
  | h b ih =>
    have hc : 0 < c := by by_contra! hz; simp_all
    have hb : 0 < b := by by_contra! hz; simp_all
    have hb1 : b ≠ 1 := by
      rintro rfl
      simp only [mul_one] at hcb
      subst n
      apply hnot
      refine ⟨hc, fun m hm => hcover m (hm.trans ?_)⟩
      simpa only [ArithmeticFunction.sigma_one_apply] using whole_le_sigma hc
    by_cases hr : ∀ p : ℕ, p.Prime → p ∣ b → σ 1 c + 1 < p
    · exact ⟨c, b, hcb, by omega, hcop, hr⟩
    push Not at hr
    obtain ⟨p, hp, hpb, hl⟩ := hr
    obtain ⟨e, t, hpt, hbt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hb.ne' p hp.ne_one
    have he : e ≠ 0 := by rintro rfl; simp_all
    have ht : 0 < t := by by_contra! hz; simp_all
    have hpow : 1 < p ^ e := one_lt_pow₀ hp.one_lt he
    have htb : t < b := by rw [hbt]; simpa using Nat.mul_lt_mul_of_pos_right hpow ht
    have htt : t ∣ b := by rw [hbt]; exact dvd_mul_left _ _
    have hcp := Nat.Coprime.coprime_dvd_right hpb hcop
    have hct := Nat.Coprime.coprime_dvd_right htt hcop
    have hptcop := hp.coprime_iff_not_dvd.mpr hpt
    apply ih t htb (c * p ^ e)
    · rw [hcb, hbt, Nat.mul_assoc]
    · exact hct.mul_left (hptcop.pow_left e)
    · exact cover_mul_prime_pow hc hp hcp (by simpa only [ArithmeticFunction.sigma_one_apply] using hl) hcover e

theorem has_practical_component {n : ℕ} (hn : 0 < n) (hnot : ¬ OeisA5153.A n) :
    ∃ u v : ℕ, n = u * v ∧ 1 < v ∧ u.Coprime v ∧
      ∀ p : ℕ, p.Prime → p ∣ v → σ 1 u + 1 < p := by
  apply component_from_cover hn hnot n 1 (by simp) (by simp)
  intro m hm
  apply OeisA5153.a_1.2 m
  simpa using hm

theorem lt_sigma_one {b : ℕ} (hb : 1 < b) : b < σ 1 b := by
  have h0 : b ≠ 0 := by omega
  have h1 : 1 ≠ b := by omega
  have hsub : ({1, b} : Finset ℕ) ⊆ b.divisors := by
    simp [Finset.insert_subset_iff, Nat.mem_divisors, h0]
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun i : ℕ => i)
    (fun _ _ _ => Nat.zero_le _)
  rw [← ArithmeticFunction.sigma_one_apply] at hle
  simpa [h1, Nat.add_comm] using hle

theorem main : H1 → H2 → type_of% @OeisA17666.conjecture := by
  intro hperfect hmultiple n hn hd
  by_contra h
  obtain ⟨c, b, hcb, hb, hcop, hrough⟩ := has_practical_component hn h
  obtain ⟨ho, k, hσ⟩ := odd_obstruction hn hcb hb hcop hd hrough
  have hs := lt_sigma_one hb
  have hk2 : 2 ≤ k := by
    by_contra! hk
    interval_cases k <;> simp_all
  rcases eq_or_lt_of_le hk2 with he | he
  · exact hperfect b hb ho (by simpa [← he, Nat.mul_comm] using hσ)
  · exact hmultiple b k hb ho he (by simpa [Nat.mul_comm] using hσ)

lemma not_practical_of_odd {b : ℕ} (hb : 1 < b) (ho : Odd b) : ¬ OeisA5153.A b := by
  intro hp
  obtain ⟨S, hS, hsum⟩ := hp.2 2 hb
  have hsub : S ⊆ {1} := by
    intro d hd
    have hdvd := (Nat.mem_divisors.mp (hS hd)).1
    have hpos := Nat.pos_of_dvd_of_pos hdvd (by omega : 0 < b)
    have hle : d ≤ ∑ i ∈ S, i :=
      Finset.single_le_sum (f := fun i : ℕ => i) (fun _ _ => Nat.zero_le _) hd
    have hne : d ≠ 2 := fun e => ho.not_two_dvd_nat (e ▸ hdvd)
    simp only [Finset.mem_singleton]
    omega
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun i : ℕ => i)
    (fun _ _ _ => Nat.zero_le _)
  simp only [Finset.sum_singleton] at hle
  omega

lemma absence_of_conjecture (h : type_of% @OeisA17666.conjecture) :
    ∀ b : ℕ, 1 < b → Odd b → ¬ b ∣ σ 1 b := by
  intro b hb ho hm
  have hbpos : 0 < b := by omega
  have ha : OeisA17666.a b = 1 := by
    simp [OeisA17666.a, hbpos.ne', ← ArithmeticFunction.sigma_one_apply,
      Nat.gcd_eq_left hm, hbpos]
  exact not_practical_of_odd hb ho (h b hbpos (ha ▸ OeisA5153.a_1))

theorem equivalence : (type_of% @OeisA17666.conjecture) ↔ H1 ∧ H2 := by
  constructor
  · intro h
    have ha := absence_of_conjecture h
    constructor
    · intro b hb ho he
      exact ha b hb ho ⟨2, by simpa [Nat.mul_comm] using he⟩
    · intro b k hb ho _ he
      exact ha b hb ho ⟨k, by simpa [Nat.mul_comm] using he⟩
  · rintro ⟨h₁, h₂⟩
    exact main h₁ h₂

end OMA.R_OeisA17666_conjecture_R1
