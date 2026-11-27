import OMAStatements.S_mo_187311
import Mathlib

open Polynomial

namespace OMA.P187311

lemma natDegree_sq_add_sq (f g : ℤ[X]) (h : (f ^ 2 + g ^ 2).natDegree = 0) :
    f.natDegree = 0 ∧ g.natDegree = 0 := by
  by_contra hc
  have hf : f.natDegree ≤ max f.natDegree g.natDegree := le_max_left _ _
  have hg : g.natDegree ≤ max f.natDegree g.natDegree := le_max_right _ _
  have hdpos : 0 < max f.natDegree g.natDegree := by
    rcases Nat.eq_zero_or_pos (max f.natDegree g.natDegree) with h0 | h0
    · exfalso
      apply hc
      constructor <;> omega
    · exact h0
  have c1 : (f ^ 2 + g ^ 2).coeff (max f.natDegree g.natDegree + max f.natDegree g.natDegree)
      = f.coeff (max f.natDegree g.natDegree) ^ 2 + g.coeff (max f.natDegree g.natDegree) ^ 2 := by
    rw [coeff_add, pow_two, pow_two, coeff_mul_add_eq_of_natDegree_le hf hf,
      coeff_mul_add_eq_of_natDegree_le hg hg]
    ring
  have c2 : (f ^ 2 + g ^ 2).coeff (max f.natDegree g.natDegree + max f.natDegree g.natDegree)
      = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [c1] at c2
  have hf0 : f.coeff (max f.natDegree g.natDegree) = 0 := by
    nlinarith [sq_nonneg (f.coeff (max f.natDegree g.natDegree)),
      sq_nonneg (g.coeff (max f.natDegree g.natDegree))]
  have hg0 : g.coeff (max f.natDegree g.natDegree) = 0 := by
    nlinarith [sq_nonneg (f.coeff (max f.natDegree g.natDegree)),
      sq_nonneg (g.coeff (max f.natDegree g.natDegree))]
  rcases max_cases f.natDegree g.natDegree with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [h1] at hf0 hdpos
    have hz : f = 0 := leadingCoeff_eq_zero.mp hf0
    rw [hz] at hdpos
    simp at hdpos
  · rw [h1] at hg0 hdpos
    have hz : g = 0 := leadingCoeff_eq_zero.mp hg0
    rw [hz] at hdpos
    simp at hdpos

lemma sharp_key (a₁ a₂ a₃ a₄ m n r s : ℤ[X])
    (h1 : a₁ - a₃ = m * n) (h2 : a₁ + a₃ = r * s) (h3 : a₄ - a₂ = m * r) (h4 : a₄ + a₂ = n * s)
    (hm : m ≠ 0) (hs : s ≠ 0) (hprim : 0 < (a₁ ^ 2 + a₂ ^ 2).content ∧ (a₁ ^ 2 + a₂ ^ 2).content < 5)
    (hdeg : (m ^ 2 + s ^ 2).natDegree = 0) : a₁ = a₄ ∨ a₁ = -a₄ := by
  obtain ⟨hmd, hsd⟩ := natDegree_sq_add_sq m s hdeg
  obtain ⟨m0, rfl⟩ : ∃ m0, m = C m0 := ⟨_, eq_C_of_natDegree_eq_zero hmd⟩
  obtain ⟨s0, rfl⟩ : ∃ s0, s = C s0 := ⟨_, eq_C_of_natDegree_eq_zero hsd⟩
  have hm0 : m0 ≠ 0 := fun h => hm (by rw [h, C_0])
  have hs0 : s0 ≠ 0 := fun h => hs (by rw [h, C_0])
  have hid : C (4 : ℤ) * (a₁ ^ 2 + a₂ ^ 2) = C (m0 ^ 2 + s0 ^ 2) * (n ^ 2 + r ^ 2) := by
    have e4 : (C (4 : ℤ) : ℤ[X]) = 4 := by simp
    rw [e4, C_add, C_pow, C_pow]
    linear_combination (2 * a₁ + C m0 * n + r * C s0) * (h1 + h2)
      + (2 * a₂ + n * C s0 - C m0 * r) * (h4 - h3)
  have hc := congrArg content hid
  rw [content_C_mul, content_C_mul, show normalize (4 : ℤ) = 4 by decide] at hc
  let c := (a₁ ^ 2 + a₂ ^ 2).content
  have hd : (m0^2 + s0^2) ∣ 4*c := normalize_dvd_iff.mp (Dvd.intro _ hc.symm)
  have hpos : 0 < c := hprim.1
  have hlt : c < 5 := hprim.2
  have hb := Int.le_of_dvd (show 0 < 4*c by omega) hd
  have bm : -3 ≤ m0 ∧ m0 ≤ 3 := by
    constructor <;> by_contra! h <;> nlinarith [show 0 < s0^2 by positivity]
  have bs : -3 ≤ s0 ∧ s0 ≤ 3 := by
    constructor <;> by_contra! h <;> nlinarith [show 0 < m0^2 by positivity]
  have he : m0 = s0 ∨ m0 = -s0 := by
    clear_value c
    obtain ⟨_,_⟩ := bm
    obtain ⟨_,_⟩ := bs
    interval_cases m0 <;> interval_cases s0 <;> first | contradiction | (norm_num; done) | (norm_num at hd; omega)
  have two : (2 : ℤ[X]) ≠ 0 := two_ne_zero
  rcases he with h | h
  · rw [h] at h1 h3
    left
    have hz : (2 : ℤ[X]) * (a₁ - a₄) = 0 := by linear_combination h1 + h2 - h3 - h4
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left two)
  · rw [h, map_neg] at h1 h3
    right
    have hz : (2 : ℤ[X]) * (a₁ + a₄) = 0 := by linear_combination h1 + h2 + h3 + h4
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hz).resolve_left two)

end OMA.P187311

open OMA.P187311 in
theorem OMA.content_at_least_five :
    ∀ a₁ a₂ a₃ a₄ : ℤ[X],
      a₁ ≠ a₂ → a₁ ≠ -a₂ → a₁ ≠ a₃ → a₁ ≠ -a₃ → a₁ ≠ a₄ → a₁ ≠ -a₄ →
      a₂ ≠ a₃ → a₂ ≠ -a₃ → a₂ ≠ a₄ → a₂ ≠ -a₄ → a₃ ≠ a₄ → a₃ ≠ -a₄ →
      a₁ ^ 2 + a₂ ^ 2 = a₃ ^ 2 + a₄ ^ 2 →
      Irreducible ((a₁ ^ 2 + a₂ ^ 2).map (Int.castRingHom ℚ)) →
      5 ≤ (a₁ ^ 2 + a₂ ^ 2).content := by
  intro a₁ a₂ a₃ a₄ _ _ h13 k13 h14 k14 _ _ _ _ _ _ heq hirr
  by_contra hcon
  have hp0 : a₁ ^ 2 + a₂ ^ 2 ≠ 0 := by
    intro h
    rw [h, Polynomial.map_zero] at hirr
    exact not_irreducible_zero hirr
  have hprim : (a₁ ^ 2 + a₂ ^ 2).content ∈ Set.Ioo (0 : ℤ) 5 := by
    change 0 < _ ∧ _ < 5
    have hnn : 0 ≤ (a₁ ^ 2 + a₂ ^ 2).content :=
      Int.nonneg_of_normalize_eq_self normalize_content
    have hne : (a₁ ^ 2 + a₂ ^ 2).content ≠ 0 := fun h => hp0 (content_eq_zero_iff.mp h)
    omega
  have hxy : (a₁ - a₃) * (a₁ + a₃) = (a₄ - a₂) * (a₄ + a₂) := by linear_combination heq
  obtain ⟨m, n, ⟨r, hr⟩, ⟨s, hs⟩, hx⟩ :=
    exists_dvd_and_dvd_of_dvd_mul (Dvd.intro _ hxy)
  have hmn : m * n ≠ 0 := by
    rw [← hx]
    exact sub_ne_zero.mpr h13
  have hm : m ≠ 0 := left_ne_zero_of_mul hmn
  have hn : n ≠ 0 := right_ne_zero_of_mul hmn
  have hy : a₁ + a₃ = r * s := by
    apply mul_left_cancel₀ hmn
    calc m * n * (a₁ + a₃) = (a₁ - a₃) * (a₁ + a₃) := by rw [hx]
      _ = (a₄ - a₂) * (a₄ + a₂) := hxy
      _ = m * n * (r * s) := by rw [hr, hs]; ring
  have hrs : r * s ≠ 0 := by
    rw [← hy]
    intro h
    exact k13 (eq_neg_of_add_eq_zero_left h)
  have hr0 : r ≠ 0 := left_ne_zero_of_mul hrs
  have hs0 : s ≠ 0 := right_ne_zero_of_mul hrs
  have hid : C (4 : ℤ) * (a₁ ^ 2 + a₂ ^ 2) = (m ^ 2 + s ^ 2) * (n ^ 2 + r ^ 2) := by
    have e4 : (C (4 : ℤ) : ℤ[X]) = 4 := by simp
    rw [e4]
    linear_combination (2 * a₁ + m * n + r * s) * (hx + hy)
      + (2 * a₂ + n * s - m * r) * (hs - hr)
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hQ := congrArg (Polynomial.map (Int.castRingHom ℚ)) hid
  rw [Polynomial.map_mul, Polynomial.map_mul, map_C] at hQ
  have h4 : (Int.castRingHom ℚ) 4 ≠ 0 := by norm_num
  have hprod0 : (m ^ 2 + s ^ 2).map (Int.castRingHom ℚ) * (n ^ 2 + r ^ 2).map (Int.castRingHom ℚ)
      ≠ 0 := by
    rw [← hQ]
    exact mul_ne_zero (C_ne_zero.mpr h4) hirr.ne_zero
  have hM0 := left_ne_zero_of_mul hprod0
  have hN0 := right_ne_zero_of_mul hprod0
  have hdegsum : ((m ^ 2 + s ^ 2).map (Int.castRingHom ℚ)).natDegree
      + ((n ^ 2 + r ^ 2).map (Int.castRingHom ℚ)).natDegree
      = ((a₁ ^ 2 + a₂ ^ 2).map (Int.castRingHom ℚ)).natDegree := by
    rw [← natDegree_mul hM0 hN0, ← hQ, natDegree_C_mul h4]
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj,
    natDegree_map_eq_of_injective hinj] at hdegsum
  have hdvd : (a₁ ^ 2 + a₂ ^ 2).map (Int.castRingHom ℚ) ∣
      (m ^ 2 + s ^ 2).map (Int.castRingHom ℚ) * (n ^ 2 + r ^ 2).map (Int.castRingHom ℚ) :=
    Dvd.intro_left _ hQ
  rcases hirr.prime.dvd_or_dvd hdvd with hd | hd
  · have hle := natDegree_le_of_dvd hd hM0
    rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj] at hle
    have hdeg : (n ^ 2 + r ^ 2).natDegree = 0 := by omega
    have hprim2 : (a₁ ^ 2 + (-a₂) ^ 2).content ∈ Set.Ioo (0 : ℤ) 5 := by rw [neg_sq]; exact hprim
    rcases sharp_key a₁ (-a₂) a₃ a₄ n m s r (by rw [hx]; ring) (by rw [hy]; ring)
      (by rw [sub_neg_eq_add, hs]) (by rw [← sub_eq_add_neg, hr]) hn hr0 hprim2 hdeg with h | h
    · exact h14 h
    · exact k14 h
  · have hle := natDegree_le_of_dvd hd hN0
    rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj] at hle
    have hdeg : (m ^ 2 + s ^ 2).natDegree = 0 := by omega
    rcases sharp_key a₁ a₂ a₃ a₄ m n r s hx hy hr hs hm hs0 hprim hdeg with h | h
    · exact h14 h
    · exact k14 h

theorem OMA.solution : type_of% @OMA.S_mo_187311.main := by
  intro a b c d h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ he hi
  have h := OMA.content_at_least_five a b c d h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ he hi
  omega

namespace MO187311Eisen

noncomputable def F (m : ℕ) : ℤ[X] := X ^ (2 * m) + 2 * X ^ m + 2

private theorem lower_degree (m : ℕ) (hm : 0 < m) :
    (2 * X ^ m + 2 : ℤ[X]).natDegree < 2 * m := by
  calc
    _ ≤ max (2 * X ^ m : ℤ[X]).natDegree (2 : ℤ[X]).natDegree := natDegree_add_le ..
    _ ≤ m := by simp [natDegree_mul]
    _ < _ := by omega

theorem monic (m : ℕ) (hm : 0 < m) : (F m).Monic := by
  rw [F, add_assoc]
  apply monic_X_pow_add
  exact lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.mpr (lower_degree m hm))

theorem natDegree_F (m : ℕ) (hm : 0 < m) : (F m).natDegree = 2 * m := by
  rw [F, add_assoc, natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
  simpa using lower_degree m hm

theorem irreducible_map (m : ℕ) (hm : 0 < m) :
    Irreducible ((F m).map (Int.castRingHom ℚ)) := by
  have hmon := monic m hm
  have hd : (F m).degree = (2 * m : ℕ) := by
    rw [degree_eq_natDegree hmon.ne_zero, natDegree_F m hm]
  have hpos : 0 < 2 * m := by omega
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hmon.isPrimitive).mp
  apply irreducible_of_eisenstein_criterion
    (Ideal.isPrime_span_singleton_of_prime (show Prime (2 : ℤ) by norm_num))
  · rw [hmon.leadingCoeff, Ideal.mem_span_singleton]
    decide
  · intro k hk
    rw [hd] at hk
    have hkNat : k < 2 * m := WithBot.coe_lt_coe.mp hk
    rw [Ideal.mem_span_singleton]
    cases k with
    | zero => simp [F, coeff_X_pow, hm.ne, hpos.ne]
    | succ k =>
      simp [F, coeff_X_pow, hkNat.ne]
      split <;> simp
  · rw [hd]
    exact_mod_cast hpos
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp [F, coeff_X_pow, hm.ne, hpos.ne]
  · exact hmon.isPrimitive

end MO187311Eisen

namespace MO187311Family
open Polynomial

/-- Two inequivalent representations with the primitive factor written explicitly. -/
theorem representations (m : ℕ) :
    ∃ a b c d : ℤ[X],
      (a ≠ b ∧ a ≠ -b ∧ a ≠ c ∧ a ≠ -c ∧ a ≠ d ∧ a ≠ -d ∧
       b ≠ c ∧ b ≠ -c ∧ b ≠ d ∧ b ≠ -d ∧ c ≠ d ∧ c ≠ -d) ∧
      a^2+b^2 = C 5 * (X^(2*m)+2*X^m+2) ∧ c^2+d^2 = a^2+b^2 := by
  let t : ℤ[X] := X^m + 1
  refine ⟨t+2,2*t-1,t-2,2*t+1,?_,?_,?_⟩
  · have ht : t.eval 1 = 2 := by simp [t]
    repeat' constructor
    all_goals
      intro h
      have he := congrArg (Polynomial.eval (1 : ℤ)) h
      norm_num [eval_add, eval_sub, eval_mul, eval_neg, ht] at he
  · dsimp [t]
    rw [show 2*m=m+m by omega, pow_add]
    norm_num
    ring
  · ring

end MO187311Family

namespace MO187311Family
open Polynomial MO187311Eisen

/-- The examples in the question exist in every positive even degree. -/
theorem all_even_degrees (m : ℕ) (hm : 0 < m) :
    ∃ a b c d p : ℤ[X],
      (a ≠ b ∧ a ≠ -b ∧ a ≠ c ∧ a ≠ -c ∧ a ≠ d ∧ a ≠ -d ∧
       b ≠ c ∧ b ≠ -c ∧ b ≠ d ∧ b ≠ -d ∧ c ≠ d ∧ c ≠ -d) ∧
      a^2+b^2 = p ∧ c^2+d^2 = p ∧ p.natDegree = 2*m ∧
      p.content = 5 ∧ Irreducible (p.map (Int.castRingHom ℚ)) := by
  obtain ⟨a,b,c,d,hd,h₁,h₂⟩ := representations m
  change a^2+b^2 = C 5 * F m at h₁
  refine ⟨a,b,c,d,C 5 * F m,hd,h₁,h₂.trans h₁,?_,?_,?_⟩
  · rw [natDegree_C_mul (by norm_num : (5:ℤ) ≠ 0), natDegree_F m hm]
  · rw [content_C_mul, (monic m hm).isPrimitive.content_eq_one, mul_one]
    decide
  · rw [Polynomial.map_mul, map_C, irreducible_mul_iff]
    exact Or.inr ⟨irreducible_map m hm, isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num))⟩

end MO187311Family
