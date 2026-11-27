import OMAReductions.R_Erdos1141_erdos_1141_variants_pollack_1_3_R1
import Mathlib

/-!
Burgess-scale divisor-sum estimate for Pollack's Theorem 1.3.
Adapted from the Pollack17 development imported by Boris Alexeev in plby/lean-proofs,
whose enclosing formalization credits GPT-5.4 Pro and Yuta Oriike,
commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e, and the BoundedGaps
contributors, frenzymath/FormalPantheon (Apache License 2.0), commit ffbb65c21afc8a36ace67720f1b0df1c63d26bd1. The Burgess modules also credit
their amplifier and subpower lemmas to Erdos587.NVDevelopment.
-/

/-! ## Nonnegative divisor coefficients of quadratic characters

Source module `ErdosProblems.Erdos1141.QuadraticCoefficients`. -/

noncomputable section

namespace Pollack17

open scoped BigOperators ComplexOrder

open ArithmeticFunction

variable {m : ℕ}

noncomputable def divisorCoefficient (χ : DirichletCharacter ℂ m) (n : ℕ) : ℝ :=
  (χ.zetaMul n).re

@[simp] theorem divisorCoefficient_zero (χ : DirichletCharacter ℂ m) :
    divisorCoefficient χ 0 = 0 := by
  simp [divisorCoefficient]

@[simp] theorem divisorCoefficient_one (χ : DirichletCharacter ℂ m) :
    divisorCoefficient χ 1 = 1 := by
  simp [divisorCoefficient, χ.isMultiplicative_zetaMul.map_one]

end Pollack17

end

/-! ## Elementary collision estimates for Burgess averaging

Source module `ErdosProblems.Erdos1141.BurgessEnergyArithmetic`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

lemma sum_Icc_inv_natCast_le_one_add_log (n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, ((r : ℝ)⁻¹)) ≤ 1 + Real.log n := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast] using harmonic_le_one_add_log n

lemma sum_Icc_natCast_div_le (q n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, (q : ℝ) / r) ≤
      q * (1 + Real.log n) := by
  simp_rw [div_eq_mul_inv]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_Icc_inv_natCast_le_one_add_log n)
    (Nat.cast_nonneg q)

lemma card_le_div_add_one_of_pairwise_modEq {s : Finset ℕ} {X h : ℕ}
    (hsX : s ⊆ Finset.Icc 1 X) (_hh : 0 < h)
    (hmod : ∀ a ∈ s, ∀ b ∈ s, a ≡ b [MOD h]) :
    s.card ≤ X / h + 1 := by
  let f : ℕ → ℕ := fun a ↦ a / h
  have hinj : Set.InjOn f s := by
    intro a ha b hb hab
    have hrem : a % h = b % h := hmod a ha b hb
    have hda : h * (a / h) + a % h = a := Nat.div_add_mod a h
    have hdb : h * (b / h) + b % h = b := Nat.div_add_mod b h
    dsimp [f] at hab
    calc
      a = h * (a / h) + a % h := hda.symm
      _ = h * (b / h) + b % h := by rw [hab, hrem]
      _ = b := hdb
  have himage : s.image f ⊆ Finset.range (X / h + 1) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [Finset.mem_range]
    have haX : a ≤ X := (Finset.mem_Icc.mp (hsX ha)).2
    exact Nat.lt_succ_of_le (Nat.div_le_div_right haX)
  calc
    s.card = (s.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (X / h + 1)).card := Finset.card_le_card himage
    _ = X / h + 1 := Finset.card_range _

lemma card_le_div_add_one_of_fst_pairwise_modEq
    {s : Finset (ℕ × ℕ)} {H a : ℕ}
    (hsH : ∀ z ∈ s, z.1 < H) (ha : 0 < a)
    (hinj : Set.InjOn (fun z : ℕ × ℕ ↦ z.1) s)
    (hmod : ∀ z ∈ s, ∀ w ∈ s, z.1 ≡ w.1 [MOD a]) :
    s.card ≤ H / a + 1 := by
  let f : ℕ × ℕ → ℕ := fun z ↦ z.1 + 1
  have hfinj : Set.InjOn f s := by
    intro z hz w hw hzw
    apply hinj hz hw
    change z.1 + 1 = w.1 + 1 at hzw
    exact Nat.add_right_cancel hzw
  have hcard : s.card = (s.image f).card :=
    (Finset.card_image_of_injOn hfinj).symm
  rw [hcard]
  apply card_le_div_add_one_of_pairwise_modEq
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    simp only [Finset.mem_Icc]
    exact ⟨Nat.succ_pos _, Nat.succ_le_iff.mpr (hsH z hz)⟩
  · exact ha
  · intro x hx y hy
    rw [Finset.mem_image] at hx hy
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    exact (hmod z hz w hw).add_right 1

def burgessIntervalCollision (p M H u₁ u₂ : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range H) ×ˢ (Finset.range H)).filter fun ij ↦
    (M + ij.1) * u₂ ≡ (M + ij.2) * u₁ [MOD p]

def positiveMultiplesUpTo (d U : ℕ) : Finset ℕ :=
  (Finset.Icc 1 U).filter fun u ↦ d ∣ u

lemma positiveMultiplesUpTo_card (d U : ℕ) :
    (positiveMultiplesUpTo d U).card = U / d := by
  have hset : Finset.Icc 1 U = Finset.Ioc 0 U := by
    ext x
    simp
    omega
  rw [positiveMultiplesUpTo, hset]
  exact Nat.Ioc_filter_dvd_card_eq_div U d

lemma sum_positiveMultiplesUpTo_quotient
    {R : Type*} [AddCommMonoid R] (d U : ℕ) (hd : 0 < d)
    (f : ℕ → R) :
    (∑ u ∈ positiveMultiplesUpTo d U, f (u / d)) =
      ∑ a ∈ Finset.Icc 1 (U / d), f a := by
  apply Finset.sum_bij (fun u _ ↦ u / d)
  · intro u hu
    change u ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u) at hu
    rw [Finset.mem_filter] at hu
    rw [Finset.mem_Icc]
    exact ⟨Nat.div_pos (Nat.le_of_dvd (Finset.mem_Icc.mp hu.1).1 hu.2) hd,
      Nat.div_le_div_right (Finset.mem_Icc.mp hu.1).2⟩
  · intro u₁ hu₁ u₂ hu₂ h
    change u₁ ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u) at hu₁
    change u₂ ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u) at hu₂
    have hd₁ := (Finset.mem_filter.mp hu₁).2
    have hd₂ := (Finset.mem_filter.mp hu₂).2
    calc
      u₁ = d * (u₁ / d) := (Nat.mul_div_cancel' hd₁).symm
      _ = d * (u₂ / d) := by rw [h]
      _ = u₂ := Nat.mul_div_cancel' hd₂
  · intro a ha
    refine ⟨d * a, ?_, ?_⟩
    · change d * a ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u)
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_Icc] at ha ⊢
        exact ⟨Nat.mul_pos hd ha.1,
          by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).mp ha.2⟩
      · exact dvd_mul_right d a
    · rw [Nat.mul_div_cancel_left]
      exact hd
  · intro u hu
    rfl

lemma sum_Icc_natDiv_add_one_cast_le (H n : ℕ) :
    (((∑ a ∈ Finset.Icc 1 n, (H / a + 1)) : ℕ) : ℝ) ≤
      H * (1 + Real.log n) + n := by
  rw [Nat.cast_sum]
  calc
    (∑ a ∈ Finset.Icc 1 n, (((H / a + 1) : ℕ) : ℝ)) ≤
        ∑ a ∈ Finset.Icc 1 n, ((H : ℝ) / a + 1) := by
      apply Finset.sum_le_sum
      intro a ha
      norm_num only [Nat.cast_add, Nat.cast_one]
      exact add_le_add (Nat.cast_div_le (α := ℝ) (m := H) (n := a)) le_rfl
    _ = (∑ a ∈ Finset.Icc 1 n, (H : ℝ) / a) + n := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ H * (1 + Real.log n) + n := by
      gcongr
      exact sum_Icc_natCast_div_le H n

lemma reduced_term_le_common_divisor_sum
    {H U u₁ u₂ : ℕ} (hu₁ : u₁ ∈ Finset.Icc 1 U) :
    H / (u₁ / u₁.gcd u₂) + 1 ≤
      ∑ d ∈ Finset.Icc 1 U,
        if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
  let d := u₁.gcd u₂
  have hu₁pos : 0 < u₁ := (Finset.mem_Icc.mp hu₁).1
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left u₂ hu₁pos
  have hdmem : d ∈ Finset.Icc 1 U := by
    rw [Finset.mem_Icc]
    exact ⟨hdpos, (Nat.gcd_le_left u₂ hu₁pos).trans
      (Finset.mem_Icc.mp hu₁).2⟩
  calc
    H / (u₁ / u₁.gcd u₂) + 1 =
        if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      simp [d, Nat.gcd_dvd_left, Nat.gcd_dvd_right]
    _ ≤ ∑ d ∈ Finset.Icc 1 U,
        if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      exact Finset.single_le_sum
        (s := Finset.Icc 1 U)
        (f := fun d ↦ if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0)
        (fun _ _ ↦ Nat.zero_le _) hdmem

def burgessDivisorOvercount (H U : ℕ) : ℕ :=
  ∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
    ∑ d ∈ Finset.Icc 1 U,
      if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0

lemma burgessDivisorSlice_eq (H U d : ℕ) (hd : 0 < d) :
    (∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
      if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0) =
      (U / d) * ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1) := by
  classical
  simp_rw [ite_and]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  change (∑ u₁ ∈ positiveMultiplesUpTo d U,
      ∑ u₂ ∈ Finset.Icc 1 U,
        if d ∣ u₂ then H / (u₁ / d) + 1 else 0) = _
  calc
    (∑ u₁ ∈ positiveMultiplesUpTo d U,
        ∑ u₂ ∈ Finset.Icc 1 U,
          if d ∣ u₂ then H / (u₁ / d) + 1 else 0) =
      ∑ u₁ ∈ positiveMultiplesUpTo d U,
        ∑ _u₂ ∈ positiveMultiplesUpTo d U,
          (H / (u₁ / d) + 1) := by
      apply Finset.sum_congr rfl
      intro u₁ hu₁
      rw [← Finset.sum_filter]
      rfl
    _ = (U / d) * ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1) := by
      simp_rw [Finset.sum_const]
      rw [positiveMultiplesUpTo_card]
      simp_rw [Nat.nsmul_eq_mul]
      rw [← Finset.mul_sum]
      congr 1
      exact sum_positiveMultiplesUpTo_quotient d U hd
        (fun a ↦ H / a + 1)

lemma burgessDivisorOvercount_eq (H U : ℕ) :
    burgessDivisorOvercount H U =
      ∑ d ∈ Finset.Icc 1 U, (U / d) *
        ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1) := by
  rw [burgessDivisorOvercount]
  calc
    (∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
        ∑ d ∈ Finset.Icc 1 U,
          if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0) =
      ∑ u₁ ∈ Finset.Icc 1 U, ∑ d ∈ Finset.Icc 1 U,
        ∑ u₂ ∈ Finset.Icc 1 U,
          if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u₁ hu₁
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Icc 1 U, ∑ u₁ ∈ Finset.Icc 1 U,
        ∑ u₂ ∈ Finset.Icc 1 U,
          if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hdmem
      exact burgessDivisorSlice_eq H U d (Finset.mem_Icc.mp hdmem).1

lemma burgessDivisorOvercount_cast_le (H U : ℕ) (hU : 0 < U) :
    (burgessDivisorOvercount H U : ℝ) ≤
      ((H : ℝ) * (1 + Real.log U) + U) *
        ((U : ℝ) * (1 + Real.log U)) := by
  rw [burgessDivisorOvercount_eq, Nat.cast_sum]
  have hlogU : 0 ≤ 1 + Real.log U := by
    have : (1 : ℝ) ≤ U := by exact_mod_cast hU
    linarith [Real.log_nonneg this]
  calc
    (∑ d ∈ Finset.Icc 1 U,
        ((((U / d) * ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1)) : ℕ) : ℝ)) ≤
      ∑ d ∈ Finset.Icc 1 U,
        ((U : ℝ) / d) * ((H : ℝ) * (1 + Real.log U) + U) := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hdpos : 0 < d := (Finset.mem_Icc.mp hdmem).1
      have hdU : d ≤ U := (Finset.mem_Icc.mp hdmem).2
      have hnpos : 0 < U / d := Nat.div_pos hdU hdpos
      have hnU : U / d ≤ U := Nat.div_le_self U d
      have hlog : Real.log (((U / d : ℕ) : ℝ)) ≤ Real.log U := by
        apply Real.log_le_log
        · exact_mod_cast hnpos
        · exact_mod_cast hnU
      rw [Nat.cast_mul]
      apply mul_le_mul
      · exact Nat.cast_div_le
      · calc
          (((∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1)) : ℕ) : ℝ) ≤
              (H : ℝ) * (1 + Real.log (((U / d : ℕ) : ℝ))) +
                (U / d : ℕ) :=
            sum_Icc_natDiv_add_one_cast_le H (U / d)
          _ ≤ (H : ℝ) * (1 + Real.log U) + U := by
            gcongr
      · positivity
      · positivity
    _ = ((H : ℝ) * (1 + Real.log U) + U) *
        ∑ d ∈ Finset.Icc 1 U, ((U : ℝ) / d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ ((H : ℝ) * (1 + Real.log U) + U) *
        ((U : ℝ) * (1 + Real.log U)) := by
      exact mul_le_mul_of_nonneg_left (sum_Icc_natCast_div_le U U)
        (add_nonneg (mul_nonneg (Nat.cast_nonneg H) hlogU) (Nat.cast_nonneg U))

lemma reduced_denominator_sum_cast_le
    (H U : ℕ) :
    ((∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
      (H / (u₁ / u₁.gcd u₂) + 1) : ℕ) : ℝ) ≤
      (burgessDivisorOvercount H U : ℝ) := by
  exact_mod_cast Finset.sum_le_sum fun u₁ hu₁ ↦
    Finset.sum_le_sum fun u₂ hu₂ ↦
      reduced_term_le_common_divisor_sum hu₁

lemma burgessIntervalCollision_card_le_of_coprime
    {q M H U u₁ u₂ : ℕ}
    (hH : 0 < H) (hU : 0 < U)
    (hu₁ : u₁ ∈ Finset.Icc 1 U) (hu₂ : u₂ ∈ Finset.Icc 1 U)
    (hcop₁ : q.Coprime u₁)
    (hsmall : 2 * (U * H) < q) :
    (burgessIntervalCollision q M H u₁ u₂).card ≤
      H / (u₁ / u₁.gcd u₂) + 1 := by
  let d := u₁.gcd u₂
  let a := u₁ / d
  let b := u₂ / d
  have hu₁pos : 0 < u₁ := (Finset.mem_Icc.mp hu₁).1
  have hu₂pos : 0 < u₂ := (Finset.mem_Icc.mp hu₂).1
  have hu₁U : u₁ ≤ U := (Finset.mem_Icc.mp hu₁).2
  have hu₂U : u₂ ≤ U := (Finset.mem_Icc.mp hu₂).2
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left u₂ hu₁pos
  have hd₁ : d ∣ u₁ := Nat.gcd_dvd_left u₁ u₂
  have hd₂ : d ∣ u₂ := Nat.gcd_dvd_right u₁ u₂
  have hfac₁ : d * a = u₁ := Nat.mul_div_cancel' hd₁
  have hfac₂ : d * b = u₂ := Nat.mul_div_cancel' hd₂
  have hapos : 0 < a := Nat.div_pos (Nat.le_of_dvd hu₁pos hd₁) hdpos
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd hdpos
  apply card_le_div_add_one_of_fst_pairwise_modEq
  · intro z hz
    exact Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).1
  · exact hapos
  · intro z hz w hw hzw
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    apply Prod.ext hzw
    change z.1 = w.1 at hzw
    rw [hzw] at hz'
    have hjmodM : M + z.2 ≡ M + w.2 [MOD q] := by
      apply Nat.ModEq.cancel_right_of_coprime hcop₁.gcd_eq_one
      exact hz'.symm.trans hw'
    have hjmod : z.2 ≡ w.2 [MOD q] :=
      Nat.ModEq.add_left_cancel' M hjmodM
    have hHq : H < q := by
      have hUHpos : 0 < U * H := Nat.mul_pos hU hH
      have hHle : H ≤ U * H := by
        simpa [mul_comm] using Nat.le_mul_of_pos_right H hU
      omega
    exact hjmod.eq_of_lt_of_lt
      (lt_trans (Finset.mem_range.mp
        (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).2) hHq)
      (lt_trans (Finset.mem_range.mp
        (Finset.mem_product.mp (Finset.filter_subset _ _ hw)).2) hHq)
  · intro z hz w hw
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    have hsum := hz'.add hw'.symm
    have hred : u₂ * z.1 + u₁ * w.2 ≡
        u₂ * w.1 + u₁ * z.2 [MOD q] := by
      apply Nat.ModEq.add_left_cancel' (M * (u₁ + u₂))
      simpa [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc,
        add_comm, add_left_comm, add_assoc] using hsum
    have hzH := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).1
    have hzH₂ := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).2
    have hwH := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hw)).1
    have hwH₂ := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hw)).2
    have hterm₁ : u₂ * z.1 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₂U hzH hU
    have hterm₂ : u₁ * w.2 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₁U hwH₂ hU
    have hterm₃ : u₂ * w.1 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₂U hwH hU
    have hterm₄ : u₁ * z.2 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₁U hzH₂ hU
    have heq : u₂ * z.1 + u₁ * w.2 =
        u₂ * w.1 + u₁ * z.2 :=
      hred.eq_of_lt_of_lt (by omega) (by omega)
    have hdeq : d * (b * z.1 + a * w.2) =
        d * (b * w.1 + a * z.2) := by
      calc
        d * (b * z.1 + a * w.2) = u₂ * z.1 + u₁ * w.2 := by
          rw [mul_add, ← mul_assoc, ← mul_assoc, hfac₂, hfac₁]
        _ = u₂ * w.1 + u₁ * z.2 := heq
        _ = d * (b * w.1 + a * z.2) := by
          rw [mul_add, ← mul_assoc, ← mul_assoc, hfac₂, hfac₁]
    have hnorm : b * z.1 + a * w.2 = b * w.1 + a * z.2 :=
      Nat.eq_of_mul_eq_mul_left hdpos hdeq
    have haw : a * w.2 ≡ 0 [MOD a] :=
      (Nat.dvd_mul_right a w.2).modEq_zero_nat
    have haz : a * z.2 ≡ 0 [MOD a] :=
      (Nat.dvd_mul_right a z.2).modEq_zero_nat
    have hfull : b * z.1 + a * w.2 ≡ b * w.1 + a * z.2 [MOD a] := by
      rw [hnorm]
    have hba : b * z.1 ≡ b * w.1 [MOD a] :=
      ((Nat.ModEq.rfl.add haw.symm).trans hfull).trans
        (Nat.ModEq.rfl.add haz)
    exact Nat.ModEq.cancel_left_of_coprime hab.gcd_eq_one hba

end Pollack17.Burgess

end

/-! ## Positive divisor-pair reindexing

Source module `BoundedGaps.BombieriVinogradov.Analytic.PositiveDivisorPairReindex`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

def positiveFactorPairs (Q : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc 0 Q ×ˢ Finset.Ioc 0 Q).filter
    (fun p ↦ p.1 * p.2 ≤ Q)

theorem sum_positiveFactorPairs_filter_fst_eq_sum_multipliers
    {Q : ℕ} {M : Type*} [AddCommMonoid M]
    (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℕ → M) :
    (∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦ P p.1),
      f p.1 p.2) =
      ∑ d ∈ Finset.Ioc 0 Q with P d,
        ∑ k ∈ Finset.Ioc 0 (Q / d), f d k := by
  let S : Finset (ℕ × ℕ) :=
    (positiveFactorPairs Q).filter (fun p ↦ P p.1)
  let T : Finset ((d : ℕ) × ℕ) :=
    Finset.sigma ((Finset.Ioc 0 Q).filter P)
      (fun d ↦ Finset.Ioc 0 (Q / d))
  have hbij :
      (∑ p ∈ S, f p.1 p.2) =
        ∑ z ∈ T, f z.1 z.2 := by
    apply Finset.sum_bij (fun p _hp ↦ ⟨p.1, p.2⟩)
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpairs, hP⟩
      rcases Finset.mem_filter.mp hpairs with ⟨hprodmem, hprod⟩
      rcases Finset.mem_product.mp hprodmem with ⟨hdmem, hkmem⟩
      have hdpos : 0 < p.1 := (Finset.mem_Ioc.mp hdmem).1
      have hkdiv : p.2 ≤ Q / p.1 := by
        apply (Nat.le_div_iff_mul_le hdpos).2
        simpa [Nat.mul_comm] using hprod
      exact Finset.mem_sigma.mpr ⟨
        Finset.mem_filter.mpr ⟨hdmem, hP⟩,
        Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hkmem).1, hkdiv⟩⟩
    · intro p _hp p' _hp' heq
      apply Prod.ext
      · exact congrArg Sigma.fst heq
      · exact congrArg Sigma.snd heq
    · intro z hz
      rcases z with ⟨d, k⟩
      rcases Finset.mem_sigma.mp hz with ⟨hdmemP, hkmem⟩
      rcases Finset.mem_filter.mp hdmemP with ⟨hdmem, hP⟩
      have hdpos : 0 < d := (Finset.mem_Ioc.mp hdmem).1
      have hkBounds := Finset.mem_Ioc.mp hkmem
      have hprod : d * k ≤ Q := by
        have h := (Nat.le_div_iff_mul_le hdpos).1 hkBounds.2
        simpa [Nat.mul_comm] using h
      have hkQ : k ≤ Q :=
        hkBounds.2.trans (Nat.div_le_self Q d)
      have hpairs : (d, k) ∈ positiveFactorPairs Q := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr ⟨hdmem,
          Finset.mem_Ioc.mpr ⟨hkBounds.1, hkQ⟩⟩, hprod⟩
      exact ⟨(d, k), Finset.mem_filter.mpr ⟨hpairs, hP⟩, rfl⟩
    · intro p _hp
      rfl
  have hsum := Finset.sum_sigma'
    ((Finset.Ioc 0 Q).filter P)
    (fun d ↦ Finset.Ioc 0 (Q / d)) (fun d k ↦ f d k)
  simpa [S, T] using hbij.trans hsum.symm

theorem sum_divisorsAntidiagonal_up_to_eq_sum_positiveFactorPairs
    {Q : ℕ} {M : Type*} [AddCommMonoid M]
    (f : ℕ → ℕ → M) :
    (∑ q ∈ Finset.Ioc 0 Q,
      ∑ p ∈ q.divisorsAntidiagonal, f p.1 p.2) =
      ∑ p ∈ positiveFactorPairs Q, f p.1 p.2 := by
  let T : Finset ℕ := Finset.Ioc 0 Q
  let g : ℕ × ℕ → ℕ := fun p ↦ p.1 * p.2
  have hmaps : ∀ p ∈ positiveFactorPairs Q, g p ∈ T := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hprod⟩
    rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
    rw [Finset.mem_Ioc] at hp₁ hp₂
    exact Finset.mem_Ioc.mpr ⟨Nat.mul_pos hp₁.1 hp₂.1, hprod⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := positiveFactorPairs Q) (t := T) hmaps
    (fun p ↦ f p.1 p.2)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le (N := Q)]
  · apply Finset.sum_congr
    · ext p
      simp only [positiveFactorPairs, g, Finset.mem_filter]
      constructor
      · rintro ⟨hp, hprod⟩
        exact ⟨⟨hp, hprod.le.trans (Finset.mem_Ioc.mp hq).2⟩, hprod⟩
      · rintro ⟨⟨hp, _⟩, hprod⟩
        exact ⟨hp, hprod⟩
    · intro p _
      rfl
  · exact (Finset.mem_Ioc.mp hq).1.ne'
  · exact (Finset.mem_Ioc.mp hq).2

theorem sum_divisors_up_to_eq_sum_positiveFactorPairs
    {Q : ℕ} {M : Type*} [AddCommMonoid M]
    (f : ℕ → ℕ → M) :
    (∑ q ∈ Finset.Ioc 0 Q,
      ∑ d ∈ q.divisors, f q d) =
      ∑ p ∈ positiveFactorPairs Q,
        f (p.1 * p.2) p.1 := by
  calc
    (∑ q ∈ Finset.Ioc 0 Q, ∑ d ∈ q.divisors, f q d) =
        ∑ q ∈ Finset.Ioc 0 Q,
          ∑ p ∈ q.divisorsAntidiagonal,
            f (p.1 * p.2) p.1 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [← Nat.sum_divisorsAntidiagonal
        (f := fun d _k ↦ f q d)]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.mem_divisorsAntidiagonal] at hp
      rw [hp.1]
    _ = _ :=
      sum_divisorsAntidiagonal_up_to_eq_sum_positiveFactorPairs
        (fun d k ↦ f (d * k) d)

end BoundedGaps.Maynard

end

/-! ## A truncated hyperbola estimate for quadratic divisor coefficients

Source module `ErdosProblems.Erdos1141.DivisorHyperbola`. -/

noncomputable section

namespace Pollack17

open scoped BigOperators

open BoundedGaps.Maynard

theorem divisor_sum_hyperbola (f : ℕ → ℝ) {X Y : ℕ} (hYX : Y ≤ X) :
    (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, f d) =
      (∑ d ∈ Finset.Icc 1 Y, ((X / d : ℕ) : ℝ) * f d) +
        ∑ a ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Ioc Y (X / a), f d := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (positiveFactorPairs X)
    (fun p : ℕ × ℕ => p.1 ≤ Y) (fun p => f p.1)
  have hsmall : (∑ p ∈ (positiveFactorPairs X).filter (fun p => p.1 ≤ Y), f p.1) =
      ∑ d ∈ Finset.Icc 1 Y, ((X / d : ℕ) : ℝ) * f d := by
    rw [sum_positiveFactorPairs_filter_fst_eq_sum_multipliers (fun d => d ≤ Y) (fun d _ => f d)]
    have hset : (Finset.Ioc 0 X).filter (fun d => d ≤ Y) = Finset.Icc 1 Y := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hset]
    simp
  have hlarge : (∑ p ∈ (positiveFactorPairs X).filter (fun p => ¬p.1 ≤ Y), f p.1) =
      ∑ a ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Ioc Y (X / a), f d := by
    rw [Finset.sum_sigma']
    apply Finset.sum_bij (fun p _ => ⟨p.2, p.1⟩)
    · intro p hp
      obtain ⟨hp, hY⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp, hprod⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
      have ha := Finset.mem_Ioc.mp ha
      have hb := Finset.mem_Ioc.mp hb
      exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr hb,
        Finset.mem_Ioc.mpr ⟨by change Y < p.1; omega, (Nat.le_div_iff_mul_le hb.1).mpr hprod⟩⟩
    · intro p _ p' _ h
      exact Prod.ext (congrArg Sigma.snd h) (congrArg Sigma.fst h)
    · rintro ⟨a, d⟩ h
      obtain ⟨ha, hd⟩ := Finset.mem_sigma.mp h
      have ha := Finset.mem_Icc.mp ha
      have hd := Finset.mem_Ioc.mp hd
      dsimp only [Sigma.fst, Sigma.snd] at ha hd
      refine ⟨(d, a), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, by simpa using not_le.mpr hd.1⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega,
        hd.2.trans (Nat.div_le_self _ _)⟩, Finset.mem_Ioc.mpr ha⟩,
        (Nat.le_div_iff_mul_le ha.1).mp hd.2⟩
    · intro p _
      rfl
  calc
    _ = ∑ n ∈ Finset.Ioc 0 X, ∑ d ∈ n.divisors, f d := by
      rw [show Finset.Icc 1 X = Finset.Ioc 0 X by ext n; simp; omega]
    _ = ∑ p ∈ positiveFactorPairs X, f p.1 := sum_divisors_up_to_eq_sum_positiveFactorPairs _
    _ = _ := by rw [← hsplit, hsmall, hlarge]

theorem abs_truncated_floor_error_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (X Y : ℕ) :
    |(∑ d ∈ Finset.Icc 1 Y, ((X / d : ℕ) : ℝ) * f d) -
      (X : ℝ) * ∑ d ∈ Finset.Icc 1 Y, f d / (d : ℝ)| ≤ Y := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 Y,
        |((X / d : ℕ) : ℝ) * f d - (X : ℝ) * (f d / (d : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 Y, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have heq : ((X / d : ℕ) : ℝ) * f d - (X : ℝ) * (f d / (d : ℝ)) =
          (((X / d : ℕ) : ℝ) - (X : ℝ) / d) * f d := by ring
      rw [heq, abs_mul]
      have hfloor : |((X / d : ℕ) : ℝ) - (X : ℝ) / d| ≤ 1 := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr Nat.cast_div_le)]
        have h := Nat.lt_floor_add_one ((X : ℝ) / d)
        rw [Nat.floor_div_eq_div] at h
        linarith
      exact (mul_le_mul hfloor (hf d) (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
    _ = _ := by simp

theorem abs_hyperbola_tail_le (f : ℕ → ℝ) {X Y : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hprefix : ∀ n : ℕ, Y ≤ n →
      |∑ d ∈ Finset.Icc 1 n, f d| ≤ (n : ℝ) * b) :
    |∑ a ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Ioc Y (X / a), f d| ≤
      2 * (X : ℝ) * b * (1 + Real.log (X : ℝ)) := by
  have hterm (a : ℕ) (ha : a ∈ Finset.Icc 1 X) :
      |∑ d ∈ Finset.Ioc Y (X / a), f d| ≤ 2 * (X : ℝ) * b * (a : ℝ)⁻¹ := by
    by_cases hN : Y ≤ X / a
    · have heq : (∑ d ∈ Finset.Ioc Y (X / a), f d) =
          (∑ d ∈ Finset.Icc 1 (X / a), f d) - ∑ d ∈ Finset.Icc 1 Y, f d := by
        rw [show Finset.Icc 1 (X / a) = Finset.Ioc 0 (X / a) by ext n; simp; omega,
          show Finset.Icc 1 Y = Finset.Ioc 0 Y by ext n; simp; omega,
          ← Finset.sum_Ioc_consecutive f (Nat.zero_le Y) hN]
        ring
      rw [heq]
      calc
        _ ≤ |∑ d ∈ Finset.Icc 1 (X / a), f d| + |∑ d ∈ Finset.Icc 1 Y, f d| := by
          simpa only [Real.norm_eq_abs] using norm_sub_le
            (∑ d ∈ Finset.Icc 1 (X / a), f d) (∑ d ∈ Finset.Icc 1 Y, f d)
        _ ≤ ((X / a : ℕ) : ℝ) * b + (Y : ℝ) * b :=
          add_le_add (hprefix _ hN) (hprefix _ le_rfl)
        _ ≤ 2 * (((X / a : ℕ) : ℝ) * b) := by
          have h := mul_le_mul_of_nonneg_right (show (Y : ℝ) ≤ (X / a : ℕ) by exact_mod_cast hN) hb
          linarith
        _ ≤ 2 * ((X : ℝ) / a * b) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right Nat.cast_div_le hb) (by norm_num)
        _ = _ := by ring
    · rw [Finset.Ioc_eq_empty_of_le (by omega), Finset.sum_empty, abs_zero]
      positivity
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 X, |∑ d ∈ Finset.Ioc Y (X / a), f d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.Icc 1 X, 2 * (X : ℝ) * b * (a : ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = (2 * (X : ℝ) * b) * ∑ a ∈ Finset.Icc 1 X, (a : ℝ)⁻¹ :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Burgess.sum_Icc_inv_natCast_le_one_add_log X) (by positivity)

theorem abs_divisor_sum_sub_truncated_main_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {X Y : ℕ} (hYX : Y ≤ X) {b : ℝ} (hb : 0 ≤ b)
    (hprefix : ∀ n : ℕ, Y ≤ n → |∑ d ∈ Finset.Icc 1 n, f d| ≤ (n : ℝ) * b) :
    |(∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, f d) -
        (X : ℝ) * ∑ d ∈ Finset.Icc 1 Y, f d / (d : ℝ)| ≤
      (Y : ℝ) + 2 * (X : ℝ) * b * (1 + Real.log (X : ℝ)) := by
  rw [divisor_sum_hyperbola f hYX]
  have heq : (∑ d ∈ Finset.Icc 1 Y, ((X / d : ℕ) : ℝ) * f d) +
      (∑ a ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Ioc Y (X / a), f d) -
        (X : ℝ) * ∑ d ∈ Finset.Icc 1 Y, f d / (d : ℝ) =
      ((∑ d ∈ Finset.Icc 1 Y, ((X / d : ℕ) : ℝ) * f d) -
        (X : ℝ) * ∑ d ∈ Finset.Icc 1 Y, f d / (d : ℝ)) +
        (∑ a ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Ioc Y (X / a), f d) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add (abs_truncated_floor_error_le f hf X Y)
    (abs_hyperbola_tail_le f hb hprefix))

end Pollack17

end

/-! ## Nonvanishing for the quadratic Stepanov construction

Source module `ErdosProblems.Erdos1141.StepanovBox`. -/

noncomputable section

namespace Pollack17.Stepanov

open Polynomial

open scoped BigOperators

variable {K : Type*} [Field K] {p A : ℕ}

def LowResidueSupport (p A : ℕ) (P : K[X]) : Prop :=
  ∀ n : ℕ, P.coeff n ≠ 0 → n % p < A

theorem choose_cast_eq_zero_of_residue_lt [Fact p.Prime] [CharP K p]
    {n k : ℕ} (h : n % p < k % p) :
    (n.choose k : K) = 0 := by
  have hmod := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := n) (k := k)
  rw [Nat.choose_eq_zero_of_lt h, zero_mul] at hmod
  exact (CharP.cast_eq_zero_iff K p _).mpr (Nat.modEq_zero_iff_dvd.mp hmod)

theorem LowResidueSupport.taylor [Fact p.Prime] [CharP K p]
    {P : K[X]} (hP : LowResidueSupport p A P) (x : K) :
    LowResidueSupport p A (taylor x P) := by
  intro k hk
  by_contra hkle
  have hkA : A ≤ k % p := Nat.le_of_not_gt hkle
  apply hk
  rw [taylor_coeff, hasseDeriv_apply, Polynomial.sum_def, eval_finsetSum]
  apply Finset.sum_eq_zero
  intro n hn
  have hnA := hP n (Polynomial.mem_support_iff.mp hn)
  have hchoose : (n.choose k : K) = 0 := choose_cast_eq_zero_of_residue_lt (hnA.trans_le hkA)
  simp [hchoose]

theorem LowResidueSupport.rootMultiplicity_mod_lt [Fact p.Prime] [CharP K p] {P : K[X]}
    (hP : LowResidueSupport p A P) (hP0 : P ≠ 0) (x : K) :
    P.rootMultiplicity x % p < A := by
  have hT : Polynomial.taylor x P ≠ 0 := (Polynomial.taylor_eq_zero x P).not.mpr hP0
  have hcoeff : (Polynomial.taylor x P).coeff (Polynomial.taylor x P).natTrailingDegree ≠ 0 :=
    Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT
  have hres := hP.taylor x _ hcoeff
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
  exact hres

theorem rootMultiplicity_neg_eq (P : K[X]) (x : K) :
    (-P).rootMultiplicity x = P.rootMultiplicity x := by
  simp only [Polynomial.rootMultiplicity_eq_natTrailingDegree, neg_comp,
    Polynomial.natTrailingDegree_neg]

theorem rootMultiplicity_pow_eq {f : K[X]} (hf : f ≠ 0) (x : K) (t : ℕ) :
    (f ^ t).rootMultiplicity x = t * f.rootMultiplicity x := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hf) hf), ih]
    ring

theorem add_pow_mul_ne_zero [Fact p.Prime] [CharP K p] {P Q f : K[X]} {x : K} {t : ℕ}
    (hP : LowResidueSupport p A P) (hQ : LowResidueSupport p A Q)
    (hne : P ≠ 0 ∨ Q ≠ 0) (hf : f ≠ 0) (hx : f.rootMultiplicity x = 1)
    (hAt : A ≤ t) (htA : t + A ≤ p) :
    P + f ^ t * Q ≠ 0 := by
  intro hzero
  have hQ0 : Q ≠ 0 := by
    intro hQzero
    have hPzero : P = 0 := by simpa [hQzero] using hzero
    exact hne.elim (fun h => h hPzero) (fun h => h hQzero)
  have hP0 : P ≠ 0 := by
    intro hPzero
    have hprod : f ^ t * Q = 0 := by simpa [hPzero] using hzero
    exact mul_ne_zero (pow_ne_zero _ hf) hQ0 hprod
  have hPmod := hP.rootMultiplicity_mod_lt hP0 x
  have hQmod := hQ.rootMultiplicity_mod_lt hQ0 x
  have hmult : P.rootMultiplicity x = t + Q.rootMultiplicity x := by
    rw [eq_neg_of_add_eq_zero_left hzero, rootMultiplicity_neg_eq,
      Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hf) hQ0),
      rootMultiplicity_pow_eq hf x t, hx, mul_one]
  have htlt : t < p := by omega
  have hsumlt : t + Q.rootMultiplicity x % p < p := by omega
  have hmod : P.rootMultiplicity x % p = t + Q.rootMultiplicity x % p := by
    rw [hmult, Nat.add_mod, Nat.mod_eq_of_lt htlt, Nat.mod_eq_of_lt hsumlt]
  omega

def boxExponent (p : ℕ) {A B : ℕ} (i : Fin A × Fin B) : ℕ := i.1 + p * i.2

theorem boxExponent_mod {A B : ℕ} (hA : A ≤ p) (i : Fin A × Fin B) :
    boxExponent p i % p = i.1 := by
  simp [boxExponent, Nat.add_mod, Nat.mod_eq_of_lt (i.1.isLt.trans_le hA)]

theorem boxExponent_injective {A B : ℕ} (hA : A ≤ p) :
    Function.Injective (boxExponent p : Fin A × Fin B → ℕ) := by
  intro i j hij
  have ha : (i.1 : ℕ) = j.1 := by
    simpa only [boxExponent_mod hA] using congrArg (fun n => n % p) hij
  have hp0 : 0 < p := (Nat.zero_le _).trans_lt (i.1.isLt.trans_le hA)
  have hmul : p * (i.2 : ℕ) = p * (j.2 : ℕ) := by
    simpa only [boxExponent, ha, Nat.add_left_cancel_iff] using hij
  exact Prod.ext (Fin.ext ha) (Fin.ext (Nat.eq_of_mul_eq_mul_left hp0 hmul))

noncomputable def boxPolynomial {A B : ℕ} (a : Fin A × Fin B → K) : K[X] :=
  ∑ i : Fin A × Fin B, monomial (boxExponent p i) (a i)

theorem boxPolynomial_coeff {A B : ℕ} (hA : A ≤ p)
    (a : Fin A × Fin B → K) (i : Fin A × Fin B) :
    (boxPolynomial (p := p) a).coeff (boxExponent p i) = a i := by
  classical
  rw [boxPolynomial, finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne := (boxExponent_injective hA).ne hji
    simp [coeff_monomial, hne]
  · simp

theorem boxPolynomial_injective {A B : ℕ} (hA : A ≤ p) :
    Function.Injective (boxPolynomial (K := K) (p := p) (A := A) (B := B)) := by
  intro a b hab
  funext i
  simpa only [boxPolynomial_coeff hA] using
    congrArg (fun P : K[X] => P.coeff (boxExponent p i)) hab

theorem boxPolynomial_lowResidueSupport {A B : ℕ} (hA : A ≤ p)
    (a : Fin A × Fin B → K) : LowResidueSupport p A (boxPolynomial (p := p) a) := by
  classical
  intro n hn
  by_contra hnot
  apply hn
  rw [boxPolynomial, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  have hne : boxExponent p i ≠ n := by
    intro h
    have : n % p = i.1 := h ▸ boxExponent_mod hA i
    exact hnot (this ▸ i.1.isLt)
  simp [coeff_monomial, hne]

theorem boxPolynomial_ne_zero {A B : ℕ} (hA : A ≤ p)
    {a : Fin A × Fin B → K} (ha : a ≠ 0) : boxPolynomial (p := p) a ≠ 0 := by
  intro h
  apply ha
  apply boxPolynomial_injective (K := K) hA
  simpa [boxPolynomial] using h

theorem box_auxiliary_ne_zero [Fact p.Prime] [CharP K p]
    {A B t : ℕ} {a b : Fin A × Fin B → K}
    (hab : a ≠ 0 ∨ b ≠ 0) {f : K[X]} {x : K}
    (hf : f ≠ 0) (hx : f.rootMultiplicity x = 1)
    (hAt : A ≤ t) (htA : t + A ≤ p) :
    boxPolynomial (p := p) a + f ^ t * boxPolynomial (p := p) b ≠ 0 := by
  have hAp : A ≤ p := by omega
  exact add_pow_mul_ne_zero (boxPolynomial_lowResidueSupport hAp a)
    (boxPolynomial_lowResidueSupport hAp b)
    (hab.imp (boxPolynomial_ne_zero hAp) (boxPolynomial_ne_zero hAp))
    hf hx hAt htA

end Pollack17.Stepanov

end

/-! ## Reduced derivatives for the quadratic Stepanov polynomial

Source module `ErdosProblems.Erdos1141.StepanovDerivative`. -/

noncomputable section

namespace Pollack17.Stepanov

open Polynomial

variable {K : Type*} [Field K]

noncomputable def reducedDerivative (f : K[X]) (t : K) (g : K[X]) : ℕ → K[X]
  | 0 => g
  | k + 1 => f * (reducedDerivative f t g k).derivative +
      C (t - k) * f.derivative * reducedDerivative f t g k

theorem mul_derivative_pow (f : K[X]) (k : ℕ) :
    f * (f ^ k).derivative = C (k : K) * f ^ k * f.derivative := by
  cases k with
  | zero => simp
  | succ k =>
    rw [derivative_pow_succ, pow_succ]
    push_cast
    ring

theorem mul_derivative_pow_mul (f g : K[X]) (k : ℕ) :
    f * (f ^ k * g).derivative =
      C (k : K) * f ^ k * f.derivative * g + f ^ (k + 1) * g.derivative := by
  rw [derivative_mul, mul_add, ← mul_assoc, mul_derivative_pow]
  rw [pow_succ]
  ring

theorem pow_mul_iterate_derivative (f g : K[X]) (t k : ℕ) :
    f ^ k * derivative^[k] (f ^ t * g) =
      f ^ t * reducedDerivative f (t : K) g k := by
  induction k with
  | zero => simp [reducedDerivative]
  | succ k ih =>
    have hderiv := congrArg (fun P : K[X] => f * P.derivative) ih
    rw [mul_derivative_pow_mul, mul_derivative_pow_mul] at hderiv
    simp only [map_natCast] at hderiv
    rw [Function.iterate_succ_apply', reducedDerivative]
    simp only [map_sub, map_natCast]
    linear_combination hderiv - (k : K[X]) * f.derivative * ih

theorem reducedDerivative_natDegree_le (f g : K[X]) (t : K) (k : ℕ) :
    (reducedDerivative f t g k).natDegree ≤ g.natDegree + k * f.natDegree := by
  induction k with
  | zero => simp [reducedDerivative]
  | succ k ih =>
    rw [reducedDerivative]
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · have hderiv := (Polynomial.natDegree_derivative_le
        (reducedDerivative f t g k)).trans (Nat.sub_le _ _)
      have hmul := Polynomial.natDegree_mul_le
        (p := f) (q := (reducedDerivative f t g k).derivative)
      nlinarith
    · have hderiv := (Polynomial.natDegree_derivative_le f).trans (Nat.sub_le _ _)
      have hconst := Polynomial.natDegree_C_mul_le (t - (k : K)) f.derivative
      have hmul := Polynomial.natDegree_mul_le
        (p := C (t - (k : K)) * f.derivative) (q := reducedDerivative f t g k)
      nlinarith

theorem iterate_derivative_mul_of_derivative_zero (g H : K[X])
    (hH : H.derivative = 0) (k : ℕ) :
    derivative^[k] (g * H) = derivative^[k] g * H := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', ih, derivative_mul, hH]

theorem derivative_frobenius_monomial {p : ℕ} [CharP K p] (b : ℕ) :
    (X ^ (p * b) : K[X]).derivative = 0 := by
  rw [derivative_X_pow]
  simp [Nat.cast_mul]

theorem eval_pow_mul_iterate_derivative_frobenius {p : ℕ} [CharP K p]
    (f g : K[X]) (t k b : ℕ) (x : K) (hx : x ^ p = x) :
    f.eval x ^ k * (derivative^[k] ((f ^ t * g) * X ^ (p * b))).eval x =
      f.eval x ^ t * (reducedDerivative f (t : K) g k).eval x * x ^ b := by
  rw [iterate_derivative_mul_of_derivative_zero _ _ (derivative_frobenius_monomial b)]
  simp only [eval_mul, eval_pow, eval_X]
  rw [pow_mul, hx, ← mul_assoc]
  have h := congrArg (fun P : K[X] => P.eval x) (pow_mul_iterate_derivative f g t k)
  simpa only [eval_mul, eval_pow] using congrArg (fun z : K => z * x ^ b) h

end Pollack17.Stepanov

end

/-! ## The linear conditions in the quadratic Stepanov argument

Source module `ErdosProblems.Erdos1141.StepanovConditions`. -/

noncomputable section

namespace Pollack17.Stepanov

open Polynomial

open scoped BigOperators

variable {K : Type*} [Field K] {p A B D : ℕ}

abbrev BoxPair (K : Type*) (A B : ℕ) :=
  (Fin A × Fin B → K) × (Fin A × Fin B → K)

noncomputable def conditionHalf (f : K[X]) (t : K) (k : ℕ)
    (a : Fin A × Fin B → K) : K[X] :=
  ∑ i : Fin A × Fin B,
    a i • (reducedDerivative f t (X ^ (i.1 : ℕ)) k * X ^ (i.2 : ℕ))

noncomputable def conditionPolynomial (f : K[X]) (t : K) (k : ℕ)
    (a : BoxPair K A B) : K[X] := conditionHalf f 0 k a.1 + conditionHalf f t k a.2

theorem conditionHalf_natDegree_le (f : K[X]) (t : K) (k : ℕ)
    (a : Fin A × Fin B → K) :
    (conditionHalf f t k a).natDegree ≤ A + B + k * f.natDegree := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  apply (Polynomial.natDegree_smul_le _ _).trans
  have hred := reducedDerivative_natDegree_le f (X ^ (i.1 : ℕ)) t k
  have hmul := Polynomial.natDegree_mul_le
    (p := reducedDerivative f t (X ^ (i.1 : ℕ)) k) (q := X ^ (i.2 : ℕ))
  simp only [natDegree_X_pow] at hred hmul
  have ha := i.1.isLt
  have hb := i.2.isLt
  omega

theorem conditionPolynomial_natDegree_le (f : K[X]) (t : K) (k : ℕ)
    (a : BoxPair K A B) :
    (conditionPolynomial f t k a).natDegree ≤ A + B + k * f.natDegree := by
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le (conditionHalf_natDegree_le f 0 k a.1) (conditionHalf_natDegree_le f t k a.2))

theorem conditionPolynomial_add (f : K[X]) (t : K) (k : ℕ)
    (a b : BoxPair K A B) :
    conditionPolynomial f t k (a + b) =
      conditionPolynomial f t k a + conditionPolynomial f t k b := by
  simp [conditionPolynomial, conditionHalf, add_smul, Finset.sum_add_distrib,
    add_add_add_comm]

theorem conditionPolynomial_smul (f : K[X]) (t : K) (k : ℕ)
    (c : K) (a : BoxPair K A B) :
    conditionPolynomial f t k (c • a) = c • conditionPolynomial f t k a := by
  simp [conditionPolynomial, conditionHalf, Finset.smul_sum, smul_add, smul_smul]

noncomputable def conditionLinear (f : K[X]) (t : K) (A B D H : ℕ) :
    BoxPair K A B →ₗ[K] (Fin D → Fin H → K) where
  toFun a k j := (conditionPolynomial f t k a).coeff j
  map_add' a b := by
    funext k j
    rw [conditionPolynomial_add, coeff_add]
    rfl
  map_smul' c a := by
    funext k j
    rw [conditionPolynomial_smul, coeff_smul]
    rfl

theorem exists_nonzero_condition_kernel (f : K[X]) (t : K) (A B D H : ℕ)
    (hdim : D * H < 2 * A * B) :
    ∃ a : BoxPair K A B, a ≠ 0 ∧ conditionLinear f t A B D H a = 0 := by
  let T := conditionLinear f t A B D H
  have hker : LinearMap.ker T ≠ ⊥ := by
    intro hbot
    have hle := T.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hbot)
    have hsource : Module.finrank K (BoxPair K A B) = 2 * A * B := by
      simp [BoxPair, Module.finrank_prod]
      ring
    have htarget : Module.finrank K (Fin D → Fin H → K) = D * H := by
      simp [Module.finrank_pi_fintype]
    rw [hsource, htarget] at hle
    exact (not_le_of_gt hdim) hle
  obtain ⟨a, ha, hane⟩ := (LinearMap.ker T).ne_bot_iff.mp hker
  exact ⟨a, hane, ha⟩

theorem exists_nonzero_vanishing_conditions (f : K[X]) (t : K) (A B D : ℕ)
    (hdim : D * (A + B + D * f.natDegree + 1) < 2 * A * B) :
    ∃ a : BoxPair K A B, a ≠ 0 ∧
      ∀ k : ℕ, k < D → conditionPolynomial f t k a = 0 := by
  let H := A + B + D * f.natDegree + 1
  obtain ⟨a, ha, hkernel⟩ := exists_nonzero_condition_kernel f t A B D H hdim
  refine ⟨a, ha, ?_⟩
  intro k hk
  have hdegree : (conditionPolynomial f t k a).natDegree < H := by
    have hdeg := conditionPolynomial_natDegree_le f t k a
    have hmul := Nat.mul_le_mul_right f.natDegree hk.le
    omega
  ext n
  rw [coeff_zero]
  by_cases hn : n < H
  · exact congrFun (congrFun hkernel ⟨k, hk⟩) ⟨n, hn⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdegree.trans_le (Nat.le_of_not_gt hn))

theorem pow_mul_boxPolynomial_eq_sum (f : K[X]) (t : ℕ)
    (a : Fin A × Fin B → K) :
    f ^ t * boxPolynomial (p := p) a =
      ∑ i : Fin A × Fin B, a i • ((f ^ t * X ^ (i.1 : ℕ)) * X ^ (p * i.2)) := by
  classical
  rw [boxPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← C_mul_X_pow_eq_monomial, boxExponent, pow_add, smul_eq_C_mul]
  ring

theorem eval_conditionHalf {p : ℕ} [CharP K p]
    (f : K[X]) (t k : ℕ) (a : Fin A × Fin B → K) (x : K) (hx : x ^ p = x) :
    f.eval x ^ k * (derivative^[k] (f ^ t * boxPolynomial (p := p) a)).eval x =
      f.eval x ^ t * (conditionHalf f (t : K) k a).eval x := by
  classical
  rw [pow_mul_boxPolynomial_eq_sum, Polynomial.iterate_derivative_sum]
  simp only [Polynomial.iterate_derivative_smul, eval_finsetSum, eval_smul,
    conditionHalf, eval_mul, eval_pow, eval_X]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := eval_pow_mul_iterate_derivative_frobenius f (X ^ (i.1 : ℕ)) t k i.2 x hx
  change f.eval x ^ k * (a i * _) = f.eval x ^ t * (a i * (_ * _))
  linear_combination a i * h

theorem eval_conditionPolynomial {p : ℕ} [CharP K p]
    (f : K[X]) (t k : ℕ) (a : BoxPair K A B) (x : K)
    (hx : x ^ p = x) (hft : f.eval x ^ t = 1) :
    f.eval x ^ k *
        (derivative^[k] (boxPolynomial (p := p) a.1 + f ^ t * boxPolynomial (p := p) a.2)).eval x =
      (conditionPolynomial f (t : K) k a).eval x := by
  have h0 := eval_conditionHalf f 0 k a.1 x hx
  have ht := eval_conditionHalf f t k a.2 x hx
  simp only [pow_zero, one_mul, Nat.cast_zero] at h0
  rw [hft, one_mul] at ht
  have hsum : derivative^[k]
      (boxPolynomial (p := p) a.1 + f ^ t * boxPolynomial (p := p) a.2) =
      derivative^[k] (boxPolynomial (p := p) a.1) +
        derivative^[k] (f ^ t * boxPolynomial (p := p) a.2) :=
    iterate_map_add Polynomial.derivative k _ _
  rw [hsum, eval_add, mul_add, h0, ht, conditionPolynomial, eval_add]

end Pollack17.Stepanov

end

/-! ## Root counting for the quadratic Stepanov polynomial

Source module `ErdosProblems.Erdos1141.StepanovRootCount`. -/

noncomputable section

namespace Pollack17.Stepanov

open Polynomial

open scoped BigOperators

variable {K : Type*} [Field K]

theorem le_rootMultiplicity_of_derivatives {p D : ℕ} [Fact p.Prime] [CharP K p]
    {P : K[X]} {x : K} (hP : P ≠ 0) (hDp : D ≤ p)
    (hvanish : ∀ k : ℕ, k < D → (derivative^[k] P).eval x = 0) :
    D ≤ P.rootMultiplicity x := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
  apply Polynomial.le_natTrailingDegree
  · exact (Polynomial.taylor_eq_zero x P).not.mpr hP
  · intro k hk
    change (Polynomial.taylor x P).coeff k = 0
    rw [Polynomial.taylor_coeff]
    have hfact : (k.factorial : K) ≠ 0 := by
      rw [ne_eq, CharP.cast_eq_zero_iff K p, (Fact.out : p.Prime).dvd_factorial, not_le]
      exact hk.trans_le hDp
    have hscaled := congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) k) P
    have heval := congrArg (fun Q : K[X] => Q.eval x) hscaled
    simp only [nsmul_eq_mul, Module.End.mul_apply, Module.End.natCast_apply,
      nsmul_eq_mul, eval_mul, eval_natCast] at heval
    rw [hvanish k hk] at heval
    exact (mul_eq_zero.mp heval).resolve_left hfact

theorem mul_card_le_natDegree_of_derivatives {p D : ℕ} [Fact p.Prime] [CharP K p]
    {P : K[X]} (hP : P ≠ 0) (hDp : D ≤ p) (S : Finset K)
    (hvanish : ∀ x ∈ S, ∀ k : ℕ, k < D → (derivative^[k] P).eval x = 0) :
    D * S.card ≤ P.natDegree := by
  classical
  by_cases hD : D = 0
  · simp [hD]
  have hmult (x : K) (hx : x ∈ S) : D ≤ P.rootMultiplicity x :=
    le_rootMultiplicity_of_derivatives hP hDp (hvanish x hx)
  have hsubset : S ⊆ P.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, ← Multiset.count_pos, Polynomial.count_roots]
    exact (Nat.pos_of_ne_zero hD).trans_le (hmult x hx)
  calc
    D * S.card = ∑ _x ∈ S, D := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ S, P.rootMultiplicity x := Finset.sum_le_sum hmult
    _ = ∑ x ∈ S, P.roots.count x := by simp only [Polynomial.count_roots]
    _ ≤ ∑ x ∈ P.roots.toFinset, P.roots.count x := Finset.sum_le_sum_of_subset hsubset
    _ = P.roots.card := Multiset.toFinset_sum_count_eq P.roots
    _ ≤ P.natDegree := Polynomial.card_roots' P

theorem boxPolynomial_natDegree_le {p A B : ℕ} (a : Fin A × Fin B → K) :
    (boxPolynomial (p := p) a).natDegree ≤ A + p * B := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  apply (Polynomial.natDegree_monomial_le (a i)).trans
  dsimp [boxExponent]
  have hmul := Nat.mul_le_mul_left p i.2.isLt.le
  have ha := i.1.isLt.le
  omega

theorem quadratic_fiber_card_bound {p A B D t : ℕ} [Fact p.Prime] [CharP K p]
    (f : K[X]) {x₀ : K} (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1)
    (hAt : A ≤ t) (htA : t + A ≤ p) (hDp : D ≤ p)
    (hdim : D * (A + B + D * f.natDegree + 1) < 2 * A * B)
    (S : Finset K)
    (hS : ∀ x ∈ S, x ^ p = x ∧ f.eval x ≠ 0 ∧ f.eval x ^ t = 1) :
    D * S.card ≤ A + p * B + t * f.natDegree := by
  classical
  obtain ⟨a, ha, hcond⟩ := exists_nonzero_vanishing_conditions f (t : K) A B D hdim
  have hpair : a.1 ≠ 0 ∨ a.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (Prod.ext h.1 h.2)
  let F := boxPolynomial (p := p) a.1 + f ^ t * boxPolynomial (p := p) a.2
  have hF : F ≠ 0 := box_auxiliary_ne_zero hpair hf hroot hAt htA
  have hdeg : F.natDegree ≤ A + p * B + t * f.natDegree := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact (boxPolynomial_natDegree_le a.1).trans (Nat.le_add_right _ _)
    · have hmul := Polynomial.natDegree_mul_le
        (p := f ^ t) (q := boxPolynomial (p := p) a.2)
      rw [Polynomial.natDegree_pow] at hmul
      have hb := boxPolynomial_natDegree_le (p := p) a.2
      omega
  apply (mul_card_le_natDegree_of_derivatives hF hDp S ?_).trans hdeg
  intro x hx k hk
  obtain ⟨hxp, hfx, hft⟩ := hS x hx
  have heval := eval_conditionPolynomial f t k a x hxp hft
  rw [hcond k hk, eval_zero] at heval
  exact (mul_eq_zero.mp heval).resolve_left (pow_ne_zero _ hfx)

end Pollack17.Stepanov

end

/-! ## Parameters for the quadratic Stepanov construction

Source module `ErdosProblems.Erdos1141.StepanovParameters`. -/

noncomputable section

namespace Pollack17.Stepanov

open Polynomial

theorem constraints_lt_coefficients {A B D d : ℕ}
    (hB : 1 ≤ B) (hD : D + 1 = 2 * B) (hA : 4 * (d + 1) * B ^ 2 < A) :
    D * (A + B + D * d + 1) < 2 * A * B := by
  have hDle : D ≤ 2 * B := by omega
  have hDd : D * d ≤ 2 * B * d := Nat.mul_le_mul_right d hDle
  have hinner : B + D * d + 1 ≤ 2 * B * (d + 1) := by nlinarith
  have hcost : D * (B + D * d + 1) ≤ 4 * (d + 1) * B ^ 2 := by
    calc
      D * (B + D * d + 1) ≤ (2 * B) * (2 * B * (d + 1)) :=
        Nat.mul_le_mul hDle hinner
      _ = _ := by ring
  have hDA : D * A + A = 2 * A * B := by
    calc
      D * A + A = (D + 1) * A := by ring
      _ = 2 * A * B := by rw [hD]; ring
  calc
    D * (A + B + D * d + 1) = D * A + D * (B + D * d + 1) := by ring
    _ < D * A + A := Nat.add_lt_add_left (hcost.trans_lt hA) _
    _ = 2 * A * B := hDA

theorem half_characteristic_parameters {p B d : ℕ} (hp : 0 < p) (hB : 1 ≤ B)
    (hsmall : 16 * (d + 1) * B ^ 2 ≤ p) :
    let A := (p - 1) / 2
    let D := 2 * B - 1
    A + A ≤ p ∧ D ≤ p ∧ D * (A + B + D * d + 1) < 2 * A * B := by
  dsimp only
  let A := (p - 1) / 2
  let D := 2 * B - 1
  have hdiv := Nat.div_mul_le_self (p - 1) 2
  have hmod := Nat.mod_add_div (p - 1) 2
  have hmodlt := Nat.mod_lt (p - 1) (by norm_num : 0 < 2)
  have hAlower : p ≤ 2 * A + 2 := by dsimp [A]; omega
  have hAupper : A + A ≤ p := by dsimp [A]; omega
  have hD : D + 1 = 2 * B := by dsimp [D]; omega
  have hBsq : B ≤ B ^ 2 := by nlinarith
  have hterm : 1 ≤ (d + 1) * B ^ 2 := by
    change 0 < (d + 1) * B ^ 2
    positivity
  have hprod : B ^ 2 ≤ (d + 1) * B ^ 2 := by
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hlarge : 4 * (d + 1) * B ^ 2 < A := by nlinarith
  have hDp : D ≤ p := by nlinarith
  exact ⟨hAupper, hDp, constraints_lt_coefficients hB hD hlarge⟩

theorem quadratic_fiber_card_bound_small_square
    {K : Type*} [Field K] {p B : ℕ} [Fact p.Prime] [CharP K p]
    (f : K[X]) {x₀ : K} (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1)
    (hB : 1 ≤ B) (hsmall : 16 * (f.natDegree + 1) * B ^ 2 ≤ p)
    (S : Finset K)
    (hS : ∀ x ∈ S, x ^ p = x ∧ f.eval x ≠ 0 ∧ f.eval x ^ ((p - 1) / 2) = 1) :
    2 * (2 * B - 1) * S.card ≤ p * (2 * B - 1) + p * (f.natDegree + 2) := by
  obtain ⟨hA, hDp, hdim⟩ := half_characteristic_parameters
    (Fact.out : p.Prime).pos hB hsmall
  have hcount := quadratic_fiber_card_bound f hf hroot le_rfl hA hDp hdim S hS
  have hD : (2 * B - 1) + 1 = 2 * B := by omega
  have hAd := Nat.mul_le_mul_right f.natDegree hA
  nlinarith

end Pollack17.Stepanov

end

/-! ## Quadratic character sums of polynomials with a simple root

Source module `ErdosProblems.Erdos1141.StepanovCharacterSum`. -/

noncomputable section

namespace Pollack17.Stepanov

open Polynomial

open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

noncomputable def residueFiber (f : (ZMod p)[X]) : Finset (ZMod p) :=
  Finset.univ.filter fun x => quadraticChar (ZMod p) (f.eval x) = 1

noncomputable def zeroFiber (f : (ZMod p)[X]) : Finset (ZMod p) :=
  Finset.univ.filter fun x => f.eval x = 0

noncomputable def polynomialCharacterSum (f : (ZMod p)[X]) : ℝ :=
  ∑ x : ZMod p, (quadraticChar (ZMod p) (f.eval x) : ℝ)

theorem polynomialCharacterSum_eq_fibers (f : (ZMod p)[X]) :
    polynomialCharacterSum f = 2 * (residueFiber f).card + (zeroFiber f).card - p := by
  classical
  have hpoint (x : ZMod p) : (quadraticChar (ZMod p) (f.eval x) : ℝ) =
      2 * (if quadraticChar (ZMod p) (f.eval x) = 1 then (1 : ℝ) else 0) +
        (if f.eval x = 0 then 1 else 0) - 1 := by
    by_cases hx : f.eval x = 0
    · simp [hx]
    · rcases quadraticChar_dichotomy hx with h | h <;> norm_num [h, hx]
  have hres : (∑ x : ZMod p,
      if quadraticChar (ZMod p) (f.eval x) = 1 then (1 : ℝ) else 0) = (residueFiber f).card := by
    simp [residueFiber]
  have hzero : (∑ x : ZMod p, if f.eval x = 0 then (1 : ℝ) else 0) = (zeroFiber f).card := by
    simp [zeroFiber]
  simp only [polynomialCharacterSum, hpoint, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, hres, hzero]
  simp

theorem zeroFiber_card_le {f : (ZMod p)[X]} (hf : f ≠ 0) :
    (zeroFiber f).card ≤ f.natDegree := by
  classical
  have hsubset : zeroFiber f ⊆ f.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
    exact (Finset.mem_filter.mp hx).2
  exact ((Finset.card_le_card hsubset).trans (Multiset.toFinset_card_le _)).trans
    (Polynomial.card_roots' f)

theorem residueFiber_spec (f : (ZMod p)[X]) (hp2 : p ≠ 2)
    {x : ZMod p} (hx : x ∈ residueFiber f) :
    x ^ p = x ∧ f.eval x ≠ 0 ∧ f.eval x ^ ((p - 1) / 2) = 1 := by
  have hchar := (Finset.mem_filter.mp hx).2
  have hfx : f.eval x ≠ 0 := by
    intro hzero
    simp [hzero] at hchar
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hpow := quadraticChar_eq_pow_of_char_ne_two' hF (f.eval x)
  have hodd := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hhalf : p / 2 = (p - 1) / 2 := by
    have := Nat.odd_iff.mp hodd
    omega
  refine ⟨?_, hfx, ?_⟩
  · simp
  · simpa only [hchar, Int.cast_one, ZMod.card, hhalf] using hpow.symm

theorem polynomialCharacterSum_le_of_small_square {B : ℕ}
    (f : (ZMod p)[X]) {x₀ : ZMod p} (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1)
    (hp2 : p ≠ 2) (hB : 1 ≤ B) (hsmall : 16 * (f.natDegree + 1) * B ^ 2 ≤ p) :
    polynomialCharacterSum f ≤
      (p : ℝ) * (f.natDegree + 2) / (2 * B - 1 : ℕ) + f.natDegree := by
  have hcount := quadratic_fiber_card_bound_small_square f hf hroot hB hsmall
    (residueFiber f) (fun _ hx => residueFiber_spec f hp2 hx)
  have hcountR : (2 : ℝ) * (2 * B - 1 : ℕ) * (residueFiber f).card ≤
      (p : ℝ) * (2 * B - 1 : ℕ) + (p : ℝ) * (f.natDegree + 2) := by
    exact_mod_cast hcount
  have hzeros : ((zeroFiber f).card : ℝ) ≤ f.natDegree := by exact_mod_cast zeroFiber_card_le hf
  have hDpos : (0 : ℝ) < (2 * B - 1 : ℕ) := by exact_mod_cast (show 0 < 2 * B - 1 by omega)
  have hquot : (2 : ℝ) * (residueFiber f).card - p ≤
      (p : ℝ) * (f.natDegree + 2) / (2 * B - 1 : ℕ) := by
    apply (le_div_iff₀ hDpos).mpr
    nlinarith
  rw [polynomialCharacterSum_eq_fibers]
  linarith

theorem abs_polynomialCharacterSum_le_of_small_square {B : ℕ}
    (f : (ZMod p)[X]) {x₀ : ZMod p} (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1)
    (hp2 : p ≠ 2) (hB : 1 ≤ B) (hsmall : 16 * (f.natDegree + 1) * B ^ 2 ≤ p) :
    |polynomialCharacterSum f| ≤
      (p : ℝ) * (f.natDegree + 2) / (2 * B - 1 : ℕ) + f.natDegree := by
  have hu := polynomialCharacterSum_le_of_small_square f hf hroot hp2 hB hsmall
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hF
  have ha0 : a ≠ 0 := by
    intro hzero
    simp [hzero] at ha
  let g := C a * f
  have hg : g ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr ha0) hf
  have hgroot : g.rootMultiplicity x₀ = 1 := by
    rw [Polynomial.rootMultiplicity_mul hg, Polynomial.rootMultiplicity_C, hroot, zero_add]
  have hgdegree : g.natDegree = f.natDegree := by
    rw [Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr ha0) hf, natDegree_C, zero_add]
  have hl := polynomialCharacterSum_le_of_small_square g hg hgroot hp2 hB
    (by simpa only [hgdegree] using hsmall)
  have hsum : polynomialCharacterSum g = -polynomialCharacterSum f := by
    simp [polynomialCharacterSum, g, map_mul, ha, Finset.sum_neg_distrib]
  rw [hgdegree, hsum] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

theorem abs_polynomialCharacterSum_le_card (f : (ZMod p)[X]) :
    |polynomialCharacterSum f| ≤ p := by
  have hpoint (x : ZMod p) : |(quadraticChar (ZMod p) (f.eval x) : ℝ)| ≤ 1 := by
    rcases quadraticChar_isQuadratic (ZMod p) (f.eval x) with h | h | h <;> norm_num [h]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun x _ => hpoint x)).trans_eq (by simp))

end Pollack17.Stepanov

end

/-! ## A square-root bound with a degree-dependent constant

Source module `ErdosProblems.Erdos1141.StepanovSqrt`. -/

noncomputable section

namespace Pollack17.Stepanov

open Polynomial

def simpleRootConstant (d : ℕ) : ℕ :=
  32 * (d + 1) + 64 * (d + 1) * (d + 2) + d

theorem sqrt_div_square_small (p c : ℕ) (hc : 0 < c) :
    c * (Nat.sqrt p / c) ^ 2 ≤ p := by
  have hdiv : c * (Nat.sqrt p / c) ≤ Nat.sqrt p := by
    simpa only [mul_comm] using Nat.div_mul_le_self (Nat.sqrt p) c
  have hc2 : c ≤ c ^ 2 := by nlinarith
  calc
    c * (Nat.sqrt p / c) ^ 2 ≤ c ^ 2 * (Nat.sqrt p / c) ^ 2 :=
      Nat.mul_le_mul_right _ hc2
    _ = (c * (Nat.sqrt p / c)) ^ 2 := by ring
    _ ≤ (Nat.sqrt p) ^ 2 := Nat.pow_le_pow_left hdiv 2
    _ ≤ p := Nat.sqrt_le' p

theorem modulus_le_sqrt_mul_div {p c : ℕ} (hp : 0 < p) (hc : 0 < c)
    (hB : 1 ≤ Nat.sqrt p / c) :
    (p : ℝ) ≤ 4 * c * ((Nat.sqrt p / c : ℕ) : ℝ) * Real.sqrt p := by
  let B := Nat.sqrt p / c
  have hmod := Nat.mod_add_div (Nat.sqrt p) c
  have hmodlt := Nat.mod_lt (Nat.sqrt p) hc
  have hfloor : Nat.sqrt p + 1 ≤ c * (B + 1) := by dsimp [B]; nlinarith
  have hnext : Nat.sqrt p + 1 ≤ 2 * c * B := by
    calc
      Nat.sqrt p + 1 ≤ c * (B + 1) := hfloor
      _ ≤ c * (2 * B) := Nat.mul_le_mul_left c (by omega)
      _ = _ := by ring
  have hpn : p ≤ 2 * c * B * (Nat.sqrt p + 1) := by
    calc
      p ≤ (Nat.sqrt p + 1) ^ 2 := (Nat.lt_succ_sqrt' p).le
      _ ≤ (2 * c * B) * (Nat.sqrt p + 1) := by
        simpa only [pow_two] using Nat.mul_le_mul_right (Nat.sqrt p + 1) hnext
  have hpr : (p : ℝ) ≤ 2 * c * B * ((Nat.sqrt p : ℝ) + 1) := by exact_mod_cast hpn
  have hs0 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg _)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hs1 : 1 ≤ Real.sqrt (p : ℝ) := by nlinarith
  have hl2 : (Nat.sqrt p : ℝ) ^ 2 ≤ p := by exact_mod_cast Nat.sqrt_le' p
  have hl : (Nat.sqrt p : ℝ) ≤ Real.sqrt p := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.sqrt p)]
  calc
    (p : ℝ) ≤ 2 * c * B * ((Nat.sqrt p : ℝ) + 1) := hpr
    _ ≤ 2 * c * B * (2 * Real.sqrt p) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

theorem abs_polynomialCharacterSum_le_sqrt
    {p : ℕ} [Fact p.Prime] (f : (ZMod p)[X]) {x₀ : ZMod p}
    (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1) :
    |polynomialCharacterSum f| ≤ (simpleRootConstant f.natDegree : ℝ) * Real.sqrt p := by
  let d := f.natDegree
  let c := 16 * (d + 1)
  let B := Nat.sqrt p / c
  have hc : 0 < c := by dsimp [c]; positivity
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hs0 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs1 : 1 ≤ Real.sqrt (p : ℝ) := by nlinarith
  have hC : (simpleRootConstant d : ℝ) =
      2 * c + 4 * c * (d + 2) + d := by
    simp only [simpleRootConstant, c, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  by_cases hlarge : 2 * c ≤ Nat.sqrt p
  · have hB2 : 2 ≤ B := (Nat.le_div_iff_mul_le hc).mpr (by simpa only [mul_comm] using hlarge)
    have hB : 1 ≤ B := by omega
    have hp2 : p ≠ 2 := by
      have hsp := Nat.sqrt_le_self p
      have hc16 : 16 ≤ c := by dsimp [c]; omega
      omega
    have hsmall : 16 * (f.natDegree + 1) * B ^ 2 ≤ p := sqrt_div_square_small p c hc
    have hraw := abs_polynomialCharacterSum_le_of_small_square f hf hroot hp2 hB hsmall
    have hpb : (p : ℝ) ≤ 4 * c * B * Real.sqrt p := modulus_le_sqrt_mul_div hp hc hB
    have hDB : (B : ℝ) ≤ (2 * B - 1 : ℕ) := by exact_mod_cast (show B ≤ 2 * B - 1 by omega)
    have hD0 : (0 : ℝ) < (2 * B - 1 : ℕ) := by exact_mod_cast (show 0 < 2 * B - 1 by omega)
    have hpD : (p : ℝ) ≤ 4 * c * (2 * B - 1 : ℕ) * Real.sqrt p := by
      apply hpb.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hDB (by positivity)) hs0
    have hquot : (p : ℝ) * (d + 2) / (2 * B - 1 : ℕ) ≤
        4 * c * (d + 2) * Real.sqrt p := by
      apply (div_le_iff₀ hD0).mpr
      have h := mul_le_mul_of_nonneg_right hpD (show (0 : ℝ) ≤ d + 2 by positivity)
      nlinarith
    have hd : (d : ℝ) ≤ d * Real.sqrt p := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hs1 (Nat.cast_nonneg d)
    calc
      |polynomialCharacterSum f| ≤ (p : ℝ) * (d + 2) / (2 * B - 1 : ℕ) + d := hraw
      _ ≤ 4 * c * (d + 2) * Real.sqrt p + d * Real.sqrt p := add_le_add hquot hd
      _ ≤ (simpleRootConstant d : ℝ) * Real.sqrt p := by
        rw [hC]
        have : 0 ≤ 2 * (c : ℝ) * Real.sqrt p := by positivity
        nlinarith
  · have hnext : Nat.sqrt p + 1 ≤ 2 * c := by omega
    have hpbound : p ≤ (2 * c) ^ 2 :=
      (Nat.lt_succ_sqrt' p).le.trans (Nat.pow_le_pow_left hnext 2)
    have hpboundR : (p : ℝ) ≤ (2 * c) ^ 2 := by exact_mod_cast hpbound
    have hsr : Real.sqrt (p : ℝ) ≤ 2 * c := by
      nlinarith [Nat.cast_nonneg (α := ℝ) c]
    have hpc : (p : ℝ) ≤ 2 * c * Real.sqrt p := by nlinarith
    calc
      |polynomialCharacterSum f| ≤ p := abs_polynomialCharacterSum_le_card f
      _ ≤ 2 * c * Real.sqrt p := hpc
      _ ≤ (simpleRootConstant d : ℝ) * Real.sqrt p := by
        rw [hC]
        apply mul_le_mul_of_nonneg_right _ hs0
        have : 0 ≤ 4 * (c : ℝ) * (d + 2) + d := by positivity
        linarith

end Pollack17.Stepanov

end

/-! ## Arbitrary moments of shifted quadratic character sums

Source module `ErdosProblems.Erdos1141.BurgessMoments`. -/

noncomputable section

namespace Pollack17.Burgess

open Polynomial

open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

noncomputable def qchar (x : ZMod p) : ℝ := (quadraticChar (ZMod p) x : ℝ)

noncomputable def shiftPolynomial {n : ℕ} (v : Fin n → ZMod p) : (ZMod p)[X] :=
  ∏ i : Fin n, (X + C (v i))

theorem shiftPolynomial_ne_zero {n : ℕ} (v : Fin n → ZMod p) : shiftPolynomial v ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact Polynomial.X_add_C_ne_zero (v i)

theorem shiftPolynomial_natDegree {n : ℕ} (v : Fin n → ZMod p) :
    (shiftPolynomial v).natDegree = n := by
  rw [shiftPolynomial, Polynomial.natDegree_prod]
  · simp
  · intro i _
    exact Polynomial.X_add_C_ne_zero (v i)

theorem shiftPolynomial_simple_root {n : ℕ} (v : Fin n → ZMod p) (i : Fin n)
    (hsingle : ∀ j : Fin n, j ≠ i → v j ≠ v i) :
    (shiftPolynomial v).rootMultiplicity (-v i) = 1 := by
  classical
  let Q : (ZMod p)[X] := ∏ j ∈ Finset.univ.erase i, (X + C (v j))
  have hfactor : shiftPolynomial v = (X + C (v i)) * Q := by
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hQeval : Q.eval (-v i) ≠ 0 := by
    simp only [Q, eval_prod, eval_add, eval_X, eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hne := hsingle j (Finset.mem_erase.mp hj).1
    simpa only [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr hne
  have hQroot : Q.rootMultiplicity (-v i) = 0 := Polynomial.rootMultiplicity_eq_zero hQeval
  have hmul : (X + C (v i)) * Q ≠ 0 := hfactor ▸ shiftPolynomial_ne_zero v
  rw [hfactor, Polynomial.rootMultiplicity_mul hmul, hQroot, add_zero]
  simpa only [map_neg, sub_neg_eq_add] using
    (Polynomial.rootMultiplicity_X_sub_C_self (x := -v i))

theorem correlation_le_of_singleton {n : ℕ} (v : Fin n → ZMod p)
    (hsingle : ∃ i : Fin n, ∀ j : Fin n, j ≠ i → v j ≠ v i) :
    |∑ x : ZMod p, qchar (∏ i : Fin n, (x + v i))| ≤
      (Stepanov.simpleRootConstant n : ℝ) * Real.sqrt p := by
  obtain ⟨i, hi⟩ := hsingle
  have h := Stepanov.abs_polynomialCharacterSum_le_sqrt (shiftPolynomial v)
    (shiftPolynomial_ne_zero v) (shiftPolynomial_simple_root v i hi)
  rw [shiftPolynomial_natDegree] at h
  simpa only [Stepanov.polynomialCharacterSum, shiftPolynomial, eval_prod,
    eval_add, eval_X, eval_C, qchar] using h

end Pollack17.Burgess

end

/-! ## Counting tuples with no singleton entry

Source module `ErdosProblems.Erdos1141.RepeatedTuples`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

def RepeatedTuple {α : Type*} {n : ℕ} (v : Fin n → α) : Prop :=
  ∀ i : Fin n, ∃ j : Fin n, j ≠ i ∧ v j = v i

theorem repeatedTuple_image_card {α : Type*} [DecidableEq α] {n : ℕ}
    (v : Fin n → α) (hv : RepeatedTuple v) :
    2 * (Finset.univ.image v).card ≤ n := by
  have hfiber (a : α) (ha : a ∈ Finset.univ.image v) :
      2 ≤ (Finset.univ.filter fun i => v i = a).card := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hji, hval⟩ := hv i
    apply Finset.one_lt_card.mpr
    exact ⟨i, by simp, j, by simp [hval], hji.symm⟩
  calc
    2 * (Finset.univ.image v).card = ∑ _a ∈ Finset.univ.image v, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ a ∈ Finset.univ.image v, (Finset.univ.filter fun i => v i = a).card :=
      Finset.sum_le_sum hfiber
    _ = n := by simpa using (Finset.card_eq_sum_card_image v Finset.univ).symm

theorem exists_tuple_factorization {α : Type*} [DecidableEq α] {n r : ℕ}
    (hn : 0 < n) (v : Fin n → α) (hcard : (Finset.univ.image v).card ≤ r) :
    ∃ a : Fin r → α, ∃ b : Fin n → Fin r, v = a ∘ b := by
  classical
  let S := Finset.univ.image v
  let e : S ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp)
  let z : Fin n → S := fun i => ⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  let b : Fin n → Fin r := fun i => ⟨(e (z i)).val, (e (z i)).isLt.trans_le hcard⟩
  let a : Fin r → α := fun j =>
    if h : j.val < S.card then (e.symm ⟨j.val, h⟩).val else v ⟨0, hn⟩
  refine ⟨a, b, ?_⟩
  funext i
  dsimp only [Function.comp_apply, a, b]
  rw [dif_pos (e (z i)).isLt]
  exact (congrArg Subtype.val (e.symm_apply_apply (z i))).symm

noncomputable def repeatedTuples (α : Type*) [Fintype α] (n : ℕ) : Finset (Fin n → α) := by
  classical
  exact Finset.univ.filter RepeatedTuple

theorem repeatedTuples_card_le (α : Type*) [Fintype α] (r : ℕ) :
    (repeatedTuples α (2 * r)).card ≤ (Fintype.card α) ^ r * r ^ (2 * r) := by
  classical
  by_cases hr : r = 0
  · subst r
    simpa [repeatedTuples] using
      (Finset.card_filter_le (Finset.univ : Finset (Fin 0 → α)) RepeatedTuple)
  let T : Finset ((Fin r → α) × (Fin (2 * r) → Fin r)) := Finset.univ
  let compose : ((Fin r → α) × (Fin (2 * r) → Fin r)) → (Fin (2 * r) → α) :=
    fun ab => ab.1 ∘ ab.2
  have hsubset : repeatedTuples α (2 * r) ⊆ T.image compose := by
    intro v hv
    have hrep : RepeatedTuple v := (Finset.mem_filter.mp hv).2
    have htwice := repeatedTuple_image_card v hrep
    have hcard : (Finset.univ.image v).card ≤ r := by omega
    obtain ⟨a, b, hab⟩ := exists_tuple_factorization (by omega : 0 < 2 * r) v hcard
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, hab.symm⟩
  calc
    (repeatedTuples α (2 * r)).card ≤ (T.image compose).card := Finset.card_le_card hsubset
    _ ≤ T.card := Finset.card_image_le
    _ = (Fintype.card α) ^ r * r ^ (2 * r) := by simp [T]

end Pollack17.Burgess

end

/-! ## Products of local quadratic characters

Source module `ErdosProblems.Erdos1141.QuadraticCRT`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

def primeModulus (s : Finset ℕ) : ℕ := ∏ p ∈ s, p

theorem primeModulus_pos (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    0 < primeModulus s := Finset.prod_pos (fun p hp => (hs p hp).pos)

theorem primeSet_pairwise (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Pairwise (fun p r : s => Nat.Coprime (p : ℕ) (r : ℕ)) := by
  intro p r hpr
  exact (hs p p.property).coprime_iff_not_dvd.mpr fun hdvd =>
    hpr (Subtype.ext ((Nat.prime_dvd_prime_iff_eq (hs p p.property)
      (hs r r.property)).mp hdvd))

noncomputable def primeCRT (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ZMod (primeModulus s) ≃+* (∀ p : s, ZMod (p : ℕ)) := by
  have hprod : primeModulus s = ∏ p : s, (p : ℕ) :=
    (Finset.prod_attach s (fun p : ℕ => p)).symm
  exact (ZMod.ringEquivCongr hprod).trans
    (ZMod.prodEquivPi (fun p : s => (p : ℕ)) (primeSet_pairwise s hs))

theorem primeCRT_natCast (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (n : ℕ) (p : s) :
    primeCRT s hs (n : ZMod (primeModulus s)) p = (n : ZMod (p : ℕ)) := by
  simp [primeCRT]

noncomputable def localChar (p : ℕ) (hp : p.Prime) (x : ZMod p) : ℝ :=
  @qchar p ⟨hp⟩ x

noncomputable def productChar (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (x : ZMod (primeModulus s)) : ℝ :=
  ∏ p : s, localChar p (hs p p.property) (primeCRT s hs x p)

theorem productChar_mul (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (a b : ZMod (primeModulus s)) :
    productChar s hs (a * b) = productChar s hs a * productChar s hs b := by
  simp [productChar, localChar, qchar, map_mul, Finset.prod_mul_distrib]

theorem abs_localChar_le_one (p : ℕ) (hp : p.Prime) (x : ZMod p) :
    |localChar p hp x| ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rcases quadraticChar_isQuadratic (ZMod p) x with h | h | h <;>
    norm_num [localChar, qchar, h]

theorem abs_productChar_le_one (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (x : ZMod (primeModulus s)) : |productChar s hs x| ≤ 1 := by
  rw [productChar, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) fun p _ =>
    abs_localChar_le_one p (hs p p.property) _

theorem productChar_complete_correlation (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] [(p : s) → NeZero (p : ℕ)] {n : ℕ} (v : Fin n → ℕ) :
    (∑ x : ZMod (primeModulus s),
        productChar s hs (∏ i : Fin n, (x + v i))) =
      ∏ p : s, ∑ y : ZMod (p : ℕ),
        localChar p (hs p p.property) (∏ i : Fin n, (y + v i)) := by
  let e := primeCRT s hs
  calc
    _ = ∑ y : (∀ p : s, ZMod (p : ℕ)),
        ∏ p : s, localChar p (hs p p.property) (∏ i : Fin n, (y p + v i)) := by
      rw [← e.toEquiv.sum_comp]
      apply Finset.sum_congr rfl
      intro x _
      rw [productChar]
      apply Fintype.prod_congr
      intro p
      congr 1
      simp [e]
    _ = _ := by rw [Fintype.prod_sum]

theorem prod_prime_gcd (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (d : ℕ) :
    (∏ p ∈ s, p.gcd d) = (primeModulus s).gcd d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [primeModulus]
  | @insert p s hp ih =>
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (Finset.mem_insert_of_mem hr)
    have hpp : p.Prime := hs p (Finset.mem_insert_self p s)
    have hcop : p.Coprime (primeModulus s) := Nat.Coprime.prod_right fun r hr =>
      hpp.coprime_iff_not_dvd.mpr fun hdvd =>
        hp ((Nat.prime_dvd_prime_iff_eq hpp (hs' r hr)).mp hdvd ▸ hr)
    rw [Finset.prod_insert hp, ih hs']
    rw [show primeModulus (insert p s) = p * primeModulus s from Finset.prod_insert hp]
    rw [Nat.gcd_comm (p * primeModulus s), hcop.gcd_mul d,
      Nat.gcd_comm d p, Nat.gcd_comm d (primeModulus s)]

end Pollack17.Burgess

end

/-! ## Subpower losses from the number of prime factors

Source module `ErdosProblems.Erdos1141.BurgessSubpower`. -/

noncomputable section

namespace Pollack17.Burgess

open Filter

open scoped BigOperators

lemma factorial_card_le_prod_of_one_le (s : Finset ℕ)
    (hs : ∀ x ∈ s, 1 ≤ x) :
    Nat.factorial s.card ≤ ∏ x ∈ s, x := by
  classical
  let f : Fin s.card ↪o ℕ := s.orderEmbOfFin rfl
  have hidx : ∀ i : ℕ, ∀ hi : i < s.card, i + 1 ≤ f ⟨i, hi⟩ := by
    intro i hi
    induction i with
    | zero =>
        have hmem : f ⟨0, hi⟩ ∈ s := by
          simp [f]
        simpa [f] using hs (f ⟨0, hi⟩) hmem
    | succ i ih =>
        have hi' : i < s.card := Nat.lt_of_succ_lt hi
        have hprev : i + 1 ≤ f ⟨i, hi'⟩ := ih hi'
        have hlt : f ⟨i, hi'⟩ < f ⟨i + 1, hi⟩ := by
          exact f.strictMono (Nat.lt_succ_self i)
        exact le_trans (Nat.succ_le_succ hprev) (Nat.succ_le_of_lt hlt)
  have hprod : (∏ i : Fin s.card, (i.1 + 1)) ≤ ∏ i : Fin s.card, f i := by
    refine Finset.prod_le_prod' ?_
    intro i _
    exact hidx i.1 i.2
  have hleft : (∏ i : Fin s.card, (i.1 + 1)) = Nat.factorial s.card := by
    calc
      (∏ i : Fin s.card, (i.1 + 1)) =
          ∏ i ∈ Finset.range s.card, (i + 1) := by
        simpa using (Fin.prod_univ_eq_prod_range (fun i : ℕ => i + 1) s.card)
      _ = Nat.factorial s.card := Finset.prod_range_add_one_eq_factorial s.card
  have hright : (∏ i : Fin s.card, f i) = ∏ x ∈ s, x := by
    calc
      (∏ i : Fin s.card, f i) =
          ∏ x ∈ Finset.map (s.orderEmbOfFin rfl).toEmbedding Finset.univ, x := by
        symm
        simpa [f] using
          (Finset.prod_map (s := Finset.univ)
            (e := (s.orderEmbOfFin rfl).toEmbedding) (f := fun x : ℕ => x))
      _ = ∏ x ∈ s, x := by
        rw [Finset.map_orderEmbOfFin_univ (s := s) (h := rfl)]
  calc
    Nat.factorial s.card = ∏ i : Fin s.card, (i.1 + 1) := hleft.symm
    _ ≤ ∏ i : Fin s.card, f i := hprod
    _ = ∏ x ∈ s, x := hright

lemma factorial_card_primeFactors_le (n : ℕ) (hn : n ≠ 0) :
    Nat.factorial n.primeFactors.card ≤ n := by
  have hprod : Nat.factorial n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
    factorial_card_le_prod_of_one_le _ (by
      intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).one_le)
  exact hprod.trans
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n))

theorem const_pow_primeFactors_card_le_rpow_eventually
    (b m : ℕ) (hb : 1 ≤ b) (hm : 0 < m) :
    ∃ Nω : ℕ, ∀ {n : ℕ}, Nω ≤ n →
      (b : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) ^ ((1 : ℝ) / m) := by
  have hfact : ∀ᶠ k : ℕ in atTop, (b ^ m) ^ k < Nat.factorial (k - 1) := by
    simpa using (Nat.eventually_pow_lt_factorial_sub (b ^ m) 1)
  rcases eventually_atTop.mp hfact with ⟨k₀, hk₀⟩
  refine ⟨max 3 ((b ^ k₀) ^ m), ?_⟩
  intro n hn
  let k := n.primeFactors.card
  have hn3 : 3 ≤ n := (Nat.le_max_left _ _).trans hn
  have hnpos : 0 < n := by omega
  by_cases hk_small : k < k₀
  · have hk_le : k ≤ k₀ := hk_small.le
    have hpow_nat : (b ^ k : ℕ) ≤ b ^ k₀ :=
      Nat.pow_le_pow_right (by omega : 0 < b) hk_le
    have hpow_real : (b : ℝ) ^ k ≤ (b : ℝ) ^ k₀ := by
      exact_mod_cast hpow_nat
    have hconst_nat : ((b ^ k₀ : ℕ) ^ m) ≤ n :=
      (Nat.le_max_right _ _).trans hn
    have hconst_real : (((b : ℝ) ^ k₀) ^ m) ≤ (n : ℝ) := by
      exact_mod_cast hconst_nat
    have hroot_le :
        (((b : ℝ) ^ k₀) ^ m) ^ ((1 : ℝ) / m) ≤
          (n : ℝ) ^ ((1 : ℝ) / m) := by
      exact Real.rpow_le_rpow (by positivity) hconst_real (by positivity)
    have hroot :
        (((b : ℝ) ^ k₀) ^ m) ^ ((1 : ℝ) / m) = (b : ℝ) ^ k₀ := by
      simpa [one_div] using
        Real.pow_rpow_inv_natCast (show 0 ≤ (b : ℝ) ^ k₀ by positivity)
          (Nat.ne_of_gt hm)
    rw [hroot] at hroot_le
    exact hpow_real.trans hroot_le
  · have hk_ge : k₀ ≤ k := Nat.le_of_not_gt hk_small
    have hmain_nat : (b ^ m) ^ k < Nat.factorial k := by
      exact (hk₀ k hk_ge).trans_le (Nat.factorial_le (Nat.sub_le _ _))
    have hk_fact_le_n : Nat.factorial k ≤ n := by
      simpa [k] using factorial_card_primeFactors_le n (Nat.ne_of_gt hnpos)
    have hpowm_nat' : (b ^ m) ^ k ≤ n :=
      (Nat.le_of_lt hmain_nat).trans hk_fact_le_n
    have hpowm_nat : (b ^ k : ℕ) ^ m ≤ n := by
      calc
        (b ^ k : ℕ) ^ m = b ^ (k * m) := by rw [pow_mul]
        _ = b ^ (m * k) := by rw [Nat.mul_comm]
        _ = (b ^ m) ^ k := by rw [pow_mul]
        _ ≤ n := hpowm_nat'
    have hpowm_real : (((b : ℝ) ^ k) ^ m) ≤ (n : ℝ) := by
      exact_mod_cast hpowm_nat
    have hroot_le :
        (((b : ℝ) ^ k) ^ m) ^ ((1 : ℝ) / m) ≤
          (n : ℝ) ^ ((1 : ℝ) / m) := by
      exact Real.rpow_le_rpow (by positivity) hpowm_real (by positivity)
    have hroot :
        (((b : ℝ) ^ k) ^ m) ^ ((1 : ℝ) / m) = (b : ℝ) ^ k := by
      simpa [one_div] using
        Real.pow_rpow_inv_natCast (show 0 ≤ (b : ℝ) ^ k by positivity)
          (Nat.ne_of_gt hm)
    rw [hroot] at hroot_le
    exact hroot_le

theorem primeModulus_primeFactors (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (primeModulus s).primeFactors = s := Nat.primeFactors_prod hs

theorem primeModulus_card_divisors (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (primeModulus s).divisors.card = 2 ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [primeModulus]
  | @insert p s hp ih =>
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (Finset.mem_insert_of_mem hr)
    have hpp : p.Prime := hs p (Finset.mem_insert_self p s)
    have hcop : p.Coprime (primeModulus s) := Nat.Coprime.prod_right fun r hr =>
      hpp.coprime_iff_not_dvd.mpr fun hdvd =>
        hp ((Nat.prime_dvd_prime_iff_eq hpp (hs' r hr)).mp hdvd ▸ hr)
    rw [show primeModulus (insert p s) = p * primeModulus s from Finset.prod_insert hp,
      hcop.card_divisors_mul, ih hs', Finset.card_insert_of_notMem hp, pow_succ', hpp.divisors]
    have hpne : p ≠ 1 := hpp.ne_one
    simp [Ne.symm hpne]

theorem eventually_const_pow_primeFactors_le (b : ℕ) (hb : 1 ≤ b)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, (b : ℝ) ^ q.primeFactors.card ≤ (q : ℝ) ^ δ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
  have hmpos : 0 < m := by
    have hreal : 0 < (m : ℝ) := lt_trans (one_div_pos.mpr hδ) hm
    exact_mod_cast hreal
  have hexp : (1 : ℝ) / m ≤ δ := by
    have hprod : 1 < (m : ℝ) * δ := (div_lt_iff₀ hδ).mp hm
    exact (div_le_iff₀ (by exact_mod_cast hmpos : 0 < (m : ℝ))).mpr (by nlinarith)
  obtain ⟨Q, hQ⟩ := const_pow_primeFactors_card_le_rpow_eventually b m hb hmpos
  filter_upwards [eventually_ge_atTop Q, eventually_ge_atTop 1] with q hq hq1
  exact (hQ hq).trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq1) hexp)

theorem eventually_const_mul_pow_primeFactors_le (K : ℝ) (b : ℕ) (hb : 1 ≤ b)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, K * (b : ℝ) ^ q.primeFactors.card ≤ (q : ℝ) ^ δ := by
  have hp := eventually_const_pow_primeFactors_le b hb (half_pos hδ)
  have hK : ∀ᶠ q : ℕ in atTop, K ≤ (q : ℝ) ^ (δ / 2) :=
    ((tendsto_rpow_atTop (half_pos hδ)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop K)
  filter_upwards [hp, hK, eventually_ge_atTop 1] with q hq hKq hq1
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq1
  calc
    K * (b : ℝ) ^ q.primeFactors.card ≤
        (q : ℝ) ^ (δ / 2) * (q : ℝ) ^ (δ / 2) :=
      mul_le_mul hKq hq (pow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hqpos.le _)
    _ = (q : ℝ) ^ δ := by rw [← Real.rpow_add hqpos]; congr 1; ring

end Pollack17.Burgess

end

/-! ## Elementary estimates for the power scales in Burgess averaging

Source module `ErdosProblems.Erdos1141.BurgessPowerScales`. -/

noncomputable section

namespace Pollack17.Burgess

open Filter

theorem eventually_const_mul_rpow_le {C d a b : ℝ} (hd : 0 < d) (hab : a < b) :
    ∀ᶠ q : ℕ in atTop, C * (q : ℝ) ^ a ≤ d * (q : ℝ) ^ b := by
  have hlarge := ((tendsto_rpow_atTop (sub_pos.mpr hab)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (C / d))
  filter_upwards [hlarge, eventually_ge_atTop 1] with q hq hq1
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq1
  have hratio : C ≤ d * (q : ℝ) ^ (b - a) := by
    simpa only [mul_comm, Function.comp_apply] using (div_le_iff₀ hd).mp hq
  calc
    _ ≤ (d * (q : ℝ) ^ (b - a)) * (q : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hq0.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hq0]; congr 2; ring

theorem eventually_floor_rpow_bounds {a : ℝ} (ha : 0 < a) :
    ∀ᶠ q : ℕ in atTop,
      (q : ℝ) ^ a / 2 ≤ (⌊(q : ℝ) ^ a⌋₊ : ℝ) ∧
        (⌊(q : ℝ) ^ a⌋₊ : ℝ) ≤ (q : ℝ) ^ a := by
  have hlarge := ((tendsto_rpow_atTop ha).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop 2)
  filter_upwards [hlarge] with q hq
  change 2 ≤ (q : ℝ) ^ a at hq
  refine ⟨?_, Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg q) _)⟩
  have hfloor := Nat.lt_floor_add_one ((q : ℝ) ^ a)
  linarith

theorem ceil_rpow_bounds {a : ℝ} (ha : 0 ≤ a) {q : ℕ} (hq : 1 ≤ q) :
    (q : ℝ) ^ a ≤ (⌈(q : ℝ) ^ a⌉₊ : ℝ) ∧
      (⌈(q : ℝ) ^ a⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ a := by
  have hpow : (1 : ℝ) ≤ (q : ℝ) ^ a := Real.one_le_rpow (by exact_mod_cast hq) ha
  refine ⟨Nat.le_ceil _, ?_⟩
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg q) a)
  linarith

theorem eventually_one_add_log_le_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, 1 + Real.log (q : ℝ) ≤ (q : ℝ) ^ δ := by
  have hcomp := eventually_const_mul_rpow_le
    (C := 1 + (δ / 2)⁻¹) (d := 1) (a := δ / 2) (b := δ) (by norm_num) (by linarith)
  filter_upwards [hcomp, eventually_ge_atTop 1] with q hq hq1
  have hpow : (1 : ℝ) ≤ (q : ℝ) ^ (δ / 2) :=
    Real.one_le_rpow (by exact_mod_cast hq1) (by linarith)
  have hlog := Real.log_natCast_le_rpow_div q (half_pos hδ)
  change Real.log (q : ℝ) ≤ (q : ℝ) ^ (δ / 2) * (δ / 2)⁻¹ at hlog
  have hbound : 1 + Real.log (q : ℝ) ≤
      (1 + (δ / 2)⁻¹) * (q : ℝ) ^ (δ / 2) := by
    nlinarith
  exact hbound.trans (by simpa only [one_mul] using hq)

end Pollack17.Burgess

end

/-! ## Averaging the gcd losses in composite-modulus correlations

Source module `ErdosProblems.Erdos1141.BurgessGcdAverage`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

theorem gcd_le_divisor_sum {q : ℕ} (hq : q ≠ 0) (n : ℕ) :
    q.gcd n ≤ ∑ d ∈ q.divisors, if d ∣ n then d else 0 := by
  have hg : q.gcd n ∈ q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left q n, hq⟩
  calc
    q.gcd n = (if q.gcd n ∣ n then q.gcd n else 0) := by simp [Nat.gcd_dvd_right]
    _ ≤ _ := Finset.single_le_sum (s := q.divisors)
      (f := fun d => if d ∣ n then d else 0) (fun _ _ => Nat.zero_le _) hg

theorem sum_gcd_Icc_le {q : ℕ} (hq : q ≠ 0) (V : ℕ) :
    (∑ n ∈ Finset.Icc 1 V, q.gcd n) ≤ V * q.divisors.card := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 V, ∑ d ∈ q.divisors, if d ∣ n then d else 0 :=
      Finset.sum_le_sum fun n _ => gcd_le_divisor_sum hq n
    _ = ∑ d ∈ q.divisors, ∑ n ∈ Finset.Icc 1 V, if d ∣ n then d else 0 :=
      Finset.sum_comm
    _ = ∑ d ∈ q.divisors, d * (V / d) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [← Finset.sum_filter]
      change (∑ _n ∈ positiveMultiplesUpTo d V, d) = _
      simp [positiveMultiplesUpTo_card, Nat.mul_comm]
    _ ≤ ∑ _d ∈ q.divisors, V :=
      Finset.sum_le_sum fun d _ => Nat.mul_div_le V d
    _ = _ := by simp [Nat.mul_comm]

theorem sum_gcd_dist_one_side_le {q V a : ℕ} (hq : q ≠ 0) (ha : a ≤ V)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 V)
    (hne : ∀ b ∈ S, b ≠ a)
    (hside : (∀ b ∈ S, b ≤ a) ∨ (∀ b ∈ S, a ≤ b)) :
    (∑ b ∈ S, q.gcd (Nat.dist a b)) ≤ V * q.divisors.card := by
  have hinj : Set.InjOn (Nat.dist a) S := by
    intro b hb c hc hbc
    rcases hside with hl | hr
    · have hb' := hl b hb
      have hc' := hl c hc
      rw [Nat.dist_eq_sub_of_le_right hb', Nat.dist_eq_sub_of_le_right hc'] at hbc
      omega
    · have hb' := hr b hb
      have hc' := hr c hc
      rw [Nat.dist_eq_sub_of_le hb', Nat.dist_eq_sub_of_le hc'] at hbc
      omega
  have hsub : S.image (Nat.dist a) ⊆ Finset.Icc 1 V := by
    intro n hn
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hn
    have hbV := (Finset.mem_Icc.mp (hS hb)).2
    have hbne := hne b hb
    simp only [Finset.mem_Icc, Nat.dist]
    omega
  calc
    _ = ∑ n ∈ S.image (Nat.dist a), q.gcd n := (Finset.sum_image hinj).symm
    _ ≤ ∑ n ∈ Finset.Icc 1 V, q.gcd n := Finset.sum_le_sum_of_subset hsub
    _ ≤ _ := sum_gcd_Icc_le hq V

theorem sum_gcd_dist_erase_le {q V a : ℕ} (hq : q ≠ 0) (ha : a ≤ V) :
    (∑ b ∈ (Finset.Icc 1 V).erase a, q.gcd (Nat.dist a b)) ≤
      2 * V * q.divisors.card := by
  let L := (Finset.Icc 1 V).filter (fun b => b < a)
  let R := (Finset.Icc 1 V).filter (fun b => a < b)
  have heq : (Finset.Icc 1 V).erase a = L ∪ R := by
    ext b
    simp only [Finset.mem_erase, L, R, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hdisj : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro b hbL hbR
    have hL := (Finset.mem_filter.mp hbL).2
    have hR := (Finset.mem_filter.mp hbR).2
    omega
  rw [heq, Finset.sum_union hdisj]
  have hL := sum_gcd_dist_one_side_le hq ha L (Finset.filter_subset _ _)
    (fun b hb => ne_of_lt (Finset.mem_filter.mp hb).2)
    (Or.inl (fun b hb => le_of_lt (Finset.mem_filter.mp hb).2))
  have hR := sum_gcd_dist_one_side_le hq ha R (Finset.filter_subset _ _)
    (fun b hb => ne_of_gt (Finset.mem_filter.mp hb).2)
    (Or.inr (fun b hb => le_of_lt (Finset.mem_filter.mp hb).2))
  nlinarith

theorem modEq_iff_dvd_dist (p a b : ℕ) : a ≡ b [MOD p] ↔ p ∣ Nat.dist a b := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab, Nat.modEq_iff_dvd' hab]
  · rw [Nat.dist_eq_sub_of_le_right hba, Nat.ModEq.comm, Nat.modEq_iff_dvd' hba]

end Pollack17.Burgess

end

/-! ## Complete composite correlations with gcd losses

Source module `ErdosProblems.Erdos1141.BurgessCompositeCorrelation`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

theorem simpleRootConstant_one_le (n : ℕ) : 1 ≤ Stepanov.simpleRootConstant n := by
  unfold Stepanov.simpleRootConstant
  omega

theorem local_correlation_le_gcd {p : ℕ} (hp : p.Prime) [NeZero p]
    {n : ℕ} (v : Fin n → ℕ) (i : Fin n) :
    |∑ x : ZMod p, localChar p hp (∏ j : Fin n, (x + v j))| ≤
      (Stepanov.simpleRootConstant n : ℝ) * Real.sqrt p *
        ∏ j ∈ Finset.univ.erase i, (p.gcd (Nat.dist (v i) (v j)) : ℝ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let g : Fin n → ℕ := fun j => p.gcd (Nat.dist (v i) (v j))
  have hg : ∀ j : Fin n, 1 ≤ g j := fun j => Nat.gcd_pos_of_pos_left _ hp.pos
  have hprod : (1 : ℝ) ≤ ∏ j ∈ Finset.univ.erase i, (g j : ℝ) := by
    exact_mod_cast Finset.one_le_prod' (s := Finset.univ.erase i) (fun j _ => hg j)
  have hbase : (1 : ℝ) ≤ (Stepanov.simpleRootConstant n : ℝ) * Real.sqrt p := by
    have hC : (1 : ℝ) ≤ Stepanov.simpleRootConstant n := by
      exact_mod_cast simpleRootConstant_one_le n
    have hS : (1 : ℝ) ≤ Real.sqrt p :=
      Real.one_le_sqrt.mpr (by exact_mod_cast hp.one_lt.le)
    nlinarith
  by_cases hsingle : ∀ j : Fin n, j ≠ i → (v j : ZMod p) ≠ v i
  · have hcorr := correlation_le_of_singleton (fun j => (v j : ZMod p)) ⟨i, hsingle⟩
    exact hcorr.trans (le_mul_of_one_le_right (le_trans zero_le_one hbase) hprod)
  · push Not at hsingle
    obtain ⟨j, hji, hval⟩ := hsingle
    have hdiv : p ∣ Nat.dist (v i) (v j) :=
      (modEq_iff_dvd_dist p (v i) (v j)).mp
        ((ZMod.natCast_eq_natCast_iff _ _ _).mp hval.symm)
    have hgj : g j = p := Nat.gcd_eq_left_iff_dvd.mpr hdiv
    have hpProd : (p : ℝ) ≤ ∏ j ∈ Finset.univ.erase i, (g j : ℝ) := by
      have h := Finset.single_le_prod' (s := Finset.univ.erase i)
        (fun j _ => hg j) (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
      rw [hgj] at h
      exact_mod_cast h
    have htrivial : |∑ x : ZMod p, localChar p hp (∏ j : Fin n, (x + v j))| ≤ p := by
      calc
        _ ≤ ∑ x : ZMod p, |localChar p hp (∏ j : Fin n, (x + v j))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _x : ZMod p, (1 : ℝ) :=
          Finset.sum_le_sum fun x _ => abs_localChar_le_one p hp _
        _ = _ := by simp
    exact htrivial.trans (hpProd.trans
      (le_mul_of_one_le_left (le_trans zero_le_one hprod) hbase))

theorem product_correlation_le_gcd (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] {n : ℕ} (v : Fin n → ℕ) (i : Fin n) :
    |∑ x : ZMod (primeModulus s), productChar s hs (∏ j : Fin n, (x + v j))| ≤
      (Stepanov.simpleRootConstant n : ℝ) ^ s.card * Real.sqrt (primeModulus s) *
        ∏ j ∈ Finset.univ.erase i, ((primeModulus s).gcd (Nat.dist (v i) (v j)) : ℝ) := by
  classical
  have : (p : s) → NeZero (p : ℕ) := fun p => ⟨(hs p p.property).ne_zero⟩
  rw [productChar_complete_correlation s hs v, Finset.abs_prod]
  refine (Finset.prod_le_prod (s := (Finset.univ : Finset s)) (fun _ _ => abs_nonneg _)
    (fun (p : s) _ => local_correlation_le_gcd (hs p p.property) v i)).trans_eq ?_
  simp only [Finset.prod_mul_distrib]
  have hC : (∏ _p : s, (Stepanov.simpleRootConstant n : ℝ)) =
      (Stepanov.simpleRootConstant n : ℝ) ^ s.card := by simp
  have hsqrt : (∏ p : s, Real.sqrt (p : ℕ)) = Real.sqrt (primeModulus s) := by
    rw [← Real.sqrt_prod _ (fun p _ => Nat.cast_nonneg _), ← Nat.cast_prod]
    congr 2
    exact Finset.prod_attach s (fun p : ℕ => p)
  have hgcd : (∏ p : s, ∏ j ∈ Finset.univ.erase i,
        ((p : ℕ).gcd (Nat.dist (v i) (v j)) : ℝ)) =
      ∏ j ∈ Finset.univ.erase i, ((primeModulus s).gcd (Nat.dist (v i) (v j)) : ℝ) := by
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro j _
    rw [← Nat.cast_prod]
    congr 1
    exact (Finset.prod_coe_sort s (fun p : ℕ => p.gcd (Nat.dist (v i) (v j)))).trans
      (prod_prime_gcd s hs _)
  rw [hC, hsqrt, hgcd]

end Pollack17.Burgess

end

/-! ## Summing independent difference weights around a distinguished tuple entry

Source module `ErdosProblems.Erdos1141.BurgessStarWeights`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

noncomputable def starWeight {α : Type*} {n : ℕ} (w : α → α → ℝ)
    (v : Fin n → α) (i : Fin n) : ℝ :=
  ∏ j : {j : Fin n // j ≠ i}, w (v i) (v j)

theorem starWeight_nonneg {α : Type*} {n : ℕ} (w : α → α → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (v : Fin n → α) (i : Fin n) :
    0 ≤ starWeight w v i := Finset.prod_nonneg fun _ _ => hw _ _

theorem starWeight_eq_prod_erase {α : Type*} {n : ℕ} (w : α → α → ℝ)
    (v : Fin n → α) (i : Fin n) :
    starWeight w v i = ∏ j ∈ Finset.univ.erase i, w (v i) (v j) := by
  exact (Finset.prod_subtype (p := fun j => j ≠ i)
    (Finset.univ.erase i) (by simp) (fun j => w (v i) (v j))).symm

theorem sum_starWeight {α : Type*} [Fintype α] {n : ℕ}
    (w : α → α → ℝ) (i : Fin n) :
    (∑ v : Fin n → α, starWeight w v i) =
      ∑ a : α, (∑ b : α, w a b) ^ (n - 1) := by
  classical
  let e := Equiv.funSplitAt i α
  let F : (α × ({j : Fin n // j ≠ i} → α)) → ℝ :=
    fun ab => ∏ j : {j : Fin n // j ≠ i}, w ab.1 (ab.2 j)
  have heq (v : Fin n → α) : starWeight w v i = F (e v) := rfl
  have hcard : Fintype.card {j : Fin n // j ≠ i} = n - 1 := by
    simp [Fintype.card_subtype_compl]
  calc
    _ = ∑ v : Fin n → α, F (e v) := Finset.sum_congr rfl fun v _ => heq v
    _ = ∑ ab, F ab := e.sum_comp F
    _ = ∑ a : α, ∑ b : ({j : Fin n // j ≠ i} → α),
        ∏ j : {j : Fin n // j ≠ i}, w a (b j) := Fintype.sum_prod_type _
    _ = ∑ a : α, ∏ _j : {j : Fin n // j ≠ i}, ∑ b : α, w a b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Fintype.prod_sum]
    _ = _ := by simp [hcard]

theorem sum_starWeight_le {α : Type*} [Fintype α] {n : ℕ}
    (w : α → α → ℝ) (hw : ∀ a b, 0 ≤ w a b) {B : ℝ}
    (hB : ∀ a : α, ∑ b : α, w a b ≤ B) (i : Fin n) :
    (∑ v : Fin n → α, starWeight w v i) ≤ (Fintype.card α : ℝ) * B ^ (n - 1) := by
  rw [sum_starWeight]
  calc
    _ ≤ ∑ _a : α, B ^ (n - 1) := Finset.sum_le_sum fun a _ =>
      pow_le_pow_left₀ (Finset.sum_nonneg fun b _ => hw a b) (hB a) _
    _ = _ := by simp

end Pollack17.Burgess

end

/-! ## An arbitrary-order moment bound from singleton correlation estimates

Source module `ErdosProblems.Erdos1141.BurgessTupleBound`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

theorem sum_tuple_correlations_le {α : Type*} [Fintype α] (r : ℕ)
    (corr : (Fin (2 * r) → α) → ℝ) (w : α → α → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) {B C T : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hrow : ∀ a, ∑ b : α, w a b ≤ T)
    (htrivial : ∀ v, corr v ≤ B)
    (hsingle : ∀ (v : Fin (2 * r) → α) (i : Fin (2 * r)),
      (∀ j, j ≠ i → v j ≠ v i) → corr v ≤ C * starWeight w v i) :
    (∑ v : Fin (2 * r) → α, corr v) ≤
      (Fintype.card α : ℝ) ^ r * (r : ℝ) ^ (2 * r) * B +
        C * (2 * r : ℕ) * (Fintype.card α : ℝ) * T ^ (2 * r - 1) := by
  classical
  have hpoint (v : Fin (2 * r) → α) :
      corr v ≤ (if RepeatedTuple v then B else 0) + C * ∑ i, starWeight w v i := by
    have hweight : 0 ≤ ∑ i, starWeight w v i :=
      Finset.sum_nonneg fun i _ => starWeight_nonneg w hw v i
    by_cases hv : RepeatedTuple v
    · rw [if_pos hv]
      exact (htrivial v).trans (le_add_of_nonneg_right (mul_nonneg hC hweight))
    · rw [if_neg hv, zero_add]
      have hsi : ∃ i : Fin (2 * r), ∀ j, j ≠ i → v j ≠ v i := by
        simpa only [RepeatedTuple, not_forall, not_exists, not_and] using hv
      obtain ⟨i, hi⟩ := hsi
      exact (hsingle v i hi).trans (mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun j _ => starWeight_nonneg w hw v j) (Finset.mem_univ i)) hC)
  have hdiag : (∑ v : Fin (2 * r) → α, if RepeatedTuple v then B else 0) ≤
      (Fintype.card α : ℝ) ^ r * (r : ℝ) ^ (2 * r) * B := by
    rw [← Finset.sum_filter]
    change (∑ _v ∈ repeatedTuples α (2 * r), B) ≤ _
    simp only [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ hB
    exact_mod_cast repeatedTuples_card_le α r
  have hweights : (∑ v : Fin (2 * r) → α, ∑ i, starWeight w v i) ≤
      (2 * r : ℕ) * (Fintype.card α : ℝ) * T ^ (2 * r - 1) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _i : Fin (2 * r), (Fintype.card α : ℝ) * T ^ (2 * r - 1) :=
        Finset.sum_le_sum fun i _ => sum_starWeight_le w hw hrow i
      _ = _ := by simp [mul_assoc]
  calc
    _ ≤ ∑ v : Fin (2 * r) → α,
        ((if RepeatedTuple v then B else 0) + C * ∑ i, starWeight w v i) :=
      Finset.sum_le_sum fun v _ => hpoint v
    _ = (∑ v : Fin (2 * r) → α, if RepeatedTuple v then B else 0) +
        C * ∑ v : Fin (2 * r) → α, ∑ i, starWeight w v i := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
      have h := add_le_add hdiag (mul_le_mul_of_nonneg_left hweights hC)
      simpa only [mul_assoc] using h

end Pollack17.Burgess

end

/-! ## Ratio energy with arbitrary coprime natural denominators

Source module `ErdosProblems.Erdos1141.BurgessEnergy`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

def naturalRatioWeight (q M H : ℕ) (D : Finset ℕ) (x : ZMod q) : ℕ :=
  ((Finset.range H ×ˢ D).filter fun iu =>
    (iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ) = x).card

noncomputable def naturalRatioEnergy (q M H : ℕ) [NeZero q] (D : Finset ℕ) : ℝ :=
  ∑ x : ZMod q, (naturalRatioWeight q M H D x : ℝ) ^ 2

theorem sum_naturalRatioWeight (q M H : ℕ) [NeZero q] (D : Finset ℕ) :
    ∑ x : ZMod q, naturalRatioWeight q M H D x = H * D.card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.range H ×ˢ D) (t := Finset.univ)
    (f := fun iu : ℕ × ℕ => (iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ)) (by simp)
  simpa only [Finset.card_product, Finset.card_range, naturalRatioWeight] using h.symm

theorem sum_naturalRatioWeight_mul (q M H : ℕ) [NeZero q]
    (D : Finset ℕ) (f : ZMod q → ℝ) :
    (∑ x : ZMod q, (naturalRatioWeight q M H D x : ℝ) * f x) =
      ∑ i ∈ Finset.range H, ∑ u ∈ D, f ((u : ZMod q)⁻¹ * (M + i : ℕ)) := by
  calc
    _ = ∑ iu ∈ Finset.range H ×ˢ D,
        f ((iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ)) := by
      rw [← Finset.sum_fiberwise' (Finset.range H ×ˢ D)
        (fun iu : ℕ × ℕ => (iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ)) f]
      apply Finset.sum_congr rfl
      intro x _
      simp [naturalRatioWeight, nsmul_eq_mul]
    _ = _ := Finset.sum_product _ _ _

theorem sum_card_fiber_sq_eq_card_collision
    {α β : Type*} [Fintype β] [DecidableEq β]
    (s : Finset α) (f : α → β) :
    (∑ y : β, ((s.filter fun a => f a = y).card) ^ 2) =
      (((s ×ˢ s).filter fun ab => f ab.1 = f ab.2).card) := by
  classical
  let c := (s ×ˢ s).filter fun ab => f ab.1 = f ab.2
  have hmap : (c : Set (α × α)).MapsTo (fun ab => f ab.1)
      (Finset.univ : Finset β) := by
    intro ab _
    exact Finset.mem_univ _
  change (∑ y : β, ((s.filter fun a => f a = y).card) ^ 2) = c.card
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro y _
  rw [pow_two, ← Finset.card_product]
  congr 1
  ext ab
  simp only [c, Finset.mem_product, Finset.mem_filter]
  aesop

theorem natural_inv_ratio_eq_iff {q n₁ n₂ u₁ u₂ : ℕ}
    (h₁ : u₁.Coprime q) (h₂ : u₂.Coprime q) :
    (u₁ : ZMod q)⁻¹ * n₁ = (u₂ : ZMod q)⁻¹ * n₂ ↔
      n₁ * u₂ ≡ n₂ * u₁ [MOD q] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, Nat.cast_mul]
  have hmul₁ := ZMod.coe_mul_inv_eq_one u₁ h₁
  have hmul₂ := ZMod.coe_mul_inv_eq_one u₂ h₂
  constructor
  · intro h
    calc
      (n₁ : ZMod q) * u₂ = ((u₁ : ZMod q) * (u₁ : ZMod q)⁻¹) * (n₁ * u₂) := by
        rw [hmul₁, one_mul]
      _ = ((u₁ : ZMod q) * u₂) * ((u₁ : ZMod q)⁻¹ * n₁) := by ring
      _ = ((u₁ : ZMod q) * u₂) * ((u₂ : ZMod q)⁻¹ * n₂) := by rw [h]
      _ = ((u₂ : ZMod q) * (u₂ : ZMod q)⁻¹) * (n₂ * u₁) := by ring
      _ = _ := by rw [hmul₂, one_mul]
  · intro h
    calc
      (u₁ : ZMod q)⁻¹ * n₁ = ((u₂ : ZMod q) * (u₂ : ZMod q)⁻¹) *
          ((u₁ : ZMod q)⁻¹ * n₁) := by rw [hmul₂, one_mul]
      _ = ((u₁ : ZMod q)⁻¹ * (u₂ : ZMod q)⁻¹) * (n₁ * u₂) := by ring
      _ = ((u₁ : ZMod q)⁻¹ * (u₂ : ZMod q)⁻¹) * (n₂ * u₁) := by rw [h]
      _ = ((u₁ : ZMod q) * (u₁ : ZMod q)⁻¹) * ((u₂ : ZMod q)⁻¹ * n₂) := by ring
      _ = _ := by rw [hmul₁, one_mul]

theorem naturalRatioEnergy_eq_sum (q M H : ℕ) [NeZero q] (D : Finset ℕ)
    (hD : ∀ u ∈ D, u.Coprime q) :
    naturalRatioEnergy q M H D =
      ((∑ u ∈ D, ∑ v ∈ D, (burgessIntervalCollision q M H u v).card : ℕ) : ℝ) := by
  let box := Finset.range H ×ˢ D
  have h := sum_card_fiber_sq_eq_card_collision box
    (fun iu : ℕ × ℕ => (iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ))
  have heq : ((box ×ˢ box).filter fun ab =>
      (ab.1.2 : ZMod q)⁻¹ * (M + ab.1.1 : ℕ) =
        (ab.2.2 : ZMod q)⁻¹ * (M + ab.2.1 : ℕ)) =
      ((box ×ˢ box).filter fun ab =>
        (M + ab.1.1) * ab.2.2 ≡ (M + ab.2.1) * ab.1.2 [MOD q]) := by
    apply Finset.filter_congr
    intro ab hab
    have hmem := Finset.mem_product.mp hab
    exact natural_inv_ratio_eq_iff
      (hD ab.1.2 (Finset.mem_product.mp hmem.1).2)
      (hD ab.2.2 (Finset.mem_product.mp hmem.2).2)
  rw [heq] at h
  have hcard : (((box ×ˢ box).filter fun ab =>
      (M + ab.1.1) * ab.2.2 ≡ (M + ab.2.1) * ab.1.2 [MOD q]).card) =
      ∑ u ∈ D, ∑ v ∈ D, (burgessIntervalCollision q M H u v).card := by
    simp only [box, burgessIntervalCollision, Finset.card_eq_sum_ones,
      Finset.sum_filter, Finset.sum_product]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    calc
      _ = ∑ i ∈ Finset.range H, ∑ v ∈ D, ∑ j ∈ Finset.range H,
          if (M + i) * v ≡ (M + j) * u [MOD q] then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := Finset.sum_comm
  rw [hcard] at h
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) h
  simpa only [naturalRatioEnergy, naturalRatioWeight, box, Nat.cast_sum,
    Nat.cast_pow] using hcast

theorem naturalRatioEnergy_le {q M H U : ℕ} [NeZero q] (D : Finset ℕ)
    (hD : D ⊆ Finset.Icc 1 U) (hcop : ∀ u ∈ D, u.Coprime q)
    (hH : 0 < H) (hU : 0 < U) (hsmall : 2 * (U * H) < q) :
    naturalRatioEnergy q M H D ≤
      ((H : ℝ) * (1 + Real.log U) + U) * ((U : ℝ) * (1 + Real.log U)) := by
  rw [naturalRatioEnergy_eq_sum q M H D hcop]
  have hfirst : (∑ u ∈ D, ∑ v ∈ D, (burgessIntervalCollision q M H u v).card) ≤
      ∑ u ∈ D, ∑ v ∈ D, (H / (u / u.gcd v) + 1) := by
    apply Finset.sum_le_sum
    intro u hu
    apply Finset.sum_le_sum
    intro v hv
    exact burgessIntervalCollision_card_le_of_coprime hH hU
      (hD hu) (hD hv) (hcop u hu).symm hsmall
  have hsecond : (∑ u ∈ D, ∑ v ∈ D, (H / (u / u.gcd v) + 1)) ≤
      ∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 U, (H / (u / u.gcd v) + 1) := by
    exact (Finset.sum_le_sum fun u _ => Finset.sum_le_sum_of_subset hD).trans
      (Finset.sum_le_sum_of_subset hD)
  calc
    _ ≤ ((∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 U,
        (H / (u / u.gcd v) + 1) : ℕ) : ℝ) := by exact_mod_cast hfirst.trans hsecond
    _ ≤ (burgessDivisorOvercount H U : ℝ) := reduced_denominator_sum_cast_le H U
    _ ≤ _ := burgessDivisorOvercount_cast_le H U hU

end Pollack17.Burgess

end

/-! ## Weighted Hölder in the integer-power form for Burgess amplification

Source module `ErdosProblems.Erdos1141.BurgessHolder`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

theorem weighted_power_sum_le {ι : Type*} (S : Finset ι) (w z : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hz : ∀ i ∈ S, 0 ≤ z i) (k : ℕ) :
    (∑ i ∈ S, w i * z i) ^ (k + 1) ≤
      (∑ i ∈ S, w i) ^ k * ∑ i ∈ S, w i * z i ^ (k + 1) := by
  let W := ∑ i ∈ S, w i
  have hW0 : 0 ≤ W := Finset.sum_nonneg hw
  by_cases hW : W = 0
  · have hwi : ∀ i ∈ S, w i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hw).mp hW
    have hleft : (∑ i ∈ S, w i * z i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hwi i hi, zero_mul]
    have hright : (∑ i ∈ S, w i * z i ^ (k + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hwi i hi, zero_mul]
    simp [hleft, hright]
  have hWpos : 0 < W := lt_of_le_of_ne hW0 (Ne.symm hW)
  have hj := Real.pow_arith_mean_le_arith_mean_pow S (fun i => w i / W) z
    (fun i hi => div_nonneg (hw i hi) hW0)
    (by rw [← Finset.sum_div]; exact div_self hW) hz (k + 1)
  have hj' : ((∑ i ∈ S, w i * z i) / W) ^ (k + 1) ≤
      (∑ i ∈ S, w i * z i ^ (k + 1)) / W := by
    simpa only [div_mul_eq_mul_div, ← Finset.sum_div] using hj
  rw [div_pow] at hj'
  have hscaled := (div_le_iff₀ (pow_pos hWpos (k + 1))).mp hj'
  calc
    (∑ i ∈ S, w i * z i) ^ (k + 1) ≤
        ((∑ i ∈ S, w i * z i ^ (k + 1)) / W) * W ^ (k + 1) := hscaled
    _ = W ^ k * ∑ i ∈ S, w i * z i ^ (k + 1) := by
      rw [pow_succ]
      field_simp
    _ = _ := rfl

theorem weighted_even_power_sum_le {ι : Type*} (S : Finset ι) (w z : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hz : ∀ i ∈ S, 0 ≤ z i) (k : ℕ) :
    (∑ i ∈ S, w i * z i) ^ (2 * (k + 1)) ≤
      (∑ i ∈ S, w i) ^ (2 * k) * (∑ i ∈ S, w i ^ 2) *
        ∑ i ∈ S, z i ^ (2 * (k + 1)) := by
  have hsum0 : 0 ≤ ∑ i ∈ S, w i * z i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (hz i hi)
  have hj := weighted_power_sum_le S w z hw hz k
  have hj2 := pow_le_pow_left₀ (pow_nonneg hsum0 _) hj 2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S w (fun i => z i ^ (k + 1))
  have hpowers (i : ι) : (z i ^ (k + 1)) ^ 2 = z i ^ (2 * (k + 1)) := by
    rw [← pow_mul]
    congr 1
    omega
  simp_rw [hpowers] at hcs
  calc
    (∑ i ∈ S, w i * z i) ^ (2 * (k + 1)) =
        ((∑ i ∈ S, w i * z i) ^ (k + 1)) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ ((∑ i ∈ S, w i) ^ k * ∑ i ∈ S, w i * z i ^ (k + 1)) ^ 2 := hj2
    _ = (∑ i ∈ S, w i) ^ (2 * k) * (∑ i ∈ S, w i * z i ^ (k + 1)) ^ 2 := by
      rw [mul_pow, ← pow_mul]
      congr 2
      omega
    _ ≤ (∑ i ∈ S, w i) ^ (2 * k) *
        ((∑ i ∈ S, w i ^ 2) * ∑ i ∈ S, z i ^ (2 * (k + 1))) :=
      mul_le_mul_of_nonneg_left hcs (pow_nonneg (Finset.sum_nonneg hw) _)
    _ = _ := by ring

end Pollack17.Burgess

end

/-! ## Interval averaging for real multiplicative characters

Source module `ErdosProblems.Erdos1141.BurgessAmplifier`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

lemma abs_sum_range_shift_sub_le (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) (M H h : ℕ) (hh : h ≤ H) :
    |(∑ i ∈ Finset.range H, f (M + i)) -
      ∑ i ∈ Finset.range H, f (M + h + i)| ≤ 2 * h := by
  have hH₁ : h + (H - h) = H := Nat.add_sub_of_le hh
  have hH₂ : (H - h) + h = H := Nat.sub_add_cancel hh
  have hdecomp :
      (∑ i ∈ Finset.range H, f (M + i)) -
          ∑ i ∈ Finset.range H, f (M + h + i) =
        (∑ i ∈ Finset.range h, f (M + i)) -
          ∑ i ∈ Finset.range h, f (M + H + i) := by
    have hleft := Finset.sum_range_add (fun i ↦ f (M + i)) h (H - h)
    have hright := Finset.sum_range_add
      (fun i ↦ f (M + h + i)) (H - h) h
    rw [hH₁] at hleft
    rw [hH₂] at hright
    rw [hleft, hright]
    have hmiddle :
        (∑ x ∈ Finset.range (H - h), f (M + (h + x))) =
          ∑ x ∈ Finset.range (H - h), f (M + h + x) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      omega
    have hsuffix :
        (∑ x ∈ Finset.range h, f (M + h + ((H - h) + x))) =
          ∑ x ∈ Finset.range h, f (M + H + x) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      omega
    rw [hmiddle, hsuffix]
    ring
  rw [hdecomp]
  calc
    |(∑ i ∈ Finset.range h, f (M + i)) -
        ∑ i ∈ Finset.range h, f (M + H + i)| ≤
        |∑ i ∈ Finset.range h, f (M + i)| +
          |∑ i ∈ Finset.range h, f (M + H + i)| := abs_sub _ _
    _ ≤ (∑ i ∈ Finset.range h, |f (M + i)|) +
        ∑ i ∈ Finset.range h, |f (M + H + i)| := by
      gcongr <;> exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ _i ∈ Finset.range h, (1 : ℝ)) +
        ∑ _i ∈ Finset.range h, (1 : ℝ) := by
      gcongr <;> exact hf _
    _ = 2 * h := by simp; ring

lemma abs_burgess_shift_average_sub_le
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (M H : ℕ) (U V : Finset ℕ) (g : ℕ → ℕ → ℕ)
    (hg : ∀ u ∈ U, ∀ v ∈ V, g u v ≤ H) :
    |((U.card * V.card : ℕ) : ℝ) *
        (∑ i ∈ Finset.range H, f (M + i)) -
      ∑ u ∈ U, ∑ v ∈ V,
        ∑ i ∈ Finset.range H, f (M + g u v + i)| ≤
      ∑ u ∈ U, ∑ v ∈ V, ((2 * g u v : ℕ) : ℝ) := by
  let S : ℕ → ℝ := fun h ↦ ∑ i ∈ Finset.range H, f (M + h + i)
  have hS0 : S 0 = ∑ i ∈ Finset.range H, f (M + i) := by
    simp [S]
  have heq :
      ((U.card * V.card : ℕ) : ℝ) * S 0 -
          ∑ u ∈ U, ∑ v ∈ V, S (g u v) =
        ∑ u ∈ U, ∑ v ∈ V, (S 0 - S (g u v)) := by
    simp only [Finset.sum_sub_distrib]
    simp
    ring
  rw [← hS0, heq]
  calc
    |∑ u ∈ U, ∑ v ∈ V, (S 0 - S (g u v))| ≤
        ∑ u ∈ U, |∑ v ∈ V, (S 0 - S (g u v))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ U, ∑ v ∈ V, |S 0 - S (g u v)| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ U, ∑ v ∈ V, ((2 * g u v : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      simpa [S] using
        abs_sum_range_shift_sub_le f hf M H (g u v) (hg u hu v hv)

lemma abs_burgess_shifted_triple_sum_le_finset
    (f : ℕ → ℝ) (M H : ℕ) (U V : Finset ℕ) (shift : ℕ → ℕ → ℕ) :
    |∑ u ∈ U, ∑ v ∈ V, ∑ i ∈ Finset.range H,
        f (M + shift u v + i)| ≤
      ∑ i ∈ Finset.range H, ∑ u ∈ U,
        |∑ v ∈ V, f (M + i + shift u v)| := by
  have hreorder :
      (∑ u ∈ U, ∑ v ∈ V, ∑ i ∈ Finset.range H,
          f (M + shift u v + i)) =
        ∑ i ∈ Finset.range H, ∑ u ∈ U,
          ∑ v ∈ V, f (M + i + shift u v) := by
    calc
      (∑ u ∈ U, ∑ v ∈ V, ∑ i ∈ Finset.range H,
          f (M + shift u v + i)) =
        ∑ u ∈ U, ∑ i ∈ Finset.range H,
          ∑ v ∈ V, f (M + shift u v + i) := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [Finset.sum_comm]
      _ = ∑ i ∈ Finset.range H, ∑ u ∈ U,
          ∑ v ∈ V, f (M + shift u v + i) := by
          rw [Finset.sum_comm]
      _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro u hu
          apply Finset.sum_congr rfl
          intro v hv
          congr 1
          omega
  rw [hreorder]
  calc
    |∑ i ∈ Finset.range H, ∑ u ∈ U,
        ∑ v ∈ V, f (M + i + shift u v)| ≤
      ∑ i ∈ Finset.range H,
        |∑ u ∈ U, ∑ v ∈ V, f (M + i + shift u v)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range H, ∑ u ∈ U,
        |∑ v ∈ V, f (M + i + shift u v)| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _

noncomputable def naturalShiftSum {q : ℕ} (f : ZMod q → ℝ) (V : ℕ) (x : ZMod q) : ℝ :=
  ∑ v ∈ Finset.Icc 1 V, f (x + v)

noncomputable def amplifierNumerator {q : ℕ} [NeZero q] (f : ZMod q → ℝ)
    (M H : ℕ) (D : Finset ℕ) (V : ℕ) : ℝ :=
  ∑ x : ZMod q, (naturalRatioWeight q M H D x : ℝ) * |naturalShiftSum f V x|

theorem abs_natural_dilated_sum {q : ℕ} (f : ZMod q → ℝ)
    (hmul : ∀ a b, f (a * b) = f a * f b) (M i u V : ℕ)
    (hu : u.Coprime q) (hfu : |f u| = 1) :
    |∑ v ∈ Finset.Icc 1 V, f (M + i + u * v : ℕ)| =
      |naturalShiftSum f V ((u : ZMod q)⁻¹ * (M + i : ℕ))| := by
  have halg (v : ℕ) : ((M + i + u * v : ℕ) : ZMod q) =
      u * ((u : ZMod q)⁻¹ * (M + i : ℕ) + v) := by
    rw [mul_add, ← mul_assoc, ZMod.coe_mul_inv_eq_one u hu, one_mul]
    push_cast
    ring
  simp_rw [halg, hmul]
  rw [← Finset.mul_sum, abs_mul, hfu, one_mul]
  rfl

theorem amplifierNumerator_eq_natural {q : ℕ} [NeZero q]
    (f : ZMod q → ℝ) (hmul : ∀ a b, f (a * b) = f a * f b)
    (M H : ℕ) (D : Finset ℕ) (V : ℕ)
    (hD : ∀ u ∈ D, u.Coprime q) (hfD : ∀ u ∈ D, |f u| = 1) :
    amplifierNumerator f M H D V =
      ∑ i ∈ Finset.range H, ∑ u ∈ D,
        |∑ v ∈ Finset.Icc 1 V, f (M + i + u * v : ℕ)| := by
  rw [amplifierNumerator, sum_naturalRatioWeight_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro u hu
  exact (abs_natural_dilated_sum f hmul M i u V (hD u hu) (hfD u hu)).symm

theorem amplified_abs_le {q M H U V : ℕ} [NeZero q]
    (f : ZMod q → ℝ) (hmul : ∀ a b, f (a * b) = f a * f b)
    (hf : ∀ x, |f x| ≤ 1) (D : Finset ℕ)
    (hD : D ⊆ Finset.Icc 1 U) (hcop : ∀ u ∈ D, u.Coprime q)
    (hfD : ∀ u ∈ D, |f u| = 1) (hUV : U * V ≤ H) :
    (D.card : ℝ) * V * |∑ i ∈ Finset.range H, f (M + i : ℕ)| ≤
      amplifierNumerator f M H D V + 2 * (D.card : ℝ) * V * (U * V) := by
  let S := ∑ i ∈ Finset.range H, f (M + i : ℕ)
  let T := ∑ u ∈ D, ∑ v ∈ Finset.Icc 1 V,
    ∑ i ∈ Finset.range H, f (M + u * v + i : ℕ)
  have havg := abs_burgess_shift_average_sub_le (fun n => f (n : ZMod q))
    (fun n => hf _) M H D (Finset.Icc 1 V) (fun u v => u * v) (by
      intro u hu v hv
      exact (Nat.mul_le_mul (Finset.mem_Icc.mp (hD hu)).2
        (Finset.mem_Icc.mp hv).2).trans hUV)
  have herror : |(D.card : ℝ) * V * S - T| ≤
      2 * (D.card : ℝ) * V * (U * V) := by
    have havg' : |(D.card : ℝ) * V * S - T| ≤
        ∑ u ∈ D, ∑ v ∈ Finset.Icc 1 V, ((2 * (u * v) : ℕ) : ℝ) := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel, Nat.cast_mul] using havg
    refine havg'.trans ?_
    calc
      _ ≤ ∑ _u ∈ D, ∑ _v ∈ Finset.Icc 1 V, ((2 * (U * V) : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro v hv
        exact_mod_cast Nat.mul_le_mul_left 2 (Nat.mul_le_mul
          (Finset.mem_Icc.mp (hD hu)).2 (Finset.mem_Icc.mp hv).2)
      _ = _ := by simp; ring
  have hT : |T| ≤ amplifierNumerator f M H D V := by
    rw [amplifierNumerator_eq_natural f hmul M H D V hcop hfD]
    exact abs_burgess_shifted_triple_sum_le_finset
      (fun n => f (n : ZMod q)) M H D (Finset.Icc 1 V) (fun u v => u * v)
  have htri : |(D.card : ℝ) * V * S| ≤ |(D.card : ℝ) * V * S - T| + |T| := by
    simpa only [sub_add_cancel] using abs_add_le ((D.card : ℝ) * V * S - T) T
  rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))] at htri
  exact htri.trans ((add_le_add herror hT).trans_eq (add_comm _ _))

theorem amplifierNumerator_even_power_le {q : ℕ} [NeZero q]
    (f : ZMod q → ℝ) (M H : ℕ) (D : Finset ℕ) (V k : ℕ) :
    amplifierNumerator f M H D V ^ (2 * (k + 1)) ≤
      ((H : ℝ) * D.card) ^ (2 * k) * naturalRatioEnergy q M H D *
        ∑ x : ZMod q, naturalShiftSum f V x ^ (2 * (k + 1)) := by
  have hh := weighted_even_power_sum_le (Finset.univ : Finset (ZMod q))
    (fun x => (naturalRatioWeight q M H D x : ℝ))
    (fun x => |naturalShiftSum f V x|)
    (fun x _ => Nat.cast_nonneg _) (fun x _ => abs_nonneg _) k
  have hsum : (∑ x : ZMod q, (naturalRatioWeight q M H D x : ℝ)) =
      (H : ℝ) * D.card := by exact_mod_cast sum_naturalRatioWeight q M H D
  have habs (x : ZMod q) : |naturalShiftSum f V x| ^ (2 * (k + 1)) =
      naturalShiftSum f V x ^ (2 * (k + 1)) := (even_two_mul _).pow_abs _
  simpa only [hsum, habs, amplifierNumerator, naturalRatioEnergy] using hh

end Pollack17.Burgess

end

/-! ## The complete Burgess moment for squarefree quadratic characters

Source module `ErdosProblems.Erdos1141.BurgessCompositeMoment`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

theorem productChar_prod (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {ι : Type*} [Fintype ι] (f : ι → ZMod (primeModulus s)) :
    productChar s hs (∏ i, f i) = ∏ i, productChar s hs (f i) := by
  classical
  simp only [productChar, localChar, qchar, map_prod, Finset.prod_apply, Int.cast_prod]
  rw [Finset.prod_comm]

theorem productChar_moment_expansion (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] (V n : ℕ) :
    (∑ x : ZMod (primeModulus s), naturalShiftSum (productChar s hs) V x ^ n) =
      ∑ v : Fin n → (Finset.Icc 1 V), ∑ x : ZMod (primeModulus s),
        productChar s hs (∏ i : Fin n, (x + (v i : ℕ))) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [naturalShiftSum, ← Finset.sum_attach, Finset.attach_eq_univ, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro v _
  exact (productChar_prod s hs (fun i : Fin n => x + (v i : ℕ))).symm

noncomputable def gcdKernel (q a b : ℕ) : ℝ :=
  if b ≠ a then (q.gcd (Nat.dist a b) : ℝ) else 0

theorem gcdKernel_nonneg (q a b : ℕ) : 0 ≤ gcdKernel q a b := by
  unfold gcdKernel
  split_ifs <;> positivity

theorem sum_gcdKernel_le {q : ℕ} (hq : q ≠ 0) (V : ℕ) (a : Finset.Icc 1 V) :
    (∑ b : Finset.Icc 1 V, gcdKernel q a b) ≤ 2 * V * q.divisors.card := by
  rw [Finset.sum_coe_sort (Finset.Icc 1 V) (fun b : ℕ => gcdKernel q a b)]
  simp only [gcdKernel, ← Finset.sum_filter, Finset.filter_ne']
  exact_mod_cast sum_gcd_dist_erase_le hq (Finset.mem_Icc.mp a.property).2

theorem productChar_even_moment_le (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] (V r : ℕ) :
    (∑ x : ZMod (primeModulus s), naturalShiftSum (productChar s hs) V x ^ (2 * r)) ≤
      (V : ℝ) ^ r * (r : ℝ) ^ (2 * r) * primeModulus s +
        ((Stepanov.simpleRootConstant (2 * r) : ℝ) ^ s.card * Real.sqrt (primeModulus s)) *
          (2 * r : ℕ) * V * (2 * V * ((primeModulus s).divisors.card : ℝ)) ^ (2 * r - 1) := by
  classical
  let α := Finset.Icc 1 V
  let q := primeModulus s
  let corr : (Fin (2 * r) → α) → ℝ := fun v =>
    ∑ x : ZMod q, productChar s hs (∏ i : Fin (2 * r), (x + (v i : ℕ)))
  let w : α → α → ℝ := fun a b => gcdKernel q a b
  let C : ℝ := (Stepanov.simpleRootConstant (2 * r) : ℝ) ^ s.card * Real.sqrt q
  have hw : ∀ a b : α, 0 ≤ w a b := fun a b => gcdKernel_nonneg q a b
  have hrow : ∀ a : α, (∑ b : α, w a b) ≤ 2 * V * (q.divisors.card : ℝ) :=
    fun a => sum_gcdKernel_le (NeZero.ne q) V a
  have htrivial (v : Fin (2 * r) → α) : corr v ≤ q := by
    calc
      _ ≤ ∑ _x : ZMod q, (1 : ℝ) := Finset.sum_le_sum fun x _ =>
        (le_abs_self _).trans (abs_productChar_le_one s hs _)
      _ = _ := by simp
  have hsingle (v : Fin (2 * r) → α) (i : Fin (2 * r))
      (hi : ∀ j, j ≠ i → v j ≠ v i) : corr v ≤ C * starWeight w v i := by
    have hbound := product_correlation_le_gcd s hs (fun j => (v j : ℕ)) i
    have hwprod : starWeight w v i =
        ∏ j ∈ Finset.univ.erase i, (q.gcd (Nat.dist (v i) (v j)) : ℝ) := by
      rw [starWeight_eq_prod_erase]
      apply Finset.prod_congr rfl
      intro j hj
      have hne : (v j : ℕ) ≠ v i := fun h => hi j (Finset.mem_erase.mp hj).1 (Subtype.ext h)
      exact if_pos hne
    rw [hwprod]
    exact (le_abs_self (corr v)).trans hbound
  rw [productChar_moment_expansion]
  have h := sum_tuple_correlations_le r corr w hw (Nat.cast_nonneg q)
    (by dsimp [C]; positivity) hrow htrivial hsingle
  simpa only [α, corr, C, q, Fintype.card_coe, Nat.card_Icc, Nat.add_sub_cancel] using h

end Pollack17.Burgess

end

/-! ## Absorbing composite moment losses into an arbitrarily small power

Source module `ErdosProblems.Erdos1141.BurgessMomentAsymptotics`. -/

noncomputable section

namespace Pollack17.Burgess

open Filter

open scoped BigOperators

theorem composite_moment_second_term (C w V n : ℕ) (hn : 0 < n) (q : ℝ) :
    (C : ℝ) ^ w * q * n * V * (2 * V * (2 : ℝ) ^ w) ^ (n - 1) =
      ((n : ℝ) * 2 ^ (n - 1)) * ((C * 2 ^ (n - 1) : ℕ) : ℝ) ^ w * q * (V : ℝ) ^ n := by
  have hV : (V : ℝ) * (V : ℝ) ^ (n - 1) = (V : ℝ) ^ n := by
    rw [← pow_succ']
    congr 1
    omega
  have htwo : ((2 : ℝ) ^ w) ^ (n - 1) = ((2 : ℝ) ^ (n - 1)) ^ w := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow, htwo]
  calc
    _ = ((n : ℝ) * 2 ^ (n - 1)) *
        ((C : ℝ) ^ w * (2 ^ (n - 1)) ^ w) * q * ((V : ℝ) * (V : ℝ) ^ (n - 1)) := by ring
    _ = _ := by rw [hV]

theorem eventually_productChar_moment_le (r : ℕ) (hr : 0 < r)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q : ℕ, ∀ (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime), Q ≤ primeModulus s →
      ∀ V : ℕ, letI : NeZero (primeModulus s) := ⟨(primeModulus_pos s hs).ne'⟩
      (∑ x : ZMod (primeModulus s), naturalShiftSum (productChar s hs) V x ^ (2 * r)) ≤
        (primeModulus s : ℝ) ^ δ *
          ((primeModulus s : ℝ) * (V : ℝ) ^ r +
            Real.sqrt (primeModulus s) * (V : ℝ) ^ (2 * r)) := by
  let n := 2 * r
  let C := Stepanov.simpleRootConstant n
  let b := C * 2 ^ (n - 1)
  have hb : 1 ≤ b := Nat.mul_pos (simpleRootConstant_one_le n) (by positivity)
  have hfirst := eventually_const_mul_pow_primeFactors_le ((r : ℝ) ^ (2 * r)) 1 (by omega) hδ
  have hsecond := eventually_const_mul_pow_primeFactors_le ((n : ℝ) * 2 ^ (n - 1)) b hb hδ
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp (hfirst.and hsecond)
  refine ⟨Q, fun s hs hq V => ?_⟩
  have : NeZero (primeModulus s) := ⟨(primeModulus_pos s hs).ne'⟩
  have hc₁ : (r : ℝ) ^ (2 * r) ≤ (primeModulus s : ℝ) ^ δ := by
    simpa using (hQ (primeModulus s) hq).1
  have hc₂ : ((n : ℝ) * 2 ^ (n - 1)) * (b : ℝ) ^ s.card ≤
      (primeModulus s : ℝ) ^ δ := by
    simpa only [primeModulus_primeFactors s hs] using (hQ (primeModulus s) hq).2
  have hm := productChar_even_moment_le s hs V r
  rw [primeModulus_card_divisors s hs, Nat.cast_pow, Nat.cast_ofNat] at hm
  have heq := composite_moment_second_term C s.card V n (by dsimp [n]; omega)
    (Real.sqrt (primeModulus s))
  change _ = ((n : ℝ) * 2 ^ (n - 1)) * (b : ℝ) ^ s.card *
    Real.sqrt (primeModulus s) * (V : ℝ) ^ n at heq
  rw [heq] at hm
  have h₁ := mul_le_mul_of_nonneg_right hc₁
    (mul_nonneg (Nat.cast_nonneg (primeModulus s)) (pow_nonneg (Nat.cast_nonneg V) r))
  have h₂ := mul_le_mul_of_nonneg_right hc₂
    (mul_nonneg (Real.sqrt_nonneg (primeModulus s)) (pow_nonneg (Nat.cast_nonneg V) n))
  refine hm.trans ?_
  nlinarith only [h₁, h₂]

end Pollack17.Burgess

end

/-! ## Finite power-scale estimates for the Burgess amplifier

Source module `ErdosProblems.Erdos1141.BurgessScaleEstimates`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

theorem pow_le_scaled_rpow {x q C a : ℝ} (hx : 0 ≤ x) (hq : 0 ≤ q)
    (h : x ≤ C * q ^ a) (k : ℕ) : x ^ k ≤ C ^ k * q ^ (a * k) := by
  simpa only [mul_pow, ← Real.rpow_mul_natCast hq] using pow_le_pow_left₀ hx h k

theorem scaled_rpow_le_pow {x q C a : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q)
    (h : C * q ^ a ≤ x) (k : ℕ) : C ^ k * q ^ (a * k) ≤ x ^ k := by
  simpa only [mul_pow, ← Real.rpow_mul_natCast hq] using
    pow_le_pow_left₀ (mul_nonneg hC (Real.rpow_nonneg hq _)) h k

theorem harmonic_energy_scale_le {q : ℕ} (hq : 1 ≤ q) {H U : ℕ}
    (hU : 0 < U) {c u δ : ℝ} (hu1 : u ≤ 1) (huδ : u ≤ c + δ)
    (hH : (H : ℝ) ≤ (q : ℝ) ^ c) (hUp : (U : ℝ) ≤ (q : ℝ) ^ u)
    (hlog : 1 + Real.log (q : ℝ) ≤ (q : ℝ) ^ δ) :
    ((H : ℝ) * (1 + Real.log U) + U) * ((U : ℝ) * (1 + Real.log U)) ≤
      2 * (q : ℝ) ^ (c + u + 2 * δ) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : 0 < (q : ℝ) := zero_lt_one.trans_le hq1
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hUq : (U : ℝ) ≤ q := hUp.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hq1 hu1)
  have hL : 1 + Real.log (U : ℝ) ≤ (q : ℝ) ^ δ := by
    have hl := Real.log_le_log hU0 hUq
    linarith
  have hL0 : 0 ≤ 1 + Real.log (U : ℝ) := by
    have hl := Real.log_nonneg (by exact_mod_cast hU : (1 : ℝ) ≤ U)
    linarith
  have hA : (H : ℝ) * (1 + Real.log U) ≤ (q : ℝ) ^ (c + δ) := by
    simpa only [Real.rpow_add hq0] using mul_le_mul hH hL hL0 (Real.rpow_nonneg hq0.le c)
  have hU' : (U : ℝ) ≤ (q : ℝ) ^ (c + δ) :=
    hUp.trans (Real.rpow_le_rpow_of_exponent_le hq1 huδ)
  have hA' : (H : ℝ) * (1 + Real.log U) + U ≤ 2 * (q : ℝ) ^ (c + δ) := by
    linarith
  have hB : (U : ℝ) * (1 + Real.log U) ≤ (q : ℝ) ^ (u + δ) := by
    simpa only [Real.rpow_add hq0] using mul_le_mul hUp hL hL0 (Real.rpow_nonneg hq0.le u)
  calc
    _ ≤ (2 * (q : ℝ) ^ (c + δ)) * (q : ℝ) ^ (u + δ) :=
      mul_le_mul hA' hB (mul_nonneg hU0.le hL0) (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hq0]; congr 2; ring

theorem moment_scale_le {q : ℕ} (hq : 0 < q) {V r : ℕ} {v δ : ℝ}
    (hv : v * (r : ℝ) = 1 / 2) (hV : (V : ℝ) ≤ 2 * (q : ℝ) ^ v) :
    (q : ℝ) ^ δ * ((q : ℝ) * (V : ℝ) ^ r + Real.sqrt q * (V : ℝ) ^ (2 * r)) ≤
      ((2 : ℝ) ^ r + 2 ^ (2 * r)) * (q : ℝ) ^ (3 / 2 + δ) := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  have h₁ := pow_le_scaled_rpow (Nat.cast_nonneg V) hq0.le hV r
  have h₂ := pow_le_scaled_rpow (Nat.cast_nonneg V) hq0.le hV (2 * r)
  have hvr : v * ((2 * r : ℕ) : ℝ) = 1 := by push_cast; nlinarith only [hv]
  rw [hv] at h₁
  rw [hvr, Real.rpow_one] at h₂
  have hqpow : (q : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) = (q : ℝ) ^ (3 / 2 : ℝ) := by
    calc
      _ = (q : ℝ) ^ (1 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
      _ = (q : ℝ) ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hq0 _ _).symm
      _ = _ := by norm_num
  have hsum : (q : ℝ) * (V : ℝ) ^ r + Real.sqrt q * (V : ℝ) ^ (2 * r) ≤
      ((2 : ℝ) ^ r + 2 ^ (2 * r)) * (q : ℝ) ^ (3 / 2 : ℝ) := by
    have ha := mul_le_mul_of_nonneg_left h₁ hq0.le
    have hb := mul_le_mul_of_nonneg_left h₂ (Real.sqrt_nonneg q)
    rw [Real.sqrt_eq_rpow] at hb ⊢
    calc
      _ ≤ (q : ℝ) * (2 ^ r * (q : ℝ) ^ (1 / 2 : ℝ)) +
          (q : ℝ) ^ (1 / 2 : ℝ) * (2 ^ (2 * r) * q) := add_le_add ha hb
      _ = (2 ^ r + 2 ^ (2 * r)) * ((q : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [hqpow]
  calc
    _ ≤ (q : ℝ) ^ δ * (((2 : ℝ) ^ r + 2 ^ (2 * r)) * (q : ℝ) ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hq0.le δ)
    _ = _ := by rw [mul_left_comm, ← Real.rpow_add hq0]; congr 2; ring

end Pollack17.Burgess

end

/-! ## Counting the admissible Burgess denominators

Source module `ErdosProblems.Erdos1141.BurgessDenominators`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

def coprimeDenominators (s : Finset ℕ) (U : ℕ) : Finset ℕ :=
  (Finset.Icc 1 U).filter fun u ↦ u.Coprime (primeModulus s)

def primeSetMultiplesInIcc (U p : ℕ) : Finset ↥(Finset.Icc 1 U) :=
  Finset.univ.filter fun u ↦ p ∣ (u : ℕ)

lemma prod_dvd_iff_all_prime_dvd
    (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (n : ℕ) :
    (∏ p ∈ t, p) ∣ n ↔ ∀ p ∈ t, p ∣ n := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem id hp).trans h
  · intro h
    induction t using Finset.induction_on with
    | empty => simp
    | @insert p t hpt ih =>
        rw [Finset.prod_insert hpt]
        have hp : p.Prime := ht p (Finset.mem_insert_self p t)
        have hcop : p.Coprime (∏ r ∈ t, r) := by
          apply Nat.Coprime.prod_right
          intro r hr
          exact (Nat.coprime_primes hp
            (ht r (Finset.mem_insert_of_mem hr))).mpr
            (Ne.symm (ne_of_mem_of_not_mem hr hpt))
        exact hcop.mul_dvd_of_dvd_of_dvd
          (h p (Finset.mem_insert_self p t))
          (ih (fun r hr ↦ ht r (Finset.mem_insert_of_mem hr))
            (fun r hr ↦ h r (Finset.mem_insert_of_mem hr)))

lemma card_inf_primeSetMultiplesInIcc
    (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (U : ℕ) :
    (t.inf (primeSetMultiplesInIcc U)).card =
      U / (∏ p ∈ t, p) := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  refine Finset.card_bij
    (s := t.inf (primeSetMultiplesInIcc U))
    (t := (Finset.Ioc 0 U).filter fun n ↦ (∏ p ∈ t, p) ∣ n)
    (fun (u : ↥(Finset.Icc 1 U)) _hu ↦ (u : ℕ)) ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_Ioc.mpr (Finset.mem_Icc.mp u.property)
    · rw [prod_dvd_iff_all_prime_dvd t ht]
      intro p hp
      have hu' : ∀ p ∈ t, u ∈ primeSetMultiplesInIcc U p := by
        simpa only [Finset.mem_inf] using hu
      have hup : u ∈ primeSetMultiplesInIcc U p := hu' p hp
      simpa [primeSetMultiplesInIcc] using hup
  · intro u₁ h₁ u₂ h₂ huv
    exact Subtype.ext huv
  · intro n hn
    have hnIoc := (Finset.mem_filter.mp hn).1
    let u : ↥(Finset.Icc 1 U) :=
      ⟨n, Finset.mem_Icc.mpr (Finset.mem_Ioc.mp hnIoc)⟩
    refine ⟨u, ?_, rfl⟩
    simp only [Finset.mem_inf]
    intro p hp
    simp only [primeSetMultiplesInIcc, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (prod_dvd_iff_all_prime_dvd t ht n).mp
      (Finset.mem_filter.mp hn).2 p hp

lemma inf_compl_primeSetMultiples_eq_coprime
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ) :
    s.inf (fun p ↦ (primeSetMultiplesInIcc U p)ᶜ) =
      (Finset.univ : Finset ↥(Finset.Icc 1 U)).filter
        (fun (u : ↥(Finset.Icc 1 U)) ↦
          (u : ℕ).Coprime (primeModulus s)) := by
  ext u
  simp only [Finset.mem_inf, Finset.mem_compl,
    primeSetMultiplesInIcc, Finset.mem_filter, Finset.mem_univ,
    true_and, primeModulus, Nat.coprime_prod_right_iff]
  constructor
  · intro h p hp
    rw [Nat.coprime_comm, (hs p hp).coprime_iff_not_dvd]
    exact h p hp
  · intro h p hp hdiv
    have hpco := h p hp
    rw [Nat.coprime_comm, (hs p hp).coprime_iff_not_dvd] at hpco
    exact hpco hdiv

lemma card_coprimeDenominators_eq_alternating
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ) :
    ((coprimeDenominators s U).card : ℤ) =
      ∑ t ∈ s.powerset,
        (-1 : ℤ) ^ t.card * (U / (∏ p ∈ t, p) : ℕ) := by
  have hIE := Finset.inclusion_exclusion_card_inf_compl s
    (primeSetMultiplesInIcc U)
  calc
    ((coprimeDenominators s U).card : ℤ) =
        (((Finset.univ : Finset ↥(Finset.Icc 1 U)).filter
          (fun (u : ↥(Finset.Icc 1 U)) ↦
            (u : ℕ).Coprime (primeModulus s))).card : ℤ) := by
      apply congrArg (fun n : ℕ ↦ (n : ℤ))
      refine Finset.card_bij
        (s := coprimeDenominators s U)
        (t := (Finset.univ : Finset ↥(Finset.Icc 1 U)).filter
          (fun (u : ↥(Finset.Icc 1 U)) ↦
            (u : ℕ).Coprime (primeModulus s)))
        (fun n hn ↦ ⟨n, ?_⟩) ?_ ?_ ?_
      · exact (Finset.mem_filter.mp hn).1
      · intro n hn
        simpa [coprimeDenominators] using
          (Finset.mem_filter.mp hn).2
      · intro a ha b hb hab
        exact congrArg Subtype.val hab
      · intro u hu
        refine ⟨u, ?_, Subtype.ext rfl⟩
        simpa [coprimeDenominators] using
          (Finset.mem_filter.mp hu).2
    _ = ((s.inf fun p ↦ (primeSetMultiplesInIcc U p)ᶜ).card : ℤ) := by
      rw [inf_compl_primeSetMultiples_eq_coprime s hs U]
    _ = ∑ t ∈ s.powerset,
          (-1 : ℤ) ^ t.card *
            ((t.inf (primeSetMultiplesInIcc U)).card : ℤ) := hIE
    _ = ∑ t ∈ s.powerset,
          (-1 : ℤ) ^ t.card * (U / (∏ p ∈ t, p) : ℕ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [card_inf_primeSetMultiplesInIcc t
        (fun p hp ↦ hs p (Finset.mem_powerset.mp ht hp)) U]

lemma alternating_prime_reciprocal_eq
    (s : Finset ℕ) (U : ℕ) :
    (∑ t ∈ s.powerset,
        (-1 : ℝ) ^ t.card *
          ((U : ℝ) / (∏ p ∈ t, p : ℕ))) =
      (U : ℝ) * ∏ p ∈ s, (1 - (p : ℝ)⁻¹) := by
  rw [Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_inv_distrib]
  simp only [Nat.cast_prod]
  ring

lemma half_le_one_sub_prime_inv {p : ℕ} (hp : p.Prime) :
    (1 / 2 : ℝ) ≤ 1 - (p : ℝ)⁻¹ := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) hp2
  norm_num at hinv ⊢
  linarith

lemma prod_one_sub_prime_inv_lower
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (1 / 2 : ℝ) ^ s.card ≤ ∏ p ∈ s, (1 - (p : ℝ)⁻¹) := by
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod (fun p hp ↦ by positivity)
    (fun p hp ↦ half_le_one_sub_prime_inv (hs p hp))

lemma abs_natCast_div_sub_div_lt_one (U d : ℕ) :
    |((U / d : ℕ) : ℝ) - (U : ℝ) / (d : ℝ)| < 1 := by
  have hle : ((U / d : ℕ) : ℝ) ≤ (U : ℝ) / (d : ℝ) :=
    Nat.cast_div_le
  have hlt : (U : ℝ) / (d : ℝ) < ((U / d : ℕ) : ℝ) + 1 := by
    simpa only [Nat.floor_div_eq_div] using
      (Nat.lt_floor_add_one ((U : ℝ) / (d : ℝ)))
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  linarith

lemma alternating_prime_floor_sum_error
    (s : Finset ℕ) (U : ℕ) :
    |(∑ t ∈ s.powerset,
        (-1 : ℝ) ^ t.card * ((U / (∏ p ∈ t, p) : ℕ) : ℝ)) -
      ∑ t ∈ s.powerset,
        (-1 : ℝ) ^ t.card *
          ((U : ℝ) / (∏ p ∈ t, p : ℕ))| ≤
        (2 : ℝ) ^ s.card := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ t ∈ s.powerset,
        ((-1 : ℝ) ^ t.card * ((U / (∏ p ∈ t, p) : ℕ) : ℝ) -
          (-1 : ℝ) ^ t.card *
            ((U : ℝ) / (∏ p ∈ t, p : ℕ)))| ≤
        ∑ t ∈ s.powerset,
          |((-1 : ℝ) ^ t.card * ((U / (∏ p ∈ t, p) : ℕ) : ℝ) -
            (-1 : ℝ) ^ t.card *
              ((U : ℝ) / (∏ p ∈ t, p : ℕ)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ s.powerset, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [← mul_sub, abs_mul, abs_neg_one_pow]
      simpa only [one_mul] using
        (abs_natCast_div_sub_div_lt_one U (∏ p ∈ t, p)).le
    _ = (2 : ℝ) ^ s.card := by simp

lemma card_coprimeDenominators_lower
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ) :
    (U : ℝ) * (1 / 2 : ℝ) ^ s.card - (2 : ℝ) ^ s.card ≤
      (coprimeDenominators s U).card := by
  let F : ℝ := ∑ t ∈ s.powerset,
    (-1 : ℝ) ^ t.card * ((U / (∏ p ∈ t, p) : ℕ) : ℝ)
  let R : ℝ := ∑ t ∈ s.powerset,
    (-1 : ℝ) ^ t.card * ((U : ℝ) / (∏ p ∈ t, p : ℕ))
  have hcount : ((coprimeDenominators s U).card : ℝ) = F := by
    have h := congrArg (fun z : ℤ ↦ (z : ℝ))
      (card_coprimeDenominators_eq_alternating s hs U)
    simpa only [Int.cast_natCast, Int.cast_sum, Int.cast_mul,
      Int.cast_pow, Int.cast_neg, Int.cast_one] using h
  have herror : |F - R| ≤ (2 : ℝ) ^ s.card :=
    alternating_prime_floor_sum_error s U
  have hR : (U : ℝ) * ∏ p ∈ s, (1 - (p : ℝ)⁻¹) = R :=
    (alternating_prime_reciprocal_eq s U).symm
  have hprod : (U : ℝ) * (1 / 2 : ℝ) ^ s.card ≤ R := by
    rw [← hR]
    exact mul_le_mul_of_nonneg_left
      (prod_one_sub_prime_inv_lower s hs) (by positivity)
  have hRF : R - F ≤ (2 : ℝ) ^ s.card := by
    calc
      R - F ≤ |R - F| := le_abs_self _
      _ = |F - R| := abs_sub_comm _ _
      _ ≤ (2 : ℝ) ^ s.card := herror
  rw [hcount]
  linarith

end Pollack17.Burgess

end

/-! ## A subpower lower bound for the admissible amplifier denominators

Source module `ErdosProblems.Erdos1141.BurgessDenominatorAsymptotics`. -/

noncomputable section

namespace Pollack17.Burgess

open Filter

theorem coprimeDenominators_lower_half (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (U : ℕ) (hU : 2 * (4 : ℝ) ^ s.card ≤ U) :
    (U : ℝ) / (2 * (2 : ℝ) ^ s.card) ≤ (coprimeDenominators s U).card := by
  let a := (2 : ℝ) ^ s.card
  have ha : 0 < a := by dsimp [a]; positivity
  have h4 : (4 : ℝ) ^ s.card = a ^ 2 := by
    dsimp [a]
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hUa : 2 * a ^ 2 ≤ (U : ℝ) := by simpa only [h4] using hU
  have hcalc : ((U : ℝ) / a - a) * (2 * a) = 2 * U - 2 * a ^ 2 := by
    field_simp
  have hhalf : (U : ℝ) / (2 * a) ≤ (U : ℝ) / a - a := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * a)).mpr
    rw [hcalc]
    linarith
  have hbound := card_coprimeDenominators_lower s hs U
  have hmain : (U : ℝ) * (1 / 2 : ℝ) ^ s.card = (U : ℝ) / a := by
    simp [a, div_eq_mul_inv, inv_pow]
  rw [hmain] at hbound
  exact hhalf.trans hbound

theorem eventually_coprimeDenominators_lower {u δ : ℝ} (hu : 0 < u) (hδ : 0 < δ) :
    ∃ Q : ℕ, ∀ (s : Finset ℕ) (_hs : ∀ p ∈ s, p.Prime), Q ≤ primeModulus s →
      ∀ U : ℕ, (primeModulus s : ℝ) ^ u ≤ U →
        (U : ℝ) * (primeModulus s : ℝ) ^ (-δ) ≤ (coprimeDenominators s U).card := by
  have h₁ := eventually_const_mul_pow_primeFactors_le 2 4 (by omega) hu
  have h₂ := eventually_const_mul_pow_primeFactors_le 2 2 (by omega) hδ
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp (h₁.and h₂)
  refine ⟨Q, fun s hs hq U hU => ?_⟩
  have h4 : 2 * (4 : ℝ) ^ s.card ≤ (primeModulus s : ℝ) ^ u := by
    simpa only [primeModulus_primeFactors s hs, Nat.cast_ofNat] using (hQ (primeModulus s) hq).1
  have h2 : 2 * (2 : ℝ) ^ s.card ≤ (primeModulus s : ℝ) ^ δ := by
    simpa only [primeModulus_primeFactors s hs, Nat.cast_ofNat] using (hQ (primeModulus s) hq).2
  have hi := inv_anti₀ (by positivity : (0 : ℝ) < 2 * 2 ^ s.card) h2
  have hi' : (primeModulus s : ℝ) ^ (-δ) ≤ (2 * (2 : ℝ) ^ s.card)⁻¹ := by
    simpa only [Real.rpow_neg (Nat.cast_nonneg _)] using hi
  calc
    _ ≤ (U : ℝ) / (2 * (2 : ℝ) ^ s.card) := by
      exact mul_le_mul_of_nonneg_left hi' (Nat.cast_nonneg U)
    _ ≤ _ := coprimeDenominators_lower_half s hs U (h4.trans hU)

end Pollack17.Burgess

end

/-! ## The Burgess amplifier on power scales

Source module `ErdosProblems.Erdos1141.BurgessCompositeAmplifier`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

theorem abs_productChar_natCast_of_coprime (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (u : ℕ) (hu : u.Coprime (primeModulus s)) : |productChar s hs u| = 1 := by
  classical
  rw [productChar, Finset.abs_prod]
  apply Finset.prod_eq_one
  intro p _
  have : Fact (Nat.Prime (p : ℕ)) := ⟨hs p p.property⟩
  have hcop : u.Coprime (p : ℕ) := hu.of_dvd_right (Finset.dvd_prod_of_mem id p.property)
  have hnz : (u : ZMod (p : ℕ)) ≠ 0 := by
    intro hz
    exact ((hs p p.property).coprime_iff_not_dvd.mp hcop.symm)
      ((ZMod.natCast_eq_zero_iff u (p : ℕ)).mp hz)
  rw [primeCRT_natCast]
  rcases quadraticChar_dichotomy hnz with h | h <;> simp [localChar, qchar, h]

theorem productChar_amplified_abs_le (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] {M H U V : ℕ} (hUV : U * V ≤ H) :
    ((coprimeDenominators s U).card : ℝ) * V *
        |∑ i ∈ Finset.range H, productChar s hs (M + i : ℕ)| ≤
      amplifierNumerator (productChar s hs) M H (coprimeDenominators s U) V +
        2 * ((coprimeDenominators s U).card : ℝ) * V * (U * V) := by
  exact amplified_abs_le (productChar s hs) (productChar_mul s hs)
    (abs_productChar_le_one s hs) (coprimeDenominators s U) (Finset.filter_subset _ _)
    (fun _ h => (Finset.mem_filter.mp h).2)
    (fun u h => abs_productChar_natCast_of_coprime s hs u (Finset.mem_filter.mp h).2) hUV

theorem amplifier_scale_le {q : ℕ} [NeZero q] (hq : 1 ≤ q)
    (f : ZMod q → ℝ) (M H U V k : ℕ) (D : Finset ℕ)
    (hD : D ⊆ Finset.Icc 1 U) (hcop : ∀ u ∈ D, u.Coprime q)
    (hH0 : 0 < H) (hU0 : 0 < U) (hsmall : 2 * (U * H) < q)
    {c u v δ : ℝ} (hu1 : u ≤ 1) (huδ : u ≤ c + δ)
    (hH : (H : ℝ) ≤ (q : ℝ) ^ c) (hU : (U : ℝ) ≤ (q : ℝ) ^ u)
    (hV : (V : ℝ) ≤ 2 * (q : ℝ) ^ v) (hv : v * (k + 1 : ℝ) = 1 / 2)
    (hlog : 1 + Real.log (q : ℝ) ≤ (q : ℝ) ^ δ)
    (hmoment : (∑ x : ZMod q, naturalShiftSum f V x ^ (2 * (k + 1))) ≤
      (q : ℝ) ^ δ * ((q : ℝ) * (V : ℝ) ^ (k + 1) +
        Real.sqrt q * (V : ℝ) ^ (2 * (k + 1)))) :
    amplifierNumerator f M H D V ^ (2 * (k + 1)) ≤
      (2 * ((2 : ℝ) ^ (k + 1) + 2 ^ (2 * (k + 1)))) *
        (q : ℝ) ^ ((c + u) * (2 * k + 1 : ℕ) + 3 / 2 + 3 * δ) := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  have hcard : (D.card : ℝ) ≤ U := by
    exact_mod_cast (Finset.card_le_card hD).trans_eq (by simp)
  have hHD : (H : ℝ) * D.card ≤ (q : ℝ) ^ (c + u) := by
    rw [Real.rpow_add hq0]
    exact mul_le_mul hH (hcard.trans hU) (Nat.cast_nonneg _) (Real.rpow_nonneg hq0.le _)
  have hpHD : ((H : ℝ) * D.card) ^ (2 * k) ≤ (q : ℝ) ^ ((c + u) * (2 * k : ℕ)) := by
    simpa only [one_mul, one_pow] using pow_le_scaled_rpow
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hq0.le
      (show (H : ℝ) * D.card ≤ 1 * (q : ℝ) ^ (c + u) by simpa only [one_mul] using hHD) (2 * k)
  have he := (naturalRatioEnergy_le (M := M) D hD hcop hH0 hU0 hsmall).trans
    (harmonic_energy_scale_le hq hU0 hu1 huδ hH hU hlog)
  have hm := hmoment.trans (moment_scale_le (by omega : 0 < q)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hv) hV)
  have hh := amplifierNumerator_even_power_le f M H D V k
  have he0 : 0 ≤ naturalRatioEnergy q M H D :=
    Finset.sum_nonneg fun x _ => sq_nonneg _
  have hm0 : 0 ≤ ∑ x : ZMod q, naturalShiftSum f V x ^ (2 * (k + 1)) :=
    Finset.sum_nonneg fun x _ => (even_two_mul _).pow_nonneg _
  calc
    _ ≤ ((H : ℝ) * D.card) ^ (2 * k) * naturalRatioEnergy q M H D *
        ∑ x : ZMod q, naturalShiftSum f V x ^ (2 * (k + 1)) := hh
    _ ≤ (q : ℝ) ^ ((c + u) * (2 * k : ℕ)) *
        (2 * (q : ℝ) ^ (c + u + 2 * δ)) *
        (((2 : ℝ) ^ (k + 1) + 2 ^ (2 * (k + 1))) * (q : ℝ) ^ (3 / 2 + δ)) := by
      exact mul_le_mul (mul_le_mul hpHD he he0 (Real.rpow_nonneg hq0.le _)) hm hm0
        (by positivity)
    _ = (2 * ((2 : ℝ) ^ (k + 1) + 2 ^ (2 * (k + 1)))) *
        ((q : ℝ) ^ ((c + u) * (2 * k : ℕ)) *
          (q : ℝ) ^ (c + u + 2 * δ) * (q : ℝ) ^ (3 / 2 + δ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
      congr 2
      push_cast
      ring

end Pollack17.Burgess

end

/-! ## Burgess cancellation on a fixed positive-power block length

Source module `ErdosProblems.Erdos1141.BurgessBlocks`. -/

noncomputable section

namespace Pollack17.Burgess

open Filter

open scoped BigOperators

theorem eventually_power_block_bound (k : ℕ) {c u v δ η : ℝ}
    (hc : 0 < c) (hu : 0 < u) (hv : 0 ≤ v) (hδ : 0 < δ) (hη : 0 < η)
    (hu1 : u ≤ 1) (huδ : u ≤ c + δ) (huv : u + v < c - η) (huc : u + c < 1)
    (hvk : v * (k + 1 : ℝ) = 1 / 2)
    (hgap : (c + u) * (2 * k + 1 : ℕ) + 3 / 2 + 3 * δ <
      (u + v + c - δ - η) * (2 * (k + 1) : ℕ)) :
    ∀ᶠ q : ℕ in atTop, ∀ (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime),
      primeModulus s = q → ∀ M : ℕ,
        |∑ i ∈ Finset.range ⌊(q : ℝ) ^ c⌋₊, productChar s hs (M + i : ℕ)| ≤
          (q : ℝ) ^ (c - η) := by
  obtain ⟨Qm, hm⟩ := eventually_productChar_moment_le (k + 1) (by omega) hδ
  obtain ⟨Qd, hd⟩ := eventually_coprimeDenominators_lower (half_pos hu) hδ
  have hroot := eventually_const_mul_rpow_le (C := 1) (d := 1 / 2)
    (a := u / 2) (b := u) (by norm_num) (by linarith)
  have hshift := eventually_const_mul_rpow_le (C := 2) (d := 1 / 2)
    (a := u + v) (b := c) (by norm_num) (by linarith)
  have hsmall := eventually_const_mul_rpow_le (C := 2) (d := 1 / 2)
    (a := u + c) (b := 1) (by norm_num) huc
  have herror := eventually_const_mul_rpow_le (C := 4) (d := 1 / 2)
    (a := u + v) (b := c - η) (by norm_num) huv
  have hbudget := eventually_const_mul_rpow_le
    (C := 2 * ((2 : ℝ) ^ (k + 1) + 2 ^ (2 * (k + 1))))
    (d := (1 / 4 : ℝ) ^ (2 * (k + 1))) (by positivity) hgap
  filter_upwards [eventually_ge_atTop Qm, eventually_ge_atTop Qd,
    eventually_ge_atTop 1, eventually_floor_rpow_bounds hc, eventually_floor_rpow_bounds hu,
    eventually_one_add_log_le_rpow hδ, hroot, hshift, hsmall, herror, hbudget]
    with q hqm hqd hq1 hHbounds hUbounds hlog hrootq hshiftq hsmallq herrorq hbudgetq
  intro s hs hsq M
  subst q
  let q := primeModulus s
  let H := ⌊(q : ℝ) ^ c⌋₊
  let U := ⌊(q : ℝ) ^ u⌋₊
  let V := ⌈(q : ℝ) ^ v⌉₊
  let D := coprimeDenominators s U
  let A : ℝ := (D.card : ℝ) * V
  let B : ℝ := (q : ℝ) ^ (c - η) / 2
  have : NeZero (primeModulus s) := ⟨(primeModulus_pos s hs).ne'⟩
  let W := amplifierNumerator (productChar s hs) M H D V
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq1
  have hHlo : (q : ℝ) ^ c / 2 ≤ (H : ℝ) := hHbounds.1
  have hHhi : (H : ℝ) ≤ (q : ℝ) ^ c := hHbounds.2
  have hUlo : (q : ℝ) ^ u / 2 ≤ (U : ℝ) := hUbounds.1
  have hUhi : (U : ℝ) ≤ (q : ℝ) ^ u := hUbounds.2
  have hVbounds := ceil_rpow_bounds hv hq1
  have hVlo : (q : ℝ) ^ v ≤ (V : ℝ) := hVbounds.1
  have hVhi : (V : ℝ) ≤ 2 * (q : ℝ) ^ v := hVbounds.2
  have hHpos : 0 < H := by
    have h : (0 : ℝ) < H := lt_of_lt_of_le (by positivity) hHlo
    exact_mod_cast h
  have hUpos : 0 < U := by
    have h : (0 : ℝ) < U := lt_of_lt_of_le (by positivity) hUlo
    exact_mod_cast h
  have hVpos : 0 < (V : ℝ) := (Real.rpow_pos_of_pos hq0 v).trans_le hVlo
  have hUroot : (q : ℝ) ^ (u / 2) ≤ U := by
    have h : (q : ℝ) ^ (u / 2) ≤ (q : ℝ) ^ u / 2 := by
      simpa only [one_mul, one_div, div_eq_mul_inv, mul_comm] using hrootq
    exact h.trans hUlo
  have hDbase : (U : ℝ) * (q : ℝ) ^ (-δ) ≤ (D.card : ℝ) := hd s hs hqd U hUroot
  have hDlo : (1 / 2 : ℝ) * (q : ℝ) ^ (u - δ) ≤ (D.card : ℝ) := by
    calc
      _ = ((q : ℝ) ^ u / 2) * (q : ℝ) ^ (-δ) := by
        rw [sub_eq_add_neg, Real.rpow_add hq0]
        ring
      _ ≤ (U : ℝ) * (q : ℝ) ^ (-δ) :=
        mul_le_mul_of_nonneg_right hUlo (Real.rpow_nonneg hq0.le _)
      _ ≤ _ := hDbase
  have hDpos : (0 : ℝ) < D.card := lt_of_lt_of_le (by positivity) hDlo
  have hApos : 0 < A := mul_pos hDpos hVpos
  have hUV : (U : ℝ) * V ≤ 2 * (q : ℝ) ^ (u + v) := by
    calc
      _ ≤ (q : ℝ) ^ u * (2 * (q : ℝ) ^ v) :=
        mul_le_mul hUhi hVhi (Nat.cast_nonneg V) (Real.rpow_nonneg hq0.le _)
      _ = _ := by rw [mul_left_comm, ← Real.rpow_add hq0]
  have hUVH : U * V ≤ H := by
    have h : (U : ℝ) * V ≤ H := hUV.trans (hshiftq.trans (by
      simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hHlo))
    exact_mod_cast h
  have hUHsmall : 2 * (U * H) < q := by
    have hUH : (U : ℝ) * H ≤ (q : ℝ) ^ (u + c) := by
      simpa only [Real.rpow_add hq0] using
        mul_le_mul hUhi hHhi (Nat.cast_nonneg H) (Real.rpow_nonneg hq0.le _)
    have hsmall' : 2 * (q : ℝ) ^ (u + c) ≤ (q : ℝ) / 2 := by
      simpa only [Real.rpow_one, one_div, div_eq_mul_inv, mul_comm, one_mul] using hsmallq
    have hstrict : 2 * ((U : ℝ) * H) < q := by
      have hle := (mul_le_mul_of_nonneg_left hUH (by norm_num : (0 : ℝ) ≤ 2)).trans hsmall'
      exact hle.trans_lt (half_lt_self hq0)
    exact_mod_cast hstrict
  have hWpow := amplifier_scale_le hq1 (productChar s hs) M H U V k D
    (Finset.filter_subset _ _) (fun _ h => (Finset.mem_filter.mp h).2)
    hHpos hUpos hUHsmall hu1 huδ hHhi hUhi hVhi hvk hlog (hm s hs hqm V)
  have hAB : (1 / 4 : ℝ) * (q : ℝ) ^ (u + v + c - δ - η) ≤ A * B := by
    have hprod := mul_le_mul hDlo hVlo (Real.rpow_nonneg hq0.le v) (le_of_lt hDpos)
    have hscaled := mul_le_mul_of_nonneg_right hprod
      (by dsimp [B]; positivity : 0 ≤ B)
    refine le_trans ?_ hscaled
    apply le_of_eq
    dsimp [B]
    rw [div_eq_mul_inv]
    calc
      _ = (1 / 4 : ℝ) * ((q : ℝ) ^ (u - δ) * (q : ℝ) ^ v * (q : ℝ) ^ (c - η)) := by
        rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
        congr 2
        ring
      _ = _ := by ring
  have hABpow := scaled_rpow_le_pow (by norm_num : (0 : ℝ) ≤ 1 / 4) hq0.le hAB (2 * (k + 1))
  have hWle : W ≤ A * B := le_of_pow_le_pow_left₀ (n := 2 * (k + 1)) (by omega)
    (by dsimp [A, B]; positivity) (hWpow.trans (hbudgetq.trans hABpow))
  have hamp := productChar_amplified_abs_le s hs (M := M) hUVH
  have hS : |∑ i ∈ Finset.range H, productChar s hs (M + i : ℕ)| ≤ B + 2 * (U : ℝ) * V := by
    apply (mul_le_mul_iff_right₀ hApos).mp
    change (D.card : ℝ) * V * |∑ i ∈ Finset.range H, productChar s hs (M + i : ℕ)| ≤ _
    calc
      _ ≤ W + 2 * (D.card : ℝ) * V * (U * V) := hamp
      _ ≤ A * B + 2 * A * ((U : ℝ) * V) := by
        dsimp only [A]
        nlinarith only [hWle]
      _ = _ := by ring
  have hboundary : 2 * (U : ℝ) * V ≤ (q : ℝ) ^ (c - η) / 2 := by
    have hUV2 := mul_le_mul_of_nonneg_left hUV (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [hUV2, herrorq]
  change |∑ i ∈ Finset.range H, productChar s hs (M + i : ℕ)| ≤ _
  dsimp only [B] at hS
  linarith

end Pollack17.Burgess

end

/-! ## Quadratic-character cancellation above the quarter-power scale

Source module `ErdosProblems.Erdos1141.BurgessQuarter`. -/

noncomputable section

namespace Pollack17.Burgess

open Filter

open scoped BigOperators

theorem eventually_quarter_block_cancellation {c : ℝ}
    (hc : 1 / 4 < c) (hc' : c < 1 / 2) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ q : ℕ in atTop,
      ∀ (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime), primeModulus s = q → ∀ M : ℕ,
        |∑ i ∈ Finset.range ⌊(q : ℝ) ^ c⌋₊, productChar s hs (M + i : ℕ)| ≤
          (q : ℝ) ^ (c - η) := by
  let e := c - 1 / 4
  have he : 0 < e := sub_pos.mpr hc
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / e)
  let v : ℝ := 1 / (2 * (k + 1 : ℝ))
  let u : ℝ := c - v - e / 4
  let η : ℝ := e / (64 * (k + 2 : ℝ))
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hv0 : 0 < v := by dsimp [v]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hveq : v * (k + 1 : ℝ) = 1 / 2 := by dsimp [v]; field_simp
  have hηeq : η * (64 * (k + 2 : ℝ)) = e := by dsimp [η]; field_simp
  have hvsmall : v < e / 4 := by
    have hek : 2 < (k : ℝ) * e := (div_lt_iff₀ he).mp hk
    dsimp [v]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (k + 1 : ℝ))).mpr
    nlinarith only [hek, he]
  have hηsmall : η < e / 4 := by
    have hkη : 0 ≤ (k : ℝ) * η := mul_nonneg hk0 hη.le
    nlinarith only [hηeq, hkη, hη]
  have hu : 0 < u := by dsimp [u, e] at *; linarith
  have hu1 : u ≤ 1 := by dsimp [u]; dsimp [e] at he; linarith
  have huδ : u ≤ c + η := by dsimp [u]; linarith
  have huv : u + v < c - η := by dsimp [u]; linarith
  have huc : u + c < 1 := by dsimp [u]; linarith
  have hgap : (c + u) * (2 * k + 1 : ℕ) + 3 / 2 + 3 * η <
      (u + v + c - η - η) * (2 * (k + 1) : ℕ) := by
    have hid : (u + v + c - η - η) * (2 * (k + 1) : ℕ) -
        ((c + u) * (2 * k + 1 : ℕ) + 3 / 2 + 3 * η) =
        2 * e - v - e / 4 - (4 * (k + 1 : ℝ) + 3) * η := by
      push_cast
      dsimp [u, e]
      nlinarith only [hveq]
    have hηloss : (4 * (k + 1 : ℝ) + 3) * η < e / 16 := by
      nlinarith only [hηeq, hη]
    apply sub_pos.mp
    rw [hid]
    nlinarith only [he, hvsmall, hηloss]
  exact ⟨η, hη, eventually_power_block_bound k (by linarith) hu hv0.le hη hη
    hu1 huδ huv huc hveq hgap⟩

end Pollack17.Burgess

end

/-! ## Extending fixed-block cancellation to every longer interval

Source module `ErdosProblems.Erdos1141.BurgessLongIntervals`. -/

noncomputable section

namespace Pollack17.Burgess

open Filter

open scoped BigOperators

theorem abs_sum_range_multiple_le (f : ℕ → ℝ) (H : ℕ) {B : ℝ}
    (hblock : ∀ M : ℕ, |∑ i ∈ Finset.range H, f (M + i)| ≤ B) (t M : ℕ) :
    |∑ i ∈ Finset.range (t * H), f (M + i)| ≤ (t : ℝ) * B := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.succ_mul, Finset.sum_range_add]
    have htail : (∑ i ∈ Finset.range H, f (M + (t * H + i))) =
        ∑ i ∈ Finset.range H, f (M + t * H + i) := by
      simp only [Nat.add_assoc]
    rw [htail]
    have htri := (abs_add_le _ _).trans (add_le_add ih (hblock (M + t * H)))
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using htri

theorem abs_sum_range_le_blocks (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {H : ℕ} (hH : 0 < H) {B : ℝ} (hB : 0 ≤ B)
    (hblock : ∀ M : ℕ, |∑ i ∈ Finset.range H, f (M + i)| ≤ B) (M L : ℕ) :
    |∑ i ∈ Finset.range L, f (M + i)| ≤ (L : ℝ) * (B / H) + H := by
  have hdecomp : L = (L / H) * H + L % H := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod L H).symm
  have heq : (∑ i ∈ Finset.range L, f (M + i)) =
      (∑ i ∈ Finset.range ((L / H) * H), f (M + i)) +
        ∑ i ∈ Finset.range (L % H), f (M + ((L / H) * H + i)) := by
    calc
      _ = ∑ i ∈ Finset.range ((L / H) * H + L % H), f (M + i) := by rw [← hdecomp]
      _ = _ := Finset.sum_range_add _ _ _
  have htail : |∑ i ∈ Finset.range (L % H), f (M + ((L / H) * H + i))| ≤ H := by
    calc
      _ ≤ ∑ i ∈ Finset.range (L % H), |f (M + ((L / H) * H + i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range (L % H), (1 : ℝ) := Finset.sum_le_sum fun i _ => hf _
      _ = (L % H : ℕ) := by simp
      _ ≤ (H : ℝ) := by exact_mod_cast (Nat.mod_lt L hH).le
  rw [heq]
  calc
    _ ≤ |∑ i ∈ Finset.range ((L / H) * H), f (M + i)| +
        |∑ i ∈ Finset.range (L % H), f (M + ((L / H) * H + i))| := abs_add_le _ _
    _ ≤ ((L / H : ℕ) : ℝ) * B + H :=
      add_le_add (abs_sum_range_multiple_le f H hblock (L / H) M) htail
    _ ≤ ((L : ℝ) / H) * B + H :=
      add_le_add (mul_le_mul_of_nonneg_right Nat.cast_div_le hB) le_rfl
    _ = _ := by ring

theorem block_bound_implies_long_bound {q : ℕ} (hq : 0 < q) {c η : ℝ}
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (hfloor : (q : ℝ) ^ c / 2 ≤ (⌊(q : ℝ) ^ c⌋₊ : ℝ))
    (hblock : ∀ M : ℕ, |∑ i ∈ Finset.range ⌊(q : ℝ) ^ c⌋₊, f (M + i)| ≤
      (q : ℝ) ^ (c - η)) (M L : ℕ) :
    |∑ i ∈ Finset.range L, f (M + i)| ≤
      2 * (L : ℝ) * (q : ℝ) ^ (-η) + (q : ℝ) ^ c := by
  let H := ⌊(q : ℝ) ^ c⌋₊
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  have hH0 : (0 : ℝ) < H := lt_of_lt_of_le (by positivity) hfloor
  have hHpos : 0 < H := by exact_mod_cast hH0
  have hratio : (q : ℝ) ^ (c - η) / H ≤ 2 * (q : ℝ) ^ (-η) := by
    apply (div_le_iff₀ hH0).mpr
    calc
      _ = (2 * (q : ℝ) ^ (-η)) * ((q : ℝ) ^ c / 2) := by
        rw [show c - η = -η + c by ring, Real.rpow_add hq0]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfloor (by positivity)
  have h := abs_sum_range_le_blocks f hf hHpos (Real.rpow_nonneg hq0.le _) hblock M L
  calc
    _ ≤ (L : ℝ) * ((q : ℝ) ^ (c - η) / H) + H := h
    _ ≤ (L : ℝ) * (2 * (q : ℝ) ^ (-η)) + (q : ℝ) ^ c :=
      add_le_add (mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg L))
        (Nat.floor_le (Real.rpow_nonneg hq0.le c))
    _ = _ := by ring

theorem eventually_squarefree_burgess {d : ℝ} (hd : 1 / 4 < d) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ q : ℕ in atTop,
      ∀ (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime), primeModulus s = q →
        ∀ M L : ℕ, (q : ℝ) ^ d ≤ L →
          |∑ i ∈ Finset.range L, productChar s hs (M + i : ℕ)| ≤
            (L : ℝ) * (q : ℝ) ^ (-σ) := by
  let c : ℝ := min ((d + 1 / 4) / 2) (3 / 8)
  have hc : 1 / 4 < c := lt_min (by linarith) (by norm_num)
  have hc' : c < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  have hcd : c < d := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨η, hη, hblock⟩ := eventually_quarter_block_cancellation hc hc'
  let σ : ℝ := min η (d - c) / 2
  have hσ : 0 < σ := half_pos (lt_min hη (sub_pos.mpr hcd))
  have hση : σ < η := by
    have h := min_le_left η (d - c)
    dsimp [σ]
    linarith
  have hσd : σ < d - c := by
    have h := min_le_right η (d - c)
    dsimp [σ]
    linarith
  have hmain := eventually_const_mul_rpow_le (C := 2) (d := 1 / 2)
    (a := -η) (b := -σ) (by norm_num) (by linarith)
  have hrem := eventually_const_mul_rpow_le (C := 1) (d := 1 / 2)
    (a := c) (b := d - σ) (by norm_num) (by linarith)
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hblock, hmain, hrem, eventually_floor_rpow_bounds (by linarith : 0 < c),
    eventually_ge_atTop 1] with q hblockq hmainq hremq hfloor hq1
  intro s hs hsq M L hL
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq1
  have hb := block_bound_implies_long_bound (by omega : 0 < q)
    (fun n => productChar s hs (n : ℕ))
    (fun n => abs_productChar_le_one s hs _) hfloor.1 (hblockq s hs hsq) M L
  have hfirst : 2 * (L : ℝ) * (q : ℝ) ^ (-η) ≤
      (1 / 2 : ℝ) * ((L : ℝ) * (q : ℝ) ^ (-σ)) := by
    have h := mul_le_mul_of_nonneg_left hmainq (Nat.cast_nonneg L)
    nlinarith only [h]
  have hsecond : (q : ℝ) ^ c ≤ (1 / 2 : ℝ) * ((L : ℝ) * (q : ℝ) ^ (-σ)) := by
    have hrem' : (q : ℝ) ^ c ≤ (1 / 2 : ℝ) * ((q : ℝ) ^ d * (q : ℝ) ^ (-σ)) := by
      simpa only [one_mul, sub_eq_add_neg, Real.rpow_add hq0] using hremq
    exact hrem'.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hq0.le _)) (by norm_num))
  nlinarith only [hb, hfirst, hsecond]

end Pollack17.Burgess

end

/-! ## Classifying quadratic characters on finite fields

Source module `ErdosProblems.Erdos1141.QuadraticFieldClassification`. -/

noncomputable section

namespace Pollack17

theorem quadratic_apply_square_unit {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) {x : R} (hx : IsUnit x) (hsq : IsSquare x) :
    χ x = 1 := by
  obtain ⟨r, rfl⟩ := hsq
  have hr : IsUnit r := (IsUnit.mul_iff.mp hx).1
  have hrnz : χ r ≠ 0 := MulChar.apply_ne_zero_iff.mpr hr
  rw [map_mul]
  rcases hχ r with h | h | h
  · exact (hrnz h).elim
  · simp [h]
  · simp [h]

theorem quadratic_field_eq_quadraticChar {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (hχ : χ.IsQuadratic) (hne : χ ≠ 1) :
    ∀ x : F, χ x = (quadraticChar F x : ℂ) := by
  classical
  obtain ⟨a, ha⟩ := MulChar.ne_one_iff.mp hne
  have ha0 : χ (a : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr a.isUnit
  have haχ : χ (a : F) = -1 := by
    rcases hχ a with h | h | h
    · exact (ha0 h).elim
    · exact (ha h).elim
    · exact h
  have hansq : ¬IsSquare (a : F) := fun h =>
    ha (quadratic_apply_square_unit χ hχ a.isUnit h)
  have haq : quadraticChar F (a : F) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hansq
  intro x
  by_cases hx : x = 0
  · subst x
    simp only [quadraticChar_zero, Int.cast_zero]
    exact χ.map_nonunit not_isUnit_zero
  by_cases hxsq : IsSquare x
  · rw [quadratic_apply_square_unit χ hχ (isUnit_iff_ne_zero.mpr hx) hxsq,
      (quadraticChar_one_iff_isSquare hx).mpr hxsq]
    norm_num
  have hxq : quadraticChar F x = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hxsq
  have hxaq : quadraticChar F (x * a) = 1 := by rw [map_mul, hxq, haq]; norm_num
  have hxasq : IsSquare (x * (a : F)) :=
    (quadraticChar_one_iff_isSquare (mul_ne_zero hx a.ne_zero)).mp hxaq
  have hxachi := quadratic_apply_square_unit χ hχ
    ((isUnit_iff_ne_zero.mpr hx).mul a.isUnit) hxasq
  rw [map_mul, haχ] at hxachi
  rw [hxq]
  linear_combination -hxachi

end Pollack17

end

/-! ## Quadratic characters on a finite product of unit groups

Source module `ErdosProblems.Erdos1141.QuadraticCharacterProducts`. -/

noncomputable section

namespace Pollack17

open scoped BigOperators

noncomputable def pullbackUnitChar {R S : Type*} [CommMonoid R] [CommMonoid S]
    (χ : MulChar R ℂ) (f : Sˣ →* Rˣ) : MulChar S ℂ :=
  MulChar.ofUnitHom (χ.toUnitHom.comp f)

theorem pullbackUnitChar_apply_unit {R S : Type*} [CommMonoid R] [CommMonoid S]
    (χ : MulChar R ℂ) (f : Sˣ →* Rˣ) (x : Sˣ) :
    pullbackUnitChar χ f x = χ (f x : R) := by
  simp only [pullbackUnitChar, MulChar.ofUnitHom_coe, MonoidHom.comp_apply,
    MulChar.coe_toUnitHom]

theorem pullbackUnitChar_isQuadratic {R S : Type*} [CommMonoid R] [CommMonoid S]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) (f : Sˣ →* Rˣ) :
    (pullbackUnitChar χ f).IsQuadratic := by
  intro x
  by_cases hx : IsUnit x
  · have heq : pullbackUnitChar χ f x = χ (f hx.unit : R) :=
      pullbackUnitChar_apply_unit χ f hx.unit
    rw [heq]
    exact hχ _
  · exact Or.inl ((pullbackUnitChar χ f).map_nonunit hx)

noncomputable def productUnitEmbedding {ι : Type*} [DecidableEq ι]
    (R : ι → Type*) [∀ i, CommMonoid (R i)] (i : ι) :
    (R i)ˣ →* (∀ j, R j)ˣ :=
  (MulEquiv.piUnits (M := R)).symm.toMonoidHom.comp
    (MonoidHom.mulSingle (fun j => (R j)ˣ) i)

theorem productUnitEmbedding_val {ι : Type*} [DecidableEq ι]
    (R : ι → Type*) [∀ i, CommMonoid (R i)] (i : ι) (x : (R i)ˣ) :
    (productUnitEmbedding R i x : ∀ j, R j) = Pi.mulSingle i (x : R i) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [productUnitEmbedding, MulEquiv.piUnits]
  · simp [productUnitEmbedding, MulEquiv.piUnits, hji]

theorem prod_productUnitEmbedding {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ι → Type*) [∀ i, CommMonoid (R i)] (x : (∀ j, R j)ˣ) :
    (∏ i, productUnitEmbedding R i (MulEquiv.piUnits x i)) = x := by
  apply Units.ext
  ext j
  simp only [Units.coe_prod, Finset.prod_apply, productUnitEmbedding_val]
  exact Fintype.prod_pi_mulSingle j (fun i => (x : ∀ j, R j) i)

noncomputable def productComponentChar {ι : Type*} [DecidableEq ι]
    (R : ι → Type*) [∀ i, CommMonoid (R i)] (χ : MulChar (∀ j, R j) ℂ) (i : ι) :
    MulChar (R i) ℂ := pullbackUnitChar χ (productUnitEmbedding R i)

theorem productComponentChar_isQuadratic {ι : Type*} [DecidableEq ι]
    (R : ι → Type*) [∀ i, CommMonoid (R i)]
    (χ : MulChar (∀ j, R j) ℂ) (hχ : χ.IsQuadratic) (i : ι) :
    (productComponentChar R χ i).IsQuadratic :=
  pullbackUnitChar_isQuadratic χ hχ _

theorem character_eq_prod_components {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ι → Type*) [∀ i, CommMonoid (R i)]
    (χ : MulChar (∀ j, R j) ℂ) (x : (∀ j, R j)ˣ) :
    χ (x : ∀ j, R j) = ∏ i, productComponentChar R χ i ((x : ∀ j, R j) i) := by
  calc
    _ = χ ((∏ i, productUnitEmbedding R i (MulEquiv.piUnits x i) : (∀ j, R j)ˣ) : ∀ j, R j) := by
      rw [prod_productUnitEmbedding]
    _ = ∏ i, χ (productUnitEmbedding R i (MulEquiv.piUnits x i) : ∀ j, R j) := by
      rw [Units.coe_prod, map_prod]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact (pullbackUnitChar_apply_unit χ (productUnitEmbedding R i) (MulEquiv.piUnits x i)).symm

end Pollack17

end

/-! ## Prime-power components of an arbitrary quadratic Dirichlet character

Source module `ErdosProblems.Erdos1141.QuadraticPrimePowerComponents`. -/

noncomputable section

namespace Pollack17

open scoped BigOperators

noncomputable def primePowerCRT (m : ℕ) (hm : m ≠ 0) :
    ZMod m ≃+* (∀ p : m.primeFactors, ZMod ((p : ℕ) ^ m.factorization p)) := by
  have hprod := Nat.prod_primeFactors_coe_pow_factorization hm
  refine (ZMod.ringEquivCongr hprod).trans (ZMod.prodEquivPi _ ?_)
  intro p r hpr
  have hp := Nat.prime_of_mem_primeFactors p.property
  have hr := Nat.prime_of_mem_primeFactors r.property
  have hcop : (p : ℕ).Coprime (r : ℕ) := (Nat.coprime_primes hp hr).mpr (by
    intro h
    exact hpr (Subtype.ext h))
  exact hcop.pow _ _

theorem primePowerCRT_natCast (m : ℕ) (hm : m ≠ 0) (a : ℕ) (p : m.primeFactors) :
    primePowerCRT m hm (a : ZMod m) p = (a : ZMod ((p : ℕ) ^ m.factorization p)) := by
  simp [primePowerCRT]

theorem exists_quadratic_primePower_components {m : ℕ} (hm : m ≠ 0)
    (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic) :
    ∃ ψ : ∀ p : m.primeFactors, DirichletCharacter ℂ ((p : ℕ) ^ m.factorization p),
      (∀ p, (ψ p).IsQuadratic) ∧
        ∀ a : ℕ, a.Coprime m → χ (a : ZMod m) =
          ∏ p : m.primeFactors, ψ p (a : ZMod ((p : ℕ) ^ m.factorization p)) := by
  classical
  let R : m.primeFactors → Type := fun p => ZMod ((p : ℕ) ^ m.factorization p)
  let e := primePowerCRT m hm
  let eU := Units.mapEquiv e.toMulEquiv
  let χ' := pullbackUnitChar χ eU.symm.toMonoidHom
  have hχ' : χ'.IsQuadratic := pullbackUnitChar_isQuadratic χ hχ _
  refine ⟨productComponentChar R χ', productComponentChar_isQuadratic R χ' hχ', ?_⟩
  intro a ha
  let x := ZMod.unitOfCoprime a ha
  have hχx : χ (a : ZMod m) = χ' (eU x : ∀ p, R p) := by
    have h := pullbackUnitChar_apply_unit χ eU.symm.toMonoidHom (eU x)
    simpa only [x, χ', MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, ZMod.coe_unitOfCoprime]
      using h.symm
  rw [hχx, character_eq_prod_components R χ' (eU x)]
  apply Finset.prod_congr rfl
  intro p _
  congr 1
  change e (a : ZMod m) p = (a : R p)
  exact primePowerCRT_natCast m hm a p

end Pollack17

end

/-! ## Squares in the principal congruence subgroups of prime-power units

Source module `ErdosProblems.Erdos1141.QuadraticPrimePowerSquares`. -/

noncomputable section

namespace Pollack17

open Polynomial

theorem isSquare_zmod_prime_pow_of_norm {p : ℕ} [Fact p.Prime]
    (a : ℤ) (n : ℕ) (ha : ‖((1 - a : ℤ) : ℤ_[p])‖ < ‖(2 : ℤ_[p])‖ ^ 2) :
    IsSquare (a : ZMod (p ^ n)) := by
  let F : Polynomial ℤ := X ^ 2 - C a
  have hder : F.derivative.aeval (1 : ℤ_[p]) = (2 : ℤ_[p]) := by
    norm_num [F, derivative_sub, derivative_pow, derivative_X]
    exact map_ofNat (aeval (1 : ℤ_[p])) 2
  have hnorm : ‖F.aeval (1 : ℤ_[p])‖ < ‖F.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    rw [hder]
    simpa [F] using ha
  obtain ⟨z, hz, _⟩ := hensels_lemma hnorm
  have hsq : z ^ 2 = (a : ℤ_[p]) := by simpa [F, sub_eq_zero] using hz
  refine ⟨PadicInt.toZModPow n z, ?_⟩
  have hmap := congrArg (PadicInt.toZModPow n) hsq
  simpa only [map_pow, map_mul, map_intCast, pow_two] using hmap.symm

theorem isSquare_zmod_odd_prime_pow_of_one_mod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a : ℤ) (n : ℕ) (ha : (p : ℤ) ∣ 1 - a) : IsSquare (a : ZMod (p ^ n)) := by
  have : Fact p.Prime := ⟨hp⟩
  apply isSquare_zmod_prime_pow_of_norm a n
  have hnorm : ‖(2 : ℤ_[p])‖ = 1 :=
    PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  rw [hnorm, one_pow]
  exact (PadicInt.norm_int_lt_one_iff_dvd (1 - a)).mpr ha

theorem isSquare_zmod_two_pow_of_one_mod_eight (a : ℤ) (n : ℕ)
    (ha : (8 : ℤ) ∣ 1 - a) : IsSquare (a : ZMod (2 ^ n)) := by
  apply isSquare_zmod_prime_pow_of_norm a n
  have hnorm : ‖((1 - a : ℤ) : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-(3 : ℕ) : ℤ) :=
    PadicInt.norm_int_le_pow_iff_dvd.mpr (by simpa using ha)
  have htwo : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := PadicInt.norm_p
  rw [htwo]
  refine hnorm.trans_lt ?_
  norm_num

end Pollack17

end

/-! ## Reducing quadratic characters at prime powers

Source module `ErdosProblems.Erdos1141.QuadraticPrimePowerReduction`. -/

noncomputable section

namespace Pollack17

theorem quadratic_factorsThrough_of_kernel_squares {m d : ℕ} [NeZero m]
    (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic) (hd : d ∣ m)
    (hsquare : ∀ a : ℤ, (d : ℤ) ∣ 1 - a → IsSquare (a : ZMod m)) :
    χ.FactorsThrough d := by
  apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  apply Units.ext
  change χ (x : ZMod m) = 1
  apply quadratic_apply_square_unit χ hχ x.isUnit
  have hval : (((x : ZMod m).val : ℕ) : ZMod d) = 1 := by
    have h := congrArg Units.val hx
    simpa only [ZMod.unitsMap_val, ZMod.cast_eq_val, Units.val_one] using h
  have hdiv : (d : ℤ) ∣ 1 - ((x : ZMod m).val : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_sub, Int.cast_one, Int.cast_natCast, hval, sub_self]
  have hsq := hsquare ((x : ZMod m).val : ℤ) hdiv
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hsq

theorem quadratic_odd_prime_power_factorsThrough {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n)
    (χ : DirichletCharacter ℂ (p ^ n)) (hχ : χ.IsQuadratic) :
    χ.FactorsThrough p := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply quadratic_factorsThrough_of_kernel_squares χ hχ (dvd_pow_self p (by omega : n ≠ 0))
  exact fun a ha => isSquare_zmod_odd_prime_pow_of_one_mod hp hp2 a n ha

theorem quadratic_two_power_factorsThrough {n : ℕ} (hn : 3 ≤ n)
    (χ : DirichletCharacter ℂ (2 ^ n)) (hχ : χ.IsQuadratic) :
    χ.FactorsThrough 8 := by
  have : NeZero (2 ^ n) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hd : 8 ∣ 2 ^ n := by
    have h := Nat.pow_dvd_pow 2 hn
    norm_num at h
    exact h
  exact quadratic_factorsThrough_of_kernel_squares χ hχ hd
    (fun a ha => isSquare_zmod_two_pow_of_one_mod_eight a n ha)

theorem quadratic_of_changeLevel {m d : ℕ} [NeZero m] (hd : d ∣ m)
    (ψ : DirichletCharacter ℂ d) (hψ : (DirichletCharacter.changeLevel hd ψ).IsQuadratic) :
    ψ.IsQuadratic := by
  apply MulChar.isQuadratic_iff_sq_eq_one.mpr
  apply DirichletCharacter.changeLevel_injective hd
  rw [map_pow, map_one, hψ.sq_eq_one]

theorem changeLevel_natCast {R : Type*} [CommMonoidWithZero R] {m d : ℕ}
    (hd : d ∣ m) (ψ : DirichletCharacter R d)
    (a : ℕ) (ha : a.Coprime m) :
    DirichletCharacter.changeLevel hd ψ (a : ZMod m) = ψ (a : ZMod d) := by
  have h := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ hd (ZMod.unitOfCoprime a ha)
  simpa only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd] using h

theorem quadratic_odd_prime_power_values {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n)
    (χ : DirichletCharacter ℂ (p ^ n)) (hχ : χ.IsQuadratic) :
    letI : Fact p.Prime := ⟨hp⟩
    ∃ b : Bool, ∀ a : ℕ, a.Coprime p → χ (a : ZMod (p ^ n)) =
      if b then (quadraticChar (ZMod p) (a : ZMod p) : ℂ) else 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let hfactor := quadratic_odd_prime_power_factorsThrough hp hp2 hn χ hχ
  let ψ := hfactor.χ₀
  have hψ : ψ.IsQuadratic := quadratic_of_changeLevel hfactor.dvd ψ (by
    rw [← hfactor.eq_changeLevel]
    exact hχ)
  have heval (a : ℕ) (ha : a.Coprime p) : χ (a : ZMod (p ^ n)) = ψ (a : ZMod p) := by
    rw [hfactor.eq_changeLevel]
    exact changeLevel_natCast hfactor.dvd ψ a (ha.pow_right n)
  by_cases hψ1 : ψ = 1
  · refine ⟨false, fun a ha => ?_⟩
    rw [heval a ha, hψ1]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime a p).mpr ha)
  · refine ⟨true, fun a ha => ?_⟩
    rw [heval a ha]
    exact quadratic_field_eq_quadraticChar ψ hψ hψ1 _

theorem quadratic_two_power_small_level (n : ℕ)
    (χ : DirichletCharacter ℂ (2 ^ n)) (hχ : χ.IsQuadratic) :
    ∃ e : ℕ, e ≤ 3 ∧ e ≤ n ∧ ∃ θ : DirichletCharacter ℂ (2 ^ e), θ.IsQuadratic ∧
      ∀ a : ℕ, a.Coprime (2 ^ n) → χ (a : ZMod (2 ^ n)) = θ (a : ZMod (2 ^ e)) := by
  by_cases hn : n ≤ 3
  · exact ⟨n, hn, le_rfl, χ, hχ, fun _ _ => rfl⟩
  have : NeZero (2 ^ n) := ⟨pow_ne_zero _ (by norm_num)⟩
  let hfactor := quadratic_two_power_factorsThrough (by omega : 3 ≤ n) χ hχ
  let θ := hfactor.χ₀
  have hθ : θ.IsQuadratic := quadratic_of_changeLevel hfactor.dvd θ (by
    rw [← hfactor.eq_changeLevel]
    exact hχ)
  refine ⟨3, le_rfl, by omega, θ, hθ, fun a ha => ?_⟩
  rw [hfactor.eq_changeLevel]
  exact changeLevel_natCast hfactor.dvd θ a ha

end Pollack17

end

/-! ## Decomposing every quadratic Dirichlet character on the units

Source module `ErdosProblems.Erdos1141.QuadraticDecomposition`. -/

noncomputable section

namespace Pollack17

open scoped BigOperators

noncomputable def quadraticPrimeValue (p a : ℕ) : ℂ := by
  classical
  exact if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    (quadraticChar (ZMod p) (a : ZMod p) : ℂ)
  else 0

theorem exists_subset_product_choices (s : Finset ℕ) (f g : ℕ → ℕ → ℂ) (P : ℕ → Prop)
    (h : ∀ p ∈ s, ∃ b : Bool, ∀ a, P a → f p a = if b then g p a else 1) :
    ∃ t ⊆ s, ∀ a, P a → (∏ p ∈ s, f p a) = ∏ p ∈ t, g p a := by
  classical
  choose b hb using h
  let B : ℕ → Bool := fun p => if hp : p ∈ s then b p hp else false
  refine ⟨s.filter (fun p => B p), Finset.filter_subset _ _, fun a ha => ?_⟩
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  simpa only [B, dif_pos hp] using hb p hp a ha

theorem quadratic_character_decomposition {m : ℕ} (hm : m ≠ 0)
    (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic) :
    ∃ s : Finset ℕ, s ⊆ m.primeFactors.erase 2 ∧
      ∃ e : ℕ, e ≤ 3 ∧ e ≤ m.factorization 2 ∧
        ∃ θ : DirichletCharacter ℂ (2 ^ e), θ.IsQuadratic ∧
          ∀ a : ℕ, a.Coprime m → χ (a : ZMod m) =
            θ (a : ZMod (2 ^ e)) * ∏ p ∈ s, quadraticPrimeValue p a := by
  classical
  obtain ⟨ψ, hψ, hprod⟩ := exists_quadratic_primePower_components hm χ hχ
  let f : ℕ → ℕ → ℂ := fun p a =>
    if hp : p ∈ m.primeFactors then ψ ⟨p, hp⟩ (a : ZMod (p ^ m.factorization p)) else 1
  have hlocal : ∀ p ∈ m.primeFactors.erase 2, ∃ b : Bool,
      ∀ a : ℕ, a.Coprime m → f p a = if b then quadraticPrimeValue p a else 1 := by
    intro p hp
    have hpne : p ≠ 2 := (Finset.mem_erase.mp hp).1
    have hpm : p ∈ m.primeFactors := (Finset.mem_erase.mp hp).2
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpm
    have : Fact p.Prime := ⟨hpp⟩
    have he : 0 < m.factorization p :=
      hpp.factorization_pos_of_dvd hm (Nat.dvd_of_mem_primeFactors hpm)
    obtain ⟨b, hb⟩ := quadratic_odd_prime_power_values hpp hpne he (ψ ⟨p, hpm⟩) (hψ ⟨p, hpm⟩)
    refine ⟨b, fun a ha => ?_⟩
    have hap : a.Coprime p := ha.of_dvd_right (Nat.dvd_of_mem_primeFactors hpm)
    simpa only [f, dif_pos hpm, quadraticPrimeValue, dif_pos hpp] using hb a hap
  obtain ⟨s, hs, hodd⟩ := exists_subset_product_choices (m.primeFactors.erase 2) f
    quadraticPrimeValue (fun a => a.Coprime m) hlocal
  have htwo : ∃ e : ℕ, e ≤ 3 ∧ e ≤ m.factorization 2 ∧
      ∃ θ : DirichletCharacter ℂ (2 ^ e), θ.IsQuadratic ∧
        ∀ a : ℕ, a.Coprime m → f 2 a = θ (a : ZMod (2 ^ e)) := by
    by_cases h2 : 2 ∈ m.primeFactors
    · obtain ⟨e, he3, hem, θ, hθ, heval⟩ :=
        quadratic_two_power_small_level (m.factorization 2) (ψ ⟨2, h2⟩) (hψ ⟨2, h2⟩)
      refine ⟨e, he3, hem, θ, hθ, fun a ha => ?_⟩
      have hd : 2 ^ m.factorization 2 ∣ m :=
        Nat.prime_two.pow_dvd_iff_le_factorization hm |>.mpr le_rfl
      simpa only [f, dif_pos h2] using heval a (ha.of_dvd_right hd)
    · refine ⟨0, by omega, Nat.zero_le _, 1, ?_, fun a ha => ?_⟩
      · exact MulChar.isQuadratic_iff_sq_eq_one.mpr (one_pow 2)
      · have hunit : IsUnit (a : ZMod (2 ^ 0)) :=
          (ZMod.isUnit_iff_coprime a _).mpr (by simp)
        simp only [f, dif_neg h2, MulChar.one_apply hunit]
  obtain ⟨e, he3, hem, θ, hθ, heval⟩ := htwo
  refine ⟨s, hs, e, he3, hem, θ, hθ, fun a ha => ?_⟩
  have hprod' : χ (a : ZMod m) = ∏ p ∈ m.primeFactors, f p a := by
    rw [hprod a ha]
    rw [← Finset.prod_coe_sort m.primeFactors (fun p => f p a)]
    apply Finset.prod_congr rfl
    intro p _
    simp only [f, dif_pos p.property]
  rw [hprod']
  have hsplit : (∏ p ∈ m.primeFactors, f p a) =
      f 2 a * ∏ p ∈ m.primeFactors.erase 2, f p a := by
    by_cases h2 : 2 ∈ m.primeFactors
    · exact (Finset.mul_prod_erase _ _ h2).symm
    · simp only [Finset.erase_eq_of_notMem h2, f, dif_neg h2, one_mul]
  rw [hsplit, heval a ha, hodd a ha]

end Pollack17

end

/-! ## Real-valued quadratic characters and the product-character interface

Source module `ErdosProblems.Erdos1141.QuadraticRealCharacter`. -/

noncomputable section

namespace Pollack17

open scoped BigOperators

theorem quadratic_apply_im_zero {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) (x : R) : (χ x).im = 0 := by
  rcases hχ x with h | h | h <;> simp [h]

noncomputable def quadraticRealChar {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) : MulChar R ℝ where
  toFun x := (χ x).re
  map_one' := by rw [map_one, Complex.one_re]
  map_mul' x y := by
    rw [map_mul, Complex.mul_re, quadratic_apply_im_zero χ hχ, zero_mul, sub_zero]
  map_nonunit' x hx := by rw [χ.map_nonunit hx, Complex.zero_re]

theorem quadraticRealChar_apply {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) (x : R) :
    quadraticRealChar χ hχ x = (χ x).re := rfl

theorem quadraticRealChar_isQuadratic {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) : (quadraticRealChar χ hχ).IsQuadratic := by
  intro x
  rcases hχ x with h | h | h
  · exact Or.inl (by simp [quadraticRealChar_apply, h])
  · exact Or.inr (Or.inl (by simp [quadraticRealChar_apply, h]))
  · exact Or.inr (Or.inr (by simp [quadraticRealChar_apply, h]))

theorem ofReal_quadraticRealChar {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) (x : R) :
    (quadraticRealChar χ hχ x : ℂ) = χ x := by
  apply Complex.ext
  · rfl
  · exact (quadratic_apply_im_zero χ hχ x).symm

theorem product_quadraticPrimeValue_eq (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (a : ℕ) :
    (∏ p ∈ s, quadraticPrimeValue p a) =
      (Burgess.productChar s hs (a : ZMod (Burgess.primeModulus s)) : ℂ) := by
  classical
  rw [Burgess.productChar, Complex.ofReal_prod]
  rw [← Finset.prod_coe_sort s (fun p => quadraticPrimeValue p a)]
  apply Finset.prod_congr rfl
  intro p _
  rw [Burgess.primeCRT_natCast]
  simp only [quadraticPrimeValue, dif_pos (hs p p.property), Burgess.localChar, Burgess.qchar,
    Complex.ofReal_intCast]

theorem quadratic_character_real_decomposition {m : ℕ} (hm : m ≠ 0)
    (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic) :
    ∃ s : Finset ℕ, s ⊆ m.primeFactors.erase 2 ∧
      ∃ hs : ∀ p ∈ s, p.Prime, ∃ e : ℕ, e ≤ 3 ∧ e ≤ m.factorization 2 ∧
        ∃ θ : DirichletCharacter ℝ (2 ^ e), θ.IsQuadratic ∧
          ∀ a : ℕ, a.Coprime m → quadraticRealChar χ hχ (a : ZMod m) =
            θ (a : ZMod (2 ^ e)) * Burgess.productChar s hs
              (a : ZMod (Burgess.primeModulus s)) := by
  obtain ⟨s, hsm, e, he3, hem, θ, hθ, heval⟩ := quadratic_character_decomposition hm χ hχ
  have hs : ∀ p ∈ s, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp (hsm hp)).2
  refine ⟨s, hsm, hs, e, he3, hem, quadraticRealChar θ hθ,
    quadraticRealChar_isQuadratic θ hθ, fun a ha => ?_⟩
  have h := congrArg Complex.re (heval a ha)
  rw [product_quadraticPrimeValue_eq s hs a] at h
  simpa only [quadraticRealChar_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] using h

end Pollack17

end

/-! ## The short two-adic factor and arithmetic progressions

Source module `ErdosProblems.Erdos1141.BurgessProgressions`. -/

noncomputable section

namespace Pollack17.Burgess

open Filter

open scoped BigOperators

theorem sum_range_mul_eq_progressions (f : ℕ → ℝ) (h t M : ℕ) :
    (∑ i ∈ Finset.range (t * h), f (M + i)) =
      ∑ a ∈ Finset.range h, ∑ j ∈ Finset.range t, f (M + a + h * j) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    simp_rw [Finset.sum_range_succ]
    rw [Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    ac_rfl

theorem abs_sum_range_le_progressions (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {h : ℕ} (hh : 0 < h) (M H : ℕ) {B : ℝ}
    (hbound : ∀ a ∈ Finset.range h,
      |∑ j ∈ Finset.range (H / h), f (M + a + h * j)| ≤ B) :
    |∑ i ∈ Finset.range H, f (M + i)| ≤ (h : ℝ) * B + h := by
  have hdecomp : H = (H / h) * h + H % h := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod H h).symm
  have heq : (∑ i ∈ Finset.range H, f (M + i)) =
      (∑ a ∈ Finset.range h, ∑ j ∈ Finset.range (H / h), f (M + a + h * j)) +
        ∑ i ∈ Finset.range (H % h), f (M + ((H / h) * h + i)) := by
    calc
      _ = ∑ i ∈ Finset.range ((H / h) * h + H % h), f (M + i) := by rw [← hdecomp]
      _ = _ := by rw [Finset.sum_range_add, sum_range_mul_eq_progressions]
  have hmain : |∑ a ∈ Finset.range h,
      ∑ j ∈ Finset.range (H / h), f (M + a + h * j)| ≤ (h : ℝ) * B := by
    calc
      _ ≤ ∑ a ∈ Finset.range h, |∑ j ∈ Finset.range (H / h), f (M + a + h * j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ Finset.range h, B := Finset.sum_le_sum hbound
      _ = _ := by simp
  have htail : |∑ i ∈ Finset.range (H % h), f (M + ((H / h) * h + i))| ≤ h := by
    calc
      _ ≤ ∑ i ∈ Finset.range (H % h), |f (M + ((H / h) * h + i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range (H % h), (1 : ℝ) := Finset.sum_le_sum fun i _ => hf _
      _ = (H % h : ℕ) := by simp
      _ ≤ (h : ℝ) := by exact_mod_cast (Nat.mod_lt H hh).le
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hmain htail)

theorem abs_twisted_progression_sum_le (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] {h : ℕ} (hcop : h.Coprime (primeModulus s))
    (θ : DirichletCharacter ℝ h) (hθ : θ.IsQuadratic) (a L : ℕ) {B : ℝ} (_hB : 0 ≤ B)
    (hbound : ∀ M : ℕ, |∑ j ∈ Finset.range L,
      productChar s hs (M + j : ℕ)| ≤ B) :
    |∑ j ∈ Finset.range L,
      θ (a + h * j : ℕ) * productChar s hs (a + h * j : ℕ)| ≤ B := by
  let q := primeModulus s
  let t : ℕ := ((h : ZMod q)⁻¹ * a).val
  have halg (j : ℕ) : ((a + h * j : ℕ) : ZMod q) =
      (h : ZMod q) * (t + j : ℕ) := by
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul]
    dsimp only [t]
    rw [ZMod.natCast_zmod_val, mul_add, ← mul_assoc, ZMod.coe_mul_inv_eq_one h hcop, one_mul]
  have hterm (j : ℕ) : θ (a + h * j : ℕ) * productChar s hs (a + h * j : ℕ) =
      (θ (a : ZMod h) * productChar s hs (h : ZMod q)) * productChar s hs (t + j : ℕ) := by
    have hθval : θ (a + h * j : ℕ) = θ (a : ZMod h) := by
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
    rw [hθval, halg, productChar_mul]
    ring
  have hθabs : |θ (a : ZMod h)| ≤ 1 := by
    rcases hθ (a : ZMod h) with hz | hz | hz <;> norm_num [hz]
  have hcoeff : |θ (a : ZMod h) * productChar s hs (h : ZMod q)| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hθabs (abs_productChar_le_one s hs _) (abs_nonneg _) (by norm_num)).trans_eq
      (one_mul 1)
  simp_rw [hterm]
  rw [← Finset.mul_sum, abs_mul]
  exact (mul_le_mul hcoeff (hbound t) (abs_nonneg _) (by norm_num)).trans_eq (one_mul B)

theorem div_small_modulus_ge_scale {H h : ℕ} (hh : 0 < h) (hh8 : h ≤ 8)
    {Q : ℝ} (hQ : 1 ≤ Q) (hH : 16 * Q ≤ H) : Q ≤ ((H / h : ℕ) : ℝ) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hh8' : (h : ℝ) ≤ 8 := by exact_mod_cast hh8
  have hdiv : (H : ℝ) / h < ((H / h : ℕ) : ℝ) + 1 := by
    simpa only [Nat.floor_div_eq_div] using Nat.lt_floor_add_one ((H : ℝ) / h)
  have hHlt := (div_lt_iff₀ hh0).mp hdiv
  have hmul := mul_le_mul_of_nonneg_left hh8'
    (by positivity : (0 : ℝ) ≤ ((H / h : ℕ) : ℝ) + 1)
  linarith only [hQ, hH, hHlt, hmul]

theorem eventually_twisted_squarefree_burgess {d : ℝ} (hd : 1 / 4 < d) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ q : ℕ in atTop,
      ∀ (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime), primeModulus s = q →
        ∀ h : ℕ, 0 < h → h ≤ 8 → h.Coprime q →
          ∀ θ : DirichletCharacter ℝ h, θ.IsQuadratic →
            ∀ M H : ℕ, (q : ℝ) ^ d ≤ H →
              |∑ i ∈ Finset.range H, θ (M + i : ℕ) * productChar s hs (M + i : ℕ)| ≤
                (H : ℝ) * (q : ℝ) ^ (-σ) := by
  let c : ℝ := (d + 1 / 4) / 2
  have hc : 1 / 4 < c := by dsimp [c]; linarith
  have hcd : c < d := by dsimp [c]; linarith
  have hd0 : 0 < d := by linarith
  obtain ⟨η, hη, hburgess⟩ := eventually_squarefree_burgess hc
  let σ : ℝ := min η d / 2
  have hσ : 0 < σ := half_pos (lt_min hη hd0)
  have hση : σ < η := by have h := min_le_left η d; dsimp [σ]; linarith
  have hσd : σ < d := by have h := min_le_right η d; dsimp [σ]; linarith
  have hscale := eventually_const_mul_rpow_le (C := 16) (d := 1) (by norm_num) hcd
  have hmain := eventually_const_mul_rpow_le (C := 1) (d := 1 / 2)
    (a := -η) (b := -σ) (by norm_num) (by linarith)
  have htail := eventually_const_mul_rpow_le (C := 8) (d := 1 / 2)
    (a := 0) (b := d - σ) (by norm_num) (by linarith)
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hburgess, hscale, hmain, htail, eventually_ge_atTop 1]
    with q hburgessq hscaleq hmainq htailq hq1
  intro s hs hsq h hh hh8 hcop θ hθ M H hH
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq1
  have : NeZero (primeModulus s) := ⟨(primeModulus_pos s hs).ne'⟩
  have hcop' : h.Coprime (primeModulus s) := by simpa only [hsq] using hcop
  have hscale' : 16 * (q : ℝ) ^ c ≤ (q : ℝ) ^ d := by simpa only [one_mul] using hscaleq
  have hHscale : 16 * (q : ℝ) ^ c ≤ H := hscale'.trans hH
  have hN : (q : ℝ) ^ c ≤ ((H / h : ℕ) : ℝ) :=
    div_small_modulus_ge_scale hh hh8
      (Real.one_le_rpow (by exact_mod_cast hq1) (by linarith)) hHscale
  have hB : 0 ≤ ((H / h : ℕ) : ℝ) * (q : ℝ) ^ (-η) := by positivity
  have hθabs (n : ℕ) : |θ (n : ZMod h)| ≤ 1 := by
    rcases hθ (n : ZMod h) with hz | hz | hz <;> norm_num [hz]
  have hf (n : ℕ) : |θ (n : ZMod h) * productChar s hs (n : ℕ)| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (hθabs n) (abs_productChar_le_one s hs _)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have hprog (a : ℕ) : |∑ j ∈ Finset.range (H / h),
      θ (a + h * j : ℕ) * productChar s hs (a + h * j : ℕ)| ≤
      ((H / h : ℕ) : ℝ) * (q : ℝ) ^ (-η) :=
    abs_twisted_progression_sum_le s hs hcop' θ hθ a (H / h) hB
      (fun K => hburgessq s hs hsq K (H / h) hN)
  have hsum := abs_sum_range_le_progressions
    (fun n => θ (n : ZMod h) * productChar s hs (n : ℕ)) hf hh M H
    (fun a _ => by simpa only [Nat.add_assoc] using hprog (M + a))
  have hcount : (h : ℝ) * ((H / h : ℕ) : ℝ) ≤ H := by
    exact_mod_cast Nat.mul_div_le H h
  have hraw : |∑ i ∈ Finset.range H, θ (M + i : ℕ) * productChar s hs (M + i : ℕ)| ≤
      (H : ℝ) * (q : ℝ) ^ (-η) + 8 := by
    refine hsum.trans ?_
    have hm := mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hq0.le (-η))
    have hh8' : (h : ℝ) ≤ 8 := by exact_mod_cast hh8
    nlinarith only [hm, hh8']
  have hfirst : (H : ℝ) * (q : ℝ) ^ (-η) ≤
      (1 / 2 : ℝ) * ((H : ℝ) * (q : ℝ) ^ (-σ)) := by
    have hm := mul_le_mul_of_nonneg_left hmainq (Nat.cast_nonneg H)
    nlinarith only [hm]
  have hsecond : (8 : ℝ) ≤ (1 / 2 : ℝ) * ((H : ℝ) * (q : ℝ) ^ (-σ)) := by
    have ht : (8 : ℝ) ≤ (1 / 2 : ℝ) * ((q : ℝ) ^ d * (q : ℝ) ^ (-σ)) := by
      simpa only [Real.rpow_zero, mul_one, sub_eq_add_neg, Real.rpow_add hq0] using htailq
    exact ht.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg hq0.le _)) (by norm_num))
  nlinarith only [hraw, hfirst, hsecond]

end Pollack17.Burgess

end

/-! ## Dirichlet-character structures for the reduced product characters

Source module `ErdosProblems.Erdos1141.QuadraticProductCharacters`. -/

noncomputable section

namespace Pollack17

open scoped BigOperators

noncomputable def transportMulChar {R S T : Type*} [CommMonoid R] [CommMonoid S]
    [CommMonoidWithZero T] (χ : MulChar S T) (e : R ≃* S) : MulChar R T where
  toFun x := χ (e x)
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  map_nonunit' x hx := by
    apply χ.map_nonunit
    intro hu
    have h := hu.map e.symm
    exact hx (by simpa only [MulEquiv.symm_apply_apply] using h)

noncomputable def productMulChar {R S T : Type*} [CommMonoid R] [CommMonoid S]
    [CommMonoidWithZero T] (χ : MulChar R T) (ψ : MulChar S T) : MulChar (R × S) T where
  toFun x := χ x.1 * ψ x.2
  map_one' := by simp only [Prod.fst_one, Prod.snd_one, map_one, mul_one]
  map_mul' x y := by simp only [Prod.fst_mul, Prod.snd_mul, map_mul]; ac_rfl
  map_nonunit' x hx := by
    by_cases h₁ : IsUnit x.1
    · have h₂ : ¬IsUnit x.2 := fun h₂ => hx (Prod.isUnit_iff.mpr ⟨h₁, h₂⟩)
      rw [ψ.map_nonunit h₂, mul_zero]
    · rw [χ.map_nonunit h₁, zero_mul]

noncomputable def Burgess.productDirichletChar (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    DirichletCharacter ℝ (Burgess.primeModulus s) where
  toFun := Burgess.productChar s hs
  map_one' := by
    classical
    unfold Burgess.productChar
    apply Finset.prod_eq_one
    intro p _
    have : Fact (Nat.Prime (p : ℕ)) := ⟨hs p p.property⟩
    simp only [Burgess.localChar, Burgess.qchar, map_one, Pi.one_apply, Int.cast_one]
  map_mul' := Burgess.productChar_mul s hs
  map_nonunit' x hx := by
    classical
    have hni : ¬IsUnit (Burgess.primeCRT s hs x) := by
      intro hu
      have h := hu.map (Burgess.primeCRT s hs).symm
      exact hx (by simpa only [RingEquiv.symm_apply_apply] using h)
    have hex : ∃ p : s, ¬IsUnit (Burgess.primeCRT s hs x p) := by
      simpa only [Pi.isUnit_iff, not_forall] using hni
    obtain ⟨p, hp⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ p)
    have : Fact (Nat.Prime (p : ℕ)) := ⟨hs p p.property⟩
    simp only [Burgess.localChar, Burgess.qchar, (quadraticChar (ZMod (p : ℕ))).map_nonunit hp,
      Int.cast_zero]

theorem Burgess.productDirichletChar_apply (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (x : ZMod (Burgess.primeModulus s)) :
    Burgess.productDirichletChar s hs x = Burgess.productChar s hs x := rfl

noncomputable def tensorDirichletChar {a b : ℕ} (hab : a.Coprime b)
    (χ : DirichletCharacter ℝ a) (ψ : DirichletCharacter ℝ b) :
    DirichletCharacter ℝ (a * b) :=
  transportMulChar (productMulChar χ ψ) (ZMod.chineseRemainder hab).toMulEquiv

theorem tensorDirichletChar_natCast {a b : ℕ} (hab : a.Coprime b)
    (χ : DirichletCharacter ℝ a) (ψ : DirichletCharacter ℝ b) (n : ℕ) :
    tensorDirichletChar hab χ ψ (n : ZMod (a * b)) = χ (n : ZMod a) * ψ (n : ZMod b) := by
  simp [tensorDirichletChar, transportMulChar, productMulChar]

end Pollack17

end

/-! ## A reduced conductor dividing the original modulus

Source module `ErdosProblems.Erdos1141.QuadraticReducedCharacter`. -/

noncomputable section

namespace Pollack17

open scoped BigOperators

theorem pow_two_coprime_primeModulus {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (hodd : 2 ∉ s) (e : ℕ) : (2 ^ e).Coprime (Burgess.primeModulus s) := by
  apply Nat.Coprime.pow_left
  apply Nat.Coprime.prod_right
  intro p hp
  exact (Nat.coprime_primes Nat.prime_two (hs p hp)).mpr (by
    intro h
    exact hodd (h ▸ hp))

theorem primeModulus_dvd_of_subset {m : ℕ} {s : Finset ℕ} (hs : s ⊆ m.primeFactors) :
    Burgess.primeModulus s ∣ m :=
  (Finset.prod_dvd_prod_of_subset s m.primeFactors id hs).trans (Nat.prod_primeFactors_dvd m)

theorem exists_quadratic_reduced_character {m : ℕ} (hm : m ≠ 0)
    (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic) :
    ∃ (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime), s ⊆ m.primeFactors.erase 2 ∧
      ∃ e : ℕ, e ≤ 3 ∧ e ≤ m.factorization 2 ∧
        ∃ θ : DirichletCharacter ℝ (2 ^ e), θ.IsQuadratic ∧
          ∃ hcop : (2 ^ e).Coprime (Burgess.primeModulus s),
            ∃ hd : 2 ^ e * Burgess.primeModulus s ∣ m,
              quadraticRealChar χ hχ = DirichletCharacter.changeLevel hd
                (tensorDirichletChar hcop θ (Burgess.productDirichletChar s hs)) := by
  have : NeZero m := ⟨hm⟩
  obtain ⟨s, hsm, hs, e, he3, hem, θ, hθ, heval⟩ :=
    quadratic_character_real_decomposition hm χ hχ
  have hodd : 2 ∉ s := fun h => (Finset.mem_erase.mp (hsm h)).1 rfl
  have hcop := pow_two_coprime_primeModulus hs hodd e
  have hq : Burgess.primeModulus s ∣ m := primeModulus_dvd_of_subset
    (fun p hp => (Finset.mem_erase.mp (hsm hp)).2)
  have h2 : 2 ^ e ∣ m := Nat.prime_two.pow_dvd_iff_le_factorization hm |>.mpr hem
  have hd := hcop.mul_dvd_of_dvd_of_dvd h2 hq
  refine ⟨s, hs, hsm, e, he3, hem, θ, hθ, hcop, hd, ?_⟩
  apply MulChar.ext
  intro x
  have ha := ZMod.val_coe_unit_coprime x
  have h := changeLevel_natCast hd
    (tensorDirichletChar hcop θ (Burgess.productDirichletChar s hs)) (x : ZMod m).val ha
  rw [tensorDirichletChar_natCast, Burgess.productDirichletChar_apply,
    ← heval _ ha] at h
  simpa only [ZMod.natCast_zmod_val] using h.symm

theorem quadraticRealChar_eq_one_iff {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) : quadraticRealChar χ hχ = 1 ↔ χ = 1 := by
  constructor
  · intro h
    apply MulChar.ext
    intro x
    have hx := ofReal_quadraticRealChar χ hχ (x : R)
    rw [h, MulChar.one_apply_coe, Complex.ofReal_one] at hx
    simpa only [MulChar.one_apply_coe] using hx.symm
  · intro h
    apply MulChar.ext
    intro x
    simp only [quadraticRealChar_apply, h, MulChar.one_apply_coe, Complex.one_re]

end Pollack17

end

/-! ## Elementary interval bounds and reduced characters

Source module `ErdosProblems.Erdos1141.CharacterIntervalBounds`. -/

noncomputable section

namespace Pollack17.Burgess

open Filter

open scoped BigOperators

theorem abs_quadratic_interval_le_length {q : ℕ}
    (χ : DirichletCharacter ℝ q) (hχ : χ.IsQuadratic) (M H : ℕ) :
    |∑ i ∈ Finset.range H, χ (M + i : ℕ)| ≤ H := by
  calc
    _ ≤ ∑ i ∈ Finset.range H, |χ (M + i : ℕ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range H, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rcases hχ (M + i : ℕ) with h | h | h <;> rw [h] <;> norm_num
    _ = _ := by simp

theorem sum_zmod_eq_sum_range {q : ℕ} [NeZero q] (f : ZMod q → ℝ) :
    (∑ a : ZMod q, f a) = ∑ i ∈ Finset.range q, f (i : ZMod q) := by
  classical
  apply Finset.sum_nbij (fun a : ZMod q => a.val)
  · intro a _
    exact Finset.mem_range.mpr a.val_lt
  · exact (ZMod.val_injective q).injOn
  · intro i hi
    exact ⟨(i : ZMod q), Finset.mem_univ _, ZMod.val_cast_of_lt (Finset.mem_range.mp hi)⟩
  · intro a _
    rw [ZMod.natCast_zmod_val]

theorem sum_quadratic_period_eq_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) (M : ℕ) :
    (∑ i ∈ Finset.range q, χ (M + i : ℕ)) = 0 := by
  calc
    _ = ∑ a : ZMod q, χ ((M : ZMod q) + a) := by
      rw [sum_zmod_eq_sum_range]
      simp only [Nat.cast_add]
    _ = ∑ a : ZMod q, χ a := Equiv.sum_comp (Equiv.addLeft (M : ZMod q)) χ
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ

theorem abs_quadratic_interval_le_modulus {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ.IsQuadratic) (hχ1 : χ ≠ 1) (M H : ℕ) :
    |∑ i ∈ Finset.range H, χ (M + i : ℕ)| ≤ q := by
  have hf (n : ℕ) : |χ (n : ZMod q)| ≤ 1 := by
    rcases hχ (n : ZMod q) with h | h | h <;> norm_num [h]
  have hblock (K : ℕ) : |∑ i ∈ Finset.range q, χ (K + i : ℕ)| ≤ (0 : ℝ) := by
    rw [sum_quadratic_period_eq_zero χ hχ1 K, abs_zero]
  simpa only [zero_div, mul_zero, zero_add] using
    abs_sum_range_le_blocks (fun n => χ (n : ZMod q)) hf (NeZero.pos q)
      (le_refl (0 : ℝ)) hblock M H

theorem interval_bound_extend_to_short {q : ℕ}
    (χ : DirichletCharacter ℝ q) (hχ : χ.IsQuadratic) {T b : ℝ}
    (hT0 : 0 ≤ T) (hb : 0 ≤ b)
    (hbound : ∀ M H : ℕ, T ≤ H → |∑ i ∈ Finset.range H, χ (M + i : ℕ)| ≤ H * b)
    (M H : ℕ) : |∑ i ∈ Finset.range H, χ (M + i : ℕ)| ≤ H * b + T := by
  by_cases hT : T ≤ H
  · exact (hbound M H hT).trans (le_add_of_nonneg_right hT0)
  · have hlen := abs_quadratic_interval_le_length χ hχ M H
    have hprod : 0 ≤ (H : ℝ) * b := mul_nonneg (Nat.cast_nonneg _) hb
    linarith

end Pollack17.Burgess

end

/-! ## Divisibility classes in translated intervals

Source module `ErdosProblems.Erdos1141.DivisibleIntervals`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

def residueClassLength (H d a : ℕ) : ℕ :=
  if a < H then (H + d - 1 - a) / d else 0

lemma lt_residueClassLength_iff
    {H d a j : ℕ} (hd : 0 < d) (ha : a < H) :
    j < residueClassLength H d a ↔ a + d * j < H := by
  rw [residueClassLength, if_pos ha, Nat.lt_div_iff_mul_lt hd]
  have heq : H + d - 1 - a - (d - 1) = H - a := by omega
  rw [heq, Nat.mul_comm j d]
  omega

lemma residueClassLength_eq_zero_of_le
    {H d a : ℕ} (ha : H ≤ a) : residueClassLength H d a = 0 := by
  simp [residueClassLength, Nat.not_lt.mpr ha]

lemma filter_range_dvd_add_eq_image_residueClass
    {M H d a : ℕ} (hd : 0 < d) (ha : a < d) (hMa : d ∣ M + a) :
    (Finset.range H).filter (fun i ↦ d ∣ M + i) =
      (Finset.range (residueClassLength H d a)).image (fun j ↦ a + d * j) := by
  ext i
  constructor
  · intro hi
    have hiH := (Finset.mem_filter.mp hi).1
    have hMi := (Finset.mem_filter.mp hi).2
    have hmod : i ≡ a [MOD d] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      have hMiz : ((M + i : ℕ) : ZMod d) = 0 :=
        (ZMod.natCast_eq_zero_iff (M + i) d).mpr hMi
      have hMaz : ((M + a : ℕ) : ZMod d) = 0 :=
        (ZMod.natCast_eq_zero_iff (M + a) d).mpr hMa
      calc
        (i : ZMod d) = ((M + i : ℕ) : ZMod d) - (M : ZMod d) := by
          push_cast
          ring
        _ = -(M : ZMod d) := by rw [hMiz]; ring
        _ = ((M + a : ℕ) : ZMod d) - (M : ZMod d) := by rw [hMaz]; ring
        _ = (a : ZMod d) := by push_cast; ring
    have himod : i % d = a := Nat.mod_eq_of_modEq hmod ha
    let j := i / d
    have hij : i = a + d * j := by
      dsimp [j]
      calc
        i = d * (i / d) + i % d := (Nat.div_add_mod i d).symm
        _ = d * (i / d) + a := by rw [himod]
        _ = a + d * (i / d) := by omega
    have hai : a ≤ i := by rw [hij]; exact Nat.le_add_right _ _
    have haH : a < H := hai.trans_lt (Finset.mem_range.mp hiH)
    have hj : j < residueClassLength H d a :=
      (lt_residueClassLength_iff hd haH).mpr (by
        rw [← hij]
        exact Finset.mem_range.mp hiH)
    rw [Finset.mem_image]
    exact ⟨j, Finset.mem_range.mpr hj, hij.symm⟩
  · intro hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    have haH : a < H := by
      by_contra h
      have hz := residueClassLength_eq_zero_of_le
        (d := d) (Nat.le_of_not_gt h)
      rw [Finset.mem_range, hz] at hj
      omega
    have hlt : a + d * j < H :=
      (lt_residueClassLength_iff hd haH).mp (Finset.mem_range.mp hj)
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr hlt
    · obtain ⟨c, hc⟩ := hMa
      refine ⟨c + j, ?_⟩
      calc
        M + (a + d * j) = (M + a) + d * j := by omega
        _ = d * c + d * j := by rw [hc]
        _ = d * (c + j) := by ring

lemma sum_ite_dvd_eq_residueClass
    (f : ℕ → ℝ) {M H d a : ℕ}
    (hd : 0 < d) (ha : a < d) (hMa : d ∣ M + a) :
    (∑ i ∈ Finset.range H, if d ∣ M + i then f (M + i) else 0) =
      ∑ j ∈ Finset.range (residueClassLength H d a),
        f (M + (a + d * j)) := by
  rw [← Finset.sum_filter]
  rw [filter_range_dvd_add_eq_image_residueClass hd ha hMa]
  rw [Finset.sum_image]
  intro x hx y hy hxy
  exact mul_left_cancel₀ hd.ne' (Nat.add_left_cancel hxy)

lemma residueClassLength_le
    {M H d a : ℕ} (hd : 0 < d) (ha : a < d) (hMa : d ∣ M + a) :
    residueClassLength H d a ≤ H := by
  have heq := filter_range_dvd_add_eq_image_residueClass
    (M := M) (H := H) hd ha hMa
  have hinj : Function.Injective (fun j : ℕ ↦ a + d * j) := by
    intro x y hxy
    exact mul_left_cancel₀ hd.ne' (Nat.add_left_cancel hxy)
  have hcard :
      residueClassLength H d a =
        ((Finset.range H).filter (fun i ↦ d ∣ M + i)).card := by
    rw [heq, Finset.card_image_of_injective _ hinj]
    simp
  rw [hcard]
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

lemma exists_divisible_sum_factorization
    (f : ℕ → ℝ) (hmul : ∀ a b, f (a * b) = f a * f b)
    (M H d : ℕ) (hd : 0 < d) :
    ∃ K L : ℕ, L ≤ H ∧
      (∑ i ∈ Finset.range H,
        if d ∣ M + i then f (M + i) else 0) =
        f d * ∑ j ∈ Finset.range L, f (K + j) := by
  have : NeZero d := ⟨hd.ne'⟩
  let a : ℕ := (-(M : ZMod d)).val
  let K : ℕ := (M + a) / d
  let L : ℕ := residueClassLength H d a
  have ha : a < d := ZMod.val_lt _
  have hMa : d ∣ M + a := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    change (M : ZMod d) + (a : ZMod d) = 0
    rw [show (a : ZMod d) = -(M : ZMod d) by
      exact ZMod.natCast_zmod_val _]
    ring
  have hK : d * K = M + a := Nat.mul_div_cancel' hMa
  refine ⟨K, L, residueClassLength_le hd ha hMa, ?_⟩
  rw [sum_ite_dvd_eq_residueClass f hd ha hMa]
  calc
    (∑ j ∈ Finset.range L, f (M + (a + d * j))) =
        ∑ j ∈ Finset.range L, f (d * (K + j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          congr 2
          calc
            M + (a + d * j) = (M + a) + d * j := by omega
            _ = d * K + d * j := by rw [hK]
            _ = d * (K + j) := by ring
    _ = ∑ j ∈ Finset.range L, f d * f (K + j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hmul d (K + j)
    _ = f d * ∑ j ∈ Finset.range L, f (K + j) := by
      rw [Finset.mul_sum]

end Pollack17.Burgess

end

/-! ## Inclusion-exclusion for an induced character

Source module `ErdosProblems.Erdos1141.CharacterUnitSieve`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

theorem prod_divisibility_indicator (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (n : ℕ) :
    (∏ p ∈ s, (if p ∣ n then (1 : ℝ) else 0)) =
      if (∏ p ∈ s, p) ∣ n then 1 else 0 := by
  classical
  by_cases h : (∏ p ∈ s, p) ∣ n
  · rw [if_pos h]
    exact Finset.prod_eq_one fun p hp => if_pos ((prod_dvd_iff_all_prime_dvd s hs n).mp h p hp)
  · rw [if_neg h]
    have hn : ¬ ∀ p ∈ s, p ∣ n := by rwa [← prod_dvd_iff_all_prime_dvd s hs n]
    push Not at hn
    obtain ⟨p, hp, hpn⟩ := hn
    exact Finset.prod_eq_zero hp (if_neg hpn)

theorem coprime_indicator_eq_alternating {m : ℕ} (hm : m ≠ 0) (n : ℕ) :
    (if n.Coprime m then (1 : ℝ) else 0) =
      ∑ t ∈ m.primeFactors.powerset, (-1 : ℝ) ^ t.card *
        (if (∏ p ∈ t, p) ∣ n then 1 else 0) := by
  classical
  have hprod : (if n.Coprime m then (1 : ℝ) else 0) =
      ∏ p ∈ m.primeFactors, (1 - (if p ∣ n then (1 : ℝ) else 0)) := by
    by_cases hc : n.Coprime m
    · rw [if_pos hc]
      symm
      apply Finset.prod_eq_one
      intro p hp
      have hpc := hc.of_dvd_right (Nat.dvd_of_mem_primeFactors hp)
      have hpn := (Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd.mp hpc.symm
      simp [hpn]
    · rw [if_neg hc]
      obtain ⟨p, hp, hpn, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
      symm
      exact Finset.prod_eq_zero (Nat.mem_primeFactors.mpr ⟨hp, hpm, hm⟩) (by simp [hpn])
  rw [hprod, Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_const_one, mul_one, prod_divisibility_indicator t
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp))]

theorem changeLevel_natCast_eq_ite {d m : ℕ} (hd : d ∣ m)
    (φ : DirichletCharacter ℝ d) (n : ℕ) :
    DirichletCharacter.changeLevel hd φ (n : ZMod m) =
      if n.Coprime m then φ (n : ZMod d) else 0 := by
  by_cases hc : n.Coprime m
  · rw [if_pos hc]
    exact Pollack17.changeLevel_natCast hd φ n hc
  · rw [if_neg hc]
    exact MulChar.map_nonunit _ (by simpa only [ZMod.isUnit_iff_coprime] using hc)

theorem changeLevel_sum_eq_alternating {d m : ℕ} (hm : m ≠ 0) (hd : d ∣ m)
    (φ : DirichletCharacter ℝ d) (M H : ℕ) :
    (∑ i ∈ Finset.range H, DirichletCharacter.changeLevel hd φ (M + i : ℕ)) =
      ∑ t ∈ m.primeFactors.powerset, (-1 : ℝ) ^ t.card *
        ∑ i ∈ Finset.range H, if (∏ p ∈ t, p) ∣ M + i then φ (M + i : ℕ) else 0 := by
  classical
  have hpoint (n : ℕ) : DirichletCharacter.changeLevel hd φ (n : ℕ) =
      ∑ t ∈ m.primeFactors.powerset, (-1 : ℝ) ^ t.card *
        (if (∏ p ∈ t, p) ∣ n then φ (n : ℕ) else 0) := by
    rw [changeLevel_natCast_eq_ite]
    calc
      _ = φ (n : ℕ) * (if n.Coprime m then (1 : ℝ) else 0) := by split_ifs <;> simp
      _ = _ := by
        rw [coprime_indicator_eq_alternating hm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        split_ifs <;> ring
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem abs_changeLevel_sum_le {d m : ℕ} (hm : m ≠ 0) (hd : d ∣ m)
    (φ : DirichletCharacter ℝ d) (hφ : φ.IsQuadratic) (M H : ℕ) {B : ℝ}
    (hbound : ∀ K L : ℕ, L ≤ H → |∑ j ∈ Finset.range L, φ (K + j : ℕ)| ≤ B) :
    |∑ i ∈ Finset.range H, DirichletCharacter.changeLevel hd φ (M + i : ℕ)| ≤
      (2 : ℝ) ^ m.primeFactors.card * B := by
  classical
  rw [changeLevel_sum_eq_alternating hm hd φ M H]
  calc
    _ ≤ ∑ t ∈ m.primeFactors.powerset,
        |(-1 : ℝ) ^ t.card * ∑ i ∈ Finset.range H,
          if (∏ p ∈ t, p) ∣ M + i then φ (M + i : ℕ) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ m.primeFactors.powerset, B := by
      apply Finset.sum_le_sum
      intro t ht
      rw [abs_mul, abs_neg_one_pow, one_mul]
      have htpos : 0 < ∏ p ∈ t, p := Finset.prod_pos fun p hp =>
        (Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp)).pos
      obtain ⟨K, L, hLH, heq⟩ := exists_divisible_sum_factorization
        (fun n => φ (n : ℕ)) (fun a b => by simp only [Nat.cast_mul, map_mul]) M H _ htpos
      rw [heq, abs_mul]
      have habs : |φ ((∏ p ∈ t, p) : ℕ)| ≤ 1 := by
        rcases hφ ((∏ p ∈ t, p) : ℕ) with h | h | h <;> rw [h] <;> norm_num
      exact (mul_le_mul habs (hbound K L hLH) (abs_nonneg _) (by norm_num)).trans_eq (one_mul B)
    _ = _ := by simp

end Pollack17.Burgess

end

/-! ## Burgess cancellation for every quadratic character

Source module `ErdosProblems.Erdos1141.GeneralBurgess`. -/

noncomputable section

namespace Pollack17.Burgess

open Filter

open scoped BigOperators

theorem real_quadratic_of_changeLevel {m d : ℕ} [NeZero m] (hd : d ∣ m)
    (φ : DirichletCharacter ℝ d) (hφ : (DirichletCharacter.changeLevel hd φ).IsQuadratic) :
    φ.IsQuadratic := by
  apply MulChar.isQuadratic_iff_sq_eq_one.mpr
  apply DirichletCharacter.changeLevel_injective hd
  rw [map_pow, map_one, hφ.sq_eq_one]

theorem eventually_quadratic_burgess {d : ℝ} (hd : 1 / 4 < d) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ (χ : DirichletCharacter ℂ m) (_ : χ.IsQuadratic), χ ≠ 1 →
        ∀ M H : ℕ, (m : ℝ) ^ d ≤ H →
          |∑ i ∈ Finset.range H, (χ (M + i : ℕ)).re| ≤
            (H : ℝ) * (m : ℝ) ^ (-σ) := by
  let c : ℝ := (d + 1 / 4) / 2
  have hc : 1 / 4 < c := by dsimp [c]; linarith
  have hcd : c < d := by dsimp [c]; linarith
  have hc0 : 0 < c := by linarith
  let κ : ℝ := (d - c) / 4
  have hκ : 0 < κ := by dsimp [κ]; linarith
  have hκd : κ < d := by dsimp [κ]; linarith
  obtain ⟨η, hη, hburgess⟩ := eventually_twisted_squarefree_burgess hc
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp hburgess
  let σ : ℝ := min (κ * η) (min (d - c) (d - κ)) / 8
  have hσ : 0 < σ := by
    dsimp [σ]
    exact div_pos
      (lt_min (mul_pos hκ hη) (lt_min (sub_pos.mpr hcd) (sub_pos.mpr hκd)))
      (by norm_num)
  have hση : 2 * σ < κ * η := by
    have h := min_le_left (κ * η) (min (d - c) (d - κ))
    dsimp only [σ] at hσ ⊢
    linarith
  have hσc : c < d - 2 * σ := by
    have h := (min_le_right (κ * η) (min (d - c) (d - κ))).trans (min_le_left _ _)
    dsimp only [σ] at hσ ⊢
    linarith
  have hσκ : κ < d - 2 * σ := by
    have h := (min_le_right (κ * η) (min (d - c) (d - κ))).trans (min_le_right _ _)
    dsimp only [σ] at hσ ⊢
    linarith
  have hlarge := ((tendsto_rpow_atTop hκ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (Q : ℝ))
  have hmain := eventually_const_mul_rpow_le (C := 1) (d := 1 / 2)
    (a := -(κ * η)) (b := -(2 * σ)) (by norm_num) (by linarith)
  have htail := eventually_const_mul_rpow_le (C := 1) (d := 1 / 2) (by norm_num) hσc
  have hsmall := eventually_const_mul_rpow_le (C := 8) (d := 1) (by norm_num) hσκ
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hlarge, hmain, htail, hsmall,
    eventually_const_pow_primeFactors_le 2 (by norm_num) hσ, eventually_ge_atTop 1]
    with m hlarge hmain htail hsmall hω hm1
  intro χ hχ hχ1 M H hH
  have hm0 : 0 < m := hm1
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  have : NeZero m := ⟨hm0.ne'⟩
  obtain ⟨s, hs, hsm, e, he3, _hem, θ, hθ, hcop, hD, heq⟩ :=
    exists_quadratic_reduced_character hm0.ne' χ hχ
  let q := primeModulus s
  let φ := tensorDirichletChar hcop θ (productDirichletChar s hs)
  change quadraticRealChar χ hχ = DirichletCharacter.changeLevel hD φ at heq
  have hq0 : 0 < q := primeModulus_pos s hs
  have : NeZero q := ⟨hq0.ne'⟩
  have : NeZero (2 ^ e * q) := ⟨(mul_pos (by positivity) hq0).ne'⟩
  have hφ : φ.IsQuadratic := real_quadratic_of_changeLevel hD φ (by
    rw [← heq]
    exact quadraticRealChar_isQuadratic χ hχ)
  have hφ1 : φ ≠ 1 := by
    intro h
    apply hχ1
    apply (quadraticRealChar_eq_one_iff χ hχ).mp
    rw [heq, h, map_one]
  have hqle : q ≤ m := Nat.le_of_dvd hm0 (primeModulus_dvd_of_subset
    (fun p hp => (Finset.mem_erase.mp (hsm hp)).2))
  have h2 : 2 ^ e ≤ 8 := by
    calc
      2 ^ e ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) he3
      _ = 8 := by norm_num
  have hφbound : ∀ K L : ℕ, L ≤ H →
      |∑ j ∈ Finset.range L, φ (K + j : ℕ)| ≤ (H : ℝ) * (m : ℝ) ^ (-(2 * σ)) := by
    intro K L hLH
    by_cases hqbig : (m : ℝ) ^ κ ≤ q
    · have hQq : Q ≤ q := by
        have hQr : (Q : ℝ) ≤ q := hlarge.trans hqbig
        exact_mod_cast hQr
      have hb (K L : ℕ) (hL : (q : ℝ) ^ c ≤ L) :
          |∑ j ∈ Finset.range L, φ (K + j : ℕ)| ≤ L * (q : ℝ) ^ (-η) := by
        have h := hQ q hQq s hs rfl (2 ^ e) (by positivity) h2 hcop θ hθ K L hL
        simpa only [φ, tensorDirichletChar_natCast, productDirichletChar_apply] using h
      have hraw := interval_bound_extend_to_short φ hφ
        (Real.rpow_nonneg (by positivity) c) (Real.rpow_nonneg (by positivity) (-η)) hb K L
      have hneg : (q : ℝ) ^ (-η) ≤ (m : ℝ) ^ (-(κ * η)) := by
        calc
          _ ≤ ((m : ℝ) ^ κ) ^ (-η) := Real.rpow_le_rpow_of_nonpos
            (Real.rpow_pos_of_pos hmR _) hqbig (by linarith)
          _ = _ := by rw [← Real.rpow_mul hmR.le]; congr 1; ring
      have hpos : (q : ℝ) ^ c ≤ (m : ℝ) ^ c :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hqle) hc0.le
      have hfirst : (L : ℝ) * (q : ℝ) ^ (-η) ≤
          (1 / 2 : ℝ) * ((H : ℝ) * (m : ℝ) ^ (-(2 * σ))) := by
        have hLM : (L : ℝ) ≤ H := by exact_mod_cast hLH
        have hneg' : (q : ℝ) ^ (-η) ≤ (1 / 2 : ℝ) * (m : ℝ) ^ (-(2 * σ)) :=
          hneg.trans (by simpa only [one_mul] using hmain)
        calc
          _ ≤ (H : ℝ) * ((1 / 2 : ℝ) * (m : ℝ) ^ (-(2 * σ))) :=
            mul_le_mul hLM hneg' (Real.rpow_nonneg (by positivity) _) (Nat.cast_nonneg _)
          _ = _ := by ring
      have hsecond : (q : ℝ) ^ c ≤
          (1 / 2 : ℝ) * ((H : ℝ) * (m : ℝ) ^ (-(2 * σ))) := by
        have ht : (m : ℝ) ^ c ≤
            (1 / 2 : ℝ) * ((m : ℝ) ^ d * (m : ℝ) ^ (-(2 * σ))) := by
          simpa only [one_mul, sub_eq_add_neg, Real.rpow_add hmR] using htail
        exact (hpos.trans ht).trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg hmR.le _)) (by norm_num))
      linarith only [hraw, hfirst, hsecond]
    · have hperiod := abs_quadratic_interval_le_modulus φ hφ hφ1 K L
      have hqsmall : (q : ℝ) ≤ (m : ℝ) ^ κ := (lt_of_not_ge hqbig).le
      have h2R : ((2 ^ e : ℕ) : ℝ) ≤ 8 := by exact_mod_cast h2
      have hperiod' : |∑ j ∈ Finset.range L, φ (K + j : ℕ)| ≤ 8 * (m : ℝ) ^ κ := by
        refine hperiod.trans ?_
        rw [Nat.cast_mul]
        exact mul_le_mul h2R hqsmall (Nat.cast_nonneg _) (by norm_num)
      have hsm' : 8 * (m : ℝ) ^ κ ≤ (m : ℝ) ^ d * (m : ℝ) ^ (-(2 * σ)) := by
        simpa only [one_mul, sub_eq_add_neg, Real.rpow_add hmR] using hsmall
      exact (hperiod'.trans hsm').trans
        (mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg hmR.le _))
  have hsieve := abs_changeLevel_sum_le hm0.ne' hD φ hφ M H hφbound
  have hlast : (2 : ℝ) ^ m.primeFactors.card * ((H : ℝ) * (m : ℝ) ^ (-(2 * σ))) ≤
      (H : ℝ) * (m : ℝ) ^ (-σ) := by
    calc
      _ ≤ (m : ℝ) ^ σ * ((H : ℝ) * (m : ℝ) ^ (-(2 * σ))) :=
        mul_le_mul_of_nonneg_right hω (by positivity)
      _ = _ := by
        rw [mul_left_comm, ← Real.rpow_add hmR]
        congr 2
        ring
  have hsum : (∑ i ∈ Finset.range H, (χ (M + i : ℕ)).re) =
      ∑ i ∈ Finset.range H, DirichletCharacter.changeLevel hD φ (M + i : ℕ) := by
    simp only [← heq, quadraticRealChar_apply]
  rw [hsum]
  exact hsieve.trans hlast

end Pollack17.Burgess

end

/-! ## Discrete partial summation for reciprocal character sums

Source module `ErdosProblems.Erdos1141.ReciprocalIntervals`. -/

noncomputable section

namespace Pollack17

open scoped BigOperators

theorem abs_reciprocal_interval_le (f : ℕ → ℝ) {x y : ℕ} (hx : 0 < x) (hxy : x ≤ y)
    {b : ℝ} (hb : 0 ≤ b)
    (hprefix : ∀ n : ℕ, x ≤ n → n ≤ y →
      |∑ i ∈ Finset.range (n + 1), f i| ≤ (n : ℝ) * b) :
    |∑ i ∈ Finset.Ioc x y, f i / (i : ℝ)| ≤ b * (3 + Real.log (y : ℝ)) := by
  by_cases heq : x = y
  · subst y
    have hy1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
    simp only [Finset.Ioc_self, Finset.sum_empty, abs_zero]
    exact mul_nonneg hb (by linarith [Real.log_nonneg hy1])
  have hlt : x < y := lt_of_le_of_ne hxy heq
  have hxR : 0 < (x : ℝ) := by exact_mod_cast hx
  have hyR : 0 < (y : ℝ) := by exact_mod_cast (hx.trans_le hxy)
  let S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), f i
  have hid : (∑ i ∈ Finset.Ioc x y, f i / (i : ℝ)) =
      (y : ℝ)⁻¹ * S y - ((x + 1 : ℕ) : ℝ)⁻¹ * S x -
        ∑ i ∈ Finset.Ioc x (y - 1),
          (((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) * S i := by
    simpa only [S, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      Finset.sum_Ioc_by_parts (fun i : ℕ => (i : ℝ)⁻¹) f hlt
  have hend : |(y : ℝ)⁻¹ * S y| ≤ b := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hyR)]
    calc
      _ ≤ (y : ℝ)⁻¹ * ((y : ℝ) * b) := mul_le_mul_of_nonneg_left
        (hprefix y hxy le_rfl) (inv_nonneg.mpr hyR.le)
      _ = _ := by field_simp
  have hstart : |((x + 1 : ℕ) : ℝ)⁻¹ * S x| ≤ b := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < ((x + 1 : ℕ) : ℝ)⁻¹)]
    calc
      _ ≤ ((x + 1 : ℕ) : ℝ)⁻¹ * ((x : ℝ) * b) :=
        mul_le_mul_of_nonneg_left (hprefix x le_rfl hxy) (by positivity)
      _ ≤ ((x + 1 : ℕ) : ℝ)⁻¹ * (((x + 1 : ℕ) : ℝ) * b) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (by push_cast; linarith) hb) (by positivity)
      _ = b := by field_simp
  have hterm (i : ℕ) (hi : i ∈ Finset.Ioc x (y - 1)) :
      |(((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) * S i| ≤ b * (i : ℝ)⁻¹ := by
    have hix := (Finset.mem_Ioc.mp hi).1
    have hiy := (Finset.mem_Ioc.mp hi).2
    have hiR : 0 < (i : ℝ) := by exact_mod_cast (hx.trans hix)
    have hi1R : 0 < ((i + 1 : ℕ) : ℝ) := by positivity
    have hinv : ((i + 1 : ℕ) : ℝ)⁻¹ ≤ (i : ℝ)⁻¹ :=
      inv_anti₀ hiR (by push_cast; linarith)
    have hdiff : 0 ≤ (i : ℝ)⁻¹ - ((i + 1 : ℕ) : ℝ)⁻¹ := sub_nonneg.mpr hinv
    rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hinv)]
    calc
      _ = ((i : ℝ)⁻¹ - ((i + 1 : ℕ) : ℝ)⁻¹) * |S i| := by ring
      _ ≤ ((i : ℝ)⁻¹ - ((i + 1 : ℕ) : ℝ)⁻¹) * ((i : ℝ) * b) :=
        mul_le_mul_of_nonneg_left (hprefix i hix.le (by omega)) hdiff
      _ = b * ((i + 1 : ℕ) : ℝ)⁻¹ := by
        push_cast
        field_simp
        ring
      _ ≤ b * (i : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hinv hb
  have hsum : |∑ i ∈ Finset.Ioc x (y - 1),
      (((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) * S i| ≤ b * (1 + Real.log (y : ℝ)) := by
    calc
      _ ≤ ∑ i ∈ Finset.Ioc x (y - 1),
          |(((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) * S i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Ioc x (y - 1), b * (i : ℝ)⁻¹ := Finset.sum_le_sum hterm
      _ = b * ∑ i ∈ Finset.Ioc x (y - 1), (i : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ b * ∑ i ∈ Finset.Icc 1 y, (i : ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ hb
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          have hi := Finset.mem_Ioc.mp hi
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        · intro i _ _
          positivity
      _ ≤ _ := mul_le_mul_of_nonneg_left (Burgess.sum_Icc_inv_natCast_le_one_add_log y) hb
  rw [hid]
  calc
    _ ≤ |(y : ℝ)⁻¹ * S y| + |((x + 1 : ℕ) : ℝ)⁻¹ * S x| +
        |∑ i ∈ Finset.Ioc x (y - 1), (((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) * S i| :=
      (by
        have h₁ := norm_sub_le ((y : ℝ)⁻¹ * S y - ((x + 1 : ℕ) : ℝ)⁻¹ * S x)
          (∑ i ∈ Finset.Ioc x (y - 1), (((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) * S i)
        have h₂ := norm_sub_le ((y : ℝ)⁻¹ * S y) (((x + 1 : ℕ) : ℝ)⁻¹ * S x)
        simp only [Real.norm_eq_abs] at h₁ h₂
        linarith only [h₁, h₂])
    _ ≤ b + b + b * (1 + Real.log (y : ℝ)) := add_le_add (add_le_add hend hstart) hsum
    _ = _ := by ring

end Pollack17

end

/-! ## Primitive Gauss sums on `ZMod`

Source module `BoundedGaps.BombieriVinogradov.Analytic.PrimitiveGaussSum`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

open AddChar Finset

private theorem PrimitiveGaussSum_sum_star_mul_dft {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ k : ZMod q, star (ZMod.dft f k) * ZMod.dft f k) =
      (q : ℂ) * ∑ j : ZMod q, star (f j) * f j := by
  classical
  have hstar (x : ZMod q) :
      star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
    simpa only [Complex.star_def] using
      (AddChar.map_neg_eq_conj ZMod.stdAddChar x).symm
  simp only [ZMod.dft_apply, smul_eq_mul, star_sum, star_mul]
  simp_rw [hstar]
  simp only [neg_neg]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  have hsummand (i k : ZMod q) :
      star (f j) * ZMod.stdAddChar (j * k) *
          (ZMod.stdAddChar (-(i * k)) * f i) =
        (star (f j) * f i) * ZMod.stdAddChar (k * (j - i)) := by
    calc
      _ = (star (f j) * f i) *
          (ZMod.stdAddChar (j * k) * ZMod.stdAddChar (-(i * k))) := by ring
      _ = (star (f j) * f i) *
          ZMod.stdAddChar (j * k + -(i * k)) := by rw [map_add_eq_mul]
      _ = _ := by
        rw [show j * k + -(i * k) = k * (j - i) by ring]
  simp_rw [hsummand, ← Finset.mul_sum]
  simp_rw [AddChar.sum_mulShift (ψ := ZMod.stdAddChar) _
    (ZMod.isPrimitive_stdAddChar q)]
  simp only [sub_eq_zero, ZMod.card, Nat.cast_ite, Nat.cast_zero,
    mul_ite, mul_zero]
  simp [eq_comm]
  ring

theorem sum_norm_sq_dft {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ k : ZMod q, ‖ZMod.dft f k‖ ^ 2) =
      (q : ℝ) * ∑ j : ZMod q, ‖f j‖ ^ 2 := by
  have h := PrimitiveGaussSum_sum_star_mul_dft f
  rw [Complex.star_def] at h
  simp_rw [← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

theorem sum_norm_sq_dirichletCharacter {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (∑ j : ZMod q, ‖χ j‖ ^ 2) = (Nat.totient q : ℝ) := by
  classical
  calc
    (∑ j : ZMod q, ‖χ j‖ ^ 2) =
        ∑ j : ZMod q, if IsUnit j then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : IsUnit j
      · have hnorm : ‖χ j‖ = 1 := by
          rw [← hj.unit_spec]
          exact χ.unit_norm_eq_one hj.unit
        simp [hj, hnorm]
      · simp [hj, χ.map_nonunit hj]
    _ = (((Finset.univ : Finset (ZMod q)).filter IsUnit).card : ℝ) := by
      simp
    _ = ((Fintype.card (ZMod q)ˣ : ℕ) : ℝ) := by
      congr 1
      calc
        ((Finset.univ : Finset (ZMod q)).filter IsUnit).card =
            (Finset.univ.map ⟨((↑) : (ZMod q)ˣ → ZMod q),
              Units.val_injective⟩).card := by
          congr 1
          ext j
          simp [IsUnit]
        _ = Fintype.card (ZMod q)ˣ := by simp
    _ = (Nat.totient q : ℝ) := by rw [ZMod.card_units_eq_totient]

theorem norm_gaussSum_stdAddChar_of_isPrimitive {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt q := by
  have hmassNeg :
      (∑ k : ZMod q, ‖χ⁻¹ (-k)‖ ^ 2) = (Nat.totient q : ℝ) := by
    calc
      _ = ∑ k : ZMod q, ‖χ⁻¹ k‖ ^ 2 :=
        Equiv.sum_comp (Equiv.neg (ZMod q)) (fun k ↦ ‖χ⁻¹ k‖ ^ 2)
      _ = (Nat.totient q : ℝ) := sum_norm_sq_dirichletCharacter χ⁻¹
  have hparseval := sum_norm_sq_dft (f := fun j ↦ χ j)
  simp_rw [hχ.fourierTransform_eq_inv_mul_gaussSum, norm_mul, mul_pow] at hparseval
  rw [← Finset.sum_mul, hmassNeg,
    sum_norm_sq_dirichletCharacter χ] at hparseval
  have htotient : (Nat.totient q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr
      (Nat.pos_of_ne_zero (NeZero.ne q))))
  have hsquare : ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (q : ℝ) := by
    apply mul_left_cancel₀ htotient
    calc
      (Nat.totient q : ℝ) * ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 =
          (q : ℝ) * Nat.totient q := hparseval
      _ = (Nat.totient q : ℝ) * q := by ring
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg q),
    norm_nonneg (gaussSum χ ZMod.stdAddChar), Real.sqrt_nonneg (q : ℝ)]

theorem primitive_fourier_expansion {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (n : ZMod q) :
    (∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (a * n)) =
      χ n * gaussSum χ⁻¹ ZMod.stdAddChar := by
  have hχinv : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
    exact hχ
  have hfourier := hχinv.fourierTransform_eq_inv_mul_gaussSum (-n)
  simpa only [ZMod.dft_apply, smul_eq_mul, mul_neg, neg_neg, inv_inv,
    mul_comm] using hfourier

theorem primitive_fourier_expansion_div {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (n : ZMod q) :
    χ n = (∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (a * n)) /
      gaussSum χ⁻¹ ZMod.stdAddChar := by
  have hχinv : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
    exact hχ
  have hnorm := norm_gaussSum_stdAddChar_of_isPrimitive χ⁻¹ hχinv
  have hgauss : gaussSum χ⁻¹ ZMod.stdAddChar ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hnorm
    have hqpos : (0 : ℝ) < q := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    nlinarith [Real.sqrt_pos.2 hqpos]
  rw [primitive_fourier_expansion χ hχ n,
    mul_div_cancel_right₀ _ hgauss]

end BoundedGaps.Maynard

end

/-! ## Abel continuation for nonprincipal Dirichlet L-functions

Source module `BoundedGaps.BombieriVinogradov.Analytic.DirichletLFunctionAbelContinuation`. -/

noncomputable section

open Asymptotics Complex Filter MeasureTheory Set

open scoped BigOperators Real Topology

namespace BoundedGaps.Maynard

private noncomputable def DirichletLFunctionAbelContinuation_characterPrefixTail
    {q : ℕ} (chi : DirichletCharacter ℂ q) (y : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator
    (fun u ↦ ∑ k ∈ Finset.Icc 1 ⌊u⌋₊, chi (k : ZMod q)) y

private lemma DirichletLFunctionAbelContinuation_measurable_characterPrefixTail
    {q : ℕ} (chi : DirichletCharacter ℂ q) :
    Measurable (DirichletLFunctionAbelContinuation_characterPrefixTail chi) := by
  apply Measurable.indicator _ measurableSet_Ioi
  exact
    (measurable_of_countable
      (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q))).comp
      Nat.measurable_floor

private lemma DirichletLFunctionAbelContinuation_norm_characterPrefixTail_le
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    (y : ℝ) :
    ‖DirichletLFunctionAbelContinuation_characterPrefixTail chi y‖ ≤ C := by
  by_cases hy : y ∈ Ioi (1 : ℝ)
  · rw [DirichletLFunctionAbelContinuation_characterPrefixTail, indicator_of_mem hy]
    exact hprefix ⌊y⌋₊
  · rw [DirichletLFunctionAbelContinuation_characterPrefixTail, indicator_of_notMem hy, norm_zero]
    exact hC

private lemma DirichletLFunctionAbelContinuation_locallyIntegrable_characterPrefixTail
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C) :
    LocallyIntegrableOn (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (Ioi 0) := by
  have hnormScale : ‖((C : ℝ) : ℂ)‖ = C := by
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
  refine ((locallyIntegrable_const ((C : ℝ) : ℂ)).locallyIntegrableOn
      (Ioi 0)).mono
      (DirichletLFunctionAbelContinuation_measurable_characterPrefixTail chi).aestronglyMeasurable ?_
  filter_upwards with y
  rw [hnormScale]
  exact DirichletLFunctionAbelContinuation_norm_characterPrefixTail_le chi C hC hprefix y

private lemma DirichletLFunctionAbelContinuation_characterPrefixTail_isBigO_atTop
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C) :
    DirichletLFunctionAbelContinuation_characterPrefixTail chi =O[atTop] (fun y : ℝ ↦ y ^ (-(0 : ℝ))) := by
  refine isBigO_iff.mpr ⟨C, Eventually.of_forall fun y ↦ ?_⟩
  simpa using DirichletLFunctionAbelContinuation_norm_characterPrefixTail_le chi C hC hprefix y

private lemma DirichletLFunctionAbelContinuation_characterPrefixTail_isBigO_nhdsGT_zero
    {q : ℕ} (chi : DirichletCharacter ℂ q) (b : ℝ) :
    DirichletLFunctionAbelContinuation_characterPrefixTail chi =O[𝓝[>] 0] (fun y : ℝ ↦ y ^ (-b)) := by
  have hlt : ∀ᶠ y : ℝ in 𝓝[>] 0, y < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [hlt] with y hy
  simp [DirichletLFunctionAbelContinuation_characterPrefixTail, not_lt.mpr hy.le]

private lemma DirichletLFunctionAbelContinuation_differentiableAt_characterPrefixMellin_neg
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun w ↦ mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-w)) s := by
  have hm : DifferentiableAt ℂ (mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi)) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow
      (a := 0) (b := (-s).re - 1)
      (DirichletLFunctionAbelContinuation_locallyIntegrable_characterPrefixTail chi C hC hprefix)
      (DirichletLFunctionAbelContinuation_characterPrefixTail_isBigO_atTop chi C hC hprefix) ?_
      (DirichletLFunctionAbelContinuation_characterPrefixTail_isBigO_nhdsGT_zero chi ((-s).re - 1)) ?_
    · simpa using (neg_lt_zero.mpr hs)
    · linarith
  exact hm.comp s differentiableAt_id.neg

private lemma DirichletLFunctionAbelContinuation_characterPrefixMellin_neg_eq_integral
    {q : ℕ} (chi : DirichletCharacter ℂ q) (s : ℂ) :
    mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-s) =
      ∫ y in Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) := by
  rw [mellin]
  simp only [smul_eq_mul]
  calc
    (∫ y : ℝ in Ioi 0,
        (y : ℂ) ^ (-s - 1) * DirichletLFunctionAbelContinuation_characterPrefixTail chi y) =
        ∫ y : ℝ in Ioi 0, (Ioi (1 : ℝ)).indicator
          (fun u ↦ (u : ℂ) ^ (-s - 1) *
            ∑ k ∈ Finset.Icc 1 ⌊u⌋₊, chi (k : ZMod q)) y := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
      by_cases hy : y ∈ Ioi (1 : ℝ)
      · simp [DirichletLFunctionAbelContinuation_characterPrefixTail, hy]
      · simp [DirichletLFunctionAbelContinuation_characterPrefixTail, hy]
    _ = ∫ y : ℝ in Ioi 0 ∩ Ioi 1,
        (y : ℂ) ^ (-s - 1) *
          (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) := by
      rw [setIntegral_indicator measurableSet_Ioi]
    _ = ∫ y : ℝ in Ioi 1,
        (y : ℂ) ^ (-s - 1) *
          (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) := by
      rw [Ioi_inter_Ioi, max_eq_right zero_le_one]
    _ = ∫ y : ℝ in Ioi 1,
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
      rw [show -s - 1 = -(s + 1) by ring, mul_comm]

private lemma DirichletLFunctionAbelContinuation_characterPartialSums_isBigO_atTop
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (0 : ℝ)) := by
  refine isBigO_iff.mpr ⟨C, Eventually.of_forall fun n ↦ ?_⟩
  simpa using hprefix n

private lemma DirichletLFunctionAbelContinuation_LFunction_eq_characterPrefixMellin_of_one_lt_re
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction chi s =
      s * mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-s) := by
  calc
    DirichletCharacter.LFunction chi s = LSeries (chi ·) s :=
      DirichletCharacter.LFunction_eq_LSeries chi hs
    _ = s * ∫ y in Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) :=
      LSeries_eq_mul_integral (chi ·) (r := 0) le_rfl (zero_lt_one.trans hs)
        (DirichletCharacter.LSeriesSummable_of_one_lt_re chi hs)
        (DirichletLFunctionAbelContinuation_characterPartialSums_isBigO_atTop chi C hprefix)
    _ = s * mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-s) := by
      rw [DirichletLFunctionAbelContinuation_characterPrefixMellin_neg_eq_integral]

theorem LFunction_eq_abelIntegral_of_prefixBound
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    (s : ℂ) (hs : 0 < s.re) :
    DirichletCharacter.LFunction chi s =
      s * ∫ y in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) := by
  have hC : 0 ≤ C := by
    simpa using hprefix 0
  let U : Set ℂ := {w | 0 < w.re}
  have hUOpen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUPre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hLeft :
      AnalyticOnNhd ℂ (DirichletCharacter.LFunction chi) U :=
    (DirichletCharacter.differentiable_LFunction hchi).differentiableOn.analyticOnNhd hUOpen
  have hRight : AnalyticOnNhd ℂ
      (fun w ↦ w * mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-w)) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw ↦ ?_) hUOpen
    exact (differentiableAt_id.mul
      (DirichletLFunctionAbelContinuation_differentiableAt_characterPrefixMellin_neg chi C hC hprefix hw)).differentiableWithinAt
  have hEq : EqOn (DirichletCharacter.LFunction chi)
      (fun w ↦ w * mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-w)) U := by
    refine hLeft.eqOn_of_preconnected_of_eventuallyEq hRight hUPre
      (show (2 : ℂ) ∈ U by simp [U]) ?_
    refine eventually_of_mem
      ((isOpen_lt continuous_const continuous_re).mem_nhds
        (show 1 < (2 : ℂ).re by norm_num)) ?_
    intro w hw
    exact DirichletLFunctionAbelContinuation_LFunction_eq_characterPrefixMellin_of_one_lt_re chi C hprefix hw
  rw [hEq hs]
  change s * mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-s) = _
  rw [DirichletLFunctionAbelContinuation_characterPrefixMellin_neg_eq_integral]

end BoundedGaps.Maynard

end

/-! ## Standard additive characters on translated integer intervals

Source module `BoundedGaps.BombieriVinogradov.Analytic.StandardAddCharInterval`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

open AddChar Finset

private theorem StandardAddCharInterval_sum_Ioc_int_eq_sum_range_add_succ
    {A : Type*} [AddCommMonoid A] (f : ℤ → A) (M : ℤ) (N : ℕ) :
    (∑ m ∈ Finset.Ioc M (M + (N : ℤ)), f m) =
      ∑ n ∈ Finset.range N, f (M + (n + 1 : ℕ)) := by
  rw [Int.Ioc_eq_finset_map, Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply]
  congr 1
  · simp
  · funext n
    congr 1
    push_cast
    ring

private theorem StandardAddCharInterval_stdAddChar_mul_int_add_succ {q : ℕ} [NeZero q]
    (a : ZMod q) (M : ℤ) (n : ℕ) :
    ZMod.stdAddChar (a * ((M + ((n + 1 : ℕ) : ℤ) : ℤ) : ZMod q)) =
      ZMod.stdAddChar (a * ((M + 1 : ℤ) : ZMod q)) *
        ZMod.stdAddChar a ^ n := by
  rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_add_eq_mul]
  congr 1
  push_cast
  simp only [nsmul_eq_mul]
  ring

private theorem StandardAddCharInterval_stdAddChar_ne_one_of_ne_zero
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : a ≠ 0) :
    ZMod.stdAddChar a ≠ 1 := by
  intro h
  apply ha
  apply ZMod.injective_stdAddChar
  simpa only [AddChar.map_zero_eq_one] using h

private theorem StandardAddCharInterval_norm_stdAddChar_sub_one_eq_two_mul_abs_sin
    {q : ℕ} [NeZero q] (a : ZMod q) :
    ‖ZMod.stdAddChar a - 1‖ =
      2 * |Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ))| := by
  rw [← ZMod.natCast_zmod_val a]
  rw [show (a.val : ZMod q) = ((a.val : ℤ) : ZMod q) by simp,
    ZMod.stdAddChar_coe]
  simp only [Int.cast_natCast]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ) / (q : ℂ) =
      Complex.I * ((2 * Real.pi * (a.val : ℝ) / (q : ℝ) : ℝ) : ℂ) by
        push_cast
        ring]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  simp only [show (2 * Real.pi * (a.val : ℝ) / (q : ℝ)) / 2 =
    Real.pi * (a.val : ℝ) / (q : ℝ) by ring]
  rw [Real.norm_eq_abs, abs_mul]
  norm_num

theorem sum_stdAddChar_Ioc_eq_geometric
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : a ≠ 0)
    (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
      ZMod.stdAddChar (a * (n : ZMod q))) =
      ZMod.stdAddChar (a * ((M + 1 : ℤ) : ZMod q)) *
        ((1 - ZMod.stdAddChar (a * (N : ZMod q))) /
          (1 - ZMod.stdAddChar a)) := by
  rw [StandardAddCharInterval_sum_Ioc_int_eq_sum_range_add_succ]
  simp_rw [StandardAddCharInterval_stdAddChar_mul_int_add_succ]
  rw [← Finset.mul_sum, geom_sum_eq (StandardAddCharInterval_stdAddChar_ne_one_of_ne_zero ha)]
  have hpow : ZMod.stdAddChar (a * (N : ZMod q)) =
      ZMod.stdAddChar a ^ N := by
    rw [show a * (N : ZMod q) = N • a by ring,
      AddChar.map_nsmul_eq_pow]
  rw [hpow]
  congr 1
  rw [div_eq_mul_inv, div_eq_mul_inv,
    show ZMod.stdAddChar a - 1 = -(1 - ZMod.stdAddChar a) by ring,
    inv_neg]
  ring

theorem norm_sum_stdAddChar_Ioc_le_inv_sin
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : a ≠ 0)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
      ZMod.stdAddChar (a * (n : ZMod q))‖ ≤
      (Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)))⁻¹ := by
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have havalpos : (0 : ℝ) < a.val := by
    exact_mod_cast Nat.pos_of_ne_zero ((ZMod.val_ne_zero a).mpr ha)
  have hanglepos : 0 < Real.pi * (a.val : ℝ) / (q : ℝ) :=
    div_pos (mul_pos Real.pi_pos havalpos) hqpos
  have hanglelt : Real.pi * (a.val : ℝ) / (q : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hqpos]
    have havallt : (a.val : ℝ) < q := by exact_mod_cast a.val_lt
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi hanglepos hanglelt
  have hnum : ‖1 - ZMod.stdAddChar (a * (N : ZMod q))‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖ZMod.stdAddChar (a * (N : ZMod q))‖ :=
        norm_sub_le _ _
      _ = 2 := by rw [AddChar.norm_apply]; norm_num
  have hdenom : ‖1 - ZMod.stdAddChar a‖ =
      2 * Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)) := by
    rw [show (1 : ℂ) - ZMod.stdAddChar a =
      -(ZMod.stdAddChar a - 1) by ring, norm_neg,
      StandardAddCharInterval_norm_stdAddChar_sub_one_eq_two_mul_abs_sin,
      abs_of_pos hsin]
  rw [sum_stdAddChar_Ioc_eq_geometric ha, norm_mul,
    AddChar.norm_apply, one_mul, norm_div, hdenom]
  calc
    ‖1 - ZMod.stdAddChar (a * (N : ZMod q))‖ /
        (2 * Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ))) ≤
        2 / (2 * Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ))) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = (Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)))⁻¹ := by
      field_simp

end BoundedGaps.Maynard

end

/-! ## Primitive character sums on translated integer intervals

Source module `BoundedGaps.BombieriVinogradov.Analytic.PrimitiveCharacterInterval`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

open AddChar Finset

private theorem PrimitiveCharacterInterval_sum_zmod_erase_zero_eq_sum_Ico_val
    {q : ℕ} [NeZero q]
    {A : Type*} [AddCommMonoid A] (f : ZMod q → A) :
    (∑ a ∈ Finset.univ.erase (0 : ZMod q), f a) =
      ∑ a ∈ Finset.Ico 1 q, f (a : ZMod q) := by
  classical
  apply Finset.sum_nbij (fun a : ZMod q => a.val)
  · intro a ha
    have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
    exact Finset.mem_Ico.mpr ⟨ZMod.val_pos.mpr ha0, a.val_lt⟩
  · exact (ZMod.val_injective q).injOn
  · intro b hb
    have hbmem := Finset.mem_Ico.mp hb
    refine ⟨(b : ZMod q), ?_, ?_⟩
    · apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      apply (ZMod.val_ne_zero _).mp
      rw [ZMod.val_cast_of_lt hbmem.2]
      exact Nat.ne_of_gt hbmem.1
    · exact ZMod.val_cast_of_lt hbmem.2
  · intro a ha
    rw [ZMod.natCast_zmod_val]

theorem sum_dirichletCharacter_Ioc_eq_fourier
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi.IsPrimitive) (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
      (∑ a : ZMod q, chi⁻¹ a *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar (a * (n : ZMod q))) /
        gaussSum chi⁻¹ ZMod.stdAddChar := by
  classical
  have hpoint (n : ℤ) :
      chi (n : ZMod q) =
        (∑ a : ZMod q,
          chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
    exact primitive_fourier_expansion_div chi hchi (n : ZMod q)
  calc
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ((∑ a : ZMod q,
            chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
            gaussSum chi⁻¹ ZMod.stdAddChar) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hpoint n
    _ = (∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ∑ a : ZMod q,
            chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      rw [Finset.sum_div]
    _ = (∑ a : ZMod q, ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      rw [Finset.sum_comm]
    _ = (∑ a : ZMod q, chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.mul_sum]

theorem sum_dirichletCharacter_Ioc_eq_fourier_erase_zero
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
      (∑ a ∈ Finset.univ.erase (0 : ZMod q), chi⁻¹ a *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar (a * (n : ZMod q))) /
        gaussSum chi⁻¹ ZMod.stdAddChar := by
  classical
  have hzero : chi⁻¹ (0 : ZMod q) = 0 :=
    DirichletCharacter.map_zero' chi⁻¹ (Nat.ne_of_gt hq)
  calc
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
        (∑ a : ZMod q, chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar :=
      sum_dirichletCharacter_Ioc_eq_fourier chi hchi M N
    _ = (∑ a ∈ Finset.univ.erase (0 : ZMod q), chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod q))]
      simp [hzero]

theorem sum_dirichletCharacter_Ioc_eq_nat_fourier
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
      (∑ a ∈ Finset.Ico 1 q, chi⁻¹ (a : ZMod q) *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))) /
        gaussSum chi⁻¹ ZMod.stdAddChar := by
  classical
  calc
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
        (∑ a ∈ Finset.univ.erase (0 : ZMod q), chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar :=
      sum_dirichletCharacter_Ioc_eq_fourier_erase_zero hq chi hchi M N
    _ = (∑ a ∈ Finset.Ico 1 q, chi⁻¹ (a : ZMod q) *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      exact PrimitiveCharacterInterval_sum_zmod_erase_zero_eq_sum_Ico_val
        (f := fun a : ZMod q => chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q)))

theorem norm_sum_dirichletCharacter_Ioc_le_reciprocalSineSum
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)‖ ≤
      (∑ a ∈ Finset.Ico 1 q,
        (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹) /
        Real.sqrt q := by
  classical
  have hchiInv : chi⁻¹.IsPrimitive := by
    rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
    exact hchi
  have hgaussNorm : ‖gaussSum chi⁻¹ ZMod.stdAddChar‖ = Real.sqrt q :=
    norm_gaussSum_stdAddChar_of_isPrimitive chi⁻¹ hchiInv
  have hnumerator :
      ‖∑ a ∈ Finset.Ico 1 q, chi⁻¹ (a : ZMod q) *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ ≤
        ∑ a ∈ Finset.Ico 1 q,
          (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := by
    calc
      _ ≤ ∑ a ∈ Finset.Ico 1 q,
          ‖chi⁻¹ (a : ZMod q) *
            ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
              ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ a ∈ Finset.Ico 1 q,
          (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := by
        apply Finset.sum_le_sum
        intro a ha
        have haIco := Finset.mem_Ico.mp ha
        have ha0 : (a : ZMod q) ≠ 0 := by
          apply (ZMod.val_ne_zero (a : ZMod q)).mp
          rw [ZMod.val_cast_of_lt haIco.2]
          exact Nat.ne_of_gt haIco.1
        have hinterval := norm_sum_stdAddChar_Ioc_le_inv_sin
          (q := q) (a := (a : ZMod q)) ha0 M N
        rw [ZMod.val_cast_of_lt haIco.2] at hinterval
        calc
          ‖chi⁻¹ (a : ZMod q) *
              ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
                ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ =
              ‖chi⁻¹ (a : ZMod q)‖ *
                ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
                  ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ :=
            norm_mul _ _
          _ ≤ 1 * (Real.sin
                (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ :=
            mul_le_mul (DirichletCharacter.norm_le_one chi⁻¹ (a : ZMod q))
              hinterval (norm_nonneg _) zero_le_one
          _ = (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := one_mul _
  rw [sum_dirichletCharacter_Ioc_eq_nat_fourier hq chi hchi M N,
    norm_div, hgaussNorm]
  exact div_le_div_of_nonneg_right hnumerator (Real.sqrt_nonneg q)

end BoundedGaps.Maynard

end

/-! ## The sharp reciprocal-sine aggregate

Source module `BoundedGaps.BombieriVinogradov.Analytic.ReciprocalSineAggregate`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

open Finset

private theorem ReciprocalSineAggregate_harmonic_cast_le_log_two_mul_add_one (n : ℕ) :
    (harmonic n : ℝ) ≤ Real.log (2 * (n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [harmonic_succ]
      simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Nat.cast_succ]
      have hden : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
      have hlog := Real.le_log_one_add_of_nonneg
        (show (0 : ℝ) ≤ 2 / (2 * (n : ℝ) + 1) by positivity)
      have hincrement :
          ((n : ℝ) + 1)⁻¹ ≤
            Real.log (2 * ((n : ℝ) + 1) + 1) -
              Real.log (2 * (n : ℝ) + 1) := by
        rw [← Real.log_div (by positivity) hden.ne']
        convert hlog using 1 <;> field_simp <;> ring_nf
      linarith

private theorem ReciprocalSineAggregate_harmonic_cast_lt_log_two_mul_add_one {n : ℕ} (hn : 0 < n) :
    (harmonic n : ℝ) < Real.log (2 * (n : ℝ) + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [harmonic_succ]
  simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Nat.cast_succ]
  have hbase := ReciprocalSineAggregate_harmonic_cast_le_log_two_mul_add_one n
  have hden : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hlog := Real.lt_log_one_add_of_pos
    (show (0 : ℝ) < 2 / (2 * (n : ℝ) + 1) by positivity)
  have hincrement :
      ((n : ℝ) + 1)⁻¹ <
        Real.log (2 * ((n : ℝ) + 1) + 1) -
          Real.log (2 * (n : ℝ) + 1) := by
    rw [← Real.log_div (by positivity) hden.ne']
    convert hlog using 1 <;> field_simp <;> ring_nf
  linarith

private theorem ReciprocalSineAggregate_harmonic_cast_pred_add_inv_two_mul_lt_log_two_mul
    {m : ℕ} (hm : 0 < m) :
    (harmonic (m - 1) : ℝ) + (((2 * m : ℕ) : ℝ))⁻¹ <
      Real.log (((2 * m : ℕ) : ℝ)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp only [Nat.succ_sub_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ]
  have hbase := ReciprocalSineAggregate_harmonic_cast_le_log_two_mul_add_one m
  have hden : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  have hx : (0 : ℝ) < (2 * (m : ℝ) + 1)⁻¹ := by positivity
  have hlog := Real.lt_log_one_add_of_pos hx
  have hincrement :
      (2 * ((m : ℝ) + 1))⁻¹ <
        Real.log (2 * ((m : ℝ) + 1)) -
          Real.log (2 * (m : ℝ) + 1) := by
    rw [← Real.log_div (by positivity) hden.ne']
    calc
      (2 * ((m : ℝ) + 1))⁻¹ <
          2 * (2 * (m : ℝ) + 1)⁻¹ /
            ((2 * (m : ℝ) + 1)⁻¹ + 2) := by
        field_simp
        linarith
      _ < Real.log (1 + (2 * (m : ℝ) + 1)⁻¹) := hlog
      _ = Real.log (2 * ((m : ℝ) + 1) / (2 * (m : ℝ) + 1)) := by
        congr 1
        field_simp
        ring
  linarith

private noncomputable def ReciprocalSineAggregate_reciprocalSineTerm (q a : ℕ) : ℝ :=
  (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹

private theorem ReciprocalSineAggregate_reciprocalSineTerm_le_div {q a : ℕ} (hq : 0 < q)
    (ha : 0 < a) (haq : 2 * a ≤ q) :
    ReciprocalSineAggregate_reciprocalSineTerm q a ≤ (q : ℝ) / (2 * (a : ℝ)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hangle0 : 0 ≤ Real.pi * (a : ℝ) / (q : ℝ) := by positivity
  have hanglehalf : Real.pi * (a : ℝ) / (q : ℝ) ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ hqR zero_lt_two]
    have haqR : (2 : ℝ) * (a : ℝ) ≤ q := by exact_mod_cast haq
    nlinarith [Real.pi_pos]
  have hjordan := Real.mul_le_sin hangle0 hanglehalf
  have hbase : 0 < 2 / Real.pi *
      (Real.pi * (a : ℝ) / (q : ℝ)) := by positivity
  have hinv := inv_anti₀ hbase hjordan
  calc
    ReciprocalSineAggregate_reciprocalSineTerm q a =
        (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := rfl
    _ ≤ (2 / Real.pi * (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := hinv
    _ = (q : ℝ) / (2 * (a : ℝ)) := by field_simp

private theorem ReciprocalSineAggregate_reciprocalSineTerm_sub {q a : ℕ} (hq : 0 < q) (ha : a ≤ q) :
    ReciprocalSineAggregate_reciprocalSineTerm q (q - a) = ReciprocalSineAggregate_reciprocalSineTerm q a := by
  rw [ReciprocalSineAggregate_reciprocalSineTerm, ReciprocalSineAggregate_reciprocalSineTerm, Nat.cast_sub ha]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  rw [show Real.pi * ((q : ℝ) - (a : ℝ)) / (q : ℝ) =
      Real.pi - Real.pi * (a : ℝ) / (q : ℝ) by field_simp,
    Real.sin_pi_sub]

private theorem ReciprocalSineAggregate_reciprocalSineTerm_two_mul_self {m : ℕ} (hm : 0 < m) :
    ReciprocalSineAggregate_reciprocalSineTerm (2 * m) m = 1 := by
  rw [ReciprocalSineAggregate_reciprocalSineTerm]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [show Real.pi * (m : ℝ) / ((2 * m : ℕ) : ℝ) = Real.pi / 2 by
      push_cast
      field_simp,
    Real.sin_pi_div_two, inv_one]

private theorem ReciprocalSineAggregate_sum_Ico_inv_eq_harmonic (n : ℕ) :
    (∑ a ∈ Finset.Ico 1 (n + 1), ((a : ℝ))⁻¹) = (harmonic n : ℝ) := by
  rw [Finset.Ico_add_one_right_eq_Icc]
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

private theorem ReciprocalSineAggregate_sum_reciprocalSine_Ico_le_half_mul_harmonic
    {q m : ℕ} (hq : 0 < q) (hmq : 2 * m ≤ q) :
    (∑ a ∈ Finset.Ico 1 (m + 1), ReciprocalSineAggregate_reciprocalSineTerm q a) ≤
      (q : ℝ) / 2 * (harmonic m : ℝ) := by
  calc
    (∑ a ∈ Finset.Ico 1 (m + 1), ReciprocalSineAggregate_reciprocalSineTerm q a) ≤
        ∑ a ∈ Finset.Ico 1 (m + 1), (q : ℝ) / (2 * (a : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact ReciprocalSineAggregate_reciprocalSineTerm_le_div hq (Finset.mem_Ico.mp ha).1
        ((Nat.mul_le_mul_left 2
          (Nat.le_of_lt_succ (Finset.mem_Ico.mp ha).2)).trans hmq)
    _ = (q : ℝ) / 2 *
        ∑ a ∈ Finset.Ico 1 (m + 1), ((a : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      field_simp
    _ = (q : ℝ) / 2 * (harmonic m : ℝ) := by
      rw [ReciprocalSineAggregate_sum_Ico_inv_eq_harmonic]

private theorem ReciprocalSineAggregate_sum_reciprocalSine_odd_eq_two_mul (m : ℕ) :
    (∑ a ∈ Finset.Ico 1 (2 * m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a) =
      2 * ∑ a ∈ Finset.Ico 1 (m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a := by
  have hq : 0 < 2 * m + 1 := by omega
  have hreflect := Finset.sum_Ico_reflect
    (ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1)) 1
    (m := m + 1) (n := 2 * m + 1) (by omega)
  have hb1 : 2 * m + 1 + 1 - (m + 1) = m + 1 := by omega
  have hb2 : 2 * m + 1 + 1 - 1 = 2 * m + 1 := by omega
  rw [hb1, hb2] at hreflect
  have hupper :
      (∑ a ∈ Finset.Ico (m + 1) (2 * m + 1),
        ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a) =
        ∑ a ∈ Finset.Ico 1 (m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a := by
    rw [← hreflect]
    apply Finset.sum_congr rfl
    intro a ha
    apply ReciprocalSineAggregate_reciprocalSineTerm_sub hq
    exact (Nat.le_of_lt_succ (Finset.mem_Ico.mp ha).2).trans (by omega)
  calc
    (∑ a ∈ Finset.Ico 1 (2 * m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a) =
        (∑ a ∈ Finset.Ico 1 (m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a) +
          ∑ a ∈ Finset.Ico (m + 1) (2 * m + 1),
            ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a := by
      rw [Finset.sum_Ico_consecutive (ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1))
        (by omega) (by omega)]
    _ = 2 * ∑ a ∈ Finset.Ico 1 (m + 1),
        ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a := by rw [hupper]; ring

private theorem ReciprocalSineAggregate_sum_reciprocalSine_even_eq_two_mul_add_one
    {m : ℕ} (hm : 0 < m) :
    (∑ a ∈ Finset.Ico 1 (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) =
      2 * (∑ a ∈ Finset.Ico 1 m, ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) + 1 := by
  have hq : 0 < 2 * m := Nat.mul_pos two_pos hm
  have hreflect := Finset.sum_Ico_reflect
    (ReciprocalSineAggregate_reciprocalSineTerm (2 * m)) 1
    (m := m) (n := 2 * m) (by omega)
  have hb1 : 2 * m + 1 - m = m + 1 := by omega
  have hb2 : 2 * m + 1 - 1 = 2 * m := by omega
  rw [hb1, hb2] at hreflect
  have hupper :
      (∑ a ∈ Finset.Ico (m + 1) (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) =
        ∑ a ∈ Finset.Ico 1 m, ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a := by
    rw [← hreflect]
    apply Finset.sum_congr rfl
    intro a ha
    apply ReciprocalSineAggregate_reciprocalSineTerm_sub hq
    exact (Nat.le_of_lt (Finset.mem_Ico.mp ha).2).trans (by omega)
  have hrest :
      (∑ a ∈ Finset.Ico m (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) =
        ReciprocalSineAggregate_reciprocalSineTerm (2 * m) m +
          ∑ a ∈ Finset.Ico (m + 1) (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a := by
    calc
      _ = (∑ a ∈ Finset.Ico m (m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) +
          ∑ a ∈ Finset.Ico (m + 1) (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a := by
        rw [Finset.sum_Ico_consecutive (ReciprocalSineAggregate_reciprocalSineTerm (2 * m))
          (by omega) (by omega)]
      _ = _ := by simp
  calc
    (∑ a ∈ Finset.Ico 1 (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) =
        (∑ a ∈ Finset.Ico 1 m, ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) +
          ∑ a ∈ Finset.Ico m (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a := by
      rw [Finset.sum_Ico_consecutive (ReciprocalSineAggregate_reciprocalSineTerm (2 * m))
        (by omega) (by omega)]
    _ = 2 * (∑ a ∈ Finset.Ico 1 m, ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) + 1 := by
      rw [hrest, hupper, ReciprocalSineAggregate_reciprocalSineTerm_two_mul_self hm]
      ring

theorem sum_reciprocalSine_Ico_lt_mul_log {q : ℕ} (hq : 1 < q) :
    (∑ a ∈ Finset.Ico 1 q,
      (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹) <
      (q : ℝ) * Real.log (q : ℝ) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' q
  · have hm : 0 < m := by omega
    change (∑ a ∈ Finset.Ico 1 (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) < _
    rw [ReciprocalSineAggregate_sum_reciprocalSine_even_eq_two_mul_add_one hm]
    have hhalf := ReciprocalSineAggregate_sum_reciprocalSine_Ico_le_half_mul_harmonic
      (q := 2 * m) (m := m - 1) (by omega) (by omega)
    have htop : m - 1 + 1 = m := Nat.sub_add_cancel hm
    rw [htop] at hhalf
    have hlog := ReciprocalSineAggregate_harmonic_cast_pred_add_inv_two_mul_lt_log_two_mul hm
    calc
      2 * (∑ a ∈ Finset.Ico 1 m, ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) + 1 ≤
          2 * (((2 * m : ℕ) : ℝ) / 2 * (harmonic (m - 1) : ℝ)) + 1 :=
        by
          simpa only [add_comm] using add_le_add_right
            (mul_le_mul_of_nonneg_left hhalf (show (0 : ℝ) ≤ 2 by norm_num)) 1
      _ = ((2 * m : ℕ) : ℝ) *
          ((harmonic (m - 1) : ℝ) + (((2 * m : ℕ) : ℝ))⁻¹) := by
        have htwoM : (((2 * m : ℕ) : ℝ)) ≠ 0 := by positivity
        field_simp
      _ < ((2 * m : ℕ) : ℝ) * Real.log (((2 * m : ℕ) : ℝ)) :=
        mul_lt_mul_of_pos_left hlog (by positivity)
  · have hm : 0 < m := by omega
    change (∑ a ∈ Finset.Ico 1 (2 * m + 1),
      ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a) < _
    rw [ReciprocalSineAggregate_sum_reciprocalSine_odd_eq_two_mul]
    have hhalf := ReciprocalSineAggregate_sum_reciprocalSine_Ico_le_half_mul_harmonic
      (q := 2 * m + 1) (m := m) (by omega) (by omega)
    have hlog := ReciprocalSineAggregate_harmonic_cast_lt_log_two_mul_add_one hm
    calc
      2 * (∑ a ∈ Finset.Ico 1 (m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a) ≤
          2 * (((2 * m + 1 : ℕ) : ℝ) / 2 * (harmonic m : ℝ)) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
      _ = ((2 * m + 1 : ℕ) : ℝ) * (harmonic m : ℝ) := by ring
      _ < ((2 * m + 1 : ℕ) : ℝ) * Real.log (((2 * m + 1 : ℕ) : ℝ)) := by
        apply mul_lt_mul_of_pos_left _ (by positivity)
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hlog

end BoundedGaps.Maynard

end

/-! ## Primitive Polya--Vinogradov interval bound

Source module `BoundedGaps.BombieriVinogradov.Analytic.PrimitivePolyaVinogradov`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

theorem norm_sum_dirichletCharacter_Ioc_lt_sqrt_mul_log
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)‖ <
      Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast Nat.zero_lt_of_lt hq
  have hsqrt : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hqpos
  calc
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)‖ ≤
        (∑ a ∈ Finset.Ico 1 q,
          (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹) /
          Real.sqrt q :=
      norm_sum_dirichletCharacter_Ioc_le_reciprocalSineSum hq chi hchi M N
    _ < ((q : ℝ) * Real.log (q : ℝ)) / Real.sqrt q :=
      div_lt_div_of_pos_right (sum_reciprocalSine_Ico_lt_mul_log hq) hsqrt
    _ = Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      apply (div_eq_iff hsqrt.ne').2
      calc
        (q : ℝ) * Real.log (q : ℝ) =
            (Real.sqrt (q : ℝ)) ^ 2 * Real.log (q : ℝ) := by
          rw [Real.sq_sqrt hqpos.le]
        _ = (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
            Real.sqrt (q : ℝ) := by ring

end BoundedGaps.Maynard

end

/-! ## Vaughan's second-term finite reduction

Source module `BoundedGaps.BombieriVinogradov.Analytic.VaughanSecondTermReduction`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable def dirichletCharacterIntervalSum
    (a b q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ h ∈ Finset.Icc a b, χ h

end BoundedGaps.Maynard

end

/-! ## Polya--Vinogradov bound for Vaughan's second term

Source module `BoundedGaps.BombieriVinogradov.Analytic.VaughanSecondTermPolyaVinogradov`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

theorem norm_dirichletCharacterIntervalSum_lt_sqrt_mul_log
    {q : ℕ} (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (a b : ℕ) :
    ‖dirichletCharacterIntervalSum a b q chi‖ <
      Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  letI : NeZero q := ⟨Nat.ne_zero_of_lt hq⟩
  have hboundPos :
      0 < Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
    exact mul_pos (Real.sqrt_pos.2 (by exact_mod_cast Nat.zero_lt_of_lt hq))
      (Real.log_pos (by exact_mod_cast hq))
  by_cases hab : a ≤ b
  · have hendpoint :
        (a : ℤ) - 1 + (((b - a) + 1 : ℕ) : ℤ) = (b : ℤ) := by
      rw [Nat.cast_add, Nat.cast_sub hab]
      push_cast
      ring
    have hfinset :
        (Finset.Icc a b).map (Nat.castEmbedding : ℕ ↪ ℤ) =
          Finset.Ioc ((a : ℤ) - 1) (b : ℤ) := by
      ext n
      simp only [Finset.mem_map, Nat.castEmbedding_apply, Finset.mem_Icc,
        Finset.mem_Ioc]
      constructor
      · rintro ⟨m, hm, rfl⟩
        constructor <;> omega
      · intro hn
        have hnnonneg : 0 ≤ n := by
          have : (a : ℤ) ≤ n := by omega
          exact (Int.natCast_nonneg a).trans this
        lift n to ℕ using hnnonneg with m
        refine ⟨m, ?_, rfl⟩
        constructor <;> omega
    rw [dirichletCharacterIntervalSum]
    calc
      ‖∑ n ∈ Finset.Icc a b, chi n‖ =
          ‖∑ n ∈ Finset.Ioc ((a : ℤ) - 1) (b : ℤ),
            chi (n : ZMod q)‖ := by
        rw [← hfinset, Finset.sum_map]
        simp
      _ = ‖∑ n ∈ Finset.Ioc ((a : ℤ) - 1)
            ((a : ℤ) - 1 + (((b - a) + 1 : ℕ) : ℤ)),
            chi (n : ZMod q)‖ := by rw [hendpoint]
      _ < Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
        norm_sum_dirichletCharacter_Ioc_lt_sqrt_mul_log hq chi hchi
          ((a : ℤ) - 1) ((b - a) + 1)
  · rw [dirichletCharacterIntervalSum, Finset.Icc_eq_empty (by omega),
      Finset.sum_empty, norm_zero]
    exact hboundPos

end BoundedGaps.Maynard

end

/-! ## Polya--Vinogradov for imprimitive prefixes

Source module `BoundedGaps.BombieriVinogradov.Analytic.ImprimitivePolyaVinogradovPrefix`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators

private theorem ImprimitivePolyaVinogradovPrefix_card_divisors_le_two_mul_sqrt
    {n : ℕ} (hn : 0 < n) :
    n.divisors.card ≤ 2 * Nat.sqrt n := by
  classical
  let small := n.divisors.filter fun d ↦ d ≤ Nat.sqrt n
  let large := n.divisors.filter fun d ↦ ¬d ≤ Nat.sqrt n
  have hsmall : small.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := by
    apply Finset.card_le_card
    intro d hd
    simp only [small, Finset.mem_filter] at hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd.1, hd.2⟩
  have hlarge : large.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := by
    refine Finset.card_le_card_of_injOn (fun d ↦ n / d) ?_ ?_
    · intro d hd
      simp only [large, Finset.mem_coe, Finset.mem_filter] at hd
      have hdDvd : d ∣ n := (Nat.mem_divisors.mp hd.1).1
      have hdPos : 0 < d := Nat.pos_of_mem_divisors hd.1
      have hquotPos : 0 < n / d :=
        Nat.div_pos (Nat.le_of_dvd hn hdDvd) hdPos
      have hfactor : n = d * (n / d) := (Nat.mul_div_cancel' hdDvd).symm
      exact Finset.mem_Icc.mpr
        ⟨hquotPos, (Nat.le_sqrt_of_eq_mul hfactor).resolve_left hd.2⟩
    · intro d₁ hd₁ d₂ hd₂ heq
      simp only [large, Finset.mem_coe, Finset.mem_filter] at hd₁ hd₂
      have hd₁Dvd : d₁ ∣ n := (Nat.mem_divisors.mp hd₁.1).1
      have hd₂Dvd : d₂ ∣ n := (Nat.mem_divisors.mp hd₂.1).1
      have hquotPos : 0 < n / d₁ :=
        Nat.div_pos (Nat.le_of_dvd hn hd₁Dvd)
          (Nat.pos_of_mem_divisors hd₁.1)
      change n / d₁ = n / d₂ at heq
      apply Nat.mul_right_cancel hquotPos
      calc
        d₁ * (n / d₁) = n := Nat.mul_div_cancel' hd₁Dvd
        _ = d₂ * (n / d₂) := (Nat.mul_div_cancel' hd₂Dvd).symm
        _ = d₂ * (n / d₁) := by rw [heq]
  have hsmall' : small.card ≤ Nat.sqrt n := by
    calc
      small.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := hsmall
      _ = Nat.sqrt n := by rw [Nat.card_Icc]; omega
  have hlarge' : large.card ≤ Nat.sqrt n := by
    calc
      large.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := hlarge
      _ = Nat.sqrt n := by rw [Nat.card_Icc]; omega
  have hpartition : small.card + large.card = n.divisors.card := by
    simpa [small, large] using
      (Finset.card_filter_add_card_filter_not (s := n.divisors)
        (fun d ↦ d ≤ Nat.sqrt n))
  omega

private theorem ImprimitivePolyaVinogradovPrefix_divisors_gcd_eq_filter
    {n r : ℕ} (hn : 0 < n) (hr : 0 < r) :
    (n.gcd r).divisors = r.divisors.filter (fun a ↦ a ∣ n) := by
  ext a
  have hgcd : 0 < n.gcd r := Nat.gcd_pos_of_pos_left r hn
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨ha, _⟩
    exact ⟨⟨ha.trans (Nat.gcd_dvd_right n r), hr.ne'⟩,
      ha.trans (Nat.gcd_dvd_left n r)⟩
  · rintro ⟨⟨har, _⟩, han⟩
    exact ⟨Nat.dvd_gcd han har, hgcd.ne'⟩

private theorem ImprimitivePolyaVinogradovPrefix_sum_moebius_divisors_eq_coprimeIndicator
    {n r : ℕ} (hn : 0 < n) (hr : 0 < r) :
    (∑ a ∈ r.divisors,
      if a ∣ n then
        ((ArithmeticFunction.moebius a : ℤ) : ℂ)
      else 0) =
      if n.Coprime r then 1 else 0 := by
  have hgcd : 0 < n.gcd r := Nat.gcd_pos_of_pos_left r hn
  calc
    (∑ a ∈ r.divisors,
        if a ∣ n then ((ArithmeticFunction.moebius a : ℤ) : ℂ) else 0) =
        ∑ a ∈ r.divisors.filter (fun a ↦ a ∣ n),
          ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
      rw [Finset.sum_filter]
    _ = ∑ a ∈ (n.gcd r).divisors,
          ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
      rw [ImprimitivePolyaVinogradovPrefix_divisors_gcd_eq_filter hn hr]
    _ = ∑ a ∈ (n.gcd r).divisors,
          (ArithmeticFunction.moebius : ArithmeticFunction ℂ) a := by
      simp
    _ = (((ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) (n.gcd r)) := by
      rw [ArithmeticFunction.coe_mul_zeta_apply]
    _ = (1 : ArithmeticFunction ℂ) (n.gcd r) := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
    _ = if n.Coprime r then 1 else 0 := by
      by_cases hcop : n.Coprime r <;> simp [hcop]

private theorem ImprimitivePolyaVinogradovPrefix_character_eq_primitive_mul_coprimeIndicator
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (n : ℕ) :
    chi n = chi.primitiveCharacter n *
      (if n.Coprime (q / chi.conductor) then 1 else 0) := by
  have hdvd : chi.conductor ∣ q := chi.conductor_dvd_level
  have hfactor : chi.conductor * (q / chi.conductor) = q :=
    Nat.mul_div_cancel' hdvd
  by_cases hnr : n.Coprime (q / chi.conductor)
  · rw [if_pos hnr, mul_one]
    by_cases hnd : n.Coprime chi.conductor
    · have hnq : n.Coprime q := by
        rw [← hfactor, Nat.coprime_mul_iff_right]
        exact ⟨hnd, hnr⟩
      simpa only [Int.cast_natCast] using
        (chi.primitiveCharacter_apply_of_isCoprime
          (Nat.isCoprime_iff_coprime.mpr hnq)).symm
    · have hnq : ¬n.Coprime q := by
        rw [← hfactor, Nat.coprime_mul_iff_right]
        exact fun h ↦ hnd h.1
      have hchiZero : chi (n : ℤ) = 0 :=
        (DirichletCharacter.apply_eq_zero_iff chi (n : ℤ)).2
          (fun h ↦ hnq (Nat.isCoprime_iff_coprime.mp h))
      have hpsiZero : chi.primitiveCharacter (n : ℤ) = 0 :=
        (DirichletCharacter.apply_eq_zero_iff chi.primitiveCharacter (n : ℤ)).2
          (fun h ↦ hnd (Nat.isCoprime_iff_coprime.mp h))
      simpa only [Int.cast_natCast] using hchiZero.trans hpsiZero.symm
  · rw [if_neg hnr, mul_zero]
    have hnq : ¬n.Coprime q := by
      rw [← hfactor, Nat.coprime_mul_iff_right]
      exact fun h ↦ hnr h.2
    simpa only [Int.cast_natCast] using
      (DirichletCharacter.apply_eq_zero_iff chi (n : ℤ)).2
        (fun h ↦ hnq (Nat.isCoprime_iff_coprime.mp h))

private theorem ImprimitivePolyaVinogradovPrefix_sum_multiples_character
    {d a Y : ℕ} (ha : 0 < a) (psi : DirichletCharacter ℂ d) :
    (∑ n ∈ (Finset.Icc 1 Y).filter (fun n ↦ a ∣ n), psi n) =
      ∑ m ∈ Finset.Icc 1 (Y / a), psi (a * m) := by
  classical
  refine Finset.sum_bij'
    (fun n _ ↦ n / a) (fun m _ ↦ a * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    have hnPos : 0 < n := zero_lt_one.trans_le hn.1.1
    exact Finset.mem_Icc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd hnPos hn.2) ha,
        Nat.div_le_div_right hn.1.2⟩
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos ha hm.1,
        by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha).mp hm.2⟩,
        Nat.dvd_mul_right a m⟩
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m hm
    exact Nat.mul_div_cancel_left m ha
  · intro n hn
    simp only [Finset.mem_filter] at hn
    congr 1
    simpa only [Nat.cast_mul] using
      congrArg (fun k : ℕ ↦ (k : ZMod d))
        (Nat.mul_div_cancel' hn.2).symm

private theorem ImprimitivePolyaVinogradovPrefix_imprimitivePrefix_eq_divisorSum
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (Y : ℕ) :
    dirichletCharacterIntervalSum 1 Y q chi =
      ∑ a ∈ (q / chi.conductor).divisors,
        (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
            chi.primitiveCharacter a) *
          dirichletCharacterIntervalSum 1 (Y / a) chi.conductor
            chi.primitiveCharacter := by
  classical
  have hdPos : 0 < chi.conductor := Nat.pos_of_ne_zero chi.conductor_ne_zero
  have hrPos : 0 < q / chi.conductor :=
    Nat.div_pos
      (Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level) hdPos
  rw [dirichletCharacterIntervalSum]
  calc
    (∑ n ∈ Finset.Icc 1 Y, chi n) =
        ∑ n ∈ Finset.Icc 1 Y,
          chi.primitiveCharacter n *
            (if n.Coprime (q / chi.conductor) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact ImprimitivePolyaVinogradovPrefix_character_eq_primitive_mul_coprimeIndicator chi n
    _ = ∑ n ∈ Finset.Icc 1 Y,
          chi.primitiveCharacter n *
            (∑ a ∈ (q / chi.conductor).divisors,
              if a ∣ n then
                ((ArithmeticFunction.moebius a : ℤ) : ℂ)
              else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ImprimitivePolyaVinogradovPrefix_sum_moebius_divisors_eq_coprimeIndicator
        (zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1) hrPos]
    _ = ∑ a ∈ (q / chi.conductor).divisors,
          ∑ n ∈ Finset.Icc 1 Y,
            chi.primitiveCharacter n *
              (if a ∣ n then
                ((ArithmeticFunction.moebius a : ℤ) : ℂ)
              else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ a ∈ (q / chi.conductor).divisors,
        (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
            chi.primitiveCharacter a) *
          dirichletCharacterIntervalSum 1 (Y / a) chi.conductor
            chi.primitiveCharacter := by
      apply Finset.sum_congr rfl
      intro a ha
      have haPos : 0 < a := Nat.pos_of_mem_divisors ha
      calc
        (∑ n ∈ Finset.Icc 1 Y,
            chi.primitiveCharacter n *
              (if a ∣ n then
                ((ArithmeticFunction.moebius a : ℤ) : ℂ)
              else 0)) =
            ∑ n ∈ (Finset.Icc 1 Y).filter (fun n ↦ a ∣ n),
              chi.primitiveCharacter n *
                ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro n hn
          by_cases han : a ∣ n <;> simp [han]
        _ = ∑ m ∈ Finset.Icc 1 (Y / a),
              chi.primitiveCharacter (a * m) *
                ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
          rw [← Finset.sum_mul, ImprimitivePolyaVinogradovPrefix_sum_multiples_character haPos,
            Finset.sum_mul]
        _ = (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a) *
            (∑ m ∈ Finset.Icc 1 (Y / a),
              chi.primitiveCharacter m) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          rw [map_mul]
          ring
        _ = (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a) *
            dirichletCharacterIntervalSum 1 (Y / a) chi.conductor
              chi.primitiveCharacter := by
          rw [dirichletCharacterIntervalSum]

theorem norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (Y : ℕ) :
    ‖dirichletCharacterIntervalSum 1 Y q chi‖ ≤
      2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  let d := chi.conductor
  let r := q / d
  have hdPos : 0 < d := Nat.pos_of_ne_zero chi.conductor_ne_zero
  have hdDvd : d ∣ q := chi.conductor_dvd_level
  have hfactor : d * r = q := Nat.mul_div_cancel' hdDvd
  have hrPos : 0 < r :=
    Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) hdDvd) hdPos
  have hdNeOne : d ≠ 1 := by
    intro hd
    exact hchi (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hd)
  have hd : 1 < d := by omega
  have hdLeq : d ≤ q := Nat.le_of_dvd (NeZero.pos q) hdDvd
  letI : NeZero d := ⟨hdPos.ne'⟩
  have hscalePos :
      0 < Real.sqrt (d : ℝ) * Real.log (d : ℝ) :=
    mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hdPos))
      (Real.log_pos (by exact_mod_cast hd))
  have hcard : r.divisors.card ≤ 2 * Nat.sqrt r :=
    ImprimitivePolyaVinogradovPrefix_card_divisors_le_two_mul_sqrt hrPos
  have hcardReal :
      (r.divisors.card : ℝ) ≤ 2 * Real.sqrt (r : ℝ) := by
    calc
      (r.divisors.card : ℝ) ≤ ((2 * Nat.sqrt r : ℕ) : ℝ) := by
        exact_mod_cast hcard
      _ = 2 * (Nat.sqrt r : ℝ) := by norm_num
      _ ≤ 2 * Real.sqrt (r : ℝ) := by
        gcongr
        exact Real.nat_sqrt_le_real_sqrt
  have hsqrt :
      Real.sqrt (d : ℝ) * Real.sqrt (r : ℝ) = Real.sqrt (q : ℝ) := by
    calc
      Real.sqrt (d : ℝ) * Real.sqrt (r : ℝ) =
          Real.sqrt ((d : ℝ) * (r : ℝ)) :=
        (Real.sqrt_mul (by positivity) _).symm
      _ = Real.sqrt (q : ℝ) := by rw [← Nat.cast_mul, hfactor]
  have hlog : Real.log (d : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by exact_mod_cast hdPos) (by exact_mod_cast hdLeq)
  rw [ImprimitivePolyaVinogradovPrefix_imprimitivePrefix_eq_divisorSum chi Y]
  calc
    ‖∑ a ∈ r.divisors,
        (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
            chi.primitiveCharacter a) *
          dirichletCharacterIntervalSum 1 (Y / a) d
            chi.primitiveCharacter‖ ≤
        ∑ a ∈ r.divisors,
          ‖(((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a) *
            dirichletCharacterIntervalSum 1 (Y / a) d
              chi.primitiveCharacter‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ r.divisors,
        Real.sqrt (d : ℝ) * Real.log (d : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      have hmu : ‖((ArithmeticFunction.moebius a : ℤ) : ℂ)‖ ≤ 1 := by
        rcases ArithmeticFunction.moebius_eq_or a with hzero | hone | hneg
        · simp [hzero]
        · simp [hone]
        · simp [hneg]
      have hcoeff :
          ‖((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a‖ ≤ 1 := by
        rw [norm_mul]
        calc
          ‖((ArithmeticFunction.moebius a : ℤ) : ℂ)‖ *
              ‖chi.primitiveCharacter a‖ ≤ 1 * 1 :=
            mul_le_mul hmu (chi.primitiveCharacter.norm_le_one a)
              (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      rw [norm_mul]
      calc
        ‖((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a‖ *
            ‖dirichletCharacterIntervalSum 1 (Y / a) d
              chi.primitiveCharacter‖ ≤
            1 * ‖dirichletCharacterIntervalSum 1 (Y / a) d
              chi.primitiveCharacter‖ :=
          mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
        _ ≤ Real.sqrt (d : ℝ) * Real.log (d : ℝ) := by
          simpa using
            (norm_dirichletCharacterIntervalSum_lt_sqrt_mul_log
              hd chi.primitiveCharacter chi.primitiveCharacter_isPrimitive
              1 (Y / a)).le
    _ = (r.divisors.card : ℝ) *
        (Real.sqrt (d : ℝ) * Real.log (d : ℝ)) := by simp
    _ ≤ (2 * Real.sqrt (r : ℝ)) *
        (Real.sqrt (d : ℝ) * Real.log (d : ℝ)) :=
      mul_le_mul_of_nonneg_right hcardReal hscalePos.le
    _ = 2 * Real.sqrt (q : ℝ) * Real.log (d : ℝ) := by
      calc
        (2 * Real.sqrt (r : ℝ)) *
            (Real.sqrt (d : ℝ) * Real.log (d : ℝ)) =
            2 * (Real.sqrt (d : ℝ) * Real.sqrt (r : ℝ)) *
              Real.log (d : ℝ) := by ring
        _ = 2 * Real.sqrt (q : ℝ) * Real.log (d : ℝ) := by rw [hsqrt]
    _ ≤ 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      gcongr

end BoundedGaps.Maynard

end

/-! ## Partial summation for nonprincipal character prefixes

Source module `BoundedGaps.BombieriVinogradov.Analytic.CharacterPartialSummation`. -/

noncomputable section

open MeasureTheory Set

open scoped BigOperators

namespace BoundedGaps.Maynard

private noncomputable def CharacterPartialSummation_characterCumulative
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, chi (n : ZMod q)

private lemma CharacterPartialSummation_characterCumulative_eq_interval
    {q : ℕ} (hq : 1 < q) (chi : DirichletCharacter ℂ q) (t : ℝ) :
    CharacterPartialSummation_characterCumulative chi t =
      dirichletCharacterIntervalSum 1 ⌊t⌋₊ q chi := by
  rw [CharacterPartialSummation_characterCumulative, dirichletCharacterIntervalSum,
    Finset.Icc_eq_cons_Ioc (Nat.zero_le ⌊t⌋₊), Finset.sum_cons]
  have hzero : chi ((0 : ℕ) : ZMod q) = 0 := by
    simpa only [Nat.cast_zero] using chi.map_zero' (Nat.ne_of_gt hq)
  rw [hzero, zero_add, ← Finset.Icc_add_one_left_eq_Ioc 0 ⌊t⌋₊]
  norm_num

private lemma CharacterPartialSummation_norm_characterCumulative_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (t : ℝ) :
    ‖CharacterPartialSummation_characterCumulative chi t‖ ≤
      2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  rw [CharacterPartialSummation_characterCumulative_eq_interval hq]
  exact norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
    hq chi hchi ⌊t⌋₊

private lemma CharacterPartialSummation_characterScale_nonneg {q : ℕ} (hq : 1 < q) :
    0 ≤ 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  exact mul_nonneg
    (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
    (Real.log_pos (by exact_mod_cast hq)).le

private lemma CharacterPartialSummation_hasDerivAt_complexOfReal_inv {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ ((u : ℂ)⁻¹))
      (-((t : ℂ) ^ 2)⁻¹) t := by
  have hcomplex : HasDerivAt (fun z : ℂ ↦ z⁻¹)
      (-((t : ℂ) ^ 2)⁻¹) (t : ℂ) :=
    hasDerivAt_inv (by exact_mod_cast ht)
  exact hcomplex.comp_ofReal

private lemma CharacterPartialSummation_integrableOn_deriv_complexOfReal_inv
    {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹))) (Icc a b) := by
  let g : ℝ → ℂ := fun t ↦ -((t : ℂ) ^ 2)⁻¹
  have hgContinuous : ContinuousOn g (Icc a b) := by
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · exact Complex.continuous_ofReal.continuousOn.pow 2
    · intro t ht
      exact pow_ne_zero 2 (by exact_mod_cast (ha.trans_le ht.1).ne')
  apply hgContinuous.integrableOn_Icc.congr_fun _ measurableSet_Icc
  intro t ht
  exact (CharacterPartialSummation_hasDerivAt_complexOfReal_inv (ha.trans_le ht.1).ne').deriv.symm

private lemma CharacterPartialSummation_integral_Ioc_inv_sq
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t : ℝ in Ioc a b, (t ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
  have hdiff : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ (fun u : ℝ ↦ u⁻¹) t := by
    intro t ht
    apply differentiableAt_inv
    have ht' : t ∈ Icc a b := by
      simpa [Set.uIcc_of_le hab] using ht
    exact (ha.trans_le ht'.1).ne'
  have hint : IntervalIntegrable
      (deriv (fun u : ℝ ↦ u⁻¹)) volume a b := by
    rw [show deriv (fun u : ℝ ↦ u⁻¹) = fun u ↦ -(u ^ 2)⁻¹ by
      funext u
      exact deriv_inv]
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · exact continuousOn_id.pow 2
    · intro t ht
      have ht' : t ∈ Icc a b := by
        simpa [Set.uIcc_of_le hab] using ht
      exact pow_ne_zero 2 (ha.trans_le ht'.1).ne'
  have hfund := intervalIntegral.integral_deriv_eq_sub hdiff hint
  rw [intervalIntegral.integral_of_le hab] at hfund
  rw [show deriv (fun u : ℝ ↦ u⁻¹) = fun u ↦ -(u ^ 2)⁻¹ by
    funext u
    exact deriv_inv] at hfund
  rw [integral_neg] at hfund
  linarith

theorem norm_dirichletCharacterReciprocalIntervalSum_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (x y : ℕ) (hx : 0 < x) :
    ‖∑ n ∈ Finset.Ioc x y,
      chi (n : ZMod q) / (n : ℂ)‖ ≤
      4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) / (x : ℝ) := by
  by_cases hxy : x ≤ y
  · have hxReal : 0 < (x : ℝ) := by exact_mod_cast hx
    have hxyReal : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hxy
    have hyReal : 0 < (y : ℝ) := hxReal.trans_le hxyReal
    let C : ℝ := 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
    have hfDiff : ∀ t ∈ Icc (x : ℝ) y,
        DifferentiableAt ℝ (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t := by
      intro t ht
      exact (CharacterPartialSummation_hasDerivAt_complexOfReal_inv
        (hxReal.trans_le ht.1).ne').differentiableAt
    have hfInt : IntegrableOn
        (deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹))) (Icc (x : ℝ) y) :=
      CharacterPartialSummation_integrableOn_deriv_complexOfReal_inv hxReal
    have habel := sum_mul_eq_sub_sub_integral_mul'
      (f := fun t : ℝ ↦ ((t : ℂ)⁻¹))
      (c := fun n : ℕ ↦ chi (n : ZMod q)) hxy hfDiff hfInt
    have hrepresentation :
        (∑ n ∈ Finset.Ioc x y,
          chi (n : ZMod q) / (n : ℂ)) =
          ((y : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (y : ℝ) -
            (x : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (x : ℝ)) -
            ∫ t in Ioc (x : ℝ) y,
              deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
                CharacterPartialSummation_characterCumulative chi t := by
      simpa [CharacterPartialSummation_characterCumulative, div_eq_mul_inv, mul_comm] using habel
    have hActual : IntegrableOn
        (fun t : ℝ ↦ deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
          CharacterPartialSummation_characterCumulative chi t) (Ioc (x : ℝ) y) := by
      apply (integrableOn_mul_sum_Icc
        (fun n : ℕ ↦ chi (n : ZMod q)) hxReal.le hfInt).mono_set
      exact Ioc_subset_Icc_self
    have hReciprocalContinuous : ContinuousOn
        (fun t : ℝ ↦ (t ^ 2)⁻¹) (Icc (x : ℝ) y) := by
      apply ContinuousOn.inv₀
      · exact continuousOn_id.pow 2
      · intro t ht
        exact pow_ne_zero 2 (hxReal.trans_le ht.1).ne'
    have hMajorant : IntegrableOn
        (fun t : ℝ ↦ C * (t ^ 2)⁻¹) (Ioc (x : ℝ) y) :=
      (continuousOn_const.mul hReciprocalContinuous).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
    have hPoint : ∀ t ∈ Ioc (x : ℝ) y,
        ‖deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
            CharacterPartialSummation_characterCumulative chi t‖ ≤ C * (t ^ 2)⁻¹ := by
      intro t ht
      have htPos : 0 < t := hxReal.trans ht.1
      rw [(CharacterPartialSummation_hasDerivAt_complexOfReal_inv htPos.ne').deriv, norm_mul]
      have hderivNorm : ‖-((t : ℂ) ^ 2)⁻¹‖ = (t ^ 2)⁻¹ := by
        rw [norm_neg, norm_inv, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos htPos]
      rw [hderivNorm]
      calc
        (t ^ 2)⁻¹ * ‖CharacterPartialSummation_characterCumulative chi t‖ =
            ‖CharacterPartialSummation_characterCumulative chi t‖ * (t ^ 2)⁻¹ := mul_comm _ _
        _ ≤ C * (t ^ 2)⁻¹ := mul_le_mul_of_nonneg_right
          (by simpa [C] using
            CharacterPartialSummation_norm_characterCumulative_le hq chi hchi t)
          (inv_nonneg.mpr (sq_nonneg t))
    have hIntegral :
        ‖∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
              CharacterPartialSummation_characterCumulative chi t‖ ≤
          C * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) := by
      calc
        ‖∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
              CharacterPartialSummation_characterCumulative chi t‖ ≤
            ∫ t in Ioc (x : ℝ) y,
              ‖deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
                CharacterPartialSummation_characterCumulative chi t‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ t in Ioc (x : ℝ) y, C * (t ^ 2)⁻¹ := by
          apply setIntegral_mono_ae_restrict hActual.norm hMajorant
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact hPoint t ht
        _ = C * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) := by
          rw [integral_const_mul, CharacterPartialSummation_integral_Ioc_inv_sq hxReal hxyReal]
    have hUpper :
        ‖(y : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (y : ℝ)‖ ≤
          C * (y : ℝ)⁻¹ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      calc
        (y : ℝ)⁻¹ * ‖CharacterPartialSummation_characterCumulative chi (y : ℝ)‖ ≤
            (y : ℝ)⁻¹ * C := mul_le_mul_of_nonneg_left
          (by simpa [C] using
            CharacterPartialSummation_norm_characterCumulative_le hq chi hchi (y : ℝ))
          (inv_nonneg.mpr hyReal.le)
        _ = C * (y : ℝ)⁻¹ := mul_comm _ _
    have hLower :
        ‖(x : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (x : ℝ)‖ ≤
          C * (x : ℝ)⁻¹ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      calc
        (x : ℝ)⁻¹ * ‖CharacterPartialSummation_characterCumulative chi (x : ℝ)‖ ≤
            (x : ℝ)⁻¹ * C := mul_le_mul_of_nonneg_left
          (by simpa [C] using
            CharacterPartialSummation_norm_characterCumulative_le hq chi hchi (x : ℝ))
          (inv_nonneg.mpr hxReal.le)
        _ = C * (x : ℝ)⁻¹ := mul_comm _ _
    rw [hrepresentation]
    calc
      ‖((y : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (y : ℝ) -
          (x : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (x : ℝ)) -
          ∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
              CharacterPartialSummation_characterCumulative chi t‖ ≤
          (‖(y : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (y : ℝ)‖ +
            ‖(x : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (x : ℝ)‖) +
            ‖∫ t in Ioc (x : ℝ) y,
              deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
                CharacterPartialSummation_characterCumulative chi t‖ := by
        exact (norm_sub_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (C * (y : ℝ)⁻¹ + C * (x : ℝ)⁻¹) +
          C * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) :=
        add_le_add (add_le_add hUpper hLower) hIntegral
      _ = 4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) / (x : ℝ) := by
        dsimp [C]
        ring
  · have hyx : y ≤ x := Nat.le_of_not_ge hxy
    rw [Finset.Ioc_eq_empty_of_le hyx, Finset.sum_empty, norm_zero]
    have hNumerator :
        0 ≤ 4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      nlinarith [CharacterPartialSummation_characterScale_nonneg hq]
    exact div_nonneg hNumerator (by positivity)

end BoundedGaps.Maynard

end

/-! ## Abel continuation and the ordered value at one

Source module `BoundedGaps.BombieriVinogradov.Analytic.NonprincipalLFunctionAbel`. -/

noncomputable section

open Asymptotics Complex Filter MeasureTheory Set

open scoped BigOperators Real Topology

namespace BoundedGaps.Maynard

theorem LFunction_eq_abelIntegral_of_ne_one
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) (hs : 0 < s.re) :
    DirichletCharacter.LFunction chi s =
      s * ∫ y in Set.Ioi (1 : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1)) := by
  simpa [dirichletCharacterIntervalSum] using
    LFunction_eq_abelIntegral_of_prefixBound chi hchi
      (2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ))
      (fun n ↦ by
        simpa [dirichletCharacterIntervalSum] using
          norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
            hq chi hchi n)
      s hs

private theorem NonprincipalLFunctionAbel_tendsto_reciprocalPrefix_of_abelIntegral
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖dirichletCharacterIntervalSum 1 n q chi‖ ≤ C)
    (habel : DirichletCharacter.LFunction chi (1 : ℂ) =
      (1 : ℂ) * ∫ y in Ioi (1 : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-((1 : ℂ) + 1))) :
    Tendsto (fun x : ℕ ↦ ∑ n ∈ Finset.Icc 1 x,
      chi (n : ZMod q) / (n : ℂ)) atTop
      (𝓝 (DirichletCharacter.LFunction chi (1 : ℂ))) := by
  let c : ℕ → ℂ := fun n ↦ chi (n : ZMod q)
  let f : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-(1 : ℂ))
  have hc0 : c 0 = 0 := by
    simpa [c] using chi.map_zero' (Nat.ne_of_gt hq)
  have hCumulative (n : ℕ) :
      ∑ k ∈ Finset.Icc 0 n, c k =
        dirichletCharacterIntervalSum 1 n q chi := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, hc0,
      zero_add, ← Finset.Icc_add_one_left_eq_Ioc 0 n]
    norm_num [c, dirichletCharacterIntervalSum]
  have hfDiff : ∀ t ∈ Ici (1 : ℝ), DifferentiableAt ℝ f t := by
    intro t ht
    exact differentiableAt_id.ofReal_cpow_const
      (zero_lt_one.trans_le ht).ne' (by norm_num)
  have hfInt : LocallyIntegrableOn (deriv f) (Ici (1 : ℝ)) := by
    exact (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one
        (by norm_num))).locallyIntegrableOn
  have hEndpoint : Tendsto
      (fun n : ℕ ↦ f n * ∑ k ∈ Finset.Icc 0 n, c k) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun n : ℕ ↦ C / (n : ℝ))
    · exact Eventually.of_forall fun n ↦ norm_nonneg _
    · filter_upwards [eventually_gt_atTop 0] with n hn
      rw [hCumulative, norm_mul]
      have hfn : ‖f n‖ = (n : ℝ)⁻¹ := by
        change ‖(n : ℂ) ^ (-(1 : ℂ))‖ = (n : ℝ)⁻¹
        rw [Complex.cpow_neg_one, norm_inv, Complex.norm_natCast]
      rw [hfn]
      calc
        (n : ℝ)⁻¹ *
            ‖dirichletCharacterIntervalSum 1 n q chi‖ ≤
            (n : ℝ)⁻¹ * C :=
          mul_le_mul_of_nonneg_left (hprefix n)
            (inv_nonneg.mpr (by positivity))
        _ = C / (n : ℝ) := by ring
    · simpa [div_eq_mul_inv] using
        ((tendsto_const_nhds (x := C)).mul
          (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hDom :
      (fun t ↦ deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =O[atTop]
        (fun t : ℝ ↦ t ^ (-2 : ℝ)) := by
    refine isBigO_iff.mpr ⟨C, ?_⟩
    filter_upwards [eventually_gt_atTop 1] with t ht
    rw [norm_mul, hCumulative]
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hderiv : ‖deriv f t‖ = t ^ (-2 : ℝ) := by
      rw [show deriv f t =
          deriv (fun u : ℝ ↦ (u : ℂ) ^ (-(1 : ℂ))) t by rfl,
        deriv_ofReal_cpow_const ht0.ne' (by norm_num), norm_mul,
        norm_neg, norm_one, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      norm_num
    rw [hderiv]
    have hgNonneg : 0 ≤ t ^ (-2 : ℝ) := Real.rpow_nonneg ht0.le _
    calc
      t ^ (-2 : ℝ) *
          ‖dirichletCharacterIntervalSum 1 ⌊t⌋₊ q chi‖ ≤
          t ^ (-2 : ℝ) * C :=
        mul_le_mul_of_nonneg_left (hprefix _) hgNonneg
      _ = C * ‖t ^ (-2 : ℝ)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hgNonneg]
        ring
  have hconv := tendsto_sum_mul_atTop_nhds_one_sub_integral₀
    (f := f) (l := 0) c hc0 hfDiff hfInt hEndpoint hDom
      (integrableAtFilter_rpow_atTop_iff.mpr (by norm_num))
  have hleft (n : ℕ) :
      (∑ k ∈ Finset.Icc 0 n, f k * c k) =
        ∑ k ∈ Finset.Icc 1 n,
          chi (k : ZMod q) / (k : ℂ) := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, hc0,
      mul_zero, zero_add, ← Finset.Icc_add_one_left_eq_Ioc 0 n]
    norm_num [f, c, Complex.cpow_neg_one, div_eq_mul_inv, mul_comm]
  have hright :
      0 - ∫ t in Ioi (1 : ℝ),
          deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k =
        DirichletCharacter.LFunction chi (1 : ℂ) := by
    rw [habel, one_mul, zero_sub, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change -(deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) = _
    rw [show deriv f t =
        deriv (fun u : ℝ ↦ (u : ℂ) ^ (-(1 : ℂ))) t by rfl,
      deriv_ofReal_cpow_const (zero_lt_one.trans ht).ne' (by norm_num),
      hCumulative]
    ring_nf
  rw [← hright]
  exact hconv.congr' (Eventually.of_forall hleft)

theorem tendsto_dirichletCharacterReciprocalPrefix_atTop
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    Tendsto
      (fun x : ℕ ↦ ∑ n ∈ Finset.Icc 1 x,
        chi (n : ZMod q) / (n : ℂ))
      atTop (𝓝 (DirichletCharacter.LFunction chi (1 : ℂ))) := by
  let C : ℝ := 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
  apply NonprincipalLFunctionAbel_tendsto_reciprocalPrefix_of_abelIntegral hq chi C
  · intro n
    simpa [C] using
      norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
        hq chi hchi n
  · exact LFunction_eq_abelIntegral_of_ne_one
      hq chi hchi (1 : ℂ) (by norm_num)

theorem norm_LFunction_one_sub_dirichletCharacterReciprocalPrefix_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (x : ℕ) (hx : 0 < x) :
    ‖DirichletCharacter.LFunction chi (1 : ℂ) -
        ∑ n ∈ Finset.Icc 1 x,
          chi (n : ZMod q) / (n : ℂ)‖ ≤
      4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) / (x : ℝ) := by
  let P : ℕ → ℂ := fun y ↦ ∑ n ∈ Finset.Icc 1 y,
    chi (n : ZMod q) / (n : ℂ)
  have htail {y : ℕ} (hxy : x ≤ y) :
      P y - P x = ∑ n ∈ Finset.Ioc x y,
        chi (n : ZMod q) / (n : ℂ) := by
    have hunion : Finset.Icc 1 x ∪ Finset.Ioc x y =
        Finset.Icc 1 y := by
      ext n
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      constructor
      · rintro (hn | hn) <;> omega
      · intro hn
        by_cases hnx : n ≤ x
        · exact Or.inl ⟨hn.1, hnx⟩
        · exact Or.inr ⟨lt_of_not_ge hnx, hn.2⟩
    have hdis : Disjoint (Finset.Icc 1 x) (Finset.Ioc x y) := by
      rw [Finset.disjoint_left]
      intro n hncc hnoc
      simp only [Finset.mem_Icc] at hncc
      simp only [Finset.mem_Ioc] at hnoc
      omega
    change (∑ n ∈ Finset.Icc 1 y,
        chi (n : ZMod q) / (n : ℂ)) -
      (∑ n ∈ Finset.Icc 1 x,
        chi (n : ZMod q) / (n : ℂ)) = _
    rw [← hunion, Finset.sum_union hdis]
    ring
  have hconv :=
    tendsto_dirichletCharacterReciprocalPrefix_atTop hq chi hchi
  have hlim : Tendsto (fun y ↦ ‖P y - P x‖) atTop
      (𝓝 ‖DirichletCharacter.LFunction chi (1 : ℂ) - P x‖) := by
    exact (hconv.sub_const (P x)).norm
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop x] with y hxy
  rw [htail hxy]
  exact norm_dirichletCharacterReciprocalIntervalSum_le
    hq chi hchi x y hx

end BoundedGaps.Maynard

end

/-! ## Approximating the real L-value by a reciprocal prefix

Source module `ErdosProblems.Erdos1141.CharacterLValueApproximation`. -/

noncomputable section

namespace Pollack17

open Filter

open scoped BigOperators

open BoundedGaps.Maynard

theorem sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, f i) = ∑ i ∈ Finset.range n, f (1 + i) := by
  have heq : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by ext i; simp
  rw [heq, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm]

theorem sum_range_succ_eq_zero_add_Icc (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), f i) = f 0 + ∑ i ∈ Finset.Icc 1 n, f i := by
  rw [sum_Icc_one_eq_sum_range, Finset.sum_range_succ']
  simp only [add_comm]

theorem eventually_quadratic_prefix_bound {d : ℝ} (hd : 1 / 4 < d) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ (χ : DirichletCharacter ℂ m), χ.IsQuadratic → χ ≠ 1 →
        ∀ n : ℕ, (m : ℝ) ^ d ≤ n →
          |∑ i ∈ Finset.Icc 1 n, (χ (i : ℕ)).re| ≤ (n : ℝ) * (m : ℝ) ^ (-σ) := by
  obtain ⟨σ, hσ, h⟩ := Burgess.eventually_quadratic_burgess hd
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [h] with m hm
  intro χ hχ hχ1 n hn
  rw [sum_Icc_one_eq_sum_range]
  exact hm χ hχ hχ1 1 n hn

theorem reciprocal_prefix_re {m : ℕ} (χ : DirichletCharacter ℂ m) (y : ℕ) :
    (∑ i ∈ Finset.Icc 1 y, χ (i : ℕ) / (i : ℂ)).re =
      ∑ i ∈ Finset.Icc 1 y, (χ (i : ℕ)).re / (i : ℝ) := by
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.div_natCast_re]

theorem abs_reciprocal_prefix_sub_LFunction_re_le {m : ℕ} [NeZero m]
    (hm : 1 < m) (χ : DirichletCharacter ℂ m) (hχ1 : χ ≠ 1)
    {x y : ℕ} (hx : 0 < x) (hxy : x ≤ y) {b : ℝ} (hb : 0 ≤ b)
    (hprefix : ∀ n : ℕ, x ≤ n → n ≤ y →
      |∑ i ∈ Finset.Icc 1 n, (χ (i : ℕ)).re| ≤ (n : ℝ) * b) :
    |(∑ i ∈ Finset.Icc 1 x, (χ (i : ℕ)).re / (i : ℝ)) -
        (DirichletCharacter.LFunction χ (1 : ℂ)).re| ≤
      b * (3 + Real.log (y : ℝ)) +
        4 * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / (y : ℝ) := by
  let P : ℕ → ℝ := fun n => ∑ i ∈ Finset.Icc 1 n, (χ (i : ℕ)).re / (i : ℝ)
  have hzero : (χ ((0 : ℕ) : ZMod m)).re = 0 := by
    rw [Nat.cast_zero, χ.map_zero' (by omega), Complex.zero_re]
  have hfinite := abs_reciprocal_interval_le (fun i => (χ (i : ℕ)).re) hx hxy hb
    (fun n hn hny => by
      rw [sum_range_succ_eq_zero_add_Icc, hzero, zero_add]
      exact hprefix n hn hny)
  have hdiff : P y - P x = ∑ i ∈ Finset.Ioc x y, (χ (i : ℕ)).re / (i : ℝ) := by
    dsimp only [P]
    rw [show Finset.Icc 1 y = Finset.Ioc 0 y by ext i; simp; omega,
      show Finset.Icc 1 x = Finset.Ioc 0 x by ext i; simp; omega,
      ← Finset.sum_Ioc_consecutive (fun i => (χ (i : ℕ)).re / (i : ℝ)) (Nat.zero_le x) hxy]
    ring
  have htail := (Complex.abs_re_le_norm (DirichletCharacter.LFunction χ (1 : ℂ) -
      ∑ i ∈ Finset.Icc 1 y, χ (i : ℕ) / (i : ℂ))).trans
    (norm_LFunction_one_sub_dirichletCharacterReciprocalPrefix_le hm χ hχ1 y (hx.trans_le hxy))
  rw [Complex.sub_re, reciprocal_prefix_re] at htail
  change |P x - (DirichletCharacter.LFunction χ 1).re| ≤ _
  have htri := abs_sub_le (P x) (P y) (DirichletCharacter.LFunction χ 1).re
  rw [abs_sub_comm (P x) (P y), hdiff] at htri
  have htail' : |P y - (DirichletCharacter.LFunction χ 1).re| ≤
      4 * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / (y : ℝ) := by
    rw [abs_sub_comm]
    exact htail
  exact htri.trans (add_le_add hfinite htail')

end Pollack17

end

/-! ## Finite comparison of the divisor sum with its L-value main term

Source module `ErdosProblems.Erdos1141.DivisorLValueComparison`. -/

noncomputable section

namespace Pollack17

open scoped BigOperators

theorem divisorCoefficient_eq_sum {m : ℕ} (χ : DirichletCharacter ℂ m) (n : ℕ) :
    divisorCoefficient χ n = ∑ d ∈ n.divisors, (χ (d : ℕ)).re := by
  unfold divisorCoefficient
  have heq : χ.zetaMul n = ∑ d ∈ n.divisors, χ (d : ℕ) := by
    change (ArithmeticFunction.zeta * toArithmeticFunction (χ ·)) n = _
    rw [ArithmeticFunction.coe_zeta_mul_apply]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [toArithmeticFunction, ArithmeticFunction.coe_mk,
      if_neg (Nat.pos_of_mem_divisors hd).ne']
  rw [heq, Complex.re_sum]

theorem abs_divisor_sum_sub_LFunction_main_le {m X Y R : ℕ} [NeZero m]
    (hm : 1 < m) (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic) (hχ1 : χ ≠ 1)
    (hY : 0 < Y) (hYX : Y ≤ X) (hYR : Y ≤ R) {b : ℝ} (hb : 0 ≤ b)
    (hprefix : ∀ n : ℕ, Y ≤ n →
      |∑ d ∈ Finset.Icc 1 n, (χ (d : ℕ)).re| ≤ (n : ℝ) * b) :
    |(∑ n ∈ Finset.Icc 1 X, divisorCoefficient χ n) -
        (X : ℝ) * (DirichletCharacter.LFunction χ 1).re| ≤
      (Y : ℝ) + (X : ℝ) * b * (5 + 2 * Real.log (X : ℝ) + Real.log (R : ℝ)) +
        4 * (X : ℝ) * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / (R : ℝ) := by
  have hf (n : ℕ) : |(χ (n : ℕ)).re| ≤ 1 := by
    rcases hχ (n : ℕ) with h | h | h <;> rw [h] <;> norm_num
  have hhyp := abs_divisor_sum_sub_truncated_main_le (fun n => (χ (n : ℕ)).re)
    hf hYX hb hprefix
  have htail := abs_reciprocal_prefix_sub_LFunction_re_le hm χ hχ1 hY hYR hb
    (fun n hn _ => hprefix n hn)
  simp_rw [← divisorCoefficient_eq_sum χ] at hhyp
  let P : ℝ := ∑ d ∈ Finset.Icc 1 Y, (χ (d : ℕ)).re / (d : ℝ)
  let L : ℝ := (DirichletCharacter.LFunction χ 1).re
  let S : ℝ := ∑ n ∈ Finset.Icc 1 X, divisorCoefficient χ n
  have htri := abs_sub_le S ((X : ℝ) * P) ((X : ℝ) * L)
  have hscaled : |(X : ℝ) * P - (X : ℝ) * L| ≤
      (X : ℝ) * (b * (3 + Real.log (R : ℝ)) +
        4 * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / (R : ℝ)) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg X)]
    exact mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg X)
  change |S - (X : ℝ) * L| ≤ _
  calc
    _ ≤ ((Y : ℝ) + 2 * (X : ℝ) * b * (1 + Real.log (X : ℝ))) +
        (X : ℝ) * (b * (3 + Real.log (R : ℝ)) +
          4 * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / (R : ℝ)) :=
      htri.trans (add_le_add hhyp hscaled)
    _ = _ := by ring

end Pollack17

end

/-! ## Absorbing the three hyperbola error terms

Source module `ErdosProblems.Erdos1141.DivisorErrorScales`. -/

noncomputable section

namespace Pollack17

open Filter

theorem eventually_three_power_errors_le {c a b d C D E : ℝ}
    (ha : a < c) (hb : b < c) (hd : d < c) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ m : ℕ in atTop,
      C * (m : ℝ) ^ a + D * (m : ℝ) ^ b + E * (m : ℝ) ^ d ≤ (m : ℝ) ^ (c - τ) := by
  let τ : ℝ := min (c - a) (min (c - b) (c - d)) / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτa : a < c - τ := by
    have h := min_le_left (c - a) (min (c - b) (c - d))
    dsimp [τ] at hτ ⊢
    linarith
  have hτb : b < c - τ := by
    have h := (min_le_right (c - a) (min (c - b) (c - d))).trans (min_le_left _ _)
    dsimp [τ] at hτ ⊢
    linarith
  have hτd : d < c - τ := by
    have h := (min_le_right (c - a) (min (c - b) (c - d))).trans (min_le_right _ _)
    dsimp [τ] at hτ ⊢
    linarith
  refine ⟨τ, hτ, ?_⟩
  filter_upwards [Burgess.eventually_const_mul_rpow_le (C := C) (d := 1 / 3) (by norm_num) hτa,
    Burgess.eventually_const_mul_rpow_le (C := D) (d := 1 / 3) (by norm_num) hτb,
    Burgess.eventually_const_mul_rpow_le (C := E) (d := 1 / 3) (by norm_num) hτd]
    with m hm₁ hm₂ hm₃
  linarith only [hm₁, hm₂, hm₃]

theorem eventually_divisor_error_le {c a σ : ℝ} (hc : 0 < c) (ha : a < c) (hσ : 0 < σ) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ m : ℕ in atTop,
      2 * (m : ℝ) ^ a + (7 + 2 * c) * (m : ℝ) ^ (c - σ) * (1 + Real.log (m : ℝ)) +
        4 * (m : ℝ) ^ (c - 3 / 2) * (1 + Real.log (m : ℝ)) ≤ (m : ℝ) ^ (c - τ) := by
  let κ : ℝ := min σ 1 / 4
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκσ : κ < σ := by
    have h := min_le_left σ 1
    dsimp [κ] at hκ ⊢
    linarith
  have hκ1 : κ < 3 / 2 := by
    have h := min_le_right σ 1
    dsimp [κ]
    linarith
  obtain ⟨τ, hτ, h⟩ := eventually_three_power_errors_le
    (C := 2) (D := 7 + 2 * c) (E := 4) ha
    (show c - σ + κ < c by linarith) (show c - 3 / 2 + κ < c by linarith)
  refine ⟨τ, hτ, ?_⟩
  filter_upwards [h, Burgess.eventually_one_add_log_le_rpow hκ, eventually_ge_atTop 1]
    with m hm hlog hm1
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm1
  have hfirst : (7 + 2 * c) * (m : ℝ) ^ (c - σ) * (1 + Real.log (m : ℝ)) ≤
      (7 + 2 * c) * (m : ℝ) ^ (c - σ + κ) := by
    rw [Real.rpow_add hm0, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  have hsecond : 4 * (m : ℝ) ^ (c - 3 / 2) * (1 + Real.log (m : ℝ)) ≤
      4 * (m : ℝ) ^ (c - 3 / 2 + κ) := by
    rw [Real.rpow_add hm0, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  exact (add_le_add (add_le_add le_rfl hfirst) hsecond).trans hm

end Pollack17

end

/-! ## The divisor-sum asymptotic above the quarter-power scale

Source module `ErdosProblems.Erdos1141.DivisorComparisonAsymptotics`. -/

noncomputable section

namespace Pollack17

open Filter

open scoped BigOperators

theorem divisor_comparison_error_le_scales {m X Y : ℕ} (hm : 1 ≤ m) (hX : 0 < X)
    {c a σ : ℝ} (hc : 0 < c) (hXu : (X : ℝ) ≤ (m : ℝ) ^ c)
    (hYu : (Y : ℝ) ≤ 2 * (m : ℝ) ^ a) :
    (Y : ℝ) + (X : ℝ) * (m : ℝ) ^ (-σ) *
        (5 + 2 * Real.log (X : ℝ) + Real.log ((m ^ 2 : ℕ) : ℝ)) +
      4 * (X : ℝ) * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / ((m ^ 2 : ℕ) : ℝ) ≤
    2 * (m : ℝ) ^ a + (7 + 2 * c) * (m : ℝ) ^ (c - σ) * (1 + Real.log (m : ℝ)) +
      4 * (m : ℝ) ^ (c - 3 / 2) * (1 + Real.log (m : ℝ)) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hXm : 0 < (X : ℝ) := by exact_mod_cast hX
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hlogX : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  have hlogXu : Real.log (X : ℝ) ≤ c * Real.log (m : ℝ) := by
    have h := Real.log_le_log hXm hXu
    simpa only [Real.log_rpow hmR] using h
  have hlogR : Real.log ((m ^ 2 : ℕ) : ℝ) = 2 * Real.log (m : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hfactor : 5 + 2 * Real.log (X : ℝ) + Real.log ((m ^ 2 : ℕ) : ℝ) ≤
      (7 + 2 * c) * (1 + Real.log (m : ℝ)) := by
    rw [hlogR]
    nlinarith only [hlogXu, hlogm, hc]
  have hfirst : (X : ℝ) * (m : ℝ) ^ (-σ) *
        (5 + 2 * Real.log (X : ℝ) + Real.log ((m ^ 2 : ℕ) : ℝ)) ≤
      (7 + 2 * c) * (m : ℝ) ^ (c - σ) * (1 + Real.log (m : ℝ)) := by
    have hxpow : (X : ℝ) * (m : ℝ) ^ (-σ) ≤ (m : ℝ) ^ (c - σ) := by
      rw [sub_eq_add_neg, Real.rpow_add hmR]
      exact mul_le_mul_of_nonneg_right hXu (Real.rpow_nonneg hmR.le _)
    have hfac0 : 0 ≤ 5 + 2 * Real.log (X : ℝ) + Real.log ((m ^ 2 : ℕ) : ℝ) := by
      rw [hlogR]
      positivity
    calc
      _ ≤ (m : ℝ) ^ (c - σ) * ((7 + 2 * c) * (1 + Real.log (m : ℝ))) :=
        mul_le_mul hxpow hfactor hfac0 (Real.rpow_nonneg hmR.le _)
      _ = _ := by ring
  have hratio : (m : ℝ) ^ c * Real.sqrt (m : ℝ) / ((m ^ 2 : ℕ) : ℝ) =
      (m : ℝ) ^ (c - 3 / 2) := by
    rw [Nat.cast_pow, Real.sqrt_eq_rpow, ← Real.rpow_add hmR,
      ← Real.rpow_natCast, ← Real.rpow_sub hmR]
    congr 1
    ring
  have hsecond : 4 * (X : ℝ) * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / ((m ^ 2 : ℕ) : ℝ) ≤
      4 * (m : ℝ) ^ (c - 3 / 2) * (1 + Real.log (m : ℝ)) := by
    calc
      _ ≤ 4 * (m : ℝ) ^ c * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / ((m ^ 2 : ℕ) : ℝ) := by
        gcongr
      _ = 4 * (m : ℝ) ^ (c - 3 / 2) * Real.log (m : ℝ) := by
        rw [← hratio]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  exact add_le_add (add_le_add hYu hfirst) hsecond

theorem eventually_divisor_sum_asymptotic {c : ℝ} (hc : 1 / 4 < c) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ [NeZero m] (χ : DirichletCharacter ℂ m), χ.IsQuadratic → χ ≠ 1 →
        |(∑ n ∈ Finset.Icc 1 ⌊(m : ℝ) ^ c⌋₊, divisorCoefficient χ n) -
          (⌊(m : ℝ) ^ c⌋₊ : ℝ) * (DirichletCharacter.LFunction χ 1).re| ≤ (m : ℝ) ^ (c - τ) := by
  let a : ℝ := min ((c + 1 / 4) / 2) (1 / 2)
  have ha : 1 / 4 < a := by dsimp [a]; exact lt_min (by linarith) (by norm_num)
  have hac : a < c := (min_le_left _ _).trans_lt (by linarith)
  have ha2 : a < 2 := (min_le_right _ _).trans_lt (by norm_num)
  have hc0 : 0 < c := by linarith
  have ha0 : 0 < a := by linarith
  obtain ⟨σ, hσ, hprefix⟩ := eventually_quadratic_prefix_bound ha
  obtain ⟨τ, hτ, herror⟩ := eventually_divisor_error_le hc0 hac hσ
  have hYX := Burgess.eventually_const_mul_rpow_le (C := 2) (d := 1 / 2) (by norm_num) hac
  have hYR := Burgess.eventually_const_mul_rpow_le (C := 2) (d := 1) (by norm_num) ha2
  refine ⟨τ, hτ, ?_⟩
  filter_upwards [hprefix, herror, hYX, hYR, Burgess.eventually_floor_rpow_bounds hc0,
    eventually_ge_atTop 2] with m hpref herr hYX hYR hfloor hm
  intro _ χ hχ hχ1
  have hm0 : 0 < m := by omega
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  let X := ⌊(m : ℝ) ^ c⌋₊
  let Y := ⌈(m : ℝ) ^ a⌉₊
  have hceil := Burgess.ceil_rpow_bounds ha0.le (show 1 ≤ m by omega)
  have hXpos : 0 < X := by
    have h : (0 : ℝ) < X := lt_of_lt_of_le (by positivity) hfloor.1
    exact_mod_cast h
  have hYpos : 0 < Y := by
    have h : (0 : ℝ) < Y := lt_of_lt_of_le (Real.rpow_pos_of_pos hmR a) hceil.1
    exact_mod_cast h
  have hYX' : Y ≤ X := by
    have hmid : 2 * (m : ℝ) ^ a ≤ (m : ℝ) ^ c / 2 := by
      nlinarith only [hYX]
    have h : (Y : ℝ) ≤ X := hceil.2.trans (hmid.trans hfloor.1)
    exact_mod_cast h
  have hYR' : Y ≤ m ^ 2 := by
    have h : (Y : ℝ) ≤ ((m ^ 2 : ℕ) : ℝ) := by
      have h := hceil.2.trans hYR
      simpa only [one_mul, Real.rpow_two, Nat.cast_pow] using h
    exact_mod_cast h
  have hb : 0 ≤ (m : ℝ) ^ (-σ) := Real.rpow_nonneg hmR.le _
  have hbound (n : ℕ) (hn : Y ≤ n) :
      |∑ d ∈ Finset.Icc 1 n, (χ (d : ℕ)).re| ≤ (n : ℝ) * (m : ℝ) ^ (-σ) :=
    hpref χ hχ hχ1 n (hceil.1.trans (by exact_mod_cast hn))
  have hcomp := abs_divisor_sum_sub_LFunction_main_le
    (by omega) χ hχ hχ1 hYpos hYX' hYR' hb hbound
  exact (hcomp.trans (divisor_comparison_error_le_scales
    (by omega) hXpos hc0 hfloor.2 hceil.2)).trans herr

end Pollack17

end

/-! ## Absorbing a sparse Euler product into a small power

Source module `ErdosProblems.Erdos1141.SparseAsymptotics`. -/

noncomputable section

namespace Pollack17

open Filter

open scoped BigOperators

theorem eventually_const_mul_rpow_le {C d a b : ℝ} (hd : 0 < d) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a ≤ d * x ^ b := by
  have hlarge := (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually
    (eventually_ge_atTop (C / d))
  filter_upwards [hlarge, eventually_ge_atTop 1] with x hx hx1
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hratio : C ≤ d * x ^ (b - a) := by
    simpa only [mul_comm] using (div_le_iff₀ hd).mp hx
  calc
    C * x ^ a ≤ (d * x ^ (b - a)) * x ^ a :=
      mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hx0.le _)
    _ = d * x ^ b := by
      rw [mul_assoc, ← Real.rpow_add hx0]
      congr 2
      ring

end Pollack17

end

theorem OMA.solution : OMA.R_Erdos1141_erdos_1141_variants_pollack_1_3_R1.H1 := by
  intro exponent h
  exact Pollack17.eventually_divisor_sum_asymptotic h
