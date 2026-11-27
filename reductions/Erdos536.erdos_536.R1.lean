import FormalConjectures.ErdosProblems.«536»

/-!
# A discrete reduction of Erdős Problem 536

The balanced pair-product cube approach is due to S. Wang, *A Proposed Complete
Solution to Erdős Problem 536*, Sections 4–7. Here a finite count of reduced residue
blocks transfers an average vertex overlap to ordinary counting with explicit error.
-/

namespace OMA.R_Erdos536_erdos_536_R1

open Finset Filter
open scoped BigOperators

/-- Arbitrarily good coverage of the reduced-residue divisor law by balanced LCM cubes. -/
def H1 : Prop :=
  ∀ (h : ℕ) (η : ℝ), 0 < η →
    let W := Fin h → ZMod 3
    ∃ (Q : ℕ) (C : Finset (W → ℕ)) (mass : (W → ℕ) → ℝ), 0 < Q ∧
      (∀ c ∈ C, Function.Injective c ∧ (∀ w, c w ∣ Q) ∧
        (∀ w, c w ≤ 2 * c 0 ∧ c 0 ≤ 2 * c w) ∧
        (∀ x y z, x + y = z + z →
          (c x).lcm (c z) = (c z).lcm (c y) ∧
          (c z).lcm (c y) = (c x).lcm (c y))) ∧
      (∀ c ∈ C, 0 ≤ mass c) ∧ (∑ c ∈ C, mass c) ≤ 1 ∧
      1 - η ≤ ∑ d ∈ Q.divisors, min
        (((Icc 1 Q).filter (fun r => r.Coprime Q)).card / ((d : ℝ) * Q))
        (∑ c ∈ C, ∑ w : W, if c w = d then mass c / (Fintype.card W : ℝ) else 0)

/-- The addition-table density bound needed in the cube sections. -/
def H2 : Prop :=
  ∀ α : ℝ, 0 < α → ∃ h : ℕ, ∀ B : Finset (Fin h → ZMod 3),
    ThreeAPFree (B : Set (Fin h → ZMod 3)) →
      (B.card : ℝ) ≤ α * Fintype.card (Fin h → ZMod 3)

theorem roth_bound : H2 := by
  intro α hα
  let h := cornersTheoremBound α
  have hh : cornersTheoremBound α ≤ Fintype.card (Fin h → ZMod 3) := by
    simpa [Fintype.card_fun, ZMod.card, h] using
      (Nat.lt_pow_self (a := 3) (n := h) (by decide)).le
  exact ⟨h, fun B hfree =>
    le_of_not_ge fun hB => roth_3ap_theorem α hα hh B hB hfree⟩

/-- Counting in complete reduced-residue blocks gives an error independent of the cutoff N. -/
theorem discrete_transfer {W : Type*} [Fintype W] [DecidableEq W] [Zero W] [Nonempty W]
    {Q N : ℕ} (hQ : 0 < Q) {C : Finset (W → ℕ)} {mass : (W → ℕ) → ℝ}
    (hDvd : ∀ c ∈ C, ∀ w, c w ∣ Q)
    (hBalance : ∀ c ∈ C, ∀ w, c w ≤ 2 * c 0 ∧ c 0 ≤ 2 * c w)
    (hm : ∀ c ∈ C, 0 ≤ mass c) (hmass : ∑ c ∈ C, mass c ≤ 1)
    (α η : ℝ) (hα : 0 < α)
    (A : Finset ℕ) (hA : A ⊆ Icc 1 N)
    (hsection : ∀ c ∈ C, ∀ m : ℕ, 0 < m →
      ((univ.filter fun w => m * c w ∈ A).card : ℝ) ≤ α * Fintype.card W) :
    let Residues := fun Q : ℕ => (Icc 1 Q).filter fun r => r.Coprime Q
    let rootMass := fun Q d : ℕ => ((Residues Q).card : ℝ) / (↑d * ↑Q)
    let q := fun d : ℕ => ∑ c ∈ C, ∑ w : W,
      if c w = d then mass c / (Fintype.card W : ℝ) else 0
    1 - η ≤ ∑ d ∈ Q.divisors, min (rootMass Q d) (q d) →
    (A.card : ℝ) ≤ (η + 4 * α) * N + Q.divisors.card * (Residues Q).card := by
  classical
  intro Residues rootMass q hcover
  let atPoint (Q d : ℕ) (v : ℕ × ℕ) : ℕ := d * (Q * v.1 + v.2)
  let rect (Q d N : ℕ) : Finset (ℕ × ℕ) := range (N / (d * Q)) ×ˢ Residues Q
  let inside (Q d N : ℕ) (A : Finset ℕ) : Finset (ℕ × ℕ) :=
    (rect Q d N).filter fun v => atPoint Q d v ∈ A
  let missing (Q d N : ℕ) (A : Finset ℕ) : Finset (ℕ × ℕ) :=
    (rect Q d N).filter fun v => atPoint Q d v ∉ A
  let scale (Q d N : ℕ) (A : Finset ℕ) : ℝ :=
    ((d : ℝ) * Q / (Residues Q).card) * (inside Q d N A).card
  have residue_pos {Q : ℕ} (hQ : 0 < Q) : 0 < (Residues Q).card := by
    apply card_pos.mpr
    exact ⟨1, by simp [Residues, Nat.succ_le_of_lt hQ]⟩

  -- The divisor is recovered by a gcd, then the reduced residue and block are unique.
  have point_injective {Q : ℕ} (hQ : 0 < Q) :
      Set.InjOn (fun v : ℕ × (ℕ × ℕ) => atPoint Q v.1 v.2)
        {v | v.1 ∣ Q ∧ v.2.2 ∈ Residues Q} := by
    rintro ⟨d,k,r⟩ hd ⟨e,l,s⟩ he heq
    obtain ⟨hd, hr⟩ := hd
    obtain ⟨he, hs⟩ := he
    obtain ⟨hr, hrc⟩ := mem_filter.mp hr
    obtain ⟨hs, hsc⟩ := mem_filter.mp hs
    have hk : (Q * k + r).Coprime Q := by
      exact (Nat.coprime_mul_left_add_left r Q k).mpr hrc
    have hl : (Q * l + s).Coprime Q := by
      exact (Nat.coprime_mul_left_add_left s Q l).mpr hsc
    change d * (Q * k + r) = e * (Q * l + s) at heq
    have hde : d = e := by
      have hg := congrArg (fun t => t.gcd Q) heq
      simpa [Nat.mul_comm d, Nat.mul_comm e, Nat.gcd_mul_of_coprime_of_dvd hk hd,
        Nat.gcd_mul_of_coprime_of_dvd hl he] using hg
    subst e
    have hd0 := Nat.pos_of_dvd_of_pos hd hQ
    have hkl := Nat.eq_of_mul_eq_mul_left hd0 heq
    obtain ⟨hr₁, hr₂⟩ := mem_Icc.mp hr
    obtain ⟨hs₁, hs₂⟩ := mem_Icc.mp hs
    have hle {x y a b : ℕ} (hxy : x < y) (ha : a ≤ Q) (hb : 1 ≤ b) :
        Q * x + a < Q * y + b := by
      calc
        Q * x + a ≤ Q * (x + 1) := by rw [mul_add, mul_one]; omega
        _ ≤ Q * y := Nat.mul_le_mul_left _ (by omega)
        _ < Q * y + b := by omega
    have : k = l := by
      rcases lt_trichotomy k l with h | h | h
      · exact False.elim ((hle h hr₂ hs₁).ne hkl)
      · exact h
      · exact False.elim ((hle h hs₂ hr₁).ne hkl.symm)
    subst l
    congr 2
    omega

  have point_mem {Q N d : ℕ} (hQ : 0 < Q) (hd : d ∣ Q)
      {v : ℕ × ℕ} (hv : v ∈ rect Q d N) : atPoint Q d v ∈ Icc 1 N := by
    obtain ⟨hk, hr⟩ := mem_product.mp hv
    have hr := mem_Icc.mp (mem_filter.mp hr).1
    have hd0 := Nat.pos_of_dvd_of_pos hd hQ
    have hm : v.1 + 1 ≤ N / (d * Q) := mem_range.mp hk
    have hbound := (Nat.le_div_iff_mul_le (Nat.mul_pos hd0 hQ)).mp hm
    apply mem_Icc.mpr
    constructor
    · unfold atPoint
      have : 0 < Q * v.1 + v.2 := by omega
      exact Nat.mul_pos hd0 this
    · calc
        atPoint Q d v ≤ d * (Q * (v.1 + 1)) := by
          unfold atPoint
          apply Nat.mul_le_mul_left
          rw [mul_add, mul_one]
          omega
        _ ≤ N := by simpa only [mul_assoc, mul_left_comm, mul_comm] using hbound

  -- Missing points across distinct divisors are disjoint members of the complement of A.
  have missing_bound {Q N : ℕ} (hQ : 0 < Q) (A : Finset ℕ) (hA : A ⊆ Icc 1 N) :
      (∑ d ∈ Q.divisors, (missing Q d N A).card) + A.card ≤ N := by
    let B := Q.divisors.sigma (fun d => missing Q d N A)
    have hsub : ∀ v ∈ B, atPoint Q v.1 v.2 ∈ (Icc 1 N) \ A := by
      rintro ⟨d,v⟩ hv
      obtain ⟨hd, hv⟩ := mem_sigma.mp hv
      obtain ⟨hv, hn⟩ := mem_filter.mp hv
      exact mem_sdiff.mpr ⟨point_mem hQ (Nat.mem_divisors.mp hd).1 hv, hn⟩
    have hinj : Set.InjOn (fun v : Σ _ : ℕ, ℕ × ℕ => atPoint Q v.1 v.2) B := by
      rintro ⟨d,v⟩ hd ⟨e,w⟩ he h
      obtain ⟨hd, hv⟩ := mem_sigma.mp hd
      obtain ⟨he, hw⟩ := mem_sigma.mp he
      have hp := point_injective hQ
        (x₁ := (d,v)) (x₂ := (e,w))
        ⟨(Nat.mem_divisors.mp hd).1, (mem_product.mp (mem_filter.mp hv).1).2⟩
        ⟨(Nat.mem_divisors.mp he).1, (mem_product.mp (mem_filter.mp hw).1).2⟩ h
      rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
      rfl
    have hB := card_le_card_of_injOn (fun v : Σ _ : ℕ, ℕ × ℕ => atPoint Q v.1 v.2)
      hsub hinj
    rw [show B.card = _ from card_sigma .., card_sdiff_of_subset hA, Nat.card_Icc] at hB
    have hcard := card_le_card hA
    rw [Nat.card_Icc] at hcard
    omega

  have inside_add_missing (Q d N : ℕ) (A : Finset ℕ) :
      (inside Q d N A).card + (missing Q d N A).card =
        (N / (d * Q)) * (Residues Q).card := by
    unfold inside missing
    rw [card_filter_add_card_filter_not]
    simp [rect]

  -- Compare the complete blocks for all words with one common larger rectangle.
  have scale_bound {c : W → ℕ} (hC : c ∈ C) :
      (∑ w : W, scale Q (c w) N A) ≤
        (Fintype.card (W) : ℝ) * (4 * α * N) := by
    let L := 2 * N / (c 0 * Q)
    let B := range L ×ˢ Residues Q
    have hc0 : 0 < c 0 := Nat.pos_of_dvd_of_pos (hDvd c hC 0) hQ
    have hR : (0 : ℝ) < (Residues Q).card := by exact_mod_cast residue_pos hQ
    have hsub (w : W) : inside Q (c w) N A ⊆ B := by
      intro v hv
      obtain ⟨hv, _⟩ := mem_filter.mp hv
      obtain ⟨hv, hr⟩ := mem_product.mp hv
      have hw0 := Nat.pos_of_dvd_of_pos (hDvd c hC w) hQ
      have hkv := (Nat.le_div_iff_mul_le (Nat.mul_pos hw0 hQ)).mp
        (show v.1 + 1 ≤ N / (c w * Q) from mem_range.mp hv)
      apply mem_product.mpr
      refine ⟨mem_range.mpr ((Nat.le_div_iff_mul_le (Nat.mul_pos hc0 hQ)).mpr ?_), hr⟩
      calc
        (v.1 + 1) * (c 0 * Q) ≤ (v.1 + 1) * ((2 * c w) * Q) := by gcongr; exact (hBalance c hC w).2
        _ = 2 * ((v.1 + 1) * (c w * Q)) := by ac_rfl
        _ ≤ 2 * N := Nat.mul_le_mul_left _ hkv
    have hswap : (∑ w : W, ((inside Q (c w) N A).card : ℝ)) =
        ∑ v ∈ B, ((univ.filter fun w => v ∈ inside Q (c w) N A).card : ℝ) := by
      simp_rw [← sum_boole]
      rw [sum_comm]
      apply sum_congr rfl
      intro w _
      rw [sum_boole, filter_mem_eq_inter, inter_eq_right.mpr (hsub w)]
    have hcount : (∑ w : W, ((inside Q (c w) N A).card : ℝ)) ≤
        (L : ℝ) * (Residues Q).card * (α * Fintype.card (W)) := by
      rw [hswap]
      calc
        _ ≤ ∑ _v ∈ B, α * (Fintype.card (W) : ℝ) := by
          apply sum_le_sum
          intro v hv
          have hr := mem_Icc.mp (mem_filter.mp (mem_product.mp hv).2).1
          have hm : 0 < Q * v.1 + v.2 := by omega
          have hcard : (univ.filter fun w => v ∈ inside Q (c w) N A).card ≤
              (univ.filter fun w => (Q * v.1 + v.2) * c w ∈ A).card :=
            card_le_card fun w hw => by
              have hp := (mem_filter.mp (mem_filter.mp hw).2).2
              exact mem_filter.mpr ⟨mem_univ _, by simpa [atPoint, Nat.mul_comm] using hp⟩
          exact (Nat.cast_le.mpr hcard).trans (hsection c hC _ hm)
        _ = _ := by simp [B]
    have hL : (L : ℝ) * ((c 0 : ℝ) * Q) ≤ 2 * N := by
      exact_mod_cast Nat.div_mul_le_self (2 * N) (c 0 * Q)
    have hcoef : 0 ≤ (2 * (c 0 : ℝ) * Q) / (Residues Q).card := by positivity
    calc
      (∑ w : W, scale Q (c w) N A) ≤
          ∑ w : W, ((2 * (c 0 : ℝ) * Q) / (Residues Q).card) *
            ((inside Q (c w) N A).card : ℝ) := by
        apply sum_le_sum
        intro w _
        unfold scale
        gcongr
        exact_mod_cast (hBalance c hC w).1
      _ ≤ ((2 * (c 0 : ℝ) * Q) / (Residues Q).card) *
            ((L : ℝ) * (Residues Q).card * (α * Fintype.card (W))) := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left hcount hcoef
      _ = 2 * ((L : ℝ) * ((c 0 : ℝ) * Q)) * (α * Fintype.card (W)) := by
        field_simp
      _ ≤ 2 * (2 * (N : ℝ)) * (α * Fintype.card (W)) := by
        gcongr
      _ = _ := by ring

  -- The minimum of the two masses lets us count omissions with coefficient at most one.
  have mass_point_bound {Q d N : ℕ} (hQ : 0 < Q) (hd : d ∣ Q)
      (A : Finset ℕ) (q : ℝ) (hq : 0 ≤ q) :
      (N : ℝ) * min (rootMass Q d) q ≤
        (missing Q d N A).card + (Residues Q).card + q * scale Q d N A := by
    let r : ℝ := (Residues Q).card
    let v : ℝ := (d : ℝ) * Q
    have hr : 0 < r := Nat.cast_pos.mpr (residue_pos hQ)
    have hv : 0 < v := mul_pos (Nat.cast_pos.mpr (Nat.pos_of_dvd_of_pos hd hQ)) (Nat.cast_pos.mpr hQ)
    have hdiv : (N : ℝ) < (((N / (d * Q) : ℕ) : ℝ) + 1) * v := by
      have hnat := (Nat.div_lt_iff_lt_mul (Nat.mul_pos (Nat.pos_of_dvd_of_pos hd hQ) hQ)).mp
        (Nat.lt_succ_self (N / (d * Q)))
      have hreal : (N : ℝ) < (((N / (d * Q)).succ * (d * Q) : ℕ) : ℝ) :=
        Nat.cast_lt.mpr hnat
      simpa only [Nat.cast_mul, Nat.cast_succ, v] using hreal
    have h₁ : (N : ℝ) * (r / v) ≤ (inside Q d N A).card + (missing Q d N A).card + r := by
      have he : ((inside Q d N A).card : ℝ) + (missing Q d N A).card =
          ((N / (d * Q) : ℕ) : ℝ) * r := by
        dsimp only [r]
        exact_mod_cast inside_add_missing Q d N A
      rw [he, ← mul_div_assoc, div_le_iff₀ hv]
      convert mul_le_mul_of_nonneg_right hdiv.le hr.le using 1
      ring
    let k := min (rootMass Q d) q / (r / v)
    have hk : 0 ≤ k := div_nonneg (le_min (div_nonneg hr.le hv.le) hq) (div_nonneg hr.le hv.le)
    have hk₁ : k ≤ 1 := (div_le_iff₀ (div_pos hr hv)).mpr (by rw [one_mul]; exact min_le_left _ _)
    have hk₂ : k ≤ q * (v / r) := by
      apply (div_le_iff₀ (div_pos hr hv)).mpr
      have hcancel : q * (v / r) * (r / v) = q := by field_simp
      rw [hcancel]
      exact min_le_right _ _
    calc
      (N : ℝ) * min (rootMass Q d) q = k * ((N : ℝ) * (r / v)) := by
        dsimp only [k]
        field_simp
      _ ≤ k * ((inside Q d N A).card + (missing Q d N A).card + r) :=
        mul_le_mul_of_nonneg_left h₁ hk
      _ = k * (inside Q d N A).card + k * ((missing Q d N A).card + r) := by ring
      _ ≤ (q * (v / r)) * (inside Q d N A).card + 1 * ((missing Q d N A).card + r) :=
        add_le_add (mul_le_mul_of_nonneg_right hk₂ (by positivity))
          (mul_le_mul_of_nonneg_right hk₁ (by positivity))
      _ = _ := by unfold scale; change _ = _ + r + q * (v / r * _); ring

  have vertexMass_nonneg (d : ℕ) : 0 ≤ q d := by
    unfold q
    apply sum_nonneg
    intro c hc
    apply sum_nonneg
    intro w _
    split_ifs
    · exact div_nonneg (hm c hc) (by positivity)
    · rfl

  have vertex_sum (f : ℕ → ℝ) :
      (∑ d ∈ Q.divisors, q d * f d) =
        ∑ c ∈ C, (mass c / Fintype.card (W)) * ∑ w : W, f (c w) := by
    simp only [q, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro c hc
    rw [sum_comm, mul_sum]
    apply sum_congr rfl
    intro w _
    have hd := Nat.mem_divisors.mpr ⟨hDvd c hc w, hQ.ne'⟩
    simp_rw [ite_mul, zero_mul]
    rw [sum_eq_single_of_mem (c w) hd]
    · simp
    · intro d _ hne
      rw [if_neg hne.symm]

  let err : ℝ := Q.divisors.card * (Residues Q).card
  have hcap : (∑ d ∈ Q.divisors, q d * scale Q d N A) ≤ 4 * α * N := by
    calc
      _ = ∑ c ∈ C, (mass c / Fintype.card (W)) * ∑ w : W, scale Q (c w) N A :=
        vertex_sum _
      _ ≤ ∑ c ∈ C, (mass c / Fintype.card (W)) *
          ((Fintype.card (W) : ℝ) * (4 * α * N)) := by
        apply sum_le_sum
        intro c hc
        exact mul_le_mul_of_nonneg_left (scale_bound hc)
          (by positivity [hm c hc])
      _ = (∑ c ∈ C, mass c) * (4 * α * N) := by
        rw [sum_mul]
        apply sum_congr rfl
        intro c _
        have hW : (Fintype.card (W) : ℝ) ≠ 0 := by positivity
        field_simp
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hmass (by positivity : 0 ≤ 4 * α * N)
  have hmissing : (∑ d ∈ Q.divisors, ((missing Q d N A).card : ℝ)) + (A.card : ℝ) ≤ N := by
    exact_mod_cast missing_bound hQ A hA
  have hfull : (N : ℝ) * (1 - η) ≤
      (∑ d ∈ Q.divisors, ((missing Q d N A).card : ℝ)) + err + 4 * α * N := by
    calc
      _ ≤ ∑ d ∈ Q.divisors, (N : ℝ) * min (rootMass Q d) (q d) := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left hcover (by positivity)
      _ ≤ ∑ d ∈ Q.divisors,
          (((missing Q d N A).card : ℝ) + (Residues Q).card + q d * scale Q d N A) := by
        apply sum_le_sum
        intro d hd
        exact mass_point_bound hQ (Nat.mem_divisors.mp hd).1 A _ (vertexMass_nonneg d)
      _ ≤ _ := by
        simp only [sum_add_distrib, sum_const, nsmul_eq_mul]
        exact add_le_add_right hcap _
  dsimp [err] at hfull
  linarith


theorem main : H1 → H2 → type_of% @Erdos536.erdos_536 := by
  intro h₁ h₂ ε hε
  let α := ε / 16
  have hα : 0 < α := by positivity
  obtain ⟨h, hroth⟩ := h₂ α hα
  obtain ⟨Q, C, mass, hQ, hC, hm, hmass, hc⟩ := h₁ h (ε / 4) (by positivity)
  let r := ((Icc 1 Q).filter fun t => t.Coprime Q).card
  let err : ℝ := Q.divisors.card * r
  filter_upwards [eventually_ge_atTop (⌊2 * err / ε⌋₊ + 1)] with N hN A hA hAε
  by_contra hfree
  have hsection (c : (Fin h → ZMod 3) → ℕ) (hmem : c ∈ C) (m : ℕ) (hm : 0 < m) :
      ((univ.filter fun w => m * c w ∈ A).card : ℝ) ≤ α * Fintype.card (Fin h → ZMod 3) := by
    apply hroth
    intro x hx z hz y hy hline
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hx hz hy
    obtain ⟨h₁, h₂⟩ := (hC c hmem).2.2.2 x y z hline
    have he₁ : (m * c x).lcm (m * c z) = (m * c z).lcm (m * c y) := by
      simp only [Nat.lcm_mul_left, h₁]
    have he₂ : (m * c z).lcm (m * c y) = (m * c x).lcm (m * c y) := by
      simp only [Nat.lcm_mul_left, h₂]
    have hneq : m * c x = m * c z ∨ m * c z = m * c y ∨ m * c x = m * c y := by
      by_contra hc'
      push Not at hc'
      exact hfree ⟨_, hx, _, hz, _, hy, by simp [hc'.1, hc'.2.1, hc'.2.2], he₁, he₂⟩
    have hcancel {a b : Fin h → ZMod 3} (he : m * c a = m * c b) : a = b :=
      (hC c hmem).1 (Nat.eq_of_mul_eq_mul_left hm he)
    rcases hneq with he | he | he
    · exact hcancel he
    · exact add_right_cancel ((hcancel he).symm ▸ hline)
    · have hxy := hcancel he
      have ht : (2 : ZMod 3) * 2 = 1 := by decide
      have heval : ∀ i, x i + x i = z i + z i := fun i => congrFun (hxy.symm ▸ hline) i
      funext i
      calc
        x i = (2 : ZMod 3) * (x i + x i) := by rw [← two_mul, ← mul_assoc, ht, one_mul]
        _ = (2 : ZMod 3) * (z i + z i) := by rw [heval i]
        _ = z i := by rw [← two_mul, ← mul_assoc, ht, one_mul]
  have hsmall := discrete_transfer hQ (fun c h => (hC c h).2.1)
    (fun c h => (hC c h).2.2.1) hm hmass α (ε / 4) hα A hA hsection hc
  have herr : err < ε * (N : ℝ) / 2 := by
    have hh' := (Nat.floor_lt (by positivity : 0 ≤ 2 * err / ε)).mp
      (show ⌊2 * err / ε⌋₊ < N by omega)
    have := (div_lt_iff₀ hε).mp hh'
    linarith
  change (A.card : ℝ) ≤ (ε / 4 + 4 * (ε / 16)) * N + err at hsmall
  linarith

end OMA.R_Erdos536_erdos_536_R1
