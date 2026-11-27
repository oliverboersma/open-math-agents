import OMAReductions.R_Erdos711_erdos_711_parts_i_R2
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Hall obstructions for rough divisors

Double counting handles windows with bounded point multiplicity. A common multiple in the
window also gives an explicit matching, by translating all divisors to one side of it.
Periodicity lets us test only shifts below the least common multiple.
-/

namespace OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R1

open Filter

/-- A uniform small-power bound on the divisor function in a polynomial range. -/
def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ y : ℕ, 0 < y → y ≤ n ^ 3 →
    (y.divisors.card : ℝ) ≤ (n : ℝ) ^ δ

/-- Hall expansion at a large residue for a family with a crowded multiple but no common one. -/
def H2 : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ᶠ n : ℕ in atTop,
    let q := ⌊(n : ℝ) ^ δ⌋₊
    ∀ r : ℕ, n ^ 2 < r → r < (Finset.Icc 1 n).lcm id →
      ∀ U : Finset ℕ, (∀ d ∈ U, 1 ≤ d ∧ d ≤ n ∧ ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ Nat.sqrt n < p) →
        (∃ y ∈ Finset.Icc (r + 1) (r + n * q), q < (U.filter (· ∣ y)).card) →
        (¬ ∃ z ∈ Finset.Icc (r + 1) (r + n * q), ∀ d ∈ U, d ∣ z) →
        U.card ≤ ((Finset.Icc (r + 1) (r + n * q)).filter (fun y => ∃ d ∈ U, d ∣ y)).card

lemma sparse_hall (r n q : ℕ) (hq : 0 < q) (U : Finset ℕ)
    (hU : ∀ d ∈ U, 1 ≤ d ∧ d ≤ n)
    (hdeg : ∀ y ∈ Finset.Icc (r+1) (r+n*q), (U.filter (· ∣ y)).card ≤ q) :
    U.card ≤ ((Finset.Icc (r+1) (r+n*q)).filter (fun y => ∃ d ∈ U, d ∣ y)).card := by
  classical
  let I := Finset.Icc (r+1) (r+n*q)
  let Y := I.filter (fun y => ∃ d ∈ U, d ∣ y)
  change U.card ≤ Y.card
  apply Nat.le_of_mul_le_mul_right _ hq
  apply Finset.card_mul_le_card_mul (fun d y : ℕ => d ∣ y)
  · intro d hd
    obtain ⟨hd0, hdn⟩ := hU d hd
    let g (j : ℕ) := (r / d + 1 + j) * d
    have hg : Function.Injective g := by
      intro i j hij
      dsimp [g] at hij
      have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < d) hij
      omega
    rw [← Finset.card_range q, ← Finset.card_image_of_injective _ hg]
    apply Finset.card_le_card
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    have hjq := Finset.mem_range.mp hj
    have hdiv : d ∣ g j := dvd_mul_left _ _
    have hlo := Nat.mod_lt r (by omega : 0 < d)
    have heq := Nat.mod_add_div r d
    rw [Nat.mul_comm d (r/d)] at heq
    have hmul : (j+1)*d ≤ q*n := Nat.mul_le_mul (by omega) hdn
    have hin : g j ∈ I := by
      apply Finset.mem_Icc.mpr
      dsimp [g]
      rw [show r/d+1+j = r/d+(j+1) by omega, Nat.add_mul]
      rw [Nat.mul_comm q n] at hmul
      constructor
      · have := Nat.mul_le_mul_right d (show 1 ≤ j+1 by omega)
        simp only [one_mul] at this
        omega
      · omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hin, d, hd, hdiv⟩, hdiv⟩
  · intro y hy
    exact hdeg y (Finset.mem_filter.mp hy).1

lemma center_hall (r n q : ℕ) (hq : 3 ≤ q) (U : Finset ℕ)
    (hU : ∀ d ∈ U, 1 ≤ d ∧ d ≤ n) (z : ℕ)
    (hz : z ∈ Finset.Icc (r+1) (r+n*q)) (hall : ∀ d ∈ U, d ∣ z) :
    U.card ≤ ((Finset.Icc (r+1) (r+n*q)).filter (fun y => ∃ d ∈ U, d ∣ y)).card := by
  classical
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hz
  by_cases h : z+n ≤ r+n*q
  · apply Finset.card_le_card_of_injOn (fun d => z+d)
    · intro d hd
      have := hU d hd
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by dsimp; omega, by dsimp; omega⟩, d, hd,
        dvd_add (hall d hd) (dvd_refl d)⟩
    · intro a ha b hb hab
      exact Nat.add_left_cancel hab
  · have hnq := Nat.mul_le_mul_left n hq
    apply Finset.card_le_card_of_injOn (fun d => z-d)
    · intro d hd
      have := hU d hd
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by dsimp; omega, by dsimp; omega⟩, d, hd,
        Nat.dvd_sub (hall d hd) (dvd_refl d)⟩
    · intro a ha b hb hab
      have := hU a ha
      have := hU b hb
      dsimp at hab
      omega
lemma match_residue (n r q : ℕ)
    (hHall : ∀ U : Finset ℕ,
      (∀ d ∈ U, 1 ≤ d ∧ d ≤ n ∧ ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ Nat.sqrt n < p) →
      U.card ≤ ((Finset.Icc (r+1) (r+n*q)).filter (fun y => ∃ d ∈ U, d ∣ y)).card) :
    ∃ a : Fin n → ℕ,
      Set.InjOn a {i | ∃ p : ℕ, p.Prime ∧ p ∣ (i.val+1) ∧ Nat.sqrt n < p} ∧
      ∀ i : Fin n, (∃ p : ℕ, p.Prime ∧ p ∣ (i.val+1) ∧ Nat.sqrt n < p) →
        r < a i ∧ a i ≤ r+n*q ∧ (i.val+1) ∣ a i := by
  classical
  let R := {i : Fin n | ∃ p : ℕ, p.Prime ∧ p ∣ (i.val+1) ∧ Nat.sqrt n < p}
  let val (i : R) := i.val.val+1
  have hval : Function.Injective val := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    exact Nat.add_right_cancel hij
  let I := Finset.Icc (r+1) (r+n*q)
  let T (i : R) := I.filter (val i ∣ ·)
  have hex : ∀ t : Finset R, t.card ≤ (t.biUnion T).card := by
    intro t
    let U := t.image val
    have hU : ∀ d ∈ U, 1 ≤ d ∧ d ≤ n ∧ ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ Nat.sqrt n < p := by
      intro d hd
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
      exact ⟨Nat.succ_le_succ (Nat.zero_le _), i.val.isLt, i.property⟩
    have hc : U.card = t.card := Finset.card_image_of_injective t hval
    rw [← hc]
    apply (hHall U hU).trans
    apply Finset.card_le_card
    intro y hy
    obtain ⟨hyI,d,hd,hdy⟩ := Finset.mem_filter.mp hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_biUnion.mpr ⟨i,hi, Finset.mem_filter.mpr ⟨hyI,hdy⟩⟩
  obtain ⟨f, hf, ht⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective T).mp hex
  let a (i : Fin n) := if hi : i ∈ R then f ⟨i,hi⟩ else 0
  refine ⟨a, ?_, ?_⟩
  · intro i hi j hj hij
    change i ∈ R at hi
    change j ∈ R at hj
    have he : f ⟨i,hi⟩ = f ⟨j,hj⟩ := by simpa [a, hi, hj] using hij
    exact congrArg Subtype.val (hf he)
  · intro i hi
    change i ∈ R at hi
    obtain ⟨hI,hd⟩ := Finset.mem_filter.mp (ht ⟨i,hi⟩)
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hI
    simpa [a,hi,val] using (show r < f ⟨i,hi⟩ ∧ f ⟨i,hi⟩ ≤ r+n*q ∧ (i.val+1) ∣ f ⟨i,hi⟩
      from ⟨hl,hu,hd⟩)

theorem main : H1 → H2 → OMA.R_Erdos711_erdos_711_parts_i_R2.H2 := by
  classical
  intro hdiv hrem ε hε
  let δ := min (ε/2) (1/2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hhalf : δ ≤ 1/2 := min_le_right _ _
  have hε' : δ + δ ≤ ε := by have := min_le_left (ε/2) (1/2 : ℝ); dsimp [δ]; linarith
  have hg : Tendsto (fun n : ℕ => (n : ℝ)^δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  filter_upwards [hdiv δ hδ, hrem δ hδ hhalf, hg.eventually_ge_atTop 3,
    eventually_ge_atTop (2 : ℕ)] with n hτ hcase hgrow hn m
  let q := ⌊(n : ℝ)^δ⌋₊
  have hq : 3 ≤ q := Nat.le_floor (by exact_mod_cast hgrow)
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0:ℝ) < n := by linarith
  have hqR : (q:ℝ) ≤ (n:ℝ)^δ := Nat.floor_le (by positivity)
  have hqn : q ≤ n := by
    have hb := Real.rpow_le_rpow_of_exponent_le hnR (show δ ≤ 1 by linarith)
    rw [Real.rpow_one] at hb
    exact_mod_cast hqR.trans hb
  let M := (Finset.Icc 1 n).lcm id
  have hM : 0 < M := by
    apply Nat.pos_of_ne_zero
    apply Finset.lcm_ne_zero_iff.mpr
    intro x hx
    have := (Finset.mem_Icc.mp hx).1
    exact Nat.ne_of_gt this
  let r := m % M
  have hr : r < M := Nat.mod_lt _ hM
  have hshift : r + M*(m/M) = m := Nat.mod_add_div _ _
  have hh : ∀ U : Finset ℕ,
      (∀ d ∈ U, 1 ≤ d ∧ d ≤ n ∧ ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ Nat.sqrt n < p) →
      U.card ≤ ((Finset.Icc (r+1) (r+n*q)).filter (fun y => ∃ d ∈ U, d ∣ y)).card := by
    intro U hU
    have hb d (hd : d ∈ U) := And.intro (hU d hd).1 (hU d hd).2.1
    by_cases hc : ∃ z ∈ Finset.Icc (r+1) (r+n*q), ∀ d ∈ U, d ∣ z
    · obtain ⟨z,hz,h⟩ := hc
      exact center_hall r n q hq U hb z hz h
    by_cases hd : ∃ y ∈ Finset.Icc (r+1) (r+n*q), q < (U.filter (· ∣ y)).card
    · by_cases hs : r ≤ n^2
      · obtain ⟨y,hy,hcrowd⟩ := hd
        obtain ⟨hylo,hyhi⟩ := Finset.mem_Icc.mp hy
        have hyn : y ≤ n^3 := by
          have hmul := Nat.mul_le_mul_left n hqn
          have hpow := Nat.mul_le_mul_left (n*n) hn
          simp only [pow_succ, pow_zero, one_mul] at hs ⊢
          omega
        have hyt := Nat.le_floor (hτ y (by omega) hyn)
        have hsub : U.filter (· ∣ y) ⊆ y.divisors := by
          intro d h
          exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp h).2, by omega⟩
        exact False.elim ((not_lt_of_ge ((Finset.card_le_card hsub).trans hyt)) hcrowd)
      · exact hcase r (by omega) hr U hU hd hc
    · push Not at hd
      exact sparse_hall r n q (by omega) U hb hd
  obtain ⟨a,ha,hw⟩ := match_residue n r q hh
  refine ⟨n*q+1, ?_, fun i => a i + M*(m/M), ?_, ?_⟩
  · push_cast
    have hone : 1 ≤ (n:ℝ) * (n:ℝ)^δ := by nlinarith
    calc
      (n:ℝ)*q + 1 ≤ 2 * ((n:ℝ) * (n:ℝ)^δ) := by nlinarith [mul_le_mul_of_nonneg_left hqR hnpos.le]
      _ ≤ (n:ℝ)^δ * ((n:ℝ) * (n:ℝ)^δ) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (n:ℝ)^(1 + (δ + δ)) := by rw [Real.rpow_add hnpos, Real.rpow_add hnpos, Real.rpow_one]; ring
      _ ≤ (n:ℝ)^(1+ε) := Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  · intro i hi j hj hij
    exact ha hi hj (Nat.add_right_cancel hij)
  · intro i hi
    obtain ⟨hl,hu,hd⟩ := hw i hi
    have hMdiv : i.val+1 ∣ M := Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨by omega,i.isLt⟩)
    change m < a i + M*(m/M) ∧ a i + M*(m/M) < m + (n*q+1) ∧ _
    exact ⟨by omega, by omega, dvd_add hd (dvd_mul_of_dvd_left hMdiv _)⟩

end OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R1
