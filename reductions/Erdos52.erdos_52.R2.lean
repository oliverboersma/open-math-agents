import FormalConjectures.ErdosProblems.«52»

/-!
# Erdős 52 for sets concentrated in a short arithmetic progression

A collision between two different unordered pairs in an integer progression
produces a rational dilation taking the entire progression into an interval
of radius at most three times the square of its length. The divisor estimate
then controls every nonzero product fibre. The resulting bound is uniform
in the offset and the common difference.

H1 is the elementary divisor estimate, proved below. H2 is the open inverse
statement. It asks whether having few sums and few products forces many
nonzero elements into a progression of polynomial length.
-/

namespace OMA.R_Erdos52_erdos_52_R2

open Finset
open scoped Pointwise

/-- A uniform subpolynomial bound on the number of positive divisors. -/
def H1 : Prop := ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
  n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ η

/-- Inverse step for the remaining sets. The constants and the polynomial
degree are independent of the set. The square on the index count makes the
threshold equivalent to at least n^(1-ε/4) progression elements. -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ K : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ A : Finset ℤ, 2 ≤ A.card →
    (max (A + A).card (A * A).card : ℝ) < c * (A.card : ℝ) ^ (2 - ε) →
    ∃ (I : Finset ℤ) (a d : ℤ), d ≠ 0 ∧
      (∀ i ∈ I, 0 ≤ i ∧ i ≤ (A.card ^ K : ℕ) ∧ a + d * i ∈ A ∧ a + d * i ≠ 0) ∧
      (A.card : ℝ) ^ (2 - ε / 2) ≤ (I.card : ℝ) ^ 2

theorem divisor_bound : H1 := by
  intro η hη
  let t : ℝ := (2 : ℝ) ^ η
  have ht : 1 < t := Real.one_lt_rpow (by norm_num) hη
  let B : ℝ := max 1 (1 / (t - 1))
  have hB : 1 ≤ B := le_max_left _ _
  have hBt : 1 ≤ B * (t - 1) :=
    (div_le_iff₀ (by linarith : 0 < t - 1)).mp (le_max_right _ _)
  obtain ⟨P, hP⟩ := exists_nat_gt ((2 : ℝ) ^ η⁻¹)
  refine ⟨B ^ P, by positivity, ?_⟩
  intro n hn
  let F := n.primeFactors
  let cost (p : ℕ) : ℝ := if p < P then B else 1
  have hpBound (p : ℕ) (hp : p ∈ F) :
      ((n.factorization p + 1 : ℕ) : ℝ) ≤ cost p * ((p : ℝ) ^ (n.factorization p) : ℝ) ^ η := by
    let a := n.factorization p
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (0 : ℝ) ≤ p := by positivity
    have hr : t ≤ (p : ℝ) ^ η := Real.rpow_le_rpow (by norm_num) hp2 hη.le
    have hpow : ((p : ℝ) ^ a) ^ η = ((p : ℝ) ^ η) ^ a := by
      rw [← Real.rpow_natCast_mul hp0, ← Real.rpow_mul_natCast hp0, mul_comm]
    change (↑(a + 1) : ℝ) ≤ cost p * ((p : ℝ) ^ a) ^ η
    rw [hpow, Nat.cast_add, Nat.cast_one]
    have hbern := one_add_mul_sub_le_pow (show - 1 ≤ (p : ℝ) ^ η by linarith) a
    by_cases h : p < P
    · rw [show cost p = B from if_pos h]
      have hcoeff : 1 ≤ B * ((p : ℝ) ^ η - 1) :=
        hBt.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
      calc
        (a : ℝ) + 1 ≤ B + (a : ℝ) * (B * ((p : ℝ) ^ η - 1)) := by
          nlinarith [mul_le_mul_of_nonneg_left hcoeff (a.cast_nonneg : (0 : ℝ) ≤ a)]
        _ ≤ B * ((p : ℝ) ^ η) ^ a := by
          nlinarith [mul_le_mul_of_nonneg_left hbern (show 0 ≤ B by linarith)]
    · rw [show cost p = 1 from if_neg h, one_mul]
      have hlarge : (2 : ℝ) ≤ (p : ℝ) ^ η := by
        have hPp : (P : ℝ) ≤ p := by exact_mod_cast (Nat.le_of_not_gt h)
        have := Real.rpow_le_rpow (by positivity : 0 ≤ (2 : ℝ) ^ η⁻¹) (hP.le.trans hPp) hη.le
        simpa [Real.rpow_inv_rpow (by norm_num : (0 : ℝ) ≤ 2) hη.ne'] using this
      nlinarith [mul_nonneg (a.cast_nonneg : (0 : ℝ) ≤ a) (sub_nonneg.mpr hlarge)]
  have hcost : ∏ p ∈ F, cost p ≤ B ^ P := by
    have heq : ∏ p ∈ F, cost p = B ^ (F.filter (· < P)).card := by
      simp [cost, ← Finset.prod_filter]
    rw [heq]
    exact pow_le_pow_right₀ hB (by
      have := Finset.card_le_card (show F.filter (· < P) ⊆ Finset.range P from fun _ hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2)
      simpa using this)
  have hfac : ∏ p ∈ F, (p : ℝ) ^ n.factorization p = (n : ℝ) := by
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  rw [Nat.card_divisors hn, Nat.cast_prod]
  calc
    _ ≤ ∏ p ∈ F, (cost p * ((p : ℝ) ^ n.factorization p) ^ η) :=
      Finset.prod_le_prod (fun _ _ => by positivity) hpBound
    _ = (∏ p ∈ F, cost p) * (n : ℝ) ^ η := by
      rw [Finset.prod_mul_distrib, Real.finsetProd_rpow F (fun p => (p : ℝ) ^ n.factorization p) (fun _ _ => by positivity) η, hfac]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcost (by positivity)


/-- Removing the common factor d from an equality of progression products. -/
lemma collision_identity {a d i j k l : ℤ} (hd : d ≠ 0)
    (h : (a + d * i) * (a + d * j) = (a + d * k) * (a + d * l)) :
    a * (i + j - k - l) = d * (k * l - i * j) := by
  apply mul_left_cancel₀ hd
  linear_combination h

/-- Equal elementary symmetric functions determine an unordered pair. -/
lemma pair_of_sum_product {i j k l : ℤ} (hs : i + j = k + l) (hp : i * j = k * l) :
    (i, j) = (k, l) ∨ (i, j) = (l, k) := by
  have h : (i - k) * (i - l) = 0 := by linear_combination i * hs - hp
  rcases mul_eq_zero.mp h with h | h
  · left; apply Prod.ext <;> dsimp <;> omega
  · right; apply Prod.ext <;> dsimp <;> omega

/-- A finite collection of ordered factorisations of a fixed nonzero integer
has at most twice its number of positive divisors. -/
lemma factor_pairs {m : ℤ} (hm : m ≠ 0) (T : Finset (ℤ × ℤ))
    (hT : ∀ p ∈ T, p.1 * p.2 = m) : T.card ≤ 2 * m.natAbs.divisors.card := by
  classical
  let label (p : ℤ × ℤ) := (p.1.natAbs, decide (p.1 < 0))
  have h := Finset.card_le_card_of_injOn (s := T)
    (t := m.natAbs.divisors ×ˢ (Finset.univ : Finset Bool)) label
  have hmap : Set.MapsTo label T (↑(m.natAbs.divisors ×ˢ (Finset.univ : Finset Bool)) : Set (ℕ × Bool)) := by
    intro p hp
    have hm' := congrArg Int.natAbs (hT p hp)
    rw [Int.natAbs_mul] at hm'
    exact Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨Dvd.intro _ hm', by simpa using hm⟩, Finset.mem_univ _⟩
  have hinj : Set.InjOn label T := by
    intro p hp q hq he
    have he₁ : p.1.natAbs = q.1.natAbs := congrArg Prod.fst he
    have he₂ : decide (p.1 < 0) = decide (q.1 < 0) := congrArg Prod.snd he
    have he₃ : p.1 = q.1 := by
      rcases Int.natAbs_eq_natAbs_iff.mp he₁ with hh | hh
      · exact hh
      · by_cases hpneg : p.1 < 0 <;> by_cases hqneg : q.1 < 0 <;> simp_all
        all_goals omega
    have hpn : p.1 ≠ 0 := fun hz => hm (by simpa [hz] using (hT p hp).symm)
    apply Prod.ext he₃
    exact mul_left_cancel₀ hpn (by rw [hT p hp, he₃, hT q hq])
  simpa [Nat.mul_comm] using h hmap hinj

/-- Bound the multiplicity of a nonzero product from a progression of span L.
The proof chooses a second representation with a different index sum whenever
one exists. -/
lemma progression_fibre (a d L z : ℤ) (hd : d ≠ 0) (hz : z ≠ 0) (hL : 0 ≤ L)
    (T : Finset (ℤ × ℤ)) (hb : ∀ p ∈ T, 0 ≤ p.1 ∧ p.1 ≤ L ∧ 0 ≤ p.2 ∧ p.2 ≤ L)
    (hf : ∀ p ∈ T, (a + d * p.1) * (a + d * p.2) = z) :
    T.card ≤ 2 ∨ ∃ m : ℤ, m ≠ 0 ∧ |m| ≤ 9 * L ^ 4 ∧ T.card ≤ 2 * m.natAbs.divisors.card := by
  classical
  rcases T.eq_empty_or_nonempty with h | ⟨p, hp⟩
  · simp [h]
  by_cases hs : ∀ q ∈ T, q.1 + q.2 = p.1 + p.2
  · left
    refine (Finset.card_le_card (t := {p, p.swap}) ?_).trans Finset.card_le_two
    intro q hq
    have he := collision_identity hd ((hf q hq).trans (hf p hp).symm)
    have hsum := hs q hq
    have hzero : q.1 + q.2 - p.1 - p.2 = 0 := by omega
    rw [hzero, mul_zero, eq_comm, mul_eq_zero] at he
    have hprod : q.1 * q.2 = p.1 * p.2 := by rcases he with he | he <;> omega
    have hpairs : q = p ∨ q = p.swap := pair_of_sum_product hsum hprod
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hpairs
  · right
    push Not at hs
    obtain ⟨q, hq, hne⟩ := hs
    let v := p.1 + p.2 - q.1 - q.2
    let w := q.1 * q.2 - p.1 * p.2
    let g (i : ℤ) := w + v * i
    have hv : v ≠ 0 := by dsimp [v]; omega
    have hrel : a * v = d * w := collision_identity hd ((hf p hp).trans (hf q hq).symm)
    have hscale (i : ℤ) : d * g i = v * (a + d * i) := by dsimp [g]; linear_combination -hrel
    let m := g p.1 * g p.2
    have he (r : ℤ × ℤ) (hr : r ∈ T) : d ^ 2 * (g r.1 * g r.2) = v ^ 2 * z := by
      calc
        _ = (d * g r.1) * (d * g r.2) := by ring
        _ = v ^ 2 * ((a + d * r.1) * (a + d * r.2)) := by rw [hscale, hscale]; ring
        _ = _ := by rw [hf r hr]
    have hm : m ≠ 0 := by
      intro hm
      have he' : d ^ 2 * m = v ^ 2 * z := he p hp
      rw [hm, mul_zero] at he'
      exact (mul_ne_zero (pow_ne_zero _ hv) hz) he'.symm
    have hprod (r : ℤ × ℤ) (hr : r ∈ T) : g r.1 * g r.2 = m :=
      mul_left_cancel₀ (pow_ne_zero 2 hd) ((he r hr).trans (he p hp).symm)
    have bp := hb p hp
    have bq := hb q hq
    have prodBound (x y : ℤ) (hx : 0 ≤ x ∧ x ≤ L) (hy : 0 ≤ y ∧ y ≤ L) :
        0 ≤ x * y ∧ x * y ≤ L ^ 2 :=
      ⟨mul_nonneg hx.1 hy.1, by simpa [sq] using mul_le_mul hx.2 hy.2 hy.1 hL⟩
    have bp' := prodBound _ _ ⟨bp.1, bp.2.1⟩ bp.2.2
    have bq' := prodBound _ _ ⟨bq.1, bq.2.1⟩ bq.2.2
    have bw : |w| ≤ L ^ 2 := abs_le.mpr (by dsimp [w]; omega)
    have bv : |v| ≤ 2 * L := abs_le.mpr (by dsimp [v]; omega)
    have bg (i : ℤ) (hi : 0 ≤ i) (hi' : i ≤ L) : |g i| ≤ 3 * L ^ 2 := by
      calc
        _ ≤ |w| + |v| * |i| := by simpa [g, abs_mul] using abs_add_le w (v * i)
        _ ≤ L ^ 2 + (2 * L) * L := by
          rw [abs_of_nonneg hi]
          exact add_le_add bw (mul_le_mul bv hi' hi (by omega))
        _ = _ := by ring
    refine ⟨m, hm, ?_, ?_⟩
    · calc
        |m| = |g p.1| * |g p.2| := abs_mul _ _
        _ ≤ (3 * L ^ 2) * (3 * L ^ 2) := mul_le_mul (bg _ bp.1 bp.2.1)
          (bg _ bp.2.2.1 bp.2.2.2) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    · let mapPair (r : ℤ × ℤ) := (g r.1, g r.2)
      have gi : Function.Injective g := by
        intro x y h
        exact mul_left_cancel₀ hv (add_left_cancel h)
      have mi : Function.Injective mapPair := fun x y h =>
        Prod.ext (gi (congrArg Prod.fst h)) (gi (congrArg Prod.snd h))
      rw [← Finset.card_image_of_injective T mi]
      apply factor_pairs hm
      intro r hr
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
      exact hprod t ht

/-- Sum the fibre estimate. The indices may be any subset of the progression,
and the surrounding set A may contain additional elements. -/
theorem progression_products (divisors : H1) (η : ℝ) (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∀ (A I : Finset ℤ) (a d : ℤ) (L : ℕ), d ≠ 0 → 1 ≤ L →
      (∀ i ∈ I, 0 ≤ i ∧ i ≤ (L : ℤ) ∧ a + d * i ∈ A ∧ a + d * i ≠ 0) →
      (I.card : ℝ) ^ 2 ≤ D * (L : ℝ) ^ (4 * η) * ((A * A).card : ℝ) := by
  classical
  obtain ⟨C, hC, db⟩ := divisors η hη
  let D := max 2 (2 * C * (9 : ℝ) ^ η)
  have hD : 2 ≤ D := le_max_left _ _
  refine ⟨D, by linarith, ?_⟩
  intro A I a d L hd hL hI
  let f (p : ℤ × ℤ) := (a + d * p.1) * (a + d * p.2)
  let U := I ×ˢ I
  have maps (p : ℤ × ℤ) (hp : p ∈ U) : f p ∈ A * A := by
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hp
    exact Finset.mul_mem_mul (hI _ hi).2.2.1 (hI _ hj).2.2.1
  have hLr : 1 ≤ (L : ℝ) := by exact_mod_cast hL
  have hpow : 1 ≤ (L : ℝ) ^ (4 * η) := Real.one_le_rpow hLr (by positivity)
  have small : (2 : ℝ) ≤ D * (L : ℝ) ^ (4 * η) :=
    hD.trans (le_mul_of_one_le_right (by linarith) hpow)
  have fibre (z : ℤ) : (((U.filter (fun p => f p = z)).card : ℕ) : ℝ) ≤ D * (L : ℝ) ^ (4 * η) := by
    let T := U.filter (fun p => f p = z)
    change (T.card : ℝ) ≤ _
    rcases T.eq_empty_or_nonempty with hem | ⟨p, hp⟩
    · rw [hem]; simp; linarith
    have coords (r : ℤ × ℤ) (hr : r ∈ T) := Finset.mem_product.mp (Finset.mem_filter.mp hr).1
    have coords' (r : ℤ × ℤ) (hr : r ∈ T) :
        0 ≤ r.1 ∧ r.1 ≤ L ∧ 0 ≤ r.2 ∧ r.2 ≤ L :=
      ⟨(hI _ (coords r hr).1).1, (hI _ (coords r hr).1).2.1,
        (hI _ (coords r hr).2).1, (hI _ (coords r hr).2).2.1⟩
    have hz : z ≠ 0 := by
      rw [← (Finset.mem_filter.mp hp).2]
      exact mul_ne_zero (hI _ (coords p hp).1).2.2.2 (hI _ (coords p hp).2).2.2.2
    rcases progression_fibre a d L z hd hz (by positivity) T coords'
      (fun r hr => (Finset.mem_filter.mp hr).2) with ht | ⟨m, hm, hmL, ht⟩
    · exact (by exact_mod_cast ht : (T.card : ℝ) ≤ 2).trans small
    have hm' : m.natAbs ≠ 0 := by simpa using hm
    have hmL' : (m.natAbs : ℝ) ≤ 9 * (L : ℝ) ^ 4 := by
      rw [Int.abs_eq_natAbs] at hmL
      exact_mod_cast hmL
    calc
      (T.card : ℝ) ≤ 2 * (m.natAbs.divisors.card : ℝ) := by exact_mod_cast ht
      _ ≤ 2 * (C * (m.natAbs : ℝ) ^ η) := by gcongr; exact db _ hm'
      _ ≤ 2 * (C * (9 * (L : ℝ) ^ 4) ^ η) := by gcongr
      _ = (2 * C * (9 : ℝ) ^ η) * (L : ℝ) ^ (4 * η) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul (by positivity : 0 ≤ (L : ℝ))]
        norm_num
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have count := Finset.card_eq_sum_card_fiberwise (t := A * A) maps
  have countR := congrArg (fun n : ℕ => (n : ℝ)) count
  rw [Nat.cast_sum] at countR
  calc
    (I.card : ℝ) ^ 2 = (U.card : ℝ) := by simp [U, sq]
    _ = _ := countR
    _ ≤ ∑ _z ∈ A * A, D * (L : ℝ) ^ (4 * η) := Finset.sum_le_sum (fun z _ => fibre z)
    _ = _ := by simp [mul_comm]

/-- For a progression of polynomial span, absorb the loss from the divisor
estimate into any prescribed positive power of the ambient cardinality. -/
lemma polynomial_index_bound (divisors : H1) (K : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (A I : Finset ℤ) (a d : ℤ), 1 ≤ A.card → d ≠ 0 →
      (∀ i ∈ I, 0 ≤ i ∧ i ≤ (A.card ^ K : ℕ) ∧ a + d * i ∈ A ∧ a + d * i ≠ 0) →
      (I.card : ℝ) ^ 2 ≤ D * (A.card : ℝ) ^ δ * ((A * A).card : ℝ) := by
  let η := δ / (4 * ((K : ℝ) + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨D, hD, estimate⟩ := progression_products divisors η hη
  refine ⟨D, hD, ?_⟩
  intro A I a d hn hd hi
  have est := estimate A I a d (A.card ^ K) hd (one_le_pow₀ hn) hi
  have hexp : (K : ℝ) * (4 * η) ≤ δ := by
    dsimp [η]
    have hk : 0 < (K : ℝ) + 1 := by positivity
    field_simp
    nlinarith
  have hfac : ((A.card ^ K : ℕ) : ℝ) ^ (4 * η) ≤ (A.card : ℝ) ^ δ := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ A.card)]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hexp
  exact est.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac hD.le) (by positivity))

/-- The product-set bound alone proves the conjectured exponent for every
subset of a progression of polynomial span, including sets containing zero.
The constant is independent of the offset and common difference. -/
theorem polynomial_progression_products (K : ℕ) (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (A : Finset ℤ) (a d : ℤ), d ≠ 0 →
      (∀ x ∈ A, ∃ i : ℤ, 0 ≤ i ∧ i ≤ (A.card ^ K : ℕ) ∧ x = a + d * i) →
      c * (A.card : ℝ) ^ (2 - ε) ≤ ((A * A).card : ℝ) := by
  classical
  obtain ⟨D, hD, estimate⟩ := polynomial_index_bound divisor_bound K ε hε
  let c := min 1 (4 * D)⁻¹
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  refine ⟨c, hc, ?_⟩
  intro A a d hd hA
  by_cases hn : 2 ≤ A.card
  · let idx (x : ℤ) := (x - a) / d
    let I := (A.erase 0).image idx
    have data (x : ℤ) (hx : x ∈ A) :
        0 ≤ idx x ∧ idx x ≤ (A.card ^ K : ℕ) ∧ x = a + d * idx x := by
      obtain ⟨i, hi, hi', rfl⟩ := hA x hx
      have hid : idx (a + d * i) = i := by simp [idx, hd]
      rw [hid]
      exact ⟨hi, hi', rfl⟩
    have hcard : I.card = (A.erase 0).card := by
      apply Finset.card_image_of_injOn
      intro x hx y hy hxy
      exact (data x (Finset.mem_of_mem_erase hx)).2.2.trans
        ((congrArg (fun i => a + d * i) hxy).trans (data y (Finset.mem_of_mem_erase hy)).2.2.symm)
    have hlarge : A.card ≤ 2 * I.card := by
      rw [hcard]
      by_cases hz : 0 ∈ A
      · rw [Finset.card_erase_of_mem hz]; omega
      · rw [Finset.erase_eq_of_notMem hz]; omega
    have hi (i : ℤ) (h : i ∈ I) :
        0 ≤ i ∧ i ≤ (A.card ^ K : ℕ) ∧ a + d * i ∈ A ∧ a + d * i ≠ 0 := by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hx₀, hxA⟩ := Finset.mem_erase.mp hx
      obtain ⟨hb, ht, he⟩ := data x hxA
      exact ⟨hb, ht, he ▸ hxA, he ▸ hx₀⟩
    have est := estimate A I a d (by omega) hd hi
    have hl : (A.card : ℝ) ≤ 2 * (I.card : ℝ) := by exact_mod_cast hlarge
    have sqBound : (A.card : ℝ) ^ 2 ≤ 4 * (I.card : ℝ) ^ 2 := by
      nlinarith only [mul_self_le_mul_self (Nat.cast_nonneg A.card) hl]
    have pos : 0 < (A.card : ℝ) := by exact_mod_cast (by omega : 0 < A.card)
    have prodBound : (A.card : ℝ) ^ (2 - ε) ≤ (4 * D) * ((A * A).card : ℝ) := by
      apply le_of_mul_le_mul_left (a := (A.card : ℝ) ^ ε) _ (Real.rpow_pos_of_pos pos _)
      rw [← Real.rpow_add pos, show ε + (2 - ε) = (2 : ℝ) by ring, Real.rpow_two]
      nlinarith only [sqBound, est]
    calc
      c * (A.card : ℝ) ^ (2 - ε) ≤ (4 * D)⁻¹ * (A.card : ℝ) ^ (2 - ε) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ ≤ _ := by
        rw [inv_mul_eq_div, div_le_iff₀ (show 0 < 4 * D by positivity)]
        simpa only [mul_comm] using prodBound
  · rcases (show A.card = 0 ∨ A.card = 1 by omega) with he | he
    · simp [Finset.card_eq_zero.mp he, Real.zero_rpow (by linarith : 2 - ε ≠ 0)]
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp he
      simp [c]

theorem main : H1 → H2 → type_of% @Erdos52.erdos_52 := by
  intro divisors inverse ε hε hε₁
  obtain ⟨K, c, hc, cluster⟩ := inverse ε hε hε₁
  obtain ⟨D, hD, estimate⟩ := polynomial_index_bound divisors K (ε / 2) (by positivity)
  let C := min 1 (min c D⁻¹)
  have hC : 0 < C := lt_min (by norm_num) (lt_min hc (inv_pos.mpr hD))
  have hCc : C ≤ c := (min_le_right _ _).trans (min_le_left _ _)
  have hCD : C ≤ D⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨C, hC, ?_⟩
  intro A
  by_cases hn : 2 ≤ A.card
  · let n : ℝ := A.card
    have hn₁ : 1 ≤ n := by dsimp [n]; exact_mod_cast (by omega : 1 ≤ A.card)
    have hn₀ : 0 < n := by linarith
    by_contra! hsmall
    have hsmall' := lt_of_lt_of_le hsmall (mul_le_mul_of_nonneg_right hCc
      (Real.rpow_nonneg (by positivity) _))
    obtain ⟨I, a, d, hd, hi, hsize⟩ := cluster A hn hsmall'
    have est := estimate A I a d (by omega) hd hi
    have hM : ((A * A).card : ℝ) ≤ (max (A + A).card (A * A).card : ℝ) := by
      exact_mod_cast le_max_right (A + A).card (A * A).card
    have upper : n ^ (2 - ε / 2) ≤ D * n ^ (ε / 2) * (max (A + A).card (A * A).card : ℝ) := by
      exact hsize.trans (est.trans (mul_le_mul_of_nonneg_left hM (by positivity)))
    have hsplit : n ^ (2 - ε / 2) = n ^ (ε / 2) * n ^ (2 - ε) := by
      rw [← Real.rpow_add hn₀]; ring_nf
    rw [hsplit] at upper
    have lower : n ^ (2 - ε) ≤ D * (max (A + A).card (A * A).card : ℝ) := by
      apply le_of_mul_le_mul_left (a := n ^ (ε / 2)) _ (Real.rpow_pos_of_pos hn₀ _)
      simpa only [mul_left_comm, mul_assoc] using upper
    have hbound : D⁻¹ * n ^ (2 - ε) ≤ (max (A + A).card (A * A).card : ℝ) := by
      simpa [inv_mul_eq_div, div_le_iff₀ hD, mul_comm] using lower
    exact (not_lt_of_ge ((mul_le_mul_of_nonneg_right hCD (by positivity)).trans hbound)) hsmall
  · have hsmall : A.card = 0 ∨ A.card = 1 := by omega
    rcases hsmall with he | he
    · simp [Finset.card_eq_zero.mp he, Real.zero_rpow (by linarith : 2 - ε ≠ 0)]
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp he
      simp [C]

end OMA.R_Erdos52_erdos_52_R2
