import FormalConjectures.ErdosProblems.«1109»
import Mathlib

/-!
# The square-modulus large sieve for a squarefree sumset

At a prime square, the occupied residues and their negatives are disjoint. The
vacant residue classes alone therefore contribute half the squared size of the
set to the weighted variance. We apply Konyagin's square-modulus inequality
(Theorem 2 of "Problems on the set of squarefree numbers") at X = floor(N^(4/15)).
-/

namespace OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1

open Filter Finset
open scoped Pointwise

/-- Konyagin's square-modulus large sieve at the balancing scale. The slack absorbs
the subpolynomial factor of his Theorem 2 and the absolute constants. -/
def H1 : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Icc 1 N →
    let Z := (A.card : ℝ)
    let X := ⌊(N : ℝ)^((4 : ℝ)/15)⌋₊
    (∑ p ∈ (range (X+1)).filter Nat.Prime, ((p*p : ℕ) : ℝ) *
      ∑ h ∈ range (p*p), (((A.filter (fun a => a % (p*p) = h)).card : ℝ) -
        Z / ((p*p : ℕ) : ℝ))^2) ≤
      (N : ℝ)^η * ((N : ℝ)*Z + (N : ℝ)^((64 : ℝ)/75)*Z^((6 : ℝ)/5))

/-- A subpower-loss lower bound for the prime count at the same scale. -/
def H2 : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop,
    (N : ℝ)^((4 : ℝ)/15-η) ≤
      (((range (⌊(N : ℝ)^((4 : ℝ)/15)⌋₊+1)).filter Nat.Prime).card : ℝ)

lemma variance_lower (A : Finset ℕ) (hs : ∀ n ∈ A + A, Squarefree n) (p : ℕ) (hp : p.Prime) :
    (A.card : ℝ)^2 / 2 ≤ ((p*p : ℕ) : ℝ) *
      ∑ h ∈ range (p*p), (((A.filter (fun a => a % (p*p) = h)).card : ℝ) -
        A.card / ((p*p : ℕ) : ℝ))^2 := by
  classical
  let q := p*p
  have hq : 0 < q := Nat.mul_pos hp.pos hp.pos
  let S := (range q).filter (fun h => (A.filter (fun a => a % q = h)).Nonempty)
  let E := range q \ S
  have hnot (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) : ¬ q ∣ a+b :=
    Nat.squarefree_iff_prime_squarefree.mp (hs _ (Finset.add_mem_add ha hb)) p hp
  have hSE : S.card ≤ E.card := by
    apply Finset.card_le_card_of_injOn (fun h => q-h)
    · intro h hh
      obtain ⟨hr, a, ha⟩ := Finset.mem_filter.mp hh
      obtain ⟨ha, hares⟩ := Finset.mem_filter.mp ha
      have hhq := Finset.mem_range.mp hr
      have hhpos : h ≠ 0 := by
        intro he
        have hd : q ∣ a := Nat.dvd_of_mod_eq_zero (hares.trans he)
        exact hnot a a ha ha (dvd_add hd hd)
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_range.mpr (by dsimp; omega), ?_⟩
      intro hin
      obtain ⟨_,b,hb⟩ := Finset.mem_filter.mp hin
      obtain ⟨hb,hbres⟩ := Finset.mem_filter.mp hb
      apply hnot a b ha hb
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod,hares,hbres]
      dsimp
      rw [show h+(q-h)=q by omega, Nat.mod_self]
    · intro a ha b hb hab
      have ha' := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
      have hb' := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
      dsimp at hab
      omega
  have hsub : S ⊆ range q := Finset.filter_subset _ _
  have he : E.card + S.card = q := by
    simpa [E] using Finset.card_sdiff_add_card_eq_card hsub
  have heR : (q : ℝ) ≤ 2*(E.card : ℝ) := by exact_mod_cast (show q ≤ 2*E.card by omega)
  let w (h : ℕ) : ℝ := (((A.filter (fun a => a % q = h)).card : ℝ) - A.card/(q:ℝ))^2
  have hempty h (hh : h ∈ E) : w h = ((A.card:ℝ)/(q:ℝ))^2 := by
    obtain ⟨hr,hs'⟩ := Finset.mem_sdiff.mp hh
    have h0 : A.filter (fun a => a % q = h) = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      exact fun H => hs' (Finset.mem_filter.mpr ⟨hr,H⟩)
    simp [w,h0]
  have hsum : (E.card : ℝ) * ((A.card:ℝ)/(q:ℝ))^2 ≤ ∑ h ∈ range q, w h := by
    calc
      _ = ∑ h ∈ E, w h := by simp only [Finset.sum_congr rfl hempty, sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun i _ _ => sq_nonneg _)
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  change (A.card : ℝ)^2 / 2 ≤ (q:ℝ) * ∑ h ∈ range q, w h
  calc
    _ = (q:ℝ) * ((q:ℝ)/2 * ((A.card:ℝ)/(q:ℝ))^2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right (by linarith : (q:ℝ)/2 ≤ E.card)
      (sq_nonneg _)).trans hsum) hqR.le
lemma balance (N Z V P η ε : ℝ) (hn : 1 ≤ N) (hz : 0 < Z) (he : 0 < ε)
    (hη : η = ε/8) (hg : 5 ≤ N^η) (hprime : N^((4:ℝ)/15-η) ≤ P)
    (hl : P*(Z^2/2) ≤ V)
    (hu : V ≤ N^η*(N*Z + N^((64:ℝ)/75)*Z^((6:ℝ)/5))) :
    Z ≤ N^((11:ℝ)/15+ε) := by
  by_contra! hZ
  have hn0 : 0 < N := by linarith
  let B := N^((4:ℝ)/15-2*η)
  have hB : 0 < B := Real.rpow_pos_of_pos hn0 _
  have h1 : N^η*N ≤ B*Z := by
    calc
      N^η*N = N^(η+1) := by rw [Real.rpow_add hn0, Real.rpow_one]
      _ ≤ N^(((4:ℝ)/15-2*η) + ((11:ℝ)/15+ε)) :=
        Real.rpow_le_rpow_of_exponent_le hn (by linarith)
      _ = B*N^((11:ℝ)/15+ε) := Real.rpow_add hn0 _ _
      _ ≤ B*Z := mul_le_mul_of_nonneg_left hZ.le hB.le
  have h2 : N^η*N^((64:ℝ)/75) ≤ B*Z^((4:ℝ)/5) := by
    calc
      _ = N^(η+64/75) := (Real.rpow_add hn0 _ _).symm
      _ ≤ N^(((4:ℝ)/15-2*η) + ((11:ℝ)/15+ε)*(4/5)) :=
        Real.rpow_le_rpow_of_exponent_le hn (by linarith)
      _ = B*(N^((11:ℝ)/15+ε))^((4:ℝ)/5) := by rw [Real.rpow_add hn0, Real.rpow_mul hn0.le]
      _ ≤ B*Z^((4:ℝ)/5) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hZ.le (by norm_num)) hB.le
  have hz2 : Z^((4:ℝ)/5)*Z^((6:ℝ)/5) = Z^2 := by
    rw [← Real.rpow_add hz, show (4:ℝ)/5+6/5 = (2:ℝ) by norm_num, Real.rpow_two]
  have hv : V ≤ 2*(B*Z^2) := calc
    _ ≤ _ := hu
    _ = (N^η*N)*Z + (N^η*N^((64:ℝ)/75))*Z^((6:ℝ)/5) := by ring
    _ ≤ (B*Z)*Z + (B*Z^((4:ℝ)/5))*Z^((6:ℝ)/5) :=
      add_le_add (mul_le_mul_of_nonneg_right h1 hz.le)
        (mul_le_mul_of_nonneg_right h2 (by positivity))
    _ = 2*(B*Z^2) := by rw [mul_assoc B (Z^((4:ℝ)/5)),hz2]; ring
  have hP : 5*B ≤ P := calc
    _ ≤ N^η * B := mul_le_mul_of_nonneg_right hg hB.le
    _ = N^((4:ℝ)/15-η) := by
      dsimp [B]
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    _ ≤ _ := hprime
  have hpV := (mul_le_mul_of_nonneg_right hP (show 0 ≤ Z^2/2 by positivity)).trans hl
  nlinarith [mul_pos hB (sq_pos_of_pos hz)]

theorem main : H1 → H2 → type_of% @Erdos1109.erdos_1109.variants.konyagin_upper := by
  classical
  intro hs hp ε hε
  let η := ε/8
  have hη : 0 < η := by dsimp [η]; positivity
  have hg : Tendsto (fun N : ℕ => (N:ℝ)^η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [hs η hη, hp η hη, hg.eventually_ge_atTop 5, eventually_ge_atTop (1:ℕ)]
    with N hlarge hpr hgrow hn
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  apply (Nat.le_floor_iff (by positivity)).mp
  unfold Erdos1109.f
  apply csSup_le
  · exact ⟨0, ∅, by simp, by simp, rfl⟩
  intro k hk
  obtain ⟨A,hA,hS,rfl⟩ := hk
  apply Nat.le_floor
  by_cases hzero : A.card = 0
  · simp [hzero,Real.rpow_nonneg]
  let X := ⌊(N : ℝ)^((4:ℝ)/15)⌋₊
  let primes := (range (X+1)).filter Nat.Prime
  let Z := (A.card : ℝ)
  let V (p : ℕ) := ((p*p : ℕ) : ℝ) *
    ∑ h ∈ range (p*p), (((A.filter (fun a => a % (p*p) = h)).card : ℝ) -
      Z / ((p*p : ℕ) : ℝ))^2
  have hlow : (primes.card : ℝ) * (Z^2/2) ≤ ∑ p ∈ primes, V p := by
    calc
      _ = ∑ _p ∈ primes, Z^2/2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun p h => variance_lower A hS p (Finset.mem_filter.mp h).2)
  exact balance (N:ℝ) Z _ _ η ε (by exact_mod_cast hn)
    (by dsimp [Z]; exact_mod_cast Nat.pos_of_ne_zero hzero) hε rfl hgrow hpr hlow (hlarge A hA)

end OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1
