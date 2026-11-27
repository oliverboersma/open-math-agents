import FormalConjectures.ErdosProblems.«692»
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# A finite search for a maximizing endpoint in Erdős problem 692

Every interval has a computable rational score obtained by counting residues
modulo a factorial. Two explicit factorials give a uniform cutoff for the
search. If both gcds exceed their respective thresholds, they witness two
different divisors. The exceptional residue classes are bounded using Euler's
totient and the harmonic sum.
-/

namespace DivScan

open Finset Filter
open scoped Topology

def goodDivs (n m x : ℕ) := (Finset.Ioo n m).filter (· ∣ x)

def good (n m x : ℕ) : Prop := (goodDivs n m x).card = 1

instance (n m : ℕ) : DecidablePred (good n m) := fun x => inferInstanceAs (Decidable ((goodDivs n m x).card = 1))

lemma good_set (n m : ℕ) : Erdos692.exactlyOneDivisorIn n m = {x | good n m x} := by
  ext x
  change _ = 1 ↔ _ = 1
  have h : {d ∈ Set.Ioo n m | d ∣ x} = (goodDivs n m x : Set ℕ) := by
    ext d
    simp [goodDivs]
  rw [h, Set.ncard_coe_finset]

lemma good_periodic (n m : ℕ) : Function.Periodic (good n m) m.factorial := by
  intro x
  unfold good
  congr 2
  ext d
  simp only [goodDivs, mem_filter, mem_Ioo]
  constructor
  · rintro ⟨hd,hx⟩
    exact ⟨hd,(Nat.dvd_add_iff_left (Nat.dvd_factorial (by omega) hd.2.le)).mpr hx⟩
  · rintro ⟨hd,hx⟩
    exact ⟨hd,dvd_add hx (Nat.dvd_factorial (by omega) hd.2.le)⟩

lemma count_period (p : ℕ → Prop) [DecidablePred p] {d : ℕ}
    (hp : Function.Periodic p d) (k : ℕ) : Nat.count p (k*d) = k * Nat.count p d := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Nat.succ_mul, Nat.count_add' p, ← ih]
    congr 1
    apply le_antisymm <;> apply Nat.count_mono_left <;> intro x _ hx <;> simpa only [hp x] using hx

lemma density_eq (p : ℕ → Prop) [DecidablePred p] {d : ℕ} (hd : 0 < d)
    (hp : Function.Periodic p d) {v : ℝ} (hv : Set.HasDensity {x | p x} v) :
    v = (Nat.count p d : ℝ) / d := by
  have hlim : Tendsto (fun k : ℕ => k*d) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_right k hd) tendsto_id
  apply tendsto_nhds_unique (hv.comp hlim)
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop 0] with k hk
  change _ = Set.partialDensity {x | p x} Set.univ (k*d)
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat]
  have he : ({x | p x} ∩ Set.Iio (k*d)).ncard = Nat.count p (k*d) := by
    rw [Nat.count_eq_card_filter_range, ← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [and_comm]
  rw [he, count_period p hp, Nat.cast_mul, Nat.cast_mul]
  field_simp

/-- Exact rational density found by enumerating a full period. -/
def score (n m : ℕ) : ℚ := (Nat.count (good n m) m.factorial : ℚ) / m.factorial

lemma score_eq (n m : ℕ) {v : ℝ} (hv : Erdos692.IsDelta₁ n m v) :
    v = (score n m : ℝ) := by
  rw [Erdos692.IsDelta₁,good_set] at hv
  simpa [score] using density_eq (good n m) (Nat.factorial_pos m) (good_periodic n m) hv

lemma totient_mul_le (a b : ℕ) : (a*b).totient ≤ a*b.totient := by
  rw [Nat.totient_eq_card_coprime, ← Nat.count_eq_card_filter_range]
  calc Nat.count _ (a*b) ≤ Nat.count (Nat.Coprime b) (a*b) := by
         apply Nat.count_mono_left
         intro x _ hx
         exact hx.coprime_dvd_left (dvd_mul_left b a)
       _ = _ := by rw [count_period _ (Nat.periodic_coprime b), Nat.count_eq_card_filter_range, ← Nat.totient_eq_card_coprime]

lemma totient_div_ge {L d : ℕ} (hd : d ∣ L) : L.totient ≤ d*(L/d).totient := by
  simpa only [Nat.mul_div_cancel' hd] using totient_mul_le d (L/d)

/-- Every positive integer up to K divides K!, so the corresponding gcd fibers
together have at least H_K times the size of the coprime fiber. -/
lemma factorial_sieve (K : ℕ) : (harmonic K : ℝ) * K.factorial.totient ≤ K.factorial := by
  let L := K.factorial
  have hL : 0 < L := Nat.factorial_pos K
  rw [harmonic_eq_sum_Icc, Rat.cast_sum, Finset.sum_mul]
  calc ∑ d ∈ Icc 1 K, ((↑(d : ℚ)⁻¹ : ℝ) * L.totient) ≤
        ∑ d ∈ Icc 1 K, ((L/d).totient : ℝ) := by
          apply sum_le_sum
          intro d hd
          obtain ⟨hd1,hd2⟩ := mem_Icc.mp hd
          have hdd : d ∣ L := Nat.dvd_factorial hd1 hd2
          have hpos : (0:ℝ)<d := by exact_mod_cast hd1
          rw [Rat.cast_inv, Rat.cast_natCast, inv_mul_eq_div, div_le_iff₀ hpos]
          exact_mod_cast (mul_comm d (L/d).totient ▸ totient_div_ge hdd)
       _ ≤ ∑ d ∈ L.divisors, ((L/d).totient : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro d hd
            exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial (mem_Icc.mp hd).1 (mem_Icc.mp hd).2, hL.ne'⟩
          · intros; positivity
       _ = _ := by
          rw [← Nat.cast_sum, Nat.sum_div_divisors L Nat.totient, Nat.sum_totient]

def scale (a w : ℕ) : ℕ := (3 ^ (2*(a+1)*w)).factorial

lemma scale_pos (a w : ℕ) : 0 < scale a w := Nat.factorial_pos _

lemma scale_bound (a w : ℕ) : (2*(a+1)*w) * (scale a w).totient ≤ scale a w := by
  let r := 2*(a+1)*w
  let K := 3^r
  have hk : (r : ℝ) ≤ Real.log (K:ℝ) := by
    dsimp [K]
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    nlinarith [Real.log_three_gt_d9, (Nat.cast_nonneg r : (0:ℝ) ≤ r)]
  have hk' : Real.log (K:ℝ) ≤ Real.log ((K+1:ℕ):ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ K)
  have hh := (hk.trans hk').trans (log_add_one_le_harmonic K)
  have he := (mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg K.factorial.totient)).trans (factorial_sieve K)
  exact_mod_cast he

def small (L a x : ℕ) : Prop := L.gcd x ≤ a

instance (L a : ℕ) : DecidablePred (small L a) := fun x => inferInstanceAs (Decidable (L.gcd x ≤ a))

lemma small_count (L a : ℕ) (hL : 0 < L) :
    Nat.count (small L a) L ≤ (a+1)*L.totient := by
  rw [Nat.count_eq_card_filter_range]
  let s := (range L).filter (small L a)
  have hf : ∀ x ∈ s, L.gcd x ∈ range (a+1) := by
    intro x hx
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hx).2)
  calc s.card = ∑ d ∈ range (a+1), (s.filter (fun x => L.gcd x = d)).card :=
          card_eq_sum_card_fiberwise hf
       _ ≤ ∑ _d ∈ range (a+1), L.totient := by
          apply sum_le_sum
          intro d _
          by_cases hd : d ∣ L
          · calc _ ≤ ((range L).filter (fun x => L.gcd x = d)).card := by
                       apply card_le_card
                       intro x hx
                       exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hx).1).1,(mem_filter.mp hx).2⟩
                   _ = (L/d).totient := (Nat.totient_div_of_dvd hd).symm
                   _ ≤ _ := Nat.le_of_dvd (Nat.totient_pos.mpr hL) (Nat.totient_dvd_of_dvd (Nat.div_dvd_of_dvd hd))
          · have he : s.filter (fun x => L.gcd x = d) = ∅ := by
              apply filter_eq_empty_iff.mpr
              intro x _ hx
              exact hd (hx ▸ Nat.gcd_dvd_left L x)
            simp [he]
       _ = _ := by simp

lemma small_count_mul (a w N : ℕ) (h : scale a w ∣ N) :
    (2*w) * Nat.count (small (scale a w) a) N ≤ N := by
  let L := scale a w
  have hp : Function.Periodic (small L a) L := by
    intro x
    simp only [small, Nat.gcd_add_self_right]
  obtain ⟨k,hk⟩ := h
  change (2*w)*Nat.count (small L a) N ≤ N
  change N = L*k at hk
  rw [hk, Nat.mul_comm L k, count_period _ hp]
  have he := Nat.mul_le_mul_left (2*w) (small_count L a (scale_pos a w))
  have hb := scale_bound a w
  change (2*(a+1)*w)*L.totient ≤ L at hb
  calc (2*w)*(k*Nat.count (small L a) L) = k*((2*w)*Nat.count (small L a) L) := by ring
       _ ≤ k*((2*w)*((a+1)*L.totient)) := Nat.mul_le_mul_left k he
       _ = k*((2*(a+1)*w)*L.totient) := by ring
       _ ≤ k*L := Nat.mul_le_mul_left k hb

def bound (n : ℕ) : ℕ := n+2 + scale n (n+1) + scale (scale n (n+1)) (n+1)

/-- Outside both exceptional sets, gcd(A,x) and gcd(B,x) lie in disjoint
subintervals of the divisor window. -/
lemma good_cover {n m x : ℕ} (hm : bound n < m) (hx : good n m x) :
    small (scale n (n+1)) n x ∨ small (scale (scale n (n+1)) (n+1)) (scale n (n+1)) x := by
  let A := scale n (n+1)
  let B := scale A (n+1)
  change n+2+A+B < m at hm
  change A.gcd x ≤ n ∨ B.gcd x ≤ A
  by_contra! h
  have hA := Nat.gcd_le_left x (scale_pos n (n+1))
  have hB := Nat.gcd_le_left x (scale_pos A (n+1))
  change A.gcd x ≤ A at hA
  change B.gcd x ≤ B at hB
  have ha : A.gcd x ∈ goodDivs n m x := mem_filter.mpr ⟨mem_Ioo.mpr ⟨h.1,by omega⟩,Nat.gcd_dvd_right _ _⟩
  have hb : B.gcd x ∈ goodDivs n m x := mem_filter.mpr ⟨mem_Ioo.mpr ⟨by omega,by omega⟩,Nat.gcd_dvd_right _ _⟩
  obtain ⟨d,hd⟩ := Finset.card_eq_one.mp hx
  rw [hd,Finset.mem_singleton] at ha hb
  omega

lemma tail {n m : ℕ} (hm : bound n < m) :
    (Nat.count (good n m) m.factorial) * (n+1) ≤ m.factorial := by
  let A := scale n (n+1)
  let B := scale A (n+1)
  let N := m.factorial
  have hm' : n+2+A+B < m := hm
  have ha := small_count_mul n (n+1) N (Nat.dvd_factorial (scale_pos _ _) (by change A ≤ m; omega))
  have hb := small_count_mul A (n+1) N (Nat.dvd_factorial (scale_pos _ _) (by change B ≤ m; omega))
  have hab : Nat.count (good n m) N ≤ Nat.count (small A n) N + Nat.count (small B A) N := by
    simp only [Nat.count_eq_card_filter_range]
    apply le_trans _ (Finset.card_union_le _ _)
    apply card_le_card
    intro x hx
    obtain ⟨hx0,hx1⟩ := mem_filter.mp hx
    rcases good_cover hm hx1 with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨hx0,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hx0,h⟩)
  change 2*(n+1)*Nat.count (small A n) N ≤ N at ha
  change 2*(n+1)*Nat.count (small B A) N ≤ N at hb
  change Nat.count (good n m) N * (n+1) ≤ N
  nlinarith [Nat.mul_le_mul_right (n+1) hab]

lemma baseline (n : ℕ) {v : ℝ} (hv : Erdos692.IsDelta₁ n (n+2) v) :
    v = 1 / (n+1 : ℕ) := by
  have hs : Finset.Ioo n (n+2) = {n+1} := by
    ext d
    simp only [mem_Ioo, mem_singleton]
    omega
  have he : {x | good n (n+2) x} = {x : ℕ | n+1 ∣ x} := by
    ext x
    by_cases h : n+1 ∣ x <;> simp [good, goodDivs, hs, Finset.filter_singleton, h]
  rw [Erdos692.IsDelta₁,good_set,he] at hv
  have hp : Function.Periodic (fun x : ℕ => n+1 ∣ x) (n+1) := by
    intro x
    simp
  have hc : Nat.count (fun x : ℕ => n+1 ∣ x) (n+1) = 1 := by
    rw [Nat.count_eq_card_filter_range, Finset.card_eq_one]
    refine ⟨0,?_⟩
    ext x
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨hx,h⟩
      by_contra hn
      exact (Nat.not_le_of_gt hx) (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h)
    · rintro rfl
      exact ⟨by omega,dvd_zero _⟩
  simpa only [hc, Nat.cast_one] using density_eq _ (Nat.succ_pos n) hp hv

def candidates (n : ℕ) : List ℕ :=
  List.range' (n+2) (bound n + 1 - (n+2))

lemma mem_candidates (n m : ℕ) : m ∈ candidates n ↔ n+1 < m ∧ m ≤ bound n := by
  have hb : n+2 ≤ bound n := by unfold bound; omega
  simp only [candidates,List.mem_range'_1]
  omega

end DivScan

/-- Return the earliest endpoint with largest rational score in the bounded list. -/
def OMA.answer (n : ℕ) : ℕ :=
  ((DivScan.candidates n).argmax (DivScan.score n)).getD (n+2)

theorem OMA.solution : Erdos692.erdos_692.parts.ii.answer = OMA.answer → type_of% @Erdos692.erdos_692.parts.ii := by
  intro hans n δ hδ
  rw [hans]
  have hbase : n+2 ∈ DivScan.candidates n := (DivScan.mem_candidates ..).mpr ⟨by omega,by unfold DivScan.bound; omega⟩
  have hbest : OMA.answer n ∈ (DivScan.candidates n).argmax (DivScan.score n) := by
    unfold OMA.answer
    cases h : (DivScan.candidates n).argmax (DivScan.score n) with
    | none => simp [List.argmax_eq_none.mp h] at hbase
    | some b => simp
  have hdomain := (DivScan.mem_candidates ..).mp (List.argmax_mem hbest)
  have hscan {m : ℕ} (hm : m ∈ DivScan.candidates n) : δ n m ≤ δ n (OMA.answer n) := by
    rw [DivScan.score_eq _ _ (hδ n m), DivScan.score_eq _ _ (hδ n (OMA.answer n))]
    exact_mod_cast List.le_of_mem_argmax hm hbest
  refine ⟨⟨OMA.answer n,hdomain.1,rfl⟩,?_⟩
  rintro _ ⟨m,hm,rfl⟩
  by_cases h : m ≤ DivScan.bound n
  · exact hscan ((DivScan.mem_candidates ..).mpr ⟨hm,h⟩)
  · apply le_trans _ (hscan hbase)
    rw [DivScan.baseline n (hδ n (n+2)),DivScan.score_eq n m (hδ n m)]
    simp only [DivScan.score, Rat.cast_div, Rat.cast_natCast]
    apply (div_le_div_iff₀ (by exact_mod_cast Nat.factorial_pos m) (by positivity)).mpr
    rw [one_mul]
    exact_mod_cast DivScan.tail (Nat.lt_of_not_ge h)
