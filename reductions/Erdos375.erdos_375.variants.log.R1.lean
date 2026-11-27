import FormalConjectures.ErdosProblems.«375»
import Mathlib

/-! Ramachandra, Shorey and Tijdeman, J. Reine Angew. Math. 273 (1975),
109–124. A minimal obstruction to Hall's theorem has only primes smaller
than the block length (their Lemmas 2–3). Section 2 produces a very small
linear form in two logarithms from such an obstruction. Section 3 bounds
this linear form from below. We separate the scalar choice of the parameter
in the latter bound and absorb all finite endpoints. -/
namespace OMA.R_Erdos375_erdos_375_variants_log_R1

open Finset Filter Real

/-- The two-logarithm configuration from the combinatorial argument of
section 2, with the height scale allowed to be an arbitrarily small power. -/
def H1 : Prop := ∀ b : ℝ, 0 < b → ∀ S₀ : ℝ, ∃ c > (0:ℝ), ∀ᶠ n : ℕ in atTop,
  ∀ k : ℕ, (k:ℝ) < c*(log n/log (log n))^3 →
  ∀ J : Finset (Fin k),
  let P := J.biUnion (fun i => (n+i.val+1).primeFactors)
  P.card < J.card → (∀ p ∈ P, p < k) →
  ∃ (S : ℝ) (u v : ℚ) (m : ℤ), S₀ ≤ S ∧ S ≤ (n:ℝ)^b ∧ 0 < u ∧ 0 < v ∧
    (u.num.natAbs+u.den:ℕ) ≤ (log S)^16 ∧ ((v.num.natAbs+v.den:ℕ):ℝ) ≤ S ∧
    2*log S/log (log S) ≤ |(m:ℝ)| ∧ |(m:ℝ)| ≤ (log S)^16 ∧
    |log (v:ℝ)| ≤ (log S)^(3/4:ℝ) ∧
    0 < |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| ∧ |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| < (n:ℝ)^(-(1/2:ℝ))

/-- The two-logarithm theorem of section 3, with height exponents A=B=16. -/
def H2 : Prop := ∃ D > (0:ℝ), ∀ S : ℝ, 27 < S → ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
  ∀ (u v : ℚ) (m : ℤ), 0 < u → 0 < v →
  ((u.num.natAbs+u.den:ℕ):ℝ) ≤ (log S)^16 → ((v.num.natAbs+v.den:ℕ):ℝ) ≤ S →
  2*log S/log (log S) ≤ |(m:ℝ)| → |(m:ℝ)| ≤ (log S)^16 →
  |log (v:ℝ)| ≤ log S/log (log S)*exp (-(log (log S))^z) →
  0 < |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| →
  exp (-D*log S*(log (log S))^(4-4*z)) ≤ |(m:ℝ)*log (u:ℝ)-log (v:ℝ)|

/-- An elementary choice of the free exponent in the logarithm estimate. -/
def H3 : Prop := ∃ K > (0:ℝ), ∀ᶠ S : ℝ in atTop, ∃ z : ℝ, 0 ≤ z ∧ z ≤ 1 ∧
  (log S)^(3/4:ℝ) ≤ log S/log (log S)*exp (-(log (log S))^z) ∧
  (log (log S))^(4-4*z) ≤ K

lemma minimal_family {n k : ℕ}
    (bad : ¬ ∃ p : Fin k → ℕ, Function.Injective p ∧ ∀ i, p i ∈ (n+i.val+1).primeFactors) :
    ∃ J : Finset (Fin k), let P := J.biUnion (fun i => (n+i.val+1).primeFactors)
      P.card < J.card ∧ ∀ p ∈ P, p < k := by
  classical
  let F (i : Fin k) := (n+i.val+1).primeFactors
  have hh : ¬ ∀ s : Finset (Fin k), s.card ≤ (s.biUnion F).card :=
    fun h => bad ((all_card_le_biUnion_card_iff_exists_injective F).mp h)
  push_neg at hh
  let fam := univ.filter fun s : Finset (Fin k) => (s.biUnion F).card < s.card
  have non : fam.Nonempty := by
    obtain ⟨s,hs⟩ := hh
    exact ⟨s,mem_filter.mpr ⟨mem_univ _,hs⟩⟩
  obtain ⟨J,hJ,least⟩ := exists_min_image fam card non
  have defic : (J.biUnion F).card < J.card := (mem_filter.mp hJ).2
  refine ⟨J,defic,?_⟩
  intro p hp
  change p ∈ J.biUnion F at hp
  obtain ⟨i,hi,hpi⟩ := mem_biUnion.mp hp
  by_contra! large
  have unique (j : Fin k) (h : p ∈ F j) : i=j := by
    have di : p ∣ n+i.val+1 := Nat.dvd_of_mem_primeFactors hpi
    have dj : p ∣ n+j.val+1 := Nat.dvd_of_mem_primeFactors h
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with hlt|he|hgt
    · have d : p ∣ j.val-i.val := by convert Nat.dvd_sub dj di using 1 <;> omega
      have := Nat.le_of_dvd (show 0 < (j.val-i.val : ℕ) by omega) d
      omega
    · exact he
    · have d : p ∣ i.val-j.val := by convert Nat.dvd_sub di dj using 1 <;> omega
      have := Nat.le_of_dvd (show 0 < (i.val-j.val : ℕ) by omega) d
      omega
  let J' := J.erase i
  have sub : J'.biUnion F ⊆ (J.biUnion F).erase p := by
    intro q hq
    obtain ⟨j,hj,hq⟩ := mem_biUnion.mp hq
    obtain ⟨ne,jm⟩ := mem_erase.mp hj
    exact mem_erase.mpr ⟨fun e => ne ((unique j (e ▸ hq)).symm),mem_biUnion.mpr ⟨j,jm,hq⟩⟩
  have cl := card_le_card sub
  have pin : p ∈ J.biUnion F := mem_biUnion.mpr ⟨i,hi,hpi⟩
  rw [card_erase_of_mem pin] at cl
  have cj : J'.card = J.card-1 := card_erase_of_mem hi
  have jpos := card_pos.mpr (show J.Nonempty from ⟨i,hi⟩)
  have ppos := card_pos.mpr (show (J.biUnion F).Nonempty from ⟨p,pin⟩)
  have sm : J' ∈ fam := mem_filter.mpr ⟨mem_univ _,by omega⟩
  have := least J' sm
  omega

theorem main : H1 → H2 → H3 → type_of% @Erdos375.erdos_375.variants.log := by
  classical
  intro extract lower adjust
  obtain ⟨D,hd,hl⟩ := lower
  obtain ⟨K,hk,hadj⟩ := adjust
  obtain ⟨S₀,hS⟩ := eventually_atTop.mp (hadj.and (eventually_gt_atTop (27:ℝ)))
  let b := 1/(2*D*K)
  have bp : 0 < b := by dsimp [b]; positivity
  obtain ⟨c,hc,hex⟩ := extract b bp S₀
  let w := fun n : ℕ => (log n/log (log n))^3
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hex.and (eventually_ge_atTop (2:ℕ)))
  let B := 1 + ∑ i ∈ range N, |w i|
  have bge : 1 ≤ B := by dsimp [B]; linarith [sum_nonneg (s := range N) (fun i _ => abs_nonneg (w i))]
  have bpos : 0 < B := by linarith
  refine ⟨min c (1/B),lt_min hc (by positivity),?_⟩
  intro n k height comp
  change (k:ℝ) < min c (1/B)*w n at height
  have wpos : 0 < w n := by
    by_contra! hn
    have := mul_nonpos_of_nonneg_of_nonpos (le_min hc.le (by positivity : (0:ℝ) ≤ 1/B)) hn
    linarith [Nat.cast_nonneg (α := ℝ) k]
  by_cases early : n < N
  · have term := single_le_sum (f := fun i : ℕ => |w i|) (fun i _ => abs_nonneg (w i)) (mem_range.mpr early)
    have wn : w n < B := by dsimp [B]; linarith [le_abs_self (w n)]
    have sml := mul_le_mul_of_nonneg_right (min_le_right c (1/B)) wpos.le
    have kk : (k:ℝ) < 1 := by
      calc
        _ < _ := height
        _ ≤ _ := sml
        _ < 1 := by rw [one_div_mul_eq_div,div_lt_one bpos]; exact wn
    have klt : k < 1 := by exact_mod_cast kk
    have : k=0 := by omega
    subst k
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  obtain ⟨huse,hn⟩ := hN n (Nat.le_of_not_gt early)
  have hsize := height.trans_le (mul_le_mul_of_nonneg_right (min_le_left c _) wpos.le)
  suffices h : ∃ p : Fin k → ℕ, Function.Injective p ∧ ∀ i, p i ∈ (n+i.val+1).primeFactors by
    obtain ⟨p,inj,h⟩ := h
    exact ⟨p,inj,fun i => ⟨Nat.prime_of_mem_primeFactors (h i),Nat.dvd_of_mem_primeFactors (h i)⟩⟩
  by_contra bad
  obtain ⟨J,defic,small⟩ := minimal_family bad
  obtain ⟨S,u,v,m,Sge,Su,up,vp,uh,vh,ml,mu,lv,Lp,Lu⟩ := huse k hsize J defic small
  obtain ⟨⟨z,z0,z1,lim,weight⟩,Sbig⟩ := hS S Sge
  have lp := log_pos (show 1 < S by linarith)
  have nn : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have low := hl S Sbig z z0 z1 u v m up vp uh vh ml mu (lv.trans lim) Lp
  have contra : (n:ℝ)^(-(1/2:ℝ)) ≤ exp (-D*log S*(log (log S))^(4-4*z)) := by
    calc
      _ = ((n:ℝ)^b)^(-(D*K)) := by rw [← rpow_mul nn.le]; congr 1; dsimp [b]; field_simp
      _ ≤ S^(-(D*K)) := rpow_le_rpow_of_nonpos (by linarith) Su (neg_nonpos.mpr (mul_nonneg hd.le hk.le))
      _ ≤ _ := by
        rw [rpow_def_of_pos (by linarith : 0 < S),exp_le_exp]
        nlinarith [mul_nonneg (mul_nonneg hd.le lp.le) (sub_nonneg.mpr weight)]
  exact (not_le_of_gt Lu) (contra.trans low)

end OMA.R_Erdos375_erdos_375_variants_log_R1
