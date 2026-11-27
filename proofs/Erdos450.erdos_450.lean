import FormalConjectures.ErdosProblems.«450»
import Mathlib

/-!
# Exact window thresholds for integers with a divisor between n and 2n

For fixed n the divisibility pattern is periodic. Write the number of interior
positions as qP+r, where P is the least common multiple of the eligible divisors.
At each starting residue the excess over the permitted count is affine in q.
Solving that inequality and taking a finite maximum gives the exact threshold,
including the cases in which arbitrarily long windows violate the density bound.
-/

section
open Finset
namespace OMA.Window

/-- A common period of all divisibility conditions in the window. -/
def period (n : ℕ) : ℕ := (Ioo n (2 * n)).lcm id

theorem period_pos (n : ℕ) : 0 < period n  := by
  apply Nat.pos_of_ne_zero
  apply Finset.lcm_ne_zero_iff.mpr
  intro d hd
  have := (mem_Ioo.mp hd).1
  change d ≠ 0
  omega

theorem dvd_period {n d : ℕ} (h1 : n < d) (h2 : d < 2*n) : d ∣ period n :=
  Finset.dvd_lcm (f := id) (Finset.mem_Ioo.mpr ⟨h1, h2⟩)

theorem medium_periodic (n : ℕ) : Function.Periodic (Erdos450.HasMediumDivisor n) (period n) := by
  intro m
  apply propext
  constructor
  · rintro ⟨d, hn, hd, hdiv⟩
    have hP : d ∣ period n := dvd_period hn hd
    exact ⟨d, hn, hd, (Nat.dvd_add_iff_left hP).mpr hdiv⟩
  · rintro ⟨d, hn, hd, hdiv⟩
    exact ⟨d, hn, hd, dvd_add hdiv (dvd_period hn hd)⟩

/-- A finite divisor test for each residue. -/
def occupied (n m : ℕ) : Prop := ∃ d ∈ Ioo n (2*n), d ∣ m

instance (n m : ℕ) : Decidable (occupied n m) :=
  inferInstanceAs (Decidable (∃ d ∈ Ioo n (2*n), d ∣ m))

theorem occupied_iff (n m : ℕ) : occupied n m ↔ Erdos450.HasMediumDivisor n m := by
  unfold occupied Erdos450.HasMediumDivisor
  simp only [mem_Ioo]
  aesop

/-- The number of occupied positions among the next L integers. -/
def block (n x L : ℕ) : ℕ :=
  ∑ i ∈ range L, if occupied n (x + i + 1) then 1 else 0

theorem local_eq (n x L : ℕ) : Erdos450.localCount n x (L + 1) = block n x L := by
  classical
  rw [block, Finset.sum_boole]
  unfold Erdos450.localCount
  symm
  apply Finset.card_bij (fun i _ => x + i + 1)
  · intro i hi
    simp only [mem_filter, mem_range, mem_Ioo] at hi ⊢
    exact ⟨⟨by omega, by omega⟩, (occupied_iff _ _).mp hi.2⟩
  · intro i hi j hj he; omega
  · intro v hv
    simp only [mem_filter, mem_Ioo] at hv
    refine ⟨v - (x + 1), ?_, by omega⟩
    simp only [mem_filter, mem_range]
    exact ⟨by omega, by rw [show x + (v - (x+1)) + 1 = v by omega]; exact (occupied_iff _ _).mpr hv.2⟩

theorem block_periodic (n L : ℕ) : Function.Periodic (fun x => block n x L) (period n) := by
  classical
  intro x
  dsimp only
  unfold block
  apply sum_congr rfl
  intro i hi
  rw [show x + period n + i + 1 = (x + i + 1) + period n by omega]
  simp only [occupied_iff]
  rw [medium_periodic n (x + i + 1)]

theorem block_add (n x a b : ℕ) :
    block n x (a + b) = block n x a + block n (x+a) b := by
  classical
  simp only [block, sum_range_add, Nat.add_assoc]

theorem block_period_decomp (n x q r : ℕ) :
    block n x (q * period n + r) = q * block n x (period n) + block n x r := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hperiod : block n (x + period n) (q * period n + r) = block n x (q * period n + r) := block_periodic n _ x
    rw [Nat.succ_mul, show q * period n + period n + r = period n + (q * period n + r) by omega,
      block_add, hperiod, ih, Nat.succ_mul]
    omega


/-- For a fixed start residue and remainder, the last failing length plus one.
The slope a and intercept b describe the excess over the permitted density. -/
noncomputable def cutoff (P r : ℕ) (a b : ℝ) : ℕ∞ :=
  if a < 0 then ⊤ else if b ≤ 0 then 0 else if a = 0 then ⊤
  else ↑((⌈b / a⌉₊ - 1) * P + r + 2)

theorem cutoff_spec (P r y : ℕ) (hP : 0 < P) (a b : ℝ) :
    cutoff P r a b ≤ (y : ℕ∞) ↔
      ∀ q : ℕ, y ≤ q * P + r + 1 → b ≤ (q : ℝ) * a := by
  by_cases ha : a < 0
  · simp only [cutoff, if_pos ha, (not_le.mpr (ENat.natCast_lt_top y)), false_iff]
    intro h
    obtain ⟨k, hk⟩ := exists_nat_gt ((-b) / (-a))
    let q := max y k
    have hq : y ≤ q * P + r + 1 := by
      have h1 : y ≤ q := le_max_left _ _
      have h2 := Nat.le_mul_of_pos_right q hP
      omega
    have hkq : (k : ℝ) ≤ q := by exact_mod_cast (le_max_right y k)
    have hh := (div_lt_iff₀ (neg_pos.mpr ha)).mp (hk.trans_le hkq)
    linarith [h q hq]
  · by_cases hb : b ≤ 0
    · simp only [cutoff, if_neg ha, if_pos hb, zero_le, true_iff]
      intro q hq
      exact hb.trans (mul_nonneg (Nat.cast_nonneg _) (le_of_not_gt ha))
    · by_cases hzero : a = 0
      · simp only [cutoff, if_neg ha, if_neg hb, if_pos hzero, (not_le.mpr (ENat.natCast_lt_top y)), false_iff]
        intro h
        have h1 := Nat.le_mul_of_pos_right y hP
        have h2 := h y (by omega)
        rw [hzero, mul_zero] at h2
        exact hb h2
      · have hap : 0 < a := lt_of_le_of_ne (le_of_not_gt ha) (Ne.symm hzero)
        let k := ⌈b / a⌉₊
        have hk : 0 < k := Nat.ceil_pos.mpr (div_pos (lt_of_not_ge hb) hap)
        have hg (q : ℕ) : k ≤ q ↔ b ≤ (q : ℝ) * a := by
          dsimp only [k]
          rw [Nat.ceil_le, div_le_iff₀ hap]
        simp only [cutoff, if_neg ha, if_neg hb, if_neg hzero, ENat.natCast_le_natCast]
        change (k - 1) * P + r + 2 ≤ y ↔ _
        constructor
        · intro hy q hq
          apply (hg q).mp
          by_contra! hsmall
          have hmul := Nat.mul_le_mul_right P (show q ≤ k - 1 by omega)
          omega
        · intro h
          by_contra! hsmall
          have hbad := (hg (k - 1)).mpr (h _ (by omega))
          omega

theorem block_inequality (ε : ℝ) (n x q r : ℕ) :
    (block n x (q * period n + r) : ℝ) ≤ ε * (q * period n + r + 1 : ℕ) ↔
      (block n x r : ℝ) - ε * ((r : ℝ) + 1) ≤
        (q : ℝ) * (ε * period n - block n x (period n)) := by
  rw [block_period_decomp]
  push_cast
  constructor <;> intro h <;> nlinarith only [h]

end OMA.Window

/-- The maximum of explicit cutoffs over the starting and length residues.
The complete-period count and every remainder count are finite sums. -/
noncomputable def OMA.answer (ε : ℝ) (n : ℕ) : ℕ∞ :=
  let P := OMA.Window.period n
  Finset.univ.sup fun x : Fin P => Finset.univ.sup fun r : Fin P =>
    OMA.Window.cutoff P r (ε * P - OMA.Window.block n x P)
      (OMA.Window.block n x r - ε * ((r : ℝ) + 1))

namespace OMA.Window

theorem answer_spec (ε : ℝ) (n y : ℕ) :
    OMA.answer ε n ≤ (y : ℕ∞) ↔ ∀ z ≥ y, Erdos450.UniformlySparse ε n z := by
  simp only [OMA.answer, Finset.sup_le_iff, Finset.mem_univ, forall_const, cutoff_spec _ _ _ (period_pos n)]
  constructor
  · intro h z hz x
    cases z with
    | zero =>
      simp [Erdos450.localCount]
    | succ L =>
      let P := period n
      let x' : Fin P := ⟨x % P, Nat.mod_lt _ (period_pos n)⟩
      let r : Fin P := ⟨L % P, Nat.mod_lt _ (period_pos n)⟩
      let q := L / P
      have hL : q * P + (r : ℕ) = L := by
        simpa [q, r, Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div L P)
      have hlen : y ≤ q * P + (r : ℕ) + 1 := by omega
      have hblock := (block_inequality ε n x' q r).mpr (h x' r q hlen)
      rw [show q * period n + (r : ℕ) = L from hL] at hblock
      have hmod : block n x' L = block n x L := (block_periodic n L).map_mod_nat x
      rw [hmod] at hblock
      simpa only [Nat.succ_eq_add_one, local_eq] using hblock
  · intro h x r q hy
    apply (block_inequality ε n x q r).mp
    simpa only [local_eq] using (h _ hy x)

end OMA.Window

theorem OMA.solution : Erdos450.erdos_450.answer = OMA.answer →
    type_of% @Erdos450.erdos_450 := by
  intro ha ε _ n
  rw [ha]
  unfold Erdos450.windowThreshold
  apply le_antisymm
  · generalize h : OMA.answer ε n = K
    induction K using ENat.recTopCoe with
    | top => exact le_top
    | coe y =>
      exact iInf_le_of_le ⟨y, (OMA.Window.answer_spec ε n y).mp h.le⟩ le_rfl
  · exact le_iInf fun y => (OMA.Window.answer_spec ε n y.1).mpr y.2

end
