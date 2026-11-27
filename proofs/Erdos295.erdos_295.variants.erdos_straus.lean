import FormalConjectures.ErdosProblems.«295»
import Mathlib

section R1Section
-- Reduction Erdos295.erdos_295.variants.erdos_straus.R1 of Erdős Problem 295 — erdos straus
-- Credit: @mrmario2202
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-
Splits the Erdős–Straus bounds `-C < k(N) - (e-1)N ≤ O N / log N` into its two halves, each stated
directly about representations `1 = 1/n_1 + ... + 1/n_m` with `N ≤ n_1 < ... < n_m` (no `sInf`).
`main` does the glue: `H2` makes the set defining `k N` nonempty, so `k N` is attained (and `H1`
bounds it below) and is at most the length of the `H2` witness.
- `H1` (elementary lower bound): every such representation has `m > (e-1)N - C`. Since `n_i ≥ N + i`,
  `1 ≤ ∑_{i<m} 1/(N+i) ≤ log((N+m-1)/(N-1))`, so `C = 2` works for `N ≥ 2`.
- `H2` (the Erdős–Straus construction [ErSt71b]): a representation with at most
  `(e-1)N + O N / log N` terms exists for all large `N`.
-/

namespace OMA.Erdos295R1

open Filter

/-- Lower bound: any representation of `1` by distinct unit fractions with denominators `≥ N`
has more than `(e - 1) N - C` terms, for all large `N`. -/
def H1 : Prop :=
  ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (n : Fin m → ℕ),
    (∀ i, N ≤ n i) → StrictMono n → ∑ i, (1 / n i : ℝ) = 1 →
      (Real.exp 1 - 1) * N - C < m

/-- Upper bound (Erdős–Straus): for all large `N` there is a representation of `1` by distinct
unit fractions with denominators `≥ N` using at most `(e - 1) N + O N / log N` terms. -/
def H2 : Prop :=
  ∃ O > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∃ (m : ℕ) (n : Fin m → ℕ),
    (∀ i, N ≤ n i) ∧ StrictMono n ∧ ∑ i, (1 / n i : ℝ) = 1 ∧
      (m : ℝ) ≤ (Real.exp 1 - 1) * N + O * N / Real.log N

theorem main : H1 → H2 → type_of% @Erdos295.erdos_295.variants.erdos_straus := by
  rintro ⟨C, hC, h1⟩ ⟨O, hO, h2⟩
  refine ⟨C, hC, O, hO, ?_⟩
  filter_upwards [h1, h2] with N hN1 hN2
  obtain ⟨m, n, hn, hmono, hsum, hm⟩ := hN2
  have hne : {k | ∃ n : Fin k → ℕ, (∀ i, N ≤ n i) ∧ StrictMono n ∧
      ∑ i, (1 / n i : ℝ) = 1}.Nonempty := ⟨m, n, hn, hmono, hsum⟩
  obtain ⟨n', hn', hmono', hsum'⟩ := Nat.sInf_mem hne
  have hlow := hN1 _ n' hn' hmono' hsum'
  have hle : Erdos295.k N ≤ m := Nat.sInf_le ⟨n, hn, hmono, hsum⟩
  have hle' : (Erdos295.k N : ℝ) ≤ m := by exact_mod_cast hle
  constructor
  · show -C < (Erdos295.k N : ℝ) - (Real.exp 1 - 1) * N
    have : (Real.exp 1 - 1) * N - C < (Erdos295.k N : ℝ) := hlow
    linarith
  · show (Erdos295.k N : ℝ) - (Real.exp 1 - 1) * N ≤ O * N / Real.log N
    linarith

end OMA.Erdos295R1
end R1Section

section H1Section
/- The logarithmic comparison for the lower bound follows the argument in
mrmario2202's Erdős–Straus reduction, project PR 3069. -/

open Filter

namespace OMA.ErdosStrausLower

lemma denominator_bound {N m : ℕ} (n : Fin m → ℕ)
    (hN : ∀ i, N ≤ n i) (hn : StrictMono n) (i : Fin m) : N + i.val ≤ n i := by
  rcases i with ⟨i, hi⟩
  induction i with
  | zero => simpa using hN ⟨0, hi⟩
  | succ i ih =>
    have hprev := ih (Nat.lt_of_succ_lt hi)
    have hstep := hn (show (⟨i, Nat.lt_of_succ_lt hi⟩ : Fin m) < ⟨i + 1, hi⟩ from Nat.lt_succ_self i)
    change N + i ≤ _ at hprev
    change N + (i + 1) ≤ _
    omega

lemma reciprocal_le_log_increment {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ≤ Real.log (x + 1) - Real.log x := by
  have hp : 0 < x + 1 := by linarith
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hp hx)
  rw [Real.log_div hp.ne' hx.ne', inv_div] at h
  calc
    1 / (x + 1) = 1 - x / (x + 1) := by field_simp; ring
    _ ≤ _ := h

end OMA.ErdosStrausLower

theorem h1_proof : OMA.Erdos295R1.H1 := by
  refine ⟨2, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with N hN
  intro m n hn hmono hsum
  let a : ℝ := (N : ℝ) - 1
  have ha : 0 < a := by
    apply sub_pos.mpr
    exact_mod_cast (show 1 < N from by omega)
  let f (j : ℕ) := Real.log (a + j)
  have hterm (i : Fin m) : 1 / (n i : ℝ) ≤ f (i.val + 1) - f i.val := by
    have hden := OMA.ErdosStrausLower.denominator_bound n hn hmono i
    have hreal : (N : ℝ) + (i.val : ℝ) ≤ n i := by exact_mod_cast hden
    have hpos : 0 < a + i.val := by positivity
    calc
      1 / (n i : ℝ) ≤ 1 / (a + i.val + 1) :=
        one_div_le_one_div_of_le (by linarith) (by dsimp [a]; linarith)
      _ ≤ _ := by
        simpa [f, Nat.cast_add, add_assoc] using
          OMA.ErdosStrausLower.reciprocal_le_log_increment hpos
  have hlog : 1 ≤ Real.log (a + m) - Real.log a := calc
    1 = ∑ i : Fin m, 1 / (n i : ℝ) := hsum.symm
    _ ≤ ∑ i : Fin m, (f (i.val + 1) - f i.val) := Finset.sum_le_sum fun i _ => hterm i
    _ = ∑ i ∈ Finset.range m, (f (i + 1) - f i) :=
      Fin.sum_univ_eq_sum_range (fun j => f (j + 1) - f j) m
    _ = f m - f 0 := Finset.sum_range_sub f m
    _ = _ := by simp [f]
  have hend : 0 < a + m := by positivity
  rw [← Real.log_div hend.ne' ha.ne', Real.le_log_iff_exp_le (div_pos hend ha),
    le_div_iff₀ ha] at hlog
  dsimp [a] at hlog
  nlinarith [Real.exp_one_lt_d9]
end H1Section

section H2Section
/- The factorial divisor representation and logarithm bound below are adapted
from Steven Enamakel (@senamakel), project PR 1451 on Erdős problem 304.
Take the last consecutive harmonic block below one, using its small residual
to keep all added denominators beyond the block. A common denominator is
bounded by Chebyshev's estimate, so the factorial expansion is short. -/

open Filter Finset
namespace OMA.StrausUpper

/-- Every `x ≤ (n+1)!` is a sum of at most `n+1` distinct positive divisors of `(n+1)!`. -/
lemma repr (n : ℕ) : ∀ x ≤ (n + 1).factorial, ∃ S : Finset ℕ, S.card ≤ n + 1 ∧
    (∀ d ∈ S, 0 < d ∧ d ∣ (n + 1).factorial) ∧ ∑ d ∈ S, d = x := by
  induction n with
  | zero =>
    intro x hx
    simp only [zero_add, Nat.factorial_one] at hx
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with rfl | rfl
    · exact ⟨∅, by simp, by simp, by simp⟩
    · exact ⟨{1}, by simp, by simp, by simp⟩
  | succ n ih =>
    intro x hx
    have hfac : (n + 2).factorial = (n + 2) * (n + 1).factorial := Nat.factorial_succ (n + 1)
    have hq : x / (n + 2) ≤ (n + 1).factorial := by
      apply Nat.div_le_of_le_mul
      rw [← hfac]; exact hx
    obtain ⟨S, hcard, hS, hsum⟩ := ih (x / (n + 2)) hq
    have hinj : Function.Injective (fun d : ℕ => d * (n + 2)) := by
      intro u v h
      simpa using h
    set T := S.image (fun d : ℕ => d * (n + 2)) with hT
    have hTcard : T.card = S.card := Finset.card_image_of_injective _ hinj
    have hTmem : ∀ e ∈ T, 0 < e ∧ e ∣ (n + 1 + 1).factorial ∧ n + 2 ≤ e := by
      intro e he
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hd0, hdd⟩ := hS d hd
      refine ⟨by positivity, ?_, by nlinarith⟩
      rw [show n + 1 + 1 = n + 2 from rfl, hfac, mul_comm d]
      exact Nat.mul_dvd_mul_left _ hdd
    have hTsum : ∑ e ∈ T, e = (x / (n + 2)) * (n + 2) := by
      rw [hT, Finset.sum_image (fun u _ v _ h => hinj h), ← Finset.sum_mul, hsum]
    have hdm := Nat.div_add_mod x (n + 2)
    have hr : x % (n + 2) < n + 2 := Nat.mod_lt _ (by omega)
    by_cases h0 : x % (n + 2) = 0
    · refine ⟨T, by omega, fun e he => ⟨(hTmem e he).1, (hTmem e he).2.1⟩, ?_⟩
      rw [hTsum]; rw [h0] at hdm; linarith
    · have hnot : x % (n + 2) ∉ T := fun h => by have := (hTmem _ h).2.2; omega
      refine ⟨insert (x % (n + 2)) T, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hnot]; omega
      · intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · refine ⟨Nat.pos_of_ne_zero h0, Nat.dvd_factorial (Nat.pos_of_ne_zero h0) (by omega)⟩
        · exact ⟨(hTmem e he).1, (hTmem e he).2.1⟩
      · rw [Finset.sum_insert hnot, hTsum]; linarith

lemma key (a b m : ℕ) (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ (m + 1).factorial) :
    ∃ S : Finset ℕ, S.card ≤ 2 * (m + 1) ∧ (∀ d ∈ S, 1 < d) ∧
      (a / b : ℚ) = ∑ d ∈ S, (d : ℚ)⁻¹ := by
  set M := (m + 1).factorial with hM
  have hMpos : 0 < M := Nat.factorial_pos _
  have hbpos : 0 < b := by omega
  set q := a * M / b with hqdef
  set r := a * M % b with hrdef
  have hdm : b * q + r = a * M := Nat.div_add_mod (a * M) b
  have hr : r < b := Nat.mod_lt _ hbpos
  have hqM : q < M := by
    rw [hqdef, Nat.div_lt_iff_lt_mul hbpos]
    rw [mul_comm M b]; exact Nat.mul_lt_mul_of_pos_right hab hMpos
  obtain ⟨S1, hc1, hS1, hs1⟩ := repr m q hqM.le
  obtain ⟨S2, hc2, hS2, hs2⟩ := repr m r (by omega)
  replace hS1 : ∀ d ∈ S1, 0 < d ∧ d ∣ M := hS1
  replace hS2 : ∀ d ∈ S2, 0 < d ∧ d ∣ M := hS2
  have hle1 : ∀ d ∈ S1, d ≤ q := fun d hd => by rw [← hs1]; exact Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) hd
  have hle2 : ∀ e ∈ S2, e ≤ r := fun e he => by rw [← hs2]; exact Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) he
  set T1 := S1.image (fun d => M / d) with hT1
  set T2 := S2.image (fun e => b * M / e) with hT2
  have hinj1 : Set.InjOn (fun d => M / d) S1 := by
    intro u hu v hv h
    simp only at h
    rw [← Nat.div_div_self (hS1 u hu).2 hMpos.ne', h, Nat.div_div_self (hS1 v hv).2 hMpos.ne']
  have hinj2 : Set.InjOn (fun e => b * M / e) S2 := by
    intro u hu v hv h
    simp only at h
    have hu' : u ∣ b * M := Dvd.dvd.mul_left (hS2 u hu).2 b
    have hv' : v ∣ b * M := Dvd.dvd.mul_left (hS2 v hv).2 b
    have hbM : b * M ≠ 0 := by positivity
    rw [← Nat.div_div_self hu' hbM, h, Nat.div_div_self hv' hbM]
  have hT1mem : ∀ y ∈ T1, 1 < y ∧ y ≤ M := by
    intro y hy
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hd0, k, hk⟩ := hS1 d hd
    have hdq := hle1 d hd
    refine ⟨?_, Nat.div_le_self _ _⟩
    rw [hk, Nat.mul_div_cancel_left _ hd0]
    rcases Nat.lt_or_ge 1 k with h | h
    · exact h
    · exfalso
      interval_cases k
      · simp at hk; omega
      · simp at hk; omega
  have hT2mem : ∀ y ∈ T2, M < y := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨he0, k, hk⟩ := hS2 e he
    have her := hle2 e he
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h] at hk; omega
      · exact h
    rw [hk, show b * (e * k) = e * (b * k) by ring, Nat.mul_div_cancel_left _ he0]
    nlinarith
  have hdisj : Disjoint T1 T2 := by
    rw [Finset.disjoint_left]
    intro y h1 h2
    have := (hT1mem y h1).2
    have := hT2mem y h2
    omega
  have hmem : (∀ d ∈ T1 ∪ T2, 1 < d) ∧ (a / b : ℚ) = ∑ d ∈ T1 ∪ T2, (d : ℚ)⁻¹ := by
    constructor
    · intro y hy
      rcases Finset.mem_union.mp hy with h | h
      · exact (hT1mem y h).1
      · have := hT2mem y h; omega
    · rw [Finset.sum_union hdisj, hT1, hT2, Finset.sum_image hinj1, Finset.sum_image hinj2]
      have e1 : ∑ d ∈ S1, (((M / d : ℕ) : ℚ))⁻¹ = (q : ℚ) / M := by
        rw [← hs1]
        push_cast
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [Nat.cast_div (hS1 d hd).2 (by exact_mod_cast (hS1 d hd).1.ne'), inv_div]
      have e2 : ∑ e ∈ S2, (((b * M / e : ℕ) : ℚ))⁻¹ = (r : ℚ) / (b * M) := by
        rw [← hs2]
        push_cast
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun e he => ?_
        rw [Nat.cast_div (Dvd.dvd.mul_left (hS2 e he).2 b)
          (by exact_mod_cast (hS2 e he).1.ne'), inv_div]
        push_cast
        rfl
      rw [e1, e2]
      have hdmQ : (b : ℚ) * q + r = a * M := by exact_mod_cast hdm
      have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hbpos.ne'
      have hMQ : (M : ℚ) ≠ 0 := by exact_mod_cast hMpos.ne'
      field_simp
      linear_combination (-1 : ℚ) * hdmQ
  have hcard : (T1 ∪ T2).card ≤ 2 * (m + 1) := by
    have := Finset.card_union_le T1 T2
    have h1 : T1.card ≤ S1.card := Finset.card_image_le
    have h2 : T2.card ≤ S2.card := Finset.card_image_le
    omega
  exact ⟨_, hcard, hmem⟩

/-- `n log n - n ≤ log n!`. -/
lemma log_factorial_ge (n : ℕ) : (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := Real.pow_div_factorial_le_exp (n : ℝ) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf] at h
  have hl := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at hl
  linarith

lemma prefix_log (N j : ℕ) (hN : 0 < N) (hj : N ≤ j) :
    Real.log j - Real.log N ≤ ∑ i ∈ Ico N j, (i : ℝ)⁻¹ := by
  induction j, hj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    rw [sum_Ico_succ_top hj, Nat.cast_succ]
    have hjr : (0 : ℝ) < j := by exact_mod_cast (lt_of_lt_of_le hN hj)
    have hx := Real.log_le_sub_one_of_pos (div_pos (show 0 < (j : ℝ)+1 by positivity) hjr)
    rw [Real.log_div (by positivity) hjr.ne'] at hx
    have he : ((j : ℝ)+1)/j - 1 = (j : ℝ)⁻¹ := by field_simp; ring
    linarith

lemma harmonic_block (N : ℕ) (hN : 2 ≤ N) :
    ∃ B : ℕ, N < B ∧ (B : ℝ) ≤ Real.exp 1 * N ∧
      (∑ i ∈ Ico N B, (i : ℚ)⁻¹) < 1 ∧
      1 ≤ (∑ i ∈ Ico N B, (i : ℚ)⁻¹) + (B : ℚ)⁻¹ := by
  classical
  let K := ⌈Real.exp 1 * N⌉₊
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have heK : Real.exp 1 * N ≤ (K : ℝ) := Nat.le_ceil _
  have hNK : N ≤ K := by
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    exact_mod_cast (show (N : ℝ) ≤ K by nlinarith)
  have hKlog := prefix_log N K (by omega) hNK
  have hl := Real.log_le_log (mul_pos (Real.exp_pos 1) hNr) heK
  rw [Real.log_mul (Real.exp_pos _).ne' hNr.ne', Real.log_exp] at hl
  have hK : (1 : ℚ) ≤ ∑ i ∈ Ico N K, (i : ℚ)⁻¹ := by
    rw [← Rat.cast_le (K := ℝ)]
    push_cast
    linarith
  let P := fun j : ℕ => (1 : ℚ) ≤ ∑ i ∈ Ico N j, (i : ℚ)⁻¹
  have hex : ∃ j, P j := ⟨K, hK⟩
  let J := Nat.find hex
  have hJ : P J := Nat.find_spec hex
  have hJK : J ≤ K := Nat.find_min' hex hK
  have hNJ : N < J := by
    by_contra! h
    norm_num [P, Finset.Ico_eq_empty_of_le h] at hJ
  let B := J - 1
  have hBJ : B+1=J := by dsimp [B]; omega
  have hNB : N ≤ B := by omega
  have hB := Nat.find_min hex (show B < J by omega)
  change ¬ (1 : ℚ) ≤ ∑ i ∈ Ico N B, (i : ℚ)⁻¹ at hB
  change (1 : ℚ) ≤ ∑ i ∈ Ico N J, (i : ℚ)⁻¹ at hJ
  rw [← hBJ, sum_Ico_succ_top hNB] at hJ
  refine ⟨B, ?_, ?_, lt_of_not_ge hB, hJ⟩
  · by_contra! h
    have h' : B = N := by omega
    rw [h'] at hJ
    simp only [Ico_self, sum_empty, zero_add] at hJ
    have : (1 : ℚ) < N := by exact_mod_cast (by omega : 1 < N)
    exact (inv_lt_one_of_one_lt₀ this).not_ge hJ
  · have hBK : B < K := by omega
    have hBr : (B : ℝ) + 1 ≤ K := by exact_mod_cast (show B+1 ≤ K by omega)
    have hx : (K : ℝ) < Real.exp 1 * N + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith

lemma factorial_bound : ∀ᶠ N : ℕ in atTop,
    let m := ⌈100 * (N : ℝ) / Real.log N⌉₊
    Nat.lcmUpto (4*N) ≤ (m+1).factorial ∧
    2 * ((m : ℝ) + 1) ≤ 204 * (N : ℝ) / Real.log N := by
  have hlim := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop 6, eventually_ge_atTop 2] with N hL hN
  change 6 ≤ Real.log N at hL
  let L := Real.log N
  let x := 100 * (N : ℝ) / L
  let m := ⌈x⌉₊
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLN : L ≤ N := by have := Real.log_le_sub_one_of_pos hN0; dsimp [L]; linarith
  have hx0 : 0 < x := div_pos (by positivity) hL0
  have hxle : x ≤ (m : ℝ) := Nat.le_ceil x
  have hmlt : (m : ℝ) < x+1 := Nat.ceil_lt_add_one hx0.le
  have hlogL : Real.log L ≤ L/2 := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < L/2)
    rw [Real.log_div hL0.ne' (by norm_num)] at h
    linarith [Real.log_two_lt_d9]
  have hlogx : Real.log x = Real.log 100 + L - Real.log L := by
    rw [show x = 100 * (N : ℝ) / L from rfl,
      Real.log_div (by positivity) hL0.ne', Real.log_mul (by norm_num) hN0.ne']
  have hmge : x ≤ ((m+1 : ℕ) : ℝ) := by push_cast; linarith
  have hmL : L / 3 ≤ Real.log (m+1 : ℕ) - 1 := by
    have := Real.log_le_log hx0 hmge
    have : 6 ≤ L := hL
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ 100 by norm_num)]
  have hfac := log_factorial_ge (m+1)
  have hxmul : x*(L/3) = 100*(N : ℝ)/3 := by dsimp [x]; field_simp
  have hfact : 100*(N : ℝ)/3 ≤ Real.log ((m+1).factorial) := by
    have := mul_le_mul hmge hmL (by positivity) (by positivity)
    nlinarith
  have hpsi := Chebyshev.psi_le_const_mul_self (x := ((4*N : ℕ) : ℝ)) (by positivity)
  rw [Chebyshev.psi_eq_log_lcmUpto] at hpsi
  have h4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  push_cast at hpsi
  constructor
  · change Nat.lcmUpto (4*N) ≤ (m+1).factorial
    have hb := Nat.lcmUpto_pos (4*N)
    have hf := Nat.factorial_pos (m+1)
    apply (Nat.cast_le (α := ℝ)).mp
    apply (Real.log_le_log_iff (by exact_mod_cast hb) (by exact_mod_cast hf)).mp
    nlinarith [mul_le_mul_of_nonneg_right h4 hN0.le]
  · change 2 * ((m : ℝ)+1) ≤ 204 * N / L
    rw [le_div_iff₀ hL0]
    have hxm : x * L = 100 * (N : ℝ) := by dsimp [x]; field_simp
    nlinarith [mul_lt_mul_of_pos_right hmlt hL0]

lemma common_remainder {N B : ℕ} (hN : 2 ≤ N) (hNB : N < B) (hmax : B ≤ 4*N)
    (hlo : (∑ i ∈ Ico N B, (i : ℚ)⁻¹) < 1) :
    let b := Nat.lcmUpto (4*N)
    ∃ a : ℕ, 0 < a ∧ a < b ∧
      (a / b : ℚ) = 1 - ∑ i ∈ Ico N B, (i : ℚ)⁻¹ := by
  let b := Nat.lcmUpto (4*N)
  let v := ∑ i ∈ Ico N B, b/i
  have hb0 : 0 < b := Nat.lcmUpto_pos _
  have hbq : 0 < (b : ℚ) := by exact_mod_cast hb0
  have hv : (v : ℚ) = (∑ i ∈ Ico N B, (i : ℚ)⁻¹) * b := by
    dsimp [v]
    push_cast
    rw [sum_mul]
    refine sum_congr rfl fun i hi => ?_
    obtain ⟨hiN, hiB⟩ := mem_Ico.mp hi
    have hi0 : 0 < i := by omega
    have hid : i ∣ b :=
      Finset.dvd_lcm (f := id) (mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [Nat.cast_div hid (by exact_mod_cast hi0.ne'), div_eq_mul_inv, mul_comm]
  have hvlt : v < b := by
    exact_mod_cast (show (v : ℚ) < b by rw [hv]; simpa using (mul_lt_mul_of_pos_right hlo hbq))
  have hvpos : 0 < v := by
    have hsum : 0 < ∑ i ∈ Ico N B, (i : ℚ)⁻¹ :=
      sum_pos' (fun i hi => by positivity) ⟨N, mem_Ico.mpr ⟨le_rfl, hNB⟩,
        inv_pos.mpr (by exact_mod_cast (show 0 < N by omega))⟩
    exact_mod_cast (show 0 < (v : ℚ) by rw [hv]; positivity)
  refine ⟨b-v, by omega, ?_, ?_⟩
  · change b-v < b
    omega
  · change ((b-v : ℕ) : ℚ) / b = _
    rw [Nat.cast_sub hvlt.le, div_eq_iff hbq.ne', hv]
    ring

end OMA.StrausUpper

theorem h2_proof : OMA.Erdos295R1.H2 := by
  classical
  refine ⟨204, by norm_num, ?_⟩
  filter_upwards [OMA.StrausUpper.factorial_bound, eventually_ge_atTop 2] with N hfac hN
  obtain ⟨B, hNB, hB, hlo, hhi⟩ := OMA.StrausUpper.harmonic_block N hN
  have hmax : B ≤ 4*N := by
    have he : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
    have h : (B : ℝ) ≤ 4 * (N : ℝ) := hB.trans (mul_le_mul_of_nonneg_right he (by positivity))
    exact_mod_cast h
  let b := Nat.lcmUpto (4*N)
  let m := ⌈100*(N : ℝ)/Real.log N⌉₊
  obtain ⟨a, ha, hab, hrem⟩ := OMA.StrausUpper.common_remainder hN hNB hmax hlo
  obtain ⟨T, hcard, hT, heq⟩ := OMA.StrausUpper.key a b m ha hab hfac.1
  have hsum : (∑ i ∈ Ico N B, (i : ℚ)⁻¹) + (∑ i ∈ T, (i : ℚ)⁻¹) = 1 := by
    rw [← heq]
    change _ + (a / Nat.lcmUpto (4*N) : ℚ) = 1
    rw [hrem]; ring
  have hbig (i : ℕ) (hi : i ∈ T) : B ≤ i := by
    have hle : (i : ℚ)⁻¹ ≤ ∑ j ∈ T, (j : ℚ)⁻¹ :=
      single_le_sum (f := fun j : ℕ => (j : ℚ)⁻¹) (fun j _ => by positivity) hi
    have hi0 : (0 : ℚ) < i := by exact_mod_cast (show 0 < i by have := hT i hi; omega)
    have hB0 : (0 : ℚ) < B := by exact_mod_cast (show 0 < B by omega)
    exact_mod_cast ((inv_le_inv₀ hi0 hB0).mp (by linarith : (i : ℚ)⁻¹ ≤ (B : ℚ)⁻¹))
  have hd : Disjoint (Ico N B) T := by
    rw [disjoint_left]
    intro i h h'
    exact  (mem_Ico.mp h).2.not_ge (hbig _ h')
  let S := Ico N B ∪ T
  refine ⟨S.card, S.orderEmbOfFin rfl, ?_, (S.orderEmbOfFin rfl).strictMono, ?_, ?_⟩
  · intro i
    rcases mem_union.mp (S.orderEmbOfFin_mem rfl i) with hi | hi
    · exact (mem_Ico.mp hi).1
    · exact hNB.le.trans (hbig _ hi)
  · have h := sum_union (f := fun i : ℕ => (i : ℚ)⁻¹) hd
    have hq : ∑ i ∈ S, (i : ℚ)⁻¹ = 1 := h.trans hsum
    have hs : ∑ i ∈ S, (i : ℝ)⁻¹ = 1 := by
      have hr := congrArg (fun q : ℚ => (q : ℝ)) hq
      push_cast at hr
      exact hr
    conv_rhs => rw [← hs, ← S.map_orderEmbOfFin_univ rfl, sum_map]
    simp [one_div]
  · change ((Ico N B ∪ T).card : ℝ) ≤ _
    rw [card_union_of_disjoint hd, Nat.card_Ico, Nat.cast_add, Nat.cast_sub hNB.le]
    have h' : (T.card : ℝ) ≤ 2*((m : ℝ)+1) := by exact_mod_cast hcard
    have hx : 2*((m : ℝ)+1) ≤ 204*(N : ℝ)/Real.log N := hfac.2
    linarith
end H2Section

theorem OMA.solution : type_of% @Erdos295.erdos_295.variants.erdos_straus :=
  OMA.Erdos295R1.main h1_proof h2_proof
