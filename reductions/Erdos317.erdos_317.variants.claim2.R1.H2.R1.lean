import OMAReductions.R_Erdos317_erdos_317_variants_claim2_R1
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
A prime-power predecessor has critical magnitude exactly when a ternary
sum realizes the positive numerator one (negate all coefficients if needed).
Eventually this is equivalent to solvability in the top valuation layer
at every prime. We separate prime and proper-power endpoints. At a proper
power the base prime always represents every residue by at most one term.

The endpoint reduction is PR 4159. PR 4040 already gave the conditional
primary assembly and smooth-grid radius for the first question. Here the
grid is filled by prime-power descent and a Chebyshev estimate, and the
primary lifts start from single-prime residues. See endpoint_iff_steps
for both directions of the reduction.
-/
namespace OMA.R_Erdos317_erdos_317_variants_claim2_R1_H2_R1

open Finset Filter Real
open scoped Nat

/-- Obstruct numerator one at the predecessor of each sufficiently large prime. -/
def H1 : Prop :=
  ∀ᶠ u : ℕ in atTop, u.Prime →
    let n := u - 1
    ∃ q ∈ Nat.primesLE n, ¬ ∃ δ : Fin n → ℤ,
        (∀ i, δ i = -1 ∨ δ i = 0 ∨ δ i = 1) ∧
        (∀ i, ¬ (q ^ Nat.log q n ∣ i.val + 1) → δ i = 0) ∧
        (q : ℤ) ∣ 1 - ∑ i : Fin n, δ i * ((Nat.lcmUpto n / (i.val + 1) : ℕ) : ℤ)

/-- At proper prime powers the witnessing prime must differ from the base.
The threshold is uniform in both the base and the exponent. -/
def H2 : Prop :=
  ∀ᶠ u : ℕ in atTop, ∀ p e : ℕ, p.Prime → 2 ≤ e → p ^ e = u →
    let n := u - 1
    ∃ q ∈ Nat.primesLE n, q ≠ p ∧ ¬ ∃ δ : Fin n → ℤ,
        (∀ i, δ i = -1 ∨ δ i = 0 ∨ δ i = 1) ∧
        (∀ i, ¬ (q ^ Nat.log q n ∣ i.val + 1) → δ i = 0) ∧
        (q : ℤ) ∣ 1 - ∑ i : Fin n, δ i * ((Nat.lcmUpto n / (i.val + 1) : ℕ) : ℤ)

lemma dvd_lcmUpto {n d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n) : d ∣ Nat.lcmUpto n :=
  Finset.dvd_lcm (f := id) (mem_Icc.mpr ⟨hd1, hdn⟩)

lemma lcmUpto_dvd_lcmUpto {a b : ℕ} (hab : a ≤ b) : Nat.lcmUpto a ∣ Nat.lcmUpto b :=
  Finset.lcm_mono (Icc_subset_Icc_right hab)

lemma div_cast_eq {B d : ℕ} (hd : d ∣ B) (hdpos : 0 < d) :
    ((B / d : ℕ) : ℚ) = (B : ℚ) / (d : ℚ) := by
  have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
  rw [eq_div_iff hdq]
  exact_mod_cast Nat.div_mul_cancel hd

lemma cast_mul_div_weight {B d : ℕ} (c : ℤ) (hd : d ∣ B) (hdpos : 0 < d) :
    ((c * ((B / d : ℕ) : ℤ) : ℤ) : ℚ) = (B : ℚ) * ((c : ℚ) / (d : ℚ)) := by
  rw [Int.cast_mul, Int.cast_natCast, div_cast_eq hd hdpos]
  ring

lemma lcmUpto_eq_self_of_not_isPrimePow {h : ℕ} (hh : 1 ≤ h) (hnp : ¬ IsPrimePow h) :
    Nat.lcmUpto h = Nat.lcmUpto (h - 1) := by
  refine Nat.dvd_antisymm ?_ (lcmUpto_dvd_lcmUpto (Nat.sub_le h 1))
  apply Finset.lcm_dvd
  intro d hd
  obtain ⟨hd1, hdh⟩ := mem_Icc.mp hd
  by_cases hlt : d < h
  · exact dvd_lcmUpto hd1 (Nat.le_sub_one_of_lt hlt)
  · have hdeq : d = h := by omega
    subst hdeq
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    cases k with
    | zero => simp
    | succ k =>
      have hpp : IsPrimePow (p ^ (k + 1)) := ⟨p, k + 1, hp.prime, by omega, rfl⟩
      have hle : p ^ (k + 1) ≤ d := Nat.le_of_dvd (by omega) hpk
      have hne : p ^ (k + 1) ≠ d := fun heq => hnp (heq ▸ hpp)
      exact dvd_lcmUpto (pow_pos hp.pos _) (by omega)

lemma log_prime_pow_pred {q e : ℕ} (hq : q.Prime) (he : 1 ≤ e) :
    Nat.log q (q ^ e - 1) = e - 1 := by
  have h1 : 1 ≤ q ^ e := one_le_pow₀ hq.one_le
  have hmul : q ^ e = q ^ (e - 1) * q := by
    conv_lhs => rw [← Nat.sub_add_cancel he, pow_succ]
  have hq2 : 2 ≤ q := hq.two_le
  have hpos : 1 ≤ q ^ (e - 1) := one_le_pow₀ hq.one_le
  have hge_add : q ^ (e - 1) + 1 ≤ q ^ e := by nlinarith
  have hge : q ^ (e - 1) ≤ q ^ e - 1 := by omega
  have hne : q ^ e - 1 ≠ 0 := by omega
  apply le_antisymm
  · by_contra! h
    have hpow : q ^ e ≤ q ^ e - 1 := by
      calc q ^ e ≤ q ^ (Nat.log q (q ^ e - 1)) := Nat.pow_le_pow_right hq.pos (by omega)
        _ ≤ q ^ e - 1 := Nat.pow_log_le_self q hne
    omega
  · exact Nat.le_log_of_pow_le hq.one_lt hge

lemma log_other_prime_pow_pred {p q e : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (_he : 1 ≤ e) : Nat.log p (q ^ e - 1) = Nat.log p (q ^ e) := by
  apply le_antisymm (Nat.log_mono_right (Nat.sub_le _ _))
  cases hk : Nat.log p (q ^ e) with
  | zero => exact Nat.zero_le _
  | succ k' =>
    have hle : p ^ (k' + 1) ≤ q ^ e := by
      rw [← hk]
      exact Nat.pow_log_le_self p (pow_pos hq.pos e).ne'
    have hne : p ^ (k' + 1) ≠ q ^ e := by
      intro heq
      have hpdvd : p ∣ q ^ e := by
        rw [← heq]
        exact dvd_pow_self p (by omega)
      exact hpq ((hq.eq_one_or_self_of_dvd p (hp.dvd_of_dvd_pow hpdvd)).resolve_left hp.ne_one)
    exact Nat.le_log_of_pow_le hp.one_lt (by omega)

lemma lcmUpto_prime_pow {q e : ℕ} (hq : q.Prime) (he : 1 ≤ e) :
    Nat.lcmUpto (q ^ e) = q * Nat.lcmUpto (q ^ e - 1) := by
  apply Nat.eq_of_factorization_eq (Nat.lcmUpto_ne_zero _)
    (mul_ne_zero hq.ne_zero (Nat.lcmUpto_ne_zero _))
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_mul hq.ne_zero (Nat.lcmUpto_ne_zero _), Finsupp.add_apply,
      Nat.factorization_lcmUpto _ hp, Nat.factorization_lcmUpto _ hp,
      hq.factorization]
    by_cases hpq : p = q
    · subst hpq
      simp [Nat.log_pow hq.one_lt, log_prime_pow_pred hq he, Nat.add_sub_cancel' he]
    · simp [Finsupp.single_eq_of_ne hpq, log_other_prime_pow_pred hp hq hpq he]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

lemma not_dvd_lcmUpto_div_pow {n q : ℕ} (hq : q.Prime) :
    ¬ q ∣ (Nat.lcmUpto n / q ^ (Nat.log q n)) := by
  have hpow : q ^ (Nat.log q n) ∣ Nat.lcmUpto n := by
    by_cases hqn : q ≤ n
    · exact dvd_lcmUpto (pow_pos hq.pos _) (Nat.pow_log_le_self q (lt_of_lt_of_le hq.pos hqn).ne')
    · simp [Nat.log_of_lt (by omega : n < q)]
  intro hdvd
  have hq1 : q ^ (Nat.log q n + 1) ∣ Nat.lcmUpto n := by
    rw [pow_succ]
    have hmul : q ^ (Nat.log q n) * (Nat.lcmUpto n / q ^ (Nat.log q n)) = Nat.lcmUpto n :=
      Nat.mul_div_cancel' hpow
    rw [← hmul]
    exact Nat.mul_dvd_mul_left _ hdvd
  have hle := (hq.pow_dvd_iff_le_factorization (Nat.lcmUpto_ne_zero n)).mp hq1
  rw [Nat.factorization_lcmUpto n hq] at hle
  omega

/-- Every nonzero residue modulo a prime `q` is hit by `M / m` for a unique `1 ≤ m < q`
whenever `q ∤ M` and every `1 ≤ m < q` divides `M`. -/
lemma mod_q_residue_hit {q M : ℕ} (hq : q.Prime) (hM : ¬ q ∣ M)
    (hdiv : ∀ m, 1 ≤ m → m < q → m ∣ M) (z : ℤ) (hz : ¬ (q : ℤ) ∣ z) :
    ∃ m : ℕ, 1 ≤ m ∧ m < q ∧ (q : ℤ) ∣ z - ((M / m : ℕ) : ℤ) := by
  let _ : Fact q.Prime := ⟨hq⟩
  have hMz : (M : ZMod q) ≠ 0 := by
    intro h0
    exact hM ((ZMod.natCast_eq_zero_iff M q).mp h0)
  have hzz : (z : ZMod q) ≠ 0 := by
    intro h0
    exact hz ((ZMod.intCast_zmod_eq_zero_iff_dvd z q).mp h0)
  let a : ZMod q := (M : ZMod q) / (z : ZMod q)
  have ha0 : a ≠ 0 := div_ne_zero hMz hzz
  let m : ℕ := a.val
  have hmlt : m < q := a.val_lt
  have hm1 : 1 ≤ m := by
    by_contra! hm0
    have h0 : m = 0 := by omega
    apply ha0
    rw [← ZMod.natCast_zmod_val a]
    simp [m, h0]
  refine ⟨m, hm1, hmlt, ?_⟩
  have hmd : m ∣ M := hdiv m hm1 hmlt
  have hmul : (m : ZMod q) * ((M / m : ℕ) : ZMod q) = (M : ZMod q) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hmd]
  have hmcast : (m : ZMod q) = a := ZMod.natCast_zmod_val a
  have heq : ((M / m : ℕ) : ZMod q) = (z : ZMod q) := by
    rw [hmcast] at hmul
    dsimp [a] at hmul
    have h1 : (M : ZMod q) * ((M / m : ℕ) : ZMod q) = (M : ZMod q) * (z : ZMod q) := by
      calc (M : ZMod q) * ((M / m : ℕ) : ZMod q)
          = (z : ZMod q) * ((M : ZMod q) / (z : ZMod q) * ((M / m : ℕ) : ZMod q)) := by
              field_simp [hzz]
        _ = (z : ZMod q) * (M : ZMod q) := by rw [hmul]
        _ = (M : ZMod q) * (z : ZMod q) := mul_comm _ _
    exact mul_left_cancel₀ hMz h1
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast, heq, sub_self]

/-- Greedy reduction on a finite set of denominators `≥ 2` (each `1/d ≤ 1/2`). -/
lemma greedy_reduce (E : Finset ℕ) (hE : ∀ d ∈ E, 2 ≤ d) (r : ℚ) (hr : 0 ≤ r) :
    ∃ γ : ℕ → ℤ,
      (∀ d, γ d = 0 ∨ γ d = 1) ∧
      (∀ d, d ∉ E → γ d = 0) ∧
      0 ≤ r - ∑ d ∈ E, (γ d : ℚ) / d ∧
      (r - ∑ d ∈ E, (γ d : ℚ) / d ≤ 1 ∨
        ((∀ d ∈ E, γ d = 1) ∧ 1 < r - ∑ d ∈ E, (γ d : ℚ) / d)) := by
  induction E using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 0, fun _ => Or.inl rfl, fun _ _ => rfl, by simpa using hr, ?_⟩
    by_cases h1 : r ≤ 1
    · left; simpa using h1
    · right; exact ⟨fun _ h => absurd h (notMem_empty _), by simpa using not_le.mp h1⟩
  | @insert a s has ih =>
    have ha2 : 2 ≤ a := hE a (mem_insert_self a s)
    have hs2 : ∀ d ∈ s, 2 ≤ d := fun d hd => hE d (mem_insert_of_mem hd)
    obtain ⟨γ, hγ01, hγout, hnonneg, hcase⟩ := ih hs2
    rcases hcase with hle1 | ⟨hall, hgt1⟩
    · refine ⟨γ, hγ01, ?_, ?_, Or.inl ?_⟩
      · intro d hd
        exact hγout d (fun h => hd (mem_insert_of_mem h))
      · rw [sum_insert has, hγout a has]
        simpa using hnonneg
      · rw [sum_insert has, hγout a has]
        simpa using hle1
    · classical
      let γ' : ℕ → ℤ := fun d => if d = a then 1 else γ d
      have hsum' : ∑ d ∈ insert a s, (γ' d : ℚ) / d = (1 : ℚ) / a + ∑ d ∈ s, (γ d : ℚ) / d := by
        rw [sum_insert has]
        simp only [γ', if_pos rfl, Int.cast_one]
        congr 1
        refine sum_congr rfl fun d hd => ?_
        have hda : d ≠ a := fun h => has (h ▸ hd)
        simp [hda]
      have ha_inv : (1 : ℚ) / a ≤ 1 / 2 := by
        have h2a : (2 : ℚ) ≤ a := by exact_mod_cast ha2
        exact one_div_le_one_div_of_le (by norm_num) h2a
      have hnn' : 0 ≤ r - ∑ d ∈ insert a s, (γ' d : ℚ) / d := by
        rw [hsum']; linarith
      refine ⟨γ', ?_, ?_, hnn', ?_⟩
      · intro d
        by_cases hda : d = a
        · right; simp [γ', hda]
        · simpa [γ', hda] using hγ01 d
      · intro d hd
        have hda : d ≠ a := fun h => hd (h ▸ mem_insert_self a s)
        have hds : d ∉ s := fun h => hd (mem_insert_of_mem h)
        simp [γ', hda, hγout d hds]
      · by_cases hle : r - ∑ d ∈ insert a s, (γ' d : ℚ) / d ≤ 1
        · exact Or.inl hle
        · right
          refine ⟨?_, not_le.mp hle⟩
          intro d hd
          rcases mem_insert.mp hd with rfl | hds
          · simp [γ']
          · have hda : d ≠ a := fun h => has (h ▸ hds)
            simp [γ', hda, hall d hds]

lemma lcmUpto_one : Nat.lcmUpto 1 = 1 := by decide +kernel

lemma smoothDivs_one {n : ℕ} (hn : 1 ≤ n) :
    let smoothDivs := fun n h : ℕ => (Icc 1 n).filter (· ∣ Nat.lcmUpto h)
    smoothDivs n 1 = {1} := by
  intro smoothDivs
  ext d
  simp only [smoothDivs, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, lcmUpto_one]
  exact ⟨fun ⟨_, h⟩ => Nat.dvd_one.mp h, fun h => by subst h; exact ⟨⟨le_rfl, hn⟩, dvd_refl 1⟩⟩

lemma smoothCap_ge_one {n h : ℕ} (hn : 1 ≤ n) (hh : 1 ≤ h) (hhn : h ≤ n) :
    let smoothDivs := fun n h : ℕ => (Icc 1 n).filter (· ∣ Nat.lcmUpto h)
    let smoothCap := fun n h : ℕ =>
      (∑ d ∈ smoothDivs n h, (1 : ℚ) / d) - ∑ k ∈ (Icc 2 h).filter IsPrimePow, (1 : ℚ) / k
    1 ≤ smoothCap n h := by
  intro smoothDivs smoothCap
  induction h, hh using Nat.le_induction with
  | base =>
    have hbase : smoothDivs n 1 = {1} := smoothDivs_one hn
    simp [smoothCap, hbase]
  | succ k hk ih =>
    have ih' := ih (by omega)
    have hsub : smoothDivs n k ⊆ smoothDivs n (k + 1) := by
      intro d hd
      simp only [smoothDivs, Finset.mem_filter] at hd ⊢
      exact ⟨hd.1, hd.2.trans (lcmUpto_dvd_lcmUpto (Nat.le_succ k))⟩
    have hsum_split : ∑ d ∈ smoothDivs n (k + 1), (1 : ℚ) / d =
        (∑ d ∈ smoothDivs n k, (1 : ℚ) / d) +
        ∑ d ∈ smoothDivs n (k + 1) \ smoothDivs n k, (1 : ℚ) / d := by
      rw [← sum_sdiff hsub, add_comm]
    by_cases hpp : IsPrimePow (k + 1)
    · have hk_mem : k + 1 ∈ smoothDivs n (k + 1) \ smoothDivs n k := by
        rw [Finset.mem_sdiff]
        refine ⟨?_, ?_⟩
        · simp only [smoothDivs, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, hhn⟩, dvd_lcmUpto (by omega) le_rfl⟩
        · simp only [smoothDivs, Finset.mem_filter, not_and]
          intro _ hdvd
          obtain ⟨q, e, hq, he, hqe⟩ := hpp
          have hqp : q.Prime := hq.nat_prime
          rw [← hqe] at hdvd
          have hle := (hqp.pow_dvd_iff_le_factorization (Nat.lcmUpto_ne_zero k)).mp hdvd
          rw [Nat.factorization_lcmUpto k hqp] at hle
          have hpow : q ^ e ≤ k := (Nat.pow_le_pow_right hqp.pos hle).trans
            (Nat.pow_log_le_self q (by omega))
          omega
      have hpp_split : ∑ j ∈ (Icc 2 (k + 1)).filter IsPrimePow, (1 : ℚ) / j =
          (∑ j ∈ (Icc 2 k).filter IsPrimePow, (1 : ℚ) / j) + (1 : ℚ) / (k + 1) := by
        have hfilt : (Icc 2 (k + 1)).filter IsPrimePow =
            insert (k + 1) ((Icc 2 k).filter IsPrimePow) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
          constructor
          · rintro ⟨⟨h2, hj⟩, hjpp⟩
            by_cases hjk : j = k + 1
            · exact Or.inl hjk
            · exact Or.inr ⟨⟨h2, by omega⟩, hjpp⟩
          · rintro (rfl | ⟨⟨h2, hj⟩, hjpp⟩)
            · exact ⟨⟨by omega, le_rfl⟩, hpp⟩
            · exact ⟨⟨h2, by omega⟩, hjpp⟩
        rw [hfilt, sum_insert (by simp)]
        push_cast; ring
      have hterm : (1 : ℚ) / (k + 1) ≤ ∑ d ∈ smoothDivs n (k + 1) \ smoothDivs n k, (1 : ℚ) / d := by
        have h := single_le_sum (f := fun d : ℕ => (1 : ℚ) / d) (fun d _ => by positivity) hk_mem
        simpa [Nat.cast_add, Nat.cast_one] using h
      dsimp [smoothCap] at ih' ⊢
      rw [hsum_split, hpp_split]
      linarith
    · have hEq : Nat.lcmUpto (k + 1) = Nat.lcmUpto k := by
        simpa using lcmUpto_eq_self_of_not_isPrimePow (by omega) hpp
      have hdivs : smoothDivs n (k + 1) = smoothDivs n k := by
        simp [smoothDivs, hEq]
      have hfilt : (Icc 2 (k + 1)).filter IsPrimePow = (Icc 2 k).filter IsPrimePow := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨h2, hj⟩, hjpp⟩
          have hne : j ≠ k + 1 := fun h => hpp (h ▸ hjpp)
          exact ⟨⟨h2, by omega⟩, hjpp⟩
        · rintro ⟨⟨h2, hj⟩, hjpp⟩
          exact ⟨⟨h2, by omega⟩, hjpp⟩
      dsimp [smoothCap] at ih' ⊢
      rw [hdivs, hfilt]
      exact ih'

lemma smooth_grid_descent_aux {n h : ℕ} (hn : 1 ≤ n) (hh : 1 ≤ h) (hhsq : h * h ≤ n) :
    let smoothDivs := fun n h : ℕ => (Icc 1 n).filter (· ∣ Nat.lcmUpto h)
    let smoothCap := fun n h : ℕ =>
      (∑ d ∈ smoothDivs n h, (1 : ℚ) / d) - ∑ k ∈ (Icc 2 h).filter IsPrimePow, (1 : ℚ) / k
    ∀ z : ℤ, |(z : ℚ) / Nat.lcmUpto h| ≤ smoothCap n h →
      ∃ δ : ℕ → ℤ,
        (∀ d, δ d = -1 ∨ δ d = 0 ∨ δ d = 1) ∧
        (∀ d, d ∉ smoothDivs n h → δ d = 0) ∧
        ∑ d ∈ smoothDivs n h, (δ d : ℚ) / d = (z : ℚ) / Nat.lcmUpto h := by
  intro smoothDivs smoothCap
  induction h, hh using Nat.le_induction with
  | base =>
    intro z hz
    have hS1 : smoothDivs n 1 = {1} := smoothDivs_one hn
    have hM1 : smoothCap n 1 = 1 := by simp [smoothCap, hS1]
    rw [lcmUpto_one, hM1, Nat.cast_one, div_one] at hz
    have hz_int : |z| ≤ 1 := by exact_mod_cast hz
    have hcases : z = -1 ∨ z = 0 ∨ z = 1 := by
      obtain ⟨h1, h2⟩ := abs_le.mp hz_int; omega
    refine ⟨fun d => if d = 1 then z else 0, ?_, ?_, ?_⟩
    · intro d; by_cases hd : d = 1 <;> simp [hd, hcases]
    · intro d hd; rw [hS1, mem_singleton] at hd; simp [hd]
    · simp [hS1, lcmUpto_one]
  | succ k hk ih =>
    have hksq : k * k ≤ n := le_trans (Nat.mul_le_mul (Nat.le_succ k) (Nat.le_succ k)) hhsq
    have hkn : k ≤ n := le_trans (Nat.le_mul_self k) hksq
    have ih' := ih hksq
    suffices hpos : ∀ z : ℤ, 0 ≤ z → (z : ℚ) / Nat.lcmUpto (k + 1) ≤ smoothCap n (k + 1) →
        ∃ δ : ℕ → ℤ,
          (∀ d, δ d = -1 ∨ δ d = 0 ∨ δ d = 1) ∧
          (∀ d, d ∉ smoothDivs n (k + 1) → δ d = 0) ∧
          ∑ d ∈ smoothDivs n (k + 1), (δ d : ℚ) / d = (z : ℚ) / Nat.lcmUpto (k + 1) by
      intro z hz
      by_cases hzn : 0 ≤ z
      · have hBpos : (0 : ℚ) < Nat.lcmUpto (k + 1) := by exact_mod_cast Nat.lcmUpto_pos (k + 1)
        have hnonneg : 0 ≤ (z : ℚ) / Nat.lcmUpto (k + 1) := div_nonneg (by exact_mod_cast hzn) hBpos.le
        rw [abs_of_nonneg hnonneg] at hz
        exact hpos z hzn hz
      · have hzn' : 0 ≤ -z := by omega
        have hBpos : (0 : ℚ) < Nat.lcmUpto (k + 1) := by exact_mod_cast Nat.lcmUpto_pos (k + 1)
        have hbound : ((-z : ℤ) : ℚ) / Nat.lcmUpto (k + 1) ≤ smoothCap n (k + 1) := by
          have : |((z : ℚ) / Nat.lcmUpto (k + 1))| = ((-z : ℤ) : ℚ) / Nat.lcmUpto (k + 1) := by
            rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (by omega : z ≤ 0)) hBpos.le)]
            push_cast; ring
          rwa [← this]
        obtain ⟨δ, hδt, hδo, hδs⟩ := hpos (-z) hzn' hbound
        refine ⟨fun d => -δ d, ?_, ?_, ?_⟩
        · intro d; rcases hδt d with h | h | h <;> simp [h]
        · intro d hd; simp [hδo d hd]
        · simp only [Int.cast_neg, neg_div, sum_neg_distrib, hδs, neg_neg]
    intro z hzn hzbound
    by_cases hpp : IsPrimePow (k + 1)
    · have hpp_saved : IsPrimePow (k + 1) := hpp
      obtain ⟨q, e, hq', he, hqe⟩ := hpp
      have hq : q.Prime := hq'.nat_prime
      have hBstep : Nat.lcmUpto (k + 1) = q * Nat.lcmUpto k := by
        have := lcmUpto_prime_pow hq he
        simpa [hqe] using this
      have hsub : smoothDivs n k ⊆ smoothDivs n (k + 1) := by
        intro d hd
        simp only [smoothDivs, Finset.mem_filter] at hd ⊢
        exact ⟨hd.1, hd.2.trans (lcmUpto_dvd_lcmUpto (Nat.le_succ k))⟩
      let D := smoothDivs n (k + 1) \ smoothDivs n k
      let R := (Icc 1 (q - 1)).image (fun m => (k + 1) * m)
      have hRD : R ⊆ D := by
        intro d hd
        obtain ⟨m, hm, rfl⟩ := mem_image.mp hd
        obtain ⟨hm1, hmq⟩ := mem_Icc.mp hm
        have hm_lt_q : m < q := by have := hq.two_le; omega
        rw [Finset.mem_sdiff]
        refine ⟨?_, ?_⟩
        · simp only [smoothDivs, Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨Nat.mul_pos (by omega) hm1, ?_⟩, ?_⟩
          · have hmqe : m ≤ k + 1 := by
              have : q ≤ q ^ e := by
                calc q = q ^ 1 := (pow_one q).symm
                  _ ≤ q ^ e := Nat.pow_le_pow_right hq.pos he
              omega
            exact (Nat.mul_le_mul_left (k + 1) hmqe).trans hhsq
          · have hcop : Nat.Coprime (k + 1) m := by
              rw [← hqe]
              exact (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm1 hm_lt_q)).pow_left e
            have h1 : k + 1 ∣ Nat.lcmUpto (k + 1) := dvd_lcmUpto (by omega) le_rfl
            have h2 : m ∣ Nat.lcmUpto (k + 1) := by
              have hmk : m ≤ k + 1 := by
                have : q ≤ q ^ e := by
                  calc q = q ^ 1 := (pow_one q).symm
                    _ ≤ q ^ e := Nat.pow_le_pow_right hq.pos he
                omega
              exact dvd_lcmUpto hm1 hmk
            exact hcop.mul_dvd_of_dvd_of_dvd h1 h2
        · simp only [smoothDivs, Finset.mem_filter, not_and]
          intro _ hdvd
          have hqe_dvd : q ^ e ∣ Nat.lcmUpto k := by
            rw [hqe]; exact (dvd_mul_right (k + 1) m).trans hdvd
          have hle := (hq.pow_dvd_iff_le_factorization (Nat.lcmUpto_ne_zero k)).mp hqe_dvd
          rw [Nat.factorization_lcmUpto k hq] at hle
          have hpow : q ^ e ≤ k := (Nat.pow_le_pow_right hq.pos hle).trans
            (Nat.pow_log_le_self q (by omega))
          omega
      have hD2 : ∀ d ∈ D, 2 ≤ d := by
        intro d hd
        obtain ⟨hd1, hdnot⟩ := Finset.mem_sdiff.mp hd
        have hdpos : 1 ≤ d := (mem_Icc.mp (mem_filter.mp hd1).1).1
        have hne1 : d ≠ 1 := by
          intro h1; subst h1
          apply hdnot
          simp only [smoothDivs, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨le_rfl, hn⟩, one_dvd _⟩
        omega
      let E := D \ R
      have hE2 : ∀ d ∈ E, 2 ≤ d := fun d hd => hD2 d (sdiff_subset hd)
      have hB1pos : (0 : ℚ) < Nat.lcmUpto (k + 1) := by exact_mod_cast Nat.lcmUpto_pos (k + 1)
      have hqpos : (0 : ℚ) < q := by exact_mod_cast hq.pos
      have hr0 : 0 ≤ (z : ℚ) / Nat.lcmUpto (k + 1) := div_nonneg (by exact_mod_cast hzn) hB1pos.le
      obtain ⟨γ, hγ01, hγout, hnn', hcase⟩ := greedy_reduce E hE2 ((z : ℚ) / Nat.lcmUpto (k + 1)) hr0
      let B1 := Nat.lcmUpto (k + 1)
      let B0 := Nat.lcmUpto k
      let z' : ℤ := z - ∑ d ∈ E, γ d * ((B1 / d : ℕ) : ℤ)
      have hz'_eq : (z' : ℚ) / B1 = (z : ℚ) / B1 - ∑ d ∈ E, (γ d : ℚ) / d := by
        have hsumE : ((∑ d ∈ E, γ d * ((B1 / d : ℕ) : ℤ) : ℤ) : ℚ) =
            (B1 : ℚ) * ∑ d ∈ E, (γ d : ℚ) / d := by
          rw [Int.cast_sum, mul_sum]
          refine sum_congr rfl fun d hd => ?_
          have hdB1 : d ∣ B1 := (mem_filter.mp (Finset.mem_sdiff.mp (sdiff_subset hd)).1).2
          exact cast_mul_div_weight (γ d) hdB1 (by have := hE2 d hd; omega)
        have hcast_z' : (z' : ℚ) = (z : ℚ) - ((∑ d ∈ E, γ d * ((B1 / d : ℕ) : ℤ) : ℤ) : ℚ) :=
          Int.cast_sub _ _
        rw [hcast_z', hsumE, sub_div, mul_div_cancel_left₀ _ hB1pos.ne']
      have hqe_dvd_B1 : q ^ e ∣ B1 := by
        rw [hqe]; exact dvd_lcmUpto (by omega) le_rfl
      let M := B1 / q ^ e
      have hqM : ¬ q ∣ M := by
        have hlog : Nat.log q (k + 1) = e := by rw [← hqe]; exact Nat.log_pow hq.one_lt e
        have := not_dvd_lcmUpto_div_pow (n := k + 1) hq
        rwa [hlog] at this
      have hm_dvd_M : ∀ m, 1 ≤ m → m < q → m ∣ M := by
        intro m hm1 hmq
        have hmk : m ≤ k + 1 := by
          have : q ≤ q ^ e := by
            calc q = q ^ 1 := (pow_one q).symm
              _ ≤ q ^ e := Nat.pow_le_pow_right hq.pos he
          omega
        have hmB1 : m ∣ B1 := dvd_lcmUpto hm1 hmk
        have hcop : Nat.Coprime m (q ^ e) :=
          (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm1 hmq)).symm.pow_right e
        have hmul : q ^ e * M = B1 := Nat.mul_div_cancel' hqe_dvd_B1
        rw [← hmul] at hmB1
        exact hcop.dvd_of_dvd_mul_left hmB1
      have hM_div : ∀ m, 1 ≤ m → m < q → M / m = B1 / ((k + 1) * m) := by
        intro m _ _
        simp [M, ← hqe, Nat.div_div_eq_div_mul]
      have hfinish : ∀ (δR : ℕ → ℤ),
          (∀ d, δR d = -1 ∨ δR d = 0 ∨ δR d = 1) →
          (∀ d, d ∉ R → δR d = 0) →
          let z_rem : ℤ := z' - ∑ d ∈ R, δR d * ((B1 / d : ℕ) : ℤ)
          (q : ℤ) ∣ z_rem →
          |(z_rem : ℚ) / B1| ≤ smoothCap n k →
          ∃ δ : ℕ → ℤ,
            (∀ d, δ d = -1 ∨ δ d = 0 ∨ δ d = 1) ∧
            (∀ d, d ∉ smoothDivs n (k + 1) → δ d = 0) ∧
            ∑ d ∈ smoothDivs n (k + 1), (δ d : ℚ) / d = (z : ℚ) / B1 := by
        intro δR hδRt hδRo z_rem hqdiv hbound0
        obtain ⟨z0, hz0⟩ := hqdiv
        have hz0_eq : (z0 : ℚ) / B0 = (z_rem : ℚ) / B1 := by
          have hB1q : (B1 : ℚ) = (q : ℚ) * B0 := by exact_mod_cast hBstep
          have hz_cast : (z_rem : ℚ) = (q : ℚ) * z0 := by exact_mod_cast hz0
          rw [hz_cast, hB1q, mul_div_mul_left _ _ hqpos.ne']
        have hz0_bound : |(z0 : ℚ) / B0| ≤ smoothCap n k := by rwa [hz0_eq]
        obtain ⟨δ0, hδ0t, hδ0o, hδ0s⟩ := ih' z0 hz0_bound
        let δ : ℕ → ℤ := fun d => δ0 d + γ d + δR d
        have hdisj_ER : Disjoint E R := disjoint_sdiff_self_left
        have hdisj_SD : Disjoint (smoothDivs n k) D := disjoint_sdiff_self_right
        have hdisj_SE : Disjoint (smoothDivs n k) E := hdisj_SD.mono_right sdiff_subset
        have hdisj_SR : Disjoint (smoothDivs n k) R := hdisj_SD.mono_right hRD
        refine ⟨δ, ?_, ?_, ?_⟩
        · intro d
          by_cases hd0 : d ∈ smoothDivs n k
          · have h1 : d ∉ E := Finset.disjoint_left.mp hdisj_SE hd0
            have h2 : d ∉ R := Finset.disjoint_left.mp hdisj_SR hd0
            simp [δ, hγout d h1, hδRo d h2, hδ0t d]
          · by_cases hdE : d ∈ E
            · have h2 : d ∉ R := Finset.disjoint_left.mp hdisj_ER hdE
              have hγ := hγ01 d
              simp only [δ, hδ0o d hd0, hδRo d h2, zero_add, add_zero]
              rcases hγ with h | h <;> simp [h]
            · simp [δ, hδ0o d hd0, hγout d hdE, hδRt d]
        · intro d hd
          have h1 : d ∉ smoothDivs n k := fun h => hd (hsub h)
          have h2 : d ∉ D := fun h => hd (sdiff_subset h)
          have h3 : d ∉ E := fun h => h2 (sdiff_subset h)
          have h4 : d ∉ R := fun h => h2 (hRD h)
          simp [δ, hδ0o d h1, hγout d h3, hδRo d h4]
        · have hS1_eq : smoothDivs n (k + 1) = smoothDivs n k ∪ (E ∪ R) := by
            have hD_eq : D = E ∪ R := (sdiff_union_of_subset hRD).symm
            rw [← hD_eq, union_sdiff_of_subset hsub]
          rw [hS1_eq, sum_union (Finset.disjoint_union_right.mpr ⟨hdisj_SE, hdisj_SR⟩),
            sum_union hdisj_ER]
          have hsum0 : ∑ d ∈ smoothDivs n k, (δ d : ℚ) / d = ∑ d ∈ smoothDivs n k, (δ0 d : ℚ) / d := by
            refine sum_congr rfl fun d hd => ?_
            simp [δ, hγout d (Finset.disjoint_left.mp hdisj_SE hd),
              hδRo d (Finset.disjoint_left.mp hdisj_SR hd)]
          have hsumE : ∑ d ∈ E, (δ d : ℚ) / d = ∑ d ∈ E, (γ d : ℚ) / d := by
            refine sum_congr rfl fun d hd => ?_
            simp [δ, hδ0o d (Finset.disjoint_right.mp hdisj_SE hd),
              hδRo d (Finset.disjoint_left.mp hdisj_ER hd)]
          have hsumR : ∑ d ∈ R, (δ d : ℚ) / d = ∑ d ∈ R, (δR d : ℚ) / d := by
            refine sum_congr rfl fun d hd => ?_
            simp [δ, hδ0o d (Finset.disjoint_right.mp hdisj_SR hd),
              hγout d (Finset.disjoint_right.mp hdisj_ER hd)]
          have hsumR_int : ((∑ d ∈ R, δR d * ((B1 / d : ℕ) : ℤ) : ℤ) : ℚ) =
              (B1 : ℚ) * ∑ d ∈ R, (δR d : ℚ) / d := by
            rw [Int.cast_sum, mul_sum]
            refine sum_congr rfl fun d hd => ?_
            have hdB1 : d ∣ B1 := (mem_filter.mp (Finset.mem_sdiff.mp (hRD hd)).1).2
            exact cast_mul_div_weight (δR d) hdB1 (by have := hD2 d (hRD hd); omega)
          have hz_rem_q : (z_rem : ℚ) / B1 = (z' : ℚ) / B1 - ∑ d ∈ R, (δR d : ℚ) / d := by
            have hcast_zr : (z_rem : ℚ) = (z' : ℚ) - ((∑ d ∈ R, δR d * ((B1 / d : ℕ) : ℤ) : ℤ) : ℚ) :=
              Int.cast_sub _ _
            rw [hcast_zr, hsumR_int, sub_div, mul_div_cancel_left₀ _ hB1pos.ne']
          rw [hsum0, hsumE, hsumR, hδ0s, hz0_eq, hz_rem_q, hz'_eq]
          ring
      have hMk_ge1 : 1 ≤ smoothCap n k := smoothCap_ge_one hn hk hkn
      rcases hcase with hle1 | ⟨hallE, hgt1⟩
      · -- Case 1: 0 ≤ (z' : ℚ) / B1 ≤ 1
        by_cases hqz' : (q : ℤ) ∣ z'
        · refine hfinish (fun _ => 0) (fun _ => Or.inr (Or.inl rfl)) (fun _ _ => rfl)
            (by simpa using hqz') ?_
          simp only [zero_mul, sum_const_zero, sub_zero]
          rw [hz'_eq, abs_of_nonneg hnn']
          exact hle1.trans hMk_ge1
        · obtain ⟨m, hm1, hmq, hhit⟩ := mod_q_residue_hit hq hqM hm_dvd_M z' hqz'
          let dStar := (k + 1) * m
          have hdStar_mem : dStar ∈ R := mem_image.mpr ⟨m, mem_Icc.mpr ⟨hm1, by omega⟩, rfl⟩
          have hdStar_ge2 : 2 ≤ dStar := hD2 dStar (hRD hdStar_mem)
          let δR : ℕ → ℤ := fun d => if d = dStar then 1 else 0
          have hsumR : ∑ d ∈ R, δR d * ((B1 / d : ℕ) : ℤ) = ((B1 / dStar : ℕ) : ℤ) := by
            rw [Finset.sum_eq_single dStar]
            · simp [δR]
            · intro d _ hne; simp [δR, hne]
            · intro h; exact absurd hdStar_mem h
          have hqdiv : (q : ℤ) ∣ z' - ∑ d ∈ R, δR d * ((B1 / d : ℕ) : ℤ) := by
            rw [hsumR, ← hM_div m hm1 hmq]
            exact hhit
          have hsumR_q : ((B1 / dStar : ℕ) : ℚ) / B1 = (1 : ℚ) / dStar := by
            have hdB1 : dStar ∣ B1 := (mem_filter.mp (Finset.mem_sdiff.mp (hRD hdStar_mem)).1).2
            rw [div_cast_eq hdB1 (by omega), div_div_cancel_left' hB1pos.ne', one_div]
          refine hfinish δR (fun d => by by_cases h : d = dStar <;> simp [δR, h])
            (fun d hd => by simp [δR, show d ≠ dStar from fun h => hd (h ▸ hdStar_mem)]) hqdiv ?_
          have hrem_eq : ((z' - ∑ d ∈ R, δR d * ((B1 / d : ℕ) : ℤ) : ℤ) : ℚ) / B1 =
              (z : ℚ) / B1 - ∑ d ∈ E, (γ d : ℚ) / d - 1 / dStar := by
            rw [hsumR, Int.cast_sub, Int.cast_natCast, sub_div, hz'_eq, hsumR_q]
          rw [hrem_eq]
          have hd_inv_le : (1 : ℚ) / dStar ≤ 1 := by
            have : (1 : ℚ) ≤ dStar := by exact_mod_cast (show 1 ≤ dStar by omega)
            exact div_le_one_of_le₀ this (by positivity)
          have hd_inv_pos : (0 : ℚ) < 1 / dStar := by
            have : (0 : ℚ) < dStar := by exact_mod_cast (show 0 < dStar by omega)
            positivity
          have habs : |(z : ℚ) / B1 - ∑ d ∈ E, (γ d : ℚ) / d - 1 / dStar| ≤ 1 := by
            rw [abs_le]; constructor <;> linarith
          exact habs.trans hMk_ge1
      · -- Case 2: 1 < (z' : ℚ) / B1 and γ ≡ 1 on E
        have hsumE_all : ∑ d ∈ E, (γ d : ℚ) / d = ∑ d ∈ E, (1 : ℚ) / d :=
          sum_congr rfl fun d hd => by simp [hallE d hd]
        have hsumR_lt1 : ∑ d ∈ R, (1 : ℚ) / d < 1 := by
          have hinj : ∀ m₁ ∈ Icc 1 (q - 1), ∀ m₂ ∈ Icc 1 (q - 1),
              (k + 1) * m₁ = (k + 1) * m₂ → m₁ = m₂ := fun m₁ _ m₂ _ h =>
            Nat.eq_of_mul_eq_mul_left (by omega) h
          rw [sum_image hinj]
          calc ∑ m ∈ Icc 1 (q - 1), (1 : ℚ) / ((k + 1) * m : ℕ)
              ≤ ∑ _m ∈ Icc 1 (q - 1), (1 : ℚ) / ((k + 1 : ℕ) : ℚ) := by
                refine sum_le_sum fun m hm => ?_
                have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
                have hle : ((k + 1 : ℕ) : ℚ) ≤ ((k + 1) * m : ℕ) := by
                  exact_mod_cast Nat.le_mul_of_pos_right (k + 1) (by omega)
                exact one_div_le_one_div_of_le (by exact_mod_cast (show 0 < k + 1 by omega)) hle
            _ = ((q - 1 : ℕ) : ℚ) / ((k + 1 : ℕ) : ℚ) := by
                rw [sum_const, Nat.card_Icc, Nat.sub_add_cancel (by have := hq.two_le; omega),
                  nsmul_eq_mul, mul_one_div]
            _ < 1 := by
                have hqle : q ≤ k + 1 := by
                  rw [← hqe]
                  calc q = q ^ 1 := (pow_one q).symm
                    _ ≤ q ^ e := Nat.pow_le_pow_right hq.pos he
                have hlt : (q - 1 : ℕ) < k + 1 := by have := hq.two_le; omega
                rw [div_lt_one (by positivity)]
                exact_mod_cast hlt
        have hcap_step : smoothCap n (k + 1) =
            smoothCap n k + (∑ d ∈ D, (1 : ℚ) / d) - (1 : ℚ) / (k + 1) := by
          have hsum_split : ∑ d ∈ smoothDivs n (k + 1), (1 : ℚ) / d =
              (∑ d ∈ smoothDivs n k, (1 : ℚ) / d) + ∑ d ∈ D, (1 : ℚ) / d := by
            rw [← sum_sdiff hsub, add_comm]
          have hpp_split : ∑ j ∈ (Icc 2 (k + 1)).filter IsPrimePow, (1 : ℚ) / j =
              (∑ j ∈ (Icc 2 k).filter IsPrimePow, (1 : ℚ) / j) + (1 : ℚ) / (k + 1) := by
            have hfilt : (Icc 2 (k + 1)).filter IsPrimePow =
                insert (k + 1) ((Icc 2 k).filter IsPrimePow) := by
              ext j; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
              constructor
              · rintro ⟨⟨h2, hj⟩, hjpp⟩
                by_cases hjk : j = k + 1
                · exact Or.inl hjk
                · exact Or.inr ⟨⟨h2, by omega⟩, hjpp⟩
              · rintro (rfl | ⟨⟨h2, hj⟩, hjpp⟩)
                · exact ⟨⟨by omega, le_rfl⟩, hpp_saved⟩
                · exact ⟨⟨h2, by omega⟩, hjpp⟩
            rw [hfilt, sum_insert (by simp)]
            push_cast; ring
          dsimp [smoothCap]
          rw [hsum_split, hpp_split]
          ring
        have hsumD_eq : ∑ d ∈ D, (1 : ℚ) / d = (∑ d ∈ E, (1 : ℚ) / d) + ∑ d ∈ R, (1 : ℚ) / d := by
          rw [← sum_sdiff hRD, add_comm]
        let sumR_int : ℤ := ∑ d ∈ R, ((B1 / d : ℕ) : ℤ)
        have hsumR_q : (sumR_int : ℚ) / B1 = ∑ d ∈ R, (1 : ℚ) / d := by
          have hcast_sR : (sumR_int : ℚ) = ∑ d ∈ R, ((B1 / d : ℕ) : ℚ) := by
            show ((∑ d ∈ R, ((B1 / d : ℕ) : ℤ) : ℤ) : ℚ) = _
            rw [Int.cast_sum]
            refine sum_congr rfl fun d _ => Int.cast_natCast _
          rw [hcast_sR, sum_div]
          refine sum_congr rfl fun d hd => ?_
          have hdB1 : d ∣ B1 := (mem_filter.mp (Finset.mem_sdiff.mp (hRD hd)).1).2
          rw [div_cast_eq hdB1 (by have := hD2 d (hRD hd); omega),
            div_div_cancel_left' hB1pos.ne', one_div]
        let rem : ℤ := z' - sumR_int
        by_cases hqrem : (q : ℤ) ∣ rem
        · let δR : ℕ → ℤ := fun d => if d ∈ R then 1 else 0
          have hsumR_eq : ∑ d ∈ R, δR d * ((B1 / d : ℕ) : ℤ) = sumR_int := by
            refine sum_congr rfl fun d hd => by simp [δR, hd]
          refine hfinish δR (fun d => by by_cases h : d ∈ R <;> simp [δR, h])
            (fun d hd => by simp [δR, hd]) (by rwa [hsumR_eq]) ?_
          have hrem_eq : ((z' - ∑ d ∈ R, δR d * ((B1 / d : ℕ) : ℤ) : ℤ) : ℚ) / B1 =
              (z : ℚ) / B1 - ∑ d ∈ E, (1 : ℚ) / d - ∑ d ∈ R, (1 : ℚ) / d := by
            rw [hsumR_eq, Int.cast_sub, sub_div, hz'_eq, hsumR_q, hsumE_all]
          rw [hrem_eq]
          have hval_pos : 0 < (z : ℚ) / B1 - ∑ d ∈ E, (1 : ℚ) / d - ∑ d ∈ R, (1 : ℚ) / d := by
            rw [← hsumE_all]; linarith
          rw [abs_of_pos hval_pos]
          have hinv_pos : (0 : ℚ) < 1 / (k + 1) := by positivity
          linarith
        · have hqneg : ¬ (q : ℤ) ∣ -rem := fun h => hqrem (dvd_neg.mp h)
          obtain ⟨m, hm1, hmq, hhit⟩ := mod_q_residue_hit hq hqM hm_dvd_M (-rem) hqneg
          let dDrop := (k + 1) * m
          have hdDrop_mem : dDrop ∈ R := mem_image.mpr ⟨m, mem_Icc.mpr ⟨hm1, by omega⟩, rfl⟩
          let δR : ℕ → ℤ := fun d => if d ∈ R ∧ d ≠ dDrop then 1 else 0
          have hsumR_eq : ∑ d ∈ R, δR d * ((B1 / d : ℕ) : ℤ) = sumR_int - ((B1 / dDrop : ℕ) : ℤ) := by
            have h1 : sumR_int = ((B1 / dDrop : ℕ) : ℤ) + ∑ d ∈ R.erase dDrop, ((B1 / d : ℕ) : ℤ) :=
              (add_sum_erase R (fun d => ((B1 / d : ℕ) : ℤ)) hdDrop_mem).symm
            have h2 : ∑ d ∈ R, δR d * ((B1 / d : ℕ) : ℤ) =
                ∑ d ∈ R.erase dDrop, ((B1 / d : ℕ) : ℤ) := by
              rw [← add_sum_erase R _ hdDrop_mem]
              simp only [δR, ne_eq, not_true_eq_false, and_false, ↓reduceIte, zero_mul, zero_add]
              refine sum_congr rfl fun d hd => ?_
              have ⟨hne, hmem⟩ := mem_erase.mp hd
              simp [hmem, hne]
            linarith
          have hqdiv : (q : ℤ) ∣ z' - ∑ d ∈ R, δR d * ((B1 / d : ℕ) : ℤ) := by
            rw [hsumR_eq]
            have heq : z' - (sumR_int - ((B1 / dDrop : ℕ) : ℤ)) = -((-rem) - ((M / m : ℕ) : ℤ)) := by
              rw [hM_div m hm1 hmq]; dsimp [rem, dDrop]; ring
            rw [heq]
            exact dvd_neg.mpr hhit
          have hdDrop_q : ((B1 / dDrop : ℕ) : ℚ) / B1 = (1 : ℚ) / dDrop := by
            have hdB1 : dDrop ∣ B1 := (mem_filter.mp (Finset.mem_sdiff.mp (hRD hdDrop_mem)).1).2
            rw [div_cast_eq hdB1 (by have := hD2 dDrop (hRD hdDrop_mem); omega),
              div_div_cancel_left' hB1pos.ne', one_div]
          refine hfinish δR (fun d => by by_cases h : d ∈ R ∧ d ≠ dDrop <;> simp [δR, h])
            (fun d hd => by simp [δR, hd]) hqdiv ?_
          have hrem_eq : ((z' - ∑ d ∈ R, δR d * ((B1 / d : ℕ) : ℤ) : ℤ) : ℚ) / B1 =
              (z : ℚ) / B1 - ∑ d ∈ E, (1 : ℚ) / d - (∑ d ∈ R, (1 : ℚ) / d - 1 / dDrop) := by
            rw [hsumR_eq, show (z' - (sumR_int - ((B1 / dDrop : ℕ) : ℤ)) : ℤ) =
                z' - sumR_int + ((B1 / dDrop : ℕ) : ℤ) by ring,
              Int.cast_add, Int.cast_sub, Int.cast_natCast, add_div, sub_div,
              hz'_eq, hsumR_q, hdDrop_q, hsumE_all]
            ring
          rw [hrem_eq]
          have hdDrop_pos : (0 : ℚ) < 1 / dDrop := by
            have : (0 : ℚ) < dDrop := by exact_mod_cast (show 0 < dDrop by have := hD2 dDrop (hRD hdDrop_mem); omega)
            positivity
          have hdDrop_le : (1 : ℚ) / dDrop ≤ 1 / (k + 1) := by
            have hle : (k + 1 : ℕ) ≤ dDrop := Nat.le_mul_of_pos_right (k + 1) (by omega)
            have hle' : ((k : ℚ) + 1) ≤ dDrop := by exact_mod_cast hle
            exact one_div_le_one_div_of_le (by positivity) hle'
          have hval_pos : 0 < (z : ℚ) / B1 - ∑ d ∈ E, (1 : ℚ) / d - (∑ d ∈ R, (1 : ℚ) / d - 1 / dDrop) := by
            rw [← hsumE_all]; linarith
          rw [abs_of_pos hval_pos]
          linarith
    · have hBstep : Nat.lcmUpto (k + 1) = Nat.lcmUpto k := by
        simpa using lcmUpto_eq_self_of_not_isPrimePow (by omega) hpp
      have hdivs : smoothDivs n (k + 1) = smoothDivs n k := by simp [smoothDivs, hBstep]
      have hfilt : (Icc 2 (k + 1)).filter IsPrimePow = (Icc 2 k).filter IsPrimePow := by
        ext j; simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨h2, hj⟩, hjpp⟩
          exact ⟨⟨h2, by have : j ≠ k + 1 := fun h => hpp (h ▸ hjpp); omega⟩, hjpp⟩
        · rintro ⟨⟨h2, hj⟩, hjpp⟩
          exact ⟨⟨h2, by omega⟩, hjpp⟩
      have hcap : smoothCap n (k + 1) = smoothCap n k := by dsimp [smoothCap]; rw [hdivs, hfilt]
      rw [hBstep, hdivs]
      rw [hBstep, hcap] at hzbound
      have hBpos : (0 : ℚ) < Nat.lcmUpto k := by exact_mod_cast Nat.lcmUpto_pos k
      exact ih' z (by rw [abs_of_nonneg (div_nonneg (by exact_mod_cast hzn) hBpos.le)]; exact hzbound)
theorem smooth_grid_descent {n : ℕ} (hn : 1 ≤ n) (z : ℤ) :
    let smoothDivs := fun n h : ℕ => (Icc 1 n).filter (· ∣ Nat.lcmUpto h)
    let smoothCap := fun n h : ℕ =>
      (∑ d ∈ smoothDivs n h, (1 : ℚ) / d) - ∑ k ∈ (Icc 2 h).filter IsPrimePow, (1 : ℚ) / k
    |(z : ℚ) / Nat.lcmUpto n.sqrt| ≤ smoothCap n n.sqrt →
    ∃ δ : Fin n → ℤ,
      (∀ i, δ i = -1 ∨ δ i = 0 ∨ δ i = 1) ∧
      (∀ i, ¬ (i.val + 1 ∣ Nat.lcmUpto n.sqrt) → δ i = 0) ∧
      ∑ i : Fin n, (δ i : ℚ) / (i.val + 1) = (z : ℚ) / Nat.lcmUpto n.sqrt := by
  intro smoothDivs smoothCap hz
  have hsq1 : 1 ≤ n.sqrt := Nat.le_sqrt.mpr (by simpa using hn)
  have hsqle : n.sqrt * n.sqrt ≤ n := Nat.sqrt_le n
  obtain ⟨δ, hδt, hδo, hδs⟩ := smooth_grid_descent_aux hn hsq1 hsqle z hz
  refine ⟨fun i => δ (i.val + 1), fun i => hδt (i.val + 1), ?_, ?_⟩
  · intro i hnd
    apply hδo (i.val + 1)
    simp [hnd]
  · rw [← hδs]
    have hbij : ∑ i : Fin n, (δ (i.val + 1) : ℚ) / (i.val + 1) =
        ∑ d ∈ Icc 1 n, (δ d : ℚ) / d := by
      refine Finset.sum_bij (fun i _ => i.val + 1) ?_ ?_ ?_ ?_
      · intro i _; exact mem_Icc.mpr ⟨by omega, by omega⟩
      · intro i _ j _ h; exact Fin.ext (by omega)
      · intro d hd
        obtain ⟨hd1, hdn⟩ := mem_Icc.mp hd
        exact ⟨⟨d - 1, by omega⟩, mem_univ _, by simp; omega⟩
      · intro i _; push_cast; rfl
    rw [hbij]
    symm
    refine Finset.sum_subset (filter_subset _ _) fun d hd hnot => ?_
    simp [hδo d hnot]

/- ## Section 3: Elementary Analytic Dominance (`Theorem 2`) -/

lemma one_sub_inv_le_log_of_pos {x : ℝ} (hx : 0 < x) : 1 - x⁻¹ ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at h
  linarith

lemma log_add_one_le_harmonic (n : ℕ) : Real.log ((n : ℝ) + 1) ≤ ∑ d ∈ Icc 1 n, (1 : ℝ) / d := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hstep : Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
      rw [← Real.log_div hk2.ne' hk1.ne']
      calc Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1))
          ≤ ((k : ℝ) + 2) / ((k : ℝ) + 1) - 1 :=
            Real.log_le_sub_one_of_pos (div_pos hk2 hk1)
        _ = 1 / ((k : ℝ) + 1) := by field_simp; ring
    have heq : (((k + 1 : ℕ) : ℝ) + 1) = (k : ℝ) + 2 := by push_cast; ring
    rw [heq]
    push_cast
    linarith

lemma harmonic_le_one_add_log {m : ℕ} (hm : 1 ≤ m) :
    ∑ d ∈ Icc 1 m, (1 : ℝ) / d ≤ 1 + Real.log m := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hstep : 1 / ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) - Real.log k := by
      rw [← Real.log_div hk1.ne' hk0.ne']
      calc 1 / ((k : ℝ) + 1)
          = 1 - (((k : ℝ) + 1) / k)⁻¹ := by field_simp; ring
        _ ≤ Real.log (((k : ℝ) + 1) / k) := one_sub_inv_le_log_of_pos (div_pos hk1 hk0)
    push_cast
    linarith

lemma inv_mul_log_le_log_log_diff {k : ℕ} (hk : 3 ≤ k) :
    (1 : ℝ) / (k * Real.log k) ≤ Real.log (Real.log k) - Real.log (Real.log ((k - 1 : ℕ))) := by
  have hk_pos : (0 : ℝ) < k := by positivity
  have hk1_pos : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hk1_gt1 : (1 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 1 < k - 1 by omega)
  have hk_gt1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hlogk : 0 < Real.log k := Real.log_pos hk_gt1
  have hlogk1 : 0 < Real.log ((k - 1 : ℕ)) := Real.log_pos hk1_gt1
  have h1 : (1 : ℝ) / k ≤ Real.log k - Real.log ((k - 1 : ℕ)) := by
    rw [← Real.log_div hk_pos.ne' hk1_pos.ne']
    have hsub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    calc (1 : ℝ) / k = 1 - ((k : ℝ) / ((k - 1 : ℕ) : ℝ))⁻¹ := by
          rw [hsub]; field_simp [hk_pos.ne']; ring
      _ ≤ Real.log ((k : ℝ) / ((k - 1 : ℕ) : ℝ)) :=
          one_sub_inv_le_log_of_pos (div_pos hk_pos hk1_pos)
  have h2 : (1 : ℝ) / (k * Real.log k) ≤ 1 - (Real.log k / Real.log ((k - 1 : ℕ)))⁻¹ := by
    have hdiv := div_le_div_of_nonneg_right h1 hlogk.le
    calc (1 : ℝ) / (k * Real.log k)
        = ((1 : ℝ) / k) / Real.log k := by ring
      _ ≤ (Real.log k - Real.log ((k - 1 : ℕ))) / Real.log k := hdiv
      _ = 1 - (Real.log k / Real.log ((k - 1 : ℕ)))⁻¹ := by
          field_simp [hlogk.ne', hlogk1.ne']
  calc (1 : ℝ) / (k * Real.log k)
      ≤ 1 - (Real.log k / Real.log ((k - 1 : ℕ)))⁻¹ := h2
    _ ≤ Real.log (Real.log k / Real.log ((k - 1 : ℕ))) :=
        one_sub_inv_le_log_of_pos (div_pos hlogk hlogk1)
    _ = Real.log (Real.log k) - Real.log (Real.log ((k - 1 : ℕ))) :=
        Real.log_div hlogk.ne' hlogk1.ne'

lemma sum_inv_mul_log_le {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∑ k ∈ Ioc a b, (1 : ℝ) / (k * Real.log k) ≤ Real.log (Real.log b) - Real.log (Real.log a) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [sum_Ioc_succ_top hm]
    have hstep := inv_mul_log_le_log_log_diff (k := m + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hstep
    linarith

lemma sum_inv_ge_log_diff {a b : ℕ} (_ha : 1 ≤ a) (hab : a ≤ b) :
    Real.log ((b : ℝ) + 1) - Real.log ((a : ℝ) + 1) ≤ ∑ k ∈ Ioc a b, (1 : ℝ) / k := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [sum_Ioc_succ_top hm]
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have hstep : Real.log ((m : ℝ) + 2) - Real.log ((m : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      rw [← Real.log_div hm2.ne' hm1.ne']
      calc Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1))
          ≤ ((m : ℝ) + 2) / ((m : ℝ) + 1) - 1 := Real.log_le_sub_one_of_pos (div_pos hm2 hm1)
        _ = 1 / ((m : ℝ) + 1) := by field_simp; ring
    have heq : (((m + 1 : ℕ) : ℝ) + 1) = (m : ℝ) + 2 := by push_cast; ring
    rw [heq]; push_cast; linarith

lemma sum_by_parts_Ioc (A f : ℕ → ℝ) {a b : ℕ} (hab : a < b) :
    ∑ k ∈ Ioc a b, (A k - A (k - 1)) * f k =
      A b * f b - A a * f (a + 1) + ∑ k ∈ Ico (a + 1) b, A k * (f k - f (k + 1)) := by
  induction b, hab using Nat.le_induction with
  | base =>
    rw [Nat.Ioc_succ_singleton, sum_singleton, Ico_self, sum_empty]
    simp; ring
  | succ m hm ih =>
    rw [sum_Ioc_succ_top (by omega : a ≤ m), sum_Ico_succ_top hm, ih]
    simp only [Nat.add_sub_cancel]
    ring

lemma discrete_abel_bound (A f : ℕ → ℝ) (C : ℝ) {a b : ℕ} (hab : a < b)
    (hAa : 0 ≤ A a)
    (hAC : ∀ k, a + 1 ≤ k → k ≤ b → A k ≤ C * k)
    (hf_anti : ∀ k, a + 1 ≤ k → k < b → f (k + 1) ≤ f k)
    (hfb : 0 ≤ f b) (hfa : 0 ≤ f (a + 1)) :
    ∑ k ∈ Ioc a b, (A k - A (k - 1)) * f k ≤
      C * ((a + 1 : ℕ) * f (a + 1) + ∑ k ∈ Ioc (a + 1) b, f k) := by
  rw [sum_by_parts_Ioc A f hab]
  have h1 : A b * f b ≤ (C * b) * f b :=
    mul_le_mul_of_nonneg_right (hAC b (by omega) le_rfl) hfb
  have h2 : 0 ≤ A a * f (a + 1) := mul_nonneg hAa hfa
  have h3 : ∑ k ∈ Ico (a + 1) b, A k * (f k - f (k + 1)) ≤
      ∑ k ∈ Ico (a + 1) b, (C * k) * (f k - f (k + 1)) := by
    refine sum_le_sum fun k hk => ?_
    obtain ⟨hk1, hkb⟩ := mem_Ico.mp hk
    exact mul_le_mul_of_nonneg_right (hAC k hk1 hkb.le) (sub_nonneg.mpr (hf_anti k hk1 hkb))
  have hid := sum_by_parts_Ioc (fun k => (k : ℝ)) f hab
  have hdiff : ∑ k ∈ Ioc a b, ((k : ℝ) - ((k - 1 : ℕ) : ℝ)) * f k =
      f (a + 1) + ∑ k ∈ Ioc (a + 1) b, f k := by
    have hsplit : Ioc a b = insert (a + 1) (Ioc (a + 1) b) := by
      ext k; simp only [mem_Ioc, mem_insert]; omega
    rw [hsplit, sum_insert (by simp)]
    have h1eq : (((a + 1 : ℕ) : ℝ) - ((a : ℕ) : ℝ)) * f (a + 1) = f (a + 1) := by
      push_cast; ring
    have hrest : ∑ k ∈ Ioc (a + 1) b, ((k : ℝ) - ((k - 1 : ℕ) : ℝ)) * f k =
        ∑ k ∈ Ioc (a + 1) b, f k := by
      refine sum_congr rfl fun k hk => ?_
      have hk1 : 1 ≤ k := by have := (mem_Ioc.mp hk).1; omega
      rw [Nat.cast_sub hk1]; push_cast; ring
    rw [Nat.add_sub_cancel, h1eq, hrest]
  have hid2 : (b : ℝ) * f b + ∑ k ∈ Ico (a + 1) b, (k : ℝ) * (f k - f (k + 1)) =
      ((a + 1 : ℕ) : ℝ) * f (a + 1) + ∑ k ∈ Ioc (a + 1) b, f k := by
    rw [hdiff] at hid
    push_cast at hid ⊢
    linarith
  have hpull : (C * b) * f b + ∑ k ∈ Ico (a + 1) b, (C * k) * (f k - f (k + 1)) =
      C * ((b : ℝ) * f b + ∑ k ∈ Ico (a + 1) b, (k : ℝ) * (f k - f (k + 1))) := by
    rw [mul_add, mul_sum]
    congr 1
    · ring
    · refine sum_congr rfl fun k _ => by ring
  rw [hid2] at hpull
  linarith

lemma theta_step (k : ℕ) (hk : 1 ≤ k) :
    Chebyshev.theta k - Chebyshev.theta (k - 1 : ℕ) = if k.Prime then Real.log k else 0 := by
  rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  have hIcc : Icc 0 k = insert k (Icc 0 (k - 1)) := by
    ext j; simp only [mem_Icc, mem_insert]; omega
  rw [sum_filter, sum_filter, hIcc, sum_insert (by simp; omega)]
  ring

lemma discrete_abel_theta (f : ℕ → ℝ) {a b : ℕ} (hab : a < b)
    (hf_anti : ∀ k, a + 1 ≤ k → k < b → f (k + 1) ≤ f k)
    (hfb : 0 ≤ f b) (hfa : 0 ≤ f (a + 1)) :
    ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log p * f p ≤
      Real.log 4 * ((a + 1 : ℕ) * f (a + 1) + ∑ k ∈ Ioc (a + 1) b, f k) := by
  have heq : ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log p * f p =
      ∑ k ∈ Ioc a b, (Chebyshev.theta k - Chebyshev.theta (k - 1 : ℕ)) * f k := by
    rw [sum_filter]
    refine sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := by have := (mem_Ioc.mp hk).1; omega
    rw [theta_step k hk1]
    split_ifs <;> simp
  rw [heq]
  exact discrete_abel_bound (fun k => Chebyshev.theta k) f (Real.log 4) hab
    (Chebyshev.theta_nonneg _) (fun k _ _ => Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg k))
    hf_anti hfb hfa

lemma sum_inv_sq_tail_le {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∑ m ∈ Ioc a b, (1 : ℝ) / ((m : ℝ) * m) ≤ 1 / a := by
  have h1 : ∑ m ∈ Ioc a b, (1 : ℝ) / ((m : ℝ) * m) ≤
      ∑ m ∈ Ioc a b, (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) := by
    refine sum_le_sum fun m hm => ?_
    have hm2 : 2 ≤ m := by have := (mem_Ioc.mp hm).1; omega
    have hm_pos : (0 : ℝ) < m := by positivity
    have hm1_pos : (0 : ℝ) < (m - 1 : ℕ) := by exact_mod_cast (show 0 < m - 1 by omega)
    have hm1_eq : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    have hle : ((m - 1 : ℕ) : ℝ) * m ≤ (m : ℝ) * m := by
      rw [hm1_eq]; nlinarith
    calc (1 : ℝ) / ((m : ℝ) * m)
        ≤ 1 / (((m - 1 : ℕ) : ℝ) * m) := one_div_le_one_div_of_le (mul_pos hm1_pos hm_pos) hle
      _ = 1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ) := by
          rw [hm1_eq]; field_simp [hm_pos.ne', (show (m : ℝ) - 1 ≠ 0 by linarith)]; ring
  have htele : ∀ c, a ≤ c → ∑ m ∈ Ioc a c, (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) =
      1 / (a : ℝ) - 1 / (c : ℝ) := by
    intro c hac
    induction c, hac using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [sum_Ioc_succ_top hm, ih, Nat.add_sub_cancel]
      ring
  have h2 := htele b hab
  have hb_nonneg : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
  linarith

lemma sum_comp_primePow_recip_le (H : ℕ) :
    ∑ h ∈ (Icc 2 H).filter (fun h => IsPrimePow h ∧ ¬ h.Prime), (1 : ℝ) / h ≤ 1 := by
  let S := (Icc 2 H) ×ˢ (Icc 2 H)
  have hsub : (Icc 2 H).filter (fun h => IsPrimePow h ∧ ¬ h.Prime) ⊆
      S.image (fun x => x.1 ^ x.2) := by
    intro h hh
    obtain ⟨hIcc, ⟨p, e, hp', he, hpe⟩, hnp⟩ := mem_filter.mp hh
    obtain ⟨_, hH⟩ := mem_Icc.mp hIcc
    have hp : p.Prime := hp'.nat_prime
    have he2 : 2 ≤ e := by
      by_contra! hlt
      have he1 : e = 1 := by omega
      rw [he1, pow_one] at hpe
      exact hnp (hpe ▸ hp)
    have hpH : p ≤ H := by
      calc p ≤ p ^ e := Nat.le_self_pow (by omega) p
        _ = h := hpe
        _ ≤ H := hH
    have heH : e ≤ H := by
      calc e ≤ 2 ^ e := Nat.le_of_lt Nat.lt_two_pow_self
        _ ≤ p ^ e := Nat.pow_le_pow_left hp.two_le e
        _ = h := hpe
        _ ≤ H := hH
    exact mem_image.mpr ⟨(p, e), mem_product.mpr ⟨mem_Icc.mpr ⟨hp.two_le, hpH⟩, mem_Icc.mpr ⟨he2, heH⟩⟩, hpe⟩
  calc ∑ h ∈ (Icc 2 H).filter (fun h => IsPrimePow h ∧ ¬ h.Prime), (1 : ℝ) / h
      ≤ ∑ h ∈ S.image (fun x => x.1 ^ x.2), (1 : ℝ) / h :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ x ∈ S, (1 : ℝ) / ((x.1 ^ x.2 : ℕ) : ℝ) := sum_image_le_of_nonneg fun _ _ => by positivity
    _ = ∑ m ∈ Icc 2 H, ∑ e ∈ Icc 2 H, (1 : ℝ) / (m : ℝ) ^ e := by
        rw [sum_product]; refine sum_congr rfl fun m _ => sum_congr rfl fun e _ => by simp
    _ ≤ ∑ m ∈ Icc 2 H, (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) := by
        refine sum_le_sum fun m hm => ?_
        have hm2 : 2 ≤ m := (mem_Icc.mp hm).1
        have hmH : m ≤ H := (mem_Icc.mp hm).2
        have hH2 : 2 ≤ H := by omega
        have hm_pos : (0 : ℝ) < m := by positivity
        have hm_ge2 : (2 : ℝ) ≤ m := by exact_mod_cast hm2
        have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by linarith
        have hshift : ∑ e ∈ Icc 2 H, (1 : ℝ) / (m : ℝ) ^ e =
            ∑ j ∈ range (H - 1), (1 / ((m : ℝ) ^ 2)) * (1 / (m : ℝ)) ^ j := by
          refine Finset.sum_bij (fun e _ => e - 2) ?_ ?_ ?_ ?_
          · intro e he; obtain ⟨h2, hH⟩ := mem_Icc.mp he; exact mem_range.mpr (by omega)
          · intro e₁ he₁ e₂ he₂ h
            have := (mem_Icc.mp he₁).1; have := (mem_Icc.mp he₂).1; omega
          · intro j hj; exact ⟨j + 2, mem_Icc.mpr ⟨by omega, by have := mem_range.mp hj; omega⟩, by omega⟩
          · intro e he
            have h2 : 2 ≤ e := (mem_Icc.mp he).1
            rw [one_div_pow, one_div_mul_one_div, ← pow_add, Nat.add_sub_cancel' h2]
        have hgeom : ∑ e ∈ Icc 2 H, (1 : ℝ) / (m : ℝ) ^ e ≤ 1 / ((m : ℝ) * ((m : ℝ) - 1)) := by
          rw [hshift, ← mul_sum, geom_sum_eq (by
            intro h1
            have : (m : ℝ) = 1 := by field_simp [hm_pos.ne'] at h1; linarith
            linarith)]
          have h1m : 0 < 1 - (1 : ℝ) / m := by
            rw [sub_pos, div_lt_one hm_pos]; linarith
          have hnum : 1 - ((1 : ℝ) / m) ^ (H - 1) ≤ 1 := by
            have : (0 : ℝ) ≤ ((1 : ℝ) / m) ^ (H - 1) := by positivity
            linarith
          have hfrac : (((1 : ℝ) / m) ^ (H - 1) - 1) / ((1 : ℝ) / m - 1) =
              (1 - ((1 : ℝ) / m) ^ (H - 1)) / (1 - (1 : ℝ) / m) := by
            rw [← neg_div_neg_eq]; ring_nf
          rw [hfrac]
          calc 1 / (m : ℝ) ^ 2 * ((1 - ((1 : ℝ) / m) ^ (H - 1)) / (1 - 1 / m))
              ≤ 1 / (m : ℝ) ^ 2 * (1 / (1 - 1 / m)) := by gcongr
            _ = 1 / ((m : ℝ) * ((m : ℝ) - 1)) := by field_simp [hm_pos.ne', hm1_pos.ne']
        have heq : 1 / ((m : ℝ) * ((m : ℝ) - 1)) = 1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ) := by
          rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
          field_simp [hm_pos.ne', hm1_pos.ne']; ring
        linarith
    _ ≤ 1 := by
        by_cases hH2 : H < 2
        · rw [Icc_eq_empty_of_lt hH2]; simp
        · have htele : ∀ c, 1 ≤ c → ∑ m ∈ Icc 2 c, (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) =
              1 - 1 / (c : ℝ) := by
            intro c hc
            induction c, hc using Nat.le_induction with
            | base => simp
            | succ m hm ih =>
              rw [sum_Icc_succ_top (by omega : 2 ≤ m + 1), ih, Nat.add_sub_cancel]
              ring
          rw [htele H (by omega)]
          have : (0 : ℝ) ≤ 1 / (H : ℝ) := by positivity
          linarith

/-- Helper A: Split rough reciprocals `d ∤ L_H` into primes `p > H` and higher powers `q ≤ H`. -/
lemma rough_harmonic_split {n : ℕ} (hn : 100 ≤ n) :
    let H := n.sqrt
    let r : ℕ → ℕ := fun q => q ^ (Nat.log q H + 1)
    ∑ d ∈ (Icc 1 n).filter (fun d => ¬ d ∣ Nat.lcmUpto H), (1 : ℝ) / d ≤
      (∑ p ∈ (Ioc H n).filter Nat.Prime, (1 : ℝ) / p * (∑ m ∈ Icc 1 (n / p), (1 : ℝ) / m)) +
      (∑ q ∈ Nat.primesLE H, (1 : ℝ) / r q * (∑ m ∈ Icc 1 (n / r q), (1 : ℝ) / m)) := by
  intro H r
  have hH_pos : 0 < H := Nat.sqrt_pos.mpr (by omega)
  have hcover : (Icc 1 n).filter (fun d => ¬ d ∣ Nat.lcmUpto H) ⊆
      (Nat.primesLE n).biUnion (fun q => (Icc 1 (n / r q)).image (fun m => r q * m)) := by
    intro d hd
    obtain ⟨hdIcc, hdnot⟩ := mem_filter.mp hd
    obtain ⟨hd1, hdn⟩ := mem_Icc.mp hdIcc
    have hex : ∃ q k, q.Prime ∧ q ^ k ∣ d ∧ ¬ q ^ k ∣ Nat.lcmUpto H := by
      by_contra! hall
      apply hdnot
      rw [Nat.dvd_iff_prime_pow_dvd_dvd]
      intro q k hq hqk
      exact hall q k hq hqk
    obtain ⟨q, k, hq, hqkd, hqkB⟩ := hex
    have hk_gt : Nat.log q H < k := by
      by_contra! hle
      apply hqkB
      cases k with
      | zero => simp
      | succ k' =>
        have hpow_le : q ^ (k' + 1) ≤ H :=
          (Nat.pow_le_pow_right hq.pos hle).trans (Nat.pow_log_le_self q hH_pos.ne')
        exact dvd_lcmUpto (pow_pos hq.pos _) hpow_le
    have hrd : r q ∣ d := (Nat.pow_dvd_pow q hk_gt).trans hqkd
    obtain ⟨m, hm⟩ := hrd
    have hm1 : 1 ≤ m := by
      by_contra! hm0
      have : m = 0 := by omega
      simp [this] at hm; omega
    have hqn : q ≤ n := by
      have : q ≤ r q := Nat.le_self_pow (by omega) q
      have : r q ≤ d := Nat.le_of_dvd (by omega) ⟨m, hm⟩
      omega
    have hm_le : m ≤ n / r q := by
      rw [Nat.le_div_iff_mul_le (pow_pos hq.pos _), mul_comm, ← hm]
      exact hdn
    exact mem_biUnion.mpr ⟨q, Nat.mem_primesLE.mpr ⟨hqn, hq⟩,
      mem_image.mpr ⟨m, mem_Icc.mpr ⟨hm1, hm_le⟩, hm.symm⟩⟩
  have h1 := sum_le_sum_of_subset_of_nonneg hcover (f := fun d : ℕ => (1 : ℝ) / d)
    (fun _ _ _ => by positivity)
  have h2 : ∑ d ∈ (Nat.primesLE n).biUnion (fun q => (Icc 1 (n / r q)).image (fun m => r q * m)), (1 : ℝ) / d ≤
      ∑ q ∈ Nat.primesLE n, ∑ d ∈ (Icc 1 (n / r q)).image (fun m => r q * m), (1 : ℝ) / d := by
    have hbi : ∀ (s : Finset ℕ) (t : ℕ → Finset ℕ),
        ∑ d ∈ s.biUnion t, (1 : ℝ) / d ≤ ∑ q ∈ s, ∑ d ∈ t q, (1 : ℝ) / d := by
      intro s t
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s has ih =>
        rw [biUnion_insert, sum_insert has]
        have h := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := fun d => (1 : ℝ) / d)
        have hnn : 0 ≤ ∑ d ∈ t a ∩ s.biUnion t, (1 : ℝ) / d := sum_nonneg fun _ _ => by positivity
        linarith
    exact hbi _ _
  have h3 : ∀ q ∈ Nat.primesLE n,
      ∑ d ∈ (Icc 1 (n / r q)).image (fun m => r q * m), (1 : ℝ) / d ≤
      (1 : ℝ) / r q * ∑ m ∈ Icc 1 (n / r q), (1 : ℝ) / m := by
    intro q _
    calc ∑ d ∈ (Icc 1 (n / r q)).image (fun m => r q * m), (1 : ℝ) / d
        ≤ ∑ m ∈ Icc 1 (n / r q), (1 : ℝ) / ((r q * m : ℕ) : ℝ) :=
          sum_image_le_of_nonneg fun _ _ => by positivity
      _ = (1 : ℝ) / r q * ∑ m ∈ Icc 1 (n / r q), (1 : ℝ) / m := by
          rw [mul_sum]; refine sum_congr rfl fun m _ => by push_cast; ring
  have hHn : H ≤ n := Nat.sqrt_le_self n
  have hsplit_p : Nat.primesLE n = Nat.primesLE H ∪ (Ioc H n).filter Nat.Prime := by
    ext q; simp only [mem_union, Nat.mem_primesLE, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨hqn, hqp⟩
      by_cases hqH : q ≤ H
      · exact Or.inl ⟨hqH, hqp⟩
      · exact Or.inr ⟨⟨by omega, hqn⟩, hqp⟩
    · rintro (⟨hqH, hqp⟩ | ⟨⟨_, hqn⟩, hqp⟩)
      · exact ⟨hqH.trans hHn, hqp⟩
      · exact ⟨hqn, hqp⟩
  have hdisj_p : Disjoint (Nat.primesLE H) ((Ioc H n).filter Nat.Prime) := by
    rw [disjoint_left]; intro q hq1 hq2
    have := (Nat.mem_primesLE.mp hq1).1; have := (mem_Ioc.mp (mem_filter.mp hq2).1).1; omega
  have h4 : ∑ q ∈ (Ioc H n).filter Nat.Prime, (1 : ℝ) / r q * (∑ m ∈ Icc 1 (n / r q), (1 : ℝ) / m) =
      ∑ p ∈ (Ioc H n).filter Nat.Prime, (1 : ℝ) / p * (∑ m ∈ Icc 1 (n / p), (1 : ℝ) / m) := by
    refine sum_congr rfl fun p hp => ?_
    have hHlt : H < p := (mem_Ioc.mp (mem_filter.mp hp).1).1
    simp [r, Nat.log_of_lt hHlt]
  calc ∑ d ∈ (Icc 1 n).filter (fun d => ¬ d ∣ Nat.lcmUpto H), (1 : ℝ) / d
      ≤ ∑ q ∈ Nat.primesLE n, (1 : ℝ) / r q * ∑ m ∈ Icc 1 (n / r q), (1 : ℝ) / m :=
        (h1.trans h2).trans (sum_le_sum h3)
    _ = _ := by rw [hsplit_p, sum_union hdisj_p, h4, add_comm]

/-- Helper B: Type 1 rough primes `p ∈ (H, n]` via discrete Abel summation + Chebyshev `θ(x) ≤ (log 4) x`. -/
lemma rough_type1_bound {n : ℕ} (hn : 10000 ≤ n) (hlogn : (1000 : ℝ) ≤ Real.log (n : ℝ)) :
    let H := n.sqrt
    ∑ p ∈ (Ioc H n).filter Nat.Prime, (1 : ℝ) / p * (∑ m ∈ Icc 1 (n / p), (1 : ℝ) / m) ≤
      Real.log 4 * (3 + Real.log 2 + (Real.log 2 - 1 / 2) * Real.log (n : ℝ)) := by
  intro H
  have hH_ge100 : 100 ≤ H := Nat.le_sqrt.mpr (by omega)
  have hH_lt_n : H + 1 < n := by have := Nat.sqrt_le n; nlinarith
  have hn_pos : (0 : ℝ) < n := by positivity
  have hH_sq_gt : n < (H + 1) * (H + 1) := Nat.lt_succ_sqrt n
  let f1 : ℕ → ℝ := fun k => (1 + Real.log (n : ℝ) - Real.log (k : ℝ)) / ((k : ℝ) * Real.log (k : ℝ))
  have hT1_le : ∑ p ∈ (Ioc H n).filter Nat.Prime, (1 : ℝ) / p * (∑ m ∈ Icc 1 (n / p), (1 : ℝ) / m) ≤
      ∑ p ∈ (Ioc H n).filter Nat.Prime, Real.log p * f1 p := by
    refine sum_le_sum fun p hp => ?_
    obtain ⟨hIoc, hpp⟩ := mem_filter.mp hp
    obtain ⟨_, hpn⟩ := mem_Ioc.mp hIoc
    have hnp1 : 1 ≤ n / p := Nat.div_pos hpn hpp.pos
    have hharm := harmonic_le_one_add_log hnp1
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hpp.one_lt)
    have hdiv_le : ((n / p : ℕ) : ℝ) ≤ (n : ℝ) / p := Nat.cast_div_le
    have hlog_div : Real.log ((n / p : ℕ) : ℝ) ≤ Real.log (n : ℝ) - Real.log (p : ℝ) := by
      rw [← Real.log_div hn_pos.ne' hp_pos.ne']
      exact Real.log_le_log (by exact_mod_cast hnp1) hdiv_le
    have hEq : Real.log (p : ℝ) * f1 p = (1 : ℝ) / p * (1 + Real.log (n : ℝ) - Real.log (p : ℝ)) := by
      dsimp [f1]; field_simp [hp_pos.ne', hlogp.ne']
    rw [hEq]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hf1_anti : ∀ k, H + 1 ≤ k → k < n → f1 (k + 1) ≤ f1 k := by
    intro k hk hkn
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    have hnum_le : 1 + Real.log (n : ℝ) - Real.log ((k : ℝ) + 1) ≤ 1 + Real.log (n : ℝ) - Real.log (k : ℝ) := by
      have := Real.log_le_log hk_pos (show (k : ℝ) ≤ (k : ℝ) + 1 by linarith)
      linarith
    have hnum_nn : 0 ≤ 1 + Real.log (n : ℝ) - Real.log ((k : ℝ) + 1) := by
      have : Real.log ((k : ℝ) + 1) ≤ Real.log (n : ℝ) :=
        Real.log_le_log hk1_pos (by exact_mod_cast (show k + 1 ≤ n by omega))
      linarith
    have hden_le : (k : ℝ) * Real.log (k : ℝ) ≤ ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1) :=
      mul_le_mul (by linarith) (Real.log_le_log hk_pos (by linarith)) hlogk.le hk1_pos.le
    dsimp [f1]
    push_cast
    exact div_le_div₀ (by linarith) hnum_le (mul_pos hk_pos hlogk) hden_le
  have hT1_abel := discrete_abel_theta f1 (a := H) (b := n) (by omega) hf1_anti
    (by
      dsimp [f1]
      rw [add_sub_cancel_right]
      exact div_nonneg (by norm_num) (mul_pos hn_pos (by linarith)).le)
    (by
      dsimp [f1]
      have hle : Real.log ((H + 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hH_lt_n.le)
      have hlp : 0 < Real.log ((H + 1 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < H + 1 by omega))
      exact div_nonneg (by linarith) (mul_pos (by positivity) hlp).le)
  have hlogH1_ge : Real.log (n : ℝ) / 2 ≤ Real.log ((H + 1 : ℕ) : ℝ) := by
    have hsq : (n : ℝ) ≤ ((H + 1 : ℕ) : ℝ) ^ 2 := by
      have : n ≤ (H + 1) * (H + 1) := hH_sq_gt.le
      rw [sq]; exact_mod_cast this
    have hlog := Real.log_le_log hn_pos hsq
    rw [Real.log_pow] at hlog
    norm_num at hlog
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hlogH1_pos : 0 < Real.log ((H + 1 : ℕ) : ℝ) := by linarith
  have hT1_bdry : ((H + 1 : ℕ) : ℝ) * f1 (H + 1) ≤ 2 := by
    dsimp [f1]
    have hH1p : (0 : ℝ) < (H + 1 : ℕ) := by positivity
    rw [mul_div_assoc', mul_div_mul_left _ _ hH1p.ne', div_le_iff₀ hlogH1_pos]
    linarith
  have hT1_sum : ∑ k ∈ Ioc (H + 1) n, f1 k ≤
      (1 + Real.log (n : ℝ)) * Real.log 2 - (Real.log (n : ℝ) / 2 - 1) := by
    have hsplit_f1 : ∑ k ∈ Ioc (H + 1) n, f1 k =
        (1 + Real.log (n : ℝ)) * (∑ k ∈ Ioc (H + 1) n, (1 : ℝ) / (k * Real.log k)) -
        ∑ k ∈ Ioc (H + 1) n, (1 : ℝ) / k := by
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun k hk => ?_
      have hk1 : 1 < k := by have := (mem_Ioc.mp hk).1; omega
      have hkp : (0 : ℝ) < k := by positivity
      have hlk : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast hk1)
      dsimp [f1]; field_simp [hkp.ne', hlk.ne']
    rw [hsplit_f1]
    have h1 := sum_inv_mul_log_le (a := H + 1) (b := n) (by omega) hH_lt_n.le
    have h1' : Real.log (Real.log (n : ℝ)) - Real.log (Real.log ((H + 1 : ℕ) : ℝ)) ≤ Real.log 2 := by
      rw [← Real.log_div (by linarith) hlogH1_pos.ne']
      refine Real.log_le_log (div_pos (by linarith) hlogH1_pos) ?_
      rw [div_le_iff₀ hlogH1_pos]; linarith
    have h2 := sum_inv_ge_log_diff (a := H + 1) (b := n) (by omega) hH_lt_n.le
    have hlogH2_le : Real.log (((H + 1 : ℕ) : ℝ) + 1) ≤ Real.log (n : ℝ) / 2 + 1 := by
      have hH_le_sq : (H : ℝ) ≤ Real.sqrt (n : ℝ) := by
        rw [Real.le_sqrt (by positivity) (by positivity), sq]
        exact_mod_cast Nat.sqrt_le n
      have hH2_le : ((H + 1 : ℕ) : ℝ) + 1 ≤ 2 * Real.sqrt (n : ℝ) := by
        have : (100 : ℝ) ≤ H := by exact_mod_cast hH_ge100
        push_cast; linarith
      have hlog := Real.log_le_log (by positivity) hH2_le
      rw [Real.log_mul (by norm_num) (Real.sqrt_pos.mpr hn_pos).ne', Real.log_sqrt hn_pos.le] at hlog
      linarith [Real.log_two_lt_d9]
    have hlogn1 : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn_pos (by linarith)
    have hmul : (1 + Real.log (n : ℝ)) * (∑ k ∈ Ioc (H + 1) n, (1 : ℝ) / (k * Real.log k)) ≤
        (1 + Real.log (n : ℝ)) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (h1.trans h1') (by linarith)
    linarith
  have hlog4_nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  calc ∑ p ∈ (Ioc H n).filter Nat.Prime, (1 : ℝ) / p * (∑ m ∈ Icc 1 (n / p), (1 : ℝ) / m)
      ≤ Real.log 4 * (((H + 1 : ℕ) : ℝ) * f1 (H + 1) + ∑ k ∈ Ioc (H + 1) n, f1 k) :=
        hT1_le.trans hT1_abel
    _ ≤ Real.log 4 * (2 + ((1 + Real.log (n : ℝ)) * Real.log 2 - (Real.log (n : ℝ) / 2 - 1))) :=
        mul_le_mul_of_nonneg_left (by linarith) hlog4_nn
    _ = Real.log 4 * (3 + Real.log 2 + (Real.log 2 - 1 / 2) * Real.log (n : ℝ)) := by ring

/-- Helper C: Type 2 higher rough powers (`q ≤ H`, `r(q) = q^(log_q H + 1) > H`). -/
lemma rough_type2_bound {n : ℕ} (hn : 10000 ≤ n) (hlogn : (1000 : ℝ) ≤ Real.log (n : ℝ))
    (hsq1000 : (1000 : ℝ) ≤ Real.sqrt (n.sqrt : ℝ)) :
    let H := n.sqrt
    let r : ℕ → ℕ := fun q => q ^ (Nat.log q H + 1)
    ∑ q ∈ Nat.primesLE H, (1 : ℝ) / r q * (∑ m ∈ Icc 1 (n / r q), (1 : ℝ) / m) ≤
      (1 / 100) * Real.log (n : ℝ) := by
  intro H r
  have hH_ge100 : 100 ≤ H := Nat.le_sqrt.mpr (by omega)
  have hH_pos : (0 : ℝ) < H := by positivity
  have h_each : ∀ q ∈ Nat.primesLE H,
      ∑ m ∈ Icc 1 (n / r q), (1 : ℝ) / m ≤ 1 + Real.log (n : ℝ) := by
    intro q _
    by_cases hdiv0 : n / r q = 0
    · simp [hdiv0]; linarith
    · have h1 : 1 ≤ n / r q := Nat.pos_of_ne_zero hdiv0
      have hle : n / r q ≤ n := Nat.div_le_self n (r q)
      exact (harmonic_le_one_add_log h1).trans (by gcongr)
  have hsum_rq : ∑ q ∈ Nat.primesLE H, (1 : ℝ) / r q ≤ 3 / Real.sqrt (H : ℝ) := by
    let S := H.sqrt
    have hS_ge10 : 10 ≤ S := Nat.le_sqrt.mpr (by omega)
    have h1 : ∑ q ∈ Nat.primesLE H, (1 : ℝ) / r q ≤
        (∑ q ∈ (Nat.primesLE H).filter (· ≤ S), (1 : ℝ) / r q) +
        (∑ q ∈ (Nat.primesLE H).filter (S < ·), (1 : ℝ) / r q) := by
      rw [← sum_filter_add_sum_filter_not (Nat.primesLE H) (· ≤ S)]
      have : (Nat.primesLE H).filter (fun x => ¬ x ≤ S) = (Nat.primesLE H).filter (S < ·) := by
        ext x; simp [not_le]
      rw [this]
    have hpart1 : ∑ q ∈ (Nat.primesLE H).filter (· ≤ S), (1 : ℝ) / r q ≤ (S : ℝ) / (H : ℝ) := by
      calc ∑ q ∈ (Nat.primesLE H).filter (· ≤ S), (1 : ℝ) / r q
          ≤ ∑ _q ∈ (Nat.primesLE H).filter (· ≤ S), (1 : ℝ) / H := by
            refine sum_le_sum fun q hq => ?_
            have hqp := Nat.prime_of_mem_primesLE (mem_filter.mp hq).1
            have hgt : H < r q := Nat.lt_pow_succ_log_self hqp.one_lt H
            exact one_div_le_one_div_of_le hH_pos (by exact_mod_cast hgt.le)
        _ = (((Nat.primesLE H).filter (· ≤ S)).card : ℝ) / H := by
            rw [sum_const, nsmul_eq_mul, mul_one_div]
        _ ≤ (S : ℝ) / H := by
            have hcard : ((Nat.primesLE H).filter (· ≤ S)).card ≤ S := by
              have hsubS : (Nat.primesLE H).filter (· ≤ S) ⊆ Icc 1 S := fun q hq => by
                obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
                exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hq1).one_le, hq2⟩
              exact (card_le_card hsubS).trans (by simp)
            exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hH_pos.le
    have hpart2 : ∑ q ∈ (Nat.primesLE H).filter (S < ·), (1 : ℝ) / r q ≤ 1 / (S : ℝ) := by
      have hsub2 : (Nat.primesLE H).filter (S < ·) ⊆ Ioc S H := fun q hq => by
        obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
        exact mem_Ioc.mpr ⟨hq2, (Nat.mem_primesLE.mp hq1).1⟩
      calc ∑ q ∈ (Nat.primesLE H).filter (S < ·), (1 : ℝ) / r q
          ≤ ∑ q ∈ (Nat.primesLE H).filter (S < ·), (1 : ℝ) / ((q : ℝ) * q) := by
            refine sum_le_sum fun q hq => ?_
            have hqp := Nat.prime_of_mem_primesLE (mem_filter.mp hq).1
            have hqH := (Nat.mem_primesLE.mp (mem_filter.mp hq).1).1
            have hlog1 : 1 ≤ Nat.log q H := Nat.le_log_of_pow_le hqp.one_lt (by simpa using hqH)
            have hsq_le : q * q ≤ r q := by
              rw [← sq]; exact Nat.pow_le_pow_right hqp.pos (by omega)
            have hq_pos : (0 : ℝ) < q := by exact_mod_cast hqp.pos
            exact one_div_le_one_div_of_le (mul_pos hq_pos hq_pos) (by exact_mod_cast hsq_le)
        _ ≤ ∑ m ∈ Ioc S H, (1 : ℝ) / ((m : ℝ) * m) :=
            sum_le_sum_of_subset_of_nonneg hsub2 fun _ _ _ => by positivity
        _ ≤ 1 / (S : ℝ) := sum_inv_sq_tail_le (by omega) (Nat.sqrt_le_self H)
    have hS_le_sqH : (S : ℝ) ≤ Real.sqrt (H : ℝ) := by
      rw [Real.le_sqrt (by positivity) (by positivity), sq]
      exact_mod_cast Nat.sqrt_le H
    have hsqH_le_2S : Real.sqrt (H : ℝ) ≤ 2 * (S : ℝ) := by
      have hlt : (H : ℝ) < ((S + 1 : ℕ) : ℝ) * ((S + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_sqrt H
      have h1' : (H : ℝ) ≤ (2 * (S : ℝ)) ^ 2 := by
        have hS10 : (10 : ℝ) ≤ S := by exact_mod_cast hS_ge10
        push_cast at hlt; nlinarith
      exact (Real.sqrt_le_left (by positivity)).mpr h1'
    have hSH : (S : ℝ) / H ≤ 1 / Real.sqrt (H : ℝ) := by
      rw [div_le_div_iff₀ hH_pos (Real.sqrt_pos.mpr hH_pos), one_mul]
      have := Real.mul_self_sqrt hH_pos.le
      nlinarith [Real.sqrt_pos.mpr hH_pos]
    have hinvS : 1 / (S : ℝ) ≤ 2 / Real.sqrt (H : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (Real.sqrt_pos.mpr hH_pos)]
      linarith
    calc ∑ q ∈ Nat.primesLE H, (1 : ℝ) / r q
        ≤ (S : ℝ) / H + 1 / (S : ℝ) := by linarith
      _ ≤ 1 / Real.sqrt (H : ℝ) + 2 / Real.sqrt (H : ℝ) := add_le_add hSH hinvS
      _ = 3 / Real.sqrt (H : ℝ) := by ring
  have hT2_1 : ∑ q ∈ Nat.primesLE H, (1 : ℝ) / r q * (∑ m ∈ Icc 1 (n / r q), (1 : ℝ) / m) ≤
      (1 + Real.log (n : ℝ)) * (3 / Real.sqrt (H : ℝ)) := by
    calc ∑ q ∈ Nat.primesLE H, (1 : ℝ) / r q * (∑ m ∈ Icc 1 (n / r q), (1 : ℝ) / m)
        ≤ ∑ q ∈ Nat.primesLE H, (1 : ℝ) / r q * (1 + Real.log (n : ℝ)) :=
          sum_le_sum fun q hq => mul_le_mul_of_nonneg_left (h_each q hq) (by positivity)
      _ = (1 + Real.log (n : ℝ)) * ∑ q ∈ Nat.primesLE H, (1 : ℝ) / r q := by
          rw [← sum_mul, mul_comm]
      _ ≤ (1 + Real.log (n : ℝ)) * (3 / Real.sqrt (H : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum_rq (by linarith)
  have hfrac : 3 / Real.sqrt (H : ℝ) ≤ 3 / 1000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq1000
  have h1 : (1 + Real.log (n : ℝ)) * (3 / Real.sqrt (H : ℝ)) ≤
      (1 + Real.log (n : ℝ)) * (3 / 1000) :=
    mul_le_mul_of_nonneg_left hfrac (by linarith)
  linarith

/-- Helper D: Prime powers `≤ H` reciprocal sum via discrete Abel summation + composite bound `≤ 1`. -/
lemma primePow_recip_bound {n : ℕ} (hn : 10000 ≤ n) :
    ∑ h ∈ (Icc 2 n.sqrt).filter IsPrimePow, (1 : ℝ) / h ≤
      5 + Real.log 4 * Real.log (Real.log (n : ℝ)) := by
  set H := n.sqrt
  have hH_ge100 : 100 ≤ H := Nat.le_sqrt.mpr (by omega)
  have hH_pos : (0 : ℝ) < H := by positivity
  have hsplit_pp : ∑ h ∈ (Icc 2 H).filter IsPrimePow, (1 : ℝ) / h =
      (∑ p ∈ (Icc 2 H).filter Nat.Prime, (1 : ℝ) / p) +
      ∑ h ∈ (Icc 2 H).filter (fun h => IsPrimePow h ∧ ¬ h.Prime), (1 : ℝ) / h := by
    rw [← sum_filter_add_sum_filter_not ((Icc 2 H).filter IsPrimePow) Nat.Prime]
    congr 1
    · congr 1; ext x; simp only [Finset.mem_filter]
      exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, h2.isPrimePow⟩, h2⟩⟩
    · congr 1; ext x; simp only [Finset.mem_filter, and_assoc]
  rw [hsplit_pp]
  have hcomp := sum_comp_primePow_recip_le H
  have hprimes_split : ∑ p ∈ (Icc 2 H).filter Nat.Prime, (1 : ℝ) / p =
      (1 : ℝ) / 2 + 1 / 3 + ∑ p ∈ (Ioc 3 H).filter Nat.Prime, (1 : ℝ) / p := by
    have hset : (Icc 2 H).filter Nat.Prime =
        insert 2 (insert 3 ((Ioc 3 H).filter Nat.Prime)) := by
      ext p; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_insert]
      constructor
      · rintro ⟨⟨h2, hH⟩, hp⟩
        by_cases h2p : p = 2
        · exact Or.inl h2p
        · by_cases h3p : p = 3
          · exact Or.inr (Or.inl h3p)
          · exact Or.inr (Or.inr ⟨⟨by omega, hH⟩, hp⟩)
      · rintro (rfl | rfl | ⟨⟨h3, hH⟩, hp⟩)
        · exact ⟨⟨le_rfl, by omega⟩, Nat.prime_two⟩
        · exact ⟨⟨by omega, by omega⟩, Nat.prime_three⟩
        · exact ⟨⟨by omega, hH⟩, hp⟩
    rw [hset, sum_insert (by simp), sum_insert (by simp)]
    norm_num; ring
  rw [hprimes_split]
  let g : ℕ → ℝ := fun k => (1 : ℝ) / ((k : ℝ) * Real.log (k : ℝ))
  have hg_eq : ∑ p ∈ (Ioc 3 H).filter Nat.Prime, (1 : ℝ) / p =
      ∑ p ∈ (Ioc 3 H).filter Nat.Prime, Real.log p * g p := by
    refine sum_congr rfl fun p hp => ?_
    have hpp := (mem_filter.mp hp).2
    have hlp : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hpp.one_lt)).ne'
    dsimp [g]; field_simp [hlp]
  have hg_anti : ∀ k, 4 ≤ k → k < H → g (k + 1) ≤ g k := by
    intro k hk _
    have hkp : (0 : ℝ) < k := by positivity
    have hlk : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    dsimp [g]
    refine one_div_le_one_div_of_le (mul_pos hkp hlk) ?_
    push_cast
    exact mul_le_mul (by linarith) (Real.log_le_log hkp (by linarith)) hlk.le (by positivity)
  have habel_g := discrete_abel_theta g (a := 3) (b := H) (by omega) hg_anti
    (by dsimp [g]; positivity) (by dsimp [g]; positivity)
  have hg4 : ((4 : ℕ) : ℝ) * g 4 = 1 / Real.log 4 := by
    dsimp [g]; field_simp
  have hsum_g := sum_inv_mul_log_le (a := 4) (b := H) (by omega) (by omega)
  have hlog4_eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  have hlog4_gt1 : 1 < Real.log 4 := by linarith [Real.log_two_gt_d9]
  have hlog_log4_pos : 0 < Real.log (Real.log 4) := Real.log_pos hlog4_gt1
  have hlogH_le_logn : Real.log (H : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hH_pos (by exact_mod_cast Nat.sqrt_le_self n)
  have hlogH_pos : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hll_le : Real.log (Real.log (H : ℝ)) ≤ Real.log (Real.log (n : ℝ)) :=
    Real.log_le_log hlogH_pos hlogH_le_logn
  have hlog4_pos : 0 < Real.log 4 := by linarith
  have hprime_tail : ∑ p ∈ (Ioc 3 H).filter Nat.Prime, (1 : ℝ) / p ≤
      1 + Real.log 4 * Real.log (Real.log (n : ℝ)) := by
    rw [hg_eq]
    calc ∑ p ∈ (Ioc 3 H).filter Nat.Prime, Real.log p * g p
        ≤ Real.log 4 * (1 / Real.log 4 + (Real.log (Real.log (H : ℝ)) - Real.log (Real.log 4))) := by
          rw [← hg4]; exact habel_g.trans (mul_le_mul_of_nonneg_left (by linarith) hlog4_pos.le)
      _ = 1 + Real.log 4 * (Real.log (Real.log (H : ℝ)) - Real.log (Real.log 4)) := by
          rw [mul_add, mul_one_div_cancel hlog4_pos.ne']
      _ ≤ 1 + Real.log 4 * Real.log (Real.log (n : ℝ)) := by
          have : Real.log (Real.log (H : ℝ)) - Real.log (Real.log 4) ≤ Real.log (Real.log (n : ℝ)) := by
            linarith
          nlinarith
  linarith

theorem eventually_smooth_mass_dominates :
    let smoothDivs := fun n h : ℕ => (Icc 1 n).filter (· ∣ Nat.lcmUpto h)
    let smoothCap := fun n h : ℕ =>
      (∑ d ∈ smoothDivs n h, (1 : ℚ) / d) - ∑ k ∈ (Icc 2 h).filter IsPrimePow, (1 : ℚ) / k
    ∀ᶠ n : ℕ in atTop,
      1 + ∑ d ∈ (Icc 1 n).filter (fun d => ¬ d ∣ Nat.lcmUpto n.sqrt), (1 : ℚ) / d ≤
        smoothCap n n.sqrt := by
  intro smoothDivs smoothCap
  have hlog2_lt : Real.log 2 < 7 / 10 := by linarith [Real.log_two_lt_d9]
  have hlog4_eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  have h_ll : ∀ᶠ n : ℕ in atTop, Real.log (Real.log (n : ℝ)) ≤ (1 / 100) * Real.log (n : ℝ) := by
    have hlo := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)
    have hbound := hlo.bound (show (0 : ℝ) < 1 / 100 by norm_num)
    have hcomp := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hbound
    filter_upwards [hcomp, eventually_ge_atTop 100] with n hn h100
    dsimp only [Function.comp_apply] at hn
    have hlog_ge1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by
      have : Real.exp 1 ≤ (n : ℝ) := by
        have := Real.exp_one_lt_d9
        have : (100 : ℝ) ≤ n := by exact_mod_cast h100
        linarith
      exact (Real.le_log_iff_exp_le (by positivity)).mpr this
    have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
    have hll_nn : 0 ≤ Real.log (Real.log (n : ℝ)) := Real.log_nonneg hlog_ge1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg hll_nn, abs_of_pos hlog_pos] at hn
    exact hn
  have h_log_large : ∀ᶠ n : ℕ in atTop, (1000 : ℝ) ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1000)
  have h_sqrt_large : ∀ᶠ n : ℕ in atTop, (1000 : ℝ) ≤ Real.sqrt (n.sqrt : ℝ) := by
    filter_upwards [eventually_ge_atTop (1000 ^ 4)] with n hn
    have h1 : 1000 ^ 2 ≤ n.sqrt := Nat.le_sqrt.mpr (by
      calc (1000 ^ 2) * (1000 ^ 2) = 1000 ^ 4 := by ring
        _ ≤ n := hn)
    have h2 : (1000 : ℝ) ^ 2 ≤ (n.sqrt : ℝ) := by exact_mod_cast h1
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr h2
  filter_upwards [eventually_ge_atTop 10000, h_ll, h_log_large, h_sqrt_large] with n hn hll hlog1000 hsq1000
  suffices hR : (1 : ℝ) +
      2 * ∑ d ∈ (Icc 1 n).filter (fun d => ¬ d ∣ Nat.lcmUpto n.sqrt), (1 : ℝ) / d +
      ∑ h ∈ (Icc 2 n.sqrt).filter IsPrimePow, (1 : ℝ) / h ≤
      ∑ d ∈ Icc 1 n, (1 : ℝ) / d by
    have hsplit : ∑ d ∈ Icc 1 n, (1 : ℝ) / d =
        (∑ d ∈ smoothDivs n n.sqrt, (1 : ℝ) / d) +
        ∑ d ∈ (Icc 1 n).filter (fun d => ¬ d ∣ Nat.lcmUpto n.sqrt), (1 : ℝ) / d := by
      dsimp only [smoothDivs]
      rw [sum_filter_add_sum_filter_not]
    have hR' : (1 : ℝ) +
        ∑ d ∈ (Icc 1 n).filter (fun d => ¬ d ∣ Nat.lcmUpto n.sqrt), (1 : ℝ) / d ≤
        (∑ d ∈ smoothDivs n n.sqrt, (1 : ℝ) / d) -
        ∑ h ∈ (Icc 2 n.sqrt).filter IsPrimePow, (1 : ℝ) / h := by linarith
    suffices hQ : ((1 + ∑ d ∈ (Icc 1 n).filter (fun d => ¬ d ∣ Nat.lcmUpto n.sqrt), (1 : ℚ) / d : ℚ) : ℝ) ≤
        (smoothCap n n.sqrt : ℝ) by exact_mod_cast hQ
    simp only [smoothCap, Rat.cast_add, Rat.cast_sub, Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    exact hR'
  have hn_pos : (0 : ℝ) < n := by positivity
  have hLHS : Real.log (n : ℝ) ≤ ∑ d ∈ Icc 1 n, (1 : ℝ) / d :=
    (Real.log_le_log hn_pos (by linarith)).trans (log_add_one_le_harmonic n)
  have hsplit := rough_harmonic_split (by omega : 100 ≤ n)
  have hT1 := rough_type1_bound hn hlog1000
  have hT2 := rough_type2_bound hn hlog1000 hsq1000
  have hpp := primePow_recip_bound hn
  have hlog4_lt : Real.log 4 < 14 / 10 := by linarith
  have hlog4_pos : 0 < Real.log 4 := by linarith [Real.log_two_gt_d9]
  have hcoef : 2 * Real.log 4 * (Real.log 2 - 1 / 2) ≤ 56 / 100 := by
    have h1 : Real.log 2 - 1 / 2 < 2 / 10 := by linarith
    have h2 : 0 < Real.log 2 - 1 / 2 := by linarith [Real.log_two_gt_d9]
    nlinarith
  have hconst : 1 + 2 * (Real.log 4 * (3 + Real.log 2)) + 5 ≤ 20 := by nlinarith
  have hll_term : Real.log 4 * Real.log (Real.log (n : ℝ)) ≤ (2 / 100) * Real.log (n : ℝ) := by
    nlinarith
  nlinarith
/-- **Corollary 2a (Eventually Full Smooth Grid Filling, matching PR #4040's H2 radius).** -/
theorem eventually_smooth_grid_full :
    ∀ᶠ n : ℕ in atTop,
      let B := Nat.lcmUpto n.sqrt
      ∀ z : ℤ, |(z : ℚ) / B| ≤ 1 + ∑ i : Fin n with ¬ (i.val + 1) ∣ B, (1 : ℚ) / (i.val + 1) →
        ∃ d : Fin n → ℤ,
          (∀ i, d i = -1 ∨ d i = 0 ∨ d i = 1) ∧
          (∀ i, ¬ (i.val + 1) ∣ B → d i = 0) ∧
          ∑ i : Fin n, (d i : ℚ) / (i.val + 1) = (z : ℚ) / B := by
  filter_upwards [eventually_ge_atTop 1, eventually_smooth_mass_dominates] with n hn hdom
  dsimp only
  intro z hz
  have hsum_eq : ∑ i : Fin n with ¬ (i.val + 1) ∣ Nat.lcmUpto n.sqrt, (1 : ℚ) / (i.val + 1) =
      ∑ d ∈ (Icc 1 n).filter (fun d => ¬ d ∣ Nat.lcmUpto n.sqrt), (1 : ℚ) / d := by
    refine Finset.sum_bij (fun i _ => i.val + 1) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, mem_univ, true_and] at hi
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hi⟩
    · intro i _ j _ h; exact Fin.ext (by omega)
    · intro d hd
      obtain ⟨hdIcc, hnd⟩ := mem_filter.mp hd
      obtain ⟨hd1, hdn⟩ := mem_Icc.mp hdIcc
      exact ⟨⟨d - 1, by omega⟩, by simp [show d - 1 + 1 = d by omega, hnd], by simp; omega⟩
    · intro i _; push_cast; rfl
  rw [hsum_eq] at hz
  exact smooth_grid_descent hn z (hz.trans hdom)

lemma dvd_of_primary {P : ℕ} (hP : P ≠ 0) {x : ℤ}
    (h : ∀ q ∈ P.primeFactors, ((q ^ P.factorization q : ℕ) : ℤ) ∣ x) :
    (P : ℤ) ∣ x := by
  apply Int.natCast_dvd.mpr
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p j hp hj
  by_cases hmem : p ∈ P.primeFactors
  · exact (Nat.pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization hP).mp hj)).trans
      (Int.natCast_dvd.mp (h p hmem))
  · have hj0 : j = 0 := by
      by_contra hj0
      have hpdiv := (dvd_pow_self p hj0).trans hj
      exact hmem (Nat.mem_primeFactors.mpr ⟨hp, hpdiv, hP⟩)
    simp [hj0]

/-- Single-prime lifting from `q ^ 1` up to `q ^ (a - b)` using disjoint valuation layers
`d = i * q ^ (a - s)` (`1 ≤ i < q`, `1 ≤ s < a - b`), all inside `H_q = {d ≤ n : q ^ (b + 1) ∣ d}`. -/
lemma single_prime_lift {n q : ℕ} (hq : q ∈ Nat.primesLE n) (t : ℤ)
    (h0 : ∃ δ : Fin n → ℤ,
      (∀ i, δ i = -1 ∨ δ i = 0 ∨ δ i = 1) ∧
      (∀ i, ¬ (q ^ (Nat.log q n) ∣ i.val + 1) → δ i = 0) ∧
      (q : ℤ) ∣ t - ∑ i : Fin n, δ i * ((Nat.lcmUpto n / (i.val + 1) : ℕ) : ℤ)) :
    let a := Nat.log q n
    let b := Nat.log q n.sqrt
    ∃ δ : Fin n → ℤ,
      (∀ i, δ i = -1 ∨ δ i = 0 ∨ δ i = 1) ∧
      (∀ i, ¬ (q ^ (b + 1) ∣ i.val + 1) → δ i = 0) ∧
      ((q ^ (a - b) : ℕ) : ℤ) ∣ t - ∑ i : Fin n, δ i * ((Nat.lcmUpto n / (i.val + 1) : ℕ) : ℤ) := by
  have hqp : q.Prime := Nat.prime_of_mem_primesLE hq
  have hqn : q ≤ n := (Nat.mem_primesLE.mp hq).1
  have hn_pos : 0 < n := lt_of_lt_of_le hqp.pos hqn
  have hsq_pos : 0 < n.sqrt := Nat.sqrt_pos.mpr hn_pos
  set a := Nat.log q n
  set b := Nat.log q n.sqrt
  have ha1 : 1 ≤ a := Nat.le_log_of_pow_le hqp.one_lt (by simpa using hqn)
  have hba : b < a := by
    have hpow : q ^ (b + 1) ≤ n := by
      by_cases hb0 : b = 0
      · simpa [hb0] using hqn
      · have hqb : q ^ b ≤ n.sqrt := Nat.pow_log_le_self q hsq_pos.ne'
        have hqb1 : q ≤ q ^ b := by
          calc q = q ^ 1 := (pow_one q).symm
            _ ≤ q ^ b := Nat.pow_le_pow_right hqp.pos (Nat.pos_of_ne_zero hb0)
        calc q ^ (b + 1) = q ^ b * q := pow_succ q b
          _ ≤ q ^ b * q ^ b := Nat.mul_le_mul_left _ hqb1
          _ ≤ n.sqrt * n.sqrt := Nat.mul_le_mul hqb hqb
          _ ≤ n := Nat.sqrt_le n
    exact Nat.lt_of_succ_le (Nat.le_log_of_pow_le hqp.one_lt hpow)
  have hind : ∀ s : ℕ, 1 ≤ s → s ≤ a - b →
      ∃ δ : Fin n → ℤ,
        (∀ i, δ i = -1 ∨ δ i = 0 ∨ δ i = 1) ∧
        (∀ i, ¬ (q ^ (a + 1 - s) ∣ i.val + 1) → δ i = 0) ∧
        ((q ^ s : ℕ) : ℤ) ∣ t - ∑ i : Fin n, δ i * ((Nat.lcmUpto n / (i.val + 1) : ℕ) : ℤ) := by
    intro s hs1 hsab
    induction s, hs1 using Nat.le_induction with
    | base =>
      simpa using h0
    | succ s hs1 ih =>
      obtain ⟨δ, hδt, hδs, hδd⟩ := ih (by omega)
      obtain ⟨c, hc⟩ := hδd
      by_cases hqc : (q : ℤ) ∣ c
      · obtain ⟨c', hc'⟩ := hqc
        refine ⟨δ, hδt, ?_, ?_⟩
        · intro i hnd
          apply hδs i
          intro hdvd
          exact hnd ((Nat.pow_dvd_pow q (by omega : a + 1 - (s + 1) ≤ a + 1 - s)).trans hdvd)
        · refine ⟨c', ?_⟩
          rw [hc, hc', pow_succ]
          push_cast; ring
      · let L := Nat.lcmUpto n
        have hqa_dvd_L : q ^ a ∣ L := dvd_lcmUpto (pow_pos hqp.pos _) (Nat.pow_log_le_self q hn_pos.ne')
        let M := L / q ^ a
        have hqM : ¬ q ∣ M := not_dvd_lcmUpto_div_pow (n := n) hqp
        have hm_dvd_M : ∀ m, 1 ≤ m → m < q → m ∣ M := by
          intro m hm1 hmq
          have hmL : m ∣ L := dvd_lcmUpto hm1 (by omega)
          have hcop : Nat.Coprime m (q ^ a) :=
            (hqp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm1 hmq)).symm.pow_right a
          rw [← Nat.mul_div_cancel' hqa_dvd_L] at hmL
          exact hcop.dvd_of_dvd_mul_left hmL
        obtain ⟨m, hm1, hmq, hhit⟩ := mod_q_residue_hit hqp hqM hm_dvd_M c hqc
        let dStar := m * q ^ (a - s)
        have hdStar_le : dStar ≤ n := by
          have h1 : m * q ^ (a - s) < q * q ^ (a - s) := Nat.mul_lt_mul_of_pos_right hmq (pow_pos hqp.pos _)
          have h2 : q * q ^ (a - s) = q ^ (a - s + 1) := by rw [pow_succ, mul_comm]
          have h3 : q ^ (a - s + 1) ≤ q ^ a := Nat.pow_le_pow_right hqp.pos (by omega)
          have h4 : q ^ a ≤ n := Nat.pow_log_le_self q hn_pos.ne'
          omega
        have hdStar_pos : 1 ≤ dStar := Nat.mul_pos hm1 (pow_pos hqp.pos _)
        let idx : Fin n := ⟨dStar - 1, by omega⟩
        have hidx_val : idx.val + 1 = dStar := by dsimp [idx]; omega
        have hidx_not_old : ¬ q ^ (a + 1 - s) ∣ idx.val + 1 := by
          rw [hidx_val]
          intro hdvd
          have hpow_eq : q ^ (a + 1 - s) = q * q ^ (a - s) := by
            have : a + 1 - s = (a - s) + 1 := by omega
            rw [this, pow_succ, mul_comm]
          rw [hpow_eq] at hdvd
          have hqm : q ∣ m := (Nat.mul_dvd_mul_iff_right (pow_pos hqp.pos (a - s))).mp hdvd
          exact Nat.not_dvd_of_pos_of_lt hm1 hmq hqm
        have hδ_idx0 : δ idx = 0 := hδs idx hidx_not_old
        have hweight : L / dStar = q ^ s * (M / m) := by
          have h1 : q ^ a = q ^ s * q ^ (a - s) := by
            rw [← pow_add, Nat.add_sub_cancel' (by omega : s ≤ a)]
          have hmM : m ∣ M := hm_dvd_M m hm1 hmq
          have hmul : (q ^ s * (M / m)) * dStar = L := by
            calc (q ^ s * (M / m)) * dStar
                = (q ^ s * q ^ (a - s)) * (m * (M / m)) := by dsimp [dStar]; ring
              _ = q ^ a * M := by rw [← h1, Nat.mul_div_cancel' hmM]
              _ = L := Nat.mul_div_cancel' hqa_dvd_L
          exact Nat.div_eq_of_eq_mul_left (by omega : 0 < dStar) hmul.symm
        let δ' : Fin n → ℤ := fun i => if i = idx then 1 else δ i
        refine ⟨δ', ?_, ?_, ?_⟩
        · intro i; by_cases hi : i = idx <;> simp [δ', hi, hδt i]
        · intro i hnd
          by_cases hi : i = idx
          · exfalso; apply hnd
            rw [hi, hidx_val]
            have : a + 1 - (s + 1) = a - s := by omega
            rw [this]; exact dvd_mul_left _ m
          · simp only [δ', if_neg hi]
            apply hδs i
            intro hdvd
            exact hnd ((Nat.pow_dvd_pow q (by omega : a + 1 - (s + 1) ≤ a + 1 - s)).trans hdvd)
        · have hsum_diff : ∑ i : Fin n, δ' i * ((L / (i.val + 1) : ℕ) : ℤ) =
              (∑ i : Fin n, δ i * ((L / (i.val + 1) : ℕ) : ℤ)) + ((L / dStar : ℕ) : ℤ) := by
            rw [← add_sum_erase univ _ (mem_univ idx),
              ← add_sum_erase univ (fun i : Fin n => δ i * ((L / (i.val + 1) : ℕ) : ℤ)) (mem_univ idx)]
            have hrest : ∑ i ∈ univ.erase idx, δ' i * ((L / (i.val + 1) : ℕ) : ℤ) =
                ∑ i ∈ univ.erase idx, δ i * ((L / (i.val + 1) : ℕ) : ℤ) :=
              sum_congr rfl fun i hi => by simp [δ', (mem_erase.mp hi).1]
            rw [hrest]
            simp [δ', hδ_idx0, hidx_val]
            ring
          obtain ⟨u, hu⟩ := hhit
          refine ⟨u, ?_⟩
          rw [hsum_diff, hweight]
          have hsub : t - ((∑ i : Fin n, δ i * ((L / (i.val + 1) : ℕ) : ℤ)) +
              ((q ^ s * (M / m) : ℕ) : ℤ)) =
              ((q ^ s : ℕ) : ℤ) * (c - ((M / m : ℕ) : ℤ)) := by
            have : t - ∑ i : Fin n, δ i * ((L / (i.val + 1) : ℕ) : ℤ) = ((q ^ s : ℕ) : ℤ) * c := hc
            push_cast at this ⊢; linarith
          rw [hsub, hu, pow_succ]
          push_cast; ring
  obtain ⟨δ, hδt, hδs, hδd⟩ := hind (a - b) (by omega) le_rfl
  refine ⟨δ, hδt, ?_, hδd⟩
  intro i hnd
  apply hδs i
  have : a + 1 - (a - b) = b + 1 := by omega
  rwa [this]

/-- **Theorem 3 (Simultaneous Prime-Power Lift, ∀ n ≥ 1, ∀ t : ℤ).**
Local mod-`q` admissibility for all primes `q ≤ n` is equivalent to solvability of
`Z(δ) ≡ t (mod L_n / L_{⌊√n⌋})` supported strictly outside the smooth divisors `d ∣ L_{⌊√n⌋}`. -/
theorem simultaneous_prime_power_lift {n : ℕ} (hn : 1 ≤ n) (t : ℤ) :
    let LocalAdmissible := fun (n : ℕ) (t : ℤ) =>
      ∀ q ∈ Nat.primesLE n,
        ∃ δ : Fin n → ℤ,
          (∀ i, δ i = -1 ∨ δ i = 0 ∨ δ i = 1) ∧
          (∀ i, ¬ (q ^ (Nat.log q n) ∣ i.val + 1) → δ i = 0) ∧
          (q : ℤ) ∣ t - ∑ i : Fin n, δ i * ((Nat.lcmUpto n / (i.val + 1) : ℕ) : ℤ)
    LocalAdmissible n t ↔
      ∃ δ : Fin n → ℤ,
        (∀ i, δ i = -1 ∨ δ i = 0 ∨ δ i = 1) ∧
        (∀ i, (i.val + 1) ∣ Nat.lcmUpto n.sqrt → δ i = 0) ∧
        (((Nat.lcmUpto n / Nat.lcmUpto n.sqrt : ℕ) : ℤ)) ∣
          t - ∑ i : Fin n, δ i * ((Nat.lcmUpto n / (i.val + 1) : ℕ) : ℤ) := by
  intro LocalAdmissible
  let L := Nat.lcmUpto n
  let B := Nat.lcmUpto n.sqrt
  let D := L / B
  have hsq_pos : 0 < n.sqrt := Nat.sqrt_pos.mpr (by omega)
  have hBL : B ∣ L := lcmUpto_dvd_lcmUpto (Nat.sqrt_le_self n)
  have hDpos : 0 < D := Nat.div_pos (Nat.le_of_dvd (Nat.lcmUpto_pos n) hBL) (Nat.lcmUpto_pos _)
  have hDne : D ≠ 0 := hDpos.ne'
  have hfacD : ∀ q : ℕ, q.Prime → D.factorization q = Nat.log q n - Nat.log q n.sqrt := by
    intro q hq
    rw [Nat.factorization_div hBL, Finsupp.tsub_apply,
      Nat.factorization_lcmUpto n hq, Nat.factorization_lcmUpto n.sqrt hq]
  have hpfD : D.primeFactors = Nat.primesLE n := by
    ext q
    rw [Nat.mem_primeFactors, Nat.mem_primesLE]
    constructor
    · rintro ⟨hq, hqD, _⟩
      have hqL : q ∣ L := hqD.trans (Nat.div_dvd_of_dvd hBL)
      have hmem := Nat.mem_primeFactors.mpr ⟨hq, hqL, Nat.lcmUpto_ne_zero n⟩
      rw [Nat.primeFactors_lcmUpto] at hmem
      exact Nat.mem_primesLE.mp hmem
    · rintro ⟨hqn, hq⟩
      refine ⟨hq, ?_, hDne⟩
      have hpos : 0 < D.factorization q := by
        rw [hfacD q hq]
        have ha1 : 1 ≤ Nat.log q n := Nat.le_log_of_pow_le hq.one_lt (by simpa using hqn)
        have hba : Nat.log q n.sqrt < Nat.log q n := by
          set b := Nat.log q n.sqrt
          by_cases hb0 : b = 0
          · omega
          · have hqb : q ^ b ≤ n.sqrt := Nat.pow_log_le_self q hsq_pos.ne'
            have hqb1 : q ≤ q ^ b := by
              calc q = q ^ 1 := (pow_one q).symm
                _ ≤ q ^ b := Nat.pow_le_pow_right hq.pos (Nat.pos_of_ne_zero hb0)
            have hpow : q ^ (b + 1) ≤ n := by
              calc q ^ (b + 1) = q ^ b * q := pow_succ q b
                _ ≤ q ^ b * q ^ b := Nat.mul_le_mul_left _ hqb1
                _ ≤ n.sqrt * n.sqrt := Nat.mul_le_mul hqb hqb
                _ ≤ n := Nat.sqrt_le n
            exact Nat.lt_of_succ_le (Nat.le_log_of_pow_le hq.one_lt hpow)
        omega
      exact hq.dvd_iff_one_le_factorization hDne |>.mpr hpos
  constructor
  · intro hadm
    classical
    let J := ↥(Nat.primesLE n)
    have hlift : ∀ q : J, ∃ f : Fin n → ℤ,
        (∀ i, f i = -1 ∨ f i = 0 ∨ f i = 1) ∧
        (∀ i, ¬ ((q : ℕ) ^ (Nat.log q n.sqrt + 1) ∣ i.val + 1) → f i = 0) ∧
        (((q : ℕ) ^ (Nat.log q n - Nat.log q n.sqrt) : ℕ) : ℤ) ∣
          t - ∑ i : Fin n, f i * ((L / (i.val + 1) : ℕ) : ℤ) :=
      fun q => single_prime_lift q.property t (hadm q q.property)
    choose f hf_t hf_s hf_d using hlift
    have hdisj : ∀ (p q : J), p ≠ q → ∀ i : Fin n, f p i ≠ 0 → f q i = 0 := by
      intro p q hpq i hpi
      by_contra hqi
      have hpd : (p : ℕ) ^ (Nat.log p n.sqrt + 1) ∣ i.val + 1 := by
        by_contra hnd; exact hpi (hf_s p i hnd)
      have hqd : (q : ℕ) ^ (Nat.log q n.sqrt + 1) ∣ i.val + 1 := by
        by_contra hnd; exact hqi (hf_s q i hnd)
      have hpp := Nat.prime_of_mem_primesLE p.property
      have hqp := Nat.prime_of_mem_primesLE q.property
      have hpne : (p : ℕ) ≠ (q : ℕ) := fun h => hpq (Subtype.ext h)
      have hcop : Nat.Coprime ((p : ℕ) ^ (Nat.log p n.sqrt + 1)) ((q : ℕ) ^ (Nat.log q n.sqrt + 1)) :=
        ((hpp.coprime_iff_not_dvd.mpr fun hd =>
          hpne ((hqp.eq_one_or_self_of_dvd p hd).resolve_left hpp.ne_one)).pow_left _).pow_right _
      have hmuld : (p : ℕ) ^ (Nat.log p n.sqrt + 1) * (q : ℕ) ^ (Nat.log q n.sqrt + 1) ∣ i.val + 1 :=
        hcop.mul_dvd_of_dvd_of_dvd hpd hqd
      have hgt1 : n.sqrt + 1 ≤ (p : ℕ) ^ (Nat.log p n.sqrt + 1) := Nat.lt_pow_succ_log_self hpp.one_lt n.sqrt
      have hgt2 : n.sqrt + 1 ≤ (q : ℕ) ^ (Nat.log q n.sqrt + 1) := Nat.lt_pow_succ_log_self hqp.one_lt n.sqrt
      have hsq : n < (n.sqrt + 1) * (n.sqrt + 1) := Nat.lt_succ_sqrt n
      have hprod_le : (n.sqrt + 1) * (n.sqrt + 1) ≤
          (p : ℕ) ^ (Nat.log p n.sqrt + 1) * (q : ℕ) ^ (Nat.log q n.sqrt + 1) :=
        Nat.mul_le_mul hgt1 hgt2
      have hle_d := Nat.le_of_dvd (by omega : 0 < i.val + 1) hmuld
      omega
    let δ : Fin n → ℤ := fun i => ∑ q : J, f q i
    refine ⟨δ, ?_, ?_, ?_⟩
    · intro i
      by_cases hex : ∃ q : J, f q i ≠ 0
      · obtain ⟨q, hqi⟩ := hex
        have hδeq : δ i = f q i := by
          dsimp [δ]
          rw [Finset.sum_eq_single q]
          · intro p _ hpq; exact hdisj q p hpq.symm i hqi
          · intro h; exact absurd (mem_univ q) h
        rw [hδeq]; exact hf_t q i
      · push Not at hex
        right; left; exact sum_eq_zero fun q _ => hex q
    · intro i hiB
      refine sum_eq_zero fun q _ => ?_
      apply hf_s q i
      intro hqd
      have hqp := Nat.prime_of_mem_primesLE q.property
      have hqB : (q : ℕ) ^ (Nat.log q n.sqrt + 1) ∣ B := hqd.trans hiB
      have hle := (hqp.pow_dvd_iff_le_factorization (Nat.lcmUpto_ne_zero _)).mp hqB
      rw [Nat.factorization_lcmUpto _ hqp] at hle
      omega
    · apply dvd_of_primary hDne
      intro p hpD
      have hpp := Nat.prime_of_mem_primeFactors hpD
      have hp_mem : p ∈ Nat.primesLE n := hpfD ▸ hpD
      let u : J := ⟨p, hp_mem⟩
      rw [hfacD p hpp]
      have hsum_comm : ∑ i : Fin n, δ i * ((L / (i.val + 1) : ℕ) : ℤ) =
          ∑ q : J, ∑ i : Fin n, f q i * ((L / (i.val + 1) : ℕ) : ℤ) := by
        simp only [δ, sum_mul]; exact sum_comm
      rw [hsum_comm, ← add_sum_erase univ _ (mem_univ u)]
      have hsplit : t - ((∑ i : Fin n, f u i * ((L / (i.val + 1) : ℕ) : ℤ)) +
          ∑ v ∈ univ.erase u, ∑ i : Fin n, f v i * ((L / (i.val + 1) : ℕ) : ℤ)) =
          (t - ∑ i : Fin n, f u i * ((L / (i.val + 1) : ℕ) : ℤ)) -
          ∑ v ∈ univ.erase u, ∑ i : Fin n, f v i * ((L / (i.val + 1) : ℕ) : ℤ) := by ring
      rw [hsplit]
      apply dvd_sub (hf_d u)
      apply dvd_sum
      intro v hv
      apply dvd_sum
      intro i _
      by_cases hfv : f v i = 0
      · simp [hfv]
      · have hvu : v ≠ u := (mem_erase.mp hv).1
        have hp_not_dvd : ¬ p ^ (Nat.log p n.sqrt + 1) ∣ i.val + 1 := by
          intro hpd
          have hvd : (v : ℕ) ^ (Nat.log v n.sqrt + 1) ∣ i.val + 1 := by
            by_contra hnd; exact hfv (hf_s v i hnd)
          have hvp := Nat.prime_of_mem_primesLE v.property
          have hvne : (v : ℕ) ≠ p := fun h => hvu (Subtype.ext h)
          have hcop : Nat.Coprime ((v : ℕ) ^ (Nat.log v n.sqrt + 1)) (p ^ (Nat.log p n.sqrt + 1)) :=
            ((hvp.coprime_iff_not_dvd.mpr fun hd =>
              hvne ((hpp.eq_one_or_self_of_dvd v hd).resolve_left hvp.ne_one)).pow_left _).pow_right _
          have hmuld := hcop.mul_dvd_of_dvd_of_dvd hvd hpd
          have hgt1 : n.sqrt + 1 ≤ (v : ℕ) ^ (Nat.log v n.sqrt + 1) := Nat.lt_pow_succ_log_self hvp.one_lt n.sqrt
          have hgt2 : n.sqrt + 1 ≤ p ^ (Nat.log p n.sqrt + 1) := Nat.lt_pow_succ_log_self hpp.one_lt n.sqrt
          have hsq : n < (n.sqrt + 1) * (n.sqrt + 1) := Nat.lt_succ_sqrt n
          have hprod_le : (n.sqrt + 1) * (n.sqrt + 1) ≤
              (v : ℕ) ^ (Nat.log v n.sqrt + 1) * p ^ (Nat.log p n.sqrt + 1) :=
            Nat.mul_le_mul hgt1 hgt2
          have hle := Nat.le_of_dvd (by omega : 0 < i.val + 1) hmuld
          omega
        have hfac_i : (i.val + 1).factorization p ≤ Nat.log p n.sqrt := by
          by_contra! hgt
          exact hp_not_dvd ((hpp.pow_dvd_iff_le_factorization (by omega)).mpr hgt)
        have hiL : i.val + 1 ∣ L := dvd_lcmUpto (by omega) (by omega)
        have hpow_dvd : p ^ (Nat.log p n - Nat.log p n.sqrt) ∣ L / (i.val + 1) := by
          rw [hpp.pow_dvd_iff_le_factorization (Nat.div_pos (Nat.le_of_dvd (Nat.lcmUpto_pos n) hiL) (by omega)).ne',
            Nat.factorization_div hiL, Finsupp.tsub_apply, Nat.factorization_lcmUpto n hpp]
          omega
        exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hpow_dvd) _
  · rintro ⟨δ, hδt, _, hDdiv⟩ q hq
    have hqp := Nat.prime_of_mem_primesLE hq
    have hqD : q ∣ D := Nat.dvd_of_mem_primeFactors (hpfD.symm ▸ hq)
    have hqdiv : (q : ℤ) ∣ t - ∑ i : Fin n, δ i * ((L / (i.val + 1) : ℕ) : ℤ) :=
      (Int.natCast_dvd_natCast.mpr hqD).trans hDdiv
    classical
    let δq : Fin n → ℤ := fun i => if q ^ (Nat.log q n) ∣ i.val + 1 then δ i else 0
    refine ⟨δq, fun i => by by_cases h : q ^ (Nat.log q n) ∣ i.val + 1 <;> simp [δq, h, hδt i],
      fun i h => by simp [δq, h], ?_⟩
    have hdiff : (t - ∑ i : Fin n, δq i * ((L / (i.val + 1) : ℕ) : ℤ)) =
        (t - ∑ i : Fin n, δ i * ((L / (i.val + 1) : ℕ) : ℤ)) +
        ∑ i : Fin n, (δ i - δq i) * ((L / (i.val + 1) : ℕ) : ℤ) := by
      simp only [sub_mul, sum_sub_distrib]; ring
    rw [hdiff]
    refine dvd_add hqdiv (dvd_sum fun i _ => ?_)
    by_cases hi : q ^ (Nat.log q n) ∣ i.val + 1
    · simp [δq, hi]
    · have hiL : i.val + 1 ∣ L := dvd_lcmUpto (by omega) (by omega)
      have hfac_lt : (i.val + 1).factorization q < Nat.log q n := by
        by_contra! hge
        exact hi ((hqp.pow_dvd_iff_le_factorization (by omega)).mpr hge)
      have hq_w : q ∣ L / (i.val + 1) := by
        rw [hqp.dvd_iff_one_le_factorization (Nat.div_pos (Nat.le_of_dvd (Nat.lcmUpto_pos n) hiL) (by omega)).ne',
          Nat.factorization_div hiL, Finsupp.tsub_apply, Nat.factorization_lcmUpto n hqp]
        omega
      exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hq_w) _
theorem eventually_local_global_equiv :
    let LocalAdmissible := fun (n : ℕ) (t : ℤ) =>
      ∀ q ∈ Nat.primesLE n,
        ∃ δ : Fin n → ℤ,
          (∀ i, δ i = -1 ∨ δ i = 0 ∨ δ i = 1) ∧
          (∀ i, ¬ (q ^ (Nat.log q n) ∣ i.val + 1) → δ i = 0) ∧
          (q : ℤ) ∣ t - ∑ i : Fin n, δ i * ((Nat.lcmUpto n / (i.val + 1) : ℕ) : ℤ)
    ∀ᶠ n : ℕ in atTop, ∀ t : ℤ, |t| ≤ Nat.lcmUpto n →
      ((∃ δ : Fin n → ℚ, δ '' Set.univ ⊆ {-1, 0, 1} ∧
        ∑ k : Fin n, δ k / (k.val + 1) = (t : ℚ) / Nat.lcmUpto n) ↔
      LocalAdmissible n t) := by
  intro LocalAdmissible
  filter_upwards [eventually_ge_atTop 1, eventually_smooth_grid_full] with n hn hgrid
  intro t ht
  let L := Nat.lcmUpto n
  let B := Nat.lcmUpto n.sqrt
  let D := L / B
  have hBL : B ∣ L := lcmUpto_dvd_lcmUpto (Nat.sqrt_le_self n)
  have hDB : D * B = L := Nat.div_mul_cancel hBL
  have hLpos : (0 : ℚ) < L := by exact_mod_cast Nat.lcmUpto_pos n
  have hBpos : (0 : ℚ) < B := by exact_mod_cast Nat.lcmUpto_pos n.sqrt
  constructor
  · rintro ⟨δ, hδ, hsum⟩
    have hs : ∀ k : Fin n, ∃ s : ℤ, (s = -1 ∨ s = 0 ∨ s = 1) ∧ (s : ℚ) = δ k := by
      intro k
      rcases hδ ⟨k, trivial, rfl⟩ with h | h | h
      · exact ⟨-1, Or.inl rfl, by simp [h]⟩
      · exact ⟨0, Or.inr (Or.inl rfl), by simp [h]⟩
      · exact ⟨1, Or.inr (Or.inr rfl), by simpa using (Set.mem_singleton_iff.mp h).symm⟩
    choose s hs_t hs_c using hs
    have hZ : ∑ k : Fin n, s k * ((L / (k.val + 1) : ℕ) : ℤ) = t := by
      have hscaled : ((∑ k : Fin n, s k * ((L / (k.val + 1) : ℕ) : ℤ) : ℤ) : ℚ) =
          (L : ℚ) * ∑ k : Fin n, δ k / (k.val + 1) := by
        rw [Int.cast_sum, mul_sum]
        refine sum_congr rfl fun k _ => ?_
        have hd : k.val + 1 ∣ L := dvd_lcmUpto (by omega) (by omega)
        rw [cast_mul_div_weight (s k) hd (by omega), hs_c k]
        push_cast; rfl
      rw [hsum, mul_div_cancel₀ _ hLpos.ne'] at hscaled
      exact_mod_cast hscaled
    intro q hq
    have hqp := Nat.prime_of_mem_primesLE hq
    classical
    let sq : Fin n → ℤ := fun k => if q ^ (Nat.log q n) ∣ k.val + 1 then s k else 0
    refine ⟨sq, fun k => by by_cases h : q ^ (Nat.log q n) ∣ k.val + 1 <;> simp [sq, h, hs_t k],
      fun k h => by simp [sq, h], ?_⟩
    have hdiff : t - ∑ k : Fin n, sq k * ((L / (k.val + 1) : ℕ) : ℤ) =
        ∑ k : Fin n, (s k - sq k) * ((L / (k.val + 1) : ℕ) : ℤ) := by
      rw [← hZ]; simp only [sub_mul, sum_sub_distrib]
    rw [hdiff]
    refine dvd_sum fun k _ => ?_
    by_cases hk : q ^ (Nat.log q n) ∣ k.val + 1
    · simp [sq, hk]
    · have hkL : k.val + 1 ∣ L := dvd_lcmUpto (by omega) (by omega)
      have hfac_lt : (k.val + 1).factorization q < Nat.log q n := by
        by_contra! hge
        exact hk ((hqp.pow_dvd_iff_le_factorization (by omega)).mpr hge)
      have hqw : q ∣ L / (k.val + 1) := by
        rw [hqp.dvd_iff_one_le_factorization (Nat.div_pos (Nat.le_of_dvd (Nat.lcmUpto_pos n) hkL) (by omega)).ne',
          Nat.factorization_div hkL, Finsupp.tsub_apply, Nat.factorization_lcmUpto n hqp]
        omega
      exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hqw) _
  · intro hadm
    obtain ⟨e, het, heB, z, hz⟩ := (simultaneous_prime_power_lift hn t).mp hadm
    have he_scaled : ((∑ k : Fin n, e k * ((L / (k.val + 1) : ℕ) : ℤ) : ℤ) : ℚ) =
        (L : ℚ) * ∑ k : Fin n, (e k : ℚ) / (k.val + 1) := by
      rw [Int.cast_sum, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      have hd : k.val + 1 ∣ L := dvd_lcmUpto (by omega) (by omega)
      rw [cast_mul_div_weight (e k) hd (by omega)]
      push_cast; rfl
    have hz_eq : (z : ℚ) / B = (t : ℚ) / L - ∑ k : Fin n, (e k : ℚ) / (k.val + 1) := by
      have hz' : (t : ℚ) - (L : ℚ) * ∑ k : Fin n, (e k : ℚ) / (k.val + 1) = (D : ℚ) * z := by
        rw [← he_scaled]
        exact_mod_cast hz
      have hDB' : (D : ℚ) * B = L := by exact_mod_cast hDB
      field_simp [hBpos.ne', hLpos.ne']
      linear_combination -(B : ℚ) * hz' - (z : ℚ) * hDB'
    have ht_le1 : |(t : ℚ) / L| ≤ 1 := by
      rw [abs_div, abs_of_pos hLpos, div_le_one hLpos]
      exact_mod_cast ht
    have he_mass : |∑ k : Fin n, (e k : ℚ) / (k.val + 1)| ≤
        ∑ k : Fin n with ¬ (k.val + 1) ∣ B, (1 : ℚ) / (k.val + 1) := by
      calc |∑ k : Fin n, (e k : ℚ) / (k.val + 1)|
          ≤ ∑ k : Fin n, |(e k : ℚ) / (k.val + 1)| := abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n with ¬ (k.val + 1) ∣ B, |(e k : ℚ) / (k.val + 1)| := by
            symm
            refine sum_subset (filter_subset _ _) fun k _ hk => ?_
            simp only [Finset.mem_filter, mem_univ, true_and, not_not] at hk
            simp [heB k hk]
        _ ≤ ∑ k : Fin n with ¬ (k.val + 1) ∣ B, (1 : ℚ) / (k.val + 1) := by
            refine sum_le_sum fun k _ => ?_
            have hkpos : (0 : ℚ) < (k.val : ℚ) + 1 := by positivity
            rcases het k with h | h | h <;> simp [h, abs_div, abs_of_pos hkpos, hkpos.le]
    have hrad : |(z : ℚ) / B| ≤ 1 + ∑ k : Fin n with ¬ (k.val + 1) ∣ B, (1 : ℚ) / (k.val + 1) := by
      rw [hz_eq]
      exact (abs_sub _ _).trans (add_le_add ht_le1 he_mass)
    obtain ⟨d, hdt, hd_rough, hd_sum⟩ := hgrid z hrad
    let δ : Fin n → ℚ := fun k => (d k : ℚ) + (e k : ℚ)
    refine ⟨δ, ?_, ?_⟩
    · rintro _ ⟨k, _, rfl⟩
      by_cases hk : k.val + 1 ∣ B
      · rcases hdt k with h | h | h <;> simp [δ, heB k hk, h]
      · rcases het k with h | h | h <;> simp [δ, hd_rough k hk, h]
    · simp only [δ, add_div, sum_add_distrib]
      rw [hd_sum, hz_eq]; ring
theorem H2_iff_eventually_local_obstruction :
    let LocalAdmissible := fun (n : ℕ) (t : ℤ) =>
      ∀ q ∈ Nat.primesLE n,
        ∃ δ : Fin n → ℤ,
          (∀ i, δ i = -1 ∨ δ i = 0 ∨ δ i = 1) ∧
          (∀ i, ¬ (q ^ (Nat.log q n) ∣ i.val + 1) → δ i = 0) ∧
          (q : ℤ) ∣ t - ∑ i : Fin n, δ i * ((Nat.lcmUpto n / (i.val + 1) : ℕ) : ℤ)
    OMA.R_Erdos317_erdos_317_variants_claim2_R1.H2 ↔
      ∀ᶠ u : ℕ in atTop, IsPrimePow u → ¬ LocalAdmissible (u - 1) 1 := by
  intro LocalAdmissible
  have heq : ∀ᶠ u : ℕ in atTop,
      (∀ δ : Fin (u - 1) → ℚ, δ '' Set.univ ⊆ {-1, 0, 1} →
        |∑ k, δ k / (k + 1)| ≠ 1 / ((Icc 1 (u - 1)).lcm id : ℕ)) ↔
      ¬ LocalAdmissible (u - 1) 1 := by
    have hshift : ∀ᶠ u : ℕ in atTop,
        ∀ t : ℤ, |t| ≤ Nat.lcmUpto (u - 1) →
          ((∃ δ : Fin (u - 1) → ℚ, δ '' Set.univ ⊆ {-1, 0, 1} ∧
            ∑ k : Fin (u - 1), δ k / (k.val + 1) = (t : ℚ) / Nat.lcmUpto (u - 1)) ↔
          LocalAdmissible (u - 1) t) :=
      (tendsto_sub_atTop_nat 1).eventually eventually_local_global_equiv
    filter_upwards [eventually_ge_atTop 2, hshift] with u hu hloc
    have h1le : |(1 : ℤ)| ≤ Nat.lcmUpto (u - 1) := by
      have hpos : 1 ≤ Nat.lcmUpto (u - 1) := Nat.lcmUpto_pos (u - 1)
      norm_num; exact_mod_cast hpos
    have hloc1 := hloc 1 h1le
    change (∀ δ : Fin (u - 1) → ℚ, δ '' Set.univ ⊆ {-1, 0, 1} →
      |∑ k : Fin (u - 1), δ k / (k.val + 1)| ≠ 1 / (Nat.lcmUpto (u - 1) : ℚ)) ↔
      ¬ LocalAdmissible (u - 1) 1
    rw [← hloc1]
    constructor
    · rintro hno ⟨δ, hδ, hsum⟩
      have hpos : (0 : ℚ) ≤ 1 / (Nat.lcmUpto (u - 1) : ℚ) := by positivity
      have habs : |∑ k : Fin (u - 1), δ k / (k.val + 1)| = 1 / (Nat.lcmUpto (u - 1) : ℚ) := by
        simpa [abs_of_nonneg hpos] using congrArg abs hsum
      exact hno δ hδ habs
    · intro hno δ hδ habs
      rcases eq_or_eq_neg_of_abs_eq habs with hpos | hneg
      · exact hno ⟨δ, hδ, by simpa using hpos⟩
      · refine hno ⟨fun k => -δ k, ?_, ?_⟩
        · rintro _ ⟨k, _, rfl⟩
          rcases hδ ⟨k, trivial, rfl⟩ with h | h | h
          · simp [h]
          · simp [h]
          · simp [Set.mem_singleton_iff.mp h]
        · simp only [neg_div, sum_neg_distrib, hneg, neg_neg, Int.cast_one]
  constructor
  · intro hH2
    filter_upwards [hH2, heq] with u h1 h2 hu
    exact h2.mp (h1 hu)
  · intro hloc
    filter_upwards [hloc, heq] with u h1 h2 hu
    exact h2.mpr (h1 hu)

/- ## Section 5: Endpoint-Specific Arithmetic & Small Explicit Failures -/

/-- **Composite prime-power base non-obstruction.**
At any composite prime-power endpoint `n = q ^ e - 1` (`q` prime, `e ≥ 2`), the base prime `q`
never obstructs any target `t : ℤ` modulo `q` (using at most a single coefficient `1` on
`{j * q ^ (e - 1) : 1 ≤ j < q}`). -/
theorem composite_prime_pow_base_non_obstruction {q e : ℕ} (hq : q.Prime) (he : 2 ≤ e) (t : ℤ) :
    let n := q ^ e - 1
    ∃ δ : Fin n → ℤ,
      (∀ i, δ i = 0 ∨ δ i = 1) ∧
      (∀ i, ¬ (q ^ (Nat.log q n) ∣ i.val + 1) → δ i = 0) ∧
      (q : ℤ) ∣ t - ∑ i : Fin n, δ i * ((Nat.lcmUpto n / (i.val + 1) : ℕ) : ℤ) := by
  intro n
  have hlog : Nat.log q n = e - 1 := log_prime_pow_pred hq (by omega)
  by_cases hqt : (q : ℤ) ∣ t
  · refine ⟨fun _ => 0, fun _ => Or.inl rfl, fun _ _ => rfl, ?_⟩
    simpa using hqt
  · let L := Nat.lcmUpto n
    have hpow_le : q ^ (e - 1) ≤ n := by
      have h1 : q ^ (e - 1) * 2 ≤ q ^ (e - 1) * q := Nat.mul_le_mul_left _ hq.two_le
      have h2 : q ^ (e - 1) * q = q ^ e := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      have h3 : 1 ≤ q ^ (e - 1) := one_le_pow₀ hq.one_le
      omega
    have hpow_dvd : q ^ (e - 1) ∣ L := dvd_lcmUpto (pow_pos hq.pos _) hpow_le
    let M := L / q ^ (e - 1)
    have hqM : ¬ q ∣ M := by
      have := not_dvd_lcmUpto_div_pow (n := n) hq
      rwa [hlog] at this
    have hm_dvd_M : ∀ m, 1 ≤ m → m < q → m ∣ M := by
      intro m hm1 hmq
      have hm_le : m ≤ n := by
        have : q ≤ q ^ (e - 1) := by
          calc q = q ^ 1 := (pow_one q).symm
            _ ≤ q ^ (e - 1) := Nat.pow_le_pow_right hq.pos (by omega)
        omega
      have hmL : m ∣ L := dvd_lcmUpto hm1 hm_le
      have hcop : Nat.Coprime m (q ^ (e - 1)) :=
        (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm1 hmq)).symm.pow_right _
      rw [← Nat.mul_div_cancel' hpow_dvd] at hmL
      exact hcop.dvd_of_dvd_mul_left hmL
    obtain ⟨m, hm1, hmq, hhit⟩ := mod_q_residue_hit hq hqM hm_dvd_M t hqt
    let dStar := m * q ^ (e - 1)
    have hd_lt : dStar < q ^ e := by
      calc m * q ^ (e - 1) < q * q ^ (e - 1) := Nat.mul_lt_mul_of_pos_right hmq (pow_pos hq.pos _)
        _ = q ^ e := by rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega)]
    have hd_pos : 1 ≤ dStar := Nat.mul_pos hm1 (pow_pos hq.pos _)
    let idx : Fin n := ⟨dStar - 1, by dsimp [n]; omega⟩
    have hidx_val : idx.val + 1 = dStar := by dsimp [idx]; omega
    let δ : Fin n → ℤ := fun i => if i = idx then 1 else 0
    have hsum : ∑ i : Fin n, δ i * ((L / (i.val + 1) : ℕ) : ℤ) = ((M / m : ℕ) : ℤ) := by
      rw [Finset.sum_eq_single idx]
      · simp only [δ, if_pos rfl, one_mul, hidx_val]
        have hdiv : L / dStar = M / m := by
          simp [M, dStar, mul_comm m _, Nat.div_div_eq_div_mul]
        rw [hdiv]
      · intro i _ hne; simp [δ, hne]
      · intro h; exact absurd (mem_univ idx) h
    refine ⟨δ, fun i => by by_cases h : i = idx <;> simp [δ, h], ?_, ?_⟩
    · intro i hnd
      have hne : i ≠ idx := by
        intro heq; apply hnd
        rw [heq, hidx_val, hlog]
        exact dvd_mul_left _ m
      simp [δ, hne]
    · rw [hsum]; exact hhit

/-- Both arithmetic steps are necessary as well as jointly sufficient. -/
theorem endpoint_iff_steps :
    OMA.R_Erdos317_erdos_317_variants_claim2_R1.H2 ↔ H1 ∧ H2 := by
  refine Iff.trans H2_iff_eventually_local_obstruction ?_
  constructor
  · intro h
    constructor
    · filter_upwards [h] with u hu hp
      have hno := hu hp.isPrimePow
      by_contra hmiss
      apply hno
      intro q hq
      by_contra hnone
      exact hmiss ⟨q, hq, hnone⟩
    · filter_upwards [h] with u hu p e hp he hpow
      subst u
      have hno := hu ⟨p, e, hp.prime, by omega, rfl⟩
      by_contra hmiss
      apply hno
      intro q hq
      by_cases heq : q = p
      · subst q
        obtain ⟨d, hd, hs, hr⟩ := composite_prime_pow_base_non_obstruction hp he 1
        exact ⟨d, fun i => Or.inr (hd i), hs, hr⟩
      · by_contra hnone
        exact hmiss ⟨q, hq, heq, hnone⟩
  · rintro ⟨hp, hc⟩
    filter_upwards [hp, hc] with u hprime hcomp hu hadm
    obtain ⟨p, e, hpr, he, hpow⟩ := hu
    have hpp := hpr.nat_prime
    by_cases h1 : e = 1
    · subst e
      rw [pow_one] at hpow
      subst u
      obtain ⟨q, hq, hno⟩ := hprime hpp
      exact hno (hadm q hq)
    · obtain ⟨q, hq, _, hno⟩ := hcomp p e hpp (by omega) hpow
      exact hno (hadm q hq)

theorem main : H1 → H2 → OMA.R_Erdos317_erdos_317_variants_claim2_R1.H2 := by
  exact fun hp hc => endpoint_iff_steps.mpr ⟨hp, hc⟩

end OMA.R_Erdos317_erdos_317_variants_claim2_R1_H2_R1
