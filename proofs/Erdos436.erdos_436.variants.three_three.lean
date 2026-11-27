import FormalConjectures.ErdosProblems.«436»
import Mathlib

/-!
Lehmer, Lehmer, Mills and Selfridge established the cubic-residue value.
This combines NickLeko's reduction, the certified search in PR 3942,
and the prime-realization proof in PR 4516. The search certificate is recoded
and the obstruction table is shared to fit a single submission.
-/

-- Reduction Erdos436.erdos_436.variants.three_three.R1 of Erdős Problem 436 — three three
-- Credit: @NickLeko
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-! `Λ(3, 3) = 23532` (Lehmer, Lehmer, Mills and Selfridge [LLMS62]), split as in the merged
reductions of `four_two` and `seven_two`: a finite search over cubic characters (H1) and the
realization of one extremal character pattern by arbitrarily large primes (H2).

* H1 is the upper bound: every labeling of the primes up to `23534` by `ZMod 3` has three
  successive integers in `[1, 23534]` with zero sums, starting at most at `23532`. A SAT search
  (one-hot encoding of the labels, `v(n) = v(n / spf n) + w(spf n)`) finds no labeling avoiding
  such a triple through `23533`, so H1 is true; a Lean proof needs a checkable certificate.
* H2 says every cubic character pattern on the primes up to `M` is realized by arbitrarily large
  primes `p ≡ 1 (mod 3)` (Kummer theory and Chebotarev). The proof of `main` applies it to one
  explicit pattern `w`, found by the same SAT search, that admits no three successive zero sums
  below `23532`.

The proof checks the whole lower obstruction through `23531` in the kernel and lifts the upper
search to a primitive root of the finite field. -/

namespace OMA.R_Erdos436_erdos_436_variants_three_three_R1
open Filter Erdos436

/-- Every labeling of the small primes modulo three has three successive zero sums. -/
def H1 : Prop :=
  ∀ w : ℕ → ZMod 3, ∃ n ∈ Finset.Icc 1 23532,
    (n.primeFactorsList.map w).sum = 0 ∧ ((n+1).primeFactorsList.map w).sum = 0 ∧
      ((n+2).primeFactorsList.map w).sum = 0

/-- Every cubic character pattern on the primes up to `M` is realized by arbitrarily large
primes `p ≡ 1 (mod 3)`: the cubic characters of distinct rational primes are independent. -/
def H2 : Prop :=
  ∀ (v : ℕ → ℕ) (M B : ℕ), ∃ p > B, p.Prime ∧ 3 ∣ p - 1 ∧
    ∃ u : ZMod p, IsPrimitiveRoot u 3 ∧ ∀ q : ℕ, q.Prime → q ≤ M →
      (q : ZMod p)^((p-1)/3) = u^(v q)

lemma lift_sum {p : ℕ} [Fact p.Prime] (g : (ZMod p)ˣ) (e : ℕ → ℤ)
    (l : List ℕ) (h : ∀ q ∈ l, ((g ^ e q : (ZMod p)ˣ) : ZMod p) = q) :
    ((g ^ (l.map e).sum : (ZMod p)ˣ) : ZMod p) = l.prod := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons,List.sum_cons,List.prod_cons,zpow_add,Units.val_mul,Nat.cast_mul]
    rw [h q (by simp),ih (fun a ha => h a (by simp [ha]))]

private lemma upper (search : H1) {p : ℕ} (hp : p.Prime) (hbig : 23534 < p) :
    r 3 3 p ≤ 23532 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  let unit (q : ℕ) : (ZMod p)ˣ := if h : (q : ZMod p) ≠ 0 then Units.mk0 _ h else 1
  have hexp (q : ℕ) : ∃ t : ℤ, g ^ t = unit q := hg (unit q)
  choose e he using hexp
  have nz {n : ℕ} (hn : 0 < n) (hs : n ≤ 23534) : (n : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun d => (Nat.not_le.mpr (hs.trans_lt hbig)) (Nat.le_of_dvd hn d)
  have cubic {n : ℕ} (hn : 0 < n) (hs : n ≤ 23534)
      (hc : (n.primeFactorsList.map (fun q => (e q : ZMod 3))).sum = 0) :
      IsPowerResidue 3 p n := by
    have hc' : (((n.primeFactorsList.map e).sum : ℤ) : ZMod 3) = 0 := by
      simpa [List.map_map, Function.comp_def] using hc
    obtain ⟨a,ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hc'
    have h := lift_sum g e n.primeFactorsList (fun q hq => by
      rw [he]
      simp [unit,nz (Nat.pos_of_mem_primeFactorsList hq)
        ((Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactorsList hq)).trans hs)])
    rw [Nat.prod_primeFactorsList hn.ne', ha, mul_comm, zpow_mul] at h
    exact ⟨nz hn hs, ((g ^ a : (ZMod p)ˣ) : ZMod p), by simpa using h⟩
  obtain ⟨n,hi,hn,hn',hn''⟩ := search (fun q => (e q : ZMod 3))
  obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hi
  have hr : 1 ≤ n ∧ ∀ i < 3, IsPowerResidue 3 p (n+i) := by
    refine ⟨hl,?_⟩
    intro i hi
    interval_cases i
    · simpa using cubic (by omega) (by omega) hn
    · exact cubic (by omega) (by omega) hn'
    · exact cubic (by omega) (by omega) hn''
  exact (iInf₂_le n hr).trans (by exact_mod_cast hu)

/-- Trial division computes the sum of `w` over the prime factors (with multiplicity), given
enough fuel and a starting divisor below every prime factor. -/
lemma trial_sum (w : ℕ → ℕ) : ∀ (fuel n d : ℕ), 2 ≤ d → (∀ p, p.Prime → p ∣ n → d ≤ p) →
    2 * n + 1 ≤ fuel + d →
    (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) fuel n d = (n.primeFactorsList.map w).sum := by
  intro fuel
  induction fuel with
  | zero =>
    intro n d hd hp hf
    by_cases hn : n ≤ 1
    · interval_cases n <;> simp
    · have h1 : n ≠ 1 := by omega
      have := hp _ (Nat.minFac_prime h1) (Nat.minFac_dvd n)
      have := Nat.minFac_le (show 0 < n by omega)
      omega
  | succ fuel ih =>
    intro n d hd hp hf
    dsimp only
    split_ifs with h1 h2 h3
    · interval_cases n <;> simp
    · have hprime : n.Prime := by
        by_contra hnp
        have hmf := hp _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd n)
        have hsq := Nat.minFac_sq_le_self (show 0 < n by omega) hnp
        have : d * d ≤ n.minFac ^ 2 := by nlinarith
        omega
      rw [Nat.primeFactorsList_prime hprime]
      simp
    · have hdn : d ∣ n := Nat.dvd_of_mod_eq_zero h3
      have hdprime : d.Prime := by
        have hm := hp _ (Nat.minFac_prime (by omega : d ≠ 1)) ((Nat.minFac_dvd d).trans hdn)
        have hle := Nat.minFac_le (show 0 < d by omega)
        rw [Nat.prime_def_minFac]
        exact ⟨hd, by omega⟩
      obtain ⟨q, rfl⟩ := hdn
      have hq0 : q ≠ 0 := by rintro rfl; simp at h1
      have hdq : d * q / d = q := Nat.mul_div_cancel_left q (by omega)
      rw [hdq]
      rw [((Nat.perm_primeFactorsList_mul (by omega) hq0).map w).sum_eq]
      rw [List.map_append, List.sum_append, Nat.primeFactorsList_prime hdprime]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      congr 1
      apply ih q d hd
      · intro p hpp hpq
        exact hp p hpp (Dvd.dvd.mul_left hpq d)
      · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
        nlinarith
    · apply ih n (d + 1) (by omega)
      · intro p hpp hpn
        have := hp p hpp hpn
        rcases Nat.lt_or_ge d p with h | h
        · omega
        · have hpd : p = d := by omega
          subst hpd
          exact absurd (Nat.mod_eq_zero_of_dvd hpn) h3
      · omega

private lemma factor_character {p : ℕ} (u : ZMod p) (w : ℕ → ℕ) (m : ℕ)
    (l : List ℕ) (h : ∀ q ∈ l, (q : ZMod p)^m = u^(w q)) :
    (l.prod : ZMod p)^m = u^(l.map w).sum := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.prod_cons,Nat.cast_mul,mul_pow,List.map_cons,List.sum_cons,pow_add]
    rw [h q (by simp),ih (fun a ha => h a (by simp [ha]))]

set_option maxRecDepth 65536 in
private def obstructionWeight (q : ℕ) : ℕ :=
  ((0x400000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000004000000004004000000000000004000000000000000000004000000000000000000000400000000000000004000000000004000404000000400000000000000400000400000000400000000000000000000400000000000400000004000000000000000000000000000000000000400000000000000000000000000000400004000000000000000000000000000000000000000400000004000000000000000000000004000000000000000000000000000000400000000000004000000400000000004000000000000000000400000000400000000004000000000000400000000000000000000000004000400000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000400000000000000000000400000000400000000000000000000000000000000000000000400000000400000000400000000004000000000400000400000000004000000400000000000000400000000000000000400000000000000000000000000400000000000000000000000000000000000000004000004000000000000400000000000000000004000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000004400000000000000004004000000000000000000000000400000000000000000004000000000000000000000004000000000000000000400000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000004000000000400000000004000000000000000000000000000000000000000000000000000004000000000000000400000000000000000000000000000000000004000000400000000000000000000000000000000000000000400004000004000000000000000000000000000000000000004000004000000000000000400400000000000000000000000000000000004000000000000000000000000004000000000400000000400000000000000000000000400000000004000004000000000000400000004000000004000000000000000000004000000000004000004000000000000000000000004000000400000000004000000000000000000400000000000000000000004000000000000004000000000000000000000000000004400000000000000004000000000400000000000000000400000000000000000000000000000004000000400400000000000000000000000000000000000004000000000000000000000000004000000000400000000000000000000000400000000000000000000000000000000004000000000000000000000000400000000000000000000000004000000000004000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000400000000000000000000400000400000000000004004000000000000000000000400000000000000000000000000000000000400004000000000000000000000000000400000400000000000000000000000000000000000000004000000000000000000000000400000000000000000000000400000004004000000000000000004000000000000004000400000000000000000000000000000004000000000000400000400000000000004000000000004000000000000000000000000000000000004000000000000000000000000000000000000000000000004000000000004000000000000000000400004004000000000000000000000000000000400000000004000000000400000004000004000400000000000000000000000000000004000000000000000400000000000400000000004000000000004000400000000000000000000004000000000000000000000000000004000000000000000000000000004000000000000000000000000000000000000000000400000000000000000000000004000000000000000000004004000000000000000400004000000400004000000000000400000000000000000000000000000000000000004004000000400000000000000000000000004000000000000004000000400000000000000000004004004000400400000004000000000000000000000000000000000400000004004000000000000000000004000000000000000004000004000000000400000000000000000000000400000000000000000000000000000000004000000000000000400004000000000400000000000000000000000000004000000000400400000000400000000000000000000400000000000000004000000000000000004004000000000000000000000000000000000004004000000000000000400000000000000004000000000000000000000400400000000000000004000000000000000000000400000000000000000000000000000000404000004000000000000000000000000400000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000004000000400000000000400004004000000000000000000000000000000400000000000004400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000004000000000000000004000400000000004000000000000000400000004000000400000000000004000400000000000000000000000000000004000000000000000000000000000000000000004000000000000004000000400000000000400000000000000000004000000000000000000000000000000004000000000000000000000000000000000400004000000004000000000400004000000000000000000004000004000400000000004000000000000000000000000000000000000000404000000400004000000000000000000000000000000004000000000000004000000000000004000000000000000000000000004400000004000000000004000000000400000000000000000000000000000404000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000400400000000000000000000000004000000000000000400000000000000004000000000000000000000000000004000000000400000000000400000000000000000000000000000000000000000000000400000400000000000000000000000000000400000000004000000000400000000004000000000000000000000000000000000000000000004000000000004000000400000000000000400400000000000000000000004004000004000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000404000000000000000400000000000000000000000000000004000000400400004000000000000000000000000000004000000000400000400000000400000000000000004000000000000000000000004000000000000000000004000000000000000004004000000004000000004000000000000000000000000000000000400400004000000000004000004000000000000000400000000004000000000000004000000000000400000000000000004000000000400000004000000000000000000000000000000000000000000000400000000000000000000000000000000400000000004000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000004000000000000000004000000000400000000400000000000000000000000000000000000400000000000000000000000000000000400000000400400400000000004400000000000000004000004000000400000000400000000004000000000400000000000000000400000000000000000000000000000000000000000000000000000000000000004000400000000000000000004004000000400000000000000000000000000400000000000000000000000404000000000000004000400000000004004000000000000000000400000004000000000004000004000000000000004000004004000000000000000000000400004000000000000000000000000000400000000000000000000000000400000400000000000000004000000000000000004004400000000004004000000000000000400004000000004000000000000000000000004000000000000000000000000000000004000000000000004000000000000000000400000000000000000000000000004000000000000000000000000004000000000000000000000000400000000000000000000000000000000004000000000004400000000000000400000000000000000000400000400000000000400000000000000000000000000000400000000000400400000000000000400004000000400000000000000000004000000000000000400000000000000004000000000000000000000000400000000000000000000000004000000400000000000000000004004000400000004000000000400000000400004000000000000000000000000000004000000004000000000000004000004000000000000000400000000000000000004000400000000000000000000000000000000000004000000000004004000000000000000004000000000000000000000004004004000000400000000000000000004004000000000400000000000000000000000000004000004004000000000400000000000000000000000000004000004000000000000000000000000400000000000000000000000000000000004400400000000000000004000000000000000004000000000000000000000000004000000000000000400000000000400000000000000400000000004000000004000000000400000004000400000000000004000000400000000400000000000000000000004000000000000000000000000000000400000000000000000000000000000000000400400000000000000000000000000000000004000000000004000000004000000400000000000000004000000000000000400004400000000000004000004000000000000000400000000000000400400000000400000000000000004004000000000000000004004000000000000000000000000000000400000004004000000000000400000000000400000000000400000000000000400000000000000400000000000000004004000000000000000000000000400000000000000000000000000000000000000000000000004000000000400000000000000000400004000000400000000000000004000404000000000000400000000400000004000000000004000000000000000000000400000004000004000000000004000000000000000000000400000000000000004004004000000000000000000000000000000000000000000400000000000000000000000000000000000000004000000000000400000004004000400000004004000004000000000000000000000000000000004000000000400000000000000400004000000000000000000004000000004000000000000004000000000004000000000400000000000000400000000000000000004000000000000000000004004000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000400000000004000400000000000000000400400000000400000000004000000000400004000000000000404000000000000000000000000000000004000000004000000000000000400004000000000004000000000004004000000000000000000000000000000000000000000000000000000000000000000000000000000400000400404004000000000000000000400000000000000004000000000000004000404000000000400000000000004000000000000000400404004000000000000000000000000400004000000000000000000000000400000400000400400000000404400400000000000000400004000000000000000000400000000000000000000004000000400004000000400400000000000400400000000000000000404004000000000000000000000000000400000000000400000000000000004004000400000400000000000000000000000400000004000004000004000000000000000400000000000000404000000400000004000000000000400400004000000000000000000000400000004400004000000000000004000400000000404000400000000000000400000400400000000004400400400000004000000000004004000000000000000000000400000000000404004000000000400004000000000400000404004000000004000000000000000000000000400000004000400004000004000000000000000000000400000400004400000004000004000004000000004000000000000000000000400000000400400400000000000000000000000000000000004004400000000004000400000400400000400000000000000000000000000000000400400000000000000000400000000400004004000000400000400000000000404000000000000400000000000004004000000400000000400004000000004400000400000000004004000000404004000000000004400004000000000004004400404000000000000000000000000000004000404000400000000000000000400000000000000000000400000400000004000004400400000000004400000000000004000004000000000000000000004000000000000004004000004004000000000000000000004000000000000000400400000000004000004000004000000400000000004000000000000000400000400000000000000400000000400400400004000400000000000004000400400000000000000004004000400000000004000000004000400004000004004404000400004000004004000404400004000000000000400000400000004000000400000000000000400404000000008000000000000000000000400004000000000000404000000400000400000000400004004000000000000400004400400000000004400000404000000000004000000000000404400000000000400000000000000000000000004000400000004000000000000400000400004404400000000400004000000000004000004004000004404000000400400000000000400000004000000000400400400000400004400400004000000400000004000400000400000000004004004000000004004004004000400004000000400004404000000000004400004000000000000004004400804400400000000004000000000400404008000004000000000000000000404004400004000004004004000400404404000000400004000000004000400000400000000000000000004400000404004004400004000000000400004000008000400400400000004000400800400004000400004400000000004004004000400800004404000000004008000004400004000400004400404000004000000400000008000000400400404000400008000404000000000400404000000404404000000000000400400004400000400004000000804000404004000400004004000400000000000004000400404000004400400404400004000004004004004400400800000004000400400008004000000004400000800404000400000000000404404000400404004400004800004000404000400404000004000400804400004004000000408408000000400004404004000400400400004400800400000000000004404000004400400404004004400004400404000000004404404000400400004404004000400404404004400400404004040 : ℕ) >>> (2*q)) % 4

private lemma chunk0 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 0 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk1 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 1000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk2 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 2000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk3 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 3000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk4 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 4000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk5 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 5000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk6 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 6000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk7 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 7000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk8 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 8000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk9 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 9000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk10 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 10000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk11 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 11000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk12 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 12000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk13 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 13000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk14 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 14000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk15 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 15000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk16 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 16000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk17 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 17000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk18 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 18000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk19 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 19000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk20 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 20000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk21 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 21000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk22 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 22000 1000).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

set_option maxRecDepth 65536 in
private lemma chunk23 (w : ℕ → ℕ) (hw : w = obstructionWeight) :
    (List.range' 23000 531).all (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) = true := by
  subst hw
  decide +kernel

private lemma lower (primes : H2) (B : ℕ) : ∃ p > B, p.Prime ∧ 23532 ≤ r 3 3 p := by
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℕ, w = obstructionWeight := ⟨_, rfl⟩
  have hcheck : ∀ j < 23531, (fun j => !((Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+1)) (j+1) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+2)) (j+2) 2 % 3 == 0 && (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0) (fun _ ih n d => if n ≤ 1 then 0 else if n < d * d then w n else if n % d = 0 then w d + ih (n / d) d else ih n (d + 1)) : ℕ → ℕ → ℕ → ℕ) (2*(j+3)) (j+3) 2 % 3 == 0)) j = true := by
    intro j hj
    obtain ⟨k, hk⟩ : ∃ k, k = j / 1000 := ⟨_, rfl⟩
    have hk24 : k < 24 := by omega
    interval_cases k
    · exact List.all_eq_true.mp (chunk0 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk1 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk2 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk3 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk4 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk5 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk6 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk7 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk8 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk9 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk10 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk11 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk12 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk13 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk14 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk15 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk16 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk17 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk18 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk19 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk20 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk21 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk22 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact List.all_eq_true.mp (chunk23 w hw) j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  have obstruct : ∀ n : ℕ, 1 ≤ n → n ≤ 23531 →
      ¬ (3 ∣ ((n.primeFactorsList.map w).sum) ∧
         3 ∣ (((n+1).primeFactorsList.map w).sum) ∧
         3 ∣ (((n+2).primeFactorsList.map w).sum)) := by
    intro n h1 h2 ⟨ha, hb, hc⟩
    have hj := hcheck (n-1) (by omega)
    beta_reduce at hj
    have two : ∀ m : ℕ, ∀ p : ℕ, p.Prime → p ∣ m → 2 ≤ p := fun _ p hp _ => hp.two_le
    rw [show n - 1 + 1 = n by omega, show n - 1 + 2 = n + 1 by omega,
      show n - 1 + 3 = n + 2 by omega,
      trial_sum w (2*n) n 2 le_rfl (two n) (by omega),
      trial_sum w (2*(n+1)) (n+1) 2 le_rfl (two (n+1)) (by omega),
      trial_sum w (2*(n+2)) (n+2) 2 le_rfl (two (n+2)) (by omega),
      Nat.mod_eq_zero_of_dvd ha, Nat.mod_eq_zero_of_dvd hb, Nat.mod_eq_zero_of_dvd hc] at hj
    simp at hj
  obtain ⟨p,hpB,hp,hd,u,hu,hpr⟩ := primes w 23533 B
  let : Fact p.Prime := ⟨hp⟩
  have vanishes {n : ℕ} (hn : 0 < n) (hs : n ≤ 23533) (hc : IsPowerResidue 3 p n) :
      3 ∣ (n.primeFactorsList.map w).sum := by
    obtain ⟨hnz,x,hx⟩ := hc
    have hx0 : x ≠ 0 := fun he => hnz (by simpa [he] using hx.symm)
    have hf := factor_character u w ((p-1)/3) n.primeFactorsList (fun q hq =>
      hpr q (Nat.prime_of_mem_primeFactorsList hq)
        ((Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactorsList hq)).trans hs))
    rw [Nat.prod_primeFactorsList hn.ne', ← hx, ← pow_mul, Nat.mul_div_cancel' hd,
      ZMod.pow_card_sub_one_eq_one hx0] at hf
    exact (hu.pow_eq_one_iff_dvd _).mp hf.symm
  refine ⟨p,hpB,hp,le_iInf₂ (fun n ⟨hn,hr⟩ => ?_)⟩
  suffices h : 23532 ≤ n by exact_mod_cast h
  by_contra! h
  exact obstruct n hn (by omega) ⟨vanishes hn (by omega) (by simpa using hr 0 (by decide)),
    vanishes (by omega) (by omega) (hr 1 (by decide)),
    vanishes (by omega) (by omega) (hr 2 (by decide))⟩

theorem main : H1 → H2 → type_of% @Erdos436.erdos_436.variants.three_three := by
  intro search primes
  rw [runLimsup,Filter.limsup_eq]
  apply le_antisymm
  · apply sInf_le
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_gt_atTop (23534 : ℕ)] with p hp hprime
    exact upper search hprime hp
  · apply le_sInf
    intro b hb
    have h : ∀ᶠ p in atTop, p.Prime → r 3 3 p ≤ b := eventually_inf_principal.mp hb
    obtain ⟨B,hB⟩ := eventually_atTop.mp h
    obtain ⟨p,hpB,hp,hr⟩ := lower primes B
    exact hr.trans (hB p hpB.le hp)

end OMA.R_Erdos436_erdos_436_variants_three_three_R1

/-! Cubic triples of Lehmer, Lehmer, Mills and Selfridge, "Machine Proof of
a Theorem on Cubic Residues" (1962). An independent three-way search picks
a prime, branches on its label, and ends at a triple whose factors have all
been assigned. The table packs each prime and its three child references
into four 16-bit fields. Lean recomputes all three weighted factorizations
at every terminal case. Credit to @NickLeko for the reduction. -/

namespace OMA.CubicTriples
private abbrev F := ZMod 3
private abbrev Env := ℕ → Option F

private def put (e : Env) (p : ℕ) (a : F) : Env := fun q => if q=p then some a else e q

private def Agrees (w : ℕ → F) (e : Env) := ∀ p a, e p = some a → w p = a

private theorem agree_put {w : ℕ → F} {e : Env} (h : Agrees w e) (p : ℕ) :
    Agrees w (put e p (w p)) := by
  intro q a ha
  by_cases eq : q=p
  · subst q
    simpa [put] using ha
  · exact h q a (by simpa [put,eq] using ha)

private def score (e : Env) : List ℕ → Option F
  | [] => some 0
  | p :: ps => do
    let a ← e p
    let b ← score e ps
    return a+b

private theorem score_ok {w : ℕ → F} {e : Env} (h : Agrees w e) (ps : List ℕ) :
    ∀ a, score e ps = some a → (ps.map w).sum = a := by
  induction ps with
  | nil => intro a ha; simpa [score] using ha
  | cons p ps ih =>
    intro a ha
    cases hp : e p with
    | none => simp [score,hp] at ha
    | some u =>
      cases hs : score e ps with
      | none => simp [score,hp,hs] at ha
      | some v =>
        have he : u+v=a := by simpa [score,hp,hs] using ha
        simpa [h p u hp, ih v hs] using he

private def Wins (w : ℕ → F) := ∃ n ∈ Finset.Icc 1 23532,
  (n.primeFactorsList.map w).sum = 0 ∧ ((n+1).primeFactorsList.map w).sum = 0 ∧ ((n+2).primeFactorsList.map w).sum = 0


set_option maxRecDepth 4000 in
private def packed (i : ℕ) : ℕ :=
(if i < 349 then (if i < 174 then (if i < 87 then (if i < 43 then (if i < 21 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 0x437b100000026ce8518164d01068002ae2710c4198863603e0009049b62d18164c00068002ae2710c000669361250a80006d085b04000e6d6a79800240166c90004c150d20000892797b80013556243c2127fb100000437b100000046ce851800010106b8ca94a6d8b5e655c4e218e329049b62c0014a536c5800003181097190003ee220000046c2497792e0000a9bd3349e70f0006885a3108c0f2680834fc64a0f38790010010000 else 0x1900030212000b468a0200011e0c9c9c4f00b2020d00000e302120000148a020001e4d01068002bd003150005834e2188320006c07d610000d9d08002f31de914cc00044b28cc10146c24800160d388620c8011b01f6ab0005b01a876af400054de9890f3878002d1a28084f354e4802d188000a521d89d4a900c6800201002070000023021294800072638ef97c4f7c625235c1c98e0000193931c000c4879c3c000fc4c0848000081f711) else (if i < 3 then 0x61300061f36bb8b74000417960994588aee2dd000107ee65e8f22600068463410c54000c1830000179828a0000153921c9480000021e3100ace4458002949c88b00000e302120000127dc4400001d14040000021b3a15840004041a8320006c07c00157138862758049939300055c4e2189d6c8464e4daade4d6c068000012280800003b36742b08b2680835aad64d6c068002d1a280800047832726c2ca9c90058000058e44580046200207 else (if i < 4 then 0x80d0004c63b12a0006de517d00017948a7b0001f82486e00076370a26000af09e2180011f8face0001b82280200044030dae000740694f000106d6a860000052c5a800062036000008a248c000009e44bbee800407166616c636324e891471be4d8263f0001731080021fb40006c636324fc8cc301c59bc0001d8548000001e9b90006c636324ab4cc301c5800151a3105aa9ab90000800077835112b960009c430000011570700037a19a8d else 0x6130000013715ed0cc7c5400000cd8c900034325c150005758fd20dbabb800430001a198f8ab6eb810000c4b545d5e522e1c0000026d6c9c9d44918000009b1925756208fd20b64e4e8da8d81c0015c84286b430001500000d3e520c7cf7a00025844000db8a0003631b1920005dc005190f800114474001794d5c88003801c5973e3000440307e51748ac6d7d00017948b800001c59774447700026a4cd78738658f8001d944aee38e0000c))) else (if i < 7 then (if i < 6 then 0x6dd0004b536f02edab2ca9a20000d8c931b8004441786200041b5ac380008da8c001f76038b214800000137e67f76b34ad100006c6497962800008bbd443c071600076535220c220006dc5000001d8412b458002111a8d547700026ce0000a228cf8c001100c00046f9c59700081579d23098bb8be830fca2e8000dbf28003edb80005dc0011896abca6ae452d40017948b460001d01a4f60003f04902a0007165dd111de37c98000049a889 else 0x59c88000044da0000786d4000005d58b3593b6acb2a6618f836324a26000af09c000030f4dcba44278003a539000007291b0000836b400221e038b46c800307a50000025dc18000bca6ae45a21cfcd8c92f2c503bd116f90005dc18bcb14000045a20060d8c900000aaee0c0005e5357231c0000df2521f000002ceb440001b1926370008882ec380008da8d4c8001100c33f00020dad0007dd80e2c8520000024dc21db565953f3000359a5) else (if i < 8 then 0x13c26ab38042da089a20000d8c92ce00041e228018ec00074f3c03ac406d6700020f11299000220188018ec000750fc0007b2860dc001880dc8e8003c8977448a30002600000e7a6e58263f0001746c800307a562100043f6800117c9a301498000004cb440039b19239c00636324c131f8000ba36400183d2b1080021fb40008be4d180d100006c649498000000c803c7c4071686e00076370dae0007406944c0015e13a9e00020dad else (if i < 9 then 0x48b00057216d700006a225c38000010db2a0004862800068687f2b24ae0400031715ba11c08abab10000108fd00036324dba000bb8312d62811c08b2a000486288c400008116ae40000e2221fda18000ab1f00002e097bd00003420bb8e3800032034001318eafa0002f2914f60003f04912a00004c514f000106d6c370003b1b85130005784edae0007406a2180011f8f8000052892391d0008772e000fbb01c59bfa28c0009af70002ad2c else 0x83b8184041b030000c4e35150000004644f38e2ae0e5c40008c51cd700009ae26371b18d8890000011c28d8c452a00016c0f030ae42000008129073ac80000a0848b89e00016f540007ca41770001710635c0003b28961100036f28a1ad0c000553cc001858b3db8001f8245e500047022f38000ec8e143000001164514068001d58500065b42a26000af09e45db1d85db0003631b1927e480d0003a834000c3c7d61400196d0c6b363b0bb6)))) else (if i < 15 then (if i < 12 then (if i < 11 then 0x3575dc5e518ffc000836b546800108cb2e10002201872a45d89122c220006dc50001b18d8c90002ee0008c5138965784ebe8dd0bca45ef58f9d94480041bb0f9b3f300070e10ae4a8d1882c0000603ac38002948068b00057200310b96aa4000320ec0010106baca6c4628e00000235012b96000b22320edbd0cd46ae580033d0c00000336224bca8ba000451c00010d872ee38e2349059f72746d460000027ca40005e115c84000000ab908 else 0xa4a41ceb200000a2122e2780005bd50001f2905dc0003f918d70000eca25435a198f8aa458002b90b6b800035112000d0cc7c56495c08fe4632a000486288c400000a16ae4000008221fda18000a80031f000894b868836325230eca6a44000000cd444b09c1b0001b0cf0003632505f20b1e44dc3a0d8350db038002b90850d6860002a0000207ca400018f80284c36800315380006e43372e0000067e0900011740048ac82ee2fa0c) else (if i < 13 then 0x575620000211fa0006c6492d62800008ae88000012974c00057748b6620ef9a51d300015dd22d98003e6948d800041b5aef510f11e592d40017948abab102ee100005468c416aa6ae400020001de0d444ae58002710c12e00055c1cbb8b74000420bd97a3c8980001d1a51c00000a0360f076000c4e340014a4008581dab9000085cb6f467a19030000ae421e10000f94822a0238000c3f90008c51cd700009ae25bbd17579488240001c28d else (if i < 14 then 0x457bd00012c220006dc518f1b18d8c92ee38e0000c7bd00064f12a1ad0c00056034001318ec4ac771b79400000335112c2622e0006c001a198f8ac6208da868b8c400057216e1c0000226d95000243143760000010c5dc71c000211fa2366c64a0e80015dd23718000022900011836324ee8000738654f0000e6d6ad9bfd44e9453c00041b5b14400098c7544c0015e138003433c1155b300000128a4eff488e65bbc42d7948b6e8000050c else 0x5dc71c0001901a00098c757d00017948a7b0001f8247cd8ee00028e3400074069910001880dace440000225eb00000252d64eda000a965a3e1d58b3fc0003b1b85130005784ea78000836b43d23e1d58b3760002ee0c6e300000352e980007e09144c0015e1388b08b42ca58a20004c73a000004836b5d30000fc12361486a1fb40f688780e2c000eca6a441844000db8a3762ee0000c68c0003a0340008eed064d0a5b3d79488000019f290))) else (if i < 18 then (if i < 16 then 0x64b4d762f1c000008ae42000206101068000009929264b7aa4361cc96f5518a3a0620ed89c68600001c28d0000104a41cc960000082122e27800058003d51f2904f30004232cdd8bb8b883122c0015c85b5c0001a8896e300078052e1c0000086dbb000034c62ee3d5000108fd0003632516310ec2c595d5880000836e8002ee0c8fd0d1363250b400005c215c80000905b2a0004862863c00036324d10000036261fda18000abde80000790 else (if i < 17 then 0x236324dba00030c317715d63f4836e8000c20c5dc5750002096a8ba00045c09a1a1fcac620002b90b70e83600036dba000008315d5880000847e8001b1924b58a000022e982feaee912d5ba1794880000b83e0700052900816000ae4004200020ed0106b25c2d2270e0000033501200107666a3572c0016446472b5c2270e59f7275124600000e7ca40001e115c8400040c2020d00045e00112c96d70c5e38000004c949325a6ba1b0e else 0x13e5200768bd230251500015486325b8e2ae0e1030003851a0000149483992c00000c4245c4f0000b0007aa3e520dd8bb87f23122c0015c85b5c0001a8896ec0003f918bb8f54000423f4000d8c938134331f1585a00000c10ae40000082d950002431431e0001b1926880000bc130fed0cc7c54000010f9480003de834890006e43372edd8bb8000317d11757948aee38e0000c7bd0a964f120000126a22584e0d8000dc620002b90b)) else (if i < 19 then 0x59f34a3800104c7dc440016ea28080002ee2710c74e7da70f5e00124a9c432098000d5c8a25800361945ba5cc00020a54000004353d80019b5238a8014289643900068f48d9c000ef65a3156c8edc70000619b22000003e34a380000241f21c0020ed89c68002948040b03e572000100800006a02572c0019e860000011b1128e50004361cbca8ba20244001c9d1b11c72ad92270e0008185721000000464a48000114f948325c2d21b0e else (if i < 20 then 0x58400700942ab6000008758f0000f590273c40000226098fc0005cc7cfea694716100000090b8a80037b964e78808ae44e2a000dee5a4222753e8cb67000428965450007d73400000c786d5ca8001100c2ae3c90000e5dc0003b720ea60007506d3d8001e2123593b6bc0aa72a00044030ab8f2400039770000edc827b0003c4247aa0003d64111cc1509c7c00000cd444800492a710c5fd0003361b18a090d7038001c9cdcd1800002bf10b else 0x7150008512cab600004c7539e20000112a6c7e0002e72a000440310f200109c7c0020f0f5903718004382988a897000620011789a301da2274000cb49b960003e5840004fa42fd2f50000bde44000008bba20002cb937de84562b7314e00080e4dd200014e5d32800021fb46530006415aa26000e0e9df780018adcb593b68002a91490269d36bb800076e418b8001100c2a28003eb9a7bc0003c36a86c0000064956c010000eb8a80037b96))))) else (if i < 32 then (if i < 26 then (if i < 23 then (if i < 22 then 0x43600000024d64edaaaca9b38002144b27b0003c4247ef00072e42a8a0a4fae6800001cdb84a4a80019b0d55c0006b81cbb8f7a000413d800000922e1000220187919123372f0fed0c7e0552540000f06c3fb43000154f60003f048ab800004e3977000002482a28003eb9a7bc0003c36ac7c00069471ca8001100c2ad8000181d4e788000044c131f8000b80e0000f59042b47629cba5450007d734f78000786d5a20001530931f0001a51c else 0x52a6860041aa2600000c9d4a80000046bc13431f81543a0003f02ad9c000ef659534001d997340b054271f54d0000025cd0200109c7d4a80058286a950003b30d7dc6863f02ad700008ba25770000edc82950000090d4f6000788490fed0c000556100000350a1b0000059263e00034a38a8a000fae698b8001100c2ad8000009d6098fc7f55ce2a000dee5939c0022b913ca8004271f86300044c6d07000098ea5ef0150f0dab17029a2018) else (if i < 24 then 0x8d90008f54ae5400088060002095471ec8a4800021b85c0007d476b2e0007ac8211400101cbc494058001b8509237bb7ebf20000044e1880019056b14800424306b276d4cd551a60009f4660e000131d4ba40001ecba4e70308ae4487400000255534052271731f0001a51c87960a84e3e0000028ba254a80d8cd86aee0000021052a0130001ad9c0010a2590ec000fc0ab04805bb32e68800054c24a8a000fae68000008f0dabee0001f815 else (if i < 25 then 0x5ee00300058cee00c0006d288094095baf70000012c9249100005f2292040446d9dc000008da51000000379249109025e94403c000dc075d5d471ec2e0003ea3b00000f3d640e8908a0005dac9db400153f4c880002f0000078594ab82000880620f8001d61bc0d000204285ee00063d5800104aa38f6452400000dbf2c37408385c100044030bdc000c7ab2452408000dc1f0063ac377440000022f0a0000f76fe45202e48cdb593b68002a else 0x8c900040850cee00008c6d288094001bc803aba8e3d65000043f690c4000c82b60c80013f1e3f400001e1362900084860ef8000dacac000081f85942e0003ea3b00000c3d640e8908a0005c0000215812b593b68002a7e99100005eb82000880620f8001d61bc0d000204285ee00063d5800104aa38f6452408080db593b68002a7e991001f5ee880000025e3640895812c6c8002b0256b276d00054e54000880600000110214000412a8e3d))) else (if i < 29 then (if i < 27 then 0x83c3d640dc60010e0a5fa1c1c0009c8e0002039779e80b69d36b080000ce8618c001131b41c000263a9748000538749ce00115c89cf40001799bef0003e1b98da897000620011789a301da0000054cbfd0001eb2065000043f690c4000c82b5ac9db400153f4000485137440000042ec52001090c20c80013f1e3be00036b2b92a0447e164c52001090c20c80013f1e3be00036b2b92a0007e1651b20011ea95ca8001100c2f70210002c else (if i < 28 then 0x74400f0002ed64eda000a9e50194044dc2e0003ea3b00000a3d640e8908a0005dac9db400153f4c880002f79490200036b82000880622940013f1e000000c2ca583e06a7586f07c000eb0dd7b80198f563a20000009779480b07736d64eda000a9e50000004dc80412a8e3d72a00044030fcb0dd022e247400101cbc49405bca1b87900084e3eab600001675d200014e1d2738000022272a00044030fd0e0e0004de4400101cbc49405b4e9b else 0x7c400000c32ff40007ac81d10000010bbca4058001b629000848611b512e000c42862f13460314800424306b276d000551b512e000c624c0010fda00045e268c092a0257e1651b512e000c40022f134603148004243000000443f68e880011265e114000f5903ca4058001b72a0934403000001afc2ca170001f51d8000041eb207448450002ed64eda000a9fa64400017bca4810001b5c10004403001c000ac0960f8001d61bc5280727e3c)) else (if i < 30 then 0x62900084860ca000087ed20c80013f1e3be00036b2b92a0007e1651b512e000c63640023d52b95000220185ee0b900059192000810a19dc0002f4da5102383bb743a89c0002ac7c00069471b38315decb38a8001fe1652a0000c01afb8d0c000558f8000d28e2a68000222e68100084e3eab71f8000756100002d90c31800226368380004c752e90000a70e939c0022b9139e800056b37de0007c372fd00000704e1880019056bbe00036b2b else (if i < 31 then 0x87900084e3e9ce0010788956c000034eb950002201879100000a2ee88e0e0004dac9db400153b8800266b383800087053060000c82b6248001a74da9780036b2b8690007d476c52001090c1a7a095471ebf4383a039386300044c6d07000098ea5cf40003659c31000320ad0008bd4d180d64eda000a9fa00024289ba20000041762900084860ef8000dacae0c80013f1e46d44b8003165000043f69254000fc2ca140001eedfc8a029c919b else 0x7fa0003d640e90000a70e939c0020f113ef0003e1b98380004c752e7a00001ece1880019056b593b68002a7e800090a26e880000125ddf0001b595b14800424308da897000620011789a3000000050fda3950002201892a0007e1650a0000f76fde5020248cdb148004243077c0546d656bf20001ec4e1883d59056a9500001a0d7dc6860002ac7c00069471c54002144b469800396197fa0003d640e90000a70e9f78001f0dcac20003b921)))) else (if i < 37 then (if i < 34 then (if i < 33 then 0x74400012626c1c0011ea95df0001b595b593b68002a1181187e16514e00080e4d8380023d52b593b68002a77c0006d6571f6000810a0000001f85939507a220185f900000226e9000023ce939c46e2b9127388e457229081504fa32d9c000ef6590e8000480a8003054271f72a79244030f4a0000b2f953400008173408004271f52a00060a1afb8d0c000558f8000d28e2adc7e0001d58400077242e2a0010a25a18c001131b46980039619 else 0x74800060e75034000810a1df0001b595bf4c880002f5c100044030bdc000c7ab0000009f859000412a8e3d9149020023600104aa38f6452400000dc1f095c18b777c0006d656fd3220000bd704001100c2f700031eac748000000751f6000810a0448449f8593a4000005ba8450000032ee880002624ddf0001b595881092bf0b28a700040726ef8000dacae3ec00102143593b68002a0000017e1651b201aac0963640323d52c2280000297) else (if i < 35 then 0x8d90148f54ad64eda000aa29c0024289b0700047aa57440000062ec52001090c1df0001b595c950003f0b28500007bb7f2280012466de943a202df3148004243077c0006d657192000810a1e94000015f4950003f0b272a00044030bdc2a0000b19dc000554da5106f86fb792a0007e164e54000880617b84b4001633b8980a81b7a572c0007d0b8000fa8ed8a4002121800000b9eb2091c8450002f14e00080e4dac9db4001500000642ca5 else (if i < 36 then 0x1117e1651b2200ac0961880019056c228000009774410b1122714e00080e4e24c0010fda3593b68002a60e0000044aef8000dacae3ec00102143e400027e3c0f50f57e164ac0000fc2ca2963d53f1e32800021fb48620006415b0640009f8f1da0000094cbfd0001eb2074800000c74d64eda000aa29c0024289ba20068001762900084861192000810a1e9400000df3be00036b2b92a0007e1651b20251ea95df0001b595c950003f0b2 else 0x6290008486000002a7ac82472114000bc53800203936530006415ad64eda000aa24c0010fda45280027e3c0000068594ae90000c1cea06800102143be00036b2b7e99100005ef292040006d704621100c3be00036b2b7e99100005ef292040006d704001100c3a40000003a5ee00063d591f6000810a0478479f8593a40000053a8620006415b08a0140005e29c00101c9c4980021fb48fb00040850f900009f8f1df0001b595b593b68002a))) else (if i < 40 then (if i < 38 then 0x143f68e5400088061df0039b595b148004243089300043f69192000810a1e94000001f3e400027e3c77c1236d656d64eda000aa29c0024289ba20000041762900084860c1c00007e95df0001b595800000a1fb472a00044031254000fc2ca140001eedfbca02b4919b6290008486112600087ed18380000d92c64800204287a50000027cef8000dacadf204453f1e3be00036b2b7c80004fc79254248fc2c9e95cb0001f42e0003ea3b else (if i < 39 then 0x7448450002eca6000c82b5ac9db400153a40000023a7710004cd67064000c32f00000121652baf8832263660e0008594aee200099ace0c8001865e3148004243077c0006d656fd322047cbd6100003050c3c8004271f86300044c6d07000098ea5cf40002e59a73800457228da897000620011789a301f78001f0dcaa680002bae76800002532ff40007ac821880019056ba4000006ba6b276d0005514e0012144dd10000010bb1480042430 else 0x60f0006b44abdd222000b19dc001a74da51000418b78388a787052d64eda000a98380000112bb8800266b3629000848610700010e0a594048d0fda3d68003ea3b62900084860ee200099ace0e00021c14ab00003f0b28328f5000791b512e000c59400010fda3be08d36b2b7910db5bf2e0010787ac81b8c0021c14c4544b800310008bc4d180ed0ff400065a4dcb0001f2c200027d215ee00063d5914e000b2e4d9400010fda3ef000315b9)) else (if i < 41 then 0x76800000332ee200099ace0e00021c14bd28a3c05be7a572c80b7cca6000c82b5bcc00003ccba40000023a6b276d00054ee200099ace0e00021c14c53802a03936b276d00054ee200099ace0e00021c14c538002039360e0000014ac52031090c1580001f8593148004243065000043f690651ea270f1d2000001dd3d2b960003e85c0007d476c52001090c1ac9db400153b8800266b38380008705314e01880e4de95cb0001f000002a0393 else (if i < 42 then 0x74800000774e880000384d8a400212183593b68002a76800000232ee200099ace0e002e1c14bb8807a66b374400001526d64eda000a9da0000024cbb8800266b383800087052c1c000002958a400e12182b00003f0b2629000848610651ea000f1df0001b595c6d44b81b317710004cd66c1c000004958a4002121841c002438297ad0007d476c52001090c20e00021c14ab00003f0b27a572c0007d229016d3a6e248001a74db593b68002a else 0x7826860002ac7c00069471c54002144b2ad8000451d54d8fc0005d0f200109c7d39c0001b913950002201858400006b430c6000898d80022f534603ef0003e1b90000113d640f2308a0005dbcdfe8000cb71800438298a700040726ca6000c82b5ac9db40015349b960003e88a89700062ca000087ed1dc40013359ba4000001ba62900084861064001212f05cc1c61652b0700042ca5629000848610640dd212f1e44000098bc18000320ad)))))) else (if i < 65 then (if i < 54 then (if i < 48 then (if i < 45 then (if i < 44 then 0x2783c36acee0007506d0ec9d9ef0ac130001f71144b00026628ab80004be393d8000971200000122e8952a0003361b23b22466e5d77000002482950000030d7dc6860002ac7c0006947156c000008eb04c7e0002e8ee2723d640b084e24c285b38002144b2a2939beb9a68800054c24a8a000fae6800001cf0dab8a8004289652a0000011afb8d0cf78550e8001ef0a8003054271f0001573d641238f30b805d44c0005593a950000a88d else 0x5450007d734bb800c76e41b38001568b2ae3ee8000e4f600068f48a8a000fae69770000edc831e8001eb207ef28072e4292b0980003575000003963670004289655c7dd0001c9ec000d1e91770000edc8317000220185450007d734000002786d5d4c9e4ea0dbd50001eb2064827c00026876a82000558f8000d28e000442a03976f389d90f32d9c000ab459571f74000727b000347a45dc0003b720c5c000880618f4000f5902a28003eb9a) else (if i < 46 then 0x50d6860002abb8000aa4317fc000fc1239532e28a115dc40e0001914400098c753cc001958b2d40002841b5c800036f291dc0007ac8149c00111cca1b00024b127e272746d46aa600051a200000063105a72c131f71167a0004e2180000626e68e098000fb8880000322e8952a0003361a9ec000d1e91570001ae072ee3de800106e96860002a970d10a984912c000038a2954260000d5d400000558d9c0010a259571f74000727b000347a4 else (if i < 47 then 0x80005124686c00f1f049e3c000e80d2898002bc27004000512460011087fa99ef0008f0dab8d0001d01a0000013d64104f10b0ee5def0000f0daa898002bc2759c880000450a2000eac59cb80018cd0c2741e2929f0006860012aa26f04af09d720000004a4774489eb207cd8913d640b380006e08a1ac001d9448004373153800060700b100000047ac81720000dbca4514772e39d5c800036f28c5c0009a46228800171ce9f98002841b else 0xb8eb10aa4cf4000311780015bc48000011eb208a20004c63ab911dce4652288001318eae40003919459c0003e744c5c0009a461bbc0014508c28b16b2b165dc80c00018000004ade25708001100c3df41820dad8a20004c63ac5c000880617d00000748b04c7e0002e4f600057749060000836b4069a18000ab1f0001a51c5c800000e28b38000cea8a1f80018cd0c2700023f1f8ee0003d6410a2000008598b0000e80d2898002bc27))) else (if i < 51 then (if i < 49 then 0x7826860002abe800000245cdc02d770839b805aee108e20005c63aeaa000016257219d4000a33d0000018c5dc80c00020f04d0c00055dee21dd58b3c1343000157370005dc20be8000002458f8100d28e000448a201852689d78732e6eeca6a442310000dc058000039a88900092559118000b66df25184577000080003428011500045d35722eecf98a327556df31464ead9b3a800146f992567a18e6e00076e418bc00100c6c6200001a8b else (if i < 50 then 0x7dc6860112aa26000af09ddee21c000b0000029a90945e00000110b231d2bb8300023a5644600022e9ab916378153372e000002e4e21549649770636c3430001555b0005c73ab24000bb83172000000ca3c40001f82480200044030e5514112245e22200fc121f380000f088c400037016da0000786d544c0015e13800006268c067a00000418bb9018000423a4000d484ae433a8001475500c5c63b1c400098c75d540015bc4ae433a80014 else 0x5270004473271e000f3a4561c000004dbaa42a32da157300047e3e9ec0007e091b34ad101cbb91800003888c400036f16bb9018000317d000000c8b95000220187dc6860002a9ed1007e09200a245100c4624759b78b8c40003e51600001ea248df880016c840000021a9095910005dc18dd2d0c000557fc000fc12289c74abc275920005dc18b9000000c51f71a18000abc40001f82455b0005c73aef710e000580021323cc8c0139522018)) else (if i < 52 then 0x69f0006397b0fa0009a46227c0017c0d39500028a114f362d0002ca18000c7ab1f540014491c9347220dad80200044031188000c0e2d77203000062fa0004489183000041b5b0fc000c66861380011f8fa7b0001f8247910008772f0a200000e5a0063b0001d28980029c277dd00051246c131f8000b9d1228c0009b44000468127a08846b94d0031d8000e944c0014e13b2ac66800287a08843fd4d05ed360004e3123ac0005aee2070000c else (if i < 53 then 0x52689d8de3200000e6a22400000ccd86afec928000c6f452a00016e6ef547ca41bb249400064622c88000b73786b3e5205745746947000001500c6c622950000b7370003e52113cc0e000221ac000d444bc834daa01359c00006244e6e00007c40000009d944a2f3de800088c48eb86b1701a000b8e757200000c0a3ee3430001563e00034a3800001c046216e800000c5aa933d0000c4f30006562cddec5aa284577000154862ff8001f824 else 0x74c0005774904e0011fe5df71a18000ab1f0001a51c6e38c800052ef710e000596700019d513e6c50479918a20005c73b16b140f9a44000010d28e2fa374000118e20004c63b144000ade25f71a198f8ab9b8002ee107bd00056f1301a00098c757223b8000a2fa0003e6914f60005774904e0011fe5df71a18000aace4400002271a0003a034da0000786d544c0015e13b593b68002a5960007562ce5c000aac858f000234093ee800236a3)))) else (if i < 59 then (if i < 56 then (if i < 55 then 0x50d0005a12a9b0d0c00035418001200b3d1c6e1b11262700089e1a86c0006c44976616c0009c3580046e0950d5410002a000ef2f06698ba3b5100c2a9000002885c40005f11c9ae000ade25434001684aa6c3430000d6088514802d0d60006a02549800111ccbe595e2f88e4a40000c81c0000687ac821680000a844620003038b52a0004031acf40000203177203000080000011a9095c200044030f220f266e5d720000024a4510002e39d else 0x91c00038b2e000dc269471cd51dd28498000009c59745555256f18dd8aa4ade311515495bc63c22dd234900007783501318a9aed9838000018f9480003c2001084790004041ab38c706e0880021acd404a212070000c8c54d75f11c8a80000323000002903842ae0000010e4d745e000128f29b0808351e400101069f98002841b86b45e000120000026dc51435a15e28a80023ba50934365d936224e0a0006de51570000014726b80700009) else (if i < 57 then 0x6ce88777b2cab8b6476e38000054aa83000004a1e873ad52900016e6e0006a6410800014884a2148a8000c45e00067a107580006de511fd35c0007000262a9a8d43652136224cca00068864eb0001914a1d68000008b52a5b04031aff40007ac80000004d4c8210435a910942000052212a1d22a0003154800181c423fa522f88e00003b1540e000a520202c000030034423c8002020d89e4d80001cd988bc0002400001cc7480000019eb20 else (if i < 58 then 0x13ee229cb04d1882e0980023105b3d0002710c44b8e00002892a02e000350ec000de8ab670003b71672a00044030ab8f2400039770000edc83f7ba0397210000040060eef0a520002de10000f94822a2070000c7a3520362251880009302d4a802900c68003939b9a30000037e21600104c7dc440016ea2808331c373b2388260003ee229ec000d1e916e97300008000002a710c52a0000011af60d0c6f4550e8000de8aa2580036194 else 0x300034a38bcb04c00044001ed4de8aad90002892344b5b36c328840000ae41989d26231038003431bd150007b050d160011880081ceb400000432e52901b112000520362251cad7086c38eb4000008300037a2628c8c57026b81cb96de89c4300000164a03305800000873ad03b4981675800000250dee380000428748aa710c37b0000131000002e00c1dde14a40005c358001f29045440f00018b88000be239434000de8aa6c2628080d))) else (if i < 62 then (if i < 60 then 0x52a57216b96000b22300000051387472a45801876b889e0000ebb8b74000416c8000fad1af2c131f69100068637a2a000f60a1a2c00231000c39d6800000864426f44c518b96de8a4c30eb4000088300037a2628c44b0006c32918ab66d7038000050cd868002950088b0008c40010e75ac4e56218eb400000c34628002270e00062637a2a896b6692a5172c00138860000012270e00066936324594592694717716e800080003349b192 else (if i < 61 then 0x4f254e8512c0000048de454a92540006bb9c939a49b4f26168512c000aa600a215d8000d0cca950002020d5830004e118b22000b4625571f2dae072d18001a8890008c56b81c0000027dc4571557138460002ae2708c52a5836f41a0000e06323c0000fcfc449bd800003085fe0003361ab8400088060001a18de8a8003d82868b3ad0005720cd571890fe1c00005d11cc80000619b0d00075d0030c000c160021ceb54a508059d6a952100b else 0x6e480c3b720000eca6a441b86214000e40ac502c0115a3000351120010da8b0e1f6d730edc82b9000003087590004a41ce4400084e3d54800138463c238e000100005a335212a98d106c64968c000d444b5c0002520e7220004271e9c0000d86514040016a4ba4b0001b1924f200080e2c000de89c2324223e4d0cc800006aa30644a00000228e600009c231961572314737c8002708c52200036e12000ab8cb0391a10f400078002a980088)) else (if i < 63 then 0x83f45870eba0008083560c0013846000000ad18955c8c56cc1cbfecda8e890fcc00187cdae58002708c5910005a3120011b864a49f2c0010d871bdbc5a138f5a300035112ef000000219dd61b9161c24b0001b1927210000011eb9724a9c23231509dae072948000118752a0004031ab6000002219292314000727000032c1400000461a2e000b52014215d8000d0ccbe98002d1895778277f448b5200000c2000168c0084aa90002708c else (if i < 64 then 0x44300000712000b46002211e53650106a4b0001b1128c671d000228e0d7000039e8c000edc8290428a290f5a300035010000b7463a4139609960088003bc221890005725a3106f600000e3d9a4000c94900026c99a8d44e0006cc1c000f16686653c8001b38b483b16800115cb5914e11918a84ed983800154c05440000031a1990005760010c840ef0b462572c00138462c88002d1890008dc32524bcaf1a7da455d800001c30002d4a4717 else 0x652200012eca0006a441f2c0014cc72720004618b44a89d36e28a6c87a0003c00148800848002104620b8c54e46cc1ceca0006a441ce000138862e22ae2998e0004023740e91e0000022176a3dcf7898000019a809000496361240009ae86c38f7d570fe861f88001e70f00049636124a6600086c3a0bd1dcf78980001da6d8b0008c401d0e00000a0221908110c0004ad18001a8080005ba31d200009caafe4539241a314727900024016))))) else (if i < 76 then (if i < 70 then (if i < 67 then (if i < 66 then 0x344030a26000af09d950001e8942ce43e9b82259c00037044932000c406d950001e8944714068001d89900046278bdad8c6c648001b18d8c920d00030f1f7e480d2cb3a8fe000948397d00017948a7b0001f8246540007a2510dc000ec6e1b5df80e80d473aa34620b00002209c0800002c60c1800100801038002909b0920005574501118a00086c394cd35dae04800000a28086146274041ac28c4e00034000018d10ca9b21e8000f else 0x7aa0004a41cc220246dc521ad8f9d944800003817870005298e716000ae40082172d548000600039a192926600004041aeb29b086c3972dbb19e864624738000b6070005721103000070a35435a18000a8000029f29063e56a00012f5400094839844000db8a32a0003d12868c7e042234c7c000eca26254000dbca2ee00000a8c00071c4a41c9e6000c2c59edc000fc122f28002381179c00076470c58dae00069cb800196d0a860000052c) else (if i < 68 then 0x63e56a000120008eebb44c0000112907279800211960005dc5c418ca8000d20a0f8da55100c3088001b71468c7e042134c7c000eca26254000dbca2ee3760000c47f0004a41cbe8000bca453d8000fc123823f01d01a00001234a3800000a0821c0014a639c58002b900b085cb552000180010bea2a460edbbd0106c624738000b6070005721103000070a35435a18000a8000031f29000056a00312d7000094838001b90cdcba5c3631b192 else (if i < 69 then 0x7273511200124a9c4314a8000cd86b658001ab9156a5cc0002118a00076e3961179922508000141b22000000e34a380000080d21c0014a639c59622b9000082c5000350131988baaaa4631239c0005b038002b9088180003851aa1ad0c000540000bcf9480002b5000896b802a4a41c0008eebb44da31f8d084d00000182d870005298e716000ae458620af5cd0c9494624738000b6070005721103000070a35435a18000a8000049f290 else 0x56a5cc2c12000124a9c432098000d5c8a25800361945ba5cc000209ec580d1e9154c000064433d0002710c8260003ee2289600000251515f81f5cd0000039b7094950003361aab8000d70395a9c8c000827b00015ca45ee0004d65800122466e5e439f4dad4cadc8004289649500a0001abb8e4600041570000edc721c8000022468800054c24a8a000fae68000a94f0daa1d1523de1568800054c24a8a000fae690e8000fc0abdc44eb5a99))) else (if i < 73 then (if i < 71 then 0x38f0008b222d8a000a106d7659740009b170002691850d54165c2b1ce0011882c00007cdcd1aa980000a8867a0004e218ab800001c3a098000fb88a25800002144f600068f480000028ba254a806ccd86adcbeec289600000436e1292a00066c355a9c8c000827b000347a45ee27b4d658bb8e46000412561300006adcbeebbd966b80006701304c0007dc4512c000004a27b007347a45dc7233b7200000066a224002495388629500019b0d else (if i < 72 then 0x5c82cd36f28000c0e01221674000dc1122f0003b2894a40000031d13c00080635720000dbca47f42b1ec3a62f0004031ab900006de510d9cd18f094358001a8895dc40e000180010dcc54e16e4001958b2e40001b794527000447328fe00001639674000dc1100016ba4b1224c0004031afc800098c756a0001f94dab980023f1f82f69b0002671e000f3a45ba0000d28e286aa08001572e85465b4286c00092c49674000dc113178002018d else 0x5635da5402686c0000044972400100c6a86b433131572b76d7d15400001a07e1c0014a639c580010c8030800000148e2ecd2e686c44929489000072270002020d91c0003d64086ce686c448001de0d404c62a6b8000e4360003622489c00066c35109bd17c464624738000b7370003e5200000167ac8000181c014425242d0000e62f0004031ab380006e089178001d944aee3762a90c86b00035112bb881c000300021b98a9c2dc80032b16)) else (if i < 74 then 0x8c48e7498171ce0011882c001c9cdcd1c130001f711000007447329ec000d1e9000000d38862951080000d5b97b80002cb74b98ef64112c001b0ca2ae2d90010e4f600068f48f96b64000396e9730edc800000a84b8600000143d0e75aa531ce2ceb639c00059d60001b79400000135320840ad4a44250800014884800001303884790004031aa1ccf498a3143800085863760001eb200004a40041ccca0006886544c0015e13800001a018d else (if i < 75 then 0x520362240000006947172dbd16446294c73aa30700000e9280cc160000021ceb639d26059d60000049437b8e00001075a0011882c000010d10ca870002710c77400049624a26000b2a9c001c9cfb11a9500029a8d43c68537a2a75a0006de2d4a92554d469bd8000050800a00b0000f1ce0011882e098000fb88b3d0002710c44b8e00002892a43a000356e4001db8b21d8001bd157b800064632d64eda828a80000040083bbc294c738b else 0x3ac02f49528eba00066c340000040083910a94b558b8c47bf498171cef7f1882c00000ccd468002952b90b0008c48e70eb9659ca4c300000615c85901462473870000010100c75af7e8402c0000c400c3800294c738b0005203622518a9ae86c3a39c0023105ab52e6000100000034e218d960006ae46314000edc73813ee1bd1555c0003b71cb640006e68db2c000fb88800103a4b127b07dc37a2a00000aae42c00231239c396600019a8d)))) else (if i < 81 then (if i < 78 then (if i < 77 then 0x5725a3106f60000023d9a5cd0c9491e7ad4a5e175298e70000e000002a8c19ad55d8d0ccabb0001a19952a0000021ab060009c2307f954dbd042022a9800085a300035112000f96d70387fc000fb88b7a2ae2708c00005e3191e0000647e224dec000020400000219b0d00052a0021675a000ae41989e31239c3c73a4c4620700068637a2a000f60a1a2daae31239c3800008223990000040090c402c160001ceb40010805a9500019b0d else 0x5ba450106f600079c3d9a5484d849000001228088e70008c416a54c4e80834001ad4d10cc738004620b42052200012ad20006a441f2c0014cc748aaae2710c0004023740e000a531ce2d23c00000442b4add234905695cc469200000249b62c00231239c38000018058642044300012b460006a0215a96e8c7482790002401600000200310000b5291c5d5d869cd0ccb2b2a92708c4430003501292c0006c449482145cd078003bc22189) else (if i < 79 then 0x4435a300012000002768c998a1b9161c0002dd18e904e58cc58022b460006a02510c001de0337fadc1a79d5fd0004e11800000a69470014000034300034325b1500052a50d16000e9eb601c019aadbd040000008040650e91552212000d0c96c540014a943458003a7ad8070005ad6f4100008bc0022557135db3071bdad318c8f00052a39116cf4ae4de820000664d6cf00000a81a0400000f3060c00080400a1c0014a639c5ab48001a990 else (if i < 80 then 0x539c32000d5a69e74001f91624b3da0001e135000812540268528bb14044001ab4d3cea83c03000265e545d8a022a53076a8c1c00003c0742000003983060000056270e000a531ce2c001484d849253aab80008000522350127bedcc73c31129915254a0000019ba070005293911600091e8a02129d55cd8490002951c88b00048f45010e6eb748d2400014a936c5800201473874d900000810000004ae41908110c0004a724831c90e else 0x819002100010768f21c1514a4e4458000129c80b00083b8e70e000b4c6323c000050d404c7280019e0e00000c37a2a0000089c231154000cdcbbd522a0001000052036224d96bca6ae4400147cd8893d538e0001000000239c32f68000786d56c8004fad1a702d9800145e58c68a0220000049c231154000cdcba702d9b391400051f36224f54e3800041795e39ed488002901b1127380004e1191ca00067839ea9c7000082702e400014))) else (if i < 84 then (if i < 82 then 0x819002106f60006323d59a168e48700006f9c80b00000133c1d1ca9171ce1c000060c6478000061a8890005a68e70e00000a6f454000009384600022a010104558053372e000a3e6c44800dc7008480130002708c00051f36224000e38050413816cc000a33940299b970005a67780e000a406c449ce000138463deb8e000104e05c800028000d5a69e740000b0e70c8003f22c4967b40003c26aa0f00c000996c9c9cfad1ad344f47387 else (if i < 83 then 0x7e237346e700008bc252a21b4f49c2dd2e64501089580c3e520e700008ba2400001e47840000029b9a34f600068e48b3e00000a2d5140017c0d000316c28968ca4f333d1d0bafc40022e39d9e80005c35c061f29055c00033d1d1ce00000c2d9e8000008444ac06000108a091e3ee22b74b98000416cc000d444ad93939b9a30000043901112a0007ca41ea8000f59043580022f094a886d62a7112a0007ca42035b9da94e8000101b220 else 0x6a56e76ad3a0000089c231ed4000d5c88002d999e0e7bf0004473311094a66e5d6e973000082ae2d999e0e37b00000510cf40009c230000004fb88c4ac064501089400076e2d12b018ef641ce000138462dd2e60001000000149624ab80006783967dc9cdcd180000e2708c000010357231ce00001c2c0019e80304253800003120007e237346e700008bc255140017c0d31300025b155800008a020db0cad0a2595140017c0d31300025b15)) else (if i < 85 then 0x3ad00042016a531ce0001c0010f4c647a1e0001bd156657bf344320000066dc24eb4000dbc5a94b22800076f950e39e1800104278ed943a4553846313800006875a60003191e9c000092a500022551a480004738038b48b00044e1c000f547ac8216800227842d48001c59759f7e200046bb6000d064d9797211dc48003039c80859d6383704489600092a50000060c647c738002080b00000b3f112c4c0006f454dec00000842c88002708c else (if i < 86 then 0x4e05c800028e700009c23000147cd8890000031ce197bd71c00020000d5a69e74000304de8ab360001e4360007e45892ca3417cb525def5c7000080003569a79d0bb0bb37a2a127032000200002e8e40580041dc73878e500033c1c000b4c6323c000010d4048510002708c00051f36224f54e380004027428cde8aa702e4000147380004e118000a3e6c448000000e70cbd538e0561000000e0620c75800000e5000002d48848002871cf0c else 0x5a979848d2eb74b98000416cc000d444b13049a5b1500000639010a1a00096c55f700011784a798003fe166d80003e520d32000c66857998b4fb88a8680025b150006e76a53adfe001180261ae034f94800000e9b22000081900510000ae47222c0000051e43b25c4f1c90e48b0003921c6f70b46323c0005b0e40584680019e0e0000a63191e00000a6a22400169a39c3800000a708c4e05b380f28000a3e6c44824dc7005c80002d33bc07))))))) else (if i < 130 then (if i < 108 then (if i < 97 then (if i < 92 then (if i < 89 then (if i < 88 then 0x48b85a33d1c91600067a39eaa030f94828680025b157380008c01291615267a38000050c647c738002078b37b00000c100000027e2258981d4de8ab130001bd150000053ee22d10000a3e48000004dcd1ad4b2d2469789400076e2cdb1018ef641a95b9c000ec4a0003b71654558c5ef340000026a2258981c0de8ab130001bd155ba5cc00020000ef6db059570270cf072ae00019e8e8e700000716cf4000006218980012d8abee00046009 else 0x7383f1126f6000b64222796450405800003ad90885a0003d640e700008bc25f700012d8a8000009ab9162689e01517110b520005da657996fd0c4f33d0000b50d0004b62ae0404318024002124f0da80000398c8f0007383f1120000026f45639d8990405b130002080b37b59100010000b6667839ed4234d5c8c2e8000010b7e267a00010e70e4e6a224000020e40428680025b1573800045e120000026ae45602030f9480000009eb20) else (if i < 90 then 0x6380003e5208bcb9000025e411dd2849a2580024a940000414e1180000506e68c002124f0da80000b99e8e00000c357220000066323c001ce0fc44b658002080b6267b537a2aacc0007ac821680000044272b3d2458b8e700038f16e700006a2258980012d8a8003e5a23995f865d540271ce0009162c00001117448002c8800887ef5e648942c4c00096c542a5ce0c647b1300025b1500067a00110c96e9a7ac81ce2478c64780000198c8f else (if i < 91 then 0x37b00035110000c4867a3912d960db8a2bb0001a1995450000023489600092a51962418cf47226c8319e8e37a0005a61eaec00068665c6e3d8ea8e0000581a51c0000080820c75800000a500002ed48848002871cf0c3ad00042016a531ce0001c2c50f4c6478590001b70966c8213c76cc4e00001a1d698000c647a7000024a940008e70051691600089c380016b6278442d0001eb20790564000268bca809422400181ce4042ce8001b822 else 0x46140e000a426c24929d55c00040002949c80b002522350128f2e220002000239ce405baca2719e0e0000013740e8f291e8a02000123d14042520001c90e44e8e7391160008040161c0014a536c580026c802880004790010c840886b4624001de110c49bdad30000f44e4276cc1cb460006a02510c001de0322700019e0e6245a64b01f1ce0009b62c0000055183332abb1a19943b00000b2a00000ab4c3cfc40000044a99b1219e8e))) else (if i < 94 then (if i < 93 then 0x4e433c1086ca7ec784a0655c8000400000898c8f00000635112000d0c6f45400169804438002901b1120006f44e1188aa00066e5e394630cf070002d33bc070005203622400000473864001bd1384646322e9ab918e500033c1c9c0b9000050001ab4d3ce8003431bd1580f6f44e118b4c0000041d22c000cf072cfb9433da30006f44e118896e60d8650000004e4431d612a9b79450d6864b62a000318752340000380b0200000418306 else 0x7783501200200066e5c001a192d8aa2137a2708c0000123d64091600001839698000c647c2d000002085a900048e2eb3ee520008d7680023c89bbbb4325b1559f72800046000cb49785d1b800111cc8004619a8890006864b62a9c0b670ca50001390cf040002d4a5e1737b0003191e86ca7e000492a21b8f45c2458000040e5a60003191f09a0011e44d9780011dc4800001b4d884a753f00024c02000be0694ad6a52f0bbee34325b15) else (if i < 95 then 0x37b2ac3191eb380007ce88dec000c647a458000008e45e7dc78a12c70b7476e4122c000cf070003ee1a88975d02844733032ae400020000028c6478000021a8890006f44e118000b4c0961d154000cdcba703d3b39140005a67780e000a406c4480ec000e70cc7280019e0e4e05c803e28b4c0000841d22c000cf0741d8001b22070e8365093600008472218eb0000dbca2ce12f9b82200052a03d1675a000048180000156c038fbad680008 else (if i < 96 then 0x42044324712b460006a02510c001de03000436a2c3857675d3433212ab60000180015c8008435a8001a19937b8585a61eb460006a225258000d8c93908002d30f66300045870e360007547167dc4000119f642c1a19900002b34a38000a5404e2ceb400005830000022d80721c6ab00010000ef06a0240b0000cdcba52a6b99e0e0006864b62a000b5a01820000018f5902458000008e45e7dc74d12000b7476e400016a4e2cba2f29580009 else 0x546390160000126323c001de0d444800000a708c61309461f36000004678380019a4d8c90030031ce1956a5ba00020000cd26c648aa0aa0de8a80000019e0e0000014e118e70ef06a22512e42db0ca000006010040000083060c00000cc4e1c001484d849253aab80008000522350120008407202c850000d10cab4ae61a990569213353204280006e81c0014a8e445922a47a280800052a4db1600080400e1d364000008400014fab906)))) else (if i < 102 then (if i < 99 then (if i < 98 then 0x8a837a2a000a527222cded5c80004000001a708c4550003372f1ca00067839ea91508a8800028f9b1128e500033c1cf54e3800041c61a6400108000019ce197b40003c36ab640007d68c88887ccdcba702d98001467221d3372e6f7032000200014a4e4058002901b1127380004e1191ca00067839ea9c7000082702e40001400000339c32000d5a69e74001f91624b28d11325e170006ad34f3aa0f00c000999c888d2f0ba3cc0c80008 else 0x80545400020e00bca6ae4400147cd88900038e000902448053372ee30d32000840000a0e70cbda0001e1b55b20263eb46e0455e9c2322a16980003ab52dd000102ae2ae4e118000b4cef01c001480d88939c0002708c7bd71c000209c0b9000050001ab4d3ce8131229ce195a689e0370ea52000a8c1d698000c647ab300019e0e70e00050936000d8a8d2400015a8d444bd800025b954e05b36c4280010760421c001698c6478000089f889) else (if i < 100 then 0x7dc1a845e1313c3380002d4340012d8ac4a8001f2907dc0008c012b72462ff85800000ce405ad98001a8897bd5ba00020a9a40eb62b96e973000082d98001a8895b977b7fc2c00005e6c8808ae06400040000129c80b00000833c1c000acc6323c000014d444c72a458000704f0004e118000cd26c64815c000e70ca25bfd361948e548b7780e0000346323c000048d4448000071bd150005a600c0e0000089c231154000cdcb8002901b112 else (if i < 101 then 0x62637a2a6f600000221571f70cf472ae3ee19e0e37b00000110b72442edc596e973000082dcbbdbb7160000104e1180000126ae440000040084253b9a117124e567a2301600000688e64000628dcd1b9c0001a88959f22b38f16e700006a2248648a8e3c580000148f0873800045d12b72c5b0a2596a4001238ba5280019e8e89e67a22516ab800067a3800001802c42798003fe1600067a00116f62c4c96c56254000f94828680025b15 else 0x4a47dc8851c948b66678385fc000d4442ed23b800135a900038b2e000fb276ac929000221473c546025b1544b0004952800003c6323c00004cfc448000051bd150006264101600000c9c230dec00000842d480019b974a589e33d1c000b66678380008acd5c8ab52dd4501037b00022b10ab913c67a3989800104058003ee19e8e00055c47f186f6b2200021b2c000d5c8bdf8002239956a5cc00020b72d50db059ce000138460000022078b))) else (if i < 105 then (if i < 103 then 0x1706c0c75800001c5000002548848002871cf0c3ad00042016a520000061d17800400040000001a2195a67383191e87800096e55994000d10cbdfa1e98c8f0000025c80e8840009c231981484d8892b544a9a99022e00036e12000c8a0021d82d698c64780021e98c8f50e0004e11875a0006de2cdec001b0c433039a28f9262700000f0eb4c0006323d380001254a00044aa349000056a0051315000096c5517800000842d480019b97 else (if i < 104 then 0x83b0160e000b4c6323c000028fc448002949c88b37b572000102c60009c23000147cd88947280019e0e0008a837a2af54e3800040000004cdcbaf2b802aa915e58c6555226f7032000200014a4e4058002901b1127380004e1191ca00067839381720000a0004541bd1500000039c32f54e38000417951755548a3cc0c80008000546390160000066783800034cfe4600000198c8f15c738351120000026323c235de0d444b8741b30f9b else 0x733c1c0000067f230001598c64780039c1a8898e548b1940e000acc6323c0002c4d444c72a458830700000d3191e00000a6a22400169830438004541bd152750004e118000a3e6c4489b1c7007480002d33bc074e05c8000280011506f455ce0001384600028f9b11200000039c32f7ae380404169a2780003a258003619473090b4e118a52000a8c1d698000c647ab300019e0e790000564260000026a22584e0d9424dab53d523490)) else (if i < 106 then 0x9077ca646328bd1806a221899ebc00058003b69c78848b00033d1cf6a0008bc25600000f9480003e53231980c0004e1189e6f70ff858000029384639c00022e890000023734600046f23c21a657998cd0800002393886267e2000169ce0006e08a2216a4000b9c5c061f29062667a29a1600123c002216e58b5ff0b3130001c80b5ba5cc000204c00006a2256e5dedb60b0000121b22000081900210000ae47222d92c920e48700000c9c80b else (if i < 107 then 0x46400041454000008678389adc08d4448003132868b55c00033d1d0cb13c000216cdf70d44480000798c8f0000073f112c4c0008202db2c000fb888003ee19e8e00055c3f9186f6b2200021efc00111cca32134a0a2a7380004e118c4c00081e2cdec00000c40000009f7115b924e76e2cb724a0edc596e973008c80000091f71100000941454f6a00000e258980000085a800002708c5b92467fc2c00000471e21600000f948253a9f93592 else 0x50e0004e118cd800078ed80010f4c6479bd800358083ad0b236f16c4e00000c1e2a00012d8aad300018c8f4e000049528000b9000225ed51755548917c601a88844b0004952800003296c5400005138460000061ab910000053191e000c4c8202cded394000400039c1a8890005b333c1c17a94a66e5c0018994345c32a72800086b00003c86c001026786d400002ccf0739c3811a88900062650d170ca53a00021ac0000f21b0004099e1b5))))) else (if i < 119 then (if i < 113 then (if i < 110 then (if i < 109 then 0x57634332a44886b462529c000c9491bdad30000f0005294db16000ef08862513909de4c72d18001a8094430008190c000a527202d3c8001200b22700019e0e5b322549528000164694700000581b031d60000071400000752212000a1c73c30eb40010805a9480005b0745e0b30001000016468864001290cf072fc32f2b1930b40005c80ead40006a6411e4a8400041d68001c80b00085b54026b4cf206323c9b8000db8485932280007 else 0x8213c76c0000046a22129d56000091b0a3ca908700000634432000002cca1d6e94a40145c8a8002930c5c44a40001c86c000b784958d2840189800000b5a875575213612522a000ade3148400001492b1a508001336a4a40001c000a9ed7299540000f0daa253229b7145c44a45bc1c4580006e81c00123d14042b4800234904a40003921c6f6c480003d138000e445b6f0003b5093f250934936000804c281c001364020400023c80106) else (if i < 111 then 0x744212ef00010cc2d2d11e00009a5c2a0ad09500055c30e1800000488425de00024185b8e3d19db9071c6e53b7209b10326683500938000052251ba8000665800054a1c000004668363114a400059acae59870c35900030e19188a52b962c000a6cc84500011e9ad9e0001ba3a91a00004e06e10000078c1832b48001a990000522007120008410d62c001139b947000475bac880004790010e94ea426c24a0b0000e786332b5a9a219 else (if i < 112 then 0x66000030e18d92e1705ca0000030c7480000009dab261500c35c3c0000166b8780010d9bec93300001870c76700039a5a00120cb602d7940023308c3c33f0001800071240b52f16b4a0003d621668d20dab50001ae1e0000003b5651cf20cb602d1e400001868003179a9904436e500012aec00068665ecc000c3862a92950000b4a74365b7247e60007506d66a41a278580000699d880004d83341a00086c64a48000014d0cc8002ae1870c else 0x61400035c3c000a520062c00172cc3862a532c0000e71c4543b720000c0ed862152996241874622948028b40100000414a94cb0000380010d8d8890002ae1870c62f4543b72118acb0a94380000ecbe838002702220a65854a0001c7240000521800007ccec42bb0001a1990004d84041a8860000182400230d6c058003729a9900008e735c3c0008beb4255854000ed9900021b2db9252e00000322bae00061c31d44001c58bbcca73b3aa2))) else (if i < 116 then (if i < 114 then 0x63300085442000b5291a5c002338ea8e3bb2dc3529d56a00035c3caec00068665e8d0d8000947d37d9dab200000931d20aec000686651e4000ea46a5321b000126fb0003b56400112a7547121000000889bd8003b48f8cc90640f166f723ced23d1e58bcea46800322805060005763433200000861c31008000d6452a532c0000e00043636224b7694cd8620001ecdb0c4000294b038b00055c5bb1c804a9518828000024cd06a008000038a else (if i < 115 then 0x8dc43636324c5e00076e4136000000443d3ad6b828b4f30003332ce450a28a43dcc0001570322180000589576000343320011860082dbfd6e0000e8000029a7880004d83a91b1ce4c46b878000009038400026c1d48d52b5a95422e8f200075235b958bcd4c800000a1a8080004d83a91a00001c63a415d8000d0cc80021b007925e571d00023198a540002c00103c0087a5b0001bd157e261c0064696c000b425561c000d20dbf130e00023 else 0x57634332d980000042c0010d93bc92dda5346e085bb59100010b60000752352dc001684ab2f23c2a0137cb5763433288400000a255d8000d0cc800352001080004d83a91a4d0a540442d3cdaa201cb0000031a8080004d83a91aaec00068664000008c74800029548c0b84b5e58cc22cc086c062495d9a90d0cc800002221096cc00090616a54000668353616b40004352adc1a79d0000043341a000a5520c2c0013600044295a52a4717)) else (if i < 117 then 0x4f30003332cf4f0a520c2c00006cea8e0000028088600044202312000aec68665b3006c0005addac8800085b001e3a91a88400000c252d8001684ab7f8000019d45f6e700010000f98752356e14a9c145a2f8209a788000003350100009b0752355d8000d0cc81081098e905767b33433200000688425b300024185a9500019a0d6a55b888c3a046000668358bc000edc826c000000884a6436363249e719466658000028060300022100409 else (if i < 118 then 0x8e752a0001696c000b42559810d96dc900c800221098e700090616a54000668353620600004279c291999600000a3a91a0009b000e216ec0000143221000001098e752a0001696c8beb42540015a8c748473a9548c0b8e752a906171cea540002d6c1c16418326c000002884a6436000240000046c6180011080c44c73a77ac88b89562f353200000086a024001108008325b8002d0958dc43655724ef0d9920c2d10814c00033178001db90 else 0x55c30e18000b9e66659b244120b940003729db9071c55c30e1894c86c00048e48000d8c323c8000028d44308900012000c5e63a400014a96dc5b7d8001dab204755230e187e60007506c000004c3862cd2a944f0b55290689e16a94cb0000380001ccc38600001728e9e0000133aa3800000601a1800110814448002bb1a1998e76cc02e16884000004252d8001684aa2f83a8290800056a31d2000006c6a0215d8000d0cc80026c1d48d)))) else (if i < 124 then (if i < 121 then (if i < 120 then 0x576000343320009b08083510c0000384800461ad80b0008e735c3c0008beb4254001b94d4c830a8001db320004365b724a5c0000044575c000c3863e3ba8bc61700075178c2ecc000061c300016e0004ebc5ae507f0f5b95cf6f82c0001fa63a403c4000ed5900007e9ae1e0004366fb24cc000061c31d9c000e6968004832d80b5e50f48cc220009b0668340010d8c9490840001a19900000644312970000b42552140010d183bc0004830b else 0x1233b100011ca004180015d8d0ccae23981870c0004d93341af2600088624001f2cd0cc8000039ae1e00055732524b8800061c3000113801c5a002dc0001d0007a354c200011848c4f1c899a52c87c73a270000b00055732524b8800061c321ade8d5308253000004128e50080000c0009c8d8c2dde000110c49bd8000018f0007cb34332000aa461c31365d1ccd06c4ebe59a1998e50003630cbe2ab861c30000098cec41c900000c86) else (if i < 122 then 0x37b0003481e000a5281e2e2cd0a800088002252341400056950b20000aea8e0261f9d052250a3c8002018d00000334432000f6661c300014a639c5a792e7c68160005298e7169e40011a058dec000f387800225234147b300030e18000c22a98421f9d053e5080000099d884f254e4802c94e0006c248001528e48727900024016000529391166f600079c3c0019151a0a39bb089a99000011140c280001ea5f41c00014911050002a500f0e else (if i < 123 then 0x54a5bb1cf26f9600024001844d488006ae21870c00054a4361c00002067620001710c3860000012018d00061435c3c9d6ac66d44c0014a581c580022524a140004540062000000468865e4c001f2c4a2ab7242a977937cb00012e3a0008e0457e97993e50a1d27b8001537a0003ce1e9e512910e58000040f14f0002ec9b5134790004031a000002688653adeccc3862758001870c0000023603eae8a520002cded03cf3879f9a850001b else 0x77358845636a9494ab7638001cc1250a2a52f88000e442000002120011686a640005ef5b0c40000009a8086274d83a91a00029063a41f2decd120c8002011828a0000463060c00002c6c24800129ccec40000041a21900000630e18000008806340014a581c580030a1ae1e4eb563000266d4a94b7639d1d4a581c5ae22a52dd8e0000054031a000c286b8780014a581c58003301870c00054a5bb1ce3c01675cbc0014a581c580022524a14))) else (if i < 127 then (if i < 125 then 0x6856987b52a0008466a640001cc1250a253c680001237b0007691e0009088e245a15a62178aa790000011600073049428884d52a0c2529e34400090002422389100073040d289510dc7a4e000004cc1830003139d48d00000135c3d1cea54b602c001c4514040002952d80b00000c4bc2eef0884000253c800201cb00022524a1454a0005bb1cc4400075cbdf68000c748316c0a800110005144b01ebdca6e000b19c207c0011b790001a219 else (if i < 126 then 0x9b2fb080000925f41c000f7cc3860000151828a0000103060c000002676220b189d01068000031e29e0007b3344329e4b9e00059cdd08c000800022118e8900044a49428ef10ccb222dc4589c00068003d99a2194f25ce0002c00088400425de00016445c3322524a1473742331d20000a947243a394000cec423c8000078d00052a391160011ce892793c8000018b00039824a144426a900012000ad263a40dec001da478002f2a3811 else 0x8c400040e1694918b20c3936606400042a50002520e5a69254271f1880009b62d4a800100c6ad7800003064a40000031c75800092850001a18cc0aa6c421c21880006863302a9ef087086215c800000c42a50002520e5a60003191f086d0c66055698000c647c92b7a1868c00034231a0862a00060c18001008c14520c000228080000043921c000bbc6605536000100c6a6b800181098c452a391171880007222e2794a900c68000f917183)) else (if i < 128 then 0x49f4c800026bb09e400059971504cc0aa522388000e4965bc00024884000766263ad8bcf94826cb888000800040e30d18b5e000ae419108000ecc4a524628000e38e0010002292cb780004927d3215009c62473a6d8b402000014089c000081850000024c346376000243204720008982e000002a021952929231472524628000e48f00000111188aa4c0e2d108000ecc4c3e373b5d1d5fd0004031ab5e0000081923c00000442a9000b038b else (if i < 129 then 0x5634a085b2696e00000224fc9422190d8003811868c56349f00026000f666886630d9c40005ab48001f29044a85b36e28948a9472438000008ea46800473a6d8b48b54a44e1c000a549b62c000eb400c322500024a1448b4a40001d216bfa61a3122d528e48700000e1ad9e40200001a089c00008185231239c0005800007a018d0004d9001108f291ec0e1981c0015c830002071868c38e000006228840007662529231400072318003592a else 0x44a00049428cb0948000380015d8d10c80000199d8845e0005a31288400061a31de14a936c58003d99868c4e452a4db16050a547222c00100807c200000e983060004a40081c00105065e555a4000ee480000021868c90c69000050000fb497ebe41127c0009a2542da4a146e65c433b1000000267620fcd422190d8003889d48d00000832f2aad200077041b95f7000048000009868c56349f00b26f6600068864001422190da250001b714)))))) else (if i < 152 then (if i < 141 then (if i < 135 then (if i < 132 then (if i < 131 then 0x6ae00066f52aaa0007547165c001219000000221ab25cf0004232c000a10e786e405ba400119f58029d48d5cf0004232c000a10e786e405ba400119f58001d48d66700091b250880009faf17e9d0600d08000079d48d00000433b108f200000418eb0001250a2522a52dd8e03d572391160009b000839d6529000032458001c88b5cb00030d189c0cb092850000004e4832b1aed250133ad0004db1675800092851b3168d72048002d780486 else 0x56200043564b9edfc000580018a9e6dc3fd0002432052f6aa41656f6600068865128000db8a00025042d935630003a91a000a540042d88d3b0000c4472b9b771f40f4c50001eac400086ac988d3b0000c2978001cb2b88e8bf6ee3e96e0a000024001c08c34600024f802135630003a91a8940006dc5242d4a80005a97abca0b2b47200048c2e000f666886630d9c40005a250001b71400085b3e520d1a00084469f1d9700008a0800044e8f) else (if i < 133 then 0x4a05f826c469d916e60001422190d8001f900b0900000a34432dca000752340010800085a3900025e175ad8763aa388940006de5000128216c98003d99868c4720004bd2ee6a0007547104182e2747bd98001868c6e50003a91a0008400022d1c9e312f0ba250001b79440f4c50001e000940bf04d1c80012f4bb9a8001d51c6234ec00030f8ecfebae44000028c34600024f836130007b334433186ce20002d128000db8a2b18001d48d else (if i < 134 then 0x420001171d612277240000004ee482250049b79444a85b36f2812000067620000128cbca80000d1dc1044a00049428000a110c86c000fc80144c75a100000b00000134432820c16ed43decc000c346207b05bb50f8eb6710001600001868864001eccc34600024f800935cf6fe4232cb2e00090c811c8001018baeb0002111a7c78880002282000113a3d99c000004948f8291d48d91f0003a91afd7236cdca5ecc000c346207c4e8000f else 0x774343330aaa530ca2d29d6f4d88922aa392d4970000ce321140001486b6780010082202000060983060004a401c1c00105065e540021c92fd78000541868c00000233b108f200075234fcd426190d80024f806935630003a91a00000c77241128001250a475a950000b00044200212000f66688651c9b912f4bbe5bd99a21944a00049429216a540002c001655d293a082f90000f89d7b334432000b2af849c001eccd10c8002213e589))) else (if i < 138 then (if i < 136 then 0x4724072e0000046c44947c000f3c7b34294b630b63000036440000ad4b9840da9d658bc70000041d48d00052900516b5e000b96192d8000cbca8004541ae1e443000915129ee9b202a2239c000d70f286c541979500000a32f2a00096c00e192dd10c0004b0a0001e31e4d9000002108aa8e40005d2f14a543458002412070b4554724bc2e91f0320002172d4a50385a6c800003884554720002e00000903218001129254a2530001b112 else (if i < 137 then 0x4a7000362246f6d5f2503db0d129254a247c0c800084b70004421200000466659aa1380000a34c428b428f6140005b93c93f1ee0004c0011c901cb8000011b11251f0003cf1ecd0a52a1a2d8c0000d91034c0001e78f72d0003d372d0a9c0000500014a543459b53aca798e61400076c3c000e9e00c19489108000480022524a944d90006c31094c0006c4496a51c8000ba5e294c328b48f819000100000028842527d1dd5009a4fc7b80013 else 0x4790004031a000c2878a791551c8000ba75a500001384348c3302a000a527222c00001914040000012d1895c40003921d0868be66054fc4000f387ad78002018d5c46243921cb5e000806340018517f4f38aa79000164dc6ca3804c8040006ec280000d0c3460000039d48d5af0000050c96c00065e54001d3cd70f0002de9b1124f74a700010a3eb92e683d23d366064400000c197950004b60060c96e8840002536400000c430a0001e31e)) else (if i < 139 then 0x831930600005e5f610000048c3460002011828a00000a3060ca420006c249ff13c8000b000240a6d8b0004426711300e000b46211e400100c680030a1e29e52b4720002e00089492a5233d7c5e4c70002949c88b7154f20002c000cc26c2491080019c449f88001e70f8075a34501000080460a28000038c1832908001b0920004f26612c000a529b62c0014899c4480000224b886600004031a8aa8e40005c0012f0f18f004a2524a94 else (if i < 140 then 0x5a63191e6f6ae40002168c000d4048000009b11238e45d8b222a3e00061a313ac00127c99c722e8001154a4707191c00068463410c54000c18320c0000078800000a30212948000726380014ccc1450004621c88b00057a3302af6a0008e04400164d6bc68003659ae1e00062457b1e00098a61a315fd6e932882520001c98e0006b8305140011887222cfc58915ec78000011810945000030514948a6672639290000e4c722835c1828a else 0x56654a3921c000cf461a311c96a586cb80000680b040000013060c894c8a928515280023147472800003084e452900016aae0006c2495a4000f94800022a1868c0009156b812bfce231a234001258d8493730001868c55252940e167be00061a31380001030a22a80044c1749f0003de26000a529902d6a55480004000485a808642000035012a9494b18a380014a536c58001d68020644a00049428a9518a00038001cdd1a482272d7a9a8d)))) else (if i < 146 then (if i < 143 then (if i < 142 then 0x4f74b632f2a00096c65e562a16bcea46800294c738b3df00030d1893e0007bc4c0023dccec40002fe9d48d0008433302a0008f20021908117e3004a3c22f8000956a45431d20000a529b62c000028d28e0001d68018644a00049428000f4e7523596152913870002b919d8800067a30d180008bcb4624000004cd468002a51c90e4725a93372e000b5a67620000eb400c322500024a140001943a91b0870ca66054000008d9101bd80018c8f else 0x49f0003de2600000467621ad4000d0ccafc294a640b0004f28072ccaca529902c0014a536c5a3900025e175a900033b1000075aae418001295390722532c24a140008c48e7168e40009785c00001402020000009830654a4a50341c94a00118a3a39539000043732a91868c3df00030d18b52aa40002127e3dcf7898001d68010654a4a50001c89408892851528001294716aab9472880000263211400000a01e10098000c18300000099d88) else (if i < 144 then 0x2b3211400000c04810188000c18301e00019d8847200048e2e00096c65e5555c000d849252aa51c90e00001640c288940000041800123ccec423cad79d48d00000a33b10000a52e0a2d298000c9491bd8000030f0000023a91a7be00061a311554052f0bb5a8001a1993f30005883690af82868c0f3d4052f0bab92948000b0007113a91a8200000023dad6274d0cc800213c830e6b5000343327be00061a310a1320da899ef8001868c else (if i < 145 then 0x48f000006106f60000083c002064cd06a538001b19200052a6c616ef0b22dbc24fcdc38d20dc0c80019a0d0004725a92f1ec00075470000004d404a5023b9ef130007590041c0010ed20c2d280000da898002fb9a1998e76b576c3cc5e00000241ded3cccccb0002700011464400086436d509e66665800001d474f0000011b1928c7000343331cf0ecd8c2d47c0000047800ad2aaa914280003de26b129e6666592823dcf78980001e1ad9e else 0x5f734332e5eaf282cad0800014345b5ac619a19964400034836000e1d24a210816694345b9134c0000f0000013341a91e0390322123e06400042140001ef1347700035012e0484e000398bd148ee080000050080600044a00828a44000b902517c00000c42532908001242000059116950eea7a4e00011c96a4b800305c928f8dc51f55724b5e92a752353dc00000c4253ade800123f3000864366f6d30e1c3c0011c96a4bc442f2be391))) else (if i < 149 then (if i < 147 then 0x5f175933c1c000ff86665800123c014441600019a0d00045f867120008ee7bc4cfc40010a07bbc25a2080b82c0003341a000eb2678380014a8e405bbc0001a8094006a534f3a00004265e540012d80603000225014944b70005c812b5e0007523400182c044780028f8029200037b8dc1000000468664001ad4f14f210004a868b4208c350d1600001078c7908000143458001bdaab880004725422e0000027fc9991166915cd8002b19ef13 else (if i < 148 then 0x48f00410000aae64a480014a94345bbc000338894006a57cc3a000a547202dde0000d404b813ac99e0e0000060180ca4400000825080000e4458004619a19945f5520001124ac16dbc3e19c040d4042d78000068d4f700e000100000086a0240011dcf7899f880036f0f00052a39016be2cbc678380014a8e4058002f2aeb910005bd4842400109668664001ad5db0f2e480039a0f7155b97b12c80800000420fcc000ea0db5123924697 else 0x52a4041b080d6a688654a8000ea4680022524a940006b5344320009e4d9c5a3e54853bc92d1a911a80973064580f280007be61a30000108d64500000e197950000060110c0000027222d4890819c44c162950000d40455200010a440006a025ce1315b787ad78000020d00052a50d16a5cbca0004400175d9c44b4523b9ef13404000002107e60007506cdedabdc3878000121c80b00002335012be2af467838001ff0cccb41600019a0d)) else (if i < 150 then 0x1a3c63c00002060a280014880144800001ad1887780004db16000a5480835711139b3073512392a1175a30003501000093ed364c001cdcc74833880026d8b00044a6f928000a54002361997dcd10c9bda628000f3f300034836ae2b5098c7639c00136c5a950001d48d0005d544f6e0008400062400000514042e235c3660e0014e46cc1cb460006a02158d27da6c980023925e970006a200a10000a44b4625de000136c58000011828a else (if i < 151 then 0x6710004db16000940d364e30d7dcd10c800003227b700002245010000be2724380011c8008b8000d0ad1895af7934041ac360067222c000004e445c94a3930d9700000145010b5ea54808351e54a806068000061830600000a44f6eb5e0007523400000914040002912d1890044725422e000e2278a7800148800c4bbc00026d8b0004e46cc1d08696e6605558d281a6c9ad7aea9d48d0004b63302a0010dc8b0e210d2a210c400001418306 else 0x47071900022f2200066e5d305bf0001436580026f1e8b368843624e4487a0003c000014c084a4c4358000b6de000402147c600072e61848000caca3c8c0299b970007bd40214722a551882c000a00c0028000c8186070000ee178060000ae5f6100000b0c34600000d9828a00000e3060c000a44010240000c168c43bc00026d8b00052a4041a0000066b878001139b3074200001a21984357a3302b0870fe6605568c000d40400039b98e90))))) else (if i < 163 then (if i < 157 then (if i < 154 then (if i < 153 then 0x6de7691eb4b198000450a5e41a0c99dba578000e42300058a2ce55198c5a457d23300008800257b8c8e7377bd3b720b3a0006e288f9800002083dea578000e72a00000422000008cba4c001b790a0780042d995944cc69857a2a852000cbc4de41b79da47ab48001e31e3b74af0001cc2400065651c700011fc640480032f1387c7ec80d3a00095e72638000028d4c837a8001f30b52a000402140010d6604258910f400079f18001cb98 else 0x72243d0001e000002604250f2300cbcabaca581c98e0000013121088097472e610600000c831ba8002010a4d20003973090c00000880001780c0848020001e31e6f500000816b70fd914474000020c0848000009e31e7378b456920dea0000062c001a213bc9000257a098e73786b3b7207cd16800040edd2bd04c737a8000088b59100000d1800000a89451cdc00000c800036f3b48f6244af0001cb4b198e3244edd2bdc24739b80000190) else (if i < 155 then 0x4d2000397307cc00076e422d1ef4c0848002579c98e62443d0001e7cc0006a640001ef4c08480029599b973e37913973000003460214dd8001008526c800189080000103e7440000040241800110cc084807ba599b974430003021290cbc000080001bd4f2c5a6900024e980006223ae5ea7e0009de480021c8cbca8002662251466574700032000b751fa4000122d04c731236f0000f4c075b54350000b3a0041800110cc084bbc37ab038b else (if i < 156 then 0x7594af0001c8260006042543938560c60002579c90e57b43d0001e7220011882db78000c084c358001a99043c00057a2aca4b526705d060dd400030002579c90e3910008c4160000046a6400021acc084af0b4421b1286b00030212878000af455c0938560c6000003989086520003382e000a566042400106000433aca57a098e57b43d0001e00095e72638f8d2e8e5cc37aa950000b4180000060c90d07600081254000caca000257a270e else 0x5c16223ae5eeb31ca7263800002cc484221a0c0000659d0003e7440009b262234000008ea4500025799e8e391482004160009040042c0016e0d34ea203f61cb980004af3931c7cd1d66a641364000c446a0c000005063750004441400097472e61bd54a40005a5d800195944c100000450ad000078c795edb7800078002139ca0e3e66123b720af6dbceb63e3952bce4c70000169888d35d0003010a00002a7522800002cc4840001ba80186))) else (if i < 160 then (if i < 158 then 0x4af3941c9b00006242106110e394300000f1808535d0003111a6ec000aa8280014a4f2c58000069890848f0000010c9e2abb218a000000ce4c73ee0001979544000049d30ebb08100064000000cbcaa2000024e987ec00034d3ad5a0009603dd75e2c000ca0e000192926a567a82c1800001201618000008f9d10003111d7af5c14ba49d30a1c000b963158c00000c980025d24e9857b00040f1edff00469a75a552e9274c00025d24e98 else (if i < 159 then 0x1371440340020301806400167433f9b460001a3e68b4422206ec000aa828000030c48424780000286778529000167cd00a00040000004caca2beb462559a70a55d90c507c600093a6129c000c9490002948010b7ec00034d3ae44dbcae23cf9a0162d080002410020b0007780020ce960007ce8a301898cbca9f1a5d24e9800000237144e96008000195edb7822078000012ce863e673700020b24a1d05830f9a01400083f9b462111a else 0x39152906c167c600072e600014a41a85a38000491110008a035320c48dbcf083c0000e4c04280000e99b97376000554140000246242123c00000c33bc2948000b00001f32b28afad18ef268f8c001274c253800192920000073931c000a520062c0019ea0b0628fb6f0000f75d78b77432000fb865e54f98000ee0843c3091959400048b00216000cf505831fb1a94d34eb9136f2580f00048200316000ef00321800143972c63f9b461cf9a)) else (if i < 161 then 0x39148f000147520007d234d6538803462d380020c080006f532c16b229c40003003dc89bc078002ee804860004184ba10ec20006582e31123c00051d48001f48d49500044b286b29c400032278000e4c7224423800196876763e844b4e00083020001bd4cb05ac8a710000c55f00037e4a000e450703c001ce10106bc944f1fd0e00008232d0e0000926042400002cc4469ae800180850004af3941c0009b062421d6506000030000009d48a else (if i < 162 then 0x7380004271e96c0009f0540013410acdb9bc75c2b9035800000b18b8800062639cdc001c7082074830000b3c10000012cd510e6656510a613400098003e5ae7990005f832b2892f0de00049a1c000dc51304aca2572e0000013131ce6f0f476e41ce000109c78002c88018b0004d042b36000e78894518463ae15c83438001b8a20007cb78b32000a4e6565184400203081e0b541bf9600000a40952000bba00a180010612e840003b09960b else 0x35955200018eb2f5c7f43800000d06032008002478a0004793851ab069c3058310080000445000439a25140000013131d0aec2276e4125400100c6b08800002108eb906000169cb0f400045de9aa0000b2ee2709bf8c0004e15dc18ad400078c79466288000e9a6c060000b4a300000222000b36c406d0cdca14491a14b4532f9372a9220002275200080634000024ea8e1ac0000010c40e0005ad16b8920c62638048000c4c70002c8ad68b)))) else (if i < 168 then (if i < 165 then (if i < 164 then 0x39000000414b8e00069a75720001128a1fa2cd0001b38f45d42b2271e8ba00044d6103800061fa2682159b00000232b28a30b9000028f01aa1200b1fa0000029b5c800000114b369c200430f00001200b1acaf88000c4e545d8f0229ca8ba856452e800003c4000000a018d4020103a91483000000a18001b0d128a2010000010a6e64e1000190aeb98bb841cdd73215c80002e61a99040285700014dc200075471915b0c000a00037a9958b else 0x3a90004031a83000000219c4dbd40dc58002e61a9906116c300028e26dea6562d23c0010603389c830000b4e545d0002275200080635cde2d215c80002ee8020677800032c1600083091e20ea4000cd46c5a435c2b905a700041810000dea6582cd6538800061d48002020d5ec6cc4de3c0000380cc1d1792e800040000009898e4d78e54180c00000a8301a4194a400058000012478a71945d00022884dccb223110938564460002948040b) else (if i < 166 then 0x232b288849c2000312551e406c69fa39e0001b611000620208849c200031148000d2479d423c8000d5895d837f2cb8400097421061774000300037a9960b5010005702e0009c20023215d150d4c82958002020d6fa6cc4de3c00001a0321c0012e801041d48001f48d0004185a70d20ca520002cd660b172c624780020c063595f1000187800006fe5a1494a40005800354195940005ad3aa387528f2000353954157d08a2f00000308 else (if i < 167 then 0x437144000c9269c756c40012b972f1345000138685fa64242a5a0011b84926c0011b51abc000289a77e768a00026b6200095cb8000009375abbf8002b1325518a9683408a4b920003c001924d38e80048c9caaa0006af7bc2a000b5b07271b4e2a5a0d028cb249a71d00082c3351acfe9ca000459dc000ea0d8000011959400000035c3d0d0bf52408584400164882c4bbd1bf960005290031688481c00031400000e555293423be599 else 0x71352a44e16e260009c82d1c117400088004359db90402857737140000066582dde177400032d380020c087927594041a8de00000a46311ae000050002a30010600041848f11168afe76e4169dbd506040004359db9047b6b800015168a8ce6e194cc0000f8500035c01a875c24ba0001000004c8301a4194a40005b732708000c52400001b3ea16000b24400015c16a4b80041619a8d67f4e500022a140007506c000050caca0002beab39a))) else (if i < 171 then (if i < 169 then 0x4bb00044b28dcc9c200030000010c4c70002bd8008f49f00365e26a2ab4a00045da61e8edc80002bd8008f52a7385361aa2ab4a00045ffc000d24dbb48002ee1049f68a00026a54f20ac634000218c0848000112098e0000070140e000a520082c00135dde03472a0c0000839000048f14dcc81cb96300012e93904472a0c2d38645e00000410f2400080635060001d643389b7a8000b47045d7c022000006830180011e4cd46a008001d48a else (if i < 170 then 0x5dd0010c23c8300642169c00106042c8a710000c0007226f01e000e708083571c000d34e9e780030d9700089e3fa1ca660007522800114cd4c82e4007a25947615460410c00001c6582dd8577400032d380020c085914e200018abe0006fc94001c8a0e0780039c2020d3cf00061b2ece60011b6ed71c000d34e80044f1fd0e5330003a914b900008965000114cd4c8293be5b81990005460310c0008300022231123c40854620002478a else 0x5b572a00022782c5b00e5a17dca800089ac0000078c40e0000011685309a22e4d390000c4c7214c268001373700065f2078200000a5914800109c7a6d0002943e7960006a53ad50000656517e1f2de2cca290002138f4da0003fb7cf2c000d4a75cb1f2d73ccb89ac88000b4e40003131cd7e00084e3dc500014a1f3438001b8a23c100037f2cd500006565149df2de2ccad380020c087136f500016c8ad866565000003902548000061960b)) else (if i < 172 then 0x4950005c828000c9cdec49640000fc12435aa60001052300088e3eb6b0be00044f05df63ccb20c000002085526f400016e6eb98000416d5ca800089e0b16b6c1640e0005ad16b6ae540004525d6f5bd892d380020c085526f402c160009f0004180010611e44305abdbeb0f5a700041810e26deaaa42c000010090300020c23c884950005c82912a000dc242269d921b5c20c000003087136f5000166b2000aa430001b0ccaca25b43280015 else (if i < 173 then 0x6c30011091e830b4e180000050603373270ac88c4e40003131c9cae54000450a5a280009afc3e580019000728512460000026e28a0f5f7cf1db2b80002d49774b0004031ad7ef1684e3cea400100c68000131d51c4b700000b2a0000020101a1fd0611e443dab9500011418000003106b0000dcc31549bd00005c32b61995947130005ad166b0286b223169c0010604370ae61a99035900001418000012022180010611e443898002c88b else 0x57b5431ea9600080835b99385ce06472c831ca0e4e40003131c26a0008301939517400089fa0002159b59b5f18f01880400004829c4c0000145a950002018d0146f5000108f2000830180013856446435aee4061000000f32b28b90000c8a19060000014424a8002018d6e64e100018000b98bb840001844fe87238b8ebe0114e40003131c92a0008063584400000c82290002138f7140005287ce58f96f1664001385770624fa7632f93)))))))) else (if i < 261 then (if i < 217 then (if i < 195 then (if i < 184 then (if i < 179 then (if i < 176 then (if i < 175 then 0x529015168bc0000162106000001034620002a98a5c700034d3a97600089451705ea0ebd7c620002a98a5914e1000191ca00072839190000e55525d8002701450157061a2e00000483018e4000123c52212072e58c8e50003131c7200002a62971c000d34e8a7a070000c38f45d000227e8b348566d178000034420c000005864bb00032b28b90000aa628001175c748a60800002285c700034e3ab120009005939800144d3b013daada95 else 0x41855300010000d507c8521494a45645a0c000003884025c20001475200080635cdd73000083bc37a8000b35900055218000d8665650eddc7104c70000059898e47045d00022ef00009c82c0021acedc820100039b8a0004e1005188529d80004dd24001198b0003541f2144950004031aafac58ace69e11891da47a0135c0000a778906000169ca8ba0004400000ccaca308c5a0001035871c0001875301880634f05aa1198b00001484f07) else (if i < 177 then 0x52a0003351aa4f080e066400106123c41d480019a8d00045e0040e6b305800030f00000dfcb3eb39c0000f8525295cb16ef00006582d82e32c0007c5a435bb4900000165dd0e9ae000728394cc00003c520c2e1000084424e1000180000167c8512551e400068000039bf9651900034e3a00000678c780014a400c5a800001caaa49b7103ea46d98a520002d49592458cf8002948b10b3f459a6d536b12d506fe58d657c400061e00001bf96 else (if i < 178 then 0x4e500122cc002ef1a4800001cd70f330000440920005705a92e9360008da8df380016488000345000935787e75134ee92ef46fe5998000220490002b82d49700088b34e3abc4bb20004d6c40012b970002be8029a8825c90001f0360006fc94001abe2a0ab0800021d107aa8a968340000bad1505638d7e99090ac48001bf960004e500122b6cae0b525d845de964883bc0001960b6e64e1000189760007c850000004dfcb293b9938199 else 0x3a90003351aef113c6582c00000d23c5000200800873905294e4167211886582db993840006000000b5c075cb5294e4170588f266a354cc0000dc5247a0c000080006b802e0edcc9c20003172d4a40005a920000069f00082c3351aa140007506c00001ccaca0002728009102464934e3aa16000b24400015c16a4b8003249a71d5b10004ae5cbc4d1401e4d624000dfcb2858002c9106b74e577a2200105866a359dc000ea0d80000b99594))) else (if i < 181 then (if i < 180 then 0x49764e0002486c0006263903a4180005a14c268001346b00065f20782472000580021cccaca3438001b8a24ee64442b36cef1de8566c00000d02548002ee924860004184ba1000691e48c2800177494c300020c25d0800048f001149ac01a72438d653880006000001a25940000013aa389ac00072638ea5254fa46a6b1251c98e0001553413000010a60424000144f8c30000071c98e000418005111ca8bc0001c00123c00451c8c621960b else 0x5a56243491eb20f128e690001844edc8000435a358b00040e0011892b13c80635e118912607a4a8002018d611000003211d720c0002d2d00008e09a72c3d345110004e15dc18ad400078c7a39e0300005a4f80032f934e500068a22ceeb36c406dcaa48800089d48002018d00000a3aa386b00000063125d93800092070002d68b4369063131c0000026263a27964539058002c8ad68b4b60004f82ae7000084e3d9dd3410acd9ac0000048c) else (if i < 182 then 0x3a94795f41a974000024210600000203000361a25144950004031aceec880006c001731880820100039b8a0006f546b16000f086923d7299a53bc911e0002018d0005cc3532080400000628001bd51ac580021ea4c0f5914e173818000dea8d62cd65548000639c21ea4c0f0000034180c80200091e280011e4e146a6aa70c160c402000019140010e689450000030c4c7238800003110007194e41600081c006319dd668000d8002ee1db90 else (if i < 183 then 0x45e4ba000100000026263935a3950603000001a0c0690652900016884000b2231b9938523c50002948060b39000000814b90000894500015c16a4bae38001a69d00040e002187e8b340006d1a977188082933c6000196ad1034271e71e8ba00044d61038000625b122a7c154e545d000220000066565146172000051ac2f88000c3c06a837f2cb90000008290a5a280009a3500032f905dc4e1000183fa8f2be834d617c400061e00001bf96 else 0x4892425bf4200001002a1c90d2e8000424780020c063595f100018000a520022cf02148dfcb000018195940005ad3aa389cb24406c4517800001c41d48002018d4180000040ce26dea0002c001b0ccaca235ae60001035971c55218e26deb20c2d23c0010603389c830000b4e545d000220010e6656511ae2d041480002ee9250677800032c1600083091e20ea4000cd46a354358001056a0004493c6b29c40003112211dc0cc80001083507)))) else (if i < 189 then (if i < 186 then (if i < 185 then 0x57d567340000046e288001924d38ead891b2572e52d0008dc249360008da8d5e000144d3ad88002572e2380004dd6a8a4b920003c002464e55511d3249a71d00082c3351acfe9ca000451a800164880000011d41b0005705a92ecc10f68ae480015c16a4ba93423bc6194424e10001800020e894508ed4a40005a4aa3c8000d46a2545dc20b8400097421061774000300037a9960b0004e1001188aa4b2ae05d4040015c0ba958002020d else 0x22157b0001ea2ab4a00045ffc000d24dbb48002ee1052a0006ef1a93ed14f204c000160c0848000042098e0004d62340c000830008223951780003869a478000a46a0003b7208deaff0f4440008a52e8390f294a720b53300003014000d7004e1d7092e8000400001020c0690652900016dcc9c200031490000054fa350002c91000082c3351acfe9ca00045428000ea0d8001289959400068a00226000ae080e5d789924d38e8002b82d497) else (if i < 187 then 0x4d60003931c92a0328965231000123c526aa708000c4bb00044b289ac000626388dd5edbc07ad380020c082146f532c160000146582c001774004326b4831c98e5a700041810b229c40003157c000df9280039141c0f0007384041a79e000c365c002278fe872999091d48a00054624b0c00083000c2231123c00051d48001f48d3594e20001892a00089651358000e4c7224461942198c400048f1497600089651355384000626b0001898e else (if i < 188 then 0x4b787f0002a000c007e09171d7cc000ec4d3b1ac7b885f72a0002283000000a20d60001b9862a937a0000b46b5cc0002076ee3800039845b0ccaca1ac00007e8c49764e0002481c1d40002d0d8000c4c7214c268001346b00065f2078200000459aa0000caca22910a2138f4520004271e9b442c7f6f969c0010604389b7a8000b46b5cc3532000001e812a400177403030078001960b0004180051118891e00028ea4000fa469aca710000c else 0x40090c0008308f221254001680a3898002c88b5900113f04883000000421549bd00005a35ae610e104975bd0002481cdecb5a2d69c00106042a937a0160b0004f82210c0008308f221358000e4c72dac2f800117130005cb167831946fe5800004408c300020c23c884950005a0286b2000002313597c4e4c726b0001c98e3c100037f2ce26000b962d82d5ec0007c358003709057f87a00022cee0006926de68000fa112b800040a97))) else (if i < 192 then (if i < 190 then 0x4e159118a544128063400001ccaca2720001898e46b000003209cae54000450a5a280009a4a9482018d4b400065f269d89c2bb831390000c4c7272b950001142968a00026bf0f96000651ac00197c8000000a018d5706e45a92e8a4f1684e3d69c0010604322b61a70143a90004031a000038754712dc000020a90a00010e067b572a000226b0000006310600b000042070002d68b49764e11b24830dcc00021c4d6456b459ac8000060c else (if i < 191 then 0x4c100021950b8e00069c751c4000e507235000001105dc4e100018a9705880835b9938577062720001898e0fc0004180c9ca8ba000450a400000c9c62b450000a3585f10001878000a6fe5a31400000452e4085995943585f1000187800006fe59aa0000caca4652d69d51c40200001f140000020381923d06047c420c000003887136f500016000d866565125400100c680035da49a97c584000032dcc9c2000317d1c764688b898000010b else 0x6118b4000206b2e3800031afdce109c78000012ee874d60003941cb12d528cc59061b0c000426b0001898e4026b82101400005411e1c0014a40405a2f000004084180000010d188424aa62a31000154c52c8a708000c8e50003941c8c800072aa91a8000d4c825dc3c270140000014180c9ad20c6263a394000c4c71c800008c8a5c700034d3a00081c428313b55c16a4ba2f000005884180002200c9760006565172000154c500022eb8e91)) else (if i < 193 then 0x46a000592203ee9ca00044434000ea0d8001471959466000088124000ae0b525c001a287889b968003403900000035c3c9363bc8da8c000060f90a0000062ee874d60003941c884be2000310612ec000428c0000030a4954790001a0000046fe580014157d089c7a94a728b0005291031671ea0abe844f00000dfcb4292948880b41800000410c26c880006cea000100c6a012e10000a7375cc620209ac00062639009ae000051d48002018d else (if i < 194 then 0x57d00049134ee00009dc48fba35e31888000ea1cc2c000101341300000866042400008cf8c30000009c98e1014181d91000083001421e4c000cd4680022f0018753348f000146b305800030f0084cdfcb3bc0001960b52a48f000148d50d600040d65388000622414e3819953300048f14000d7040a1db9938400062e5a948000b5240000063e8d4000b24400020b0cd468fea728001150a0003a83600051e656503f9a287a8980041619a8d else 0x3594e200018e040007f438fb9e24000880039e2251457d89f4913518800000628d740000006a53800277125ba87b67c206ba000a543627800104c72dd3deb3e1035d0003e91aa5400001c28001b11128a0002d1981093ee00000422b84000682600015fdb14826e000241a657d81e49134b84000682600023193b890002c420e1900000137246afb120922695f4001244d26e40f1ff260005a3302126b29c400030001b11128a00045a2ee10))))) else (if i < 206 then (if i < 200 then (if i < 197 then (if i < 196 then 0x5a3302128de00000245fcdde5244d36226825a9b5a300030212782a9c6fe5800166987cd8000123ff8800000630212000d109dc4a31129c00051aca710000c35d00052a1a94c00089451065429a70fa4d8001b9230000084095318800002e28d7400001468000099a0984a70004ee2513c00082638fba3180008c44ac443a194a791b4ee240000166826231002c00051ae8002950d4b60000022a6b29c400031065428f30f8002e91bc24 else 0x83413000103200a2000000cc08480030b1bf9600052670332f18b5291c5d629858dfcb2d18001810958a54e37f2c00103297421708000c084a3f0001e61f00000240952f8aa4c00065071dd237090002d4a47174a773e3d0246ba000a5434d65388000624a8002259400000a3931cdcc0000022002d68cc084ad1800181094b70000012af60af6d5e3de9c000ea8e000293b029949b000372460009746826167d5eda607b7300000208) else (if i < 198 then 0x3590003df1800000c6042517800168c42dd0002e6100007370010caeefe88e6900010f5da87a8a22ec66110005a300310000002b4e1935d7c4e4c72ee39bac9104790000020cb8800062639771cddc7082e20001898e00043d9251e878d5e0005525d6f572490000192ee868c400001c146ba000b5e3525400112ca3982708000c0000073931d13d0320002168c000c084abd0000011500057b6af1f05ef206d44c0012e8d04c0043c41bc24 else (if i < 199 then 0x35940e00018000dccbba18d74001aac6a4a800225947ef8545fa42a5200005a1cd7400100c6a0100000c0a0004e13df180000046042517800168c440ca21373064420000080c000b46dcc217b0000f14f26c0002098e4860003d6408e2000004440012e8d04c35fabda138f42968a3de26b4eb4600021218000f5503ac8001898e00043d0041ed7e0006826147c001724922d80025c9c49b59f46d46000b346926dcf0001380a28ac7848f11 else 0x834130010e260001c00103800c60003732ee8635d0005af1a92ae608965172c001774325d8002251492557b4271e0000069741c00239400431aeb13ad78d38f45d826226ba000806351e400000433732071ef8c4860003d54000081c7be310f000000ca80021e8008f51e8e786c3cbd91cf0d8780010f40047a8fadeae4920000043de26000002c2c59aa1629380a0002cd9a49b38f8cc62d2271f198d144555000000439aca071ef8c))) else (if i < 203 then (if i < 201 then 0x36a65e4131c0010c66fe58001629128a3128002fd216430003fa1d18ac2c78228000060c4c70002070030c39000035914000dcc00418d740016bc6b13a2100c870060005dd0e6baeb280634000f7c01439c80002aa0a5cb0000010c6ba8f2eb23400149a000c9aebacb138d0000075dd0c6ba000d5634e4172c000525bb130001500057b4981e92a0008965000172547c91e7844a47174bb00044a28720000dcc2a4955ed26079c800000f0a else (if i < 202 then 0x9125a95422e000b74bb8418a9d8c001c20ca859e61f4190003cc3e0009c40123000000cd6451ae8002d78d00082a4101e79ea56c365c0016a5508b8003879d72f4a70003d024000b8268260f3e0cd2607ac54319bf9600000a34130d6000078ed8001a3d1d1220c8001e61f00060061b2e0008ab22431cc4000f59000040e9e8120004a73591479e0008203cd760a96bc6b7d0001e29e6b00003c76c8320007987c0013880086438c7b80013 else 0x5a948e2edcc8aab9630d65389b98624d8001b92300002b40952d6000078ed8000075128a0000081a09835d0000071a00000278a797fda3d1d120002dd391904a60004ef24a2e00000229b916a5508bb153b2009b85af0000011494d2369de492d800000ca9aca710000c7380004981e782d526fe58d65388000639c342a4c0f6fa0003c53cc4a000bf485c6138800063218001fd0e0000024271e79e000c365d801a3d1d123120000008a)) else (if i < 204 then 0x8246663f13e00074068001a3cdc91b5bbae225140006134b536000d88894515f4001244d45c80024c0f42900091f26cd118c9dc49de0001774380021e8008f4860013d54080400000228f8dc4cd04c1aca079ef8c0005a3055108bc0000121c00001569c31ae8001c28d4d70003931c72200000229109384f7c61acaf89ef8c577000473486ba00080635c4d2e8d04c000003ad3860000003931c000000812a4e4400000c51ae8002d78d else (if i < 205 then 0x6016063fa1c000b520182800002504078002298021042979000026a2e000894500022e52d4db5eaf0a77120008b94b536852f200004d3a182400173b33501bba457c000491348330490547cd6138800061e08001bf9641982469c3e6ba0007d23606000005c30003bc001078c400055314b8497468260fb80000348800001a3a2400060051b2e00113e92268f3d5f12607abf0003fa0a5c200034130d70f8000038001384fe860003879d72f else 0x41950b6663e00000a8e89000132400c620c8003331f35d8240001aafc00e6b2290e1e24fe8735000024c0f00068f37246afc00000c280016a5508b80022a8010c62400071c1cbd8ad478a79890000fe8720cb66b331f3c18878522c6ba000a0a35ac0000f1db000006a8d9700045500618000e1e75cbc00000cd6051e78002080f57c00049134a5918c7a04929e318f409000477a5a9b0008c63d024f640009226800129dcf85332a9300019)))) else (if i < 211 then (if i < 208 then (if i < 207 then 0x1044db160000dc6042400013968c400022f009870000015a70c6bac4e66a3631000155050000021a69d77600044a286ba00000234769708d04c2c4aec283160005c2341300003ae7c850d740000146c4f0001ca0e0006cc3c53cbd89c20003118c000e555238359413116140003c53c000d9872839b2d4160988bbc0002d3863ee00001822000afe00e415f800001050002d4aa1170004550011883311cccc7d0644c5998f9aca710000c else 0x447665000328e119909645bd000100c6a38000000116b56655263200002480a10000e8ccb43c6200026d8b64700067112000b46aa62000123cc1832998002dd8e52a0000011a7ff14469e7517c001ec0a9ff8001a79d5785950004ea800000064dc180013ac632b000407168d05d936124d0a0008d051c180015b4632b2c4ba4963a30000040e708000e44180014a55ac5ad3ab9000084e48c53131d1cf1886582cc68000adc20000d198085) else (if i < 209 then 0x4828c4168f20000021a31522d6ec70002a92c18c5808a035722b751886582c000004c446a6c8012e6070000015cc0f188d571ce2d6e94a6310580000c98c0f0000014050879c74665a1ce8c0000b83800294c620b00040f00318708000002197f531500c6a70485a34143840000040cb4eae4000200024555b84a250001b7143fa6cc3131c000008adc2517800164442700001b7145fe0004031a7c6df493a60fe9ae0000700000118988 else (if i < 210 then 0x43d0007220c91eae4000213912bcc4c70002578010e44e0004031ab069c27f4323140000043247ab918988000003313108bc0006a224fa400100c6a62a70c160c47b5ba00020b249c2bb8300014a63103a950002c58d000553003100008bc6a0240011e54883472a57c628e4690000042077c9c20003168c0015b848002c8c8a863fa4af3131cb4600063a24edd2bcc4c71c500023d90000009312107120006a224fa4000c446a6c80000287 else 0x456e128bc000b2221380000db8a37a0002018d489803584427f4d7000038164000c4c437a0002018d470000001229c116a8d05170a129274c1c2037b91063be4e1000180011886582d77551800031fd2f88000e0000053131000000476624001c88c607a25ab69b7140007223181e978b52a845d8500010106a488001a31a7047223181e644000062140000080802000201196873ce5a63191e0000209b62e31000239c3a4c0000018f))) else (if i < 214 then (if i < 212 then 0x6c500034836b34d560002d6c000000c31c48003b50944a00032b28c2284ec5e38e2400110c4ae4000195946117bd8c51c00001880a10000e8ccb439e700018c0f8c40004db16c8e000ce22400168d54c4000247983065330005bb1c8be000f60552f4001234ba9500003c8d3ff00034f3abd898b0f830e8c0000543800294c620b0000123181ea3c81e00030e1000001432d3ab90000800000256e128940006dc50fea314c4c71fd35c1898e else (if i < 213 then 0x710372460009c20043172d774000323ab912d30f3fa4af0001d18abba000194880015b848002d1989883e94790001b1b800064a491d5c856987800294c620752a00058b1a0c6aa6000211a40001a881df2708000c4525a60001eb46000adc2545117419489c500023d90000008312107120006a22554c0001b838002414620b3e90003111a8f20d0000191d40000047a8a4504661152153f325240d2000622340001ad7303a29ad30000f else 0x39152a000169c0b9065650000009014205480018c0f5a63a332d0e7468040001c000004c607a080021960b5dd0007220ca8c0006582d5c800000441d4a952020d3a952a58b1a0000d66b678c880000e828358000118400001a4db1718800001c1d1d41b400078002578028e0000034e4108bc0006a22400123e31431f4a3c9c28d44e7114031b18a0da0001800000cc4c422f0001a88948600036540a42e6864a491ed6e8000828ea70aee0c)) else (if i < 215 then 0x2b54602b0c752000622340013840586000003189083be0000030e8f200000218e25438d4449c8a94b038b5dd0004790cb60a546582ce240000244800287002063be0005dd0e000a52b222d0410f40007a78aaeb482839152a0001677c0006581ce280016e88253b632f0920000025220c000a54cf42cef9de17743ab92950000b3be60732c0e712000adc257f8000c4840002c1b70074430000010cae4a54b602d16c000ea8e253a9080012 else (if i < 216 then 0x3350003501277c000004315011dc00099b526b99e8e8e54d733d1c7200000082cef9b9800062100002b7090004d73131c7f2ca269470eb145ccaca1d48001c28d4797118191000080400a1c0012bccf471df0001fd0c0005c400110dc08bc6a024e400e536c58000061960b3915dd0000c00000a72021488000d44480027148a8c3a94790001a000dbe64a4916dfd8ea8e2912d1800090004e256e1875200080835a4157400142083912628f else 0x57252a32b169c0b90a2e516e94a40005a70000195945176070000c8eaf08ed23ce24000d484800003989083530000040c8f200007e1c0012080045a5e29599c1759d676370449b20008f21ce4520981c59a98000010657252a00016b60b746581ce454a800058002dd196073b700033d1c8b6096754700000580a820001ba9830600001232d0e79c0006323dcdc000d4c80002e6004883a90000031a77c98a000300017f8d4049d628b9b714)))))) else (if i < 239 then (if i < 228 then (if i < 222 then (if i < 219 then (if i < 218 then 0x3e55173532000000269470fe535ccf47020000328887375cc3532075200070a34eb54a40005a3c800303883ac64532b280888040001c000204cb059c8aee8000600000239010a440006a224ea51e412c69d4b0a2020d3a90003111a71400002840000018c48440c800002064790000540e000a5202c2d040001e107aceb3b1f3a24d904e4790e000010b981cef938400061c48002b7094430000040c894000004511fc000cf472b9245ad80b else 0x48a6ab0001600001480428000f7c0186000225195943e60004ca20e4600078c78000004e80d3463f9b6e0979770a69050000002ade251554accdcb9f322a2dd1043c0004b62a7cc000b7441758000e84d0003e836e090008e73c63cbd87be8a831229aad81c580004c9908a32200008d0a0000806b67800004806420001ba9830600000c32d0e79c0006323cef97b00006000002ab7093a90003351a75a8400002ceb0000caca2b680028c08) else (if i < 220 then 0x67500032b28848000b125800139c0184c4f0003d70e00050e47f189c00006b228001468cdcb9f3000265107f368c3a034f5c0011ca38f98000c74800037a23f8c00000a3a0349c00006b229348001274c2abb63000124f000075a508b600075470000008d5c8a8a00018c0f78777478b32b920006303e0dd2662e4d8000029ab915140003181e9c00006b229abc001ec4abec0001da328886723382e0010987d48dc8a174c6079c180000906 else (if i < 221 then 0x6ea8c75f732aaa000ad278000018e84d0000022fb9970c0005cf14fb2000768c8001bd143863af4573191d8c76f450e18dd4000bee65b11265620d800323aec0900050e33218aaed8ccc248f9800004082118002c49600064700212000d1874269381fce148500037a23f8c0000053a0349c00006b229300001d6940120001ab910006723382ef30bad14254000008d5c8a8a00018c0f4e001f35914e440006303e176130fa91a6537a23f8c else 0x52b65a2521400000e78c780015a4d4c82a38003dcb489e7090001ce389c4000300000054745295ad1ab7896e55a356f12000b986a64151c001ee5a44f3848000e4dc8146404c0000a27441ce0d1e400030002450008b7224983181e00005c6e28a278002394700000d195944240000162cbb0c8e00025300001d69422d8002179c5646db000267cc00063a400000195fc880037a2870c0000023a034e320006b22a221d2cce0ba8a00018c0f))) else (if i < 225 then (if i < 223 then 0x6e63df4eb187d200005615a88000ce0bb2900000b870006ab4db168f200001e1800168c01848000011e31e4d271300030a5693a804294ac001008521e00025b1554a48b8281c00000278c7934a129c4cc0000022010a0004e156f180008a86a4410f1778000ac914441ab9143c8c04b62a000b4600624e44001008533d2870000c85251a3322c722000804299e9bd143860002949960b5dd0004790c92889400050000008dc918002d1b3809 else (if i < 224 then 0x5415de2a000a3666e5c0010a54b88c62a38be00e7783cb000160008bebbc555f90a54b889c1800193060000144d90e000c8e6a024001920c9c98002450038b0004983181eaa600118828001768f18f28f0000010c0000093372ed7aaae00e49af555e34490002ed1e31e00067637144000e9666e5c0010a5f1c8aa98000018a5ec0005f518f8c000754717795052d8a9ac8002f60c8ef4d07ff36914000d562d2d0000c9c9a950002010a else 0x6754e032b2870600001018000010d70f0001d4a010a0003df0011892a89501e512296c1bd058001d4a010a49544a00028914b606562d22800181c58001d4a010a6480003de260007be9d631c88000c607b338002e49273400035c3c00113c724396a4000ce0ba430001eaa000050e6db12848bc800059900000e053000270283946a76da8c02a00004e5f820000fa40302a30800193060004d95dd0eaa68c000028001114c9c98000021a809)) else (if i < 226 then 0x48a00c1600075318828001040c607a4aa25000140006470051297800066e5c001890cf4725a0001b49355766700024be29c2dc0312f0000ce0b800270ab78c5148883572292a8946565000122800459c89d4c620a00000d37144000752b6028002278cf472d480019c170004e032b28000c8e00424001385b8062abb63330120004e150e187cc00063a40001c64d5c8b918001ae1e0000003a034a28b4a6303c000ea56c0500044f19e8e else (if i < 227 then 0x6a20003382e9b20000181c000ea500852308000008649444a645287220009b62c001528e4872640001b4930005a3004129d69c2000300017d248888003789c62985254e3322c9d69c2a1c300014a4cb05a308000018649444a00028b60752000289bd68d9c449c89d4ad80a00002c3a20e70600003018000024d70f24aa250001400048a32b1600075318828001040c607800323801890004e16e019180bbc000557c5890cf4748aa70ab78c else 0x68c5f03a1340000ee62034000070bf041ae8000080500000635112000d4466e5d184000c9832218000008754064832726000a526582d6c0ea40345230800193060000016dc0eaa675288828001920c9c98001d4a010a0004b44db160008208503c00122d6ec7238a14b45113830003260c0000060101c00191cd404aa99d48000a54044532726000c9064e4c0010f4c607aed0001ae1e0003a940214a96852d14455194a4cb059ae80000a05)))) else (if i < 233 then (if i < 230 then (if i < 229 then 0x20160a6b27be00030f01b38cc8b1f480019d0840c000008288f28940001a31400152872b800019c973590003fa18000000718a4001bd181c580036e338893c151a6162c000db800e25948000ce4ba3dae6000104793530000c0000046562cd6603c00061db9fd2a50e3596f480c18ce20006562d1ed730d4881c18000030643c0005de2a000002db825178014fa443bc00026d8b0005a33e91090cbc07ac80c98000fa440002d1b6e09 else 0x45343d3181e000b609b62d218000f5502f00003f8893265a30001092c000b6e48e3e31964c8a0100000c0a4600000110a8189c000050fa4000ce842d480019c970006dc007128f2000002193ed730d4c80000009958b3e371349d300009c200231b9115132883722e62ee1065a0003ea468f2000002193ed730d488000270ab78c00045435220a94d70eb238e0c000008321e0000001501d0206dc1264c0007d22000168db704a432f01eaa0) else (if i < 231 then 0x4b60005ea2aa8000064e4d370000e0930002252839400068c7d034000ac875471f196a5234ba568001c1268c40004db160000028c23513a316418725a000193933c10000042d1280006303c00231589071acac88000c466713695306b2b226643000005100c6a011d48000a35d0000090a0008c20081969c000ce84000000aa50e47b5cc3b720782a9c66658c98000ce840002d83038b65900038c528f6b9899640e0c000008327d80026590 else (if i < 232 then 0x7dc8c53131d18b20c62638d4101000044622950000b00050d32f2a66800000418001e28c4c7322a25195948c578a3131c00001067420001178d404ad3800193060000024d71c8c27d200035109710c3c61ba8004628a3a93e90001a8849c261e31a89948ce4b800323bf8890003a25a31070600064c18dd400004051d48002300d4260003674200000c7b6ec0014f936c580024c18c0f00053d71d2296c000000540013857d46321af8a388e else 0x6263cb50d166a080800020cd0000008325b0001979578a8e53131c0009c261e3125948400090003912628f00051b5a92ebbe00065e55e28000c4c73130002868b000002559308e00009ca4525538119ca2380002729178445231d206ba0000123400118400831e0800199965a73e954e1064c7d2000214880000044bbc1e58048b8c50003131c6b20007f431259486370936e000003098c43cb000168bc80800020001434cbca99a00000086))) else (if i < 236 then (if i < 234 then 0x5c249d30000ced00489e48001ae0730b2330001600000133218ab696ce045503d6440005b8e2e1a65105de4b60002a930f4e0002de4dc05ae072280001828a3a93e94601a0000c865a1c0000e811029bb0000108a35d4600001adb800001e25179010000425b8001979533400000b0c0011ca62638000f2d43458002071878c4c56240001e92c00000a490a0000da49c8d800249a90005e063c40ed29f6000410dda81ed922143341b493 else (if i < 235 then 0x85436742000008a746d095538000b2448001990c0005c34ca20f26e38d7039095264000b2448001990c6dd59159a160008f280834001c44d70f24aa25000140003a93051501ea3c00030e45bd0cac580021eaee8700044a46828000d860322000191cd4048000041828a3910000031692aa5400035a15778000ab702c89878c4950000011aa2ab26b4a45a15778000aa8aa82ad2913a90004601a00001469470001a31f40d3320001a79d else 0x4794020000e000a526562da88000ce4bb288001a51c54a4af0001c0000026a641b95de1ef44ab53bc0000962e79149d3097a0006725d948000010380030a2018d0003a93051492889400050e456c0cac58002949960b39100030514752e2280834000070c6078001e72ee8700001445110000c8e6a024000020c145000225470140007f634a3800000467a39b80001710624abc9a628d6e00003f918e3800099441ff153970cb1d48002300d)) else (if i < 237 then 0x4f700a2a0000066a6400010f001c3a38a14800117c76a23392e0011686a2251c50a4000880021e001073914b40001692889465650e452d0cb058000021a8890003e95401ac2600074e6ce452d00005ad8355996070008b4353207229680002c001cdccb03c6fb5119c970000143c53c92889400050000020c1450002579c90e39100032b16000008a521c001730d4c8238800491110004794041b0beaaa694716c14a900c69d48002020d else (if i < 238 then 0x6470007f11291e74400020001698c607a620000008c56b40e8c416f088a8994415ad4a40005a47c0c0000844b00036f2800000a6303d3100000046261b703f8894c30007f112f4e00069472460f9532880001f2a7d900000027651288400124a312b1a68f690bd3c8c1a51c0003840010ead69151882d5ad4a5228580012694c030000741280800000260c18c8d0c0e0c299180001b0500001733a1000095eb7638001280c9c98002a51828a else 0x57245010c8e8bcb46264a0001fc44a7080048a8c0005a66e00e00081f1882c000e8800442feb7a2300d5fd0004041a9c092a6dc510f40000103a010001aa840006274031a988bfa0003130e455fc448000009aa845465294db16a8ca520002d12c000dbca00000128c084c30007f112884b2322a3131000154861cf3701d98937500001b080000088c034000e100043ab5a954620b56b529000169c2bfb05830000e1001c3a130001ed21))))) else (if i < 250 then (if i < 244 then (if i < 241 then (if i < 240 then 0x4426e0552186ea0000a41000000d180681b9c20000756b5290001689692a6de500e8e11850380019100985376000004089c081800051fc4db80004a3d80018f1046955400d0e6aa0005ee1952800001c70002aa0050700046947b200011ca004200011811e46aa5a389ab115a300056a1271c8e06ac4400155000c3800245a6d8b44e4600001a8f2eb2808223114a4c2c580000e17b8600000d3171e0000086aa10001008044380024c26d8b else 0x9280007f112000b4c0041d098000f690c01a4c4620b4426e000018a8ca520002d12c000db8a0002a928c086330003674305892a8c0350f40000303a010001aa840006274031a986000fe22400154c01840002950020b44e0006b81c000978a565d7c0000d14d34d4019b3a15cc3e535420000a54ae42d13a279ae0701c0001aa84546529000168960006de5000000d46042618003f88944259100018c6722c6ce84000f94d5082618001d989) else (if i < 242 then 0x4a0000327260027528c234000ea50106a1daef4541556b52900016f45218920a0000e1023c3b139d48000d3350006dc128f20008082121d3fcec9880001d9ad9e0003220100a6ec00000e11381030000a3f89b7000090003b3867100720005ee180015500043a3da3498e903ad52930b166aa0005ee195280000fc70002aa0210700046947b200711ca00020001181010680029526d8b38e471356220000465ee1800002cc5c781f0001aa84 else (if i < 243 then 0x49436e280007230302d5a91a40008272b8c98f9100039181816b5a000754700011a4c78800024a0001485254e5c32c758818000500010040a43a342d318c8f4e049400028000bbc96c5610e10ccec40001c28038747900033b1091e00000810cd4000d404a99a578000e3ad0006ab16820b4c6323ccd568cd40499700e0000400052930b160007dc6ac45396488cec4000001005040003843740ead67229b62c000e1001438001d100108 else 0x3a2451108bc986b46253893100006000221ab78954641f4db1600064400a140012bce4873f8a998000956900031e200007227ca2d390ecccec400000298b8f0003910011683f250fe2240024a1fc44b23a010000744b5c836f2887a8040001d518e440005a258001b7945c84c37f11200064404a14000ea4060680000880a0400048f33b1000000665c1c0012d8cbca80024a361946ab3918181600096c65e54001528cf4722180000209))) else (if i < 247 then (if i < 245 then 0x7113a90021ad567520003400195150d421e2ef9979500054a33d1c000a110c86cfd0000cec426c9d4a018d0000163171e000a3c01230000019388380020826d8b64791500012b466a000020001770c7480001d4a020d679669361240008d26a841ff1c5570cb00020826d8b0000065460e0008a86a8417315c800042d18002b7890003a94041a00089c67839efdf2d498c8001d1000885f14e433d1c0008d26a8417c5890cf071e700000107 else (if i < 246 then 0x32e093000091cea526162c000e100183ab58004738b39100048a0800074472020000ea51846a1daef000154102dc3181e6e8000218115ad4a400058001d4a308d4b65de6262a00008e5ee180000d8d54200019100c0500001332e0e00079c00e3c00000ccec421e0001979575051e00019050a94b76390f0000cbcaab92080000b6ab3a95df1a000004676210f0000cbcab6f22f25b896de00035012000e6e6a840001250db8a2b90000008b else 0x6c4025460f1ce8040001c1b64a1fc4480019100f050003a901a1a00001601a1000123ccec400025b197958a800032e0e000a9467a3910c00001048001c8c0c0b00049436e28b5a000754724611a41d080001c8c0c0b5da4a132726000802c281ceb1030240a27024a0001400000236f16000bbc96c541de2a239c3800473a948700000133b109c2cf4de830000db8d404a708000010c4550003372eb88a9491638fe952922c70381c280007)) else (if i < 248 then 0x73c8b9349360000ca67620000ea500c68002a519e8e4f782832f2a00002462e3c00104136c58000032a307647000001128bcae40cc2168cd40000403200018e905dc00045418cf292e6c248000e8801040001d4a018d00044e33d1c000ac664e4d0a5395f0088002349aa100003a94031a00089c678380017717c462d182d48a893ce0671170e000644008140012bce4873f8a998000906d391000171ce8046161c0001c8c5c78001c88008b else (if i < 249 then 0x531d2000087a6323c00152936071df0002e20c4a751f00024878db0fb8540010f4c6479df0003fe0c56951e4493cf56a20774cc000380c1050000309ad9e0000362f70c0000566aa10000c880582800008997070003ce0051e000006676210f0000cbca8002084738b8284e45bb1cae48211ce2c000008cec421e000197958284275bb1c000e6e6a8415c800239c5a0f8001a80900049436e2887800065e54000ea577c6c142138000e else 0x4e25cb7501800000283a65b3973ccccb2712e5afb0c4300003830a0006ea60828001004dd039ae80019a0d00081933b1000002266658001decd4c82c4a060001400043d3191e77c0000103129d47c00090002948010b00341f00012b20e3e8e89000130c0084800299a6b8e73451e4493cf6689083a640014a400c580020f800895c45334d71cb88a949b0397d9121074c8002948068b00041f00312000a669ae38ef80017106473b662249e)))) else (if i < 255 then (if i < 252 then (if i < 251 then 0x7c25783884e000a44ce2256bc000cd06800001a28084e26f400018be87dc0004599549a12ccc4f2579c90e0003233830a00080201c1c000ea4cd06800294a6d8b81900000510000a446a024001c44d70f21e25b0001500057737748b20b970583168d4880004a1e25b000150005773774800087b2503c0011d4d70f45db5aa0e990003a93341a000a546162c001489de04c0c8002d18800071135c3c00095e0063a10d2d8000a8000001bba4 else 0x3764300000a00002262e3c00100c0043ab5a94a6d8b3be00030f18a8c0009b62c000e780284800002a02085476a300068000b3c694712d158c0009a598001eebc73044b6f9287de00068a69249a8c001a0002124039658a44b6f928b4600080820fbd634d14d2620001878c4c339e00012ad681e9b62c0000b4d5420000081820a0003233830a0007229b62c0015500183800291338895af0003341a0000028a021e4d2bce4870002579c90e) else (if i < 253 then 0x6af6a70002aa8c000bac2d51d7ec001a0002cf1d51c0008b637948b7400000241e8ddbd3bc92f0bb7a779200039e58d12924bf6000d15140010f85ab1a500001300058c3aa3800000c7baf1abda9c000a800225b7c946640004323a00116c6f290001609131b3dfc332cc196af6a70002a00116c6f2912b122400108002c1226365580004ef24a98000008400000050c8eb32225b7c946840003824cc4886f11a3a1f912dbe4a1df2621878c else (if i < 254 then 0x8604af89e1c0000088082000107d1784800257add8e6244980001e9630c0dfaf000107c0184ab1aa0000130064980001e9620007baf218109c00070002e5277926517353aa389c400061e3000103c0047b28acf1d51c4b10006fd78be60008647618109c000700030c20e997504b778a2a00005262e3c00001501041df0001878c00039e45e12a8ebf6000d15180010f85b1227244f0e3be00030f1800001468a68000e79fcc4ab1a5000013 else 0x114c33171ead6a520002d730000c74800000118b8f00058330f191b8a3e9de48001310c3c600028a1de910004e96095d1b8aae9de48000c8c00c28002d19a8090004824db16968a80d364c000010c5c78003239a8090004a069b269689040002db8160cc3c6261b239a8090003230200a0000166162c00001901042710001878c00039e45e120009860043dd413dc000ab12257add8e0084275bb1c9680000024d5011dd2844a598001eebc))) else (if i < 258 then (if i < 256 then 0x5f600039d32000aa71861c000fe935c700024a001145d80003322cd88b347506c0016610c8e9c5000001104c8563000267c8a6293a615fd458c7c89c4ad19a8890003a900d1ab5e6ba00014000025014200000198b8f56b52a00016b608040001d51d7ed0f9a0001e70008756b4985b016a8ca540002c0013651404261a21a2f090000003171ead6a549b62c000194c40200020100c0700000d404100006460021404d17968c480022f00089 else (if i < 257 then 0x5f300034f3adaad3a7506c000028bf0400022f8029500049500328000b52a565c0017d8e74cb6236e9d41b7ff6dd3a836000bec73a65efd30c000780024aa34146c46dd349369689900004ce2908c00082c049118f9138941f000120006a05f8213859e943860002951858b0000033a836712000ce225384e78000636738a999167ff0002fc1071200076625384e7800062fac911ab1100000e2fc10000a549b62d38554800061c480028709 else 0x42fc109c2dcc000300014a554859c48002870968645f0072a7120006a0240014a507c5a709cf0000c5a951b6d42e0000066162ce240019c44a709cf0000c75d5f639d320000025f821385b99bd060002ce1f3a266b44b000289c200000230e24e78ecc48002082340f0007153322c71200076625a193e0000ac5423a9ae1e0000234050a000aa80321c0014a405459c4800338894e139e0001800000866458000004bf0436ab6e9d41b)) else (if i < 259 then 0x9278e533c1cb1293200058001aa40044a3b30598c8f8c0350867108d00006323d82d30c0004c601a84328800000640410000a9cd9c59625330000a2c18001878c59139e0001200000063a411a14d8c647ac18001878c00039e350128eca6c6323d3dc0000044297413491110008e533c1ceb2000808352d0000da89a3b800433890008c339d32e8a00069471350001230bad9a4ac33142012013171e00003462034000d7501428002aa00487 else (if i < 260 then 0x73358d3453400079c01c1d5ad04000058000012288800045e86712d86b911c05000130cd40480000239b900004c400d18000e6668a6800189dfcc6aabb3cb301273300034534aaecf20004977131000063fe211999163be4c400018000886ade255190400005800001228887fc0003322cb148971c051ff1090cc8b0002180120500040232e0e0007220022c02107d9c4480000b1979543b00000b1a00092a00e50000008ea0db6243280008 else 0x56b00043e1600083e03024000034e404294a2f000073be00000a180009b200634001138004736628f1ae1e8e751d35c3c968a800004c0016796b4e00027244f0e4b30003dc78000cf29de4a38112dbe4a37a26c9878d4823a20000e9b2a540003558d28000099df0001878c7f300034534000b18fc670000008f75e2dd000800106e71024323aedecf29de4a19c000e4041a81d10000769b4a0000271988ba00044ef40015bc62dd00018f10))))))) else (if i < 305 then (if i < 283 then (if i < 272 then (if i < 266 then (if i < 263 then (if i < 262 then 0x6794ef24dcebe6864750a15000009a588001ee3c0005c94ef24f92c266926c0014a80046c73b889ae1e5635400002600082000e3c001678004e33c2549fba50000013dd790d495e000380019e53bc92f83b78001a4e239f30f189620007baf00017293bc93ad8002a1a86c94270001cbd0ca2e3671178000e40449122ec66110000283171e000bf600cd000000951c3ab5a948000b6217b973720000744aa62117800219c4ab5a0fb038b else 0x4b35ed00078be68c4000754800015c47b8da6a0001c4e2432000190e2d7ed28612cc000f75e00033caf692000692742650880000043400146d4acbc4f257bc98e4e200030f18be0ede73e691d930c00078002138048e0007cb39d320007dab4a4400168c00842711cf0000c6f45f430f1ab6689600051388e7800060002fa9878d6854f86982ab76b466782000107c06c48000051c8080004af5bb1ceb2a5400035388000c3c60002078010f) else (if i < 264 then 0x6780006b44a000ac2e84c80012a95006c73aed1ae1e45e5a3000108ec8a20003c00109ccf070003c59ce990006794ef24000e8e808360b0e78000600022e801910006a55713aff8000664598ed4922b0fb8e39b98f9000002930b16000038ce22400001168c4000257add8e4e200000118eb2de805635bd1e4cc3c6a5a000007138df0006522e9a6000d689400146d2a8680025e1ae1e8435410002b15ac66000858d13f80009000257ade0e else (if i < 265 then 0x8c400039116af400066054001ed51c08ac98002d78d6cb00035c3cc48000af63d314000c3462dd2bfa65100000023021200094872639ae1140c1450002281828a5334a43931c0005225c0080007ecbd818000d317b8600011b3041400014a19610000c8c19428002aa00e070005294db1600001cce22400002168c40018002c7320005d00031e000a40002499d9fe40011000a57add8e0004275bb1ceb2f260003571160cc3c625a00034d93 else 0x5f10003921c8e40000065c00000568c4a2fc21998157935af4041a000c367222d4a96bd0106a91000004890000015a3108e4d44a845c001de136c5a950002020d00000135c3d0ff08666055138001b3070004201a21957a8433302a000b466a021cdc000c748000338a6d8b4a000069b26bef18668864d08000c68200018a9830600041800f1000000860424001290e4c735c0001828a8c400039116c487e2af63c001290e4c72998001828a))) else (if i < 269 then (if i < 267 then 0x73700031d20000ce29b62d128001be4a2950000008d5f78663443298a6f60003c000fccd20dad42b8a631d0000103051400000660c192d8000cc0ac3700022c384a88438431000000289edd7556bcea468002d79d48d00000545010e2200078a7948800000848003bc26d8b4e40036cc1c940ac6d364d48800168c4a390002a1174b78433302a00001a60c1800001113db8000011c88b00000945010a548f2016351ca4a586cb80480022808 else (if i < 268 then 0x64573080f2800001a78c791c80012f4bb51000005085220005a312000ef09b62c000014c1450002951d48d44a00049528d6a000688653c8001b38b290c7ca779252a0004041ad6b0806886548968cd4048000049828a0008e74db16000a547523575400113dba1000000189000001450109c8004d9839ae1711b3070002d19a80849f56369b26a44000008240b800168c40003bc26d8b52a0004041a89cb88d983800168cd40424f80034d93 else 0x6a540034f3a000018024180016bc0106a950002868b5e552e00022bae000ce2251dda28f789800202001080003f33a836d5e6f6e1c3c004000e4058000009a8097595f133c1caf4be267838000010e445a954160000d55240400010000a446a025315ce1b787a10291338897fc0003332c0010586683523c00001042ab8001929252a00050d16000ef0ce225a95001f30ea950001c80b00077835012eb2e04678380000a4c34600000098306)) else (if i < 270 then 0x735012a540007202d79400175c8ade8002421284b00034332d6a000ed878001725cd07adcb8abd8964770003de260007e2dbc3d4a8000e405b2f2f899e0e00040401f1000c7e67506c00148801048002101c88b8c300034332aa48be0002182e495b7878004339a8084726a248d2eff80006665923c000014400041619a0d45f000867128ee0007bc4c000fc50a07a5a3bc2080b00082c3341aeb2000678394a8000e4058003bc1a809 else (if i < 271 then 0x134333186840a1a2dad4000f14f004a102868b0000023c63c000840a1a2e30dad4d0cc8002102868b37b000557108e4000a845c00000cff932b18001ef135f700034332af2e5e82cad66991115cd8003221a41b70e00092510b34840a1a2d2556bcea46b4c3910000f0000053341b03291e000200010a0f78980023b9a8094277020001c8a4c5e7704000123e06443871f99a41b00002432f2a00002002e180016bc034680a27b80008 else 0x5917786de12001032668351c80016a4b80047b1d51c00001335012eb20000083a1d800241858002501b5135f700034332d6b1ceed8780018bc0048279bbd999964e000000228000c890c86d3cdaa0cccb000000a8e9e8f74a03de260000086c64800147c0047ad2800aaa910004283de269e6b126665800231cd0ccc3b473b630b4774a03de2696c0000321912800005ca00025bae4090005af3a91ac160000223d47c00001491bd80046e08)))) else (if i < 277 then (if i < 274 then (if i < 273 then 0x64544a49428a520009b62c0011c92f0b8002d499d883ad0005720c94a0009c839961129250a00004b17d843df00030d180000a46b2280000b8cbca800003007860004f700310b7a94e00048000fce190db4c1bdb870f4720005a92ebcb110f8e451280000fca0002912e40900045f00310a4294c000480010816445bbaa541e9384720005a92ec1600124a3d47e37155c90002478028800037b03e1f0320006683400129cd8c92950003630b else 0x5296564c816000d6a686654a57e132058002250010648f00033b10b5e8f275234000020cec4294ab90000b7110003a91a0008200023e275ad4d0cca138004830e0006b5343320007be61a313210a0da89a948003828b0004a6325240006f600c3c00000cea4680035a9a1990003f358836f8290a868c0000f7cc346280a2aa5e175013cf4bc2e00000c60c18000010cec4000239247174b600032f2a000aae6c249529294e48725b27b99795) else (if i < 275 then 0x57200033b10cf400061a3117800168c480080019a8d54a0003921cb528e466e5c00004cc8454620004738b0004724bc2e00000601010000f7cc3462a92d4800088f749f3de2600000660c180012963147272472800085526e630d1894aa9405c38eb40000103252aa50000e00044a49428e6e0008d2416bd1394d468002a52528e5720008e510b4c6f66323c0000780982000003a06140003df30d1800093e7bc4c000008cec427900040396 else (if i < 276 then 0xa00e08a520011ce2c000f7cc34600024f9ef138f700033b10bfa0007523610c000cc0aa3c8000008645f4208c0128be8f0000251515a8c74800002a1830600005233b1096c00065e556be2a0ea46a9480026d8b00000b34a38b5a00067620eb4000010300022524a140000013a91abfb21661a3219610ccc0a8000011b22067a00030d18b528e4c365c000decc647aa52b31c90e3ad0000030c00089492851e9c000ea46aa532c2270e else 0x4558982e00093e7bc4d4a40013205aa92d48000890b0005010c0008406a02529552a314700003c1830600054a8c51c0011ca00c214a539000058002ab9b0920005693e5208a800061a32454001ae04b88aff4688d49600036124000dcc61a314a55490385a9480026d8b3ad0000020c000894928523155280f872d300018c8f57237b00010000b466a024000010d88900028f9868c0004eb49f268ba71c000451c1529c64722e9c745911))) else (if i < 280 then (if i < 278 then 0x4f27150002ccc20006c2480011099c448001f89e70f5a380745010000a426c2493c9ff0000b24080026d8b4420006711200100eb46200011e500c6b0a0001e29e47252b0002e89400092a517c633de4c71a100018d040003153060c80400060a2800106114040000011c90e0008c439116a5513c80635778000cc0a80026c2018d0004d730212a551887222c0002305ec18000251ad9e0000233211400001202a10000f7cc34600027020614 else (if i < 279 then 0x4d948f8191000003661a31008000c14500000598306529000391160000088a0200016bd00c6b0a0002fe9e4f27150002cd949b87009800000d68c48001f89e70f0005af4031ac48b8872438651710e4870002909b0924f20006612ca520009b62d4880019c44800002a4b880004794031ac2800078a791c9154000ba502758001348c8433302a000cc0806351c9154000ba5e0001e31e44a1864952880400060a28000018c1832948001c88b else 0x5296686c6168ee93ea804d2d8000018322125b800090004d900310000c2878c7800129cd8893579bdc940f44a6c34952903291e000200012dd1084800006199960006145b93d1ee93e0004d1c800101cb8000031b11200063036440000d3079e3c001cb4f4dca703428001452900050d16eb26d49e63800147cf3c7a94b342868b4e06a8000290a2d30d0a3c0016bc014300025b1979574f00035c3cb7a0006c44929d3dc00042e4a8fb9a0f)) else (if i < 281 then 0x48200040e168e48aa9785e06523c0004294ae5a070b52900000616000b5eb96180012d8cbcac540001ae1e000443915129b29ee000211c91556a4b8004739ae1e8a850d32f2a0000587523400004ccbca80030a3b61e74f0000060c884a4400025128001254a00026cb61880004a6362248e4b520005d4a52f21945c0ca4780008000008442131ee93e0004d1c800101cb8000019b11200063036440ad4000b9841d64da98bc700028f9e78f else (if i < 282 then 0x48b39116000b9661a31961381250a0000019c9060003ad4db160007589285168db317204aed2b1a50130004790020c000758928515292916ec72b90001c88b54a48b3921c0000a65f610001008dd8500000e9868c0000133a91a00001065e5400136405c423922a800170000018190cb7a94e6c449128001254a0002531b11277400034332a530ab0ca2d2d800001c3221a5b800090006143c63c0009b2004211c9154000ba94a5e2868b else 0x89d40f0001e940000bf04d3b188e2dcc3d98001868c49f00000126dfcb9e8465800165d2190000239203170005d642235110f8e0004400104227478003338011200091f3a91ae82bf50068400247cea46c8dbf5b37295083f386436000016752356bc000024300022524a144a46580001caec00068864000008cec43d98001868c52a4e44db160008bcb4624001108c3462953bc26d8b52a00f391160000146762136000001072523ac80006))))) else (if i < 294 then (if i < 288 then (if i < 285 then (if i < 284 then 0x4a000085b26000ac6752354a80000085a763118001857388e6ee3e98a81e0003c0015890d592763118001800052f3965717f11cddc7d27c0000249bd98001a2196718c3000160008946dc5000158cea468002b121ab26fe5cf0002cc54000f36e0001fe92190355297a0b2b85b44a36e2800089492851420002190d9f9000002894208eb0001600000468864001eccc346305a07bb50f60b41076a1ece31d60002c000010d10c8003d99868c else 0x50800073c36dd32020008c000facea46824c2227ebc0000303b820a100010c86cfc800005848000059a2190007b330d18000dca752350800000045bc623925e1700044a36f2898a81e0003d2800017e0980023925e970007353aa389d8c46000619fdf1d75c88003729d48d420000002160008e49785e1d96b4ea8e0002251b7944a000085b26f6600061a300011c92f4b80039a9d51c60b41089d1e00001861a30001eccd10c8002251b714) else (if i < 286 then 0x85b44a36f280b48946de500011e4ea46a849f9c321b00006b33b1000003c65e540012dc0044a841f94321b70200030d1893e0000084c00158cea468002251b71452a90b00016af2a5e82cac0011c9230bbd98001a2196718c3000160008946dc5216c000f948000346a111a65c7c70002200082113a3c001ab99bd48002aa9d51c0005974864000000a86ac800173d08cb28400039e1b6e9901000460007d67523401199e46c90002e7a1196 else (if i < 287 then 0x8e70004db16a9491689c3900800023820000009830654a4a43921c94800003c3a0a0000cbcac3900025faf00000130d18b88dcc6762000005ccec424f800006930005633a91a00000a77240001129250a2954858000b59500074a4ebe48200003dece274d10c80022524a1452a8eb0001688400000425ecc000d10cb7223925e977b37cb34432b2a000f849decc000d10ca210003e589420000002160011d67724216d129250a0000009dc90 else 0x2135b3c80400003210084000c1832520000030e82800032f2a000ad277240088000c346348486000287da0004bf5e93f2080684c000294cec43888001d48d00000632f2a07296e00025c08000c34624fab1800137b300034432ce31860002c2055a4f9480002b49dc107dc6e50001200000861a30001eccd10ca840004321b00044a36e28940ac70b64d27d58c1e498000021d48d52a0004db1675a00015c18001129250a2522458ba8e))) else (if i < 291 then (if i < 289 then 0x5a63191ed0d08666054001698c647b7a4929868c00040201a080009c08185239e31000058000042018d7114d90001081c00061a300016bd5c830002211d9898c54a40001c00271c000456f1258000926424faa0134d90000011091e8f2c0e1800181d5c832070001868c00038e00622000884766263152900007000231b592a4c849f000269e4bb000059505970cc0aa38a520000e5bc49600024000884766258be3acf948473c6226d8b else (if i < 290 then 0x402014080009c081850000024c3460002fea018d0005af0040c00091e0022000554981c58004622070b8c54a49061d0329b2000200015292907492ad32138f0006ec486400008e51305c0000154043462a520000e00048f00110aa5188c0e2c001108ecc4b73c3e35d1d4a454a8c51c0011889b62c0014a900c68002d7803060004a40031c00075892851a18000cc0ac21a6c421886860003302b0869ef086200015c800c40002a52520e else 0x4cc44b29014cc06c24960c001388600020c9b01f62437a3ce1e0009480041c002310e445a95313a018d529000391160000046042568c001140423c007993930000053ee220000028a02164daad6c068000009b3a155c5e64e218b26b088083400000514043c9b55ad80d00000236742ab80009c4319093acc9c98002c22020d0004193603eab80009c4300013acc9c9aa730b2401600019d30c0e00021e3220c000104c8450000121ad9e)) else (if i < 292 then 0x85436842000d82736b40013cd200b000364a60a80006904493c000bdc9aab210921d3fd88000011b3a155c0004e21910c8326c07d64d181010680000c9c90e00000139116033188a521e3100000143800001981095a3000450108f000064e4c0022790106af89df1ef8c00000230212b460008a0215393cd200b000001228080006ab5b01aaf487601455e4c0010106abd000003155830004e2180008326c07c001610d9d0af30001de91 else (if i < 293 then 0x86677859116c4f05880834d08000c68200018a98306000026305148040000061c000004c084b5c2521c98e02a4a43931c000012726394a400136c5800000981099283f13ce1e000e327dc44000008d8493440002d1887934604041a970bbc000559a4de8f387b120001e70f3f10003021200000a7dc44000004dec424138ca6d8b037000367420008c0808354a5c6536c58000059bd884820004db16b268c00003557000138863348001b092 else 0x6a944200012ad200063a40000dedda47af2800238116986857b52a8460006a641cc0001250a4682538001200037b7691e9080008e245a61a16178a8002790011673000049428d52884a0c2634529c00092420002389173000040d290dc9507a4e0000038cec40000039e29e6277110001af66000688657393c8000b22100000109000778591168950cc9285108dcdcc7483d98001a2195cf4f20002c846e6e00041108000c744a2500024a14)))) else (if i < 299 then (if i < 296 then (if i < 295 then 0x33501000000263a418bd1e4ea46bd9be5a24194d86273a91ac4e00075234000040d70f3888002280852a0005b0160000029785d2955296ec72213bc000090004f28072c894000928500015296ec70003111d72f0007da31d2102ac5a000454500012c07a9baf70002c81f67000046000de468865621dcd158da95473ad80b0000193060ca9400072438002394cec400023c8078d52a000391171ce000892780013c8018b39800024a14 else 0xf34432000010806354a400181c5a2500024a1454a0005bb1cf96f2600025844000d4882e20001870c00071d47022bccbf49f285850000d70f2948003038b66000030e18a94000b7638001c78eb97ab1a759b51300000130e18a94b88b763800000500c6a94ba3b038b52900060716c280006b87958d3ac0009aa51b52dd8e3df00030e1800003c60a28000028c18339800024a145f154a0001c000884004262d0000d4c83de80236188) else (if i < 297 then 0x5290008e716b9e9e51a059764000da8980023ca018d00000c344320009d661c30000020d80fa851f98001b00037b3481ea5200081e2d0aa2cc0008a250002341456900050b20aea0008e025d061f92250a94aba0000b40f37b3ce1ef669d661c31710000c3860000052018d529000607168940009285115000001080000009a2197cb79300f12000f26f9625b91156154ba7ba1d0001500037a3ce1f1289e510e59850040d70f25380019d88 else (if i < 298 then 0x46c982e50ab800061c300000051084b72b8e1db9000077890616f46e3876e40000144be83a010001828a0000093060c00000e6762000129cd8492a50001c90e0004f24802ca520007222c000decf387b228002341461173735320a9c9e4900580000b0d8492a500021b0e00001d33b1000001878a780011e500c68000039a2195290008e7160009e51a058000decf387a25000234140007b330e18c22000a9841d061f93e50bd98001870c else 0x5d730e18ea2f8ef185dd44001e30b8003301870c5b80000013ab94f160183d73d6e5be0b00000118e9000056a35c3c01401476ac8000020ed590040001ae1e4360006fb24000cc061c30001d9ce696c830002d80b0005e58cc22b4af160003d669620d20d80030a9ae1e9068e75b0169b0000668350d8000c9490000049a19900000244312dca00076e41571c70c38600025c2d09500048543460000ef120c2d570000c3862e780019996))) else (if i < 302 then (if i < 300 then 0x44e00000416b7080000075e8c00153084610002313c6697224b21ef470d6a9840000038cec421b253000120003923630c0008f200e3400110c0044b17b729a99062f00031d20a54000b6e2c001beced592a90001870c7b3576343320007e67506c000004c3864832a944f0b55259a89e1600072403e180015d8d0cca6c0002020d00044300e13186000b602e39c000d70f22f8002d0956e500035320000c2a76cc90d80016dc900029700111 else (if i < 301 then 0x5767cb343320000088842400239e418580029519a0d8184d8000110a49e666659b31de24185aa500000f0e00000b33b1000094c0104802239400032720003630b000778443120006f60063df2c000d0ccaa90001870c7474d93341af9713a68664002394d8c32ae2f89870c8e50000020caec00068665cc1710c38626c80019a0d00079344312f960006866400000cd70f2274738000b5570003252400eb8861c3155c000c9490002e21870c else 0x4420000250c00096eb42550da37155c926c000003880005bb0050c000884004254aa39c0005a2fa5b2d09556a00031d20a551cf2302d4aa39e4185a954738000b7055b09060c00001802618001108010480025b2d09500045f001100728f275235aa13ce01cb2b500018e9003b00035010000aec68665360000ea46a954738000b0004b65a12a86ccc0b6e491080000144abb0001a1996cc8e700016b22b76000200016c0ea46a3c32f2a013)) else (if i < 303 then 0x6fb8fa3b56488400007c255d8000d0cc80036601c8b4360004ef2494cb771b820000025108480000219a0d00062f3b7200009b0002210d9298d8c94652799999652a000906169b0000002212954ad238ba1b46e1b1920006cc90616000a54668356e1a96230e80000c9d51c00000e3a91a0009b000a210d929800090000009b18662f8953532088400004c253be39d64458000021a80904e4420000c000c5e76e400013cccccb4293d3c830b else (if i < 304 then 0x52a00091816bcb097198451080001744abb0001a19901f6cc00016b22b76000200016c0ea4682ba5bad09500000644212000044668340018bcedc800026c000885ad7a7705160009e66665a145c8914878003664830b00052a3341ab5a9b0000216e1a94d3ce800006809060004420061200096cb4254001bfc00ceb73a2f800087cc0003a91aa54b70e0a2c0d917cd3c403a0001a8084d80003a91a000aec68664000000c74821b33000012 else 0x56a35c3c000aec686650d9e8c0f490002bb1a19943600003b24e3abca000454aa3300005a078000010f0004b637a2ac38fc400c8c0012d9684a8002c39a41b61c7e200046000c670a8856a4001234bc670001d51c5b87766a53a000082a3a78000080ea8e00000700a0600044200612000aec68665a9000016c426c0001d48d52a00000116b52a569785d6a54ad508b8000009a8086a4576343329b0000752340015d8d0cc80f80018e90)))))) else (if i < 327 then (if i < 316 then (if i < 310 then (if i < 307 then (if i < 306 then 0x65854a0001c8a8e3876e4181c001b0c432c2a54830e5298c400016cb118aa9438000281110532c2a50000e00002830e18000e60ab81800110c02048002bb1a1998c300000416b70dfe00074208000d3c426c0001d48d0288e735c3c0fe00081c2136009cea468000051a80814d00031d20000aec686640011e4ea46a1b253000120006fb3b56512a0007547000121000888001bdbb48f9068cc40f1723c6f6ed23d360000ea4680000198e90 else 0x133b110329b066835360000cd06a1b0001929211c00034332ab800061c3047000110848003bc4330b4784b400026a82970b425400006cbe83b22800005065760003433200000861c31ecc001b0c42948003038b55c0005bb1ca9480518828001008d64532c2a50000e4360003622494cb76d8620000014cd068002008068a65854a0001c86c0006c449570000c38622a3179db9000040100714000c286b8794a400000c5ae58001870c) else (if i < 308 then 0x6e544300012000aec68664001eccc3862952a90000b4364a75b7240007e67506e41966a27858002bb1a1994d80004041a0008860182630c0016c05b728001a9908e700035c3c8be000b4254001854ed9921b0002db9200052e00322000bae61c30001d45c58ba73bccb3aa200066030e18e16d9305ca0444000c74800008d9dab211b00035c3c86c000df648001980c3860003b39cd2d9060005b016000bcb198459fa1e0000c389088a05a9 else (if i < 309 then 0x8c65e5555220008aa66e5d6cd3819c8a0000002708c5b344b6c32800000a7f231598000c6478000009a88948b8e57780e9171ca0001e42d12db0ca2b300018c8f738000351129171ca0001dcc112db0ca0000ab17d8400003940c280000105f41d38100800051baa250000600065854a1c00000466834000d64c386294c622e58b5298c400016b966b261c3138000111052a532c0000e0003920230c000012676200011e40186b178001a990 else 0x57200039116000c967243a168decc6478000039c80b0005295460e000b4c6323c001598cf070003c82b21300000135112f54ad48d2420d984d424d80000c99e0e0000033191f13cb4c0001c00112db0ca485b982708c00000835112b4c000ef01d721380000a4540001bd150007384e118a3e0006c448000000e70cb8e3de8001045d5e555522b4c0000121e2a0000de8a800002a708c51f00036224e38000004416cd380000a402b3919b97))) else (if i < 313 then (if i < 311 then 0x5a60003191e0000127e226064dec00042948001c80b52000036224000e709c230002394cf072e4270000148a800037a2a00000073865c71ea80b482948001c88b57237b0001000000c9c23147c000d88900047299e0e8a800037a2ae38f54000400b4000cdcbb802f2aaa910004553372e0591ca6783a0651e400042a30001c80b00000233c1c0060006323dde00a0d4448170001fc8c0000013191f06ce1cc3e6dce00bcd444c0c80000188 else (if i < 312 then 0x56a353200008f20022176958d50098001d69c80b85b00054026f20b4c6323c0011093846290b301b11250e00039e1800075a8402c0014a40143800a2f0000800000134432e70b4c6323d290000cf0732f2fc2b1930006653443287af7e6323c000020db84b22800000875a660b3191e000a1c9c2300019b0f1db21e80018c8f00037b6b01000075a6de2dcd198147c90001d69b78b6455290000ea1cdf273c30000080d91041d80000b07 else 0xd464414540000069c23189800143458002ae19e8e89e865010100000126ae4589800143458004328008876d6b241454000d60790da04c000f0da80023220a2a00800033c1ce040006a225296220cdcb80000398c8f62600050d169cb0ca00020001ac0f21b4098001e1b500000133c1cfb8b666a225c09ce0d444b130002080b4e537b00010e700006a2256cc000cf0725280019b975ba56a8a0200007580285000002548848000032e407)) else (if i < 314 then 0x7b545e12000b007ca41f28001918c8004062708c7b84f37fc2c000f6a0102400189800858002802708c00e5b97fc2c00000271e21f2a41d918c8002c01f29053f4a7000250da9507a4e2301178d4440000051f8890007384e118000c4c81e2c000dec01440000011f7110005b976e2cb18a8abde680016e5db8b40636c3bd905cc5ba00020ef6b72db05800189904058003659f7117dc00033d1cab80007f231644dec00040003dfa2399 else (if i < 315 then 0x5a63191e0009c092a517200000044a2ebdaaaa918c0000351108eef209424c00112d254a00001ca5b150000263191e0000247dc44000019384648f0000008862d5b97fc2c000c4c7202d7316e800080148001a8895b355c33c1c000e708ba24000018dcd1800000b938867a62603316fc4c4c0002c00139cdc112d4c440001780c38b3e52000000323c219696a5234baf334cb19a100000841454f5ec4c0002ddb4000e3c400024599e8e else 0x45d5e58a0220000046f45569a2a00003add2b506f905a600000f0e0000149c23147c000d88938e000000908050d93372ed32e3000084008000e70c8003da1e1b50005b23eb46b669c0000500019c8cdcbc632f2c50110004553372ea400006c44915201400082f2b801ab910cf7024e118acc0006323c344000d444a45c72800070000034e118cd20006c64800033ce70cbfd225b61940d161361f360000be1001800189c01c380045425b15)))) else (if i < 321 then (if i < 318 then (if i < 317 then 0x669000363242042046f4559a4000d8c90830831ce19819000002100006f66323e169598e4870000041c80b0005295460e000b4c6323c001598cf070003872849b6c500046920ad40006a224001ec12dcaad9a703621400002433c1c0000066323e279698000387b0002708c778738351120000166a225698001de03a900001b1120007384e118e38f7a00041721380000a3568001a79d00000139c3300ca0e00499f90001624b00028d25e17 else 0x7384e1180011ca67839c71ea800082e42700001400000339c32d5a00069e7601941c001301c33925e176ad03534f3b1500006f4554a4000e445ab91bd800080000084e118a3e0006c448002394cf0738e3d5000106997180004207600073864001ed0f0da8002d91f5a303a10d3372e0008aa66e5c002394cf0722a3d50851081947900010a8c0007202c000004c64780b80b99e0e7780003511200007c9c23000000ccf072dd2b500010) else (if i < 319 then 0x626000410160000049c230000dec234444f2ae19e8e00037b00210000b5266e5e279294cf472d980019e0e0c50d33572200075801250000009488480006d2e40789556a35320a1c00073c30000eb50805800294801070dc45e000101b61b6688643750f12dca8000739b7096450df0000e87a0006323c00143938460001d69b78b0e137b6c3100000546c8820ec0000743ad300018c8f00000c3f1130326f6000214a4000e405a900001b112 else (if i < 320 then 0x7344a700024196e708bc2400000d11cc80039c1a88900500038f16e4eb3e6e68c000004dcd1b93b9c1a88900073835112000b3e71e2d7316ea28080000059f8890007384e11800000a81e2c000dec00840002dcbb71680c89577b20b98b7400041ded6e5db8b3130001bd1500037b00110fb8ab867a39f71570cf070000041bd1500062641016fb800067a395700011fc62c89bd800080006cb35722000f7e88e657315a800083542dcb6c16 else 0x7dc8c012f30b5291a5c0014352d8a80044a9f2900007dc8c012000b72ff859b9e035a94e800279bfe1667a00000116c4cf6296c54002254f948000286a5b150007dc45e12000d32c66858b5798fb888000019c80b5cc5ba00020000b666a225ded6e5ff0b0002d99a8895ba7bd0002001ea9ab62b8000018d5c8800001c8f080005a948e2e00094a67a399ea278010580039c22e8962d5b98512c000004008219e93940005c0644a9f290))) else (if i < 324 then (if i < 322 then 0x54f0006b94c000aa0786d5915128db8a294add0000b52155736124ab094e000491e4d85484380006a9a51c0000600700c000c4e01e1c001698c64780027024a9489500046920ad400000a240022a12d8a80022f001080005a93372efb894910a396cd290cf070000689a8884775da00026000b527165df64000ed590002524428e8c078a4b62a00089692a500000c0c64780000d2708c00055c33d1c0000120222000227800c580031325b15 else (if i < 323 then 0x73740e91e0008a0200015a51a480002521c90e62437b0001e00089c7222c001b79da84a849f91a49b48f47945010000ad26a64148800001c4a100004358b44e0006e51d1d6000eb2211e40000043a90a539b09200082c39e18d6acca68866084000f1db0000089a8880000063443200001cd6a1c0024555bc6000290801124a1563000269486d400c392917116f07000003b328700091552618948b88000380010d96f09250ab180013 else 0x68600037a2ade901e9c231bd0001384622ec631ab916f40004e118b4c0003d01c001154cdcbbd3a70339140000013910cd0ca1a96c54000eb0dbca0002ce1b82268650d6262a000022072110080018503a6c800004084790000020caec0006866510d48968c4800253992925a637b0001ea520009b62dde000110c4a13a273c98e0005a335012000887032194a4000e4058002792401600044e33c1c000b6692a516998912c0780000498306)) else (if i < 325 then 0x48b0011cfb88bcf14256e98e0edc80002458008e7dc45e74d12b7400076e416a4000e2cba95a2f0000900037b3191e8eee6a9424c00122ccf073ee0001a88900075d44732b669c10ca51aacaf800043bc0001a8090000013372e9ae94a67839bd110938462b940c800080000053191e000b4c0061c00122ccf0700041d9b22083670e50936de83e89c230000024d444ad30003bc075200003622400000873864002394cf072e427000014 else (if i < 326 then 0x53f436000250dc9507a2e16b4b0800043bc0001a80900002d3372ed0c05896c555ca064000400000198c8f0005a60300e00091667839ca167d9ed18000031a8895a60007780ea400006c4480000cce70c80047299e0e5c84e000028d5a05c69e75a18000de8aad30000128752000036224de83bc9c2300c8000e44301a1d61b79452a00002f1600075a0321800004d6c03b4300025b155ad00000d1000000a7ac80001670f9d10001bd98c8f else 0x5cc56935320dcc7be73c300000d4d28e2950000190b0003ad0210c000038b601c000028f5900002458038e0005a63191e00109b1e44c0019791dc4800000b4d886867dc4b62aa7e94e0004899d8057c0d27200019e0853f43663c2400091601638001698c64780042d002080005a948e2ee52b3e0008c00176a3c89b433bba5b1572859f00046cb40009785c0011b911ccc618001a8896860304b62a9c8000678216a40012f0b8001bd98c8f))))) else (if i < 338 then (if i < 332 then (if i < 329 then (if i < 328 then 0x5a335012000886ef01a1b4001161c3aeabb1a1995b00000010caeccca686655c8000008400035a9a19985837b5a61e000b466a224001258d8c9000390ad30f00066345870000e3675471c4167c0011c2c1f61a1990000073060c0000066e81d4a8000e445a47800228085ba56946920a520007222d23c00114042aba539b0920000026270e000ad26a641915129254a2908001b0925574a700010a440006a025080000e4058000009a219 else 0xe35112b4c000ef01d721380000a00039c2708c51f0003622400000673865c71ef400083568001a79d19719737a2ae38f7a00041ab4000d3ce8ca0001bd1500066c3c86cfc8000b12586454696a4bad3000473870000044e118a3e0006c449c7096000080000cd9bd1578e5e57b522b669c101e5122e39639c380004a9d48d00001702908a540009b62d008000024380026c802080000015720d0dceea8b0e110d0800004add2b518e90) else (if i < 330 then 0x43d0003191ef7ecca68864000928db84c10b361e3b600001136441032000004220ec0011e43a949641c88b00000139017076a52a8c1e0ec00239c380047299e0e5a60003191e00000a6a025721380000a00039c2708c51f0003622400000073865c71ea86b4800012da708c51f00036224e38f5403a4206400001042b90001c88b0000014790e4ac9167243a27992ce4870000009c80b8e75295460e00003067838000004c647c4f2d347387 else (if i < 331 then 0x37b5b210b2313c8202c00002cd5c8800473a458b00000445d12000c4c96c559e800000443a6b259eb2091e7383191eb2200000221799fbd225080031325b157380003191e46cf7e88e64000020c6478002b31eb2000085a00110cf49ca9162c00239ce3c580039c1a8890006264b62af9600088e659757e15009b9c0001f8890006cb41016f6ac4c6f454000eb001ca000000a910991550e4e118a1c00073c30000eb50805c73a9480007 else 0x48b33d1d0190d67ca400014352d8a80039c22f09000019357220000047ac8000122ccf474063d51f29085a48b33d1ce700007e224000010de8a8003132080b59137b00010b6600067838079ed4d5c8b13473a080b8490003c36a00002067a38000030c647800001ad90867a89e00016000a1a96c54875c0a300480042d1eb2000073845e12000fb896c54000008d5c8ad4c44000175e66995bf4313cc4c0002e031600f94839c0001f889))) else (if i < 335 then (if i < 333 then 0x80d86b3e520000a1a96c54001f711784800279bfe161886d83e5200011ce81e2c000dec02840000039f88900062637a2a0000047dc45b9da94000e92bc4a3b71600068851f240004806e68c95a251db8b0003131bd156e76a56ad3a00000a6a224001898de8aae62dd0001077b0006d82c000ab867839c9d6c8dcd1918b131bd1500001737347092000786d4000038c64780042e8008b67a7e218a10000008720200014352d8a80039c46009 else (if i < 334 then 0x2415b23eb468a800000242015154cdcba900001b1125e56cb357220000e80fc1800189c03038002d318c8f0004e0495291ce00000a2c00122d13872d680044f0800085a3d640ac8f200004d5011792844b038001c80800059d37044000c707ca417211789104800225a4a940000234e11800001e6323c001570cf470004738020b18667a00010b98b74000400016ccd44480d31325b1500000439010000a1a96c55b9c001a94e80037fc6009 else 0x24e118a3e0006c449c71ea8068800022a99b974547aa01e2103246a000202d4000e40580006719e0e0b60003191e0000166a225698001de03a900001b1120007384e118e38f7a00041721380000a3568001a79d24000039c32fc8000b1258001ed0f09ac03283800267275b23eb46b4c0011ce1c00000cde8a80013ea708c51f00036224e384f817440000019384628f8001b11271c27a00020000002738656cd38090ca0003da1e1b5)) else (if i < 336 then 0x3ac00628174000a4425438000e7860001d6a100b8e75290000e87a0006323c2e90f0de8a80013b9b7098210b33c76c0000366c8820642ec000405e8001c80b83b0008e70eb4c0006323c000030d404a900001b1120007384e1180011ca67839c71ea800082e42700001400000139c32d5a4aa69e75ab4000d3cebf20002c4960007b43c26b024000a804d1750a6280880047299e0e00000337a2a0005129c23147c000d88938e3d506a10 else (if i < 337 then 0x62d0008512c9e719467a3800239c8585b3d000110080004a700624fc40006e68c001ce117848002a2af81a0006264b62a000b0114041959b62144b0002a2af81a0006264b62afc441c6e68c00239d04058000049f88900037b00410000cf49c230000004fb8890b44a3b71680c8958a020000e709c2317316e8000810480024b1220855c33c1c000c4c6f454000dec004403a2c8a708c0000014e118b98b744c640001ed4d5c8ad985699e0e else 0x85a89e10000b527165df8967c00118002edb41935c865e47712c0e000720218e1674dc11000225a4a940000253191e00001a9c230001570cf470004738028b00067a0021101912a0004247a280fb88ae62dd000100a55b3351120000027202083a254f94800044a9f2900007aa3d6400010d68bc261b52a18a9c0000051ab9100073845d1200000323c219ea39c29858000009b9a37e285d0a4160009ecd1c9000167c28858002a2af81a)))) else (if i < 343 then (if i < 340 then (if i < 339 then 0x90665833d1d20c89a67a38000fc40044b1229999e8e00037b35110c4800067a3996112cdb8a0001bd2d30f000576343331ece3675470000010c1830000fe1ba0748f000450100009487243a39d138e44580000130a07711479000111ce0087202d484000d8492aba538000852900039016a440006a025139d64cf070000469a51c0000470500c000c4e01a1c001698c64780027024a94895000469211ce00000e2c00122d13873d50001eb20 else 0x52a00050d16e9e000b601d6b4015bd04000003003866860004b62aa54000a1a2dd3c0016c03b5580037a0845e0002d6129aeab8d983a4554394884a950001c88b57267a6f410000038052110080000283a9480026d8b4d9000005108f20000021910d08168c4bbc000221895a637b0001e84e89cd983800168cd404800221bbc0620544e33c1c0011ce9b62c0005a9518300021d805950000055a61e000aec68664001514008d000225a4a94) else (if i < 341 then 0x6b88e544e1c00032a6b6780000a8ea4680000700c0452a0004db168040011ce1c0013640204000002ab9065a344300012000004768c96e8000c748466272ac01186e6624587088684000026419390e4870002d19a8090004437780cb70dfe69e74000010c1830000d09ba0752a0003911691e0008a0216e9cdd1a480d1000313875290008e716a420006c24955d29c00042910d29a8090005fd4e11800000a6947000002c030334300025b15 else (if i < 342 then 0x7dc7b037a2a000d966ae44002314edc73ee3811bd157bf3ad4201632c000ae42e31000239c380000199a8d5200003622400000069471bd172d644600a2e5ac88c00000600c0c000eba66c3400000400c3bdfc6224c0b5290006ab16a40b946c449efe39e3105b05800000875293ad4201600075a8402c0014a8cd868001d624a9468543c37a2a00000666a346040015c85c62000473876f45cb52618a54000ae42e31000239c38002e5a930c else 0x3ad8c4160080006886400143938860003ba24b120005135954ee4e0007d88c0c54a94d468001d69b78b49552a5351a0006f60102000000ccd86b430001bd157b000050d17188d571ce1d4a800000858001d6ab9068c46278e70e9311cf1881c00006511cc800008008860000010040f1cf1889302d4a400239c5a900001b1124d78c54361c0011cf1882d7315a80008000002a710c00055c3b71c000b646e68c001b2cfb8894f00024b12))) else (if i < 346 then (if i < 344 then 0x1b9280c0006f6012200c80240003800473c620b0008263ee22000cf49c43238112c000a008a4a8000d0005b976e2c0008766f454a65ee1918c814800000875297788e7160011cf1882dc9c000dcd18004131f711000002447320009ecd1e916c9f2c010700027b347a40000034e218000896d86516c957000072e62dd1db9000052a0011ad0cf606f455ee16e4000b2e62dd3bd9000060b0010f1ce75a9302c000eb0020a4701bd80008 else (if i < 345 then 0x7e068c421340009e684659770001710600032a348286953e344030a520011ce2d5c8000008439a0001929285a64b4361c0000266a025c9d67d4491800005809078e78c400016000c0eae420002060e146b43286800150000013e520c7d0d6eca255a8000008480035c2520e6c64b8363248ee000bb44df8da31084d2948004738b572000002110760008083616992d13870000009a80945d8cc5552307609a66a3551a39e31058000149f889 else 0x68650d0002a05e0007ca415a8000008480035c2520e6e402f3372e000f5494838001844db8a3f03462111a5290008e716ae40000062154972c000642f80028a916ef83b4041add8b96cf430000070d28e00000a817078e78c400016000c0eae420002060e146b43286800150000073e520000c7ceca24002254dbca3762ee0000c00047f4a41c000be8bca440013d8fc123f03821d01a56a63e000128ee000bb44c00000929070003089b714)) else (if i < 347 then 0x49962036000ca8f44a2036388000e80044ca313c6c65ed36324000a26af09c001951e89443eace1b8226c600036324000834c3c7e035f90000eb63c6b30bb600047f4a41c000be8bca440013d8fc1200032a3d12800086e76370fc0dae740695a98f800048003d52520e00061136e28022ca8f44a14a400239c5ab900000a885525cb00018e6800064a480019810106a6c3aca1b0e00000b0410f1cf1880002c00181d5c8400040c1c28d else (if i < 348 then 0x66534432000a26af09c9d4a8d00c680021b000922745c94031aedae56fa2a92911fd7c4700023ca018d67a50e4c518ad4840a44254a4eb639c58000211b22000002f34a380000500e01e39e3100005800303ab9080008183851ad0ca1a0005400007cf94800031f3b28900089536f28000bb802c31c700012907000279b0b160007b73f048000bca8e044001e71d91c36bb160001a00072e65b42000a18014b0000019100c0002ce1b822 else 0x7dd5b977b2c00092a66c35c8d5a8000800027b347a40005ee4d658d0cdd200055a212e1530900035c338090008263ee22000896004500013d9a3d23f02a2beb9a7235dc3b72000000a6a22649400138860004131ab9100044b6c328b98b740004000d3d9a3d24928002710c00052a3361ab98ad4000416ca314edc700000921e878e73ad000160007586de50000038d4c80002102910900000a60710000a1c01030001bb0f5902520000018e))))))))) else (if i < 523 then (if i < 436 then (if i < 392 then (if i < 370 then (if i < 359 then (if i < 354 then (if i < 351 then (if i < 350 then 0x79272a44030000d10a9848001515f5cd00021d1f81589d7b86b53200092a66c34001571ae07391ab5000100004f600348000bdc9acb2448000cdcbbe9c8735a9968687f3f02ae4e0006a226494001388600029519b0d0006cb35722b98ad400040002314edc72f32c2244a100055301810000cf49c43000157004070004131f71100044b004280009ecd1e900000051744beeadcc289600e52a3361a0000066dc25c8d770000842624a8000d else 0x7fa52744732a520011ce2c00000402042dd3c22349000000548e2e00094a002393611e501068002272020d00091c3d640e6886c6c449cd19a4d8893bc0001a8094d78c50001c00086c6c448001138cd86b7a2212f88c0008e78c4160000446e68c00154c068400033d2710c0008263ee2206a89600050000038db848002dcc289600b4950001ae46bb800040001570edc700021c802a400068854c24000a8afae68004000f0da80021d3de15) else (if i < 352 then 0x59d3704400000292c49c9d6c91b518000042018d0007e44c63a000b50fca6c0015cd1f8fb4dc178001300038f79d22000dd069471505434000ac2a39732da169b7905402600086c92c48001674dc11000317a018d00038f8b222000d8aa106d97576400098003172691854150d65c2ac0e00000a221692900007000317a018d00059c370440008bceca25bb177154860004359a88940e5dc000190dc000c54e00016e5958b0002e41b794 else (if i < 353 then 0x645010d6a0006886400239e3105a912100000900056935220000f96a66395724553886000473c620b62752a4041a00022a6323c000230280300001a822078e78c400016000e6e7ca40000098f5903038000048800059d370440008bceca2400129000c700044f2018d0005c836f290ad1fc7b0e80018bd00c68002e41b79473443663c240010d66a2250397700006437000315380005b96562c000b906de5000149d11cc80023f8068e else 0x55c6f44e118ab8b8a9c2315d9ad4d0ccc620004738700000900b0c0009e49005800000401042a932b2708c5a900048e2e000aec686653651e501068002219a809000496362250a2a40e683d10d080000493fad19a80877800044312ae4000b4620000dec0047b9a334992925a93cf4bc2e00000860c19008000dd03a948004738b28848f00010b98ad28d2410080000143a948004738b00056935320b740008a020000decf387a90b349b092))) else (if i < 356 then (if i < 355 then 0x3ad1bb0cde888498a30000eb400c337a0002628c00044b6c328b6718ad7039bd172d38863ae8000010660b1ab0000ea5475a8402d4a80015c858002e5ac88c00000344e1d13cd700001d6e97700008000ad91f5a348b8e50000f04cbca7da440000880d82000007a6d8b8e75290000e000018a8c180015d8d0cc8002950020d0005834e118aa6000de82000164568c4be5aae35c0e55340400010000b466a225f2c001ae070000009f711 else 0x1d03ad0000ca400006c449ae23950d870001d6811066f40004c518e0518ad70394a800004c5c62000000876273ad1c20c00075a0061800231513873130001bd155b344b49528000b969c43000001913872dd2ee000106690003632400056c694720997940008bda8001bd152b55b251246cd20006c648000004d28e000309b0f9b5ba5dc0002104cbcaa2c440010815c8324c313c620700000a3361ad0c0006f455ec00014345c6200000107) else (if i < 357 then 0x5207a336224e4e0006e68c000025f8858004131f7110004f668f48b98b740004000000538862d92ae1db8e1b052a0001a0008746f45400112db0ca443b673bd968260003ee22b74001140421b998dd91c000305800872e13ad4981600075800252380dec000448aa872710c00037b00610000bfc66c34001709100c3430001bd157b000050d1600075aae41a311aae1fc3800010223990000093361ad0c0006f455ec00014345c6200000187 else (if i < 358 then 0x7aa64b4361d06e000c3e6c000fcdc3842a32b94620b00002f3f11200005325018000dec04c400980000307529778000160010d67ca4103d15000060002e22f88e00050d37a2a98a9b002434000028fb888004134620b00067a4e2191c089600050719254000680021d9bd150006ce76e2c000e5488061e4957000070002ee1db907407ef72e4304c9cb1882c000008018380046224c0b1bc52a4031aa52ef00002c001e10f94820722a0000c else 0x45d4b55e522000c960062227922c0005bd50001f2905dc6ec3f918000916ae42c001ae0d4448003761fc8c7aa5dc000200011fa6c649a19c098f8aa954620000b81860757211076000c4e354a40000245ab90e50000800021435012000b96cf430000008d889393800236235b28e544e1c0011ca86c391757940008b8e2ee234908180005721000000a64a48000008f94800022a2a90c71c64b55c1c8bc00123025ae192d8bc70000d41f290)))) else (if i < 364 then (if i < 361 then (if i < 360 then 0x63c36324000d1000225a1a1fd8f8abb2c8c1a9100000033e520e38bb800030001ef593c4b43286b1f157bd00000312dc800066e5d771bb0000622eafa2f29100061136e28d8cc786c648000020d4448004622b90b83670e00036000dba008318815d4000800047e9b1928a04b5000221d8e98aee91ba12d57948c1b3098001b0008c4572160000086c648001b7401462baaee0001045d4b500022d0ce050fe54001b7400462baaee47e90 else 0x62057500020000dbabb8300023f4d8c945025aa381152900000116ae441c40620000014f948000000ab90883b8186271b03000080834000154c9493d5325c628e784000572110300008083517813c0004800000992924d764b62f1c9aec9686c395180023105ab92a98000877800035112000b969c43000000957072dd2ee0001065e82f8f226de813a66a340000c811838000179c28d0000244a41c0010b4020200015c8014580032a48628) else (if i < 362 then 0x6dd00a18c40aea000400023f4d8c945025a800110005d100252000e98aee904ed6cdf34a0003a62bba40005b37cd280011b0836b621ddea23cb00025aaf2916205755dc20000c260026da1a2bd8f8ab4300031f150008c450d16e04dba09c3000192c010444f2458000b7aa0003e5200009e684659771bb17106000245ab90b0006b835112000dc6f00a4001c38014d8003760018c7aa5dc000200011fa6c64a21e2c5858b3742e2a3811 else (if i < 363 then 0x61136e28bb8dd800030001a30e80d23b800341936cf4295e52200000a7ca41c7177000060003deb278968650d0002a00101a98c763ba254dbca3de82d8300900002035112001188ae42c001c38044d80032a486280006ec00218e38bb80004053e3f4d8c900041d2bba40006e3004522980006c648001dd0e70c80029e1cdad7fa5b389d28000a78836b4002289318e800289abc276860007822a2c4b6600050001bbd7948b93ad928923 else 0x68687f0002a000f7a02041c717700006000406a631d0005f45e5220009ec7e0923b9f34000a00038d1d01a00064462037100b38000880017ac0094bb6b590002a8f85967562c000ff0ec6e000144d5e1380029e20dad8f80007562cedad64b2ca8001bb17706000371802a900074c3f048000a26af09c0000021652c502f28001188777a80e2c00114498e7400000906d6c43800407168a05e577a22000e987e092435b090fda3b28001a910))) else (if i < 367 then (if i < 365 then 0x8965135784edd0be8bca44001d64010444f2458000b0007aa3e520000bb87f230281ae1d944800245ab90b0006b835112d0c000c7c55c0a494fe4600041db138d52900000316ae400000221361d66314737a2e5b3d0c00081857210000f087ca40001150004638e44f2ae0e0003f98c51c000d709ae25175bbd79488000411a51c00006b0790e00016270a3400015d290700042d0180800057202816000ca9218a00018f0d8c900034400f89 else (if i < 366 then 0x8c400d16000ae400621a1a1fc000ab1f00005f896884b8363240000066a2260d9c38000d8dd0001b1926205758fd2106cc260006c000004d8c9482c17c79135750008fd20bb8dba1a43000181d5c84343286800150000013e520c7cf7aeca258f80000284800436b15386e40003372e0000087e090001ff906d680028d211960005c2440308bae55122451740000048aee2c82fa0c5dc3575e518000c226dc51b18000d8c92ee0000008c else 0x52900000b16ae40000042154972c000602541da020d00000535012000b96cf430000004d889393acfa36a345d5e50002221a8e086c3800172d644637a41d99a8d0000063e52000000cae42000206189c6821a2a0000c0005c48c51c000d709ae25b1a370d8893c20002b90881883b4041aa8c0011882d5c954c00043bc0001a8890005cb4e21800017eab8396e9770000832f3f74791300002e1040e0001da70a3400008d290700032a48628)) else (if i < 368 then 0x70038b2e8eee880004daf1498e70c8003ac8098889e48b00016000f547ca40001771710600035c3b28900061136f28d0ca1a000540013cd858b0003db9f8240005e547022000f38ec8e00014300116406c510001d00058565b42000a26af09db1e45d85db3630001b19280d7e40003a000834c3c7c97561596d0800245ab90b0006b835112000e1c0066c001952431434300043f957029250c218c40aea000400023f4d8c9061b6eaee0c else (if i < 369 then 0x86e76370000a26af09c0022191f8f8002ce1b82200080244030000dae740680014f106d68002860052c0005a862036000008a248e3f18240017000310a1fb46c600036324cc2fc901c58000005e44bc51ba246f930007dd80e2cd8ccc26c648001bc1d8548000001e9b96c600036324cc2ab501c59ef58f800048003089b7146c600036324bb800000a300021f2288eaf28001ab9170000038b2e0007c6880622e8fc9158d8002fa2f291 else 0x96104b1747e40006c001f95f6dc2ee0000008c5e54b53572200096abca44001a30e80d00027b1f82400081538b2e8eee891be4c001a2d088d23bc6a80013000670511460007c68806237c000e2cbc0a8003ce915dc84c5f4180000026a2243b1c381d0d87d3098001b00000136324d0c1f6c7c55a181d52e0a800303ab90868650d0002a0000387ca400018f9d944b8e2ee0000c00080d4c63a00112a6de500017d1794880027b1f824))))) else (if i < 381 then (if i < 375 then (if i < 372 then (if i < 371 then 0x87c00b3a000d106c6480018de220b80030e236a300053244030000cfc836b5f74002038b0002148009376d70859654000fccd6694001b752d4dbb6bc0acb2a00068836324000c6f1105c00218906d680030e236a37dd00080e2c0008520004dfddf99acd2c27ba40003a000539006280011b0836b621c002038b00046cb07a50e30005dc18bca0006ae45cfda20d8c900037caee0c8a05e5000221b4d106c649d94000d4880003089b714 else 0x8fc6090005c0011b2c1e940018850fda45f000268c000052600132002d106c648000e70d8c947c084c071600091d8772efba00101c5a28dbf800098002f72ad2c0000043c26a000d106c6480016720f114764008003a10079e620361feb38da0880021b9d8dc00036b9d01a0005135784e000a78836b620167000110003681e1b50000f87562d1f0cc26c64800144d5e1380000b9e9b90000015dc181f2d106c649794000d5c880047037c94) else (if i < 373 then 0xa24a41c000ca9218a00023101d058002b90368868687f0002a000c7c0b024001ef40cc838e2ee0000c00080d4c63a000be8bca440013d8fc1200044a8131400053c41b5a0010dcec6e000144d5e1380036b9d01a00088647e3e00002ca248c0016720f11000299220188ec801000740010fc7b2840020dd880d80048ebc8978a37440002600000c7a6e63f1824001700046cb07a500062143f6917c0009a300001a20d8c9003a9300399 else (if i < 374 then 0x2856ce77b2cb3e00069472098000fb88add000450105dc0004e218fb4e9ce1ebe49400138860002fe99b0d1d48c56b81c00001287a1c001994d10c8001d6322942e53ad00016000ff47ac8000000cd4c80002102910991550e00018508aa4c0e221ad0814884a949d68000b00073735320000840a4426455108000600022f33d080003ac36f289ae8fe000393140014d46a90a1b1b11200011a364400001bc6947000030435838000e59c28d else 0x63e34a3910a00080e5e275bce43cc805ba99d41b0006ce55a2cfbaab8000380013d9a3d20002ee1db9000062e44030000c7a7ac80001515f5cd0000009e1b560a88e84e3e000cee7506c0010edef0abb6b593c0aa00052a3361a0009ecd1e90001571ae073deaee140908264e53ee220000206a225c9c000dcd1800004bf10b9250004e21800104c6ae4400112db0ca2e62dd0001000052a0021a0009eccda90a19c56144b00021cb47a4))) else (if i < 378 then (if i < 376 then 0x4f628c48000b8488062449e44cdcb8004131f71100002b45d1200089601c521314a800068002ea002ac0006ce8512cfbaab8000380013d9a3d20002a2beb9a0065dc3b720000d9cab459f75570000700027b347a40005457d734000bb876e400018f4f59000c3f7b972184c4950001a000ba801cb0001b3a144b3eeaae0000e0004f668f48000bb876e400018b9100c0002a2beb9a0000063c36a000f547ac800359200009aa0a1d80015 else (if i < 377 then 0x5457d734000f78786d40010d800c90022ad8001d0007156f72c00eb080128400156c010e80031e1eb208804e7000451f8c12000b9fd58f8d28e0002c2001210007156f72d1009cf15c88001c55bdcb44ec8427d190006ce8512c000a8afae68000014f0da8003952201879255c0001c000bb876e400013d9e21201a3d51eb2000072a44030f24ab800038001770edc80003a99d41b0324f67884800092a66c34001571ae073deaee00010 else 0x8ec85653974000a8afae68001ef0f0da8003442a61200063e34a38000e2b0a25800156c098ec40273800228fc54d0005c000e54880600021e6138fc1e0001eb200006e38705312f114000c62f0001346044ebb40001972c6930007c000b089f485ea1fa400178003c8801170007445972708afbcc56e400229d01c98003a429cba00065043f68000ca6c82b400144dc1d38003ef315b976d6b200055205228d3a6c001770edc800031722018)) else (if i < 379 then 0x63e34a38000a8afae680018b9100c0002ad8009d8fc6097f55c000e2adee5800139e2b910003cac271f00086344c6c00107098ea4211ef0f0da841b172201800043600024edad64aaca8001b3a144b00027b3c4240007ef72e4208aa8afae68000128db8480024a81e0d68687f0002a0009ec7e09000157009c70002ee004900005457d734000f78786d40018f8d28e0003952201800055b0303b1009ce0008a3f182400170000379eb20 else (if i < 380 then 0x91291d3372e00002c8ba2400177001080072950000d0006ce8512c0008767e054041825d9970003442a6120005457d734000012786d400144c00d38002950008d6867823f02a00e8747e0540015340097000340c271f00152a60a1a000a54ecc35a19f70fc0a8003ee1f81568652a0001a000d9cef658001535d997305340c271f29552a3361a000d708ba24001770edc80002950090d0004f678848d0d0fe00054001610035080021b00592 else 0x5c14403000107ceb0dc00206902140002f731eac82500051c7b2052280006e1b9f96041c00042e3ea3b0005973d64000108a80e5e02e248000dc91c283ddbf0005f9002260010c4c82b40018a612183b6b59266aa0008d34fa3200107098ea4001d20f65d01ca73c572200043a0012a042a9b138b80018f8d28e30543cc271f0007158512c000a5400235a19f71ef0a80021d3de1560a00084e3e52c0007ac81e62471700b80029519b0d)))) else (if i < 386 then (if i < 383 then (if i < 382 then 0x85c7d4760000287ac80001d1000cb80046cab0250008507bb7f0172292466c0023655812bb6b590002a00072a4403000000a810a00197b8001600033b8009b0074a20076e03a944000ddd5c071471ec1280028e3d0005ee00259221248000be40a450060d80033b8009b9109249025e02a94402ade115d10000b8000032b02576d6b200055220fd2000bc001705100c0002f731eac9029140003601b07ceb0dddb5ac800154883f48002f else 0x8d98f54a000e54880600457b80016000464a04280006770463605c944000ddd5e401471e80032821fb40008626415a0010649f8f0001fa00f09800314c243000077c6d656000024fc2c8002171f51d8000031eb200137440002eedad64000a80023663d528003952201882500051c7b20122806a6e115d10000bbb6b590002a9107e90005e0400010b294001705100c00041f3ac3700081a40850000bdcc7ab2094001471ec8048a0131b) else (if i < 384 then 0x7077e800026000f2280e5e02e249a74dc1e0001eb200006e387052e0efd00004c00247101cbc05bcf34e9b000584067420010c6898d80020e131d48003a429c3a0004e78ae44000e7a0bccc001f79f0dcc4bc6d000318bc0004d180000ed002a64001fe8f59000032821fb40008626415aedad64000a8001fa242898003a200217000629848600010649f8f0001df1b5958144953f0b2000629848600010649f8f0001df1b5958004953f0b2 else (if i < 385 then 0x8a54fc780000250b29403e0f9d61b80042e3ea3b0000053d640000e880025e02de50210dbb6b590002a06b79400036012e5488062115d10000bbb6b590002a9107e90005f204f280006c001705100c0000022b02500083e7586e00114a9f8f00017b98f564373f2c08b807183e7586e000e891265c002114f590405bca0001b07272a4403000123a80e5e02e249e50d80043cc271f00055b00b3a000e90a70e800139c011100039522018 else 0x7e8038260010c4c82b4001df1b5958003e2006190007fa3d640000e880085e02de50000d800314c24308978da000631781429a3000018a612183b6b590002a8978da0006200112687ed22f00013460004c953f0b28978da000631780009a3000018a61218000010a1fb400000e7e1640010b8fa8ec000010f5900073a20001776d6b200054000f2801e6e096401471ec22ba20001776d6b200055220fd2000be409e50000d8002e0a2018))) else (if i < 389 then (if i < 387 then 0x92a7e1640010a0f76fc0de45248cd800314c243000065043f680010649f8f0001df1b5958004953f0b28978da000620011b31ea94001ca9100c0442f70002c0008c940850000cee17a6c0ad2881ddbc4e21d0001500063e34a3818ad9cef658001c54ff0b0002950600d6867dc0002a000c7c694700015341117000340c271f8fc55b0003a000b0816c8400218d131b00041c263a9000748538740009cf15c88001cf42b598003ef3e1b9 else (if i < 388 then 0x74853874000fbcf86e4001611dc9080043cc271f0004e783c44000ab601a74001ca9100c0003c88051770774400026edad64000a8001dc5335980041c438290008306415a001124d3a6c0014bdb595800434bea3b0006298486104ad3ca38f5c1dfa101c9800431a26360008384c752000e7a1b2cc0021899056c5e800268c076d6b200054000fd12144c001d10020b800314c243000077c6d6560010649f8f225e368001880032821fb4 else 0x7158512c0010c6898d800234dcb0c8003fd1eb20000748538740009cf07888001f79f0dc80041c263a900073d00f660010c4c82b5db5ac800150003f4485130007440092e000ef8dacac0018a6121844bc6d000318bc0004d18000200087ed0001ca9100c0004953f0b20008507bb7e0c8f292466c0018a6121802a3be36b2b0005f90f6261eb0c4c82b40014a80d06b433ee0001500063e34a38000e2b0a25800234dcb0c8003fd1eb20)) else (if i < 390 then 0x5ee63d58000e90000e80023ed02140870873f0b200074860e74001034810a0001df1b595c883f48002f0005c144030000bdcc7ab0000009f85941280028e3d9009140023704a000a38f640a450000d88b41f418b70005f900226000e9023ae846939e2b9108da73c57221589084fa32000d9cef6580010e847cab05156c271f0007a50597c000a9a040b8001a06138f8002953050d6867dc0002a000c7c694723f156c000e8002c23b921 else (if i < 391 then 0x74800b7400108a0065c001d1051c98003be36b2b11f11e7e16400114e80e4c001df1b59580047da042876d6b200054000002fc2c80363663d5280646cab0250008450052e000e882784c00183a3d528003be36b2b76d6b200054224224fc2c800229d01c980030747aa576d6b200054000ef8dacac0023ed02140000003f0b211772a4403108b2380005c00229d01c9bb6b590002a0000078594a000ef8dacae441fa400178002e0a2018 else 0x92a7e1640251b31ea94001df1b5958004953f0b20148d98f54aedad64000a800229e428980030747aa50007440062e000c53090c0001df1b5958004953f0b20008507bb7e0012292466c32de9602df000314c243000077c6d656001192810a0001e94015f0004953f0b200072a4403023cbdc000b00019dc550d8612510613700092a7e164000e54880604d97b8001609c33b8a79b72c7a50007c0010b8fa8ec0018a6121800000c9eb20)))))) else (if i < 414 then (if i < 403 then (if i < 397 then (if i < 394 then (if i < 393 then 0x6536415aedad64000a800224d0fda000452a7e3c0000088594a000ef8dacae441fa40017c813ca0001b0005c144030000e90000e80017b98f5600047da04281061067e164000e90c1ce800206902140003be36b2b9107e90005f204f280006c5cd705100c00032821fb40008626415a0010649f8f0001da0094c8003fd1eb2000074800c74edad64000a800229e4289806ba20001700062984860001192810a0001e9400df0003be36b2b else 0x7c84fc7824d254fc2c9cb1e94001f00042e3ea3b000629848600000307ac80001d20029d000431320ad00a8450002e00114e80e4c00224d0fda00047da04280007c84fc78000ef8dacaddb5ac800150848003f0b21178d95604a0010c4c82b4002114004b8893a2093130008a74072600112687ed1db5ac800150003070022500077c6d6560011f6810a0001f213f1e0860863f0b20005607e1651eb14a9f8f2116470000b800453a0393) else (if i < 395 then 0x76d6b20005400114f2144c001d10010b800314c243000100043f68000e5488060039df1b595800314c243000089343f68001192810a0001e94001f0003e427e3c12277c6d656edad64000a800229e42898003a20041700062984860000c1c05494001df1b59580080021fb400072a44030001254fc2c8002141eedf82b3ca4919b0006298486000112687ed00018380852800464a04280007a50027c000ef8dacac441f213f1e0003be36b2b else (if i < 396 then 0x5ee63d5800114eb2e4c0019410fda0003ef315b98457440002e000ca6c82b5db5ac800150003a40023a0007714cd66001064c32f00100021652882bafa263600060e8594a000ee299acc0020c9865e000314c243000077c6d657220fd247ebc001610305080043cc271f00086344c6c00107098ea4001cf42e59800273c57228978da000631780009a300001f79f0dc8002a682bae00076802532000ff47ac8000218990568003a4006ba else 0x65043f6825eef8dacac00183dad12c88af70002c00067769d36000945062de29e0e21c14c22bc8800177fa6f300032000dc70e0a400229d01c9800329b20ad76d6b200054e58d26000fa25e228001880032821fb40007714cd66000e90006e80018a61218000419484bc01b11c8594a000c1d0b2940018a6121800c419484bc0db7915bf2f0780007ac80001b8e1c14c4bc45000318bc0004d180ff4ed000065cb1a4c001f0002c227d21))) else (if i < 400 then (if i < 398 then 0x7714cd660010710e0a400229d01c9800307000a501362984860000ac0fc2c80018a6121800032821fb48f583214878000e9000ee9cb1e94001f00042e3ea3b00062984860edad64000a8001dc5335980041c438290078a740726e58f4a000f800003d01c9bb6b590002a00060e0044a000ee299acc0018a6121800041c4382913865043f68000f5afa8ec0018a612180003b8a66b300083887052000ac0fc2ca3d60c8001e44bc6d00031 else (if i < 399 then 0x60e0014a006c53090c0001581f859000314c24308f583200078000ef8dacae25e3680c588003b8a66b300060e0024a000c53090c00120e21c148003d6bea3b000629848600010710e0a4001581f8593963d28003e80b91469d36001124d3a6ddb5ac800150003b4001990007714cd660010710e0a455de9602df3963d2c05be0006536415a000de601e64001d20011d3b6b590002a0007714cd660010710e0a401629d01c9bb6b590002a else 0x5457d7340004b2786d400144c55538002950a88d6867820002a000c7c69470001c56144b0002ad8451d8fc54d0005c0010f309c7c00139c1b910003952201800058406b420010c6898da2f400134600003ef3e1b90000563d640000f2204c5c0020c190568003a4003ba00074401c26000c53090c1db5ac800150003b4001190007714cd660170710e0a403ddc533598003a200a9376d6b200054000ed001264001dc5335980041c43829)) else (if i < 401 then 0x50d5a12ad0c9b000036145821200b0004359a80900052644732556f96be239e10000008400023ca020d63859c370450d60006a025039108000626bc62af88e00055328b100005151882c0019e9388600013b9b9a30008263ee220008964ca50001570978700027b12da400025a45d12000bb8012400014a80186b433ee0001500063e34a38000ab6004763f18240017141c771eb2028258426242000d9d0a2589f9515f5cd0003442a612 else (if i < 402 then 0x6e12d934a38ef00006a02535e315b3070000111f2900004540181800001c81c20001c14dbca0002ae0028e0174d700012000a1ab4255a193600006800283240168dc7a336224000c4f13c340010d8d88942daec8001300086b8dc12a82a1a00055de4001e0cd476b172201800055c0011c8bc9ae57e240011e501068001f9a841b45e86b000120000046dc511dc0012849aeca1b1b11268550d78a2a000aa400a200017117c4700026bab789 else 0x83d640000b906de500018b9348c0004512e39d0003f350836d0ca1a0005400177154860002ff9f82465c72a51422000b906de523ba28971cea072ee0000c0008a24c63a0009e6cac580016a1420d8002e41b7940008ee3d640000a4e88e640010d92589393bf1236a352900000e16582000016200011e50106a6c44f0000e45e6cc0001200000263a415491515bc60000019eb2000000138b2eaa4dd8ade315491555bc600048e1c597)))) else (if i < 408 then (if i < 405 then (if i < 404 then 0x87bc3c36a000e3474068000018f5900003de1e1b50005135784f100b3800088002145d58b000397319a183c84e5253f10b04f0ee5da18000004abc1289abc270005c8001291231dc7ac82245f34f5900002e1220188307be41b5acf4aa4000300011795bc48000031eb200008a24c63a000b90e4650001670f9d1000317269180006ef51422c5b0a2cac58002289318ec772e43919400059c370440010d6eca261b80018a9c30380000588 else 0x86b7373e52124abfa000314a9bd00005bd539b9f2900007373b720000c5e806340023100d45800014c758880c5dc0001800004aade24002289318e800317220180005f401d231f8c12000b80013d95dd200041820dad68601a0002a000c7c69470001720038a0002ce33aa200087e6334200109c8fc7c0023b8f5900004288021600062c3a034000a26af09c0000394491806a1b47c1200078f3a034000a26af09c0000294491c420001fea6) else (if i < 406 then 0x8a08b57cd22000b8488060001e44cdcbc74a89abc2700001234a38000e6ebb840001ef55bc4800406a631d8ee5c800028000be8f9a440013d95dd2000413c7f976867dc0002b100b3800088001c68e80d0003681e1b50005135784eedad64000a8001659d58b0003972ab2100063c8d024000fba8da8e27549a378cb742fa000110008e24c63a001144ade25a19f718f8a8000009a8892b22b234a3800000666c36495bb000062c8c620000b else (if i < 407 then 0x8c4370160000046a2259d56cc000a492b7cb3d0c92500059118b66000df25177184400083428000011545d00035722f98eeca3275f3156d464ea954620000b0007373e520c0f13c00020b1e1acd44480042d015880008c460716000a54806340019e804464062ee0001000000c35212000b900125000228971ce8003a62bba40008278ff2ed0cfb8000540018f8d28e4643718002988777b0002c000b38cea8a281f363cc88004512e39d else 0x425ff3f0480007ce03c20002310dc058003681e1b50005135784e0000129a300002389718e8003aa803096755c800028000cf40023203177002483433c1000150007375dc2001cbe802045d95cdcd48800033d0030c80c5dc000200011d26a4259d5720000a0003aaae31d6867820002b10eef6eac58002389318e8003aaab7896755c800028d0cf04000540017d0008880039baee1006b63e34a38000e6ebb842244001100c44ea933c399))) else (if i < 411 then (if i < 409 then 0x1151246000a26af09e21ddec000b0000049a90900000772710d0cdb00005400156d71ce8002c92ee0c0005c801428000f107e090002009100c450395448915925525dc180008bc002223a564577064748002c88c45d0003572302ac6e66e5c001f896c840000051a9090005925dc18000b9000c51a19f70000a8003c41f82400055b5c73b10eef60005a1300023cc8b95401220186867dc0002b100f107e090001645770634337480015 else (if i < 410 then 0x5dc55218000bfe7e090001a7d8e5e80043ea691800089f5f034000e54a28458b53cc000b00028631eac0007d5512471c924c836b5a6e0bc0009c75c620000b40e5dc00018000a4e88e64000e3de7488002c38009b85475465b42000ae68fc7c0013d8fc1215c366a0397000723007100011886de2e03177000060002fa0019100072a44030d0cfb8000562013d8fc12448c01220188eb8c436f16f7a8bc000223ae3121ac58004621f28b else 0x73703e20000076eca2400203571ce8002e4018146867dc0002a000c7c6947000005408c4000401220180008c460717018bb8000300017d2244880041820dad00087e6334200109c8fc7c0013d8fc120003c8c3b970008510072d1d9002000e800144d4e138003eea89238fc6090005d146e880004c001a2234094423d035ca68ec80100074000a26a709e33595400144423d01fea60005ba00316cf4aa4000300013cd958b316b77a8a11)) else (if i < 412 then 0x496000361249ae00086c39570f7cfe862010000020752100036124aae0008a0200023150d8726ba99b5c0900000f45010c4ec2800034000014d10ca1ea9b0000f52200500012000eca6a440001ce138862ae2e22998e43d5360001ea44000004250800023105a72462b660e00076535220000f96a663800139230c5c4ea251b7146276144041a00058c6323c000a98aa4300008c0a8070004a40c71c0001227ac8000023100c68002ce030a2 else (if i < 413 then 0x75d4041a000b069c23000000568c4b36affa3a248c555c6cc1c0007e6c3e6c00172d38460002c8ad1898dc00032524000f9686c39e2cded09c7abb000000867784205a312000b969c23000164568c4c6e0001929278d5e53ed22000b466a224b69de0000300024b1b1920007210011f24ab969c23109e315ae07000005983064020003740e00091e002223dd768f7898000021a8090003f13ce1e92c0006c2480014cd0d8723bc179ef13 else 0x4f24802c00088600c2568cb40000400024b1b11271d8c600022d708e000038001e8cedc8428a902290f0005a335010b7400063a420993956008a21a10000090005a335010b7400063a413940015fc8c832724628e77800044312ae4000b4620000dec01c7800334992924d90003351a00089cd9839e2c000d0cc8002793671662d90700022b22b969c23109e315b3072a980000a8800000e34332000aec00e196a4001238bc1f80022c38))))) else (if i < 425 then (if i < 419 then (if i < 416 then (if i < 415 then 0x7224271e0009c0d86500014056a4b80024b1b1920004f280e2cde80009c2323e6420d0cc800004aa30655300000310000aec686640014a90106968ac1a708c0005a33511318a000d7038000b48fb88aae0002708c58352a6f41a00089400450001cc138462ae32c4628e0006f94e118000a446dc25570001960721ea340000f55300000110a9c9e50a2580000051bc8b0b2794289649552a0001b24eee66926e310000070380000580806 else 0x2d435b3c0000ea12e100000ed36c58002948118700052a4031a000b600221a315290000700027032c1400000761a2e000b520142168c00000848002a92708c80c6e43b720eca0006a442215b84000e45040aac0115a900000310000aec68664001f4d68c4c13abbbfa240005a3351130da0008b0e1731f6cedc80002b9003080007594a41c000e4484e3c001549384638e3c2000105a300035212d10a986c64800168cd44480035c2520e) else (if i < 417 then 0x3896711273c9c200031c55b38cc8b1ae800202855540000090e0000085f820000e24d404a9480020f8b39e4e100018a36b52da85db9938400062948002a90b00038950e128bed0c01c5400002cc2c580000497e0859c0003e744896cd60005000138400461cf1c49d9894100004681ee2a00066458000e24ecc4a7c343000154758a835c3cdcc9c2de830000e259c449cf2708000c5f675d39d320005c860014000b74b88180016c1908a else (if i < 418 then 0x5540000190ea5200002a2c000e259c449cf2708000c00000e3322c0000065f8213212d00009a119c50001092258031f228be00000a5525400000ca2d4800295975f600039d32dbad887506db75ffcea0dafb0001ce994c37bf0001e92a0008d051b75b10d24d80000117e080005f334f3ad3adaa7506db75b54ea0da0f9c4800093500002fc10cf49c2a1c314a8000c2c58000021d41b0007ff2fc1000071276624e7938400064912fa9ab11 else 0x5404b400026b3c000b5a7139000227870002599ee3c6790004ef248971c0df251365bd0c3c68004339c8083a23500000e940d360004d17633000088001deab78c0005ba31e20b1ae6668a680000d0c406800008202850000012fc10b467126a2254a800136c5aa92708000c00038950e12000bec73a6554c00230c39fd00026b8e49400000228000bb066459669b10ea0dacc0002191d00038a00220ac69900004d4c4f91274c28b2bf98f91))) else (if i < 422 then (if i < 420 then 0x410546000160000028a221091ff0cc8b0003fe1991644b58a8e028bf600000cd000000d51c39d10002a98800045e8671283ead6c0e2d4a55ac0005bdcb10b9b9000056b43e1683e0000322400002ce4041d12410000752a4d90001a940ac60004c000ef8c3c60003f99a29a58c0007e3380020007baf00016e8004833cbb7a77920006e74323a896cc8df2511794a400038001df0050c4d90000031a89c00000239479b30d70f28ec739ae1e else (if i < 421 then 0x6bf871694300009667baf19e40017b493490003a1320008440021aa36000a565d2be279e4c70002711878c76f5f039f3495e000b7638001388008637a3ac8000d5f36e74323af26de861e34000058c5c79e70000070741056b000160000148a22130c000d40480000239b9000073334534cf2aae000493117700006211bfe199164c400000918e6600068a6989c001fcc6b3caabb301245e00086712b90d871c051310ef800062218002b789 else 0x5c90004ef24c26f926926c001178e40422ec914661100000c671129868ec0003d09c00002473e58001ce993ed0005a522b4600000420e7938800062fa37a1878d44b5b30002873c9c4000317d4000c3c6a7c342b4c155a35bb33c1000002eb46200012d0038980046fb29170004d36b44aa36000954352f0000d70f2a0c21800156338ad000429fcc68000492bc0016f072f6a598003c4625f30003a000a40ae23d351c6c000e2192710000c)) else (if i < 423 then 0x52000000224ff2cec0028909c0056ec72578002dd8e7937590001ab06b8861e30000074c2c5a0f80000d0900001039010a5400000235c4639cd70f2a02b1800134100000071eb3c000002712a59e0fdd28008001eebc4af86a0001ccf20009de49dbd7c0000d1cfa711878c0004b13dd78b940009de48001d6d50d4213b648000e6515e871b3895e000b76394a9d6400068002711878c40f0000011ecf205c9de495010a000098002589ee3c else (if i < 424 then 0x54e0006ce2c998b120005000160cc3c61cf2c88000900000031d20a6c8d06323c000000c5c79c8ab5a6d8b3230000650aaa80000381d4a400136c5800006338895a345e000108a28ec0003d09c000cf073c58001ce996790004ef24e8e00080834e7a0b0000622e800001916a50005713a000ff8664594918ee2b0fb9bb8e18f900000055a310000968d364c0019e1ad12ab08003a1324aa0005401abb51ce6b87800001163992e80000010f else 0x270cd0886000004815008000cb839c88000008b41f0106711200001465e540013dc0044413297491118e500033c1c000eb2808340012d0da8980023bc33898c300039d32000e8a69470001351230ba4aad9c331400043b00b1a92a00000e50000010ea0da4cac4800166a900000112c168ec6323cd4230219c4432b62000088e592733c1c0008d06323d30d82c00049a84604328800000340410000b0661e30e78000d404a9b23b18c8f)))) else (if i < 430 then (if i < 427 then (if i < 426 then 0xa3dd78d4ed5e000562d8000de52244a560002158200044c6c000ab09de4800153000c8000068a191d0006843824c86ec4911a3912e1f9be4a353b578001544b0006f928000cc8864762d8000de522c1000226368667bf5983273c000fe62528158c0009b53b57800150005465d616bf6a8e000d1678000ea8e45b0001bca40005ba00120edef469de49dbd7853bc90001df1878c39e00045e12bf6a8e000d00015190f85a7231244f0e else 0x40f0000011eb3cca2754700012c5bf5e0002f9a191d4278600001cc3000083a652ddd41e28aa0f80022f094af0005bb1c930c480163c000011010400025a000934775404a1120009667baf12be18227870002711878c39e00045e129860000043d3ddd40000aa57b122dd8e4270005bb1d0c0962dfaf0000004c5c7a621df1878c0000224041000077c61e30000058d14d1cf0002c6895fb49200068000a8a87c2d28158c0009ac60001d51c) else (if i < 428 then 0x4820004db16a80968d364c000004c5c7b23a619a80964700035012940000d364d2092d001059918000008545e0025a3128bc0000042530c000c5c7ac1b701878c52956b00016000b9863a40000010c5c7a620001878c5140003bd229d2000c12b955e3713bc92c18001878c51f8dc4ef246460000401400004cc2c5800007a020841f00000612a80ac60004d26001800078002589eebc4278600001cb940009de49cd5944ea8e0002711878c else (if i < 429 then 0x4d9000450108869868bc254a95ac0005a012d8000075fb54743e6800002c620110c0dd8000280000198b8f0004c430f1873c9860002503d5ad36c5a018000008752956b4db1600077c61e3000151936c59cf00000509000004404100007de68a69a8d248001a2120004039644b58a6f928d46a8e000d1678000d28e2b1a5a000130004b33dd78896e60df25000168d01042c69f79a29a4020000180e00001280820c8c00000c2ad18001a809 else 0x4b68430002a0000006ee9172d389d406000000a0e995cb4e25f618b9ed9c66658c8c000e0c29c880026d8b5540000060ea44000ce2240016bccd06800001228084af0003921caf0f847109d2bde4ce487291000338890005af3341a0000028a0212be278e48737a2710000c3ee5f400022a4cccb09664000224c1051d48000068d35d5af0000a00000480a10000000c5c7a952b5a6d8b0000053171e79c0000021d2615ad6c05a952a30000b))) else (if i < 433 then (if i < 431 then 0x4c300000212a660009ae39479cd1124f2243d9a0e995290000031683e000002254cd71135c72a52e226c0e4485f641d3200003860828c8c000e0c2a00800007073a90003341aa520009b62c00206401442910001a80971100035c3c96c878000555dc000ddd22e5ac84160c5225a30001296c878000555dc000ddd221e8004940f47500035c3cd6b17683a64ea4000cd06a950001858b52200077812001032b4621c44000d70f2578000018e else (if i < 432 then 0x669679361240000a85ee18000098d5420002181c185375000304148020006e81c000d74cd06c0c80019d8800000f3332ca5200001a2d07c00000c4a9980026b8e0003be5c418d991ce8927800000cc74821e80018c8f0003be7fc18a3cad2892790f4000c647aa500026c0e0003be5c418a3e94e00049b610f1f70aa883d59dd3377b00035320818b12000510f4000c6478001df0040c51f4a700024a520000042d07c00c0004b8fac823a24 else 0x41f350129280006dc500010f0cbca9d48002ef8d4278280001d172e786926c0010f0cbcaa13c142dd8e0000043171e00079c0041ce880011444261a2f2d1895295464db168200009b62c00002d51839d1000002083a90004031a89c00067a3958c000c9c9a72a14be0114690003542075200080635138000cf072ee0002f88c0005a391512e2aff8b865800191c0044ab922f002083505a30001000000463a40001771150624bb3c9b092)) else (if i < 434 then 0x4af0003921ca66fe200024e4400000459d9a7219d884028e730b0e00000862e3d0090f400039c8aa30000b00044b36f28986b90fe224e440000085a010002a30792841f7f1128051ce0001e4a0001fc44ae42259b7943220000170a00000a65c1c000004cec41d4a6ca018d3a90004031aa9400067a3a0a13dccbca9e70000028f00000133b10820ae51ce2c0010f0cbcaa080004738b4e48285bb1c00001067621cdc000d5080002b94738b else (if i < 435 then 0x4e1002180008aa66e5d52971122c72a51fd2458e67a4e16f418bbc00096c562a0ba639c39c28000038700047933b1000091e00810000cd4d404a57a998000e0003ad6ab16b4c8206323d68ccd4d404800197000845293ad30b16a531ce6162ce1000001838002b5c738b00039148a0874400072020ea40011846aef21d800152e64103181e0006e8006114a55ac00059d48002308d5de4b66262aa52ad69142c000044d54219100000285 else 0x46900035420c48be267839150000d5082b92e6000080005a356f1275200080835138000cf073e5bdfa93190000352f70c64400005014ea40000706800001807844010006140e818758000517790ee2a0aa4780019d884b600032f2a00115065c1d528000cf4700022180289391000818169280006dc500016b4ea8e234c8c000107194e531f227220010302d285768c9c9a4a2700001400000836f171ce000a521c000014cec41b70001a809))))))) else (if i < 479 then (if i < 457 then (if i < 446 then (if i < 441 then (if i < 438 then (if i < 437 then 0x3a96ab5df1a00087865e55479d4000062a54142dd8e00000833b10000dbc6a025cdc000d50824a0001b71400057200116752e2200434ea5aac0006b2a0002a1a85df43c32f2a00087865e55179b792dc480000218b8f0793ce0000e9889c40003110c0015bc4a0faa326d8b51e000007180000029c41d1a4208d50820800026d8b915647000126a0b4600021770000c7481d48422020d4100004db16000008a8c1ce8800000442722f899e8e else 0x3840000040e74400000420001280c9c99d48252308d3a90494041aa52ad60002e431e8924141c20df9ba073840000740e752c4e00034000cd5b70480023ca02084ff4873b2620000126aa10c880000102a578001c90e5337f100012000ad263c40e441c0f94583900018b8f39107700017250000fe22500991c1e0399100000b8500000332e0ea9400067a39420002190d83b9fa19d883ce0000071e000006676200010f0cbcaa082b90000b) else (if i < 439 then 0x6735b3c0000565ee18c8800007029d480000b0d00000301308818758000510040002243ad323418c8f48f00033b1000001665c1d2d8000cbcaaa500019e8e000443003129280006dc50e440020605a34ab50341039100081816000b5a754711a4000c78824a0000001454e8525c32c96c00065e55250001b0ca1c8b55c0c0b4944e000028bbc5d496c54e141b4000383a1970000452900030b167dc0006ac46489394cec400000380404 else (if i < 440 then 0x44e6b81c978000a565c0017c0d14d401b4d1b3a13e55cc35420a54000ae42e279139ae070000721aa84529546000160008966de5000000d46041f28001aa100004c33b312dc0884aa43000130dfc44ac8a210000c916633367420000146aa100024a1fc44ad3000001070004263da429310071882db811080006294aa30000b00044b36e28aa4000a30200018ccd9d0a4ac162300d4020000cf0e9300009b62d5c8001140422f323ad189 else 0x4600004791a8e2a966ac451800010106a9500026d8b47138e35622aa80000061d22c00136c5a302270000d75947940410a531886162c000038bdc30001ba805840000064601a708000c281ce8923c00042d300018c0f0004c40011881cad71882d151e1132881c20000008752a56b8c416a52ad60002d25512cdbca1c20000628748a56b8c41600002e62e3c0010f403038002011aa846270004031a000986fe22554c00001842950000020b))) else (if i < 443 then (if i < 442 then 0x12b35508a52a8c0002c00112cdbca00000128c080004c455218dc073c7662400130dfc44ac8a2148a8c00005335508001250fe22400138645462d30003700740f0008c41674400000221bd17f518068002fea020d4954e036e2864400003014000dd802022062700001436e7f1000127660010ce20000008bdc32aa00006c0746947b31d200008f663c415511a403838001aa97b8600054a0081caa80000161d1a40011ec847280000108 else 0x8e503f00010000b46ad4251c0e38d58880000b17b86000375052080000228c034e1000000838002131ed210456477f112a52ad60002e06123c00040002259b7940000053181e7ca0009f640000005d944c8c3d39a51c00044292518d349587b4840013100046370261bf8890004c37f112000f4e69470f9646132881c201e0000752956b00016bfa9c305830000034c5c780021e8020700040235508c4e000806357f5310000648aa61bf889) else (if i < 444 then 0x6a57ec34d3adbce449603d4a400000c5b3d0004160c6de51f0001ef16ebaee865f70000cbca8001f31dc1061287832b280006ba602152bc000e50726c000189084187590000c00000a75228000f8ce5cc2948000020b000470922231400006a641b79891e107a949c88000b8eb3e6353200002d65ec0c000224c10500001c9ad9e32200000a0a0006ec00411031380000a1b73f881e890003552f70c000a9408e395500001283a3480023d90 else (if i < 445 then 0x3e349d3000094e64a494a400000858003f61a69d6de7225711f00a7cd16840000dd955050000071890848200000416ef00000041943800172c63463f99cf9a4ba3e349d300000026e28800400d67430000010020668c7f3000351687cc84441cdcf9800082872c94160c6de57b0001e960eb27263800123c0103294bbc0000b00000132b28abae15218a1a315f5de4d0001f1a4e980004a7325240000087263922c0000085b3d0004160c else 0x32f2a00088093a60001fb0d34e800356a580f78b75d0003200083864a499e9a960b060003ee1979500044049d31080ebb000640000f8c446800001980854af0003941c0009b06242110d062394300000b19b97000376554140000126242120800000c5bbc00000c0600074b3e744c4d18065e54000004dc5100080d2ce8600074b01b0d00a7cc00041a31fcd088d000247802065297780001700a7cc00040068000caca3462bea559a)))) else (if i < 451 then (if i < 448 then (if i < 447 then 0x6de57b75b1e95f1ca7263906110c00030002ce9f3a24d90003111a000008752292080000085adc0001a69d7ec4403973095e0d4726392bc000cf472411c88340b00035d3111a0006ecaa8294a4000f2c58000069890800000200b0c97400093a61889704eb978000031f3a200050e5cb18000ac60064d2e8001274c0002bda078f8026ff34d3a974d2a93a61888000ebd7a5d2e0a4e988e57593931c00091e002195753c643140000039c98e else 0x3918c4160000066a6400021acc08480021e2bd154e1702583190d600060425a217850d891ba800001864af7590001c0008266042538543960c62578001c90e43d57b0001e0007231882c001b78c0848004359a99000043c57a2ab52ca46705c0000dcc08480000c1808500000d312100009b26223400106002830001baa220a4ba00039730a52dea0002c0012eccaca000260802280005683c63cdbcaf60003d09c000e5073091f31db90) else (if i < 449 then 0x74b0003372edeaef0c0e2d0f5c880007848800181098c043c32f2a0006ba60214000058ea450000071890852a6f50001600083000c1a0ed218001000024a995944af00044e1c0009a472e60000f98edc83dec5a181094af0003931c87ac480003c000f98d4c83de8001810952b0003372ef227c672e60001948ce0ba95800181094180000010c95eeb2826390f55ec0007a578001c98e4ba3e33973000001262420dd506000032578001c90e else (if i < 450 then 0x8057913372e000dea7cc2c0014a900854358001810943d6240001e0007c672e61c651c000088003c899b976fc4c100050000d969bc79a222cd0d8925d2201cb98000376402140009b262420000008f9d12ce800009064430103021200001a0201800110cc084af0243000206f50003cb160009a493a61888000eb9780029fa779287200032f2a99800089451d1d994000cadd00047e9048b0004131cdbcc480003dd6d30150d422180018109 else 0x4af7bd0001c000e54008440100019749b6f0002140f85b00032b28d30998af4540010a59789b6f3c83b48f0005693c63c95e76e00038001848caca00038e23f8c00080965e26fd90f901a74000018f18f00037a8018b6880004ef2495e0008263a1adcdcedc845a1f3000104af3b74131d168e6ead2412bc000e4c70000049a99043d7220001e00000460425ef400100852951c8c620b86b49800016000dbc80428000f8ce5cc00030919594))) else (if i < 454 then (if i < 452 then 0x643111a00009460214000120c48400020c01906000375402140009a472e6000121801102f00001810900002c3c63c000dea0522dfb16e2288e800011181090006f501116000b2201a3000001d128a00039b801906de0007691f198b4a00045e410a5a0c9a579db8000e00042358a2d198e54c5a44001cdc00c836f0003b48f4af6240001d198b4ae32452bceddc2474662fa000114af0007191cf7ae6e76e40001674dc510001f300410 else (if i < 453 then 0x6b03c76c000020a365d6a400003050000012080f00057c491350488330547d14c00001083c82148001300051744a2917200096a6d785af53b8945c80025a9b79042900026c129d0000b9a81d98ddd22711ac0000c0003c137f2d048832d387d15400001863878001d72f0000013581518c94e7a048000f3d04078002be2489a8c652c3d0251de00096a6e318000f4090003d92489a4a700073e14a4ccca00065819804fe8700004919687 else 0x5c200034130d52b128cc59761625418b3139ae99a8d0007785a70c0007dc032455fc00002080002bf0028a5a90005422e8aa00000232239065998f80020cb331f73e4a73d0249c46b20003142d065998f800004a3a240006a04981ed1e0006e48c0015f801452d48002a1174550000011800ec48e3838001890fe87366a0cb331f8873c18522c99200000830001065998fc121ae8000d00057e35914ad4bd878a79e250e0fe870001aea828d)) else (if i < 455 then 0x60000051b2f13e000922695f0f3d2607b0980025a9b6c400044a28000afa922680022e52607800214c8f938c66684ee24000ef0bba1d0f40000047800a431eaa000040200114e267c66826103cd64f7c622f00000a070000125a70c001188aa82800002cd34eae10001a09800c0003e4280006ba00a34002278e5073660001e29e4e15ec000180008c672aa9ac91c2098880030a1e29e6cc0003941ca0ad9704c44001dd9128a0001ae8010d else (if i < 456 then 0x47935d7591aa4c00100065d64d7589c6800001aee860004bb44a28000720dcc295ee49526078001aeb558d5cb39000014c4c96e000555ec001260780024aa25945c900051f2400079e91c5d538f04dfcb00000fad18800035d3e91a00103002e19de000000838004622a98a4ba5c2341300007dc01a440000251d120002bf3fa0a0005c234130f80d7000039384000fe863878001d72f8240006663e00113e74069a3c000dc91bae35ba2514 else 0x26162cb360006926e330e3d8b48ac5354270147130000030f1ca0000021989cd756bc6a2e9c7c131140e00000218dcc000bba1803cd756bc68002e5aee860004bb44a28af724a84e3c0015500043a071ac9ef8c40e35900018dcc000bba18000d75aac680024aa25948547ef5fa4281c00000e30000e40d6453730000018600035d5af1a884c4e0001dcc125512ca0000032ee8775935d4031a7be00000a1c000e4155050002e580086))))) else (if i < 468 then (if i < 462 then (if i < 459 then (if i < 458 then 0x5af0011523694c9de480012d800caa711ac8000c0007384981ed527826fe59388d640006342b9c24c0f0000003931c000000812a4000e4400c50001aead78d5a900048e2e8aadccb9631388d65b9860000129898e00039001d14000024682600000492e838001aea018d0004790010c81cdcc7be30001218f5502070001ef8c00043c0032a87a0000023e39d47a1b0f473af64361e43d0000011eb7aa3eb9248000004f789c661c7b4511 else 0x4e20000091800000a6b2296a4001508bb878001d72f0004a73d024b82000682620ccf3d26078001aead78d82a0004101ea5679ec365e18d628dfcb0000059a0980006fa3c53c000c4abf485389c6000060003219fd0e0000044271e000c48002296a6449508badd0002ee1076362a0097000079ec365da3d8011d120001ae8040d0000063c53cb74000e46400012993bc900028b8008a5a96e45422eec8c54000e142d064f30fb47affa3a24) else (if i < 460 then 0x4d73931c00072200229385108f7c62f89ac9ef8c0000435a70c0009366e48c00005902548000059a0980006fa3c53c000d6078ed8001064f30fa710000010c8f787100026cbc6d48263a18c000dfcb2c5000225140006255fa42000c867f43985a314f0450003581e3b668f000474480008327987d80000186cba2a8004890c0007313d64103a0007a04929c000d6450001e7a080f82a35d5af1a000d6078ed8000031128a00020c9e61f else (if i < 461 then 0x79082f36a2697400068261e20000de122a72c51bf9600035d52a1a9c46b20003000125512ca0000029c98e0006e600310b46000604240111bc0008a6836225a9b0a15a330212000dcc0042168c000c084bbcbf9a489a0005a33021200096e002555edec1abc78003d39d51c527000605320009366e48d2e8000d04c2bdacfb4c0f00009630212b460000aa200011780243800001ad386000577473480006ba806352e9c4cd04c0001ae9c28d else 0x89e4131cf7ab74cf841a200013b89253c620000a4e2359000180006baa5434001299128a28520cb4e1f0008c401b140006bab5e3400125512ca270b980000c00000f3931c00000e682620640012e840002e11810900047e3cc3e000002812a56a43e5238ba933e28001977441c8dc2503200000a20000004c084b0b2c51bf9661600037f2ca4c000e06656a5e31238b803ad19810981989e00010000b46604240015e8008aabd8003578f))) else (if i < 465 then (if i < 463 then 0x8b40005dc20000afa92268001dc13b8946b9f74631100001d302120009366e48c00003902548000009a0980018c40161400118800228034d7403468001aea950d0004b60022a9c46b200031429064f30fae90001bc244e235900018000e047f439e24fb80008b9e0002251489f57d4913400118801228000d7401c68000011a0980004a74ee250f6b74cf84000129d3b8900044f2098e8c63ee00022b111130e86646d29d3b890001aea950d else (if i < 464 then 0x5c43131c87a00124a3dabd0f0000aadea4bae49200045e5a310000b74b9841cdc00000433fa2bba39a443d00076a1e8baa29198440000f577432cd00030f9b0000177ff100006ba7d2340014a80385362000225145a3000302120007dc00844001708d04c2bf800362900004dc4834d03cafa92268001708d04c4630002771258800041c320000046e48c0015f5244d40f26e1ff2689057d49134b4600060425388d64000636200022514 else 0x14302120008840101968c001b9840002f61e29e0004d84131c00090c7ac800011c40088a5d0001a09857b6bf4271ed148527bc4d68d69c00040002431eaa00007593131c87a0000083c001afcd04c00028fae49200045b4b938b3e9368da8d668000d24d80039e270148f051591e220008bcb462110a065b9830001ac9ef8c00000b30212b460000062000000569c339baee2c9105f14d73931c0008f200418001710c4c739baee38e10)) else (if i < 466 then 0x35c3c0009368da8df9d5e144d3bbd3a49bf965700005a92f0f6cc08ae48001de0cb05a70b730000c0004bb3e4280000046fe580014a8cd46c20293b81997325277033283000000a2117a3940003a478000008a8c439132c160008d476e415fd1be1e888000022478a4e16e600018000002d701d1e60b0cd46a94ae5a720b4010000010ea527209c82e310e40cb0580004e26d8b00052902d0e0006ba8063400100806052708001ef8c else (if i < 467 then 0x3c037f2ca530a4b962c001de0cb05a47a950000a86b46a000209c46b200030001121c0ccb3b3439f42200053348f14d700000381d385b980006294ae58000b0005240083e0008d4b24420b0000cd46a728040001100050a3a83601200065651a280000409ab8000203976495e234e3b05800066a340011a96488272800000915705b65a92e0000147506c000004caca3bd2c49bf9600066088124ae0000b525da280000109800396b4039 else 0x3a84031ab8480400029731cdd880800026b1898e6b840200014000752806362d1844000838e1ac8000c7386bf4271e0009ac728397c5108000625da0c00008000518008148f292a00034000010dfcb2948000008b50538f5f4220008d4bb8414153957d08a828002fa1152938f4e5160007806fe594a61480005ad68001d51c9224e5000228f2752be8340000c8e4c720c000006080007933351a8bc0000081d23d4cc00054161ac8000c)))) else (if i < 473 then (if i < 470 then (if i < 469 then 0x49544b2918689008a6400231123c5270a6a8000c0004bb44b280009ac626395ec001bc07b9c29529b0d9064d63931c000b4e83021bd4000cb05a712c88000c7220006f01ee700008083400171cd34e8001e7b0d9789e0003fa1c000a667522914c000d4c80002e4225947cb527703320000487c618000018f90a0000022ee876c3418000100009ac62639ae100800053541e0a33161c44d63941c000016bba1c00106001043223098001b else 0x48f8c4000140007527d235388d64000600024aa259401c4d63931c00118891e280012ed12ca270a6a8000c0004d63131caf603a0003d69545400088003ff9a49b0007695dc20000a54dde35a2927de409b7aad3a0c085dd0170000c000b4e8302138964400060002af9bf257220008381ee7000080834000f3d86cbc4f0001fd0e01a5333a914bba00001e18000034cb05a0c0000030848f8c4000140007527d235388d64000600026b1c98e) else (if i < 471 then 0x5c734e3a0008e2728380011a80088270aee0000c82c54b4041a9c2dccbb8315ec00150c78002a5a020d4e16e67381920d1ca72838001390c4c700000720c0645d4e5000220008520064da2a31400052f89ac0000c0083c037f2c00118a00828001720caca00023532f904e15dc000188f210abe8357c4d6000060001e01bf960006a832b28b5b194754700011096446270b732478a00001c409520000246582d518000040320c00000288 else (if i < 472 then 0x6f571355216a520000302c001178028400020c001860008c45531400097689451ea1704ebd78004622a98a4e1591000180011ca72838001190e5550002351a9908784bb4e02800001683018002394c4c70001c80028a0005c734d3a81c000002315c13b56a4ba2e9c78001159a3f442b368ba71e00045038d60000600025b27c154d03f442b3720c9ac6263800117803c400020c006860004bb32b28000b90aa629174001c74880026080328 else 0x40e5ad16c9c92e0004a4190d8c4c737320c000085917135ad168310fe8f22000169d06042e63709a9900003590101800000e01818001060010437a2a90000b5cc46b00020e54b6a000458b4f05b60b2dea4b800126f640e5ad168300008f220001255680a000389ac88b0005903f048be29ac7263800169d060437a2a90000b5cc46b353209f000000a190600011e4400026b1c98e85f5b500022000e26b962e328f04dfcb0002d3a0c08))) else (if i < 476 then (if i < 474 then 0x7cb5f878b320008a484e3c001368fedf3e5b962e7998ef67742b368300008f220001255680a0169ac8000c0004d63931c0007826fe58001c4d72c5abdb058000f00086b6e1210f4afe000440019dcd24d8003cd1f4220005708152f0fe96e00055800000fc122f9ae38001d76389a58f70000b4e83021bd5c4c084580025b8081500000c00d0ce54f6a00044000d60020600020c002086f455200016b988d600041c70edc0007361b0899594 else (if i < 475 then 0x14031af168a484e3db915c16a4b8002721898e00046b00520e549ca00045a290a4000980024aa018d6a877a0002c9c2bb86fe300012d197c9a70a762ee0c41848f000108f200070a353853560b060002d3a0c086c36454e02800075280634000090ea8e0000088108672a85f0002200083000220094d61b9860001ac0060c64e4970002405081c0002c0010d8c4c7426a148001300046b65f2000078200658001aa0caca0002292138f else 0x41814d000100000069741d1e4000cd468002009d48a52a71344e16a520009c82c000e4123c52073732e58c0005a741810eb2f24808340003a8c08480003a858070004020241400003c0421800106001c437ab898000b6c300032b2800092a80635aec00124d4c203e2800194e16e600018e3abe923444001c4c00c5a708002c88c00052a4031abb90d701840000020caca0002721898e72a4e500022d148520004df2d7e0000c800235b2f90)) else (if i < 477 then 0x48f4180d20ce260002d1753940008c39800195948b446b00020e386b000032030ea500c6a5d000002080003a93e91a830000b4e194a64180005c161acae58c00048f4180cbe26b2000314a40000045c291e01bf9600012632b28d507806fe5977400001c30003bc1960b41800048f1000075266a361ad1a800080002b52249e4e23590001908e890e066400169d060437a8001960b4e23590001800075280835b317b1378f26b00000406 else (if i < 478 then 0x6af0007bc2ab5a001072722a5b4da0d00003bfab1328a955168340c9200069c740016c52b972fd4343212182c0003351a9cacfe000440011a964880000bc1d41b5700005a92f08ea4cf18640017092e842eea0c000066f500032c169c2000002300ad1555c0b800280ab81700052b4041a000912b7e85b31be9378f00000780d0700045e0071000075280634001060010337ab898000b6c300032b28b988d600041c70d65548637ab89c830b else 0x5e4131c000a6606a29ae00000ac3a5d2e1000080000074180c9c288400030000005128a3542c49bf9652900000216000a0072aaa11d499f2cca3ca4a8b28d529906000169c2dcc00030001490064f8002352c91082c0003351a9cacfe00044001428ea0d8c38001959468a17e00026ae0000b525d5f400159cd0000069b8a200052d8dc240009368da8c0015e144d38002d8a572e0000064dd6ab928a40003e464000e5553248001a71d)))))) else (if i < 501 then (if i < 490 then (if i < 484 then (if i < 481 then (if i < 480 then 0x5f13580001832e7806fe5972146000052f89ac0368c529906135171ca9ac830180000390254aee800004064180004ba1091e01c00029388d640006000000a259419a4d63931c00200075470001358e4c724a9d49f48d0005a741810dea0006582d38964400060002af9bf257220098381ebba000008190600012e842478000008a1b74d63921c9c46b231a3000169d060437a8001960b4e259100018e44000de03dce00010106c4f3c91fd0e else 0x3c10012d0e6d50656521cc000caca0003439b8a26444ee42b360006b00043193925c000907d2072d68b0000043131cb22000b5a2c0012d93e0a80039c2138f4d067742b36b2313c9c82c2f900523c525d22f000080000143131c000024830194a400002458001c80908a0005c844a28ae0000b525c00171cd34ea070000010c59a3f400036bb88d4c4041e31498000c88bb56a138f45d4e50002200000865650001720004534521489993) else (if i < 482 then 0x6110042120d1d60002c0012d00049c3d272b451187a4e50e3229c2000bb8300015a8f18f4064738000b00049f65f260009cad144566d9dd880d800238803117190004e41681c000006316699dc000daee0001db906245a53491ef12b208e691844000edc84358002358b40e0000011913c92a80635891e112607c91395000110003a94031a00001675470000d603a4632724b800120004363131d20c81c0002e1350a40009800235b2f90 else (if i < 483 then 0x48f2290001400075266a36279de0cb058000731a09800007b302120000920c01c0012e8050400020c004066c300044a2800092a806359119dc000dae60003101000040273714dea0008d62de10000d247b34ae5277920000084031ab980006a64000100800c537a8002358b43d0004981e9c2b22e7031bd40011ac5aa91ac8000c43d7384981e0008047522938560e0b0600001920c0600040201a150e600089450000030c4c700024aa018d else 0x4e50000012245ecc0f1a48000034d70f000330440925700005a92f11600069c7576578800098002d8a572e57d00000534b931040003c00206cdf92b578004541500061043a21152f54d06817580022a0aafd471b212100066088124ae0000b525c00126d1b518003e72c91068a2272282683000091e20000ea4cd46a2f0000018782c359000180007806fe59ce1f5881878003bc1960b8cb60b0001f0d7168ed2410600008b4422f47280007))) else (if i < 487 then (if i < 485 then 0x3c037f2caa683000021aa0000f90a294c290000b5ad0003aa388f275244c340000dce4c70002998168a41848f00010d7000049c1d385b980006294ae58000b00052400d3f05800066a34001428ea0d8000019959400058937f2c000a16b2441395addde88a728000009164923934e3a000a16b24415c00016a4bb248001a71d0005b14ae5cd14bc447a4e0b0000cd4680033b9d41b00000332b28000b126fe593948c80008bbd308ac910 else (if i < 486 then 0x906778000168ba9ca000448c4000caca45a3088909045d47000022000ef09c82e1ac000edc800020139b8a4e1000005189d88520004c001d25198b3540001f2140004954031ac58afaace69891e11da4780026b9ca0e00053300e14b848300002138510800060698001f2144794950001a0000046fe594a40008cc5acd1fa36a9b00051934e3a00000278c794a5b3000c5a948000010b00050039554e209367d48d9254948b0faf89ac8000c else 0x5dd7610000c000b4e8302138964400060002af9bf257220008381ee7000080834000f3d86cb800339c6dbb0005c734d3b13c0007f4380014ccea450002e42259445323b353200000026582d519d8486832ee800001864180001551091e72200028398ea4fa469182d3a0c080000313e30c000032bba1c00106001c42e12010000a0003a94031ab98e6e00041bd5de000058001acaa90c6c300032b28e3876e82638000014c4c735c2010000a)) else (if i < 488 then 0x5c734e3a000b129005800139944d3bdab012da950004e43131c0000068301917539400088001fa2159b5f159b8f01800000291e29385109644622eb8c800116e64425911800003e812a4000044cb05aa300011a864180000011091f1880402800231123c500025da25944e16e60001800000c626395ec90c0007ad2a8a800110007ff34936000ed2bb841a2927c0009bc82952b18d57b0000011e47a93ecbc4d6954540008c3d3b49db90 else (if i < 489 then 0x6c364532b289f000042e190600011e442bdb05beb0f529000015160008bc0122000106000830004622a98a2165c734d3a001188aa62938564400060004729ca0e000464395540009769c0515c1405868b80000420c060008e53131c0007200082800171cd34ea0700010c8c59a3f4000368ba71e85645174e3c0008a071ac10d0c00039048f1481c884b9630001178024400020c113860004bb32b28000b90aa629174001c74880026091028 else 0x76489a86d70000b4e83021bd5c4c074580025b8049500021a21b0ce54f6a0004400106000c40001ac3730c6f455200016d870ca65650001c4d6b458001ac2c88c9065c43131c0006b20263000001803c300020c001086f455200016b98e6e42a400010396b45b952da800115bd4976f6248300008f220001c4d644580024aae41464e0006f624000b207e0915321ac0008000291c471f85f5b500022efa7831e65800169d060437a2a90000b)))) else (if i < 495 then (if i < 492 then (if i < 491 then 0x6f5713000160006b2aa431b0c000caca432a5b0001572a5b500022c5a78300e59caa17c00088001ac0068c00040e0011709a8520444c001390c4c7426a148001300073765f200007820085800114909c780026d2943e0007966a53a414d506565000114909c780026d1fdbe20a7966a53ab22e260002c001390c4c700035fa138f0007145287c000d0e6e288000f04dfcb000354195947cb52778b328300008f220001255720a00044ab7090 else 0x41848f5a70c00001483018001390c4c73952728001168a42900026f96bf000065ca000144918000019b8a20005705a92e000e9680635e2dafd09c7befc1e9e3b64e16e659118000b90c8a18001060014400024aa018d4e16e600018b98000bb841844000fe8738ea38be0110004e43131c00092a8063400184400c80002292138f0007145287cf96e58f1665384001770627624fb2f930003a94031a00004a75470000078088300020c00308) else (if i < 493 then 0x6f5713000168ba8e0f80440008650603000389a720b45d470000230d600076e4215d009cdc52948000010b4d70007780c8311ca42c212e8001390420c472ad38600000832c160008de00845ae231000052a30001350641800048f10aff16876e421ac000edc835c23d8000a5468b47370cbbaef041a180002f4c08480003604a8700040202314000e260082c0014a900c6b7a802000080004794180c9c242ab2230000038caca36180000088 else (if i < 494 then 0x4e1000001188a90ae6a6408394ad01068000068098700045e0071000075280634001060008337ab898000b5cc73785720b980006a641b0d844000a37ab899958b00048f4180d20ce260002d17539400088001d4a018d8b4737857209744220002000123d06032f89ac8000c0003c037f2ca530a40002daa0434caca2ee80010e0600077832c1683000091e20000ea4cd46c35c5a42b9000000a00f0e0008bc00820001e4900c680020c3ac86 else 0x50b59220ae0000b525e0b0000cd46a72b3f8001100050a3a83600000265651925464d38eabe8002b39a00000937144000a5b1b84800126d1b518002bc289a768a7e700026000b6295cb800083d375aae4a290000f64900034e3b23241472aa9924000d38e8002d8a572e68a5e220d2705800066a353959fc000880033b9d41b00000132b28526c22b2440000000d70f2fd434490210005c24ba10bba83000019bd4000cb05800280ab817))) else (if i < 498 then (if i < 496 then 0x940952bba000414190600012e840003b09960b48f8c4000140007527d23400125512ca2711ac8000c00089e3931d08e8905286577400082c320c00025d0876112432c1600009c826380014cc0d0535c000016074ba5c200010000016830194a40000045a072211080c00000632b28e787e80006c0018458808270a210000c0004523491e8f275000035761624dfcb270a210000c4794952921aa5320c0002d385b98000600029200a9f else (if i < 497 then 0x61180c20d507826fe58000d6000460742072d68b0000053131cb22000b5a2c001ce109c780025b27c154d000042b371d6e6f0ae421e9cdcedc8000200a478a4791cd3851a9748bc00020000040c4c700000720c06529000003160007202082800171cd34e8802e42251400000732b280007e800a6c0017200045270acd8010c0003c04802cbe26b2000311753963c08a2ea72a15915c851800014d50780900594a64184285c72a6ba0c06 else 0x4e10005dc18000ad478c7a289464000ec061a68000b0004a300222b36000c406dca10cd4491b45214b2f936118573b721244e5400044000ea500c680000b1d51c00035800a18000b8862638001cddc7084832070000b20c3c10002d09a8520004df2c00173ccafc0001959486f49700024000d0e6e2896518252b970000091898e0007384271eb220000062d3400010acdb9e000225148eb61185720000d0e6e289f2c001e2cca9380019594)) else (if i < 499 then 0x42954b68a22c8e0006a024ea554c0005222aa01939352954632c1600063456e10000a80c0428000fd9cc2c0000cd341300000c660424000108154380025d006880002084031a00083000819b0c001128a00020104c0a4e16e600018b990aebb841730000d4c842ba010000a0006e13aa38d86c8a00051bd4000cac5aa91ac8000c7ae7593fa1c0000628301800100803854398002251400000b3131c00092a8063400184400484834759020b else (if i < 500 then 0x647000002129c2000dc031b1955d98092708002870c0003e631d20e320006ae44001c8cd70f0000001d01a5a55143181e0006ba02014000024d444800230993060000066dc0ec9000064e4cea4001008525a00026d8b4100004281e916000b76390a51c5a2889d4aa9a220a6a20003372e0008c264c1800110c0043b242a01939352900032c16752b6001228000e0cc983000002804076480003272687a0006303c001768d70f1d48002010a else 0x3a90008c4148200006303d129254000a323800002890004bc3372ec4800067a380012d0da49b33aab800124e15f16e0180009786705d3840015bc644428a1ab9144a49532b2889492a00051228000cac59d48004620a4100003181ec8e00000625384001b8062ef460000156245f133d1c9c322aade3122800000459d49c8c620a00000337144752000b602a278000cf4727033a995943a90005b01513c00067a380016a4ce0ba7000019594))))) else (if i < 512 then (if i < 506 then (if i < 503 then (if i < 502 then 0x44a49400028752b600002968cacd9c449d49c8ad80a0000183a20e0007060101800000cd70f1d48002010a44a49500028b609146562cea400100851ef8000008c44a49580f28b60914de82c00122981c59d48002010a0006483de267be0009d630001c88c607800333ae49200073435c3d13c000724380016a4ce0b8002431eaa050e0006db12bc884800058001900e053270000283946da6a78c02a00070603018000038d70f2450000060b else 0x51e0021801200066e5d55daf401c92abb5ec68925da0003c63ccec0006e289d2c000cdcba148003e39100055300314000bd8bea30001f18ea8e2a0aef25b150003595ec189a11deffe6c000168bf040001ae80a050006a23382e0009b20181cea400100850002308008644a494645280007229b62d528000e4870002641b4935a3000004129c29d6000317d00024888b788001c62954e8523322c9c29d6a1c314a4000cb0580023080186) else (if i < 504 then 0x5143181f18edd4bee64001c64d6453a5c4419c176470005d812a1c00066431b1955d98491f4800006050004613260c9b2000bba1d18154c00052228001939300000335012796ef00002d17c001778aa14abf297115410005de2aa3600066e5d0a40014b88a38c62be00e0003833260c0000089b21c001229aac580025a1939300052a402147bedcc9d63191c000d404b240001939348a000007169300006303c00154e31052ed0001e31e else (if i < 505 then 0x53a0340000046ae44001c88c607c2642e9f5230005143181e00a9c06b228001380d6450002603ad2800000235722ce40006705d759e62284ab3944419c176f44ca47f1800084802c5991d76000048002603ad2800045b42f38db6ac80004c000f98c7480000052bf910005555693c00000474268001ba97dcca4cb622c41b0000015f732de918ea1c30001c3173c50003ec9da326f400050e1915cebcc6475bd000143860000011d01a else 0x51a0003372e0007cc99441a31fcce80d0003d74728e0003e631d20de80008fe3000001ce80d0000011ab9184c0003ea470bae446303c001450c6078002701ac8a0006af7b12a03afb0768c8001380d64500026924e986c6557000240009e0eb4a000116cea8e0000011ab910005c93181e93306f1726c001450c607bba3c3bc59900089e8e51c00002665650000f980448000211ac49664700000212d1800074269fcd382148537a00023f8c))) else (if i < 509 then (if i < 507 then 0x65a52b2bb140000287441c000e0c0483355a450000b0000064021400087896c54000f996e880002eb1d09a7d00006dc131ce00078c78f7d7b115061ef8000030c44a00032b280007cc99440001c8cf18f0000009d01a70a79769050fe6d18db8240000055bc4a2a1f32dd1052b4553372ed56914c0e2d1e4e0c00032450000008b4987223181e00003c6e2880019d4caca0002122c4964e70000061200113cf5c394380011fc60002701ac8a else (if i < 508 then 0x49d52b4021400000c78c78000005008546021e25b154e100056f188a80006a4417790f0000ac444911ab9184a4d271330b4600000624000e45008528733d0000c51a8523322c00072280429bd19e943862948001960b0005dd4790c89492800050000030dc918000021e31e5cc00035320000a8ef72d1c26278000740a26e3202656900035320000a8ef72d1c26278000727138e0000c00000151d14b46dcaade2568d4ad5bc4ad180033809 else 0x3a94601b0a80006ce8400000d4e8da4ca128001600048933218b22dbab342d539094000b0002449990c5c30004ca20e38f26d7039128002380a3fb0001a51c00000333d1c000dc07f230001c7132882a73fe2e1960006e05c418f2692a98a350c0c8ce0c280005d1880d0000922fc100007d205614001a88ce0b80032900b876ab0004db160008f201e1968c00001848000019e31e00052b4021400087896c5522d52a0a07389a6900018)) else (if i < 510 then 0x7a749800016e02f26d7039a30001f40d0003321a79d5c200049d30cec00100488001e49ae0723330b0001600000233218b2281e0002d70dc71328825b2adb811500039100316a5492a00035779a14000aac8b701878c0004950011ab26a2ab4a45779a14000aa82a8aad291000450305147d27528c034f380017743800003228884790004041ae220006b879129254000a1d48001828a51e80f00018de87226562d91c000d4048000051828a else (if i < 511 then 0x4af0005bb1c94000064e4d528000c14527b80000515000005353211680006a2250a51c40008a1e000002874b439100016894928656510f00000083a14a38800116a27c73392e9687226582c000010d444c5a0001a9904b439100016e6e0006581da8a37cce4b9f48002a00d0006133a7369687220002daad6c0cb0380000f18c0f43d0005dd0e8940008d051b0c00006443238001a80900000f305140007528c03400000cd28e25b2ef00015 else 0x713060c00064606a14000074ce840000049e29e0004bd3392e000ca40081d85000100c69d48001828a44a49400028b607226562d4a4000cb058001c89828a7113a94041a89492800050000028c1450001d4a020d4024790000ea520006562c001a88ce4b8003289a51c4af54a0001c0000046a641de15a80004bc8b1724e987786e57bd1295e00072438000e44cac5976800294875cc000353200008e3244451e40010106aaac2f9a51c)))) else (if i < 517 then (if i < 514 then (if i < 513 then 0x78a8c53131cc8e000fe224e8800168c40001c199306000375010140007528c034001098d9d08000039edbb0004b65ea2a000a8064e4c001370e0932250002839468c0007d034ac8000754716a5f19234ba9f00026d8b4980003181ea7a000e3a440012d8000aa708002fa8c5f16434711c00095a7049800231136c5800003a308d0004b43272600078200858002250c607c628003120e59135900018e268ccd2a61644d64cc86462a274830e else 0x51b0005a92e000bbe65e54001e28c4c70003132868b000002559300008e09ca45149e10c748000238272914e0495467280006ba0123518400000830001e0999963e95a754e107d264c0002000148800449e5bbc0048b0008c53131c0006b27f43148525a370900036e003093cb8c4000168088bc00021434000cbca80019a000868c57dc3131d20d18a62639010d4000042954620000b50d00032f2a00066800419e28000c4c722532299594) else (if i < 515 then 0x5a73260c0000069ae38000dd631451f49d48000d4e144230f187d28c200035711108c3c60001bb0108a46035d0001a000db801e25011178000400025b9979500033400b0d1ca00062638f2c0014345a070001878c6244c50001e00092c00a480010a0da4980048da49a95e000063c409f6ed200041a810dded923342141b4933cb62650d168086a000020000cd0008300025b197958e578a3131c9c200061e3148525800093910002628f else (if i < 516 then 0x36dc12000ef09b62d68c000fa442f02431eb2000245e3e91000064c7d22168c001b704af83461d09a3a9402000140006ba0121518400001030002d399d0800000154a1ca9c782666597311ecedc800019319d085b000060716000cb2718a57311ed32c80001c1801060004fb4cb2087a8a66303d6c000136c58002431eaa00005e07f112b4664c000200012596dc94631c7ac99100000a0440a00000267421949a88ce4ba2f0001a809 else 0x6b854a7591c000706004180010f0000a80f81036e090003263e910b46000db825781218f55000000a00b050003e933a10000818010511291e40003000462aa50e0005703392e0006b27f430000000e314b7a0003038b6dc00067112a34782c2c59b7000001c480032919c975cc47b000206a68f200018000004cac5b7a1acc060c80f359000187f476ea94380019c4cac5ae623d9a9103df35900018d9c78066458000e0c018300021e2ef15))) else (if i < 520 then (if i < 518 then 0x4023a30000e0000086303c001775c8830002a31960b00057200210a5475280834001040cb05a951d4ac58d0000013181e746b4c65a1ce8cf38cb4380005a0938400004f32d0e000074806340010080605000230008854e040c000280007d2674200016a4ce4bb6e000003890004790010cb989f66a64000000ccac5a708000008c4546e44ca20b98dc8bb841c4cf8d274c00032d1f5230004790010cb989f66a4413840015bc622a0001a910 else (if i < 519 then 0x4430040c000894004500011fccf47245ab92d80b52a57232b16b909c0a2e50002064010300023c80a0752900001216000820f083d9d9674f9d100026ca3c87529391607160007126a424000020c4840001a98010652a57200016b74b606581d4a8e440005add000196070003b733d1c0008b675471721380caca0001a9802860004790030e9040000022d4ad2f0ce0bb3b2ce9b82252a5b032c160009b28f21d208e4581c580000420284 else 0x522351128f275200035fd916cea8e1ba8001830600000432d0e00075270a354a4eb4000580023cb03886453ac32b2800079c6323d7b0ef80006000002ab70900000334a38000002ca221731cdcd4c826bc7299e8e4d73f933d1c00075266a35080eb400058001d61959400056d51810a2e7ca6a640000ea4c4468001c500a9000000d31210000008b981d4a56e80005800270195946075170000cf088eaed23d384ef800060001c4ab709)) else (if i < 521 then 0x52a3910001600077c6581c000e296e88363253af0920000025220ca54ae40002d81cef8cb03a9500033d0b7783be5dd0e00077c0041c0011e410432871c49a88904f5dd4790c000712adc240017f8c4842c1800370070004430010ca54ae4b602c00116cea8e290a538001252a3910411600001a040110080000143a5780019e8e0003be3fa18b8800000221179b80d4048259c826d8b04a00032c16bba72200018000004e40430a1d4a020d else (if i < 522 then 0x4793a90001adbe08064a48dd4000c183000001196870003a93851ae228f303220000f38c64780039b9a9905cc0000081000075200635314ef800062ff0001a8095173ac36e2800066a6a024000ef8100623baa0000134d736a33d1c0007200082db98ef800060002102b7094d70003131cca27f26947145ceb0caca0001d49888d4e10000141800001e62420000e240244a87000002060003be5dd0ea52000b222d0f50400007aaea78b4828 else 0x7220003181eb52978a845dc88000c607ab6a259b7143a300032d0e00079c6303c00231136c5800323b38895a30005531091e00060c180014cd6ec700022fbd8150004bd48d2e000a5400434000ffcd3cea62af643e0c8a23ff34f3a00064411a14000108d6cf000007011844020420000e0000026582d51824024032ee9c88000600000539010b46a44000253880015b860001d4a020d55d69000050e4482098a3c001488d444a7100048a8c)))))))) else (if i < 610 then (if i < 566 then (if i < 544 then (if i < 533 then (if i < 528 then (if i < 525 then (if i < 524 then 0x3847220cae4b4e00022315390c4c7207a8f0000c0003840050cae4b4e000200000055b84b5c1fd1898e00044a36e2918a7f4626380000215b84b5c1fd0000e00000431310000de8806340011c00048c5aa702341484a5c249d30cca88e000663311c212c880022f2c8880004e036e28000de88063600d2256110a709df0000c8c400032c16a8cbba000197c4fe80007000001989880006144041a00092268c69c89c10c6078000011d989 else 0x40200032d0eb4c79c6323c000e291ec80000071890800000b3111a016000b981d69914c00078003629a41b6ab59a00016000b6000618000e25da848002251959442761162f1c00071288624001720caca3deb08c628e0004d95cc0ea52b751882c000e24d4448002a9803874820008c4160007d2622340011e40043245c62add8e0004750011f140a29198454fd484c9494622dd1960b000027405080007460321d4a4002310580000198c0f) else (if i < 526 then 0x5a331d1295e76e62638002310048380023a8018f00043d7220cae491e000212bd390c4c72578000028e0000014e410e2289c80634001178d444a47800462864793e93851a00118a002195c923cc4c4000001189885ba47b000209c2a3abb830001178d4448002431b2a073452132524e200006e48d38400000862eeae5800067224755a61e95e7f40003977631400030002912b7095a3000313108f27d200034002370c949390a3aad30f else (if i < 527 then 0x90b4e046828000708008195c969c000448a8002b70900044a36e28d987f4626380000155b84b5c1fd0000e00006831310000de8806340011c00008b32b5aa931900045e591100009c06dc500017f900c6b7d1f1a4e988c48e732c16000644094140000b40bc200000726d8b5290008c40e000a54b163554c00000c422f0001a8094790005220c95f1cb18a380011a401482709df0000c5a64520001e000b46adc251754500008a579fd1898e else 0x4820008c4160ea8f20001954800160c64502c01ab910000153181e00000680a10000e8c0a438001c23910652907856b1674600065a1c00231136c5800323b38895a30005531091e00060c180014cd6ec70502950000d00045f7b02a0007fe69e756555e000138002a0001930007064eb18000cad01c59766340d849000342a341400070656d18b12cace92580004bd01420001d180a075290008c41681e00000630000e100043262afea018d))) else (if i < 530 then (if i < 529 then 0xd03211400009e6b678000c88084280003e00a040000074db16a520011881c0014a962c6aa982780008000469057209c277c0003000168d5b84ac8829c8a860008c48e70e0ac9300003d2bc00000870002272018d4e15833fa180b918a00018000008c4c42dd23d800104e15925dc180008bc6a224000fa500c6a70a62c160c00038a47b20000006624200001d4c44683a8002e6076ab8c48e7160007126a224000fa4c44680026c83d87 else 0x530d18658a520002cd8d6dc00094680001989635662d00022760be6d4a74dfc000cccb1ab3168001178866d8f348658a520002dc89698f3879962948000b3635b70002492e00061a3193d648f9482690001a0980000022fe10812000a90a4d8d55d48491b18002909272100043d1e000930b6e2d12c000ca8a3220001f99b00080f30d1800000477e28001784c74831a9c92f88e80e7153312c0005d65dc04000b6cb7c10000b594b83) else (if i < 531 then 0x4cf86b48b166180000021ccb14a507c58000011f99b4090005d152896c88818510240000354a478000070a00000730d1800000a66258d580000048a333d49a098484000497246a4000b98410b23f59806aabb30a4b9237f0004f22c858b0600035aac00107c59a94062e61048f00000114896d7681850cf2394000726780020f8b3569220002285889ca5434001488c084986000009873345350001a00001a5fc2135c000c4c71c90000048a else (if i < 532 then 0x6c65b7497240440007e66c000024c3462478001df8a00002a3312caae00092e48000010c7482258002061442c0006601a0011d6b6e2e27a3958bc72258112061400000831d208960008185123c00001051bf8002791642c5830001a876db000055aae3ad898599e4728000e4cf8eb48b1691e00001228dfc0013c8b2258002061459286b00016aaeb6e00048e70002100c9ab4258001189d0005201e858b06000350ee10cee4a99e3de8000e else 0x3568cc00022760000b70740000053c8b33d1bf9868c69d42c61f36ba2000c3e6d520000c0848003f79898e00000f41f1600091e67a2912c000ca8a1d500022d1c3569220002200001261a30000010cc4b2228000011342c0003a91aad91d4bf2cd0b1920ea46a42253800123b00006e73ae1c000a403da6156de28aa162c19d48d42c89e6ab1a00004e60424c3000001839962948000b3b05c70003a000d4a61a30000004cc4b26337a3138d)))) else (if i < 538 then (if i < 535 then (if i < 534 then 0x30c0000050e658a520002c00107cc0849d82e38001d0006a530d18dce91e800292b0000d9d0a0480000ea90007ef3131c00091e67a299b929c00090000084620b44b00032a28c88000c3e6c000018c0848000019868c39c00044832e1c000a403da61c092e0ab8700028f8f39c774448326ad24400045dd40012a1c2160001d48d3aa0005ad38000b0661a3111400192099ce20f2241900052a3a91a000004604259e8000c34648b24c2440f else 0x3f17210001e95e00084e38cd0000c446b67000198960006123ac289d40009368d90dc61d0109ce000224197fd0003312c95e00002039a85848eb0a0000008048655e5764483200000860424001438c346256319800214af0003681d018dca622352bc00104472870001868c57641e44832000ef0604252bc00000c74628001ba8a00059230d18668dca62234cd0000c4469f8b912138f3840003740c95f1ca82238d540001ec300001c97f08) else (if i < 536 then 0x4d70005bb1d18a00099e29570000d6461bfb0b304164f20003332c00000483e2d518cb0000399a29ab558d0005290020f18800080428cd14d500c6b9100018b8f0000014cf14668a5475234cd14d40006a1d800286953a80003f336b960006b230d598b40008c17aa0345132f50002f00664600005010c48000bf841860000120732c529000160000227ca40d4d3ec00030001a91810946f3bb00022000c9e61a3172c000dd451b180000392 else (if i < 537 then 0x32d0020ea8c83e0002ccd14d900c699a29b0000d58b41f778169d40009368d07c00136c58000029bb0a4025290000e000a546223400001ccd030001ef23b935a64767901ea540006223554d4a400039ef8001ac8c3850003740c89c00082239280f791dc99aa8000080600000a41f1600065800a1c00000d004500035c2dd8e35682600022794a9675234d89a21b7c926b8002dd8e3ca0006ab1aab8b060003155da223449303a9480007 else 0x43600049724b9800063a413619200006a1dc2f1dc9537f0006082c9b0b06000350ee179434aaae0001cf0c59100090616b9800063a422d000133c52952c181b8d7224763171e00002e04a1000169c0403000196806873f100060b1e00083e00e2cf2800100c6a250001951481c4b4000260009d701e30001008efc544a000198963624978d1246a80007ca41668000fc8da160002018d6575814a94a9b270a0003562d07e06059f880018b8f))) else (if i < 541 then (if i < 539 then 0x35500002b0c0008860141d20981c00058004832090e00000233c146ac00104c451159751dc99ab000000914c865d477266c400118c493200011dc9b242a5a018d00001a4121c00000a67828e75074000c9ab000000915cc8b431d20000e331862cf2a278ea469ab000002915cc00031d200000027e66d3c98b5264b279316800163317fc359180000068ee4e28c000d6461bf8003fe165910084c816e32000cba2c000014d64627900019896 else (if i < 540 then 0x103f23600000a62234f2800136c58002951bb0a4025290000e020000668193600450447000001804063ad0004db16a540006ec2954d4a4e143800001a088e4703bb00022000a960141d00554ccf052ae2871cf0c3f15363171e00000e6ec2900801c00038000019ba063ad0003911600070a62234fc64a20d478000002088e3df50e39e18aa60000021ccb14a536c58000019ba060003de69b267be0006b230eb564536c59efa871ac8c else 0x4d93850001ab160010302cea400133c52ef00028695000591359186a8bb863a40f10001378f000196802074820000011718880499e28d896dc00092e627d9f2904d70004111c00001062e3ccd000000c6b55a270000b5a65b000014e6edca63a40ea5b78000537280018e9058b4cf00016be2b22de830cd14d800069d48000038a6e500031d20896e1200050ca800000c5a1e0002869547f000359187611c2ae2751fd644d646372bc218e90)) else (if i < 542 then 0x4090008c85200000668260f9da1c00111e52c18000d43b78a5df2aa84fdaae05d57000103862048004642957641e606330ce00099e2954d4a40003a6bb0b1898e07f0003021200000883e2d208cb00003b3d0002070c3345350001a752aa4e2a2981d4a40003c33859a678a000078302120000540941000169c03c300019680407482010000166c4b6e00048d50000f9482f0a010000a33c0004121c000dca80634efd93c0006271a5bad095 else (if i < 543 then 0x4d83a81a794a551862d024000e354a1b2ab8001239c0000033283a00067a29984000d6462a90034660b00000333d14000e331862d984000e7862d2a3b28f8f7190008c316aa40006b2314a9361aac6c62b0b0000a0004cf90616ab800073c3112c000ca8a2048002a4290005c2341307600007fe74f2960c0006b72b8498e9000001041f169046580001d35c000c4c7433b0b0000a44b00032a287600007fe7400001d16ce2ae0002070c else 0x27780c0009eebbc55129461720a1d43099f91b0007ef3131c0009ae00818000e1400469e520fc0c0b3a900033d14bbc9eefb85400107dde0599a26c2c58d4f20004242c6aa00007c180000a4c084800221803870005534011400118a62638d580000088c134620000b5808b43e5206c400118c48389c65b18580000b9898e35600000922b0000063a422d0000cf453fe8001ac8c4364a7000247380000026554803e12c5800429a5a9b))))) else (if i < 555 then (if i < 549 then (if i < 546 then (if i < 545 then 0x5dc00031d20896e130fc5162d33c0005b7280018e900008b40010c894a310fc50000000c5c7af8b732c88c00032d00e0e90483e0002c001de00283433a010000a3540003e52000000878058fc400182c780028a1f7110004f33131c894a30c2450fc400182c780028a1f71159a42b3f2367e200062e3e0383accccb0000061b3a10004d90031a01a000668180010b0fc8d9e520facd0b58b41f000167520000042800123dde032ef27bc6015 else 0x3ca0004031a000002a8c19129460ca8a1df8001cf0c51800032a2800096eb4255b6193d0e881b12db800120003240010cc6896eb4254efdb9964460003f79b3a10004d900c1a00000466818f280020605c0ca952678a39248f0001479499e0002c0022d0c7482258000019455c00039e18a84000ae05d3cd76108cb23f8001cf0c5fe6254de3c7520000102800123c00831aa00018e9044a70987e289e600066659b78000c5c7af88001ac8c) else (if i < 547 then 0x15460c89494c65450efc000e78628c253195140003240060cc689ee00054001009778540c8001d48d00050d001168950ca65450d51784f9482a33038000b55c0003fa180009f67ca40001009b98519a0001d48d0005363171f01cef66665800002135c30001c28008d7dc4f78c02a75200067a297793dc000aac5a868000b35400031d2086c94e00049771980d646462a4799e8a00032d00e0ed70804000293cc000f00b0002678038b else (if i < 548 then 0x32c44b0e8c0d5680634f294a800068000011e5890003924121c9de86c6484900c0014a439b129f9921240232d0000e8c000062034e1400000432501ef1941357b5363171e0006aa00619bd400136c59e52950000d4034445290edea0007222d81d110dd0380006017f08000312077080000a460424000094c4c700019680d0736200000b2400080400a2800231400830004622db8b3ca0043a91a000dbc62e3d51981d6dc5800267adb8b else 0x4034795290e794a540003500c0014a4380023c8008600344230e18a6600062638d894fc00090000009870c8a349f328260009406504cfc4000c5c7a37a14800116090003a45c9e6e2a8485800133cd305a4a0001951400032c44b0e894000a8c18efc000c3862a70001e0160005f13131c8c2000806351c571552c88001ad1bb0a5534440000e0006aa6e819180e151e468001ad19d8a00000b01008b4e00091e1800000cd305a4a00019514))) else (if i < 552 then (if i < 550 then 0x40c6440002877c000ada310a8ef175c8a2f000001073c40000003c79cc1706a3d84c00187cda06322000143be00056d18856778bae44eb40010805a2f000294873ce72243d1e5fe00038c14000110bc0180001597f08000312026080006b40382800001cd305a4a0001951400032c44b0e894000a8c18000004c3862a732b198960003923131c8c003880634000018f2c48002999898e3ca52a0001a000004a441900c0011e43b6730421216 else (if i < 551 then 0x556e1901c00066259035254000a00023fc3d0e4b04520001e65489ccba2e0d51480007ae200043d0e39255400014a4090800048de9e2a10ca9df00022a0c3340004611a81a92ac8a51ee8000c9c98000019ba0737500000114afc776d1445439b815b861baaaa0000a43c0008432aa1c000adc30000eeded48a1000025a0b5c465d0001c6a4aff0f440000c9803c31a900023d10000006327268bc00e0001d84c00187cd99a2160000d else 0x52150e0c66800080634001de8cc4b275b4d994138dc00050e0c940f746504cc8154c0005000001287063340004611affaef466258cf1ef5044722e8001df077fd0003312c640aa800028f39e10000780029121e86520484496245fa00005010000c9806c32500001939335200000820000004adc32038000cc4b19a3bda308d0003bb5d7227dc0000021ccd02591846a06800322943344954611a00077663e44fb8000030399a0002308d)) else (if i < 553 then 0x200e087be00077c1cd491e8e2881a92c00001049648400024c2600000c6c000004ef839f70032870600055300114754ca297271c940012e4e275236b93a38640003be0e7e8000a1c190a5ee8ca098000021df073ee5220000c75a0006162c0015f900451d4a952018d0000013312d01ca440ac1800148815431a900023d105dc554011146a400063e411e800004020000051df0736100000724640000004280014854383275b4519413 else (if i < 554 then 0x38400b0c818c8a00050ca94a40005a458002088e3be0005d7180008cacf420cd000101069900002c98a68a0003282600099800256479260de87c8f24c1bd8f3ad52900016000a6a8c234c800000105272800000883be4653591877c0006b23153121178491df0000028c4e546500010000930a2a3c001ed52d8a80025a1939348b8e536a1c9ca00000221455261220780024c28a8f40c80f3ac286a2000066200011955b860001de00c91 else 0x5e50020c0008ca8bc20cd1255010680029aa308d00046545e1075a000de82cea54a800051e73911bd8f6453840000c75aa520002c001194004437a29aa020d6eb4b43272600001675818fb800000c3800000a2f0857542b62036aea8567e86c0010ad87cd9952948000b0000037ff1066800080834ef8000d5c6245bb9a088e3be4653571873cbca6ae3000117401439900002010a00064f3591800073c0021a1ad72cc2c5aa5a9aa018d)))) else (if i < 560 then (if i < 557 then (if i < 556 then 0x73e5166a600075a19030000ca8a0000011930839e00056d18884c9e7081c001208e1039cf2214078c3530000050c0000047081c00181cc9841cf2212070c0008eb3261073cc9e81c3000000d4a43b03800475880005354031a752a54802280502e517840001de0131140c000018280000126ae31628000cc4b0000021df073ee39e0000c000a6a80634ea400100451d6a951858b00039e0010c66892aa0a342b54d51846b2780000407 else 0x50080c6680008c234001de8cccb2a7000407080004655d71813affa77c1c000004e1039cf2212f28c39e6e05e5180000226e81c00143802064358001858b6070008cc1000000480635bbc0012207b52a192e39d5360007221e678000f80393ad978ca09c160002018d86b00030b1681c00119820cf0001f0072078003910f36178d000249368d80008dee9978ca098002870010c7fd0003312ca96ef4a0c3552d60d64c680000998f10) else (if i < 558 then 0x50400000456000e766504c0010a5ee8319a0002308d4d969b4a010000aa8006280022d0dd4319a0002300d39152a77c16000012e5e18cd000118468003702c18c00077b3312c9b200101c2127c000ca09a410003be0b49648400024678be20003926d1b144519cf2f28000c40d80f5c82818a7086e818c8000002450002aa0020700064f3591800073c14a18cd000100c6b8abbd198960003843740c77c0006b230cd00011846a25a4ab2294 else (if i < 559 then 0x5936271a79c000dde3d129255720a3fe8001989600048449624000a52d8c2d16c0012e4e26ba1b0000e32061600014db870a000358bdb84c7c800005898109389000052088f400063c40000eec09c880000801287361484000249368da0008cfb800001431cf2210000c4023580001400000264a21645038c2c5c35b039858b37500000314000a1c6b0321ac000c2c5b03aa9344087ba0003282681a000b905000143a03c637fa192e39d else 0x49b000372470cedfc00028cf0001c6472253ae1951448b0009061c86c00092c4a19d29c000522500023f9459a73c000367cad8a8a84000003004421900000020a3be0000020e00092c6484945169947c7aaba4b192123be0000030e8c2b06000340014a962c59e248aa6f1e4613850001a000a52b162d4fd258c9091900004910a3be5530000e9360006e48c0014a536c5a6c9c2b138d3be0000060e64000000428f396940007a8fa4224b12))) else (if i < 563 then (if i < 561 then 0x3890000030895e00082238dd80014cc51cf2329ac8c39e465000186ae778bca440011955b860001de011114290003282600000601211b9800248851df000000073c48f74de3c77c0000081cdd954c000524d800027a333c0004111c86c9088da4926c0a0dc919df000002070006dc6271a75200005828f396980007a2524ab98140000053312cdb870a0003526c000dc91803a948000b48b0009061c86d1a092c49b70e1400068002948020b else (if i < 562 then 0x3506dc3850e6ec91e000292bc0010447000002a6d8b0003bb51622a8c0000021d4cd208c0848001c2a020d5336dc30212000004a521cef8001038637a2d82018d5330003021296e9ee00055129eb9720a0000059810900047637b1e00079c00c1ce7800001062f29de0001100054b4031a640000804295190423305aa32070068b5cc00031d20000b4d16828ea4e1501069a8000001070006dc4041a752aa608829b70e15010680000318109 else 0x6dc0030e77c000adc30fb8eec00089a82329c7080005294db1689692a6545100c00001838002212b70c0000013312c808a9d01c20000eed52c89bb2c98000a5cb52a4db168080009b221b6c000ca09800232ab70c54e0003312c6ecdfc000295f8eed64c8800000803073ee3bc45d22668db800035010000004436db241941364800032726788e229bc78eb54a40005a4db3d9b9230000223261000000602210e24000c084a308002020d)) else (if i < 564 then 0x3ad4c8000167ca00063c40000ef145889f7000002073340005051ad360008bc20001194d5c62baa151fa1b59a42a61f3675acbc0002cf94000c7880001de28b113ee0000060e668000a0a363114cc00050002c19ab8c67a00045e10e92000662590da3f525892cd3b9b0f9b00000a01e080008860061ccd000100c69a800017e883be46556e1866800000434000008bf44004a94b558b4040002fd107880009bc79b6e3dcca0999a0000030d else (if i < 565 then 0x4d90009221086c908000480014a536c5aa7020998967c046592210a2c0009b62c0000094a439df0001ac8c4eb3de32826b960006b230001194e3841e230a2f61e4030000010ea0a776a964501000136442578002090e37600053314b26776a0a4400003104470001de001913ee0000090ebe20006ae30cd160d414680000118f103ad0003e5169168baa521c00117400c399000019e8a00015338e1075a9169c82ceb54a522c580000499413 else 0x7f1420127cc00063c40efc00164862a62dbb44123bf6e64651889200000220d1dc88dec780029aac20d45e5fe3361260e0006e818000004e102a062251d61400044a00428000a44fe2240011a4c7482e619d800084cb3856271a000a44fe224ca800136c58001c2a950d5fe33b000109de94c64a48c04000350280003218b0600003b3021271200003010cd00000446a578002090e3760005331400077600e44000014d6061df2f880007)))))) else (if i < 588 then (if i < 577 then (if i < 571 then (if i < 568 then (if i < 567 then 0x15fa129968d263a414380015bc627cc330001957e3bb00022000b6eaae4932d1a4c7c80002fd1e58947a46931d2080400003e1cc1c0000483000000805053ad01e01e1600089400850001489fc4480019da2f084790004041adeb0309b62c001489fc4480019da2f0832a0004db168f303080835124000014440c8002c20d33c0005bb1cfe29ae000240012f4cdcb9a9c5a23d1000b7115841a00062c00e1400001523c424537a8000b else 0x52900000f0e65c84c0001536512400040000031e58947a00031e20000d1868c68d1c00000479d03702078c43d0007220c73edc0a3c30d4800000482c01dd9c7110003bb31f2268e8a40003d0f4001b783299a6ba088e0000060160abf4000c8e24000e1400432872212b78c0004765361e000af70ce21435ec0cbcaa6c99d800080003853160c00089600c500180017e84a870002b78c4f98c30003284a000900595f8eec00088032532ab92) else (if i < 569 then 0x47a000452210d6b0000024001e4d0487000000a10066434c550e1800089465451135f80d18d21e800391060007c04111cd98a66dbc24000e1000c31dfae58000c00056f4821268ec16a3c3c0e55f908048000081880d0000063ca0aa5265c0001d7e800191c48000012ff084795af0000c0408ecdbc3d5ed1d8dec7a94a13000076f533b0001000103062c180017f8cd4480023498e900004f43d4727500009a06c0014393286212b2b19896 else (if i < 570 then 0x23160c848000900591e5364c406800241291096cc4e44111c00000862c1800000920848001dd9c79142562d4802ca1cb96ade300002292084b660002088e7593853101adea89200020000eece38880000480d076140003101a000006be8311e800203081f72c90000686b57f420127dc00000218cf57c504470003702100947a64f31e2000000a620340016c000432feae5c160c0005fe420128768be00055b3135d97071a38000038f else 0x65a0005124663c0012022644800119461bfb8abb71600004a34c1600002c04e14000cb804838000019880d0004d93a210000ad68f2197f8d40cd44a6c8001d10833c0000091c00000c7f4300015ac00830002871d9893ee3bb6cb229ae000766240011d8dec7be01dda8a915cb56b0000c9aedc076624001048ecc4adda08800067193bb51622bf4000c8e2520800219c419e01d2090e0004260010e77e7bee303000112cca8a00019d80288))) else (if i < 574 then (if i < 572 then 0x3df00118d0ce049ee54d1d31547879dfa650000c61144b32a288860000041c0013610106aa13293511763161b6a22e6160000021d5092f1a88b8001c2001063350004041aca4978c625d8c52f1a88b9a38001bd8f00000257b0e0007be8ca313291e914c800023d004104ca000465180006a60021993cd4801c4b279a90000933c0004111c9b000099634000f2d1385a1dc21abd150007370020c63cc1600024cf135d04871c5b5100017 else (if i < 573 then 0x6868434f72ac660000081c00144ce1d39a38000008f71b42d65138dc099498a3000144ce1939a38000010f6310006a22ec36dea9782cefd32931460001e580e8b00000f4121c67a0000101c000005010699aa3c80b8643b8430002a9ee00000418001128ca8a1a99dc39b900003b886b2068e0220223c000e1000c319a8002020d00044b32a2877eb96e6030002404dc91806234b9b9000047a86b200006a600e18cd4001010680026b80187 else 0x54260e00000662c180014a5bd4599e8002720e0657594031aa8ca52dea2c000020c5833138002020d43b0000022a000886d32252bdd650487460221800094af7590001c9c8000af42dd3d7c5038623c8002020d4430000041273c000ade30e75ecc000caeba37800115218b2324248760009ee55915128000a19500037a8b4af0000011ca4286c64848da958cca4980001997e8800035100e12bfc000808340011e8c7880001a980086)) else (if i < 575 then 0x4ca8b45dc2000089422051894cec000422f2913f88944900000610678000b7639fc535c000499b0000010d7c000054b228520009404c440f2c4405a2f000000895fe7118191a66ce2303234000c5800c280008a247880005354041abfcfe266c2512444e15041838001ba061160003840a00089400651894cec000400029122f090e83856271a000a44fe224ca800136c58001c2a950d5fe33b0e4100000cc1d610c8c000070280019d97e88 else (if i < 576 then 0x44b0022800094caae4932d1a5e8c80002be8029a44d7590001c740000a3a31048001b804bc5000381159284c57d71e9968d295640474000f2c49a8a24800083bf91556f1800062c008140000094d878832bd800081108676471221e8ecc8e26151124000423d2348001031d0003cb1268e8a4dbc3d008000070398380000b0600000800b0a75a0002622d6bc0014a86b7a800000883bf12e465188bcfe200024efd9e80006000207a8f0f else 0x58875d5ce32ffacac662594a40000643997000007056f533b0001000001462c195ec0010f47800262a078c00050e00112996b2463c4000000cd7cf80024a23f140006563312c996b248a442138eec0008a65abf98f9036100032524dbeb6ea442536512400040000021e5890000026330c68e00087a3d64531503c61b0b6f992920000016330c68ec1687a3cd4844000080899dd98f910003850100c0000020181543174ce61626c99d80008)))) else (if i < 582 then (if i < 579 then (if i < 578 then 0x46931d20000a1c99430ea14e987cda3c8002ff0833c0004121ca1c8847f4300018cc01042ff000323890004766de1e00122a81c31694eed52c88002ff3238900046931d20750a747e86dbd4cec000400040c18b065290000080e000bfc66a250ed17c000a8002870020c3a80003f436cb6776000455ec0010f479b0b6fb7b1257b40f43d1e000bfc66a24ea0001340d80023498e900004f43d472000a1c99430000eec008880031699896 else 0x6140003101ae30000be830fb800000432212fd099091335fa4201200001cc6618d1c0010f478002e58048c4e80006095c93e0000064c0014380044afe8019880d7544d74121c000a1c00425500000c4069d03461a29a3cc84e3603f05800061e340015bd4384a3d43598f105b00003101a6a6000004421ad6000004c71bc9a088e31e15686b120000506203400004cf282a94997000070005af0090c00000a66a251e400000442bda441bd8f) else (if i < 580 then 0x33c0004121c000776002441095ad8cc328aa3b1bd8f00033b00110c4a92865450000040c5830001dd9c7913ee0000080e000b9600430002138d7cf9d02f82a21a57b00043d1e00000461e340015bccd44a1da2fb2d9500556f50e12000afc9042400143800c60003169989600044b32a289d2e6ce2eb9b30fe904872a30000010700044a32a286c294c64a48001128ca8a0002531929212e4ef48212dea89200020000eece3888000028a507 else (if i < 581 then 0x1273c02c24d2026e48cd1c000dec78000012bd870003df46518258a526162c00001215030002be1a29a00060b13512dc00008ca3193d1e8c7881a9a3d39b9000004c34c1600002c05e14000cb802038000019880d0004d93a210000ad68f2197e8d40cd44a6c8001d1085fa0003b31267800082439c61b80fe86000003b238900046931d20000996620357f920800040002b58008600050e4ca1800077671e4503512cca8a24100043388 else 0x4790004041a95e9b0000391fc00103861bfb042401662544a00028654000dea2e0600010106a948001c2874430000021273c00081c3132158cca49a578000870e4c16c955d500000285fa20000d4401c4aff0002020d00047a31e2021c6a600018d1c0000087abd888000071135133864e6f508718054000f2c4c858000022090e62500032a2800089400218cd5255010699e895a258700047a86b202406a60001910c4a000039dfa650000c))) else (if i < 585 then (if i < 583 then 0x42fd109cadea0002d1e4001010689e225800146864cc4f72a68eaf66f63c00123cbf44318be3b51173070003750c4366ec00014001550e1038002949858b00000139010fe26a119824d4c0011e882ee2c92328c00000135b3ced8ed8ed81cf68000429080001c071043230000180a0006765fa20000034c583312a4a0001432a0006f516a5200000c1d89c0010106a1d8000009569944300113180886000252bdd64000723faf8a070c else (if i < 584 then 0x5268c37bf3278a0006b678cd400100c6a57abd28e8e00057b37b1e95e0011ca38dfc001200b00044a2e58b00044b32a28bc8c3479e5d1c4e480007209000004896b84440000e00089400c51460000bf441cf0002328c36a4450002673a000cca64e4630c0005a0e3441921236a445329260000025fa20e459c5bd459b52228001300044a329280008880041ce454a40005a77a909921200057b37b1eecaa2ec224111155000038001c200306 else 0x14111d1ca00303021d64002060423423b1bd8f71d0da0001096c00065e5503512e194a37aa6c800080008183160c00000266a25ae0e4904872872f2ab78c3070003750c49e6ec00014001550e1038002949858b4e5000390106a60008f441771648d5c60001dd81a043230000290a00002862c1a488000bf442f28002328c00044400b0e000a52b962c001250ca8a271800000953c574f35b3c000d5e6f63c001491ad8fbda80000089)) else (if i < 586 then 0x48f2fd10c62000d445d86dbd60985a010000048732e0005540a00000a62c1a48954c00041c80001a60b00057e67112000a54620355edb790f47800225322945185530cc10ed80006b678000024d3059c88000028656b0003840a00089465451394000e4042410001d98939e55246518e3a00072020000c591242a4110c1d98900052a3101a00001a794156bc0000243206a25000140000036471200000303021ae1d6504472342441bd8f else (if i < 587 then 0x83160c7dc8880001dc74000bf440002bd9bd8f4af0008e51c910f8000034001794c3c64070001989691e44b730292440005fa2000111000839c8a948000b6c65213242400089400c512bce4800072090000008939e5d746518000af66f63c0013d8ddd22441c2bc98d32a0000021600070b03035321114ca49b63000192124af3920001c824d10000251fc00119460001c2afe0d48857b37b1e888aa80001c000e10004338e83297e88 else 0x35a3761400067400620000e24ecc498e22f000073073742f80c60e00000a18fd8000dd038001a80010938a00031e208de8ba64044db5b0d128a00000197c075298c400016dcc0007be30e3cef4c8088001a8002893340003e91aa540000042cd8c00129c91c53d198f103635b74a7246c600094e48e29e8c000800038a999963340003e91adcc6fe73c30bc4000a9c10001321780300035a093140000aa64044000090134219180000e85))))) else (if i < 599 then (if i < 593 then (if i < 590 then (if i < 589 then 0x4430007f1128300006a020000004f285a77b44192123525cc000211fab6e64848000008be031d6000206145184186c31000001081850ea800116ce0000019b68941800042e10e0a0007942d1a61acc78820c0001a8887050003ca1667c9c8d7039060001b0c40000022c18c40a0008c8520008926b6791a55a400081b12a6192120006f43ca16000004ce224d88000c90939c1f8a078f3626883242463665c8041cbd0c88000180019197984 else 0x6270030e000830aa620000ef8f7c61e2af61ad9e00041800110758a3081850eb1b0d030a1ba800004045dd0000020e8308f20002110cd41fc44a4a800206144180006c31000105901e310280023214afea249ad9e31b32e4010e00000e05610c1cdd400032ee80017c0700038936c128bc00083020d4c000c7880004359e50b4545915cb1800000a0181c000ef8f7c618e0003f88950e5dd0000c0000006a2214a5518f2859c280031386) else (if i < 591 then 0x31b32e0000e0000105f0180014d500c680020c0010833d0008c51c9a497467e60cd8d4400048001f898b8f33d0004b01c9968a4dca40cf6314000720c0002dd880006a23382e6c2000010480011b4dcd1a6c8001f50d52a0003ca169ca000640440014ac00848001deaeb8c51a6163322c9607e2c163c00001525c600030b199164d90004031aa540007942cd5c000c808a8d295aeb894d95834031a00002675234000020cd0318380001e84 else (if i < 592 then 0x3f55dd0c6a49f600040f2d0816e8580100017c063cb5720001664272200029d49259e1891e580026d8b4965b70002475a64800019518000be039a92e6000103218b400014000de8620352212611d87a75393a4da300035a02c1400001201c10000e24db049838000020631c0003740e83091e00020e28000c7882294943058f31c0002f80e6a600063c411781b90604000222201070005dd0010ca5275a0022d4a5518000598e1e5bf889 else 0x5350005460c64318877e28e1400189c31a9000001103210005af14a66ab8c5e38c840016bc5299aae0000e50d0007022a000bd4a7cecdbdeb8000a2de0001929261c46c49b460009b600a11178cb800038002b917c06321402000146a40009f64112d45dbe4a2102b9000064820002f80e642722dcc2800004006020000039a01800732e0000e0000045f018d480013ec81e5a102c90b32140100014796ae40002ccf935d390700019700187))) else (if i < 596 then (if i < 594 then 0x3e95af4041a840ae400018fa589d01069fa800001063cb572000166a40927cc40f2c00000459b1b4424b123570004e5227ac0006c880d8da2525890000151a8883cb000020167d200080834000010040222f197000074200002f80c67c9ae00038c850056bc51d6800002065dd0003740e6420006ea28d4a2d00008262a4c23b0f5460002f80e0009308ec3cd49da40008190ad78000a4b70005de2a6c6b6e00048ff9371ae5300000126c87 else (if i < 595 then 0x3e900035110796ae40002c00125953092441f882d0f0003750010c79675a9b62cf7c000be039e580026d8b000005350107d2000620352dc001778a9a9000000907694984761e6c6a991b848d8d6dc00091a92e6000103f34d0000368e48ac0005d7f0000c406a5b8002ef155694497113c00000c8041d77400000830001fa9a8883cb00748216796a8c0002d208000d4441b0b44a4b12000006350107960000062c0000059e831f49c2a020d else 0x230e1880800400021c892611d87a0200033d0836300049624d7a9308ec3c000010018319b1c28000d35300031e208087ea0002164593cc38627d80018f103365af6271a66ac4e00034000018c3861eb0001b2206e400031e2080800000420d8c00125893dd23ba03136484774062680800000220f58000d91037232798f1000003230e186426b20002800002406820001970008745e063351106a48a8000413ec000be030002d7a018d)) else (if i < 597 then 0x3c00004232c6c2000aae48f5800178100001df9870c572591000166ae00111045128001aa0a00023ba03933365af80c1a00077e61c30d8400001492e5aa30000b5574820001078000084858d5c000fb88b91492a3b0f0004965571066a00080834f2951800059e0000240967210004761e0000068ac6ce7400111cc80043d98e905708d062f1c6aedde7dc454a400002c5800008001063363850001a6a70d663c40cd589c00069f18001a018 else (if i < 598 then 0x35300031e208a800061c3112d45c000a229a3398b8f0005af4031a89400000050fa40000084355ab90000b7524966892400096c65e555c9435aac58001ba802860003ad4db16000794620340014a589c39f480040c084103f13171e7c600068060000004be039ef9df9870c5290004db160007e20063c000005140427dbb498f104fb5cc31e209231dafa0691c8000cdcb80000f201075dd00000c0c0009f663a40000fd4004419b2d7a020d else 0x4fb62f31e207ea0000041d4a55c80005ade36324b125525728c416ab872400038cd56bc000680000197c074045530001000089c7202cd85cf955c9294a271c88b00001e02d0800065c0121c00000577431a9a7d98e9008f3f50001000077e61c315c964400059e0000212160005af6271a894000bb050d894fd980900000399f980000022f80c6a600063c4112cf921e0a19f0002a48e0005af4031a8947c800050fa5360028400000217c06)))) else (if i < 604 then (if i < 601 then (if i < 600 then 0x3530005dd0caa67ea000215ca310e405aa9ae6000084fb0005dd0cae50d67202c00143801030001d69c88b40e00045010dc07ea0001d4a8f28c406b7000017c075290004db1666ab5e620351c8000cdcb80000380a8600053355c1cae000067c1d22c000008599b1c28000d35364f31e200007ea72020cd8e1501068002998020e57000033e0e9160000022cda51dd01c9ab92721c8080000045bb1066c00080834f280015c85c6200026c87 else 0x37b4517221e6000003381400005c4b4180023919c9700033a007100007d280834000c9800c3000000a30845af48f46014c4e65c8f21d1840018c4223c99717c072fc00000c0800065c0061d508001b5052281fa800065af6273a91a0000025f0191450f4c5c7a4a2250001440100000114a52c0e7202d18000100c68001a8ae4095293ca8c416a02860c6218000274c0849908000180a35900030e1800001002010000cb9008380000198e90) else (if i < 602 then 0x5a7418106ec6b4aa628c8c001014298a800001860003853111a0006b475228c4923d140418900000a8840c00044a280000106223603c000f7c6000001a620f32c000498160006b475228de90eda14a8001ad1d48a353453000207feae298c7603c000f7c61960000010b42600036742ed88926b67a310d680005000002181894980004c41f04c8de00045e4ce5000071a9a29b09104988e04c41e0006b48a028cb000231058001ca2dd8e else (if i < 603 then 0x36f495000290e60006806000175d7d0620b39d0002b69400054026a66cbc000398d50a8000db84b1032f900000003101b04c8df1984400005ccb421d1800009853150000030c6580009b62cdd4d6800051d49c2ad78d32c0004db16000b4e00620db0d4000048001ad1818a39e40e442180007289c838da407800099bd8000020f353452000206d8cbe00024000d68c0c5211a233041600035a410146d898600024e7903d108618a9c200006 else 0x4715152282ca08000ad160000005c3cdb042401670987a89a206247ea00021645be400062eba72800117934e40001c000ff89005a30d994000c8002dbb441263b61d6663e62400001620000014c4069908000018a32c0008c4167ea70800018f8c014d00c1fa9c2002063f53840000c6580000022cc856c00045190c620000a34743d7221e642aa600028000e1114031960000060b0000013101a68e8a29103cd1d1440007800237a8a91))) else (if i < 607 then (if i < 605 then 0x321000006146580011882c0016bdb7069ff8002cc9d48843d0001e6b2cf400030e391bd7948c9421e8000f4600006dc1a000af070c9da09ae16ec719680017984000020302126da00000a50000008c40699a9c2000063210060271492a70800018e7943a03c61908000020a32b0008c416624000aa620fd4e1000031a3a1ea618f0000013101a66a70803c18000e1007431a38000008f3123f54511065600000e2cc48fd400043c9a998000e else (if i < 606 then 0x3120000071000000a62034c84001180519600026d8b3e3000340306b2000ade3103d0f51d87ab19ef2a0133215534501462c0000081910c000c0849930002d388321553000148c070a80834000034c08480021ea3b0f321000004146f6aa600020cb0002310599b2d78000d35940f30f186f600000220cb1041208599b0000010d32c4100001671c8ba9ca44cb104000059cf2c19878c35000000310642aa6000291800010106c91237ac991 else 0x32b0004db168bc00000820cec000008519b0002020d37b5a64c31e6c2cf292c4909000000cb1b0800253124440006791466cd9c00634d84001298922200033c8a3360005061aaf6b4c9863cc040000f0299680000c843160000010c8c270a62034000034c0849cf2870000c00000530f1a6420008c028c4800154c41960002410b4970004a724ea0876b7a54cb000136c5990ad78000a312000450106da000002510410f5c887b622163221b)) else (if i < 608 then 0x3923131cbea8ded1444000e4800c71f2b8e0001000253300012be88ded144400104d4cc4abdb9123b0f4a08a34b41062c00002818dd4000030519600026d8b3a93850001a0008080042110cd4000049cba6924e983c48e70003c6b2bd8000311095bc0004800237af2914240008072cd509280005166537cd38e99600026d8b443000303126a0000002216bce150106ad79c28000d59100056f18af681ec163c00148910c49b6a2500014 else (if i < 609 then 0x282f30a65800002e2dbd400001842a98000018a0003ad0010c752a6a80834d64f7d9e860004339818937b4104761e7ea75a00018000f7c00862aa1ac8000a57b4104c41e000a1a9f05555000001c51d4afe0000d3c48e70003c99477200041920f7800099bd3910000f4760004de12a6672482638de90400007a3b000181898c53fa4131caa800118828ea400162c6a9a9c2800063593df000180007bc0144c00158c00c422f1a800009 else 0x40c49500028000df28843000164984483c5450ba8153120004501067c00000238f8de48cfcc2063d72e41431b0000060864600080a14c54fd8000318900008a080004793111a0006b475228cf23144187000006179853150000080c00075a6162cc7000001449fa8000018848f35a0001475200080834eb1b0ccaca4621ad2478a67135a30314638a4400024000d68c0c5338a451858b3153f60000c67c72695e3800013c32c197d99680004))))))) else (if i < 654 then (if i < 632 then (if i < 621 then (if i < 615 then (if i < 612 then (if i < 611 then 0x67f47071d221f6b767c618f2dc4c00059a3a4c0000f312000488100007eae4418cfa278000739c3d32210c3ca00000b16000e2667e60cf956400070000039f18636f3e40002868e0000023cc495c914441892b900008000470515220010f4c2241425c39ffcd9891faadd880005b000f0c62400000820cfa39400071a3a4c0000f00047071d231d70f4b0040d1d144000799f2720000e00047000322000bae8843000164a280820624a80194 else 0x7504f78a12ab22dc000030cf939000073a827c000156df5b7688247120005e610c84000050500000219f983125c2000108a00007c618e4000003c5b3cadb992123cb7130001662400001420000014c4068001fa8010633e3920001c6b2f4c88430d640015bc620639837c940003f55b00c67c72400038d1d2600007b93216acf1c1040003101a8a00008f218cf93916ec70000061880d00000533f3067cab200038c4800000840001fa9f186) else (if i < 613 then 0x5723f50000c68e01ee443c0016ed14031a3a288000f4580000047113400063a40001b81e98600028da769787a4715152200000463a40001088d18d211b043541650970e6203668e00000c3cc4800114442b91fa8000633e5330001c73ca1c0003125d48400091f72bf2f2910000037220c624ae400020cf94cc0007284b1abff9b3123f50001067c84eb7638d1d26000078002d8391063120000041067ca66000380016440046475c0618e90 else (if i < 614 then 0x4fe47c0004a8f600063a40fb80017948b16b60000165756356d53600000298618c495c914041891fa800083590304421868e9300003c00001530c3189000228083350003101a67c724000391ec000c7481acac8c858c3123f5000106b2df288430000024c40699a800000863123f58191073ca1c00030c4800114041958004858b4975210002468e000e423d5de2a8001200b80b99f9832b00001d1600001e67e60cf94cc000718900000108 else 0x33101a66a92a00018e794380006189027a28084950000020c6247ea00020cf94cd6ec71cf2870000c3120004501067ca6609238c8400009c519580000e8b00000c33f3000000662034cd400000431891fa8b68835950e82c186b2000002311ee030c7483d3221000063120004791092ea4200048d1c00130c799f3c98000e7a85c13ae5e68e0000163cc4800114442619fa8000635950e0001905800061e34cf9e48000724ba9080012))) else (if i < 618 then (if i < 616 then 0x39000008a166b200088430d1d1441d879aca870000c3120004791067cf260003925d48400091a38002618f3ca0004981600001e67e60001704eb97b3538a8001639d847000328f600063a400020bdaf098002030029700042f6a4387f08f800094e98001b54d9f70002f29146a60c64e5800085ed4870fe11f000129d300036a9b75e7245993a00105f1044c00146c004b9f72db2f2910007150012c7dcc5abca44fb80017948a0b281c81ab else (if i < 617 then 0x192f30888200067e6000003948831b68000019438a00031d206428f600028cd525518069a3a338000f321000001147148f663a41b80000008619580026d8b3357a64601a66a00061e34cac00136c5a0b800397ab7fc8526a92c64c7ea0002151800136c59b6800002945910004421871400063a40c851ec00051a3a290000f48880c4601a68e8ce0fe3cdb40000bca1908000120a0000013101a66a92a0641925400001031891fa80008 else 0x3215af0001492edbed1248000018c3c6989000001883210004601492e00094e4a3054356d0a9908002280a33e89e4af1c6240008f220c856bc000519f3c9a578e36d0000032873c77c00030c84001b80519b2d79878d0004d233f3073a000f0e64e78ef800061908003700a6e65c200010656000df22ccf8e496ec71c4800003043e300033f3062400000621b70000c406990ad78000a50e3be56f18db88f262034f8d348cfcc00005298109)) else (if i < 619 then 0x39e00056f1873af66c0c6400001d1405000001a91093e500031d20000dca62235221145c887800228a618f00052055724910b9262234ea5d64c4469cba6919f983010000320a62c7ec000180000a0c0849b600000e0439e3be000186da00000c50000058c3c69908002300a3120000021092e00094e48cfa3152bc71c800826d8b32b0004db1600001067e60000010c3c69908002300a31200000b1092e00094e495cd874d78f98900023c88 else (if i < 620 then 0x60755310f5c6da8bc24000db54cc4b130002869587f6075531068e0008203e4a0db40004a2f0002a98887f8656262ad86000aa62133d81c0005bac9c98000e87f0006262a000af4a6624d1e4a104078000a717c8700001b137060000045e814becc8c0002294a451858b3163f60000c5f600002a10c4800000c424b290800126890005221273d1b8ade30cf80016ec71a60000030b00000d45014000002a442401dd64c446800228a618f else 0x86136c522120006d90c225178001060420f8002410b8c435a0001400070adb8357f0efc0006461a0f1a19940235a554146360000201c00002ce10319f1c98000e3f5000004106766b400028000d414cc4a0f8002410b8c341d34332c4e00080834000d68ea451a38002288f793000928126dab9089450cd000118469930000008833b35a3a9148a06b475229008d6800050001d4a018d0003342f80c0000168945133c00001858001c98010e)))) else (if i < 626 then (if i < 623 then (if i < 622 then 0x36c00c1200081801051b0c00000c44620002678b8430004f72b18ad7120c38001405238bc620002678b0003ca4031b087142a1a5631000133c58001e52018d6754e73714483e00099e2d17800000c40002bdc940f00040c46828a2a8bb19844e3d1740008c62a384830e86136c0001283e00000a2d008000004522f0021c80845e00060710ce00006e48d579078d0cca010002678a55e41d3433200064601614c6c00002439fb00000086 else 0x41f0000031600083c686659c400231051ac9df2870c33e0009061c00077ca1c30000d6533c51aa1f2bb29000002b2f80c80200002c28001030024a0001b6001096c300045010008af72503d178001140420f9c88000b00041d34332000af60023e10da9d3dcac21c32a7b950003a94031a0006d800a254a8e440005800280b1897000001450106b281cb22311a0f3e4a07a0f9c88000b45e00045010000a02c625d1a0f3c0007a779e833492) else (if i < 624 then 0xf3b31200000c8de4603c000fe861a38002078f7fc0004802c7ae00099c80001075738c805003b441280f0003fa1868e00081e3cf5c00133903fe0002401600064f4232000000290849abe285898ab68a803e8aa5910003fa18ff8000900597f639cd6cf0001c217c0731c0004431268e79c0003d22000000442679d6a080b5143ee59322a54b160002d33d36d18028001a1020830003232f40a7460000141cfd80010c034309b600009 else (if i < 625 then 0x3b900120da29391bca9d898aa26dc3e3000246970008d485d46000b24dc84213501d76c9a67a0f8000b3f54820001000001a90848f5c00133901a38002080f0000063fa18ff483a00064001738cc8b1d50000009c8ac47d35e3eda2938000aa37964a2808357800313156d150000054ff800090059fe9075738c80022099f986600003fa18ff800090058001071738c9a38002078f3d77fa4ce407ea0000022203db98fe86267b558000b else 0x3ce0071e6a8b7400041e8d48000092feaa90000c0003ee593220000026906ddce278fe873a02fd29d215fd5524c51903000083020f14000d6cf2aba4b253920003a241810d5703099e2c000cd01103000000b138731c4436dc1267c948000380000a9128a0001b6b5c0900001246f2299e83e0002cfd520800041a38002080f3d70004ce400000367f430001981a2093fd20e800190005ce3322c754024000700017358257000001b1315))) else (if i < 629 then (if i < 627 then 0x3470008351ea2ae3a8e04589c00100c68000011d9897cf0003b262898d62792d9644000f7c63c5450abd150003a90701a0008c004814000cd004030001fb2aa0731c86100012ad60006162c001060ecc426b8002720e5526e60001800079c84e3c0013951c488000019a41b0006913b464c88000894513e219610caadd3c20001000047832726000000768c9cc1b11128a00000817c0731c000861120000166162c00239cd6cf0001e2a0c08 else (if i < 628 then 0x6270004031a000880f4c60d1c0020d47a8ab8eb3f910003de32726c4edb880634000db4ecc4a94a0f8000b62789e4031a0006daa66254a507c000580019d8028800040e3df180007bc64e4c001651b21700038ea38113475158351ec4e00080634f5e0ed9d1032c1ca0000e529000004169c86760002107c000ecc4b138002018d6e06f43df1800067601020001038f7c60001ef193930006e0533120008fcae87d89c00100c68002203d318 else 0x40744526d5f142d0c563f54ad010699319d8000800000a3b312668000808354a907c00059eb80029a2051b00052b2ed8c000d1048000004fe8638e3722349000064f46920000ef6666596e6470d6cf19a0002020d78a0006862aa551880002cf5c0014d10363344000120008d03332cb720006b678d1daf51d478001ba17c0600001a44a2800072801e38000cec02c40001b68040952941f000160007bc64e4c001038f7c60002ca3642e)) else (if i < 630 then 0x3ab63f84d38a36000a565c000008fe860002c9211903476bd5151e68ed7a81e3d508001c58b800203a229380f0003fa18000c9e84640002285b60a9a3b57a078f00000d44a2800088267e600000211bc8b308001fd0c34700040f1e00000688a4c0000050106c7eb27a11906af80a6852b1560008083546d01d4acbac98002020d51b00052b2eef4dc884641984000fe86000327a119038b0000052f1fa00080834d1c00103c780022099f98 else (if i < 631 then 0x40744526d5ec4cdb454002128d6cf1ebb76000200008fd6892468e000d7a3c00241511499d5bd3c269c7150004802c000044d104800006d128a000015a37910000144041a68e000a2a3c0019a111498000071fd0c0005924232000000ac4c54e2c000004ba04003416a80070003a55c00088267e60015408e5959c5800000978d47ce64c4600000474ab8f5c0014d10394be7326233d7000534411cedd86b679abc001898a9eb80029a20 else 0x3263a20001067a726b7638cf400129070001d120c0800044033f3000070af2435aae06227858002220010731c36c000126d68f088a4d4a400136c59d69ba17c0644400006a0e67a00000239290e4ce1030000299c2063f533b000100002c67662400107c05458002952020d00059346f22000e0a89450001104cfcc0000021fd0c7150003322c000cc0d12480300011149afc20f2e71900064f469207160000085c0023f5a2491a380035e8f))))) else (if i < 643 then (if i < 637 then (if i < 634 then (if i < 633 then 0x2602b0a00003a8881c000fd801032b58001858b31c861000120008307662135e315390718e0004308900000730b1600000483020001101278c473b7d1ad9e0004614791a78a0006b678cf0001b307425220a4f18000001418110308c2b16340011851e4699e0004628e3c500035b3c00079c0043d450fb80008b2e3c53da95557496000240007dcb4a4571400131461b6a530001435400000120ebaa4f08065c3a3c12d4d9fb00000106 else 0x36b478000266760000102800000d00839d52170001c0000034f50c00e75a01c2c00000510c32949d68060b4b4391000166a67cb0d64000107c0245800294c62070004b40010c75889492850000ef80086271800198157dc5c44a41c00000266055684fe929073ee1fd2520e38a3e586b2060264400014c1c00001832910001810900041f4db1664200099e294a4001008399f1c90000e36d7ae658280007085f01d4a4eb536c58001ad0640a) else (if i < 635 then 0x58343b4791a67c0008263911000000452ef22f9981500045f3302aa5299e0002ce28ee23ac800000317c070000044131cb4200066054cec00000451d531f27a9c72663e4f538b8877c7f430cec00000851d500027a9c5de63e3302aa5299e0002ce28f9400083b52080000f3ef7d757c340000145f820dad1e0000980020f80e0b0005290060e000ef000218ffd6e0d34e8001df2c88c5830004791aa546b20002938d0eccc0aaa9a014620a else (if i < 636 then 0x730b160000067f43160c0011e46b4321d8001552a3595de147148a863a40000004c2c5ae22c89fd0c7dc84350d2a8888040002a31000133c58001d697c0600038941f12c0e0005f820000f395ec7800462a578e0008434f72a00079480635452489f0088001b6010890385220000c0000225f820000028be03800002a098e3694a000026b42000660540010ed1e46a5bad78000a6ab4cf8181600077c7f4314ccd64000527180019815 else 0x3e14c40001866a00000234c51bd11e4418a202000087504f74e32a6280006a020cd40010106b558001d68b44a3ac8e02800043e544080006c0bc82000034839830000262f40a0007460361c000e2591c48001fb0028600000330b160000025f8223952912bc700021e27b9538a4fb31d2000001294838002394bf040000019858b6ab0004791ad0c876000554a8ea577850001e523c8d00058436842000910af63d60dc61ce0600000317e08))) else (if i < 640 then (if i < 638 then 0x39c587000329d4e4e6e48cd1c000fc47b05997000073e000056f180000045f82219cd6400052ae2f898a0e000359001146c692ea3e49128001030a382bbc26d8b38300000e0ca1c000ade30000d6402c50002008008737f7fc4802d0ce0006a020d1c0000087a4b800192925c98d13a91a000e4e6e48d25c000c9490004689d48d4205b7000171a8bbc876554cd2be31471a3b910000f4c335a0001484e95e00038000f3801838002a31850b else (if i < 639 then 0x6e65c98c01000095f18a38e70002000c8000012db8b40e00092510b92b5e808351396bc0006b23000000915144049251000080924a2112d6cd034a000010191843830000150c00065c00c1c001080c2859b0a90800120003252fc108886b400029579070000cc001c918a0e0000042fc110ce6b400028001080e4459f00001df8c8c53923141c0007e4c3e6d3b8000c9491f024b8000c00035a3bf1468e0007e23c0020b0ea068002ef19795 else 0x5f56bd3a91a0007e48ac6d7d5af4ea0680028722a8c3c50000011091abbcd3054001779a60ac600001d48d000660520240289dea542c0012be314700028728f0c3c5000925108840080001d0d8058c94900028748a8c4420000020e8026b40002a3112614a45800002a901200035a0031486c95e00038c5000171042771f930f9b4364af8c51c0006b400e28001779a60a800001adb8b40e00000110b92cc075235ab5000d3ce8003301d48d)) else (if i < 641 then 0x3a96274031a00009260424e0c000f883291000191843470003f11e0000526b6791c8000048b9e2800002086133f200036000002c3e1cd89480c9492901e81929200035a00b1400080200a1d10943800061b12900001200052b3a91a000bea7dc4630177938ca8002001a79d6ad61b00016000a54752340016dd48094602ef21d9592550e51e180006b4020280010040203a212870000c36252000024f8e0007dc44f14c9400040000009850b else (if i < 642 then 0x3a63f4620360007e8c406dc9a0d8d2ce1ea8003d52076c00035b3cdd8dc0a3a30000f88c0849f0a870000c00000f2fa0e8886b400028f2c000c2859be00000488000545345340000048c23513631400073b628e9ad9e5f43bd00022760000dfe74001788c9c9a8a0003910f70451e35b3c7d2000808352a51f000129f433b2ce2240135a000147960011882cdf120800041f48002018d3ce9257221e6aa70600019774000be838001ad2008a else 0x4cb5ba31e20000bf8cf4313296e8c78819a9d48000d4444033500e000a6a01034000cd4c084a21a010000744a0004952899600063c42310000c2458002411c8080007093131cb427726605400162cc245800196462074040005a7108860006042517c000cc0aa77b1a192122fb0000280800070602019774000be839ba9ad0000a3910008c4166f8000c0e21208000c084c629c90000e3350004031aac600064e4cd5000001081e70000008f)))) else (if i < 648 then (if i < 645 then (if i < 644 then 0x4300050c000ef11882ccd8000f2868000009868c50161b3372e8d91b892e48cd400101069b1800001920005b7391167c200061a310f61764a079f0a4b9868c0000270540468480a00010c20000e0c30001ad00a8a0000084501000075280834000cd4c084a21800001074cb00031d20658ef06122d128001254a4078002b68c4ca64f31e200000126042510c00000439963039848b000000324240009046122d11400128098001d48008d else 0x4ef00051f24bb80009f6413cd53a21cb1f0af89868c3740000020c7c000061a31081de136c5a1eb910000f3e04c430d1800086000218065de122c5a792a70001600035a392147c2ff861a3219cd680005000005808040000040070ce6c0009d0ba10d2d8000a80021da020d5635407ba260008407222c001b78c5c7a29bc227d900003f27ff3666a0007503610da190eca9ba000000863e06e630d1866a00080834f80000c34621eb912620f) else (if i < 646 then 0x5010003372ec36ef00002d39122cc5072792a7000163e164c30d189d400000610dd00000dc31f00001868c8673596e6140008600041a19cd6800053f13bc4620b3350004041b0ce6b400029f88000e445a3480027d908c53923b71c0000386a0216c8000c50700000800a8400000500e0c0006b518a28da4001ee89aa00001d48d0005b052a168209867e23c000d68e48526180018b8f00042090616000a6c75234da55000009a070001868c else (if i < 647 then 0x8354983f11efc40011882e10d2d8000a80046298a0e81843b6ab1a00006862838000cf6314526180018b8f00042000616000a6c752353bc0014fc92f080027d9044b81f0002881c00061a31841604df52a22b2f0001300058137d4af08c209f640f84000c3460001ac80b8a43d0003f11e000b026fa9400126000c5a050001c6293350003a91b086bbe87655770001dac80002f898a0e44a81f000288e31409ca44dd00980fc300021800186 else 0x6a750d5de2a00086001019108000c3460001aca010a0008670011066d0327523400181d4a4599b0001d48d5010003372e82098679e3c000d69008519a8001d48d00086700310000c0ea522cf84000c3462792a73fe164510004c31e000004a522e330e3800089f0aeb9868c3635b7557240000766e48c0000b8d4040000130138400000c0190c0006b400629114001ee89aa00001d48d84354143b2a0000069d0b9f88002310580046298a0e))) else (if i < 651 then (if i < 649 then 0x35a392146d2f740004c001604df529e58004830b44e0003a91b086a1a87655028000e3148001ad0020a0000023a91b086bbc000556f58d0c949421aef21d953cb00039117086a1abbc54f81438c34618600001287000007010088886b40002910c00000434622101c88b3e100030d180000025f82231181d4a45bff9f94321b3df00030d188046b20002a31000136c59ba8003bc064760003171e000c0e004214dc0013556357a86aef15 else (if i < 650 then 0x44e4d81d08696caf45610d2d90eca986201000073cb0008c41600000c6e48df880019e84000286a5b155830004041a9e40008485912c001720a1cec204419900000167a10896a30b90523514352d8a80000f2180430c4430000e0000285f820000034c50700019ec628a0000063171e7960000022e10d4355e8a8000009868c4535dc4fb20000b346906d14d93d3ec81e5a4c0000b00052a3a91a896b660005160c000c3463d82ef45095 else 0x58137d4a7980000047cf2d8ec0005a4d2cd3ff9b8190103a91a6188046e81cc3000002839e58002948b0000066071000103075234001436300aabd00018a0e4f20007fc2c6d2000d364d5655253b0c40c0001d48d590473577480000026e48d3c8001930b2c18001d48d81900047910796b60a542c000dd4030200000217e0830c0000020e796000a522d26984db74d9e5808c620b30c45e0000e7960011882cf318ec000f8000012020d)) else (if i < 652 then 0x8180003a91a8bea1aea0551d931000078001ad0048a00000300510796cf40002c0014a8ea46a3bab1c51938190003a91aa02d448aa5c0011e4ea469e58003558b4f26088522c7960011882d9e80000104000286a5b154f20004242d03000080835405469154b80027ba5b155010004552e9e4c10000580011e54ac6a3b8002b1934540006d920af400076e38000e380008a25b84ae4140003590191400000e01010c31110000380024797e08 else (if i < 653 then 0x3ce0006981e7c0a1c0003118400100c6bb628f1ad9e3553160000c0007c460424000004be839d81ffae39d00035a4011487ae452503c000210c0848000319f10600002f30d180007c001c10c300000103a221ad0000a00045e2fc10796000a522d26984e190d8001ad0010a00048f2fc10b0607e7523400000cbf041e58004620b0008c53141ce0496caf454f2c0023105ac18232020d30c0000050e0006b480428f2c0014a45b3d00030388 else 0x47b59231e20b0670a62234c49208000440c3139888d3e000056e180006b200a28001008008398922f000084793853111a6246a000022060ea4c4469890001c80845e8c43500e5f600002c1000002cbe838000021850b0003160010c6ea6b472228000f88c0849f02871df0c0003160010c6ea6b499e28f80000ef860001aca678a4450004eb26a1c7c460425008d680005000267a6d8b3913160000c0007c460424df0000e40422f80021e15)))))) else (if i < 676 then (if i < 665 then (if i < 659 then (if i < 656 then (if i < 655 then 0x43d89460b1e8f600063c410f400182c78001dba520e49a59b620369907bc0444c000d6a31051f03700000c0003a93111a6240010322112c000caca1fd3d726b8e3e000056e188ee0000044cf78cb000038011acc620a0003590031402a6580001cc48d40000440c9d49888d00032c8c40e6248bc000212dd3dd0f0a800006181090007780090e7be00000e30000d6401050001c29888d3120004791087a000c163d25947da2091890001c808 else 0x55180c0000026e8111851e5b7068000009c88b40e3e030d1887b25079c3c00000948820001a61c88b4d73923141c9ae00062838000f80c3462070002948b5b04d93ca1a6020002fc140000f816c11a1000191843074300000c00004a6122c000064c084800196009073df00002c180006b200e28000e14c44698900023c8843d00060b1e92ca3e00048001720caca000342a1d9584041c3443262400000e20001cc0caca0001e000096) else (if i < 657 then 0x3923141cdb88f280634000f84c34619a468a018d0003250010c8bc88660624f8a19cc0c48001ef9868c82c0004031a9e400066458000008018324a1d6000145d8442303126c4000cc049108000c0c4a3c993000085ca5363171e7c4a1c6062525112c000a000005981890005c83e20c00000c6e810000d314a45a80b0d0001773000030d18000b22dcc20000000c507230a3cac58d0003cb3911687a00079c3d03cf80c3460004339a808 else (if i < 658 then 0x4543b77bd2000076e63a40000fa500c68001f00020c00046f7192274092200068001211e3492442902be0f00046f5e5226dc928b9050e4133cc2459800001910530c0000250e00003280410d8400002092aba4b0000800048f0030c0007e70c86c000d30e405a30c0c1d40d3e200030312668000806355edaf4fc478000062ab88000005303120008867c418000d300045a2ea72c66114610004031b1a2cc061a3110c00000c30001a61c88b else 0x7bb3302a84eaf482638cd14d4000680000019815404000001109a0934a126d340fd1424d9ba000001863345350001b05800077c3172cd314a858001f09df0c00034c007160000068a02000206101068001c91898e4d07ff508360007806645a0600020b069a3abdb910f40e0004501068e81ee443cc88000bd4298418b0000600033a0111000099e6122c000004e44248325798a0e0003e241f12000a666283800000935c38001f01df8c))) else (if i < 662 then (if i < 660 then 0x63a6813ecd0a3ec3a4800001114442138001898e36900042826d5600080834e9dc39424d8000091959400036e00c128f00008504d2200000146b932168001c3a700050936dbab060003000101d154ba13a52acd8e0004c15435000080ea025c001e60cc0aa2980018f105bf6994ac42000982a86a1221e5c0006ab1800214130080003302a984f77082fc00110c00c4a3c0002141380f90b00018ea280e8aa5e03e42c0006261000218bf else (if i < 661 then 0x50e35045e1200080408a1c000d30c28580001f1c20634700001d1eaf6000b4e2000110c0144b932168001c4780004c82674c000a126c0022bccc0aad62be1a31a5714000003a00001665650001b9c0046262c1639c0d4c20004317e0000069904c000da504c72680002841b55e58860632c90f9800034020000cc0a800203a2a970085c06cd3f01edce000313080010c5f8002be1a31a0000014c826fe6f98ac635921f300006c148001d2ae else 0x436842b7e80c0005e370000c949389b1b00018809921370440011d270c9dc4d8d8000c00020300317809000370440007dc63e46370000c9492be0001a31a00042f00038d4c86469a76370000c9490001f718f9180900037044bd8978e6878e9c000000dba54749c32736f44a0002874e0000046d25c000c9494781f718f916946368163000200077c3000000cf843189000000883473ce57b1edea7209b62ccd0000c44698900024788)) else (if i < 663 then 0x4a54060002f1b800064a4806cfb8c7c8a4b800192924a54060002e000af465e55a521c6058c0002bd1979536f44a0002800000ea1c31295018000bb89b1a800188dc000325240007dc63e46024000dc11000326a9d2170f4be74e5ed28c6b02c60000084fe861b7a250001400001d32f2a74e0000146c000fb8c7c8c6e000192920004060052e000c6e70c9d3b5a50000c4048001b8225bf00036842bd8ff6e68780023a4e193b89b4a00898 else (if i < 664 then 0x534d3a000e0c70c9d5552f0000f34b29d8002d00c00037d4addb1e26e0880021d4e193b4b29d8002d5554bc0003cd58000004d4018000df52bdb0009bca400400037d4a00000268c69a122e1371334200026e2674600058660d4888efa465a558d8000c0001f718f9174a0003864f10a85e000715552f1d3cf24122f000094a00005ab260010546bc7d14d08c000800000b2098e3a700000a366de8940005000001143860002bd19795 else 0x88542f000380007dc63e440023a4e193b5f31b030188dc0003252400085e0047000101a214bae041a1af1f00047d35e3eb8080c0005c000fb8c7c88004749c3276be63600030aaa9780007a024000dc11478a191a69d6113b80002074c0c20c26d77108c000824b800192923a6000004360000046bc7d701018000b82f82f997958344068d22f1480006d0840020acd78fae02030001700001532f2ad2ac6c000622150bc000e0001f718f91)))) else (if i < 670 then (if i < 667 then (if i < 666 then 0x80100060d74e20ce0faa8c001d0cf35bc00800306ba00073b7f256da48b8000822c143e3999a4b8001929269563500030a16846000422919354e908000131fd0c00002332f2ac2284600040e98000034d8001f718f918dc0003252402a80c0005c002348d78fc42a178001c0008e93864ed7cd2a000615552f0000f0360001b42180900037044e400006f2900010c8d34eb564022d23500000736842b7e80c0005e370000c9490004691af1f else 0x8dc00032524e26c6a00060000fb8c7c88004749c32700064d53a42e1e97c000bd7b12f0000f3008001a31a00042f00c3800086469a7594d4ec0016b020001d8b05a20006f05200088ec0a66024000dc110004531bea500c49000050000e8679ade004001835d00039dbf92b80800c3995800086469a7594d4ec0016ad1000378290004477d2330120006e08a08c000ec580004531bea500049000551010000732b1e14000f75e0003a19e6b7) else (if i < 668 then 0x64d58442ec0000de0a5c3d2f80017c048001b82200049000b51046000762c1b4917000100002238031972000037949010000732b1166088001cb29b3e8002d0008a637d4b00201ac1aea020000e656329b3e818ad6d245c0004000088f19264002298df52c00800306ba8230003b160ca6cfa000b6020000e6560000001e6b76970005a46ae400006f291166088001cbb14081e93849700032524a16846172400000a11546285a1180010 else (if i < 669 then 0x6040003b16000092001ea1c3d2f80017c040001ccac65367d0005ab44000de0a400111d814cc048001b822720000379488b3044000e4002298df52c00800306ba6170005aa6cd2e000b48d5e14000f75e0000001e6b702a7a477e64e1e97c000be024000dc11329b3e8002d5a20006f05200088ec0a64002298df52c00800306ba8080003995800000279addeb14723a1eb4b8002d23572000037948bcef429b8995552f0000f0002191a69d else 0x69653b0005ab7297800078dbd128014a2859dc00010497000325240007dc63e44dbd128000a4520001b42188542f70d3892e00064a48d1c0020a87c1a318c69173470000ca1e9048bc000252800016ac99b7a250001400007a4131c000af465e5400178cd78fa52b18800173a60000493600008c8aa3142d08c000846e000192920003ee31f220011d270c9dc4da54000c3008001a31a00042f02138bd89780007800193561108002191a69d))) else (if i < 673 then (if i < 671 then 0x5b97fb7343cc2277026240da40016ac98000129af1f3a70000093692e00064a48d1c0003fc7ae03188001700000332f2ad2b0e2000623c0fb80008a85b7298f9036f44a00028a1677025240d1c0004a47b4ab1b000185c06310002e00002265e54000020d34ea85b72800108a40003684292e00064a4800000cdf528001f718f917f00003cd6e00ee0c70c9e215cd5c34e24b8001929250b6e5000200007dc63e46290000da1080043a9c327 else (if i < 672 then 0x3ee31f220011a46bc7c0023a4e193b5f31b0001888542f8ca38c22bb8000400023a4e193b5f31b000188dc0003252400085ee1a71a9901a214b8004151af1f4535dc0002074e00000c6c0023a4e1938001f718f918dc0003252400080c0105d3b5a50000c2df8061b4210008e93864ee26c6c00060000010da10c6e000192925bf4060002e0007dc63e456e52f1cd0f46e0001929200042f70d3800080d10a5c000fb8c7c8abe0001a31a else 0x4a00005ab260011e86bc7ce9c000008da52b18800170030054551868e00000a3d2958c4000b800000a2a8c36f44a00628d2ac6a0006125e340c949252b1880017000144455186de8940005114d770000846e468192920000313fa186de894000500000b8cbca9b48002d5933470000161e74c00000a6c000fb800c8c6e0001929200042f8ca381dac6310a5d845770c7c80002191a69d00000836842b7ec620005d845770000846e00019292)) else (if i < 674 then 0x59148230a16be29486263969c000030319a0000040d0000063500e0008be6605560cf7c00062fa1de800113470000011e6dc8948d05114ce28c7c81961c8a948b00039152a160006586a01cdb9128caca1c20001a80732c5723ad1600065a30e1c000010e1030001c89850b3120006f51068f06a0003d14d3edcdc819a0001888d31200048f100000046142c0011790804a212872c18c00006f3332c9048bc0002400004504c70002bd19795 else (if i < 675 then 0x38e8cc2200071463c4000111cd0cc8002ed26f1e85b60332b280009d2d90b965112c000a0002d38010832b00040e168f292a80834cace4180c58000009df0745438a31e20026b4e00020cb0e414a459a3c940000f3340000041a00a0320001d915128000a0001f01df0c32b39190b16000722a542c000cb0bb03a211ef8000c45338a31e200000110ce20001fcd010680019a40c8600039e002188840008f21ccb181d03858000009df07 else 0x66d439378480007c000e3110812c00048002251959458a0003322c668a6a000340011d19b523bb0001a71d3fd5076844c0008946565110cdb80004bbb2191a71d3a2000450100006a07c4240016e8c78823ba640001347657b7221e6148049141c0000f873820001f79a31a00002438912000032fa018000e7c050620aa980002b00072f00c0e000a8c6142c000f7800898002a0998154d049a9133668e0008503c00169c004426824d36e9b))))) else (if i < 687 then (if i < 681 then (if i < 678 then (if i < 677 then 0x8170003111aff2bc2cd2499d939da1d14308352100900034c02c160006580201d51800002830001ef8028c3345350001a80800000422184d440004c131f7466116dd3f450936000cf400220cd14d50106a729de800118ef3f4509360000028a0211e4e1501068001a89f1094773de000268ed05e9303cdd000005431d10000048844335000012be600069c74000f810c860002251959458a0003322c668a6a00034d4d08c000800022fa1d15 else 0x44b32b28cea000d0e8a05c000c446baeadf3c59900062f3111a000896656511fc00000462b2c0bb43a20003bd00322000df8e18a0e5c0018b8c3c32a6242126e142d6e83800072400c38001358e616250c88800130004755da3c8ba85200044001600c7c82b1c231888d00044b32b28cea9ced0e8909ce4800070002098050945200031e20b22c9e00030000ef400c88003adaa1a80005e148424cecff2d0e88001034caca33a800343a2) else (if i < 679 then 0x3d500085a40f3cd2a0004c00237d230bad7371325274df00034e3a864b2200031a910b4000e3938001b9a39223bd00022a100006906ce5d8d4000c2f134ac7b9347f5915c4180010d663c40000010c4468001e72bd8f51571d0002289c7240003934249cd20d8001c93178e0003ce4271e7500006906ce5d8d5c4cc332a239a2190003906f516000052ae418000f3806c780023b0088900076931e2000072400c38001fbcd9d0b70a168001c else (if i < 680 then 0x39102c16000b7463c4000112ccaca0002238089900075d3111a00079caf63c001124014f2f62c88000c0003925c41c0000007a6e5c990b4000e2aa9de803910003920071cbf8b2200030000004f4dcab1c6ec7b9372642d00038ac600109a4d6b1134000d1eabd542d2047f59151d1800072402c38000f3909c78002248061e5ec5910001924477a00045a910b4000e2840001a41b0007394f82ae4e0006e68ce5d8d4000c0002333dc16 else 0x3a849a613360006a27122569e1840003000196000874d93858181a00071463c4199630cd0cc9e58001c4890003513901000095e62638000008f286c3099a0000636e40c7ae289047440001cdb9030000a24a9c8bd70600032d00c0e62400000e20000d4400c48001e59850b5468610000ce4c85a9ea70000004f8832a31c89850b42067130a160007206142d5180015c8319a0001888d82c5cb5831862400007420000d41178480043081b86))) else (if i < 684 then (if i < 682 then 0x4943ac6c32861800000e1d0080000082279000199163e250e442127c400088424000cec004420724126d8b45157b4c41eb0600000211251129cc0a2fe00026d8b36f44a0002800067600420f2c0019c44b18b0d19b973cb350671120004da4e008000c882fc280000e048040000124db16000016dea20000cb00043aa317384d060004af3131c00081865650000db8e244800430805063d55e000040000dccb22311e400101068001c518f10 else (if i < 683 then 0x8b53e241f126acbca0004400001cc245c130000020700045171b1e0007c488424db9250000a000a99a098e70544b0002894c908cc048000f899c44a53a42330120003e2001126dc928ada51fc4000004220f9a59848b000671309166ac71ebca44c00000c8828001ac9868c4600003a91a0008b601618c3000001c3a01000002044943ac00028bf800075a2d81ccec00041e5a212410900033b4501081cc0e9b62d60c000dd0223c99d80008 else 0x5dd4012870e000c500021cea4fa51e468002258009436e35041f120006a083e2535deb8c5073730000030400034b309160007c483e240018a0008399e80018a0e36e4947ae289aebe262839bd4000c2458001f13388936e4946f92861062c00018000d6406461d48002020d00000200c08bba8020001e17d79648888001a59848b6ab0000030e0007c483e24000e3e0988a53a422ab9270544b0002879c000e443d29c00147c92421c780011)) else (if i < 685 then 0x4430008cc12cd20006484947cd6400062722f8a1b0e00044a32b2880800000620000d64ef860001a82e40933c53347f1c0006b277c30000db97204a8bae618f1038432c0000ec50000ae4216bcea400068001ac9df0c8eb80c4fb20614a520001cdd0000014319a1d48000d4040006f5100006b277c30d1d03c0007c0744a199165720006f5105106b277c30c88000bd4280019d00a883083160000c0006b201230001038c245800000b7a84 else (if i < 686 then 0x33c0007931c68f250b4a3c000e38c7c898f0001c4894e56f530a1600065a00a1c00002ce1030002a31850b3120006f51068f06a0003d220ea4c44698913b000080000044f50c00075262235bd400136c5a500002b1935f07e334634bbc00065e54cd0ea4c4468001a580e8b3750000170c66875200034000cb00343aef00019815404000005109680009404d10d17c000499e0002098e0003595f11868ee70d5e3d394e3800089a38002288f else 0x3474680001e66875200035778000cc0a8001a81c48932b58b00016000b6e64a4a1751b00011aeb3b79a31a0003503891268ee440003d220ea40006c0c2b91d68b4155305e95600080477c1c00002ce1030002d3802083470000011e98a7528083514ce2800082d29de98f9100054630a1600071c00444d1c0014547b32a239a1998cc000389128a871463e41150e280008370800003080003bd31f226687520003400162cc28598f0001c489)))) else (if i < 692 then (if i < 689 then (if i < 688 then 0x3cb86100012a1ac7c9ee5400010814020001ac8148c0004020180e00002070818000018cc0aaef9d48000d4045a700010000a8c6142c001108e2448001c7466113476a75151e00088471224001518c285aa09ef000133470004281e000b4e00420000ea50106b34a8fae51200038e8cc22c68a3ef1a48cd0ea40006aef0001981500058b30a168080000022110917ce244a210001c4896b878a4e41cc5000001c2169c0000243322a2500014 else 0x33c6b80001c0006b2b8830000f2d4a85a3fa25995945ba3cb52a1600065a8bc1d77d8f90eca8001968010754600030a167970c2904240000554a858002259959400036e0101200079c0163c001da4c7882c89ac8000c8b53bd000220007f4dd038f55ea8001000034d1b32150800034836f3e000ac64d6b1134000d1e62b98001f3976356953084e9c8000399780010a09a3f9ac8000c8b53bd6e8231c079c0003d2840010a09b3aa73c1022) else (if i < 690 then 0x3220410a00002c6ec1000100802038000011850b5462e80000c35823cae420000ea4f28680019a000863cb861389128f29b200020f2c1b0e244b140000030800035038912b4f0c200018000f2d36c58001acb730c0003a98181a67895eb8839bd400136c59e58001c4898610000020c6dc75800050cd0ea4f286ad81d49e50d0003a93111a0006689ea18c4800003040001a88048900032d0010ea8c7966142c000f395ec780000218f10 else (if i < 691 then 0x71b4510001e0007c488424db92511a0a382a25a17940003e267112b5a0000041cd591bc0008b8ca8b2098e36e44b42f2860000064414000d64c3462300001d48d30c0000090e80400000a113c8000cc8b00019d8010854e4790000c7c485c88426048f79590988429a800063e20004421285c6762242160c000008226c99d8000849444b42f286e8a6a000197f000136c59b7a250001400033b42f10796000ce2256ada6d920980005d07902 else 0x3343a90001a00062200a11010000004421722f9c48900058b30a16fec000712257c4fe539070001a61850b40467a0001068eb3c8a23d008cb400021961a62948b3220002f50a00067401420c20c58000300027a801845dd4010000e0006a0fe22535d2bcc50737a8001848b40e359000180007c4ce224000fe4c5071ab2382f2913083160000c0009ea0041177500400038061f121709000007309166ac71e00044000d65794641300000187))) else (if i < 695 then (if i < 693 then 0x44a002280006dcb90250104150b842020002178834757b4681e70804a0001c001fd8f88480000318f1000000342e1000069881c2c00112ccaca0022999898e8eb34c0001668e81eb3c3c0000090b840001a61f30b5af3a94041a0006987cc2d6bcea6030680000b1df0700000a3840c00000c6ea1000169c00c40002a31850b34759e0001e84e7f262639fd8000e2449cea239a19900054630a16624000dea20cf0fe571072ef00019815 else (if i < 694 then 0x1113840c000a8c6142cc48001bd44217221000095c800032b2868eb3c0003ccf15e904c70001d49888d0003345af0c62400000220d1cf392207b7a00026d8b3473ce0001e85cdbc000252800010a09800241a6e2642754f4131c6ea00002618cd0ea400068002018060744200000312bbc0006605501117c00040189a61850b00034c30a16808000008212d0001280999e0002098e57a0003302a68eb3cd5e3d778000cc0aa72380a098e else 0x23322c80859e0002000962cc2858002c59850b40454e00010bbc1ec66054001fd8e244800004a17080000063131c000002008191e4ea50106a8c2250001432b00040e1666875280836418104eb458001d4a020d4793345af0cb4e00000819915128000a1a3a340000f3343a90001a656b16b3c2cd1dc8800078002b91d68b4883a98181a00065a01a1c000014cbca8002ef1c20600054630a16624000dea210b910800049a3acf0850f)) else (if i < 696 then 0x5a78610000c6567969b62c000ea4c44680019a00806312000006100006a2006250b8cb400038001e72bd8f6e10db31e2000065a8bc1d519de0c28586e1968000742e86100012000006a542c000f380047c70225995940ee44b32b28b3c79c0003d2840010a099b7a25a1794312000819100006a27c4250b8cb400038001e5a950b7223ce57b1e0006b20b2300000780d82000201005070000013840cfec88471225108000e24499a1d48000d else (if i < 697 then 0x36e389120006de9b62c000d6564463f52cf2138f42e8613891200000e7122400000d0b840001e5a6d8b0004af3131c01e81865650000f2d36c58001acb730c57b59e6f01e0006a0004200012bcc4c71b720628c145720e64db1600081801450000db8e2448001b7a6d8b00000542e1000091e00418000d6564460192579898e0004af3131d0307528083569e184000319e257c830e00000242f1000095e626380ad23d46030001a81c489 else 0xb4cb78080015817783321000201147540001da700002e435810001910228500002d3760800080400a1c3b4000c2858001d49e50d5ad4d90001079600071226184cd0570320480000aa900045a0080c000b4e00c200012bcc4c700020602514))))))))))

/- Each search row uses seven bits for the prime index and twelve per child.
   Most nonterminal children point back a short distance. The dictionary stores
   the remaining backward offsets and the terminal witnesses. -/
private def offsetBlock (i : ℕ) : ℕ :=
(if i < 29 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then 0x226022502240223022202210220021f021e021d021c021b021a02180217021602150214021302110210020f020e020d02090207020602050204020202010000 else (if i < 2 then 0x24c024b024a02490248024502440243024202410240023f023c023a023902380237023602350234023302310230022f022e022d022c022b022a022902280227 else 0x2a802a70295028f028e028b0277026c026a026902680266026302620260025f025e025d025c025b025a025902580257025602550254025302510250024f024d)) else (if i < 5 then (if i < 4 then 0x330032e032a0325032403220321031903140311030a030803060303030202fa02f002e802e502e402e302e002d602d102cb02c202c102bb02b302b102b002ae else 0x42f04250420041d040803e903de03c703c603c303b4039e03820376036a0367035e0358034d034c034903470344033c033b0338033603350334033303320331) else (if i < 6 then 0x651064b06450637062e060105fe05ec05da05d305d005c4058c05630561053e04fb04f804e904e204da04cd04c204ba04b304af049a04990480047804660435 else 0xe1f0dcc0d710ccd0ab70a8b09a90962085a083107fc07b2079b0793078f07880782076e075d075707130704070306f206de06ab06890687067b0677066e0669))) else (if i < 10 then (if i < 8 then 0x80188017801680158014801380128011800f800e800d800c800b800a800880078006800138d5375121101875180815441431141d11320fbf0f660f640f0e0e21 else (if i < 9 then 0x803b803a803980388037803680358034803380328031802e802d802c802b802a8029802880278026802580248023802280218020801f801e801d801b801a8019 else 0x805f805e805d805c805b805a805980588057805680558054805380528051804e804d804c804b804a804980488047804680458044804380428040803f803e803c)) else (if i < 12 then (if i < 11 then 0x808280818080807f807d807c807b807a8079807880778076807580748073807280718070806f806e806d806c806a806980688067806680648063806280618060 else 0x80a480a380a180a0809f809e809d809c809b809a809980988097809680948093809280918090808f808e808d808c808b808a8089808880878086808580848083) else (if i < 13 then 0x80cc80cb80ca80c880c780c680c480c380c280c180bd80bc80bb80ba80b980b880b780b680b580b480b080af80ae80ad80ac80ab80aa80a980a880a780a680a5 else 0x80f680f580f480f380f280ee80ec80eb80ea80e980e880e780e680e480e280e080de80dd80dc80db80da80d880d780d680d580d480d380d180d080cf80ce80cd)))) else (if i < 21 then (if i < 17 then (if i < 15 then 0x811d811c811b811a8117811681158113811281118110810f810e810c810b810a8109810881068104810381028101810080ff80fe80fd80fc80fa80f980f880f7 else (if i < 16 then 0x8152814d814c814b814a81488147814681458143814281418140813f813e813a81348130812f812e812d812c812b812a812981278126812281218120811f811e else 0x8195819481938192818e818981878186818281818180817c817881778176817281718170816c816b816a81698168816481638162815e81578156815581548153)) else (if i < 19 then (if i < 18 then 0x81e281e081db81da81d981d881d781d681d581d481d081c681c381c281c181b881b481b381b281ac81ab81aa81a981a881a781a0819f819e819d819c819b8196 else 0x82278226822582248220821f821e821a8216821582148213821282118210820f820d82048203820081ff81fe81fa81f981f881f081ef81ee81ed81ec81e481e3) else (if i < 20 then 0x8290828f828e828a828982888284827e827d827c827b82748273826f826282618260825c825b825a824e824d824c824782468244823e823d823c8234822f822e else 0x830b8307830682fb82f282ec82eb82e482e082df82d982d882d482d182d082ca82c982c882c782c682bf82be82b782b082ae82ac82a8829e829a829982988297))) else (if i < 25 then (if i < 23 then (if i < 22 then 0x837b837a83798378836a836983668365836483638356835283518350834f834e834d834c834383408338832f832e832583248323831f831e83178314830d830c else 0x83f783f683eb83e883e783e083dc83db83da83d983d883d383d283c883c683c183c083bf83ba83b483b083af83ae839b838783868385838483838380837f837d) else (if i < 24 then 0x84778473846b846a84608457845684518450844a8440843b8437843684318430842f842e842a842984288420841e841d8413840c840b840a8401840083ff83fe else 0x84f784f684f584e284de84dd84d984d884d784c484c384c284b984b884b784ab84aa84a4849f849e849a8499849884978490848884878486848584848483847a)) else (if i < 27 then (if i < 26 then 0x857e857c857b8571856f856e8569856885618560855f85588553854e854c85478545853e853b853a853585338532852b8520851f851e851d851c84fa84f984f8 else 0x865c864f864a863e862c8627860e8604860385f885f485ef85ee85ed85e185e085df85d685c385c285b685b085af85a885a485a385a285a085968590858c858b) else (if i < 28 then 0x86e886e786d686d586d486ca86c886c086bf86b386ae86a686a586a4869e869a86918690868f86888680867386728671866f866b866686618660865f865e865d else 0x87a987a88790878f878587848780877f877d8774876f876a8762875e875d875c875b8746873e873d873887218720871a87198717870e870d870c8706870086e9))))) else (if i < 43 then (if i < 36 then (if i < 32 then (if i < 30 then 0x88af88ae88a288a188a08887886e8861886088568855885488438842883c883b883a881a8816880a8809880887fe87f187e787de87dd87d887d087c687b687b2 else (if i < 31 then 0x89918990897e8972896e896d896c8967894a8940893d893c893b89318930891a89138912891188fb88f688e688e588d588d488d388cf88ce88c088b788b688b1 else 0x8a6b8a6a8a698a688a5a8a4f8a438a428a418a408a3f8a3e8a278a238a178a0e8a0d8a0089f289ec89e589df89cb89ca89c989c489c389ba89b989b489ae89a0)) else (if i < 34 then (if i < 33 then 0x8b488b418b408b358b208b1f8b0d8b0c8b098b048aea8ae98ade8ad58ad48ad38ad28ad18ad08ac68ac28abe8ab78ab18ab08aa68aa58aa48a8c8a7c8a768a6c else 0x8c588c578c4e8c4d8c488c478c388c378c2a8c1f8c1e8c088bf28bea8bd08bc68bc08bbf8bac8bab8ba48b8e8b868b7f8b6c8b6b8b678b628b5e8b528b4a8b49) else (if i < 35 then 0x8d978d968d958d948d938d8f8d6f8d668d5e8d4a8d498d488d368d348d338d2e8d228d148d078cf88cd88cd68ccb8cc28cb08ca08c8b8c8a8c7c8c7b8c708c65 else 0x8ec68ec58ec48ebe8ebd8ebc8ea68ea58e9f8e8c8e8b8e728e458e408e298e288e238e228e1a8e0c8df78def8ddf8dde8ddd8dd08dce8dae8da88da78d9c8d9b))) else (if i < 39 then (if i < 37 then 0x8fe48fe38fe28fdb8fce8fbe8fbd8fbc8faf8f8a8f888f878f838f788f778f608f558f548f4a8f498f488f408f2e8f2d8f228f1e8f1d8f008efa8ede8ed68ed2 else (if i < 38 then 0x91ce91cd91cc91bf91ac91a8919c917091659164915c9130912f91289111911090f990f890c490aa909f909690899088905990559054902c8fff8ffe8ff78ff0 else 0x935e934093389324932393229321932092e892d792ce92c592bb92ba92a592a09294927a926b925a92599242922d92209210920f91f891f791f691e191df91d3)) else (if i < 41 then (if i < 40 then 0x952f951294ff94f894ee94d694d094bf94be94ab94aa94a9948394829480947f947e9476945e9456943f941e940d940393db93da93d293d193cc93979396935f else 0x96b096a496a39694968f9686966596429641963e960a95f995f895ea95d495d295c795bc95b795ad95ac95ab95aa95a195a0959f95629553954c954b954a9533) else (if i < 42 then 0x985798569846983c981f981e9810980497f897e697d897cf97bb97ab978a9760975f9758974a97459720971b9701970096ff96fe96fd96f296d096c696c596b1 else 0x9a199a099a0899f299df99de99b299ae99ad999b999a9984997d99629960994e994d994299269925990798ff98f698e298db98d398b098ae98a89892986e986d)))) else (if i < 50 then (if i < 46 then (if i < 44 then 0x9c379c359c349be39be29be19bc19bc09b759b5e9b509b389b2a9b269b119af59af49ae89adb9aca9abc9a809a7f9a6f9a6d9a5e9a469a459a449a439a299a27 else (if i < 45 then 0x9e829e819e809e799e789e449e439e3e9e0f9e039dae9dab9d8f9d8e9d8d9d649d5f9d4f9d4e9d329d319d009cd39cd29ccb9cca9cbe9c929c919c629c599c46 else 0xa188a16ba16aa154a153a100a0f3a0bda081a07fa066a05aa058a02fa017a016a0159ff09fd49fc89fbd9f939f729f5c9f139f129f069ef19ee09ec29ea89ea7)) else (if i < 48 then (if i < 47 then 0xa422a3fca3fba3cba3b8a3b7a37ea37da367a365a364a31fa31da31ca310a2ffa2e2a2cda2c8a26ea253a252a244a243a211a210a1eea1eda1dea1c8a1b0a198 else 0xa7b4a7a4a78da73ba730a70fa6fea6e1a6d7a6bea6bda6a1a6a0a672a648a601a600a5ffa5e4a583a579a578a574a52aa529a4eda4c7a4a3a49ca490a468a435) else (if i < 49 then 0xab0fab0caaecaab5aaa8aaa7aa7faa7eaa7daa6faa68aa67aa29aa26aa07aa06a9a2a980a97ca97ba95fa958a952a8c8a885a871a853a833a82da829a808a7d7 else 0xaf47af42af2eae8fae04adfeadfaadf5ad8ead8dad8cad8bad8aad53ad33ad16acecacbfacbeacaeac84ac83ac82ac6eac27ac14ac04ab7fab72ab65ab29ab10))) else (if i < 54 then (if i < 52 then (if i < 51 then 0xb3f2b339b2b9b27eb278b24eb24cb219b203b1c4b1b6b168b151b147b146b11bb0b1b09cb089b05eb020b01fb00aafe1afbcafb4afa1af87af86af69af59af58 else 0xb8c6b876b875b80eb800b7ffb7c6b750b6edb6ecb6bcb670b62eb600b5ceb5bab5a6b596b595b594b578b50fb4b0b4a9b48eb477b476b43fb432b415b3feb3f3) else (if i < 53 then 0xbf29bf28bebabea4bdffbdfebde6bde0bdb7bd7fbd4ebd46bd2fbd04bd00bcc1bca1bc60bc08bc07bc06bbefbb91bb18bb00bad9bac0bab4ba64b9f7b950b908 else 0xc40fc3fec3fdc3fcc376c34ac349c330c310c2d7c2b8c29ac27ac279c275c247c209c1c3c1b3c17ec12bc100c0bfc07ec057c04fc01ec010c00fbfffbfe0bf60)) else (if i < 56 then (if i < 55 then 0xcb70cb5bcb27cb1bcaa4ca3dc9dac9d9c9a0c947c938c922c8fbc8a8c83ac7f8c7f7c7f5c752c73fc6ccc6aec69ec5fdc5d3c518c4a8c4a7c4a6c488c432c431 else 0xd158d126d120d0c5d069d016d015d014cfdfcf9ecf97cf50cf1ccec3ce92ce28ce27ce20ce0ccde6cde5cd7ccd08cd07cce3cc8ecc5ecc2ecc02cbebcbeacb8f) else (if i < 57 then 0xd906d866d84ed84dd7acd6f7d68ad66dd655d653d652d619d618d586d56ad55dd4d3d4d2d4b9d49ad467d44ed404d3a4d3a3d388d37bd333d2ecd2c0d294d1ea else 0xdbecdb6fdb4ddab2da2cd9d8d9b7d972d91ed90bd90a))))))

private def dataAt (i : ℕ) := ((packed (i/32)) >>> (43*(i%32))) % (2^43)

private def primeAt (row : ℕ) : ℕ :=
  ((0x3c77054b4e51b4651543d0d41d013ecf13bce9394e337cd331cc5304bf2d4b32b4a728c9d25c9522c8920c7f1c46d1ac67194611645313c4911c430f43b0d42f0ac290941f0741704c110340b01c0500c00 : ℕ) >>> (10 * (row % 128))) % 1024

private def childAt (i row j : ℕ) : ℕ :=
  let code := (row >>> (7 + 12*j)) % 4096
  let value := if code < 512 then code + 1 else
    let k := code - 512
    ((offsetBlock (k/32)) >>> (16*(k%32))) % 65536
  if value < 32768 then i - value else value

private def valid (e : Env) (n : ℕ) : Bool :=
  decide (1 ≤ n ∧ n ≤ 23532 ∧ score e n.primeFactorsList = some 0 ∧
    score e (n+1).primeFactorsList = some 0 ∧ score e (n+2).primeFactorsList = some 0)

private def replay : ℕ → ℕ → Env → Bool
  | 0, _, _ => false
  | k+1, i, e =>
    if 32768 ≤ i then valid e (i-32768) else
    let r := dataAt i
    (List.finRange 3).all fun a =>
      replay k (childAt i r a.val) (put e (primeAt r) a)

private def Covered (e : Env) := ∀ w, Agrees w e → Wins w

private theorem replay_ok {k i e} (hc : replay k i e = true) : Covered e := by
  intro w ha
  induction k generalizing i e with
  | zero => simp [replay] at hc
  | succ k ih =>
    by_cases hi : 32768 ≤ i
    · have h : valid e (i-32768) = true := by simpa only [replay,if_pos hi] using hc
      obtain ⟨h1,h2,h3,h4,h5⟩ := of_decide_eq_true h
      exact ⟨i-32768,Finset.mem_Icc.mpr ⟨h1,h2⟩,score_ok ha _ _ h3,
        score_ok ha _ _ h4,score_ok ha _ _ h5⟩
    · simp only [replay,if_neg hi] at hc
      let p := primeAt (dataAt i)
      have h := List.all_eq_true.mp hc (w p : Fin 3) (List.mem_finRange _)
      exact ih h (agree_put ha p)

private theorem combine (e : Env) (p : ℕ) (c0 : Covered (put e p 0))
    (c1 : Covered (put e p 1)) (c2 : Covered (put e p 2)) : Covered e := by
  intro w hw
  have cases3 : ∀ z : F, z=0 ∨ z=1 ∨ z=2 := by decide
  rcases cases3 (w p) with h|h|h
  · exact c0 w (by simpa [h] using agree_put hw p)
  · exact c1 w (by simpa [h] using agree_put hw p)
  · exact c2 w (by simpa [h] using agree_put hw p)

private def emptyEnv : Env := fun _ => none

private def env0_0 : Env := put (put emptyEnv 2 0) 3 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok1 : Covered (env0_0) := replay_ok (k := 1) (i := 32769) (by decide +kernel)

private def env0_1 : Env := put (put emptyEnv 2 0) 3 1

private def env2_0 : Env := put (env0_1) 5 0

private def env3_0 : Env := put (env2_0) 13 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok4 : Covered (env3_0) := replay_ok (k := 1) (i := 32793) (by decide +kernel)

private def env3_1 : Env := put (env2_0) 13 1

private def env5_0 : Env := put (env3_1) 7 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok6 : Covered (env5_0) := replay_ok (k := 21) (i := 90) (by decide +kernel)

private def env5_1 : Env := put (env3_1) 7 1

private def env7_0 : Env := put (env5_1) 31 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok8 : Covered (env7_0) := replay_ok (k := 1) (i := 32830) (by decide +kernel)

private def env7_1 : Env := put (env5_1) 31 1

private def env9_0 : Env := put (env7_1) 127 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok10 : Covered (env9_0) := replay_ok (k := 1) (i := 32893) (by decide +kernel)

private def env9_1 : Env := put (env7_1) 127 1

private def env11_0 : Env := put (env9_1) 11 0

private def env12_0 : Env := put (env11_0) 53 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok13 : Covered (env12_0) := replay_ok (k := 1) (i := 32821) (by decide +kernel)

private def env12_1 : Env := put (env11_0) 53 1

private def env14_0 : Env := put (env12_1) 17 0

private def env15_0 : Env := put (env14_0) 137 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok16 : Covered (env15_0) := replay_ok (k := 1) (i := 32903) (by decide +kernel)

private def env15_1 : Env := put (env14_0) 137 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok17 : Covered (env15_1) := replay_ok (k := 38) (i := 396) (by decide +kernel)

private def env15_2 : Env := put (env14_0) 137 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok18 : Covered (env15_2) := replay_ok (k := 26) (i := 591) (by decide +kernel)

private theorem ok15 : Covered (env14_0) := combine _ 137 ok16 ok17 ok18

private def env14_1 : Env := put (env12_1) 17 1

private def env19_0 : Env := put (env14_1) 19 0

private def env20_0 : Env := put (env19_0) 23 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok21 : Covered (env20_0) := replay_ok (k := 12) (i := 613) (by decide +kernel)

private def env20_1 : Env := put (env19_0) 23 1

private def env22_0 : Env := put (env20_1) 37 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok23 : Covered (env22_0) := replay_ok (k := 1) (i := 50343) (by decide +kernel)

private def env22_1 : Env := put (env20_1) 37 1

private def env24_0 : Env := put (env22_1) 41 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok25 : Covered (env24_0) := replay_ok (k := 1) (i := 33792) (by decide +kernel)

private def env24_1 : Env := put (env22_1) 41 1

private def env26_0 : Env := put (env24_1) 151 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok27 : Covered (env26_0) := replay_ok (k := 1) (i := 32919) (by decide +kernel)

private def env26_1 : Env := put (env24_1) 151 1

private def env28_0 : Env := put (env26_1) 61 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok29 : Covered (env28_0) := replay_ok (k := 1) (i := 33072) (by decide +kernel)

private def env28_1 : Env := put (env26_1) 61 1

private def env30_0 : Env := put (env28_1) 73 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok31 : Covered (env30_0) := replay_ok (k := 34) (i := 697) (by decide +kernel)

private def env30_1 : Env := put (env28_1) 73 1

private def env32_0 : Env := put (env30_1) 47 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok33 : Covered (env32_0) := replay_ok (k := 19) (i := 722) (by decide +kernel)

private def env32_1 : Env := put (env30_1) 47 1

private def env34_0 : Env := put (env32_1) 157 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok35 : Covered (env34_0) := replay_ok (k := 12) (i := 746) (by decide +kernel)

private def env34_1 : Env := put (env32_1) 157 1

private def env36_0 : Env := put (env34_1) 29 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok37 : Covered (env36_0) := replay_ok (k := 1) (i := 33317) (by decide +kernel)

private def env36_1 : Env := put (env34_1) 29 1

private def env38_0 : Env := put (env36_1) 59 0

private def env39_0 : Env := put (env38_0) 67 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok40 : Covered (env39_0) := replay_ok (k := 1) (i := 34242) (by decide +kernel)

private def env39_1 : Env := put (env38_0) 67 1

private def env41_0 : Env := put (env39_1) 103 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok42 : Covered (env41_0) := replay_ok (k := 1) (i := 41831) (by decide +kernel)

private def env41_1 : Env := put (env39_1) 103 1

private def env43_0 : Env := put (env41_1) 251 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok44 : Covered (env43_0) := replay_ok (k := 1) (i := 33018) (by decide +kernel)

private def env43_1 : Env := put (env41_1) 251 1

private def env45_0 : Env := put (env43_1) 173 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok46 : Covered (env45_0) := replay_ok (k := 39) (i := 1034) (by decide +kernel)

private def env45_1 : Env := put (env43_1) 173 1

private def env47_0 : Env := put (env45_1) 43 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok48 : Covered (env47_0) := replay_ok (k := 5) (i := 1038) (by decide +kernel)

private def env47_1 : Env := put (env45_1) 43 1

private def env49_0 : Env := put (env47_1) 79 0

private def env50_0 : Env := put (env49_0) 109 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok51 : Covered (env50_0) := replay_ok (k := 1) (i := 32876) (by decide +kernel)

private def env50_1 : Env := put (env49_0) 109 1

private def env52_0 : Env := put (env50_1) 83 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok53 : Covered (env52_0) := replay_ok (k := 1) (i := 45382) (by decide +kernel)

private def env52_1 : Env := put (env50_1) 83 1

private def env54_0 : Env := put (env52_1) 113 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok55 : Covered (env54_0) := replay_ok (k := 34) (i := 1233) (by decide +kernel)

private def env54_1 : Env := put (env52_1) 113 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok56 : Covered (env54_1) := replay_ok (k := 28) (i := 1371) (by decide +kernel)

private def env54_2 : Env := put (env52_1) 113 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok57 : Covered (env54_2) := replay_ok (k := 1) (i := 34348) (by decide +kernel)

private theorem ok54 : Covered (env52_1) := combine _ 113 ok55 ok56 ok57

private def env52_2 : Env := put (env50_1) 83 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok58 : Covered (env52_2) := replay_ok (k := 1) (i := 38410) (by decide +kernel)

private theorem ok52 : Covered (env50_1) := combine _ 83 ok53 ok54 ok58

private def env50_2 : Env := put (env49_0) 109 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok59 : Covered (env50_2) := replay_ok (k := 1) (i := 35927) (by decide +kernel)

private theorem ok50 : Covered (env49_0) := combine _ 109 ok51 ok52 ok59

private def env49_1 : Env := put (env47_1) 79 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok60 : Covered (env49_1) := replay_ok (k := 1) (i := 36638) (by decide +kernel)

private def env49_2 : Env := put (env47_1) 79 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok61 : Covered (env49_2) := replay_ok (k := 1) (i := 40034) (by decide +kernel)

private theorem ok49 : Covered (env47_1) := combine _ 79 ok50 ok60 ok61

private def env47_2 : Env := put (env45_1) 43 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok62 : Covered (env47_2) := replay_ok (k := 1) (i := 34099) (by decide +kernel)

private theorem ok47 : Covered (env45_1) := combine _ 43 ok48 ok49 ok62

private def env45_2 : Env := put (env43_1) 173 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok63 : Covered (env45_2) := replay_ok (k := 1) (i := 33977) (by decide +kernel)

private theorem ok45 : Covered (env43_1) := combine _ 173 ok46 ok47 ok63

private def env43_2 : Env := put (env41_1) 251 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok64 : Covered (env43_2) := replay_ok (k := 7) (i := 1384) (by decide +kernel)

private theorem ok43 : Covered (env41_1) := combine _ 251 ok44 ok45 ok64

private def env41_2 : Env := put (env39_1) 103 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok65 : Covered (env41_2) := replay_ok (k := 1) (i := 34210) (by decide +kernel)

private theorem ok41 : Covered (env39_1) := combine _ 103 ok42 ok43 ok65

private def env39_2 : Env := put (env38_0) 67 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok66 : Covered (env39_2) := replay_ok (k := 1) (i := 36653) (by decide +kernel)

private theorem ok39 : Covered (env38_0) := combine _ 67 ok40 ok41 ok66

private def env38_1 : Env := put (env36_1) 59 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok67 : Covered (env38_1) := replay_ok (k := 8) (i := 1396) (by decide +kernel)

private def env38_2 : Env := put (env36_1) 59 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok68 : Covered (env38_2) := replay_ok (k := 1) (i := 35186) (by decide +kernel)

private theorem ok38 : Covered (env36_1) := combine _ 59 ok39 ok67 ok68

private def env36_2 : Env := put (env34_1) 29 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok69 : Covered (env36_2) := replay_ok (k := 3) (i := 1399) (by decide +kernel)

private theorem ok36 : Covered (env34_1) := combine _ 29 ok37 ok38 ok69

private def env34_2 : Env := put (env32_1) 157 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok70 : Covered (env34_2) := replay_ok (k := 1) (i := 33866) (by decide +kernel)

private theorem ok34 : Covered (env32_1) := combine _ 157 ok35 ok36 ok70

private def env32_2 : Env := put (env30_1) 47 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok71 : Covered (env32_2) := replay_ok (k := 1) (i := 34366) (by decide +kernel)

private theorem ok32 : Covered (env30_1) := combine _ 47 ok33 ok34 ok71

private def env30_2 : Env := put (env28_1) 73 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok72 : Covered (env30_2) := replay_ok (k := 1) (i := 33279) (by decide +kernel)

private theorem ok30 : Covered (env28_1) := combine _ 73 ok31 ok32 ok72

private def env28_2 : Env := put (env26_1) 61 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok73 : Covered (env28_2) := replay_ok (k := 1) (i := 44052) (by decide +kernel)

private theorem ok28 : Covered (env26_1) := combine _ 61 ok29 ok30 ok73

private def env26_2 : Env := put (env24_1) 151 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok74 : Covered (env26_2) := replay_ok (k := 19) (i := 1453) (by decide +kernel)

private theorem ok26 : Covered (env24_1) := combine _ 151 ok27 ok28 ok74

private def env24_2 : Env := put (env22_1) 41 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok75 : Covered (env24_2) := replay_ok (k := 1) (i := 36540) (by decide +kernel)

private theorem ok24 : Covered (env22_1) := combine _ 41 ok25 ok26 ok75

private def env22_2 : Env := put (env20_1) 37 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok76 : Covered (env22_2) := replay_ok (k := 2) (i := 1456) (by decide +kernel)

private theorem ok22 : Covered (env20_1) := combine _ 37 ok23 ok24 ok76

private def env20_2 : Env := put (env19_0) 23 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok77 : Covered (env20_2) := replay_ok (k := 1) (i := 34286) (by decide +kernel)

private theorem ok20 : Covered (env19_0) := combine _ 23 ok21 ok22 ok77

private def env19_1 : Env := put (env14_1) 19 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok78 : Covered (env19_1) := replay_ok (k := 29) (i := 1739) (by decide +kernel)

private def env19_2 : Env := put (env14_1) 19 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok79 : Covered (env19_2) := replay_ok (k := 14) (i := 1798) (by decide +kernel)

private theorem ok19 : Covered (env14_1) := combine _ 19 ok20 ok78 ok79

private def env14_2 : Env := put (env12_1) 17 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok80 : Covered (env14_2) := replay_ok (k := 11) (i := 1820) (by decide +kernel)

private theorem ok14 : Covered (env12_1) := combine _ 17 ok15 ok19 ok80

private def env12_2 : Env := put (env11_0) 53 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok81 : Covered (env12_2) := replay_ok (k := 17) (i := 1933) (by decide +kernel)

private theorem ok12 : Covered (env11_0) := combine _ 53 ok13 ok14 ok81

private def env11_1 : Env := put (env9_1) 11 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok82 : Covered (env11_1) := replay_ok (k := 15) (i := 2056) (by decide +kernel)

private def env11_2 : Env := put (env9_1) 11 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok83 : Covered (env11_2) := replay_ok (k := 12) (i := 2090) (by decide +kernel)

private theorem ok11 : Covered (env9_1) := combine _ 11 ok12 ok82 ok83

private def env9_2 : Env := put (env7_1) 127 2

private def env84_0 : Env := put (env9_2) 11 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok85 : Covered (env84_0) := replay_ok (k := 29) (i := 2447) (by decide +kernel)

private def env84_1 : Env := put (env9_2) 11 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok86 : Covered (env84_1) := replay_ok (k := 11) (i := 2478) (by decide +kernel)

private def env84_2 : Env := put (env9_2) 11 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok87 : Covered (env84_2) := replay_ok (k := 10) (i := 2499) (by decide +kernel)

private theorem ok84 : Covered (env9_2) := combine _ 11 ok85 ok86 ok87

private theorem ok9 : Covered (env7_1) := combine _ 127 ok10 ok11 ok84

private def env7_2 : Env := put (env5_1) 31 2

private def env88_0 : Env := put (env7_2) 127 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok89 : Covered (env88_0) := replay_ok (k := 1) (i := 32893) (by decide +kernel)

private def env88_1 : Env := put (env7_2) 127 1

private def env90_0 : Env := put (env88_1) 43 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok91 : Covered (env90_0) := replay_ok (k := 1) (i := 32983) (by decide +kernel)

private def env90_1 : Env := put (env88_1) 43 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok92 : Covered (env90_1) := replay_ok (k := 11) (i := 2549) (by decide +kernel)

private def env90_2 : Env := put (env88_1) 43 2

private def env93_0 : Env := put (env90_2) 11 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok94 : Covered (env93_0) := replay_ok (k := 21) (i := 2900) (by decide +kernel)

private def env93_1 : Env := put (env90_2) 11 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok95 : Covered (env93_1) := replay_ok (k := 10) (i := 2930) (by decide +kernel)

private def env93_2 : Env := put (env90_2) 11 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok96 : Covered (env93_2) := replay_ok (k := 8) (i := 2944) (by decide +kernel)

private theorem ok93 : Covered (env90_2) := combine _ 11 ok94 ok95 ok96

private theorem ok90 : Covered (env88_1) := combine _ 43 ok91 ok92 ok93

private def env88_2 : Env := put (env7_2) 127 2

private def env97_0 : Env := put (env88_2) 43 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok98 : Covered (env97_0) := replay_ok (k := 1) (i := 32983) (by decide +kernel)

private def env97_1 : Env := put (env88_2) 43 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok99 : Covered (env97_1) := replay_ok (k := 16) (i := 3088) (by decide +kernel)

private def env97_2 : Env := put (env88_2) 43 2

private def env100_0 : Env := put (env97_2) 11 0

private def env101_0 : Env := put (env100_0) 109 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok102 : Covered (env101_0) := replay_ok (k := 1) (i := 32876) (by decide +kernel)

private def env101_1 : Env := put (env100_0) 109 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok103 : Covered (env101_1) := replay_ok (k := 20) (i := 3295) (by decide +kernel)

private def env101_2 : Env := put (env100_0) 109 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok104 : Covered (env101_2) := replay_ok (k := 16) (i := 3473) (by decide +kernel)

private theorem ok101 : Covered (env100_0) := combine _ 109 ok102 ok103 ok104

private def env100_1 : Env := put (env97_2) 11 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok105 : Covered (env100_1) := replay_ok (k := 10) (i := 3490) (by decide +kernel)

private def env100_2 : Env := put (env97_2) 11 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok106 : Covered (env100_2) := replay_ok (k := 15) (i := 3529) (by decide +kernel)

private theorem ok100 : Covered (env97_2) := combine _ 11 ok101 ok105 ok106

private theorem ok97 : Covered (env88_2) := combine _ 43 ok98 ok99 ok100

private theorem ok88 : Covered (env7_2) := combine _ 127 ok89 ok90 ok97

private theorem ok7 : Covered (env5_1) := combine _ 31 ok8 ok9 ok88

private def env5_2 : Env := put (env3_1) 7 2

private def env107_0 : Env := put (env5_2) 11 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok108 : Covered (env107_0) := replay_ok (k := 1) (i := 32788) (by decide +kernel)

private def env107_1 : Env := put (env5_2) 11 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok109 : Covered (env107_1) := replay_ok (k := 23) (i := 3875) (by decide +kernel)

private def env107_2 : Env := put (env5_2) 11 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok110 : Covered (env107_2) := replay_ok (k := 22) (i := 4030) (by decide +kernel)

private theorem ok107 : Covered (env5_2) := combine _ 11 ok108 ok109 ok110

private theorem ok5 : Covered (env3_1) := combine _ 7 ok6 ok7 ok107

private def env3_2 : Env := put (env2_0) 13 2

private def env111_0 : Env := put (env3_2) 19 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok112 : Covered (env111_0) := replay_ok (k := 1) (i := 32806) (by decide +kernel)

private def env111_1 : Env := put (env3_2) 19 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok113 : Covered (env111_1) := replay_ok (k := 31) (i := 4447) (by decide +kernel)

private def env111_2 : Env := put (env3_2) 19 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok114 : Covered (env111_2) := replay_ok (k := 20) (i := 4847) (by decide +kernel)

private theorem ok111 : Covered (env3_2) := combine _ 19 ok112 ok113 ok114

private theorem ok3 : Covered (env2_0) := combine _ 13 ok4 ok5 ok111

private def env2_1 : Env := put (env0_1) 5 1

private def env115_0 : Env := put (env2_1) 7 0

private def env116_0 : Env := put (env115_0) 11 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok117 : Covered (env116_0) := replay_ok (k := 21) (i := 5127) (by decide +kernel)

private def env116_1 : Env := put (env115_0) 11 1

private def env118_0 : Env := put (env116_1) 13 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok119 : Covered (env118_0) := replay_ok (k := 1) (i := 32794) (by decide +kernel)

private def env118_1 : Env := put (env116_1) 13 1

private def env120_0 : Env := put (env118_1) 197 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok121 : Covered (env120_0) := replay_ok (k := 1) (i := 32963) (by decide +kernel)

private def env120_1 : Env := put (env118_1) 197 1

private def env122_0 : Env := put (env120_1) 97 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok123 : Covered (env122_0) := replay_ok (k := 1) (i := 32865) (by decide +kernel)

private def env122_1 : Env := put (env120_1) 97 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok124 : Covered (env122_1) := replay_ok (k := 30) (i := 5393) (by decide +kernel)

private def env122_2 : Env := put (env120_1) 97 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok125 : Covered (env122_2) := replay_ok (k := 26) (i := 5734) (by decide +kernel)

private theorem ok122 : Covered (env120_1) := combine _ 97 ok123 ok124 ok125

private def env120_2 : Env := put (env118_1) 197 2

private def env126_0 : Env := put (env120_2) 97 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok127 : Covered (env126_0) := replay_ok (k := 1) (i := 32865) (by decide +kernel)

private def env126_1 : Env := put (env120_2) 97 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok128 : Covered (env126_1) := replay_ok (k := 30) (i := 5945) (by decide +kernel)

private def env126_2 : Env := put (env120_2) 97 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok129 : Covered (env126_2) := replay_ok (k := 23) (i := 6202) (by decide +kernel)

private theorem ok126 : Covered (env120_2) := combine _ 97 ok127 ok128 ok129

private theorem ok120 : Covered (env118_1) := combine _ 197 ok121 ok122 ok126

private def env118_2 : Env := put (env116_1) 13 2

private def env130_0 : Env := put (env118_2) 37 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok131 : Covered (env130_0) := replay_ok (k := 1) (i := 33767) (by decide +kernel)

private def env130_1 : Env := put (env118_2) 37 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok132 : Covered (env130_1) := replay_ok (k := 18) (i := 6362) (by decide +kernel)

private def env130_2 : Env := put (env118_2) 37 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok133 : Covered (env130_2) := replay_ok (k := 19) (i := 6622) (by decide +kernel)

private theorem ok130 : Covered (env118_2) := combine _ 37 ok131 ok132 ok133

private theorem ok118 : Covered (env116_1) := combine _ 13 ok119 ok120 ok130

private def env116_2 : Env := put (env115_0) 11 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok134 : Covered (env116_2) := replay_ok (k := 1) (i := 32822) (by decide +kernel)

private theorem ok116 : Covered (env115_0) := combine _ 11 ok117 ok118 ok134

private def env115_1 : Env := put (env2_1) 7 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok135 : Covered (env115_1) := replay_ok (k := 20) (i := 6988) (by decide +kernel)

private def env115_2 : Env := put (env2_1) 7 2

private def env136_0 : Env := put (env115_2) 11 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok137 : Covered (env136_0) := replay_ok (k := 24) (i := 7294) (by decide +kernel)

private def env136_1 : Env := put (env115_2) 11 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok138 : Covered (env136_1) := replay_ok (k := 19) (i := 7474) (by decide +kernel)

private def env136_2 : Env := put (env115_2) 11 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok139 : Covered (env136_2) := replay_ok (k := 20) (i := 7590) (by decide +kernel)

private theorem ok136 : Covered (env115_2) := combine _ 11 ok137 ok138 ok139

private theorem ok115 : Covered (env2_1) := combine _ 7 ok116 ok135 ok136

private def env2_2 : Env := put (env0_1) 5 2

private def env140_0 : Env := put (env2_2) 7 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok141 : Covered (env140_0) := replay_ok (k := 1) (i := 32782) (by decide +kernel)

private def env140_1 : Env := put (env2_2) 7 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok142 : Covered (env140_1) := replay_ok (k := 17) (i := 7957) (by decide +kernel)

private def env140_2 : Env := put (env2_2) 7 2

private def env143_0 : Env := put (env140_2) 17 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok144 : Covered (env143_0) := replay_ok (k := 1) (i := 32783) (by decide +kernel)

private def env143_1 : Env := put (env140_2) 17 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok145 : Covered (env143_1) := replay_ok (k := 17) (i := 8041) (by decide +kernel)

private def env143_2 : Env := put (env140_2) 17 2

private def env146_0 : Env := put (env143_2) 31 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok147 : Covered (env146_0) := replay_ok (k := 1) (i := 32798) (by decide +kernel)

private def env146_1 : Env := put (env143_2) 31 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok148 : Covered (env146_1) := replay_ok (k := 24) (i := 8179) (by decide +kernel)

private def env146_2 : Env := put (env143_2) 31 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok149 : Covered (env146_2) := replay_ok (k := 22) (i := 8462) (by decide +kernel)

private theorem ok146 : Covered (env143_2) := combine _ 31 ok147 ok148 ok149

private theorem ok143 : Covered (env140_2) := combine _ 17 ok144 ok145 ok146

private theorem ok140 : Covered (env2_2) := combine _ 7 ok141 ok142 ok143

private theorem ok2 : Covered (env0_1) := combine _ 5 ok3 ok115 ok140

private def env0_2 : Env := put (put emptyEnv 2 0) 3 2

private def env150_0 : Env := put (env0_2) 5 0

private def env151_0 : Env := put (env150_0) 13 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok152 : Covered (env151_0) := replay_ok (k := 1) (i := 32793) (by decide +kernel)

private def env151_1 : Env := put (env150_0) 13 1

private def env153_0 : Env := put (env151_1) 19 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok154 : Covered (env153_0) := replay_ok (k := 1) (i := 32806) (by decide +kernel)

private def env153_1 : Env := put (env151_1) 19 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok155 : Covered (env153_1) := replay_ok (k := 20) (i := 8869) (by decide +kernel)

private def env153_2 : Env := put (env151_1) 19 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok156 : Covered (env153_2) := replay_ok (k := 31) (i := 9282) (by decide +kernel)

private theorem ok153 : Covered (env151_1) := combine _ 19 ok154 ok155 ok156

private def env151_2 : Env := put (env150_0) 13 2

private def env157_0 : Env := put (env151_2) 7 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok158 : Covered (env157_0) := replay_ok (k := 21) (i := 9373) (by decide +kernel)

private def env157_1 : Env := put (env151_2) 7 1

private def env159_0 : Env := put (env157_1) 11 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok160 : Covered (env159_0) := replay_ok (k := 1) (i := 32788) (by decide +kernel)

private def env159_1 : Env := put (env157_1) 11 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok161 : Covered (env159_1) := replay_ok (k := 22) (i := 9529) (by decide +kernel)

private def env159_2 : Env := put (env157_1) 11 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok162 : Covered (env159_2) := replay_ok (k := 23) (i := 9871) (by decide +kernel)

private theorem ok159 : Covered (env157_1) := combine _ 11 ok160 ok161 ok162

private def env157_2 : Env := put (env151_2) 7 2

private def env163_0 : Env := put (env157_2) 31 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok164 : Covered (env163_0) := replay_ok (k := 1) (i := 32830) (by decide +kernel)

private def env163_1 : Env := put (env157_2) 31 1

private def env165_0 : Env := put (env163_1) 127 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok166 : Covered (env165_0) := replay_ok (k := 1) (i := 32893) (by decide +kernel)

private def env165_1 : Env := put (env163_1) 127 1

private def env167_0 : Env := put (env165_1) 43 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok168 : Covered (env167_0) := replay_ok (k := 1) (i := 32983) (by decide +kernel)

private def env167_1 : Env := put (env165_1) 43 1

private def env169_0 : Env := put (env167_1) 11 0

private def env170_0 : Env := put (env169_0) 109 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok171 : Covered (env170_0) := replay_ok (k := 1) (i := 32876) (by decide +kernel)

private def env170_1 : Env := put (env169_0) 109 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok172 : Covered (env170_1) := replay_ok (k := 16) (i := 10082) (by decide +kernel)

private def env170_2 : Env := put (env169_0) 109 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok173 : Covered (env170_2) := replay_ok (k := 20) (i := 10295) (by decide +kernel)

private theorem ok170 : Covered (env169_0) := combine _ 109 ok171 ok172 ok173

private def env169_1 : Env := put (env167_1) 11 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok174 : Covered (env169_1) := replay_ok (k := 15) (i := 10336) (by decide +kernel)

private def env169_2 : Env := put (env167_1) 11 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok175 : Covered (env169_2) := replay_ok (k := 10) (i := 10353) (by decide +kernel)

private theorem ok169 : Covered (env167_1) := combine _ 11 ok170 ok174 ok175

private def env167_2 : Env := put (env165_1) 43 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok176 : Covered (env167_2) := replay_ok (k := 16) (i := 10503) (by decide +kernel)

private theorem ok167 : Covered (env165_1) := combine _ 43 ok168 ok169 ok176

private def env165_2 : Env := put (env163_1) 127 2

private def env177_0 : Env := put (env165_2) 43 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok178 : Covered (env177_0) := replay_ok (k := 1) (i := 32983) (by decide +kernel)

private def env177_1 : Env := put (env165_2) 43 1

private def env179_0 : Env := put (env177_1) 11 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok180 : Covered (env179_0) := replay_ok (k := 21) (i := 10824) (by decide +kernel)

private def env179_1 : Env := put (env177_1) 11 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok181 : Covered (env179_1) := replay_ok (k := 8) (i := 10837) (by decide +kernel)

private def env179_2 : Env := put (env177_1) 11 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok182 : Covered (env179_2) := replay_ok (k := 10) (i := 10865) (by decide +kernel)

private theorem ok179 : Covered (env177_1) := combine _ 11 ok180 ok181 ok182

private def env177_2 : Env := put (env165_2) 43 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok183 : Covered (env177_2) := replay_ok (k := 11) (i := 10908) (by decide +kernel)

private theorem ok177 : Covered (env165_2) := combine _ 43 ok178 ok179 ok183

private theorem ok165 : Covered (env163_1) := combine _ 127 ok166 ok167 ok177

private def env163_2 : Env := put (env157_2) 31 2

private def env184_0 : Env := put (env163_2) 127 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok185 : Covered (env184_0) := replay_ok (k := 1) (i := 32893) (by decide +kernel)

private def env184_1 : Env := put (env163_2) 127 1

private def env186_0 : Env := put (env184_1) 11 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok187 : Covered (env186_0) := replay_ok (k := 29) (i := 11286) (by decide +kernel)

private def env186_1 : Env := put (env184_1) 11 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok188 : Covered (env186_1) := replay_ok (k := 10) (i := 11306) (by decide +kernel)

private def env186_2 : Env := put (env184_1) 11 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok189 : Covered (env186_2) := replay_ok (k := 11) (i := 11340) (by decide +kernel)

private theorem ok186 : Covered (env184_1) := combine _ 11 ok187 ok188 ok189

private def env184_2 : Env := put (env163_2) 127 2

private def env190_0 : Env := put (env184_2) 11 0

private def env191_0 : Env := put (env190_0) 53 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok192 : Covered (env191_0) := replay_ok (k := 1) (i := 32821) (by decide +kernel)

private def env191_1 : Env := put (env190_0) 53 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok193 : Covered (env191_1) := replay_ok (k := 17) (i := 11451) (by decide +kernel)

private def env191_2 : Env := put (env190_0) 53 2

private def env194_0 : Env := put (env191_2) 17 0

private def env195_0 : Env := put (env194_0) 137 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok196 : Covered (env195_0) := replay_ok (k := 1) (i := 32903) (by decide +kernel)

private def env195_1 : Env := put (env194_0) 137 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok197 : Covered (env195_1) := replay_ok (k := 26) (i := 11656) (by decide +kernel)

private def env195_2 : Env := put (env194_0) 137 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok198 : Covered (env195_2) := replay_ok (k := 38) (i := 11938) (by decide +kernel)

private theorem ok195 : Covered (env194_0) := combine _ 137 ok196 ok197 ok198

private def env194_1 : Env := put (env191_2) 17 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok199 : Covered (env194_1) := replay_ok (k := 11) (i := 11958) (by decide +kernel)

private def env194_2 : Env := put (env191_2) 17 2

private def env200_0 : Env := put (env194_2) 19 0

private def env201_0 : Env := put (env200_0) 23 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok202 : Covered (env201_0) := replay_ok (k := 12) (i := 11978) (by decide +kernel)

private def env201_1 : Env := put (env200_0) 23 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok203 : Covered (env201_1) := replay_ok (k := 1) (i := 34286) (by decide +kernel)

private def env201_2 : Env := put (env200_0) 23 2

private def env204_0 : Env := put (env201_2) 37 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok205 : Covered (env204_0) := replay_ok (k := 1) (i := 50343) (by decide +kernel)

private def env204_1 : Env := put (env201_2) 37 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok206 : Covered (env204_1) := replay_ok (k := 2) (i := 11979) (by decide +kernel)

private def env204_2 : Env := put (env201_2) 37 2

private def env207_0 : Env := put (env204_2) 41 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok208 : Covered (env207_0) := replay_ok (k := 1) (i := 33792) (by decide +kernel)

private def env207_1 : Env := put (env204_2) 41 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok209 : Covered (env207_1) := replay_ok (k := 1) (i := 36540) (by decide +kernel)

private def env207_2 : Env := put (env204_2) 41 2

private def env210_0 : Env := put (env207_2) 151 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok211 : Covered (env210_0) := replay_ok (k := 1) (i := 32919) (by decide +kernel)

private def env210_1 : Env := put (env207_2) 151 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok212 : Covered (env210_1) := replay_ok (k := 19) (i := 12028) (by decide +kernel)

private def env210_2 : Env := put (env207_2) 151 2

private def env213_0 : Env := put (env210_2) 61 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok214 : Covered (env213_0) := replay_ok (k := 1) (i := 33072) (by decide +kernel)

private def env213_1 : Env := put (env210_2) 61 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok215 : Covered (env213_1) := replay_ok (k := 1) (i := 44052) (by decide +kernel)

private def env213_2 : Env := put (env210_2) 61 2

private def env216_0 : Env := put (env213_2) 73 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok217 : Covered (env216_0) := replay_ok (k := 34) (i := 12109) (by decide +kernel)

private def env216_1 : Env := put (env213_2) 73 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok218 : Covered (env216_1) := replay_ok (k := 1) (i := 33279) (by decide +kernel)

private def env216_2 : Env := put (env213_2) 73 2

private def env219_0 : Env := put (env216_2) 47 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok220 : Covered (env219_0) := replay_ok (k := 19) (i := 12134) (by decide +kernel)

private def env219_1 : Env := put (env216_2) 47 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok221 : Covered (env219_1) := replay_ok (k := 1) (i := 34366) (by decide +kernel)

private def env219_2 : Env := put (env216_2) 47 2

private def env222_0 : Env := put (env219_2) 157 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok223 : Covered (env222_0) := replay_ok (k := 12) (i := 12158) (by decide +kernel)

private def env222_1 : Env := put (env219_2) 157 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok224 : Covered (env222_1) := replay_ok (k := 1) (i := 33866) (by decide +kernel)

private def env222_2 : Env := put (env219_2) 157 2

private def env225_0 : Env := put (env222_2) 29 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok226 : Covered (env225_0) := replay_ok (k := 1) (i := 33317) (by decide +kernel)

private def env225_1 : Env := put (env222_2) 29 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok227 : Covered (env225_1) := replay_ok (k := 3) (i := 12160) (by decide +kernel)

private def env225_2 : Env := put (env222_2) 29 2

private def env228_0 : Env := put (env225_2) 59 0

private def env229_0 : Env := put (env228_0) 67 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok230 : Covered (env229_0) := replay_ok (k := 1) (i := 34242) (by decide +kernel)

private def env229_1 : Env := put (env228_0) 67 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok231 : Covered (env229_1) := replay_ok (k := 1) (i := 36653) (by decide +kernel)

private def env229_2 : Env := put (env228_0) 67 2

private def env232_0 : Env := put (env229_2) 103 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok233 : Covered (env232_0) := replay_ok (k := 1) (i := 41831) (by decide +kernel)

private def env232_1 : Env := put (env229_2) 103 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok234 : Covered (env232_1) := replay_ok (k := 1) (i := 34210) (by decide +kernel)

private def env232_2 : Env := put (env229_2) 103 2

private def env235_0 : Env := put (env232_2) 251 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok236 : Covered (env235_0) := replay_ok (k := 1) (i := 33018) (by decide +kernel)

private def env235_1 : Env := put (env232_2) 251 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok237 : Covered (env235_1) := replay_ok (k := 7) (i := 12167) (by decide +kernel)

private def env235_2 : Env := put (env232_2) 251 2

private def env238_0 : Env := put (env235_2) 173 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok239 : Covered (env238_0) := replay_ok (k := 39) (i := 12455) (by decide +kernel)

private def env238_1 : Env := put (env235_2) 173 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok240 : Covered (env238_1) := replay_ok (k := 1) (i := 33977) (by decide +kernel)

private def env238_2 : Env := put (env235_2) 173 2

private def env241_0 : Env := put (env238_2) 43 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok242 : Covered (env241_0) := replay_ok (k := 5) (i := 12458) (by decide +kernel)

private def env241_1 : Env := put (env238_2) 43 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok243 : Covered (env241_1) := replay_ok (k := 1) (i := 34099) (by decide +kernel)

private def env241_2 : Env := put (env238_2) 43 2

private def env244_0 : Env := put (env241_2) 79 0

private def env245_0 : Env := put (env244_0) 109 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok246 : Covered (env245_0) := replay_ok (k := 1) (i := 32876) (by decide +kernel)

private def env245_1 : Env := put (env244_0) 109 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok247 : Covered (env245_1) := replay_ok (k := 1) (i := 35927) (by decide +kernel)

private def env245_2 : Env := put (env244_0) 109 2

private def env248_0 : Env := put (env245_2) 83 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok249 : Covered (env248_0) := replay_ok (k := 1) (i := 45382) (by decide +kernel)

private def env248_1 : Env := put (env245_2) 83 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok250 : Covered (env248_1) := replay_ok (k := 1) (i := 38410) (by decide +kernel)

private def env248_2 : Env := put (env245_2) 83 2

private def env251_0 : Env := put (env248_2) 113 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok252 : Covered (env251_0) := replay_ok (k := 34) (i := 12653) (by decide +kernel)

private def env251_1 : Env := put (env248_2) 113 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok253 : Covered (env251_1) := replay_ok (k := 1) (i := 34348) (by decide +kernel)

private def env251_2 : Env := put (env248_2) 113 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok254 : Covered (env251_2) := replay_ok (k := 28) (i := 12791) (by decide +kernel)

private theorem ok251 : Covered (env248_2) := combine _ 113 ok252 ok253 ok254

private theorem ok248 : Covered (env245_2) := combine _ 83 ok249 ok250 ok251

private theorem ok245 : Covered (env244_0) := combine _ 109 ok246 ok247 ok248

private def env244_1 : Env := put (env241_2) 79 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok255 : Covered (env244_1) := replay_ok (k := 1) (i := 40034) (by decide +kernel)

private def env244_2 : Env := put (env241_2) 79 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok256 : Covered (env244_2) := replay_ok (k := 1) (i := 36638) (by decide +kernel)

private theorem ok244 : Covered (env241_2) := combine _ 79 ok245 ok255 ok256

private theorem ok241 : Covered (env238_2) := combine _ 43 ok242 ok243 ok244

private theorem ok238 : Covered (env235_2) := combine _ 173 ok239 ok240 ok241

private theorem ok235 : Covered (env232_2) := combine _ 251 ok236 ok237 ok238

private theorem ok232 : Covered (env229_2) := combine _ 103 ok233 ok234 ok235

private theorem ok229 : Covered (env228_0) := combine _ 67 ok230 ok231 ok232

private def env228_1 : Env := put (env225_2) 59 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok257 : Covered (env228_1) := replay_ok (k := 1) (i := 35186) (by decide +kernel)

private def env228_2 : Env := put (env225_2) 59 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok258 : Covered (env228_2) := replay_ok (k := 8) (i := 12809) (by decide +kernel)

private theorem ok228 : Covered (env225_2) := combine _ 59 ok229 ok257 ok258

private theorem ok225 : Covered (env222_2) := combine _ 29 ok226 ok227 ok228

private theorem ok222 : Covered (env219_2) := combine _ 157 ok223 ok224 ok225

private theorem ok219 : Covered (env216_2) := combine _ 47 ok220 ok221 ok222

private theorem ok216 : Covered (env213_2) := combine _ 73 ok217 ok218 ok219

private theorem ok213 : Covered (env210_2) := combine _ 61 ok214 ok215 ok216

private theorem ok210 : Covered (env207_2) := combine _ 151 ok211 ok212 ok213

private theorem ok207 : Covered (env204_2) := combine _ 41 ok208 ok209 ok210

private theorem ok204 : Covered (env201_2) := combine _ 37 ok205 ok206 ok207

private theorem ok201 : Covered (env200_0) := combine _ 23 ok202 ok203 ok204

private def env200_1 : Env := put (env194_2) 19 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok259 : Covered (env200_1) := replay_ok (k := 14) (i := 12875) (by decide +kernel)

private def env200_2 : Env := put (env194_2) 19 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok260 : Covered (env200_2) := replay_ok (k := 29) (i := 13155) (by decide +kernel)

private theorem ok200 : Covered (env194_2) := combine _ 19 ok201 ok259 ok260

private theorem ok194 : Covered (env191_2) := combine _ 17 ok195 ok199 ok200

private theorem ok191 : Covered (env190_0) := combine _ 53 ok192 ok193 ok194

private def env190_1 : Env := put (env184_2) 11 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok261 : Covered (env190_1) := replay_ok (k := 12) (i := 13192) (by decide +kernel)

private def env190_2 : Env := put (env184_2) 11 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok262 : Covered (env190_2) := replay_ok (k := 15) (i := 13309) (by decide +kernel)

private theorem ok190 : Covered (env184_2) := combine _ 11 ok191 ok261 ok262

private theorem ok184 : Covered (env163_2) := combine _ 127 ok185 ok186 ok190

private theorem ok163 : Covered (env157_2) := combine _ 31 ok164 ok165 ok184

private theorem ok157 : Covered (env151_2) := combine _ 7 ok158 ok159 ok163

private theorem ok151 : Covered (env150_0) := combine _ 13 ok152 ok153 ok157

private def env150_1 : Env := put (env0_2) 5 1

private def env263_0 : Env := put (env150_1) 7 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok264 : Covered (env263_0) := replay_ok (k := 1) (i := 32782) (by decide +kernel)

private def env263_1 : Env := put (env150_1) 7 1

private def env265_0 : Env := put (env263_1) 17 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok266 : Covered (env265_0) := replay_ok (k := 1) (i := 32783) (by decide +kernel)

private def env265_1 : Env := put (env263_1) 17 1

private def env267_0 : Env := put (env265_1) 31 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok268 : Covered (env267_0) := replay_ok (k := 1) (i := 32798) (by decide +kernel)

private def env267_1 : Env := put (env265_1) 31 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok269 : Covered (env267_1) := replay_ok (k := 22) (i := 13599) (by decide +kernel)

private def env267_2 : Env := put (env265_1) 31 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok270 : Covered (env267_2) := replay_ok (k := 24) (i := 13736) (by decide +kernel)

private theorem ok267 : Covered (env265_1) := combine _ 31 ok268 ok269 ok270

private def env265_2 : Env := put (env263_1) 17 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok271 : Covered (env265_2) := replay_ok (k := 17) (i := 13821) (by decide +kernel)

private theorem ok265 : Covered (env263_1) := combine _ 17 ok266 ok267 ok271

private def env263_2 : Env := put (env150_1) 7 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok272 : Covered (env263_2) := replay_ok (k := 17) (i := 14185) (by decide +kernel)

private theorem ok263 : Covered (env150_1) := combine _ 7 ok264 ok265 ok272

private def env150_2 : Env := put (env0_2) 5 2

private def env273_0 : Env := put (env150_2) 7 0

private def env274_0 : Env := put (env273_0) 11 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok275 : Covered (env274_0) := replay_ok (k := 21) (i := 14464) (by decide +kernel)

private def env274_1 : Env := put (env273_0) 11 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok276 : Covered (env274_1) := replay_ok (k := 1) (i := 32822) (by decide +kernel)

private def env274_2 : Env := put (env273_0) 11 2

private def env277_0 : Env := put (env274_2) 13 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok278 : Covered (env277_0) := replay_ok (k := 1) (i := 32794) (by decide +kernel)

private def env277_1 : Env := put (env274_2) 13 1

private def env279_0 : Env := put (env277_1) 37 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok280 : Covered (env279_0) := replay_ok (k := 1) (i := 33767) (by decide +kernel)

private def env279_1 : Env := put (env277_1) 37 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok281 : Covered (env279_1) := replay_ok (k := 19) (i := 14727) (by decide +kernel)

private def env279_2 : Env := put (env277_1) 37 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok282 : Covered (env279_2) := replay_ok (k := 18) (i := 14883) (by decide +kernel)

private theorem ok279 : Covered (env277_1) := combine _ 37 ok280 ok281 ok282

private def env277_2 : Env := put (env274_2) 13 2

private def env283_0 : Env := put (env277_2) 197 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok284 : Covered (env283_0) := replay_ok (k := 1) (i := 32963) (by decide +kernel)

private def env283_1 : Env := put (env277_2) 197 1

private def env285_0 : Env := put (env283_1) 97 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok286 : Covered (env285_0) := replay_ok (k := 1) (i := 32865) (by decide +kernel)

private def env285_1 : Env := put (env283_1) 97 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok287 : Covered (env285_1) := replay_ok (k := 23) (i := 15221) (by decide +kernel)

private def env285_2 : Env := put (env283_1) 97 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok288 : Covered (env285_2) := replay_ok (k := 30) (i := 15451) (by decide +kernel)

private theorem ok285 : Covered (env283_1) := combine _ 97 ok286 ok287 ok288

private def env283_2 : Env := put (env277_2) 197 2

private def env289_0 : Env := put (env283_2) 97 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok290 : Covered (env289_0) := replay_ok (k := 1) (i := 32865) (by decide +kernel)

private def env289_1 : Env := put (env283_2) 97 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok291 : Covered (env289_1) := replay_ok (k := 26) (i := 15753) (by decide +kernel)

private def env289_2 : Env := put (env283_2) 97 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok292 : Covered (env289_2) := replay_ok (k := 30) (i := 15958) (by decide +kernel)

private theorem ok289 : Covered (env283_2) := combine _ 97 ok290 ok291 ok292

private theorem ok283 : Covered (env277_2) := combine _ 197 ok284 ok285 ok289

private theorem ok277 : Covered (env274_2) := combine _ 13 ok278 ok279 ok283

private theorem ok274 : Covered (env273_0) := combine _ 11 ok275 ok276 ok277

private def env273_1 : Env := put (env150_2) 7 1

private def env293_0 : Env := put (env273_1) 11 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok294 : Covered (env293_0) := replay_ok (k := 24) (i := 16268) (by decide +kernel)

private def env293_1 : Env := put (env273_1) 11 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok295 : Covered (env293_1) := replay_ok (k := 20) (i := 16383) (by decide +kernel)

private def env293_2 : Env := put (env273_1) 11 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok296 : Covered (env293_2) := replay_ok (k := 19) (i := 16563) (by decide +kernel)

private theorem ok293 : Covered (env273_1) := combine _ 11 ok294 ok295 ok296

private def env273_2 : Env := put (env150_2) 7 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok297 : Covered (env273_2) := replay_ok (k := 20) (i := 16927) (by decide +kernel)

private theorem ok273 : Covered (env150_2) := combine _ 7 ok274 ok293 ok297

private theorem ok150 : Covered (env0_2) := combine _ 5 ok151 ok263 ok273

private theorem ok0 : Covered (put emptyEnv 2 0) := combine _ 3 ok1 ok2 ok150

private def env298_0 : Env := put (put emptyEnv 2 1) 3 0

private def env299_0 : Env := put (env298_0) 5 0

private def env300_0 : Env := put (env299_0) 13 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok301 : Covered (env300_0) := replay_ok (k := 22) (i := 17131) (by decide +kernel)

private def env300_1 : Env := put (env299_0) 13 1

private def env302_0 : Env := put (env300_1) 7 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok303 : Covered (env302_0) := replay_ok (k := 1) (i := 32775) (by decide +kernel)

private def env302_1 : Env := put (env300_1) 7 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok304 : Covered (env302_1) := replay_ok (k := 19) (i := 17516) (by decide +kernel)

private def env302_2 : Env := put (env300_1) 7 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok305 : Covered (env302_2) := replay_ok (k := 17) (i := 17584) (by decide +kernel)

private theorem ok302 : Covered (env300_1) := combine _ 7 ok303 ok304 ok305

private def env300_2 : Env := put (env299_0) 13 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok306 : Covered (env300_2) := replay_ok (k := 1) (i := 32792) (by decide +kernel)

private theorem ok300 : Covered (env299_0) := combine _ 13 ok301 ok302 ok306

private def env299_1 : Env := put (env298_0) 5 1

private def env307_0 : Env := put (env299_1) 7 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok308 : Covered (env307_0) := replay_ok (k := 1) (i := 32775) (by decide +kernel)

private def env307_1 : Env := put (env299_1) 7 1

private def env309_0 : Env := put (env307_1) 13 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok310 : Covered (env309_0) := replay_ok (k := 18) (i := 17876) (by decide +kernel)

private def env309_1 : Env := put (env307_1) 13 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok311 : Covered (env309_1) := replay_ok (k := 18) (i := 18088) (by decide +kernel)

private def env309_2 : Env := put (env307_1) 13 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok312 : Covered (env309_2) := replay_ok (k := 1) (i := 32794) (by decide +kernel)

private theorem ok309 : Covered (env307_1) := combine _ 13 ok310 ok311 ok312

private def env307_2 : Env := put (env299_1) 7 2

private def env313_0 : Env := put (env307_2) 31 0

private def env314_0 : Env := put (env313_0) 127 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok315 : Covered (env314_0) := replay_ok (k := 1) (i := 32893) (by decide +kernel)

private def env314_1 : Env := put (env313_0) 127 1

private def env316_0 : Env := put (env314_1) 139 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok317 : Covered (env316_0) := replay_ok (k := 16) (i := 18370) (by decide +kernel)

private def env316_1 : Env := put (env314_1) 139 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok318 : Covered (env316_1) := replay_ok (k := 16) (i := 18636) (by decide +kernel)

private def env316_2 : Env := put (env314_1) 139 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok319 : Covered (env316_2) := replay_ok (k := 1) (i := 33046) (by decide +kernel)

private theorem ok316 : Covered (env314_1) := combine _ 139 ok317 ok318 ok319

private def env314_2 : Env := put (env313_0) 127 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok320 : Covered (env314_2) := replay_ok (k := 2) (i := 18638) (by decide +kernel)

private theorem ok314 : Covered (env313_0) := combine _ 127 ok315 ok316 ok320

private def env313_1 : Env := put (env307_2) 31 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok321 : Covered (env313_1) := replay_ok (k := 1) (i := 32892) (by decide +kernel)

private def env313_2 : Env := put (env307_2) 31 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok322 : Covered (env313_2) := replay_ok (k := 17) (i := 18786) (by decide +kernel)

private theorem ok313 : Covered (env307_2) := combine _ 31 ok314 ok321 ok322

private theorem ok307 : Covered (env299_1) := combine _ 7 ok308 ok309 ok313

private def env299_2 : Env := put (env298_0) 5 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok323 : Covered (env299_2) := replay_ok (k := 1) (i := 32776) (by decide +kernel)

private theorem ok299 : Covered (env298_0) := combine _ 5 ok300 ok307 ok323

private def env298_1 : Env := put (put emptyEnv 2 1) 3 1

private def env324_0 : Env := put (env298_1) 5 0

private def env325_0 : Env := put (env324_0) 13 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok326 : Covered (env325_0) := replay_ok (k := 13) (i := 18817) (by decide +kernel)

private def env325_1 : Env := put (env324_0) 13 1

private def env327_0 : Env := put (env325_1) 7 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok328 : Covered (env327_0) := replay_ok (k := 16) (i := 18927) (by decide +kernel)

private def env327_1 : Env := put (env325_1) 7 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok329 : Covered (env327_1) := replay_ok (k := 18) (i := 19205) (by decide +kernel)

private def env327_2 : Env := put (env325_1) 7 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok330 : Covered (env327_2) := replay_ok (k := 11) (i := 19228) (by decide +kernel)

private theorem ok327 : Covered (env325_1) := combine _ 7 ok328 ok329 ok330

private def env325_2 : Env := put (env324_0) 13 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok331 : Covered (env325_2) := replay_ok (k := 1) (i := 32793) (by decide +kernel)

private theorem ok325 : Covered (env324_0) := combine _ 13 ok326 ok327 ok331

private def env324_1 : Env := put (env298_1) 5 1

private def env332_0 : Env := put (env324_1) 19 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok333 : Covered (env332_0) := replay_ok (k := 1) (i := 32786) (by decide +kernel)

private def env332_1 : Env := put (env324_1) 19 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok334 : Covered (env332_1) := replay_ok (k := 20) (i := 19489) (by decide +kernel)

private def env332_2 : Env := put (env324_1) 19 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok335 : Covered (env332_2) := replay_ok (k := 27) (i := 19823) (by decide +kernel)

private theorem ok332 : Covered (env324_1) := combine _ 19 ok333 ok334 ok335

private def env324_2 : Env := put (env298_1) 5 2

private def env336_0 : Env := put (env324_2) 11 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok337 : Covered (env336_0) := replay_ok (k := 1) (i := 32778) (by decide +kernel)

private def env336_1 : Env := put (env324_2) 11 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok338 : Covered (env336_1) := replay_ok (k := 14) (i := 19940) (by decide +kernel)

private def env336_2 : Env := put (env324_2) 11 2

private def env339_0 : Env := put (env336_2) 7 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok340 : Covered (env339_0) := replay_ok (k := 25) (i := 20256) (by decide +kernel)

private def env339_1 : Env := put (env336_2) 7 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok341 : Covered (env339_1) := replay_ok (k := 9) (i := 20266) (by decide +kernel)

private def env339_2 : Env := put (env336_2) 7 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok342 : Covered (env339_2) := replay_ok (k := 13) (i := 20371) (by decide +kernel)

private theorem ok339 : Covered (env336_2) := combine _ 7 ok340 ok341 ok342

private theorem ok336 : Covered (env324_2) := combine _ 11 ok337 ok338 ok339

private theorem ok324 : Covered (env298_1) := combine _ 5 ok325 ok332 ok336

private def env298_2 : Env := put (put emptyEnv 2 1) 3 2

private def env343_0 : Env := put (env298_2) 7 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok344 : Covered (env343_0) := replay_ok (k := 1) (i := 32774) (by decide +kernel)

private def env343_1 : Env := put (env298_2) 7 1

private def env345_0 : Env := put (env343_1) 13 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok346 : Covered (env345_0) := replay_ok (k := 18) (i := 20595) (by decide +kernel)

private def env345_1 : Env := put (env343_1) 13 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok347 : Covered (env345_1) := replay_ok (k := 20) (i := 20977) (by decide +kernel)

private def env345_2 : Env := put (env343_1) 13 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok348 : Covered (env345_2) := replay_ok (k := 1) (i := 32794) (by decide +kernel)

private theorem ok345 : Covered (env343_1) := combine _ 13 ok346 ok347 ok348

private def env343_2 : Env := put (env298_2) 7 2

private def env349_0 : Env := put (env343_2) 31 0

private def env350_0 : Env := put (env349_0) 5 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok351 : Covered (env350_0) := replay_ok (k := 13) (i := 21044) (by decide +kernel)

private def env350_1 : Env := put (env349_0) 5 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok352 : Covered (env350_1) := replay_ok (k := 16) (i := 21065) (by decide +kernel)

private def env350_2 : Env := put (env349_0) 5 2

private def env353_0 : Env := put (env350_2) 13 0

private def env354_0 : Env := put (env353_0) 11 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok355 : Covered (env354_0) := replay_ok (k := 17) (i := 21150) (by decide +kernel)

private def env354_1 : Env := put (env353_0) 11 1

private def env356_0 : Env := put (env354_1) 19 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok357 : Covered (env356_0) := replay_ok (k := 6) (i := 21158) (by decide +kernel)

private def env356_1 : Env := put (env354_1) 19 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok358 : Covered (env356_1) := replay_ok (k := 1) (i := 32843) (by decide +kernel)

private def env356_2 : Env := put (env354_1) 19 2

private def env359_0 : Env := put (env356_2) 17 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok360 : Covered (env359_0) := replay_ok (k := 1) (i := 32937) (by decide +kernel)

private def env359_1 : Env := put (env356_2) 17 1

private def env361_0 : Env := put (env359_1) 43 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok362 : Covered (env361_0) := replay_ok (k := 1) (i := 32811) (by decide +kernel)

private def env361_1 : Env := put (env359_1) 43 1

private def env363_0 : Env := put (env361_1) 23 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok364 : Covered (env363_0) := replay_ok (k := 1) (i := 33481) (by decide +kernel)

private def env363_1 : Env := put (env361_1) 23 1

private def env365_0 : Env := put (env363_1) 37 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok366 : Covered (env365_0) := replay_ok (k := 1) (i := 32804) (by decide +kernel)

private def env365_1 : Env := put (env363_1) 37 1

private def env367_0 : Env := put (env365_1) 83 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok368 : Covered (env367_0) := replay_ok (k := 1) (i := 32851) (by decide +kernel)

private def env367_1 : Env := put (env365_1) 83 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok369 : Covered (env367_1) := replay_ok (k := 39) (i := 21427) (by decide +kernel)

private def env367_2 : Env := put (env365_1) 83 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok370 : Covered (env367_2) := replay_ok (k := 22) (i := 21538) (by decide +kernel)

private theorem ok367 : Covered (env365_1) := combine _ 83 ok368 ok369 ok370

private def env365_2 : Env := put (env363_1) 37 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok371 : Covered (env365_2) := replay_ok (k := 3) (i := 21541) (by decide +kernel)

private theorem ok365 : Covered (env363_1) := combine _ 37 ok366 ok367 ok371

private def env363_2 : Env := put (env361_1) 23 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok372 : Covered (env363_2) := replay_ok (k := 1) (i := 32812) (by decide +kernel)

private theorem ok363 : Covered (env361_1) := combine _ 23 ok364 ok365 ok372

private def env361_2 : Env := put (env359_1) 43 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok373 : Covered (env361_2) := replay_ok (k := 1) (i := 32852) (by decide +kernel)

private theorem ok361 : Covered (env359_1) := combine _ 43 ok362 ok363 ok373

private def env359_2 : Env := put (env356_2) 17 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok374 : Covered (env359_2) := replay_ok (k := 5) (i := 21548) (by decide +kernel)

private theorem ok359 : Covered (env356_2) := combine _ 17 ok360 ok361 ok374

private theorem ok356 : Covered (env354_1) := combine _ 19 ok357 ok358 ok359

private def env354_2 : Env := put (env353_0) 11 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok375 : Covered (env354_2) := replay_ok (k := 16) (i := 21612) (by decide +kernel)

private theorem ok354 : Covered (env353_0) := combine _ 11 ok355 ok356 ok375

private def env353_1 : Env := put (env350_2) 13 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok376 : Covered (env353_1) := replay_ok (k := 1) (i := 32831) (by decide +kernel)

private def env353_2 : Env := put (env350_2) 13 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok377 : Covered (env353_2) := replay_ok (k := 25) (i := 21804) (by decide +kernel)

private theorem ok353 : Covered (env350_2) := combine _ 13 ok354 ok376 ok377

private theorem ok350 : Covered (env349_0) := combine _ 5 ok351 ok352 ok353

private def env349_1 : Env := put (env343_2) 31 1

private def env378_0 : Env := put (env349_1) 109 0

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok379 : Covered (env378_0) := replay_ok (k := 23) (i := 22080) (by decide +kernel)

private def env378_1 : Env := put (env349_1) 109 1

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok380 : Covered (env378_1) := replay_ok (k := 15) (i := 22317) (by decide +kernel)

private def env378_2 : Env := put (env349_1) 109 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok381 : Covered (env378_2) := replay_ok (k := 1) (i := 32984) (by decide +kernel)

private theorem ok378 : Covered (env349_1) := combine _ 109 ok379 ok380 ok381

private def env349_2 : Env := put (env343_2) 31 2

set_option maxRecDepth 25000 in
set_option maxHeartbeats 4000000 in
private def ok382 : Covered (env349_2) := replay_ok (k := 1) (i := 32830) (by decide +kernel)

private theorem ok349 : Covered (env343_2) := combine _ 31 ok350 ok378 ok382

private theorem ok343 : Covered (env298_2) := combine _ 7 ok344 ok345 ok349

private theorem ok298 : Covered (put emptyEnv 2 1) := combine _ 3 ok299 ok324 ok343

private theorem finish (w : ℕ → F) : Wins w := by
  have empty (f : ℕ → F) : Agrees f emptyEnv := by intro p a h; simp [emptyEnv] at h
  have cases3 : ∀ z : F, z=0 ∨ z=1 ∨ z=2 := by decide
  rcases cases3 (w 2) with h|h|h
  · exact ok0 w (by simpa [h] using agree_put (empty w) 2)
  · exact ok298 w (by simpa [h] using agree_put (empty w) 2)
  · let v : ℕ → F := fun p => -w p
    have hv : v 2 = 1 := by change -w 2 = 1; rw [h]; decide
    obtain ⟨n,hn,h0,h1,h2⟩ := ok298 v (by simpa [hv] using agree_put (empty v) 2)
    have negsum (ps : List ℕ) : (ps.map v).sum = -(ps.map w).sum := by
      induction ps with
      | nil => simp
      | cons p ps ih => simp [ih,v,add_comm]
    exact ⟨n,hn,by simpa only [negsum,neg_eq_zero] using h0,
      by simpa only [negsum,neg_eq_zero] using h1,
      by simpa only [negsum,neg_eq_zero] using h2⟩
end OMA.CubicTriples

theorem OMA.CubicTriples.searchBound : OMA.R_Erdos436_erdos_436_variants_three_three_R1.H1 :=
  OMA.CubicTriples.finish

/-! Prime-ideal Dirichlet sums from the Dedekind zeta pole and Euler product.
Adapted from Chris Birkbeck, Riccardo Brasca and the contributors to
CBirkbeck/chebotarev-density, revision
a00054a0e6bbc394b0e81de750db0cd2efc8bd88, under Apache-2.0.
The Euler product originally comes from flt-regular-bernoulli.
The comparison of rational reduction counts is independent of that source. -/
noncomputable section

open Filter Topology

theorem tendsto_log_one_div_sub_one_atTop :
    Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop := by
  refine Real.tendsto_log_atTop.comp ?_
  have h1 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((continuous_sub_right 1).tendsto' 1 0 (by ring)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s hs ↦ by
        simp only [Set.mem_Ioi] at hs ⊢
        linarith)
  simpa only [one_div] using! h1.inv_tendsto_nhdsGT_zero

theorem tendsto_ratio_one_of_div_atTop_pm_bounded
    {l : Filter ℝ} {g f : ℝ → ℝ} (hg : Tendsto g l atTop)
    (h_le : ∃ C : ℝ, ∀ᶠ s in l, f s ≤ g s + C)
    (h_lower : ∃ C : ℝ, ∀ᶠ s in l, g s - C ≤ f s) :
    Tendsto (fun s : ℝ ↦ f s / g s) l (𝓝 1) := by
  obtain ⟨C₁, hle⟩ := h_le
  obtain ⟨C₂, hlower⟩ := h_lower
  have h0 : Tendsto (fun s ↦ (f s - g s) / g s) l (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero (b := -C₂) (B := C₁)
      (hlower.mono fun s h ↦ by linarith) (hle.mono fun s h ↦ by linarith) hg
  refine (add_zero (1 : ℝ) ▸ h0.const_add 1).congr' ?_
  filter_upwards [hg.eventually_gt_atTop 0] with s h
  rw [add_div_eq_mul_add_div _ _ h.ne', one_mul, add_sub_cancel]

theorem tendsto_ratio_one_of_log_pm_bounded (f : ℝ → ℝ)
    (h_le : ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), f s ≤ Real.log (1 / (s - 1)) + C)
    (h_lower : ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), Real.log (1 / (s - 1)) - C ≤ f s) :
    Tendsto (fun s : ℝ ↦ f s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 1) :=
  tendsto_ratio_one_of_div_atTop_pm_bounded tendsto_log_one_div_sub_one_atTop h_le h_lower
end
noncomputable section

open NumberField
open scoped Topology nonZeroDivisors

namespace Chebotarev

section NumberFieldEulerProduct

variable (L : Type*) [Field L] [NumberField L]

abbrev NonzeroIdeal : Type _ := {I : Ideal (𝓞 L) // I ≠ ⊥}

noncomputable def idealNormMultiplicity (n : ℕ) : ℕ :=
  Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 = n}

lemma idealNormMultiplicity_zero : idealNormMultiplicity L 0 = 0 := by
  unfold idealNormMultiplicity
  rw [Nat.card_eq_zero]
  exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩

lemma idealNormMultiplicity_one : idealNormMultiplicity L 1 = 1 := by
  unfold idealNormMultiplicity
  have : Unique {I : NonzeroIdeal L // Ideal.absNorm I.1 = 1} :=
    { default := ⟨⟨⊤, by simp⟩, Ideal.absNorm_top⟩
      uniq := fun ⟨⟨I, hI⟩, hnorm⟩ ↦
        Subtype.ext (Subtype.ext (Ideal.absNorm_eq_one_iff.mp hnorm)) }
  exact Nat.card_unique

lemma dedekindZeta_eq_tsum_idealNormMultiplicity {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∑' n : ℕ, (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) := by
  unfold NumberField.dedekindZeta LSeries
  refine tsum_congr fun n ↦ ?_
  unfold LSeries.term
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
    simp [idealNormMultiplicity_zero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  · simp only [hn.ne', ↓reduceIte]
    rw [Complex.cpow_neg, div_eq_mul_inv]
    congr 1
    unfold idealNormMultiplicity
    have hequiv : {I : Ideal (𝓞 L) // Ideal.absNorm I = n} ≃
        {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} := by
      refine {
        toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
        invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
      intro h
      rw [h, Ideal.absNorm_bot] at hI
      lia
    exact_mod_cast Nat.card_congr hequiv

lemma sum_idealNormMultiplicity_isBigO :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity L k : ℝ))
      =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
  classical
  have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal L | Ideal.absNorm I.1 = b}.Finite := fun b ↦
    Set.Finite.preimage (f := fun I : NonzeroIdeal L ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
      (Ideal.finite_setOf_absNorm_eq (S := 𝓞 L) b)
  have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity L k =
      Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 ≤ n} := fun n ↦ by
    have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal L ↦
      Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ ↦ h_finite b)
    rw [show ((fun I : NonzeroIdeal L ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
        {I : NonzeroIdeal L | Ideal.absNorm I.1 ≤ n} by
      ext ⟨I, hI⟩
      simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_setOf_eq]
      exact ⟨fun h ↦ h.2, fun h ↦
        ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
    exact key.symm
  have h_card_bridge : ∀ n : ℕ,
      Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 ≤ n} =
      Nat.card {I : (Ideal (𝓞 L))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
    fun n ↦ Nat.card_congr
      { toFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
          ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
        invFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
          ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
    (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ L).comp
      tendsto_natCast_atTop_atTop).congr' ?_)
  filter_upwards with n
  simp only [Function.comp_apply, Real.rpow_one]
  rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
  push_cast
  rfl

lemma summable_idealNormMultiplicity_mul_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ ↦ ‖(idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)‖ := by
  classical
  have h_lss : LSeriesSummable (fun n : ℕ ↦ ((idealNormMultiplicity L n : ℝ) : ℂ)) s :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg
      (f := fun n ↦ (idealNormMultiplicity L n : ℝ))
      (sum_idealNormMultiplicity_isBigO L) (fun _ ↦ Nat.cast_nonneg _) zero_le_one
      (by exact_mod_cast hs)
  have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity L n : ℝ) : ℂ)) s =
      fun n ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) := by
    funext n
    simp only [LSeries.term]
    split_ifs with hn
    · subst hn
      simp [idealNormMultiplicity_zero]
    · simp [Complex.cpow_neg, div_eq_mul_inv]
  exact (h_term_eq ▸ h_lss :
    Summable fun n ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)).norm

private noncomputable def insertPiEquiv {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι)
    (ha : a ∉ s) : ({i // i ∈ insert a s} → ℕ) ≃ ℕ × ({i // i ∈ s} → ℕ) :=
  ((Finset.subtypeInsertEquivOption ha).arrowCongr (Equiv.refl ℕ)).trans Equiv.piOptionEquivProd

@[simp] private lemma insertPiEquiv_fst {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι)
    (ha : a ∉ s) (e : {i // i ∈ insert a s} → ℕ) :
    (insertPiEquiv a s ha e).1 = e ⟨a, Finset.mem_insert_self a s⟩ := rfl

@[simp] private lemma insertPiEquiv_snd {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι)
    (ha : a ∉ s) (e : {i // i ∈ insert a s} → ℕ) (i : {i // i ∈ s}) :
    (insertPiEquiv a s ha e).2 i = e ⟨i.1, Finset.mem_insert_of_mem i.2⟩ := rfl

private lemma prodInsertAttach {ι : Type*} [DecidableEq ι] (g : ι → ℂ) (a : ι) (s : Finset ι)
    (ha : a ∉ s) (e : {i // i ∈ insert a s} → ℕ) :
    ∏ i ∈ (insert a s).attach, g i.1 ^ e i =
      g a ^ (insertPiEquiv a s ha e).1 *
        ∏ i ∈ s.attach, g i.1 ^ (insertPiEquiv a s ha e).2 i := by
  rw [insertPiEquiv_fst]
  conv_rhs => rw [show (∏ i ∈ s.attach, g i.1 ^ (insertPiEquiv a s ha e).2 i)
    = ∏ i ∈ s.attach, g i.1 ^ e ⟨i.1, Finset.mem_insert_of_mem i.2⟩ from
    Finset.prod_congr rfl fun i _ ↦ by rw [insertPiEquiv_snd]]
  rw [Finset.attach_insert, Finset.prod_insert, Finset.prod_image]
  · exact fun x _ y _ h ↦ Subtype.ext (Subtype.mk.inj h)
  · simpa only [Finset.mem_image, Finset.mem_attach, Subtype.mk.injEq, true_and,
      Subtype.exists, exists_prop, exists_eq_right] using ha

private lemma finsetGeometricProd_summable_and_hasSum {ι : Type*} (g : ι → ℂ)
    (hg : ∀ i, ‖g i‖ < 1) (s : Finset ι) :
    (Summable fun e : {i // i ∈ s} → ℕ ↦ ‖∏ i ∈ s.attach, g i.1 ^ e i‖) ∧
      HasSum (fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i)
        (∏ i ∈ s, (1 - g i)⁻¹) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    refine ⟨?_, ?_⟩
    · have h1 : (fun e : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ ‖∏ i ∈ Finset.attach ∅, g i.1 ^ e i‖)
          = fun _ ↦ (1 : ℝ) := by
        funext e
        simp [Finset.attach_empty]
      rw [h1]
      exact (hasSum_unique (fun _ : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ (1 : ℝ))).summable
    · have h1 : (fun e : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ ∏ i ∈ Finset.attach ∅, g i.1 ^ e i)
          = fun _ ↦ (1 : ℂ) := by
        funext e
        simp [Finset.attach_empty]
      rw [h1]
      exact hasSum_unique (fun _ : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ (1 : ℂ))
  | insert a s ha ih =>
    obtain ⟨ihsum, ihhas⟩ := ih
    rw [Finset.prod_insert ha]
    have hgeo : HasSum (fun n : ℕ ↦ g a ^ n) (1 - g a)⁻¹ :=
      hasSum_geometric_of_norm_lt_one (hg a)
    have hgeosum : Summable (fun n : ℕ ↦ ‖g a ^ n‖) := by
      simp_rw [norm_pow]
      exact summable_geometric_of_lt_one (norm_nonneg _) (hg a)
    have hprodsum : Summable (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
        g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i) :=
      summable_mul_of_summable_norm (f := fun n : ℕ ↦ g a ^ n)
        (g := fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i) hgeosum ihsum
    have hHsum : Summable (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
        ‖g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i‖) :=
      Summable.mul_norm (f := fun n : ℕ ↦ g a ^ n)
        (g := fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i) hgeosum ihsum
    have hHhas : HasSum (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
        g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i) ((1 - g a)⁻¹ * ∏ i ∈ s, (1 - g i)⁻¹) :=
      HasSum.mul (f := fun n : ℕ ↦ g a ^ n)
        (g := fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i) hgeo ihhas hprodsum
    refine ⟨?_, ?_⟩
    · have heq : (fun e : {i // i ∈ insert a s} → ℕ ↦ ‖∏ i ∈ (insert a s).attach, g i.1 ^ e i‖)
          = (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
              ‖g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i‖) ∘ insertPiEquiv a s ha := by
        funext e
        rw [Function.comp_apply, prodInsertAttach g a s ha e]
      rw [heq]
      exact (insertPiEquiv a s ha).summable_iff.mpr hHsum
    · have heq : (fun e : {i // i ∈ insert a s} → ℕ ↦ ∏ i ∈ (insert a s).attach, g i.1 ^ e i)
          = (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
              g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i) ∘ insertPiEquiv a s ha := by
        funext e
        rw [Function.comp_apply, prodInsertAttach g a s ha e]
      rw [heq]
      exact (insertPiEquiv a s ha).hasSum_iff.mpr hHhas

private lemma prod_natCast_cpow {ι : Type*} (S : Finset ι) (m : ι → ℕ) (z : ℂ) :
    (∏ i ∈ S, (m i : ℂ) ^ z) = ((∏ i ∈ S, m i : ℕ) : ℂ) ^ z := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]

lemma norm_absNorm_cpow_neg_lt_one {s : ℂ} (hs : 1 < s.re)
    (𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ < 1 := by
  have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h ↦ 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
  have hne1 : Ideal.absNorm 𝔭.1 ≠ 1 := fun h ↦ 𝔭.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have h2 : 2 ≤ Ideal.absNorm 𝔭.1 := by lia
  rw [Complex.norm_natCast_cpow_of_pos (by lia), Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast h2.trans_lt' one_lt_two) (by linarith)

theorem prod_eulerFactor_eq_tsum_exponentVector {s : ℂ} (hs : 1 < s.re)
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    (∏ 𝔭 ∈ S, (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹) =
      ∑' e : S →₀ ℕ, ∏ 𝔭 ∈ S.attach, (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s) := by
  classical
  have hg : ∀ 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ < 1 := norm_absNorm_cpow_neg_lt_one L hs
  have hHS := (finsetGeometricProd_summable_and_hasSum
    (fun 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)) hg S).2
  have hrw : ∀ e : S → ℕ,
      (∏ 𝔭 ∈ S.attach, ((Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-s)) ^ e 𝔭) =
        ∏ 𝔭 ∈ S.attach, (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s) := fun e ↦
    Finset.prod_congr rfl fun 𝔭 _ ↦ by
      rw [← Complex.cpow_nat_mul]
      ring_nf
  rw [← hHS.tsum_eq, ← (Finsupp.equivFunOnFinite (α := S) (M := ℕ)).tsum_eq
    (fun e : S → ℕ ↦ ∏ 𝔭 ∈ S.attach, ((Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-s)) ^ e 𝔭)]
  refine tsum_congr fun e ↦ ?_
  simp only [Finsupp.equivFunOnFinite_apply]
  rw [hrw]

theorem absNorm_prod_pow_of_primeIdeal
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (e : S → ℕ) :
    Ideal.absNorm (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭) =
      ∏ 𝔭 ∈ S.attach, Ideal.absNorm 𝔭.1.1 ^ e 𝔭 := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun 𝔭 _ ↦ map_pow Ideal.absNorm 𝔭.1.1 (e 𝔭)

theorem prod_absNorm_cpow_eq_absNorm_prod_pow_cpow {s : ℂ}
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (e : S → ℕ) :
    (∏ 𝔭 ∈ S.attach, (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s)) =
      (Ideal.absNorm (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭) : ℂ) ^ (-s) := by
  have hinner : ∀ 𝔭 ∈ S.attach,
      (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s) =
        ((Ideal.absNorm 𝔭.1.1 ^ e 𝔭 : ℕ) : ℂ) ^ (-s) := fun 𝔭 _ ↦ by
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
    ring_nf
  rw [Finset.prod_congr rfl hinner, prod_natCast_cpow, absNorm_prod_pow_of_primeIdeal]

private instance instFiniteAbsNormFiber (n : ℕ) :
    Finite {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} :=
  Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal L ↦ I.1)
    ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 L) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
    (fun _ _ _ _ ↦ Subtype.ext)

private lemma tsum_absNormFiber {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M]
    [IsTopologicalAddGroup M] (n : ℕ) (g : ℕ → M) :
    (∑' y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n}, g (Ideal.absNorm y.1.1))
      = idealNormMultiplicity L n • g n :=
  (tsum_congr fun y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
    (tsum_const (g n))

theorem hasSum_nonzeroIdeal_absNorm_cpow {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : NonzeroIdeal L ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s))
      (NumberField.dedekindZeta L s) := by
  classical
  set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal L ↦ Ideal.absNorm I.1)
  have hval : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n},
      (Ideal.absNorm (y.1).1 : ℂ) ^ (-s)) = (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) :=
    fun n ↦ by rw [tsum_absNormFiber L n fun k ↦ (k : ℂ) ^ (-s), nsmul_eq_mul]
  have hnorm : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n},
      ‖(Ideal.absNorm (y.1).1 : ℂ) ^ (-s)‖) = ‖(idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)‖ :=
    fun n ↦ by
      rw [tsum_absNormFiber L n fun k ↦ ‖(k : ℂ) ^ (-s)‖, nsmul_eq_mul, norm_mul,
        Complex.norm_natCast]
  have hsummable : Summable fun I : NonzeroIdeal L ↦ ‖(Ideal.absNorm I.1 : ℂ) ^ (-s)‖ := by
    rw [← e.summable_iff]
    refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun _ ↦ Summable.of_finite, ?_⟩
    exact (summable_idealNormMultiplicity_mul_cpow_neg L hs).congr fun n ↦ (hnorm n).symm
  have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} ↦
      (Ideal.absNorm (e p).1 : ℂ) ^ (-s) :=
    (e.summable_iff (f := fun I : NonzeroIdeal L ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s))).mpr
      hsummable.of_norm
  have hval_sum : (∑' I : NonzeroIdeal L, (Ideal.absNorm I.1 : ℂ) ^ (-s))
      = NumberField.dedekindZeta L s := by
    rw [dedekindZeta_eq_tsum_idealNormMultiplicity L hs,
      ← e.tsum_eq (fun I ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s)), hsummable_sigma.tsum_sigma]
    exact tsum_congr hval
  exact hval_sum ▸ hsummable.of_norm.hasSum

open UniqueFactorizationMonoid in

private theorem factorization_primePow_apply
    (𝔭 𝔮 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (n : ℕ) :
    factorization (𝔭.1 ^ n) 𝔮.1 = if 𝔮 = 𝔭 then n else 0 := by
  rw [factorization_pow, Finsupp.smul_apply, smul_eq_mul, factorization_eq_count,
    normalizedFactors_irreducible (Ideal.prime_of_isPrime 𝔭.2.2 𝔭.2.1).irreducible,
    normalize_eq, Multiset.count_singleton]
  split_ifs <;> simp_all [Subtype.ext_iff]

open UniqueFactorizationMonoid in

private theorem factorization_prod_primePow_apply
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (e : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℕ)
    (𝔮 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    factorization (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭.1) 𝔮.1 =
      ∑ 𝔭 ∈ S.attach, factorization (𝔭.1.1 ^ e 𝔭.1) 𝔮.1 := by
  classical
  induction S using Finset.induction with
  | empty => rw [Finset.attach_empty, Finset.prod_empty, Finset.sum_empty, factorization_one,
      Finsupp.coe_zero, Pi.zero_apply]
  | insert a s ha ih =>
    rw [Finset.attach_insert, Finset.prod_insert, Finset.sum_insert,
      factorization_mul (pow_ne_zero _ a.2.2)
        (Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ ↦ pow_ne_zero _ 𝔭.1.2.2)), Finsupp.add_apply,
      Finset.prod_image (fun x _ y _ h ↦ Subtype.ext (by simpa using h)),
      Finset.sum_image (fun x _ y _ h ↦ Subtype.ext (by simpa using h)), ih] <;>
    · rw [Finset.mem_image]
      rintro ⟨x, -, hx⟩
      exact ha ((Subtype.mk.inj hx) ▸ x.2)

open UniqueFactorizationMonoid in

private theorem factorization_prod_primePow_eq
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (e : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℕ)
    (𝔮 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    factorization (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭.1) 𝔮.1 = if 𝔮 ∈ S then e 𝔮 else 0 := by
  classical
  rw [factorization_prod_primePow_apply L S e 𝔮]
  simp_rw [factorization_primePow_apply L]
  by_cases h𝔮 : 𝔮 ∈ S
  · rw [if_pos h𝔮, Finset.sum_eq_single (⟨𝔮, h𝔮⟩ : {x // x ∈ S})]
    · rw [if_pos rfl]
    · rintro b _ hb
      rw [if_neg (fun h ↦ hb (Subtype.ext h.symm))]
    · exact fun h ↦ absurd (Finset.mem_attach S _) h
  · rw [if_neg h𝔮, Finset.sum_eq_zero]
    rintro ⟨b, hb⟩ -
    rw [if_neg (fun h : 𝔮 = b ↦ h𝔮 (h.symm ▸ hb))]

open UniqueFactorizationMonoid in

private noncomputable def primeFactorsOf (𝔞 : NonzeroIdeal L) :
    Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
  (normalizedFactors 𝔞.1).toFinset.attach.map
    (⟨fun p : {x // x ∈ (normalizedFactors 𝔞.1).toFinset} ↦ (⟨p.1, by
        have hp := p.2
        rw [Multiset.mem_toFinset] at hp
        exact ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor p.1 hp),
          (prime_of_normalized_factor p.1 hp).ne_zero⟩⟩ :
        {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}),
      fun a b h ↦ Subtype.ext (congrArg
        (fun x : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (x : Ideal (𝓞 L))) h)⟩ :
      {x // x ∈ (normalizedFactors 𝔞.1).toFinset} ↪ {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})

open UniqueFactorizationMonoid in

private theorem mem_primeFactorsOf (𝔞 : NonzeroIdeal L) (p : Ideal (𝓞 L))
    (hp : p ∈ normalizedFactors 𝔞.1) :
    ∃ 𝔭 ∈ primeFactorsOf L 𝔞, 𝔭.1 = p := by
  refine ⟨⟨p, ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor p hp),
      (prime_of_normalized_factor p hp).ne_zero⟩⟩, ?_, rfl⟩
  rw [primeFactorsOf, Finset.mem_map]
  exact ⟨⟨p, by rwa [Multiset.mem_toFinset]⟩, Finset.mem_attach _ _, rfl⟩

open UniqueFactorizationMonoid in
private theorem factorization_idealOfExp_eq
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (f : S →₀ ℕ) (𝔮 : S) :
    factorization (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ f 𝔭) 𝔮.1.1 = f 𝔮 := by
  classical
  have hprod : (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ (fun q ↦ if h : q ∈ S then f ⟨q, h⟩ else 0) 𝔭.1)
      = ∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ f 𝔭 :=
    Finset.prod_congr rfl fun 𝔭 _ ↦ by simp only [dif_pos 𝔭.2]
  rw [← hprod, factorization_prod_primePow_eq L S
    (fun q ↦ if h : q ∈ S then f ⟨q, h⟩ else 0) 𝔮.1, if_pos 𝔮.2, dif_pos 𝔮.2]

open UniqueFactorizationMonoid in
private theorem prod_primePow_count_eq (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (𝔞 : NonzeroIdeal L) (hsupp : ∀ p ∈ normalizedFactors 𝔞.1, ∃ 𝔭 ∈ S, 𝔭.1 = p) :
    (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ (normalizedFactors 𝔞.1).count 𝔭.1.1) = 𝔞.1 := by
  classical
  rw [show (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ (normalizedFactors 𝔞.1).count 𝔭.1.1)
      = ∏ p ∈ S.image (fun 𝔭 ↦ 𝔭.1), p ^ (normalizedFactors 𝔞.1).count p by
    rw [Finset.prod_image (fun x _ y _ h ↦ Subtype.ext h), ← Finset.prod_attach S
      (fun p ↦ p.1 ^ (normalizedFactors 𝔞.1).count p.1)]]
  rw [← Finset.prod_subset (s₁ := (normalizedFactors 𝔞.1).toFinset)
    (s₂ := S.image (fun 𝔭 ↦ 𝔭.1))
    (fun p hp ↦ by
      rw [Multiset.mem_toFinset] at hp
      obtain ⟨𝔭, h𝔭S, rfl⟩ := hsupp p hp
      exact Finset.mem_image.mpr ⟨𝔭, h𝔭S, rfl⟩)
    (fun p _ hp ↦ by
      rw [Multiset.mem_toFinset] at hp
      rw [Multiset.count_eq_zero_of_notMem hp, pow_zero])]
  conv_rhs => rw [← finprod_pow_count_eq_of_subsingleton_units 𝔞.2]
  exact (finprod_eq_finsetProd_of_mulSupport_subset _ (by
    intro p hp
    simp only [Function.mem_mulSupport] at hp
    rw [Finset.mem_coe, Multiset.mem_toFinset]
    by_contra hc
    rw [Multiset.count_eq_zero_of_notMem hc, pow_zero] at hp
    exact hp rfl)).symm

omit [NumberField L] in

private theorem weight_prod_primePow (w : Ideal (𝓞 L) → ℂ) (hw_one : w ⊤ = 1)
    (hw_mul : ∀ {𝔞 𝔟 : Ideal (𝓞 L)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → w (𝔞 * 𝔟) = w 𝔞 * w 𝔟)
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (e : S → ℕ) :
    w (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭) = ∏ 𝔭 ∈ S.attach, (w 𝔭.1.1) ^ e 𝔭 := by
  classical
  have wpow : ∀ (𝔭 : Ideal (𝓞 L)) (_ : 𝔭 ≠ ⊥) (k : ℕ), w (𝔭 ^ k) = (w 𝔭) ^ k := by
    intro 𝔭 h𝔭 k
    induction k with
    | zero => simpa using hw_one
    | succ n ih => rw [pow_succ, hw_mul (pow_ne_zero _ h𝔭) h𝔭, ih, pow_succ]
  have key : ∀ T : Finset S, w (∏ 𝔭 ∈ T, 𝔭.1.1 ^ e 𝔭) = ∏ 𝔭 ∈ T, (w 𝔭.1.1) ^ e 𝔭 := by
    intro T
    induction T using Finset.induction with
    | empty => simpa using hw_one
    | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        hw_mul (pow_ne_zero _ a.1.2.2)
          (Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ ↦ pow_ne_zero _ 𝔭.1.2.2)),
        wpow a.1.1 a.1.2.2, ih]
  exact key S.attach

private theorem weighted_prod_eulerFactor_eq_tsum {s : ℂ} (hs : 1 < s.re)
    (w : Ideal (𝓞 L) → ℂ) (hw_one : w ⊤ = 1)
    (hw_mul : ∀ {𝔞 𝔟 : Ideal (𝓞 L)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → w (𝔞 * 𝔟) = w 𝔞 * w 𝔟)
    (hw_norm : ∀ 𝔞, ‖w 𝔞‖ ≤ 1)
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (idealOfExp : (S →₀ ℕ) → NonzeroIdeal L)
    (hidealOfExp : ∀ e : S →₀ ℕ,
      (idealOfExp e).1 = ∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭)
    (hinj : Function.Injective idealOfExp) :
    (∏ 𝔭 ∈ S, (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹)
      = ∑' 𝔞 : Set.range idealOfExp,
          w 𝔞.1.1 * (Ideal.absNorm 𝔞.1.1 : ℂ) ^ (-s) := by
  classical
  have hg : ∀ 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      ‖w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ < 1 := fun 𝔭 ↦
    ((norm_mul_le_of_le (hw_norm _) le_rfl).trans_eq (one_mul _)).trans_lt
      (norm_absNorm_cpow_neg_lt_one L hs 𝔭)
  have hHS := (finsetGeometricProd_summable_and_hasSum
    (fun 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)) hg S).2
  have hsummand : ∀ e : S →₀ ℕ,
      (∏ 𝔭 ∈ S.attach, (w 𝔭.1.1 * (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-s)) ^ e 𝔭)
        = w (idealOfExp e).1 * (Ideal.absNorm (idealOfExp e).1 : ℂ) ^ (-s) := fun e ↦ by
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib,
      show (∏ 𝔭 ∈ S.attach, ((Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-s)) ^ e 𝔭)
        = ∏ 𝔭 ∈ S.attach, (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s) from
      Finset.prod_congr rfl fun 𝔭 _ ↦ by
        rw [← Complex.cpow_nat_mul]
        ring_nf,
      prod_absNorm_cpow_eq_absNorm_prod_pow_cpow L S (fun 𝔭 ↦ e 𝔭),
      ← weight_prod_primePow L w hw_one hw_mul S (fun 𝔭 ↦ e 𝔭), hidealOfExp e]
  have hHS' : HasSum
      (fun e : S →₀ ℕ ↦ w (idealOfExp e).1 * (Ideal.absNorm (idealOfExp e).1 : ℂ) ^ (-s))
      (∏ 𝔭 ∈ S, (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹) := by
    have hbase := (Finsupp.equivFunOnFinite (α := S) (M := ℕ)).hasSum_iff.mpr hHS
    refine hbase.congr_fun fun e ↦ ?_
    simp only [Function.comp_apply, Finsupp.equivFunOnFinite_apply]
    exact (hsummand e).symm
  rw [← hHS'.tsum_eq]
  exact (tsum_range
    (fun 𝔞 : NonzeroIdeal L ↦ w 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)) hinj).symm

open UniqueFactorizationMonoid in

theorem weighted_eulerProduct_eq_tsum {s : ℂ} (hs : 1 < s.re)
    (w : Ideal (𝓞 L) → ℂ) (hw_one : w ⊤ = 1)
    (hw_mul : ∀ {𝔞 𝔟 : Ideal (𝓞 L)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → w (𝔞 * 𝔟) = w 𝔞 * w 𝔟)
    (hw_norm : ∀ 𝔞, ‖w 𝔞‖ ≤ 1) :
    (∏' 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹)
      = ∑' 𝔞 : NonzeroIdeal L, w 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s) := by
  classical
  set P := {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}
  set Dw : NonzeroIdeal L → ℂ := fun 𝔞 ↦ w 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s) with hDw
  set idealOfExp : (S : Finset P) → (S →₀ ℕ) → NonzeroIdeal L :=
    fun S e ↦ ⟨∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭,
      Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ ↦ pow_ne_zero _ 𝔭.1.2.2)⟩ with hidealOfExp
  have hnormD : Summable fun 𝔞 : NonzeroIdeal L ↦ ‖Dw 𝔞‖ := by
    refine ((hasSum_nonzeroIdeal_absNorm_cpow L hs).summable.norm).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (fun 𝔞 ↦ ?_)
    rw [hDw]
    exact (norm_mul_le_of_le (hw_norm _) le_rfl).trans_eq (one_mul _)
  have hinj : ∀ S : Finset P, Function.Injective (idealOfExp S) := by
    intro S e e' h
    rw [hidealOfExp, Subtype.mk.injEq] at h
    ext 𝔮
    rw [← factorization_idealOfExp_eq L S e 𝔮, ← factorization_idealOfExp_eq L S e' 𝔮, h]
  have hmem : ∀ (S : Finset P) (𝔞 : NonzeroIdeal L),
      (∀ p ∈ normalizedFactors 𝔞.1, ∃ 𝔭 ∈ S, 𝔭.1 = p) →
      𝔞 ∈ Set.range (idealOfExp S) := by
    intro S 𝔞 hsupp
    refine ⟨Finsupp.onFinset S.attach
      (fun 𝔭 ↦ (normalizedFactors 𝔞.1).count 𝔭.1.1) (by simp), ?_⟩
    rw [hidealOfExp, Subtype.ext_iff]
    simpa only [Finsupp.onFinset_apply] using prod_primePow_count_eq L S 𝔞 hsupp
  have hpartial : ∀ S : Finset P,
      (∏ 𝔭 ∈ S, (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹)
        = ∑' 𝔞 : Set.range (idealOfExp S), Dw 𝔞.1 := by
    intro S
    exact weighted_prod_eulerFactor_eq_tsum L hs w hw_one hw_mul hw_norm S (idealOfExp S)
      (fun e ↦ rfl) (hinj S)
  refine HasProd.tprod_eq ?_
  rw [HasProd, SummationFilter.unconditional, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨F, hF⟩ := ((tendsto_tsum_compl_atTop_zero (fun 𝔞 ↦ ‖Dw 𝔞‖)).eventually
    (gt_mem_nhds hε)).exists
  refine ⟨F.biUnion (primeFactorsOf L), fun S hS ↦ ?_⟩
  have hF_sub : ∀ 𝔞 ∈ F, 𝔞 ∈ Set.range (idealOfExp S) := by
    intro 𝔞 h𝔞F
    refine hmem S 𝔞 fun p hp ↦ ?_
    obtain ⟨𝔭, h𝔭, rfl⟩ := mem_primeFactorsOf L 𝔞 p hp
    exact ⟨𝔭, hS (Finset.mem_biUnion.mpr ⟨𝔞, h𝔞F, h𝔭⟩), rfl⟩
  rw [dist_eq_norm, hpartial S]
  have hsplit : ∑' 𝔞 : NonzeroIdeal L, Dw 𝔞 =
      (∑' 𝔞 : Set.range (idealOfExp S), Dw 𝔞.1) +
        ∑' 𝔞 : ↥(Set.range (idealOfExp S))ᶜ, Dw 𝔞.1 :=
    (hnormD.of_norm.tsum_subtype_add_tsum_subtype_compl _).symm
  rw [hsplit, sub_add_cancel_left, norm_neg]
  refine (norm_tsum_le_tsum_norm (hnormD.subtype _)).trans_lt ?_
  refine lt_of_le_of_lt ?_ hF
  refine (hnormD.subtype _).tsum_le_tsum_of_inj
    (fun 𝔞 : ↥(Set.range (idealOfExp S))ᶜ ↦
      (⟨𝔞.1, fun h ↦ 𝔞.2 (hF_sub 𝔞.1 h)⟩ : {x // x ∉ F}))
    (fun x y h ↦ Subtype.ext (congrArg (fun z : {x // x ∉ F} ↦ (z : NonzeroIdeal L)) h))
    (fun _ _ ↦ norm_nonneg _) (fun _ ↦ le_rfl) (hnormD.subtype _)

open UniqueFactorizationMonoid in

theorem dedekindZeta_eq_tprod_primeIdeal {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∏' 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ := by
  have hw := weighted_eulerProduct_eq_tsum L hs (fun _ ↦ 1) (by simp) (by simp) (by simp)
  simp only [one_mul] at hw
  exact (hw.trans (hasSum_nonzeroIdeal_absNorm_cpow L hs).tsum_eq).symm

theorem dedekindZeta_re_pos_of_one_lt (s : ℝ) (hs : 1 < s) :
    0 < (NumberField.dedekindZeta L (s : ℂ)).re := by
  have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  set g : ℕ → ℝ := fun n ↦ (idealNormMultiplicity L n : ℝ) * (n : ℝ) ^ (-s) with hg
  have key : ∀ n : ℕ,
      (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) = ((g n : ℝ) : ℂ) := by
    intro n
    have hcast : ((n : ℝ) ^ (-s) : ℝ) = ((n : ℂ) ^ (-(s : ℂ))) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n) (-s)]
      norm_cast
    rw [hg]
    push_cast [hcast]
    ring
  have hsumC : Summable
      fun n : ℕ ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) :=
    (summable_idealNormMultiplicity_mul_cpow_neg L hs').of_norm
  have hsumR : Summable g := Complex.summable_ofReal.mp (by simpa only [key] using hsumC)
  have hre : (NumberField.dedekindZeta L (s : ℂ)).re = ∑' n : ℕ, g n := by
    rw [dedekindZeta_eq_tsum_idealNormMultiplicity L hs']
    simp_rw [key]
    rw [Complex.re_tsum (by simpa only [key] using hsumC)]
    simp
  rw [hre]
  refine hsumR.tsum_pos (fun n ↦ ?_) 1 ?_
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · rw [hg]
    simp [idealNormMultiplicity_one]

end NumberFieldEulerProduct

end Chebotarev
end
noncomputable section

open Filter NumberField Topology Set

namespace Chebotarev

variable {K : Type*} [Field K] [NumberField K] {S : Set (Ideal (𝓞 K))} {δ : ℝ}

def primeIdealZetaSum (S : Set (Ideal (𝓞 K))) (s : ℝ) : ℝ :=
  ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
    (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)

theorem primeIdealZetaSum_def (S : Set (Ideal (𝓞 K))) (s : ℝ) :
    primeIdealZetaSum S s =
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := rfl

private theorem summable_nonzeroIdeal_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s)) :=
  ((hasSum_nonzeroIdeal_absNorm_cpow K (s := (s : ℂ)) (by simpa using hs)).summable.norm).congr
    fun I ↦ (Complex.norm_natCast_cpow_of_pos
      (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2)) _).trans <| by
      rw [Complex.neg_re, Complex.ofReal_re]

theorem summable_prime_absNorm_rpow (S : Set (Ideal (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) := by
  have hi : Function.Injective
      (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
        (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal K)) :=
    fun a b hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)
  exact ((summable_nonzeroIdeal_absNorm_rpow hs).comp_injective hi).congr fun _ ↦ rfl

private theorem primeIdealZetaSum_nonneg (S : Set (Ideal (𝓞 K))) (s : ℝ) :
    0 ≤ primeIdealZetaSum S s :=
  tsum_nonneg fun _ ↦ by positivity

private theorem primeIdealZetaSum_le_univ {s : ℝ} (hs : 1 < s) :
    primeIdealZetaSum S s ≤ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s := by
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def]
  refine (summable_prime_absNorm_rpow S hs).tsum_le_tsum_of_inj
    (fun 𝔭 ↦ ⟨𝔭.1, ⟨mem_univ _, 𝔭.2.2.1, 𝔭.2.2.2⟩⟩)
    (fun a b hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab))
    (fun c _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun 𝔭 ↦ le_of_eq rfl) (summable_prime_absNorm_rpow (univ : Set (Ideal (𝓞 K))) hs)

theorem primeIdealZetaSum_le_of_subset {T : Set (Ideal (𝓞 K))} (hST : S ⊆ T) {s : ℝ} (hs : 1 < s) :
    primeIdealZetaSum S s ≤ primeIdealZetaSum T s := by
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def]
  refine (summable_prime_absNorm_rpow S hs).tsum_le_tsum_of_inj
    (fun 𝔭 ↦ ⟨𝔭.1, hST 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩)
    (fun a b hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab))
    (fun c _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun _ ↦ le_rfl) (summable_prime_absNorm_rpow T hs)

theorem primeIdealZetaSum_union_of_disjoint {T : Set (Ideal (𝓞 K))} (hDisj : Disjoint S T) {s : ℝ}
    (hs : 1 < s) :
    primeIdealZetaSum (S ∪ T) s = primeIdealZetaSum S s + primeIdealZetaSum T s := by
  let eS : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
      ↑{x : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 K)) ∈ S} :=
    { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, Or.inl 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩, 𝔭.2.1⟩
      invFun := fun x ↦ ⟨x.1.1, x.2, x.1.2.2.1, x.1.2.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let eT : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
      ↑{x : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 K)) ∈ S}ᶜ :=
    { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, Or.inr 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩,
        fun h ↦ hDisj.le_bot ⟨h, 𝔭.2.1⟩⟩
      invFun := fun x ↦ ⟨x.1.1, x.1.2.1.resolve_left x.2, x.1.2.2.1, x.1.2.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def, primeIdealZetaSum_def,
    ← (summable_prime_absNorm_rpow (S ∪ T) hs).tsum_subtype_add_tsum_subtype_compl
      {x | (x.1 : Ideal (𝓞 K)) ∈ S},
    ← eS.tsum_eq (fun x ↦ (Ideal.absNorm (x.1 : Ideal (𝓞 K)) : ℝ) ^ (-s)),
    ← eT.tsum_eq (fun x ↦ (Ideal.absNorm (x.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))]
  rfl

theorem primeIdealZetaSum_empty (s : ℝ) : primeIdealZetaSum (∅ : Set (Ideal (𝓞 K))) s = 0 := by
  have : IsEmpty {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (∅ : Set (Ideal (𝓞 K))) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
    ⟨fun x ↦ x.2.1⟩
  rw [primeIdealZetaSum_def, tsum_empty]

theorem primeIdealZetaSum_biUnion_of_pairwiseDisjoint {ι : Type*} (t : Finset ι)
    (g : ι → Set (Ideal (𝓞 K))) (hg : (t : Set ι).PairwiseDisjoint g) {s : ℝ} (hs : 1 < s) :
    primeIdealZetaSum (⋃ i ∈ t, g i) s = ∑ i ∈ t, primeIdealZetaSum (g i) s := by
  classical
  induction t using Finset.induction with
  | empty => simp [primeIdealZetaSum_empty]
  | insert a t ha ih =>
      have hdisj : Disjoint (g a) (⋃ i ∈ t, g i) :=
        disjoint_iUnion₂_right.2 fun i hi ↦
          hg (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hi)
            (fun h ↦ ha (h ▸ hi))
      rw [Finset.set_biUnion_insert, primeIdealZetaSum_union_of_disjoint hdisj hs,
        Finset.sum_insert ha, ih (hg.subset (Finset.coe_subset.mpr (Finset.subset_insert a t)))]

theorem primeIdealZetaSum_eq_univ_of_forall_prime_mem
    (hS : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭 ∈ S) (s : ℝ) :
    primeIdealZetaSum S s = primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s := by
  let e : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
      {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (univ : Set (Ideal (𝓞 K))) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
    Equiv.subtypeEquivRight fun 𝔭 ↦
      ⟨fun h ↦ ⟨mem_univ _, h.2⟩, fun h ↦ ⟨hS 𝔭 h.2.1 h.2.2, h.2⟩⟩
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def,
    ← e.tsum_eq (fun 𝔭 ↦ (Ideal.absNorm (𝔭.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))]
  rfl

variable (K)

private theorem summable_prime2_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) :=
  ((summable_prime_absNorm_rpow (univ : Set (Ideal (𝓞 K))) hs).comp_injective
    (Equiv.subtypeEquivRight fun _ ↦ ⟨fun h ↦ ⟨mem_univ _, h⟩, fun h ↦ h.2⟩).injective).congr
    fun _ ↦ rfl

private theorem two_le_absNorm_of_prime {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) :
    (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ) :=
  have : (2 : ℕ) ≤ Ideal.absNorm 𝔭 := Nat.two_le_iff _ |>.2
    ⟨mt Ideal.absNorm_eq_zero_iff.1 hne, mt Ideal.absNorm_eq_one_iff.1 hp.ne_top⟩
  mod_cast this

private theorem absNorm_rpow_neg_lt_one {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) {s : ℝ}
    (hs : 1 < s) : (Ideal.absNorm 𝔭 : ℝ) ^ (-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg
    (by have := two_le_absNorm_of_prime K hp hne; linarith) (by linarith)

private theorem primeIdealHigherTail_term_le {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥)
    {s : ℝ} (hs : 1 < s) :
    (Ideal.absNorm 𝔭 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭 : ℝ) ^ (-s)) ≤
      2 * (Ideal.absNorm 𝔭 : ℝ) ^ (-(2 : ℝ)) := by
  set x : ℝ := (Ideal.absNorm 𝔭 : ℝ)
  have hx : (2 : ℝ) ≤ x := two_le_absNorm_of_prime K hp hne
  have hxs_half : x ^ (-s) ≤ 1 / 2 :=
    calc x ^ (-s) ≤ (2 : ℝ) ^ (-s) := Real.rpow_le_rpow_of_nonpos zero_lt_two hx (by linarith)
      _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  have hden_pos : (0 : ℝ) < 1 - x ^ (-s) := by linarith
  have hinv_le : (1 - x ^ (-s))⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hden_pos (by norm_num)]; linarith
  have hexp : x ^ (-(2 : ℝ) * s) ≤ x ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
  rw [div_eq_mul_inv]
  calc x ^ (-(2 : ℝ) * s) * (1 - x ^ (-s))⁻¹
      ≤ x ^ (-(2 : ℝ)) * 2 := mul_le_mul hexp hinv_le (by positivity) (by positivity)
    _ = 2 * x ^ (-(2 : ℝ)) := by ring

theorem primeIdealZetaHigherTail_bounded :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) ≤ C := by
  refine ⟨2 * ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
    (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ)), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [mem_Ioi] at hs
  have hbound : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) ≤
        2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ)) := fun 𝔭 ↦
    primeIdealHigherTail_term_le K 𝔭.2.1 𝔭.2.2 hs
  have hnonneg : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (0 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) :=
    fun 𝔭 ↦ div_nonneg (Real.rpow_nonneg (by positivity) _)
      (by have := absNorm_rpow_neg_lt_one K 𝔭.2.1 𝔭.2.2 hs; linarith)
  have hsummable_rhs : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ))) :=
    (summable_prime2_absNorm_rpow K one_lt_two).mul_left 2
  calc ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))
      ≤ ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
          2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ)) :=
        (Summable.of_nonneg_of_le hnonneg hbound hsummable_rhs).tsum_le_tsum hbound hsummable_rhs
    _ = 2 * ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
          (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ)) := tsum_mul_left

private theorem primeIdealZetaSum_univ_eq_tsum_prime2 (s : ℝ) :
    primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s =
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := by
  rw [primeIdealZetaSum_def, ← (Equiv.subtypeEquivRight fun 𝔭 ↦
    ⟨fun h ↦ ⟨mem_univ _, h⟩, fun h ↦ h.2⟩).tsum_eq
    fun 𝔭 ↦ (Ideal.absNorm (𝔭.1 : Ideal (𝓞 K)) : ℝ) ^ (-s)]
  rfl

private theorem one_sub_absNorm_rpow_pos {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥)
    {s : ℝ} (hs : 1 < s) : (0 : ℝ) < 1 - (Ideal.absNorm 𝔭 : ℝ) ^ (-s) := by
  have := absNorm_rpow_neg_lt_one K hp hne hs
  linarith

private theorem neg_log_one_sub_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ - Real.log (1 - x) - x ∧ - Real.log (1 - x) - x ≤ x ^ 2 / (1 - x) := by
  have hden : 0 < 1 - x := by linarith
  have habs : |x| < 1 := by rwa [abs_of_nonneg hx0]
  refine ⟨by have := Real.log_le_sub_one_of_pos hden; linarith, ?_⟩
  have key := Real.abs_log_sub_add_sum_range_le habs 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_one, Nat.cast_zero, zero_add,
    div_one, abs_of_nonneg hx0, Nat.reduceAdd] at key
  linarith [(abs_le.mp key).1]

private theorem summable_neg_log_one_sub_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      - Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))) := by
  refine ((Real.summable_log_one_add_of_summable
    (summable_prime2_absNorm_rpow K hs).neg).neg).congr fun 𝔭 ↦ ?_
  rw [sub_eq_add_neg]

private theorem log_dedekindZeta_re_eq_tsum_neg_log_one_sub {s : ℝ} (hs : 1 < s) :
    Real.log (dedekindZeta K (s : ℂ)).re =
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (- Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))) := by
  set g : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℝ :=
    fun 𝔭 ↦ (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))⁻¹ with hg
  have hgpos : ∀ 𝔭, 0 < g 𝔭 :=
    fun 𝔭 ↦ inv_pos.mpr (one_sub_absNorm_rpow_pos K 𝔭.2.1 𝔭.2.2 hs)
  have hlogsum : Summable (fun 𝔭 ↦ Real.log (g 𝔭)) := by
    refine (summable_neg_log_one_sub_absNorm_rpow K hs).congr (fun 𝔭 ↦ ?_)
    rw [hg, Real.log_inv]
  have hCprod : HasProd (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)))⁻¹)
      ((Real.exp (∑' 𝔭, Real.log (g 𝔭)) : ℝ) : ℂ) := by
    refine ((Real.hasProd_of_hasSum_log hgpos hlogsum.hasSum).map Complex.ofRealHom
      Complex.continuous_ofReal).congr_fun fun 𝔭 ↦ ?_
    rw [Function.comp_apply, Complex.ofRealHom_eq_coe, hg]
    push_cast [Complex.ofReal_cpow (show (0 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) by positivity)]
    ring
  have hre : (dedekindZeta K (s : ℂ)).re = Real.exp (∑' 𝔭, Real.log (g 𝔭)) := by
    rw [dedekindZeta_eq_tprod_primeIdeal K (by simpa using hs), hCprod.tprod_eq,
      Complex.ofReal_re]
  rw [hre, Real.log_exp]
  exact tsum_congr fun 𝔭 ↦ by rw [hg, Real.log_inv]

private theorem abs_tsum_neg_log_one_sub_sub_rpow_le :
    ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ),
      |∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (- Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))
          - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))| ≤ C := by
  obtain ⟨C, hC⟩ := primeIdealZetaHigherTail_bounded K
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with s hs_tail hs1
  simp only [mem_Ioi] at hs1
  set f : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℝ :=
    fun 𝔭 ↦ - Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)
  set h : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℝ :=
    fun 𝔭 ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) with hh
  have hxbound : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) < 1 := fun 𝔭 ↦ absNorm_rpow_neg_lt_one K 𝔭.2.1 𝔭.2.2 hs1
  have hxnn : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (0 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := fun 𝔭 ↦ Real.rpow_nonneg (by positivity) _
  have hfnn : ∀ 𝔭, 0 ≤ f 𝔭 := fun 𝔭 ↦ (neg_log_one_sub_sub_le (hxnn 𝔭) (hxbound 𝔭)).1
  have hfle : ∀ 𝔭, f 𝔭 ≤ h 𝔭 := fun 𝔭 ↦ by
    refine (neg_log_one_sub_sub_le (hxnn 𝔭) (hxbound 𝔭)).2.trans_eq ?_
    rw [hh]
    congr 1
    rw [← Real.rpow_natCast ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) 2, ← Real.rpow_mul (by positivity)]
    ring_nf
  have hsummh : Summable h := by
    have hnn : ∀ 𝔭, 0 ≤ h 𝔭 := fun 𝔭 ↦ by
      rw [hh]
      exact div_nonneg (Real.rpow_nonneg (by positivity) _)
        (one_sub_absNorm_rpow_pos K 𝔭.2.1 𝔭.2.2 hs1).le
    refine Summable.of_nonneg_of_le hnn (fun 𝔭 ↦ primeIdealHigherTail_term_le K 𝔭.2.1 𝔭.2.2 hs1)
      ((summable_prime2_absNorm_rpow K one_lt_two).mul_left 2)
  have hsummf : Summable f := Summable.of_nonneg_of_le hfnn hfle hsummh
  rw [abs_of_nonneg (tsum_nonneg hfnn)]
  calc ∑' 𝔭, f 𝔭 ≤ ∑' 𝔭, h 𝔭 := hsummf.tsum_le_tsum hfle hsummh
    _ ≤ C := hs_tail

theorem logDedekindZeta_sub_primeIdealZetaSum_bounded :
    ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ), |Real.log (dedekindZeta K (s : ℂ)).re
      - primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s| ≤ C := by
  obtain ⟨C, hC⟩ := abs_tsum_neg_log_one_sub_sub_rpow_le K
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with s hs_bound hs1
  simp only [mem_Ioi] at hs1
  rwa [log_dedekindZeta_re_eq_tsum_neg_log_one_sub K hs1,
    primeIdealZetaSum_univ_eq_tsum_prime2 K s,
    ← (summable_neg_log_one_sub_absNorm_rpow K hs1).tsum_sub
      (summable_prime2_absNorm_rpow K hs1)]

theorem logDedekindZeta_sub_log_inv_sub_one_bounded :
    ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ),
      |Real.log (dedekindZeta K (s : ℂ)).re - Real.log (1 / (s - 1))| ≤ C := by
  set r := dedekindZeta_residue K
  have hrpos : 0 < r := dedekindZeta_residue_pos K
  have hF : Tendsto (fun s : ℝ ↦ (s - 1) * (dedekindZeta K (s : ℂ)).re)
      (𝓝[>] (1 : ℝ)) (𝓝 r) := by
    refine ((Complex.continuous_re.tendsto _).comp
      (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)).congr fun s ↦ ?_
    rw [Function.comp_apply, show ((s : ℂ) - 1) = ((s - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
  refine ⟨max |Real.log (r / 2)| |Real.log (2 * r)|, ?_⟩
  have hev : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      (s - 1) * (dedekindZeta K (s : ℂ)).re ∈ Ioo (r / 2) (2 * r) :=
    hF.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hev, self_mem_nhdsWithin] with s hF_s hs1
  simp only [mem_Ioi] at hs1
  have hsm1 : (0 : ℝ) < s - 1 := by linarith
  obtain ⟨hlo, hhi⟩ := hF_s
  have hFpos : (0 : ℝ) < (s - 1) * (dedekindZeta K (s : ℂ)).re := by linarith
  have hζpos : (0 : ℝ) < (dedekindZeta K (s : ℂ)).re := (mul_pos_iff_of_pos_left hsm1).mp hFpos
  rw [one_div, Real.log_inv, sub_neg_eq_add,
    ← Real.log_mul hζpos.ne' hsm1.ne', mul_comm]
  exact abs_le_max_abs_abs (Real.log_lt_log (by linarith) hlo).le (Real.log_lt_log hFpos hhi).le

theorem log_minus_bounded_le_primeIdealZetaSum :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      Real.log (1 / (s - 1)) - C
        ≤ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s := by
  obtain ⟨C₁, h₁⟩ := logDedekindZeta_sub_primeIdealZetaSum_bounded K
  obtain ⟨C₂, h₂⟩ := logDedekindZeta_sub_log_inv_sub_one_bounded K
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with s hs₁ hs₂
  linarith [abs_le.mp hs₁, abs_le.mp hs₂]

theorem primeIdealZetaSum_le_log_plus_bounded :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s
        ≤ Real.log (1 / (s - 1)) + C := by
  obtain ⟨C₁, h₁⟩ := logDedekindZeta_sub_primeIdealZetaSum_bounded K
  obtain ⟨C₂, h₂⟩ := logDedekindZeta_sub_log_inv_sub_one_bounded K
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with s hs₁ hs₂
  linarith [abs_le.mp hs₁, abs_le.mp hs₂]

theorem primeIdealZetaSum_univ_tendsto_log :
    Tendsto
      (fun s : ℝ ↦ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s
        / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 1) :=
  tendsto_ratio_one_of_log_pm_bounded
    (primeIdealZetaSum (univ : Set (Ideal (𝓞 K))))
    (primeIdealZetaSum_le_log_plus_bounded K)
    (log_minus_bounded_le_primeIdealZetaSum K)

theorem primeIdealZetaSum_univ_tendsto_atTop :
    Tendsto (primeIdealZetaSum (univ : Set (Ideal (𝓞 K)))) (𝓝[>] 1) atTop := by
  have hL := tendsto_log_one_div_sub_one_atTop
  have hhalf : Tendsto (fun s : ℝ ↦ (1 / 2 : ℝ) * Real.log (1 / (s - 1))) (𝓝[>] 1) atTop :=
    hL.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' _ ?_ hhalf
  filter_upwards [(primeIdealZetaSum_univ_tendsto_log K).eventually
      (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)), hL.eventually_gt_atTop 0] with s hs hpos
  exact ((lt_div_iff₀ hpos).mp (mem_Ioi.mp hs)).le

end Chebotarev
end

section
open NumberField Filter Set
open scoped Topology
namespace WeakDensity436
noncomputable section

abbrev Fibr (K : Type) [Field K] [NumberField K] (p : ℕ) :=
  {I : Ideal (𝓞 K) // I.absNorm=p}

lemma count_homs (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    Nat.card (𝓞 K →+* ZMod p)=Nat.card (Fibr K p) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have sur (f : 𝓞 K →+* ZMod p) : Function.Surjective f := fun x => ⟨(x.val:ℕ),by simp⟩
  let g (f : 𝓞 K →+* ZMod p) : Fibr K p :=
    ⟨RingHom.ker f, (Nat.card_congr (f.quotientKerEquivOfSurjective (sur f)).toEquiv).trans (by simp [Nat.card_eq_fintype_card])⟩
  apply Nat.card_congr (Equiv.ofBijective g ⟨?_,?_⟩)
  · intro f h eq
    have e : RingHom.ker f=RingHom.ker h := congrArg Subtype.val eq
    ext x
    have d : x-((f x).val:ℕ) ∈ RingHom.ker f := by change f _=0; simp
    rw [e] at d
    change h _=0 at d
    simpa using (sub_eq_zero.mp (by simpa only [map_sub,map_natCast,ZMod.natCast_zmod_val] using d)).symm
  · rintro ⟨I,hi⟩
    letI := (Ideal.absNorm_ne_zero_iff I).mp (hi ▸ hp.ne_zero)
    letI := Fintype.ofFinite (𝓞 K ⧸ I)
    let e := ZMod.ringEquivOfPrime (𝓞 K ⧸ I) hp (by rw [←Nat.card_eq_fintype_card]; exact hi)
    refine ⟨e.symm.toRingHom.comp (Ideal.Quotient.mk I),Subtype.ext ?_⟩
    ext x
    change e.symm (Ideal.Quotient.mk I x)=0 ↔ x∈I
    rw [map_eq_zero_iff _ e.symm.injective,Ideal.Quotient.eq_zero_iff_mem]

abbrev Targets (K : Type) [Field K] [NumberField K] (B : ℕ) : Set (Ideal (𝓞 K)) :=
  {I | B < I.absNorm ∧ I.absNorm.Prime}

lemma project {K : Type} [Field K] [NumberField K] (I : Ideal (𝓞 K)) (h : I.IsPrime) (nz : I ≠ ⊥) :
    (I.under ℤ).absNorm.Prime ∧ (I.under ℤ).absNorm ^ I.inertiaDeg ℤ = I.absNorm := by
  letI := h
  letI : NeZero I := ⟨nz⟩
  exact ⟨Nat.absNorm_under_prime I,Ideal.absNorm_pow_inertiaDeg (I.under ℤ) I⟩

lemma fiber_bound {K : Type} [Field K] [NumberField K] (S : Set (Ideal (𝓞 K))) (q : Nat.Primes) :
    let A := {I : Ideal (𝓞 K) // I∈S ∧ I.IsPrime ∧ I ≠ ⊥}
    let g (I : A) : Nat.Primes := ⟨(I.val.under ℤ).absNorm,(project I.val I.2.2.1 I.2.2.2).1⟩
    Finite (g ⁻¹' {q} : Set A) ∧ Nat.card (g ⁻¹' {q} : Set A) ≤ Module.finrank ℚ K := by
  classical
  dsimp only
  let T := Ideal.span ({(q.val:ℤ)} : Set ℤ)
  have tn : T≠⊥ := by simp [T,q.property.ne_zero]
  letI : T.IsMaximal := ((Ideal.span_singleton_prime (by exact_mod_cast q.property.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp q.property)).isMaximal tn
  let U := IsDedekindDomain.primesOverFinset T (𝓞 K)
  let A := {I : Ideal (𝓞 K) // I∈S ∧ I.IsPrime ∧ I ≠ ⊥}
  let g (I : A) : Nat.Primes := ⟨(I.val.under ℤ).absNorm,(project I.val I.2.2.1 I.2.2.2).1⟩
  let j (x : (g ⁻¹' {q} : Set A)) : U := ⟨x.1.1, by
    apply (IsDedekindDomain.mem_primesOverFinset_iff tn _).mpr
    refine ⟨x.1.2.2.1,?_⟩
    have eq : (x.1.1.under ℤ).absNorm = q.val := congrArg Subtype.val (show g x.1=q from x.2)
    rw [Ideal.liesOver_iff,← Int.ideal_span_absNorm_eq_self (x.1.1.under ℤ),eq]⟩
  have ji : Function.Injective j := fun _ _ eq => Subtype.ext (Subtype.ext (congrArg (fun v:U => (v:Ideal (𝓞 K))) eq))
  refine ⟨Finite.of_injective j ji,(Nat.card_le_card_of_injective j ji).trans ?_⟩
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe,U] using
    Ideal.card_primesOverFinset_le_finrank (S := 𝓞 K) (K := ℚ) (L := K) tn

end
end WeakDensity436
namespace Chebotarev
open Set
open scoped ENNReal
theorem tsum_comp_le_card_fibre_mul {β γ : Type*} (g : β → γ) (f : γ → ℝ≥0∞) (d : ℕ)
    (hfin : ∀ y, Finite (g ⁻¹' {y} : Set β)) (hfib : ∀ y, Nat.card (g ⁻¹' {y} : Set β) ≤ d) :
    ∑' b, f (g b) ≤ (d : ℝ≥0∞) * ∑' y, f y := by
  rw [← ENNReal.tsum_fiberwise (fun b ↦ f (g b)) g, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum (fun y ↦ ?_)
  rw [tsum_congr (fun b : (g ⁻¹' {y} : Set β) ↦ by rw [b.2])]
  haveI := hfin y
  letI := Fintype.ofFinite (g ⁻¹' {y} : Set β)
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]
  gcongr
  exact_mod_cast hfib y

/-- **Fibre-counting bound for real-valued sums.** The `ℝ`-valued companion of
`tsum_comp_le_card_fibre_mul`: for nonnegative summable `FA, FK` with `FA b ≤ FK (g b)` and every
fibre `g ⁻¹' {y}` finite of size `≤ d`, the sum `Σ_b FA b` is at most `d · Σ_y FK y`. -/
theorem tsum_real_comp_le_card_fibre_mul {β γ : Type*} (g : β → γ) (FA : β → ℝ)
    (FK : γ → ℝ) (d : ℕ) (hsummA : Summable FA) (hsummK : Summable FK) (hnonnegA : ∀ b, 0 ≤ FA b)
    (hnonnegK : ∀ y, 0 ≤ FK y) (hterm : ∀ b, FA b ≤ FK (g b))
    (hfin : ∀ y, Finite (g ⁻¹' {y} : Set β)) (hfib : ∀ y, Nat.card (g ⁻¹' {y} : Set β) ≤ d) :
    ∑' b, FA b ≤ (d : ℝ) * ∑' y, FK y := by
  have hchain : ∑' b, ENNReal.ofReal (FA b)
      ≤ (d : ℝ≥0∞) * ∑' y, ENNReal.ofReal (FK y) :=
    calc ∑' b, ENNReal.ofReal (FA b) ≤ ∑' b, ENNReal.ofReal (FK (g b)) :=
          ENNReal.tsum_le_tsum fun b ↦ ENNReal.ofReal_le_ofReal (hterm b)
      _ ≤ (d : ℝ≥0∞) * ∑' y, ENNReal.ofReal (FK y) :=
          tsum_comp_le_card_fibre_mul g (ENNReal.ofReal <| FK ·) d hfin hfib
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonnegA hsummA,
    ← ENNReal.ofReal_tsum_of_nonneg hnonnegK hsummK] at hchain
  rw [← ENNReal.toReal_ofReal (tsum_nonneg hnonnegA),
    ← ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg d) (tsum_nonneg hnonnegK)),
    ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hchain
end Chebotarev
open NumberField Filter Set Chebotarev
open scoped Topology
namespace WeakDensity436
noncomputable section

lemma high_tail (K : Type) [Field K] [NumberField K] (B : ℕ) :
    ∃ C : ℝ, ∀ s : ℝ, 1<s → primeIdealZetaSum (Targets K B)ᶜ s ≤ C := by
  classical
  let S := (Targets K B)ᶜ
  let A := {I : Ideal (𝓞 K) // I∈S ∧ I.IsPrime ∧ I ≠ ⊥}
  let g (I:A) : Nat.Primes := ⟨(I.val.under ℤ).absNorm,(project I.val I.2.2.1 I.2.2.2).1⟩
  let w (n:ℕ) : ℝ := (n:ℝ)^(-(2:ℝ))+(if n≤B then 1 else 0)
  have ws : Summable w := (Real.summable_nat_rpow.mpr (by norm_num : -(2:ℝ)< -1)).add (by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_Iic B).subset
    intro n hn
    by_contra h; exact hn (if_neg h))
  have wn (n:ℕ) : 0≤w n := add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by split_ifs <;> norm_num)
  refine ⟨Module.finrank ℚ K * ∑' q:Nat.Primes, w q.val,fun s hs => ?_⟩
  apply Chebotarev.tsum_real_comp_le_card_fibre_mul g _ _ _
    (summable_prime_absNorm_rpow S hs) (ws.comp_injective Subtype.val_injective)
    (fun _ => by positivity) (fun q => wn q.val)
    _ (fun q => (fiber_bound S q).1) (fun q => (fiber_bound S q).2)
  intro I
  let J := I.val
  have primes := (g I).property
  have eq : (g I).val ^ J.inertiaDeg ℤ=J.absNorm := (project J I.2.2.1 I.2.2.2).2
  letI : J.IsPrime := I.2.2.1
  letI : J.LiesOver (J.under ℤ) := Ideal.over_under J
  have fpos := Ideal.inertiaDeg_pos J ℤ
  have lo : (1:ℝ)≤(g I).val := by exact_mod_cast primes.one_le
  have pn : 0 < (g I).val := primes.pos
  have normlo : (g I).val ≤ J.absNorm := by rw [←eq]; exact Nat.le_self_pow (by omega) _
  change (J.absNorm:ℝ)^(-s) ≤ w (g I).val
  by_cases small : (g I).val ≤ B
  · have o : (J.absNorm:ℝ)^(-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast primes.one_le.trans normlo) (by linarith)
    dsimp [w]; rw [if_pos small]; linarith [Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) (g I).val) (-(2:ℝ))]
  · have deg : 2≤J.inertiaDeg ℤ := by
      by_contra hh
      have e : J.inertiaDeg ℤ=1 := by omega
      rw [e,pow_one] at eq
      exact I.2.1 (show B<J.absNorm ∧ J.absNorm.Prime by rw [←eq]; exact ⟨by omega,primes⟩)
    dsimp only [w]; rw [if_neg small,add_zero,←eq,Nat.cast_pow,
      ←Real.rpow_natCast ((g I).val:ℝ) (J.inertiaDeg ℤ),←Real.rpow_mul (by positivity)]
    apply Real.rpow_le_rpow_of_exponent_le lo
    have hh : (2:ℝ)≤J.inertiaDeg ℤ := by exact_mod_cast deg
    nlinarith [mul_le_mul hh hs.le (by norm_num) (by positivity : (0:ℝ)≤J.inertiaDeg ℤ)]

lemma large_comparison (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (B : ℕ)
    (h : ∀ p>B, p.Prime → 2*Nat.card (Fibr E p) ≤ Nat.card (Fibr K p))
    (s : ℝ) (hs : 1<s) :
    2*primeIdealZetaSum (Targets E B) s ≤ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s := by
  classical
  have emb (p : ℕ) (hp : p>B) (pr : p.Prime) : Nonempty ((Bool × Fibr E p) ↪ Fibr K p) := by
    letI : Fintype (Fibr K p) := (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) p).fintype
    letI : Fintype (Fibr E p) := (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 E) p).fintype
    apply Function.Embedding.nonempty_of_card_le
    simpa [Fintype.card_prod,Nat.card_eq_fintype_card] using h p hp pr
  let A := {I : Ideal (𝓞 E) // I∈Targets E B ∧ I.IsPrime ∧ I≠⊥}
  let C := {I : Ideal (𝓞 K) // I∈(univ : Set (Ideal (𝓞 K))) ∧ I.IsPrime ∧ I≠⊥}
  let f (v : Bool × A) : Ideal (𝓞 K) := ((emb v.2.1.absNorm v.2.2.1.1 v.2.2.1.2).some (v.1,⟨v.2.1,rfl⟩)).1
  have eq (v : Bool × A) : (f v).absNorm=v.2.1.absNorm := ((emb _ v.2.2.1.1 v.2.2.1.2).some (v.1,⟨v.2.1,rfl⟩)).2
  let j (v : Bool × A) : C := ⟨f v,mem_univ _, Ideal.isPrime_of_irreducible_absNorm (by rw [eq]; exact v.2.2.1.2),
    fun h => v.2.2.1.2.ne_zero (by rw [←eq v,h,Ideal.absNorm_bot])⟩
  have inject : Function.Injective j := by
    rintro ⟨i,⟨I,hI⟩⟩ ⟨k,⟨J,hJ⟩⟩ ee
    have ee' := congrArg Subtype.val ee
    change f (i,⟨I,hI⟩)=f (k,⟨J,hJ⟩) at ee'
    have n := (eq (i,⟨I,hI⟩)).symm.trans ((congrArg Ideal.absNorm ee').trans (eq (k,⟨J,hJ⟩)))
    have agree {p q:ℕ} (hp : B<p) (pp:p.Prime) (hq:B<q) (pq:q.Prime)
        (a:Bool × Fibr E p) (b:Bool × Fibr E q) (e:p=q)
        (v : ((emb p hp pp).some a).1=((emb q hq pq).some b).1) :
        a.1=b.1 ∧ a.2.1=b.2.1 := by
      subst q
      have same := (emb p hp pp).some.injective (Subtype.ext v)
      cases same
      exact ⟨rfl,rfl⟩
    obtain ⟨ik,ij⟩ := agree hI.1.1 hI.1.2 hJ.1.1 hJ.1.2 (i,⟨I,rfl⟩) (k,⟨J,rfl⟩) n ee'
    exact Prod.ext ik (Subtype.ext ij)
  let w (v:A) := (v.1.absNorm:ℝ)^(-s)
  have summ : Summable w := summable_prime_absNorm_rpow (Targets E B) hs
  have bp : Summable (fun v:Bool × A => w v.2) :=
    (summable_prod_of_nonneg (fun v => Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr
      ⟨fun _ => summ,Summable.of_finite⟩
  have le := bp.tsum_le_tsum_of_inj j inject (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun v => show w v.2 ≤ ((j v).1.absNorm:ℝ)^(-s) by rw [show (j v).1.absNorm=v.2.1.absNorm from eq v])
    (summable_prime_absNorm_rpow univ hs)
  rw [bp.tsum_prod' (fun _ => summ),tsum_fintype,Fintype.sum_bool] at le
  rw [two_mul]
  exact le

theorem compare (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (B : ℕ) :
    ∃ p>B, p.Prime ∧ Nat.card (𝓞 K →+* ZMod p)<2*Nat.card (𝓞 E →+* ZMod p) := by
  classical
  by_contra! nope
  have h (p : ℕ) (hp : p>B) (pr : p.Prime) : 2*Nat.card (Fibr E p) ≤ Nat.card (Fibr K p) := by
    rw [←count_homs E p pr,←count_homs K p pr]
    exact nope p hp pr
  obtain ⟨C,tail⟩ := high_tail E B
  obtain ⟨a,low⟩ := log_minus_bounded_le_primeIdealZetaSum E
  obtain ⟨b,up⟩ := primeIdealZetaSum_le_log_plus_bounded K
  have pos : ∀ᶠ s in 𝓝[>] (1:ℝ), 1<s := self_mem_nhdsWithin
  obtain ⟨s,hs,left,right,big⟩ := (pos.and (low.and (up.and
    (tendsto_log_one_div_sub_one_atTop.eventually_gt_atTop (2*a+2*C+b))))).exists
  have double := large_comparison E K B h s hs
  have add := primeIdealZetaSum_union_of_disjoint (S := Targets E B) (T := (Targets E B)ᶜ) disjoint_compl_right hs
  rw [union_compl_self] at add
  linarith [tail s hs]

end
end WeakDensity436

end

/- The fixed-order and radical constructions adapt the related reductions by @marcusbuffett. -/

/-! Rational reductions of an order are counted by its homomorphisms to the
prime field. If each residue of z above the fixed order were rational,
precomposing by the given automorphism would produce two different rational
reductions of the order generated by z above every rational reduction of the
fixed order. The mean number of rational reductions of a number field is one. -/
namespace FixedOrder436
open NumberField

/-- Degree-one primes in two number fields cannot have a pointwise factor of
two in their splitting counts at every sufficiently large rational prime. -/
def H1 : Prop := ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (B : ℕ),
    ∃ p > B, p.Prime ∧ Nat.card (𝓞 K →+* ZMod p) < 2*Nat.card (𝓞 E →+* ZMod p)

/-- Away from a finite index, an order and the maximal order in its fraction
field have the same reductions to prime fields. -/
def H2 : Prop := ∀ (L : Type) [Field L] [NumberField L] (R : Subalgebra ℤ (𝓞 L)),
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (B : ℕ), ∀ p > B, p.Prime →
      Nonempty ((R →+* ZMod p) ≃ (𝓞 E →+* ZMod p))

lemma finite_hom (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    Finite (𝓞 K →+* ZMod p) := by
  classical
  let b := Module.Free.chooseBasis ℤ (𝓞 K)
  let f (g : 𝓞 K →+* ZMod p) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) := g (b i)
  apply Finite.of_injective f
  intro g h eq
  have lin : g.toIntAlgHom.toLinearMap=h.toIntAlgHom.toLinearMap :=
    b.ext (fun i => congrFun eq i)
  ext x
  exact LinearMap.congr_fun lin x

lemma lift_mod (L : Type) [Field L] [NumberField L] (R : Subalgebra ℤ (𝓞 L))
    (p : ℕ) [Fact p.Prime] (f : R →+* ZMod p) :
    ∃ (F : Type) (_ : Field F) (_ : CharP F p) (φ : 𝓞 L →+* F),
      ∀ r : R, φ r = ZMod.castHom (m := p) dvd_rfl F (f r) := by
  classical
  have sur : Function.Surjective f := fun x => ⟨(x.val:ℕ),by simp⟩
  letI := RingHom.ker_isMaximal_of_surjective f sur
  letI : Algebra.IsIntegral R (𝓞 L) := Algebra.IsIntegral.tower_top (R := ℤ)
  obtain ⟨Q,hQ,hQf⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) (RingHom.ker f)
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R (𝓞 L))]; exact bot_le)
  let F := 𝓞 L ⧸ Q
  letI : Field F := Ideal.Quotient.field Q
  let φ := Ideal.Quotient.mk Q
  have ker (x : R) : φ x = 0 ↔ f x=0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change x ∈ Q.comap (algebraMap R (𝓞 L)) ↔ _
    rw [hQf]; rfl
  have pz : (p:F)=0 := by simpa using (ker (p:R)).mpr (by simp)
  letI : CharP F p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr pz
  refine ⟨F,inferInstance,inferInstance,φ,fun r => ?_⟩
  have diff := (ker (r-((f r).val:ℕ))).mpr (by simp)
  change φ ((r:𝓞 L)-((f r).val:ℕ))=0 at diff
  rw [map_sub,map_natCast,sub_eq_zero] at diff
  rw [diff]
  exact (by simpa only [ZMod.castHom_apply,ZMod.cast_eq_val])

lemma distinguish (L : Type) [Field L] [NumberField L] {x y : 𝓞 L} (h : x ≠ y) :
    ∃ B : ℕ, ∀ p > B, ∀ (F : Type) [Field F] [CharP F p] (φ : 𝓞 L →+* F), φ x ≠ φ y := by
  let I : Ideal (𝓞 L) := Ideal.span {x-y}
  have nz : I.absNorm ≠ 0 := mt Ideal.absNorm_eq_zero_iff.mp (by simpa [I,sub_eq_zero] using h)
  refine ⟨I.absNorm,fun p hp F _ _ φ eq => ?_⟩
  have le : I ≤ RingHom.ker φ := by
    rw [Ideal.span_le,Set.singleton_subset_iff]; change φ (x-y)=0; simp [eq]
  have e := le I.absNorm_mem
  change φ (I.absNorm:𝓞 L)=0 at e
  rw [map_natCast,CharP.cast_eq_zero_iff F p] at e
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero nz) e).not_gt hp

lemma descend_hom {S F : Type} [CommRing S] [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (g : S →+* F) (hg : ∀ x, (g x)^p=g x) :
    ∃ h : S →+* ZMod p, ∀ x, ZMod.castHom (m := p) dvd_rfl F (h x)=g x := by
  let j := ZMod.castHom (m := p) dvd_rfl F
  have mem (x : S) : g x ∈ j.range := by
    have hh := (Subfield.mem_bot_iff_pow_eq_self F p).mpr (hg x)
    rw [← ZMod.fieldRange_castHom_eq_bot p] at hh
    exact hh
  let e := RingEquiv.ofBijective j.rangeRestrict ⟨fun _ _ eq => j.injective (congrArg Subtype.val eq),j.rangeRestrict_surjective⟩
  let h := e.symm.toRingHom.comp (g.codRestrict j.range mem)
  refine ⟨h,fun x => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ((g.codRestrict j.range mem) x))

lemma two_lifts {A F : Type} [CommRing A] [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (σ : A ≃+* A) (z : A)
    (R S : Subalgebra ℤ A) (hR : ∀ x, x∈R ↔ σ x=x)
    (hS : S = Algebra.adjoin ℤ ((R : Set A) ∪ {z})) (f : R →+* ZMod p) (φ : A →+* F)
    (fix : ∀ x : R, φ x=ZMod.castHom (m := p) dvd_rfl F (f x))
    (allz : ∀ g : A →+* F, (∀ x, σ x=x → (g x)^p=g x) → (g z)^p=g z)
    (diff : φ (σ z) ≠ φ z) :
    ∃ g h : S →+* ZMod p, g ≠ h ∧ ∀ x : R, ∀ hx : (x:A)∈S, g ⟨x,hx⟩=f x ∧ h ⟨x,hx⟩=f x := by
  let j := ZMod.castHom (m := p) dvd_rfl F
  have res (ψ : A →+* F) (hh : ∀ x:R, ψ x=j (f x)) : ∀ x, σ x=x → (ψ x)^p=ψ x := by
    intro x e
    have eq := hh ⟨x,(hR x).mpr e⟩
    change ψ x=j _ at eq
    rw [eq,←map_pow,ZMod.pow_card]
  have get (ψ : A →+* F) (hh : ∀ x:R, ψ x=j (f x)) : ∃ g : S →+* ZMod p, ∀ x:S, j (g x)=ψ x := by
    let ψ' := (frobenius F p).comp ψ
    have incl : S ≤ AlgHom.equalizer ψ'.toIntAlgHom ψ.toIntAlgHom := by
      rw [hS,Algebra.adjoin_le_iff]
      intro x hx
      change (ψ x)^p = ψ x
      rcases hx with h|h
      · exact res ψ hh x ((hR x).mp h)
      · simpa using (Set.mem_singleton_iff.mp h ▸ allz ψ (res ψ hh))
    exact descend_hom (ψ.comp S.val.toRingHom) (fun x => incl x.2)
  have twice (x:R) : (φ.comp σ.toRingHom) x=j (f x) := by
    change φ (σ x)=_; rw [(hR x).mp x.2,fix x]
  obtain ⟨g,hg⟩ := get φ fix
  obtain ⟨h,hh⟩ := get (φ.comp σ.toRingHom) twice
  have hz : z ∈ S := hS ▸ Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton _))
  refine ⟨g,h,fun e => diff ((hh ⟨z,hz⟩).symm.trans (e ▸ hg ⟨z,hz⟩)),fun x hx => ?_⟩
  exact ⟨j.injective ((hg ⟨x,hx⟩).trans (fix x)),j.injective ((hh ⟨x,hx⟩).trans (twice x))⟩

theorem main : H1 → H2 → ∀ (L : Type) [Field L] [CharZero L] [NumberField L] [IsGalois ℚ L]
    (σ : (𝓞 L) ≃+* (𝓞 L)) (z : 𝓞 L), σ z ≠ z → ∀ B : ℕ,
    ∃ p > B, p.Prime ∧ ∃ (F : Type) (_ : Field F) (_ : CharP F p) (φ : 𝓞 L →+* F),
      (∀ a : 𝓞 L, σ a = a → (φ a)^p=φ a) ∧ (φ z)^p ≠ φ z := by
  classical
  intro compare maximal L _ _ _ _ σ z hz B
  let R := AlgHom.equalizer σ.toRingHom.toIntAlgHom (AlgHom.id ℤ (𝓞 L))
  let S := Algebra.adjoin ℤ ((R : Set (𝓞 L)) ∪ {z})
  have hR (x : 𝓞 L) : x∈R ↔ σ x=x := Iff.rfl
  have inc : R ≤ S := fun _ h => Algebra.subset_adjoin (Set.mem_union_left _ h)
  obtain ⟨E,_,_,b,hb⟩ := maximal L R
  obtain ⟨K,_,_,c,hc⟩ := maximal L S
  obtain ⟨d,hd⟩ := distinguish L hz
  obtain ⟨p,hp1,hp,counts⟩ := compare E K (max (max b c) (max B d))
  refine ⟨p,by omega,hp,?_⟩
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨r⟩ := hb p (by omega) hp
  obtain ⟨s⟩ := hc p (by omega) hp
  rw [←Nat.card_congr r,←Nat.card_congr s] at counts
  letI := finite_hom K p
  letI : Finite (S →+* ZMod p) := Finite.of_equiv _ s.symm
  by_contra bad
  have no (F : Type) [Field F] [CharP F p] (φ : 𝓞 L →+* F) (h : ∀ x, σ x=x → (φ x)^p=φ x) :
      (φ z)^p=φ z := by by_contra hn; exact bad ⟨F,inferInstance,inferInstance,φ,h,hn⟩
  have lifts (f : R →+* ZMod p) : ∃ g h : S →+* ZMod p, g ≠ h ∧ ∀ x:R, ∀ hx : (x:𝓞 L)∈S, g ⟨x,hx⟩=f x ∧ h ⟨x,hx⟩=f x := by
    obtain ⟨F,_,_,φ,hφ⟩ := lift_mod L R p f
    exact two_lifts σ z R S hR rfl f φ hφ (no F) (hd p (by omega) F φ)
  choose g h ne agree using lifts
  let T (f : R →+* ZMod p) (i : Bool) := if i then g f else h f
  have recover (f : R →+* ZMod p) (i : Bool) (x:R) : T f i ⟨x,inc x.2⟩=f x := by
    cases i <;> simp [T,agree]
  have inj : Function.Injective (fun x : (R →+* ZMod p) × Bool => T x.1 x.2) := by
    rintro ⟨f,i⟩ ⟨f',j⟩ eq
    have ff : f=f' := by
      ext x
      exact (recover f i x).symm.trans ((DFunLike.congr_fun eq ⟨x,inc x.2⟩).trans (recover f' j x))
    subst f'
    cases i <;> cases j
    · rfl
    · exact ((ne f) eq.symm).elim
    · exact ((ne f) eq).elim
    · rfl
  have le := Nat.card_le_card_of_injective _ inj
  rw [Nat.card_prod,show Nat.card Bool=2 by simp [Nat.card_eq_fintype_card]] at le
  omega
end FixedOrder436

open NumberField
open scoped nonZeroDivisors
namespace OrderCompare

lemma restrictions {A C F : Type*} [CommRing A] [CommRing C] [Field F]
    (j : A →+* C) (hj : Function.Injective j) (s : A) (clear : ∀ x:C, ∃ y:A, j y = j s*x)
    (nz : ∀ f:A →+* F, f s ≠ 0) : Nonempty ((A →+* F) ≃ (C →+* F)) := by
  classical
  choose t ht using clear
  have one : t 1=s := hj (by rw [ht,mul_one])
  have zero : t 0=0 := hj (by rw [ht,mul_zero,map_zero])
  have add (x y : C) : t (x+y)=t x+t y := hj (by rw [map_add,ht,ht,ht,mul_add])
  have mul (x y:C) : t (x*y)*s=t x*t y := hj (by simp only [map_mul,ht]; ring)
  let res (g : C →+* F) := g.comp j
  refine ⟨(Equiv.ofBijective res ⟨?_,?_⟩).symm⟩
  · intro g h e
    have a (x:A) : g (j x)=h (j x) := DFunLike.congr_fun e x
    ext x
    apply mul_left_cancel₀ (nz (h.comp j))
    change h (j s)*g x=h (j s)*h x
    rw [←a s,←map_mul,←ht,a,ht,map_mul,a s]
  · intro f
    let g : C →+* F := {
      toFun := fun x => f (t x)/f s
      map_zero' := by simp [zero]
      map_one' := by simp [one,nz f]
      map_add' := fun x y => by rw [add,map_add,add_div]
      map_mul' := fun x y => by
        have eq := congrArg f (mul x y)
        simp only [map_mul] at eq
        field_simp [nz f]
        exact eq }
    refine ⟨g,?_⟩
    ext a
    have ta : t (j a)=s*a := hj (by rw [ht,map_mul])
    change f (t (j a))/f s=f a
    rw [ta,map_mul,mul_div_cancel_left₀ _ (nz f)]

lemma maximal_aux (L : Type) [Field L] [NumberField L] (R : Subalgebra ℤ (𝓞 L))
    (E : Type) [Field E] [NumberField E] [Algebra R E] [IsFractionRing R E] :
    ∃ B : ℕ, ∀ p > B, p.Prime →
      Nonempty ((R →+* ZMod p) ≃ (𝓞 E →+* ZMod p)) := by
  classical
  haveI : Module.Finite ℤ R := Module.Finite.of_injective R.val.toLinearMap Subtype.val_injective
  let j : R →+* 𝓞 E := (algebraMap R E).codRestrict (integralClosure ℤ E)
    (fun x => IsIntegral.map_of_comp_eq (RingHom.id ℤ) (algebraMap R E) (Subsingleton.elim _ _) (Algebra.IsIntegral.isIntegral (R := ℤ) x))
  have hj : Function.Injective j := fun x y e => (IsFractionRing.injective R E) (congrArg (fun q:𝓞 E => (q:E)) e)
  let b := Module.Free.chooseBasis ℤ (𝓞 E)
  obtain ⟨s,hs⟩ := IsLocalization.exist_integer_multiples_of_finite R⁰ (fun i => ((b i):E))
  have finite_clear (x : 𝓞 E) : ∃ y : R, j y=j (s:R)*x := by
    choose d hd using hs
    refine ⟨∑ i, (b.repr x i : ℤ) • d i,?_⟩
    have hb (i) : j (d i) = j (s:R)*b i := RingOfIntegers.ext (by
      change (algebraMap R E) (d i) = (algebraMap R E) (s:R)*(b i:E)
      simpa only [Algebra.smul_def] using hd i)
    rw [map_sum]
    conv_rhs => rw [← b.sum_repr x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul,hb,mul_smul_comm]
  have sn : ((s:R):𝓞 L) ≠ 0 := fun eq => (nonZeroDivisors.coe_ne_zero s) (Subtype.ext eq)
  obtain ⟨B,hB⟩ := FixedOrder436.distinguish L (x := ((s:R):𝓞 L)) (y := 0) sn
  refine ⟨B,fun p hP hp => ?_⟩
  letI : Fact p.Prime := ⟨hp⟩
  apply restrictions j hj s finite_clear
  intro f hf
  obtain ⟨F,_,_,φ,hφ⟩ := FixedOrder436.lift_mod L R p f
  apply hB p hP F φ
  rw [map_zero,hφ (s:R),hf,map_zero]

lemma maximal (L : Type) [Field L] [NumberField L] (R : Subalgebra ℤ (𝓞 L)) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (B : ℕ), ∀ p > B, p.Prime →
      Nonempty ((R →+* ZMod p) ≃ (𝓞 E →+* ZMod p)) := by
  classical
  let E := FractionRing R
  let h : R →+* L := (algebraMap (𝓞 L) L).comp R.val.toRingHom
  have hi : Function.Injective h := (FaithfulSMul.algebraMap_injective (𝓞 L) L).comp Subtype.val_injective
  let u : E →+* L := IsFractionRing.lift hi
  letI : CharZero E := CharZero.of_addMonoidHom (algebraMap R E).toAddMonoidHom ((algebraMap R E).map_one) (IsFractionRing.injective R E)
  letI : FiniteDimensional ℚ E := FiniteDimensional.of_injective u.toRatAlgHom.toLinearMap u.injective
  letI : NumberField E := ⟨⟩
  exact ⟨E,inferInstance,inferInstance,maximal_aux L R E⟩

end OrderCompare
open Polynomial Finset
namespace OrbitResidue

lemma separate {m p : ℕ} (hp : p.Prime) (large : m*m < p)
    {R F : Type} [CommRing R] [Field F] [CharP F p]
    (ψ : R →+* F) (f : Fin m → R →+* F) (point : ∀ x, ∃ i, ψ x=f i x) :
    ∃ i, ∀ x, ψ x=f i x := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  by_contra! bad
  choose a ha using bad
  let P (i : Fin m) : F[X] := ∑ j : Fin m, monomial j.val (ψ (a j)-f i (a j))
  have nz (i : Fin m) : P i ≠ 0 := by
    intro hz
    have eq := congrArg (fun Q : F[X] => Q.coeff i.val) hz
    rw [show (P i).coeff i.val = ψ (a i)-f i (a i) by
      simp [P,finset_sum_coeff,coeff_monomial,Fin.val_inj]] at eq
    exact ha i (sub_eq_zero.mp (by simpa using eq))
  have deg (i : Fin m) : (P i).natDegree ≤ m :=
    natDegree_sum_le_of_forall_le _ _ fun j _ => (natDegree_monomial_le _).trans j.isLt.le
  let U := univ.biUnion fun i : Fin m => (P i).roots.toFinset
  have cu : U.card ≤ m*m := calc
    _ ≤ ∑ i : Fin m, (P i).roots.toFinset.card := card_biUnion_le
    _ ≤ ∑ _i : Fin m, m := sum_le_sum fun i _ =>
      (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (deg i))
    _ = _ := by simp
  let j := ZMod.castHom (m := p) dvd_rfl F
  have sub : univ.image j ⊆ U := by
    intro y hy
    obtain ⟨t,_,rfl⟩ := mem_image.mp hy
    let v : R := ∑ k : Fin m, a k*(t.val : R)^k.val
    obtain ⟨i,hi⟩ := point v
    refine mem_biUnion.mpr ⟨i,mem_univ _,Multiset.mem_toFinset.mpr ((mem_roots (nz i)).mpr ?_)⟩
    have e : j t = (t.val : F) := by
      change ZMod.castHom (m := p) dvd_rfl F t = _
      conv_lhs => rw [← ZMod.natCast_zmod_val t]
      rw [map_natCast]
    rw [Polynomial.IsRoot.def,e]
    simp only [v,map_sum,map_mul,map_pow,map_natCast] at hi
    simpa only [P,eval_finsetSum,eval_monomial,sub_mul,Finset.sum_sub_distrib] using sub_eq_zero.mpr hi
  have low := card_le_card sub
  rw [card_image_of_injective _ j.injective,card_univ,ZMod.card] at low
  omega

lemma iteration {R : Type} [CommRing R] (σ : R ≃+* R) (n : ℕ) (x : R) :
    (σ : R → R)^[n] x = (σ^n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',pow_succ']
    exact congrArg σ ih

lemma conjugate {R F : Type} [CommRing R] [Field F] (σ : R ≃+* R) (m : ℕ)
    (pos : 0 < m) (period : ∀ x : R, (σ : R → R)^[m] x=x)
    (φ ψ : R →+* F) (fix : ∀ x, σ x=x → ψ x=φ x) (x : R) :
    ∃ i : Fin m, ψ x = φ ((σ : R → R)^[i.val] x) := by
  classical
  let g (i : ℕ) : R[X] := X-C ((σ : R → R)^[i] x)
  let P := ∏ i ∈ range m, g i
  have cyc : P.map σ.toRingHom = P := by
    change (Polynomial.mapRingHom σ.toRingHom) (∏ i ∈ range m, g i) = _
    rw [map_prod]
    have step (i : ℕ) : Polynomial.mapRingHom σ.toRingHom (g i) = g (i+1) := by
      simp [g,Function.iterate_succ_apply']
    simp only [step]
    change (∏ i ∈ range m,g (i+1))=∏ i ∈ range m,g i
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
    rw [prod_range_succ,prod_range_succ' g]
    congr 1
    simp [g,period]
  have cfix (i : ℕ) : σ (P.coeff i)=P.coeff i := by
    simpa using congrArg (fun Q : R[X] => Q.coeff i) cyc
  have maps : P.map ψ=P.map φ := by ext i; simp [fix _ (cfix i)]
  have root : (P.map ψ).eval (ψ x)=0 := by
    change (Polynomial.evalRingHom (ψ x)) ((Polynomial.mapRingHom ψ) (∏ i ∈ range m,g i))=0
    rw [map_prod,map_prod]
    apply prod_eq_zero (mem_range.mpr pos : 0 ∈ range m)
    simp [g]
  rw [maps] at root
  change (Polynomial.evalRingHom (ψ x)) ((Polynomial.mapRingHom φ) (∏ i ∈ range m,g i))=0 at root
  rw [map_prod,map_prod,Finset.prod_eq_zero_iff] at root
  obtain ⟨i,hi,eq⟩ := root
  exact ⟨⟨i,mem_range.mp hi⟩,sub_eq_zero.mp (by simpa [g] using eq)⟩

theorem orbit {R : Type} [CommRing R] (σ : R ≃+* R) (m p : ℕ)
    (pos : 0 < m) (period : ∀ x, (σ : R → R)^[m] x=x)
    (large : m*m < p) (hp : p.Prime) (F : Type) [Field F] [CharP F p] (φ : R →+* F)
    (fix : ∀ a, σ a=a → (φ a)^p=φ a) : ∃ t : ℕ, ∀ a, (φ a)^p=φ ((σ : R → R)^[t] a) := by
  letI : Fact p.Prime := ⟨hp⟩
  let ψ := (frobenius F p).comp φ
  let f (i : Fin m) := φ.comp (σ^i.val).toRingHom
  obtain ⟨i,hi⟩ := separate hp large ψ f (fun x => by
    obtain ⟨i,eq⟩ := conjugate σ m pos period φ ψ fix x
    refine ⟨i,?_⟩
    rw [iteration] at eq
    exact eq)
  refine ⟨i,fun x => ?_⟩
  rw [iteration]
  exact hi x

end OrbitResidue
open scoped BigOperators
open scoped BigOperators
namespace PrimeKummer436

lemma prime_independence {k : ℕ} [Fact k.Prime] {I F : Type} [Fintype I] [Field F] [CharZero F] [FiniteDimensional ℚ F]
    (hdeg : Module.finrank ℚ F < k) (p : I → ℕ) (hinj : Function.Injective p) (hp : ∀ i, (p i).Prime)
    (a : I → ZMod k) (x : F) (h : x^k = ∏ i, (p i : F)^(a i).val) : a = 0 := by
  classical
  have hk := (Fact.out : k.Prime)
  let N : ℕ := ∏ i, p i ^ (a i).val
  have eqn : x^k = algebraMap ℚ F (N : ℚ) := by simpa [N] using h
  have eq' := congrArg (Algebra.norm ℚ) eqn
  simp only [map_pow,Algebra.norm_algebraMap] at eq'
  funext i
  haveI : Fact (p i).Prime := ⟨hp i⟩
  have fac : N.factorization (p i) = (a i).val := by
    unfold N
    rw [Nat.factorization_prod_apply (fun j _ => pow_ne_zero _ (hp j).ne_zero)]
    rw [Finset.sum_eq_single i]
    · exact Nat.factorization_pow_self (hp i)
    · intro j _ hj
      rw [(hp j).factorization_pow,Finsupp.single_eq_of_ne (fun he => hj (hinj he.symm))]
    · simp
  have hv := congrArg (padicValRat (p i)) eq'
  simp only [padicValRat.pow,← padicValRat_of_nat] at hv
  rw [← Nat.factorization_def N (hp i),fac] at hv
  have degpos := Module.finrank_pos (R := ℚ) (M := F)
  have av := (a i).val_lt
  have eq0 : (a i).val = 0 := by
    have hv' : (k : ℤ) * padicValRat (p i) (Algebra.norm ℚ x) = (Module.finrank ℚ F : ℤ) * ((a i).val : ℤ) := hv
    have hd : (k : ℤ) ∣ (Module.finrank ℚ F : ℤ) * ((a i).val : ℤ) := ⟨_,hv'.symm⟩
    have hdN : k ∣ Module.finrank ℚ F * (a i).val := by exact_mod_cast hd
    rcases hk.dvd_mul.mp hdN with d|d
    · exact False.elim (hdeg.not_ge (Nat.le_of_dvd degpos d))
    · by_contra nz
      exact av.not_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero nz) d)
  exact ZMod.val_injective k (by simpa using eq0)

lemma prescribe {k : ℕ} [Fact k.Prime] {I F E : Type} [Fintype I] [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (z : F) (hz : IsPrimitiveRoot z k)
    (b : I → F) (r : I → E) (hr : ∀ i, (r i)^k = algebraMap F E (b i)) (hne : ∀ i, r i ≠ 0)
    (hind : ∀ (a : I → ZMod k) (x : F), x^k = ∏ i, (b i)^(a i).val → a=0)
    (v : I → ZMod k) : ∃ σ : E ≃ₐ[F] E, ∀ i, σ (r i) = r i * (algebraMap F E z)^(v i).val := by
  classical
  have hk := (Fact.out : k.Prime)
  let u := algebraMap F E z
  have hu : IsPrimitiveRoot u k := hz.map_of_injective (algebraMap F E).injective
  have fixed (σ : E ≃ₐ[F] E) : σ u = u := σ.commutes z
  let S : AddSubmonoid (I → ZMod k) := {
    carrier := {a | ∃ σ : E ≃ₐ[F] E, ∀ i, σ (r i) = r i * u^(a i).val}
    zero_mem' := ⟨AlgEquiv.refl,fun i => by simp⟩
    add_mem' := by
      rintro a b ⟨σ,hσ⟩ ⟨τ,hτ⟩
      refine ⟨τ.trans σ,fun i => ?_⟩
      simp only [AlgEquiv.trans_apply,hτ,map_mul,map_pow,hσ,fixed,Pi.add_apply,ZMod.val_add]
      have cyc (n : ℕ) : u^(n%k) = u^n := hu.eq_orderOf ▸ pow_mod_orderOf u n
      rw [cyc,pow_add,mul_assoc] }
  let W : Submodule (ZMod k) (I → ZMod k) := {
    S with
    smul_mem' := fun c a ha => by
      change c • a ∈ S
      have h := S.nsmul_mem ha c.val
      simpa only [← Nat.cast_smul_eq_nsmul (ZMod k),ZMod.natCast_zmod_val] using h }
  suffices W = ⊤ from (show v ∈ W by rw [this]; trivial)
  by_contra hproper
  obtain ⟨g,hg,hker⟩ := W.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hproper)
  let a (i : I) := g (Pi.single i 1)
  have repr (t : I → ZMod k) : g t = ∑ i, t i * a i := by
    have eqv : t = ∑ i, t i • Pi.single i (1 : ZMod k) := by
      funext j
      simp [Finset.sum_apply,Pi.single_apply,ite_mul,mul_ite]
    conv_lhs => rw [eqv]
    simp [a]
  let w := ∏ i, (r i)^(a i).val
  have invari (σ : E ≃ₐ[F] E) : σ w = w := by
    have character (i : I) : ∃ c : ZMod k, σ (r i) = r i*u^c.val := by
      have root : (σ (r i)/r i)^k = 1 := by
        rw [div_pow,← map_pow,hr,σ.commutes,div_self]
        exact (hr i ▸ pow_ne_zero k (hne i))
      obtain ⟨j,hj,he⟩ := hu.eq_pow_of_pow_eq_one root
      refine ⟨j,?_⟩
      rw [ZMod.val_natCast,Nat.mod_eq_of_lt hj]
      exact (div_eq_iff (hne i)).mp he.symm |>.trans (mul_comm ..)
    choose c hc using character
    have hcW : c ∈ W := ⟨σ,hc⟩
    have eqz : ∑ i, c i * a i = 0 := (repr c).symm.trans (hker hcW)
    have hd : k ∣ ∑ i, (c i).val * (a i).val := (ZMod.natCast_eq_zero_iff ..).mp (by simpa using eqz)
    change σ (∏ i, (r i)^(a i).val) = _
    simp only [map_prod,map_pow,hc,mul_pow,Finset.prod_mul_distrib,← pow_mul,Finset.prod_pow_eq_pow_sum]
    rw [hu.pow_eq_one_iff_dvd _ |>.mpr hd,mul_one]
  obtain ⟨x,hx⟩ := (IsGalois.mem_range_algebraMap_iff_fixed w).mpr invari
  have hx3 : x^k = ∏ i, b i ^ (a i).val := (algebraMap F E).injective (by
    rw [map_pow,hx,map_prod]
    change (∏ i, (r i)^(a i).val)^k = _
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul,Nat.mul_comm,pow_mul,hr,map_pow])
  have zero := hind a x hx3
  apply hg
  apply LinearMap.ext
  intro t
  simp [repr t,zero]

end PrimeKummer436
open Polynomial NumberField
open scoped IntermediateField
namespace PrimeKummer436

lemma lift_roots (k : ℕ) (hk : k.Prime) {I : Type} [Fintype I] (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (v : I → ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : CharZero L) (_ : NumberField L) (_ : IsGalois ℚ L)
      (σ : (𝓞 L) ≃+* (𝓞 L)) (u : 𝓞 L), IsPrimitiveRoot u k ∧ σ u=u ∧ (∃ m : ℕ, 0 < m ∧ ∀ x, (σ : 𝓞 L → 𝓞 L)^[m] x = x) ∧
      ∀ i, ∃ r : 𝓞 L, r^k = p i ∧ σ r=r*u^(v i) := by
  classical
  letI : Fact k.Prime := ⟨hk⟩
  let g (i : I) : ℚ[X] := X^k - C (p i : ℚ)
  let P := cyclotomic k ℚ * ∏ i, g i
  let L := P.SplittingField
  letI : Polynomial.IsSplittingField ℚ L P := Polynomial.IsSplittingField.splittingField P
  letI : NumberField L := ⟨⟩
  letI : IsGalois ℚ L := isGalois_iff.mpr ⟨inferInstance,Polynomial.SplittingField.instNormal P⟩
  have pg (i : I) : (g i).natDegree = k := natDegree_X_pow_sub_C
  have neP : P ≠ 0 := mul_ne_zero (cyclotomic_ne_zero k ℚ) (Finset.prod_ne_zero_iff.mpr
    (fun i _ h => by have := pg i; simp [h] at this; exact hk.ne_zero this.symm))
  have root (f : ℚ[X]) (hf : f ∣ P) (hd : 0 < f.natDegree) : ∃ y : L, f.aeval y = 0 := by
    let j := algebraMap ℚ L
    have h := (IsSplittingField.splits L P).of_dvd (map_ne_zero (f := j) neP)
      (map_dvd (mapRingHom j) hf)
    have hd0 : (f.map j).natDegree ≠ 0 := by rw [natDegree_map]; exact hd.ne'
    obtain ⟨y,hy⟩ := h.exists_eval_eq_zero (degree_ne_of_natDegree_ne (n := 0) hd0)
    refine ⟨y,?_⟩
    rw [aeval_def,eval₂_eq_eval_map]
    exact hy
  obtain ⟨u,hu⟩ := root (cyclotomic k ℚ) (dvd_mul_right ..) (by rw [natDegree_cyclotomic]; exact Nat.totient_pos.mpr hk.pos)
  have prim : IsPrimitiveRoot u k := by
    apply isRoot_cyclotomic_iff.mp
    simpa [Polynomial.IsRoot.def,aeval_def,eval₂_eq_eval_map] using hu
  have each (i : I) : ∃ r : L, r^k = p i := by
    obtain ⟨r,hr⟩ := root (g i) (dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) (dvd_mul_left ..))
      (by rw [pg]; exact hk.pos)
    exact ⟨r,by simpa [g,sub_eq_zero] using hr⟩
  choose r hr using each
  let F : IntermediateField ℚ L := ℚ⟮u⟯
  let u' : F := ⟨u,IntermediateField.mem_adjoin_simple_self ℚ u⟩
  have hu' : IsPrimitiveRoot u' k := prim.of_map_of_injective (f := F.subtype) Subtype.val_injective
  have deg : Module.finrank ℚ F < k := by
    rw [show Module.finrank ℚ F = (minpoly ℚ u).natDegree from IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ u),
      ← cyclotomic_eq_minpoly_rat prim hk.pos,natDegree_cyclotomic]
    exact Nat.totient_lt k hk.one_lt
  have rn (i : I) : r i ≠ 0 := by
    intro hz
    have h := hr i
    rw [hz,zero_pow hk.ne_zero] at h
    exact (Nat.cast_ne_zero.mpr (hp i).ne_zero) h.symm
  obtain ⟨σ,hσ⟩ := prescribe u' hu' (fun i => (p i : F)) r (fun i => by simpa using hr i) rn
    (prime_independence deg p hinj hp) (fun i => (v i : ZMod k))
  let τ := RingOfIntegers.mapRingEquiv σ.toRingEquiv
  let U : 𝓞 L := ⟨u,prim.isIntegral hk.pos⟩
  refine ⟨L,inferInstance,inferInstance,inferInstance,inferInstance,τ,U,?_,?_,?_,?_⟩
  · exact prim.of_map_of_injective (f := algebraMap (𝓞 L) L) (FaithfulSMul.algebraMap_injective (𝓞 L) L)
  · exact Subtype.ext (σ.commutes u')
  · refine ⟨orderOf σ,orderOf_pos _,fun x => Subtype.ext ?_⟩
    have it (j : ℕ) : (((τ : 𝓞 L → 𝓞 L)^[j] x : 𝓞 L) : L) = (σ^j) (x : L) := by
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [Function.iterate_succ_apply',pow_succ']
        exact congrArg σ ih
    exact (it _).trans (by rw [pow_orderOf_eq_one]; rfl)
  · intro i
    have integral : IsIntegral ℤ (r i) := IsIntegral.of_pow hk.pos
      ((hr i).symm ▸ (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ L (p i : ℤ))))
    refine ⟨⟨r i,integral⟩,Subtype.ext (hr i),?_⟩
    apply Subtype.ext
    change σ (r i) = r i*u^(v i)
    have e := hσ i
    change σ (r i) = r i*u^((v i : ZMod k).val) at e
    simpa only [ZMod.val_natCast,prim.eq_orderOf,pow_mod_orderOf] using e

end PrimeKummer436

open NumberField
lemma iterate_radical {R : Type} [CommRing R] (σ : R ≃+* R) (u : R) (hu : σ u=u)
    (r : R) (k : ℕ) (hr : σ r=r*u^k) (t : ℕ) :
    (σ : R → R)^[t] r=r*(u^t)^k := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih,map_mul,map_pow,map_pow,hu,hr,pow_succ,mul_pow]
    ring

lemma descend {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [CharP F p]
    (y : F) (hy : y^p=y) : ∃ z : ZMod p, ZMod.castHom (m := p) dvd_rfl F z = y := by
  have h := (Subfield.mem_bot_iff_pow_eq_self F p).mpr hy
  rw [← ZMod.fieldRange_castHom_eq_bot p] at h
  exact h

theorem prescribe_prime (k : ℕ) (hk : k.Prime) (v : ℕ → ℕ) (M B : ℕ) :
    ∃ p>B, p.Prime ∧ k ∣ p-1 ∧ ∃ u:ZMod p, IsPrimitiveRoot u k ∧
      ∀ q:ℕ, q.Prime → q≤M → (q:ZMod p)^((p-1)/k)=u^(v q) := by
  classical
  obtain ⟨Q,hL,hQ⟩ := Nat.exists_infinite_primes (M+1)
  let w (q:ℕ) : ℕ := if q=Q then 1 else v q
  let T := (Finset.range (Q+1)).filter Nat.Prime
  obtain ⟨L,_,_,_,_,σ,u,hu,hs,⟨m,hm,hit⟩,roots⟩ := PrimeKummer436.lift_roots k hk
    (fun i : T => i.val) (fun i => (Finset.mem_filter.mp i.property).2) Subtype.val_injective (fun i => w i.val)
  have haveRoot (q : ℕ) (hq : q.Prime) (h : q≤Q) :
      ∃ r : 𝓞 L, r^k=q ∧ σ r=r*u^(w q) :=
    roots ⟨q,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hq⟩⟩
  obtain ⟨r0,r5,rs⟩ := haveRoot Q hQ le_rfl
  have rne : r0≠0 := by intro he; rw [he,zero_pow hk.ne_zero] at r5; exact (Nat.cast_ne_zero.mpr hQ.ne_zero) r5.symm
  have w2 : w Q=1 := by simp [w]
  rw [w2,pow_one] at rs
  have moved : σ r0≠r0 := by
    intro he
    have u1 : u=1 := mul_left_cancel₀ rne (rs.symm.trans (he.trans (mul_one r0).symm))
    exact hu.ne_one hk.one_lt u1
  obtain ⟨p,hpB,hp,F,_,_,φ,fixed,moves⟩ := FixedOrder436.main WeakDensity436.compare OrderCompare.maximal L σ r0 moved (max (max B Q) (m*m))
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t,hF⟩ := OrbitResidue.orbit σ m p hm hit (by omega) hp F φ fixed
  let j := ZMod.castHom (m := p) dvd_rfl F
  obtain ⟨z,hz⟩ := descend (φ u) (fixed u hs)
  change j z=φ u at hz
  have z5 : z^k=1 := j.injective (by simpa only [map_pow,hz,map_one] using congrArg φ hu.pow_eq_one)
  have wt : z^t≠1 := by
    intro he
    apply moves
    rw [hF,iterate_radical σ u hs r0 1 (by simpa using rs) t,pow_one,map_mul,map_pow,←hz,←map_pow,he,map_one,mul_one]
  have zt5 : (z^t)^k=1 := by rw [←pow_mul,Nat.mul_comm,pow_mul,z5,one_pow]
  have prim : IsPrimitiveRoot (z^t) k := isPrimitiveRoot_of_mem_nthRootsFinset hk
    ((Polynomial.mem_nthRootsFinset hk.pos 1).mpr zt5) wt
  have zne : z^t ≠ 0 := by intro he; simp [he,hk.ne_zero] at zt5
  have pd := prim.dvd_of_pow_eq_one (p-1) (ZMod.pow_card_sub_one_eq_one zne)
  refine ⟨p,by omega,hp,pd,z^t,prim,fun q hq hM => ?_⟩
  obtain ⟨r,rc,rσ⟩ := haveRoot q hq (by omega)
  have ec : (φ r)^k = (q : F) := by simpa only [map_pow,map_natCast] using congrArg φ rc
  have en : (q : ZMod p) ≠ 0 := by
    intro he
    have := Nat.le_of_dvd hq.pos ((ZMod.natCast_eq_zero_iff _ _).mp he)
    omega
  have nz : φ r ≠ 0 := by
    intro er
    apply en
    apply j.injective
    simpa [er,hk.ne_zero] using ec.symm
  have ep : (φ r)^(p-1) = ((φ u)^t)^(w q) := by
    apply mul_left_cancel₀ nz
    calc
      φ r*(φ r)^(p-1) = (φ r)^p := by rw [←pow_succ',Nat.sub_add_cancel hp.pos]
      _ = φ ((σ : 𝓞 L → 𝓞 L)^[t] r) := hF r
      _ = _ := by rw [iterate_radical σ u hs r (w q) rσ t,map_mul,map_pow,map_pow]
  apply j.injective
  simp only [map_pow,map_natCast,hz,← ec,← pow_mul,Nat.mul_div_cancel' pd,ep]
  all_goals simp [w,show q≠Q by omega]


theorem OMA.CubicTriples.realizePattern : OMA.R_Erdos436_erdos_436_variants_three_three_R1.H2 := prescribe_prime 3 (by decide)

theorem OMA.solution : type_of% @Erdos436.erdos_436.variants.three_three :=
  OMA.R_Erdos436_erdos_436_variants_three_three_R1.main
    OMA.CubicTriples.searchBound OMA.CubicTriples.realizePattern
