import FormalConjectures.OEIS.«113258»
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Matrix
section
/-
# Partial results on OEIS A113258

The registered problem asks whether any term after the fourth is a perfect power.
The principal theorem, `exponent_factors_ge_index`, proves that any prime factor of
the exponent in such a representation must be at least the index. Terms five through
eight are ruled out for all exponents.
-/

namespace OeisA113258

/- For n at least three, only the first two summands contribute modulo three. -/
end OeisA113258


namespace FactorialSeries

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def partialSum (n : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => partialSum n k + (Nat.factorial (k+1)) ^ (Nat.factorial (n-k))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def term (n : Nat) := partialSum n n

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def summand (n i : Nat) := (Nat.factorial (i+1))^(Nat.factorial (n-i))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem facAtLeastTwo {k : Nat} (hk : 2 ≤ k) : 2 ≤ Nat.factorial k := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  change 2 ≤ (t+1)*Nat.factorial t
  exact Nat.le_trans hk (Nat.le_mul_of_pos_right _ (Nat.factorial_pos _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nextLeFac {k : Nat} (hk : 3 ≤ k) : k+1 ≤ Nat.factorial k := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have := Nat.mul_le_mul_left (t+1) (facAtLeastTwo (k := t) (by omega))
  change t+1+1 ≤ (t+1)*Nat.factorial t
  omega

/- After the third summand, each exponent shrinks fast enough to offset its larger base. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem summand_le_prev {n i : Nat} (hi : 2 ≤ i) (hin : i+1 < n) :
    summand n (i+1) ≤ summand n i := by
  have b := nextLeFac (k:=i+1) (by omega)
  have hsq : Nat.factorial (i+2) ≤ Nat.factorial (i+1)^2 := by
    change (i+2)*Nat.factorial (i+1) ≤ Nat.factorial (i+1)^2
    rw [Nat.pow_two]
    exact Nat.mul_le_mul_right _ b
  have hbase := Nat.le_trans hsq
    (Nat.pow_le_pow_right (Nat.factorial_pos (i+1)) (by omega : 2 ≤ n-i))
  have hpow := Nat.pow_le_pow_left hbase (Nat.factorial (n-(i+1)))
  change Nat.factorial (i+2)^Nat.factorial (n-(i+1)) ≤ Nat.factorial (i+1)^Nat.factorial (n-i)
  rw [← Nat.pow_mul] at hpow
  have hfac : Nat.factorial (n-i) = (n-i)*Nat.factorial (n-(i+1)) := by
    conv => lhs; rw [show n-i = (n-(i+1))+1 by omega]
    change ((n-(i+1))+1)*_ = (n-i)*_
    rw [show (n-(i+1))+1 = n-i by omega]
  rwa [hfac]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem summand_le_third (n t : Nat) (h : t+2<n) : summand n (t+2) ≤ 6^Nat.factorial (n-2) := by
  induction t with
  | zero => exact Nat.le_refl _
  | succ t ih => exact Nat.le_trans (summand_le_prev (i:=t+2) (by omega) (by omega)) (ih (by omega))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sum_bounds (n t : Nat) (h : t+2≤n) :
    (1 + 2^Nat.factorial (n-1) ≤ partialSum n (t+2)) ∧
    (partialSum n (t+2) ≤ 1 + 2^Nat.factorial (n-1) + t*6^Nat.factorial (n-2)) := by
  induction t with
  | zero =>
    change (1+2^Nat.factorial (n-1) ≤ 0+1^Nat.factorial (n-0)+2^Nat.factorial (n-1)) ∧ _
    simp [partialSum, Nat.factorial]
  | succ t ih =>
    have ⟨hl, hu⟩ := ih (by omega)
    have hs := summand_le_third n t (by omega)
    change (1 + 2^Nat.factorial (n-1) ≤ partialSum n (t+2) + summand n (t+2)) ∧
      partialSum n (t+2) + summand n (t+2) ≤ 1 + 2^Nat.factorial (n-1) + (t+1)*6^Nat.factorial (n-2)
    rw [Nat.add_mul, Nat.one_mul]
    omega

/- The second summand dominates, and all other summands fit inside a gap between powers. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gap_bounds {n : Nat} (hn : 9 ≤ n) :
    2^Nat.factorial (n-1) < term n ∧ term n < 2^Nat.factorial (n-1) + 2^(4*Nat.factorial (n-2)) := by
  obtain ⟨hl,hu⟩ := sum_bounds n (n-2) (by omega)
  rw [show n-2+2 = n by omega] at hl hu
  let E := Nat.factorial (n-2)
  have hE : n-1 ≤ E := by
    have := nextLeFac (k:=n-2) (by omega)
    dsimp [E]; omega
  have hg : n-1 < 2^E := Nat.lt_of_le_of_lt hE (Nat.lt_pow_self (by decide))
  have h6 : 6^E ≤ 8^E := Nat.pow_le_pow_left (by decide) E
  have hpos := Nat.one_le_pow E 8 (by decide)
  have hle := Nat.mul_le_mul_left (n-2) h6
  have hlarger := Nat.mul_lt_mul_of_pos_right hg (by omega : 0<8^E)
  have hsub : n-1 = (n-2)+1 := by omega
  rw [hsub, Nat.add_mul, Nat.one_mul] at hlarger
  have hprod : 2^E * 8^E = 2^(4*E) := by
    rw [show (8:Nat)=2^3 by decide, ← Nat.pow_mul, ← Nat.pow_add]
    congr 1; omega
  rw [hprod] at hlarger
  change 2 ^ Nat.factorial (n-1) < partialSum n n ∧ partialSum n n < 2 ^ Nat.factorial (n-1) + 2^(4*E)
  change partialSum n n ≤ 1+2^Nat.factorial (n-1)+(n-2)*6^E at hu
  omega

/- The leading term is an e-th power because e divides (n-1)!, and the next e-th power is too large. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ne_small_power {n e : Nat} (hn : 9 ≤ n) (he : 2 ≤ e) (hen : e < n) (b : Nat) :
    term n ≠ b^e := by
  obtain ⟨lo,hi⟩ := gap_bounds hn
  obtain ⟨j,hj⟩ := Nat.dvd_factorial (by omega : 0 < e) (by omega : e ≤ n - 1)
  let X := 2^j
  have hX : X^e = 2^Nat.factorial (n-1) := by dsimp [X]; rw [← Nat.pow_mul,hj,Nat.mul_comm j e]
  intro heq
  rw [heq, ← hX] at lo
  have hXb := (Nat.pow_lt_pow_iff_left (by omega : e≠0)).mp lo
  have epos : 0 < e-1 := by omega
  have hj_le : j ≤ j*(e-1) := Nat.le_mul_of_pos_right j epos
  have hprod : j*(e-1)+j = Nat.factorial (n-1) := by
    rw [← Nat.mul_succ,show (e-1).succ=e by omega,Nat.mul_comm,hj]
  have big : 8*Nat.factorial (n-2) ≤ Nat.factorial (n-1) := by
    have hfac : Nat.factorial (n-1)=(n-1)*Nat.factorial (n-2) := by
      conv => lhs; rw [show n-1=(n-2)+1 by omega]
      change ((n-2)+1)*_=(n-1)*_
      rw [show (n-2)+1=n-1 by omega]
    rw [hfac]; exact Nat.mul_le_mul_right _ (by omega)
  have hgrow := Nat.pow_le_pow_right (n:=2) (by decide) (show 4*Nat.factorial (n-2) ≤ j*(e-1) by omega)
  change 2^(4*Nat.factorial (n-2)) ≤ 2^(j*(e-1)) at hgrow
  rw [Nat.pow_mul 2 j (e-1)] at hgrow
  change 2^(4*Nat.factorial (n-2)) ≤ X^(e-1) at hgrow
  have hgap : X^e + X^(e-1) ≤ (X+1)^e := by
    have hmon := Nat.mul_le_mul_right (X+1) (Nat.pow_le_pow_left (Nat.le_succ X) (e-1))
    rw [Nat.mul_add, Nat.mul_one] at hmon
    have cut (t : Nat) : t^(e-1)*t = t^e := by
      rw [← Nat.pow_succ,show (e-1).succ=e by omega]
    rwa [cut X, cut (X+1)] at hmon
  have hlast := Nat.pow_le_pow_left hXb e
  change (X+1)^e ≤ b^e at hlast
  rw [← hX, heq] at hi
  omega


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem partialSum_eq (n t : ℕ) :
    partialSum n t = ∑ i ∈ Finset.range t, (i+1).factorial ^ (n-i).factorial := by
  induction t with
  | zero => simp [partialSum]
  | succ t ih => rw [partialSum, Finset.sum_range_succ, ih]

end FactorialSeries

namespace OeisA113258

/- For all n ≥ 9, the sequence avoids every nontrivial e-th power for e < n. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ne_power_of_exponent_lt {n e : ℕ} (hn : 9 ≤ n) (he : 2 ≤ e) (hen : e < n) (b : ℕ) :
    a n ≠ b^e := by
  simpa only [FactorialSeries.term, FactorialSeries.partialSum_eq, a] using
    FactorialSeries.ne_small_power hn he hen b

end OeisA113258

namespace OeisA113258

/- A prime dividing a number exactly once certifies that it is not a nontrivial power. -/
private theorem FactorialPowers_not_power_of_single_prime_factor {m p b e : ℕ} (hp : p.Prime)
    (hd : p ∣ m) (hs : ¬ p^2 ∣ m) (he : 2 ≤ e) : m ≠ b^e := by
  rintro rfl
  exact hs (pow_dvd_pow_of_dvd_of_le (hp.dvd_of_dvd_pow hd) he)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ne_power_five_to_eight {n b e : ℕ} (lo : 5 ≤ n) (hi : n ≤ 8) (he : 2 ≤ e) :
    a n ≠ b^e := by
  have hs : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
  rcases hs with rfl | rfl | rfl | rfl
  · apply FactorialPowers_not_power_of_single_prime_factor (p:=23) (by decide) _ _ he <;> decide +kernel
  · apply FactorialPowers_not_power_of_single_prime_factor (p:=661) (by decide) _ _ he <;> decide +kernel
  · apply FactorialPowers_not_power_of_single_prime_factor (p:=13) (by decide) _ _ he <;> decide +kernel
  · apply FactorialPowers_not_power_of_single_prime_factor (p:=733) (by decide) _ _ he <;> decide +kernel

/- Any nontrivial power after term four has prime factors of its exponent at least n. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem exponent_factors_ge_index {n b e p : ℕ} (hn : 4 < n) (hp : p.Prime) (hd : p ∣ e)
    (he : 2 ≤ e) (ht : a n = b^e) : n ≤ p := by
  by_contra h
  by_cases hs : n ≤ 8
  · exact (ne_power_five_to_eight hn hs he) ht
  obtain ⟨k, hk⟩ := hd
  apply ne_power_of_exponent_lt (by omega : 9 ≤ n) hp.two_le (by omega : p < n) (b^k)
  rw [ht, hk, Nat.mul_comm p k, Nat.pow_mul]

end OeisA113258


namespace OeisA113258

/- A single modular witness excludes all p-th powers with the same residue. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem exclude_power_by_witness {q p t : ℕ} (hq : q.Prime) (hpq : p ∣ q - 1)
    (ht : (t : ZMod q) ≠ 0) (hw : (t : ZMod q) ^ ((q - 1) / p) ≠ 1)
    (b : ℕ) : t ≠ b ^ p := by
  intro heq
  let _ : Fact q.Prime := ⟨hq⟩
  by_cases hp0 : p = 0
  · subst p
    simp at hw
  have hcast : (t : ZMod q) = (b : ZMod q)^p := by rw [heq, Nat.cast_pow]
  have hb : (b : ZMod q) ≠ 0 := by
    intro h
    apply ht
    rw [hcast, h, zero_pow hp0]
  apply hw
  rw [hcast, ← pow_mul, Nat.mul_comm p, Nat.div_mul_cancel hpq]
  exact ZMod.pow_card_sub_one_eq_one hb

/- The exponent bound established in the written argument using Laurent's Corollary 2. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def AnalyticCutoff : Prop :=
  ∀ n p b : ℕ, 9 ≤ n → p.Prime → a n = b^p → p < 6000 ∧ (p < 3000 ∨ n ≤ 100)

/- The finite modular certificate checked by the two companion programs. -/
end OeisA113258
end




section
namespace OeisA113258.PackedCompute

/- Bounded local exponents use natural-number powers directly. Larger exponents split in base 8. -/
def powerAux (m b : Nat) : Nat → Nat → Nat
  | 0,e => b^e % m
  | k+1,e =>
    if e < 8 then b^e % m else
      let t := powerAux m b k (e/8)
      ((t^8 % m) * (b^(e%8) % m)) % m

def power (m b e : Nat) : Nat :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.pow b (Nat.div e 16)) m) 16)
    (Nat.pow b (Nat.mod e 16))) m

def update (m : Nat) : Nat → List Nat → List Nat
  | _,[] => []
  | j,b::bs => power m b j :: update m (j+1) bs

/- From the terms and n! at n, produce their new values at n+1. -/
def step (m nextN : Nat) (st : Nat × List Nat) : Nat × List Nat :=
  let factorial := st.1 * nextN % m
  (factorial, factorial :: update m 2 st.2)

def state (m : Nat) : Nat → Nat × List Nat
  | 0 => (1 % m, [])
  | n+1 => step m (n+1) (state m n)

/- Check a whole interval using the triangular recurrence exactly once per row. -/
def replay (m : Nat) : Nat → Nat × List Nat → List Nat → Bool
  | _, _, [] => true
  | n, st, r::rs =>
    let next := step m (n+1) st
    next.2.sum % m == r && replay m (n+1) next rs

end OeisA113258.PackedCompute
end

section
namespace OeisA113258.BookCheck

abbrev Book := List (Nat × List Nat)

def goodResidue (p r q : Nat) : Bool :=
  let t := r % q
  decide (t ≠ 0) && decide (PackedCompute.power q t ((q-1)/p) ≠ 1)

def cells (p : Nat) (qs : List Nat) : Nat → List Nat → Bool
  | _, [] => true
  | n, r::rs =>
    (decide (n < 9 ∨ p < n) || qs.any (goodResidue p r)) && cells p qs (n+1) rs

def checked (start : Nat) (rs : List Nat) (book : Book) : Bool :=
  book.all (fun entry => cells entry.1 entry.2 start rs)

end OeisA113258.BookCheck

namespace OeisA113258.BookCheck
theorem checked_append (n : Nat) (rs : List Nat) (b c : Book) :
    checked n rs (b++c) = (checked n rs b && checked n rs c) := by
  simp [checked]
end OeisA113258.BookCheck
end

section
namespace OeisA113258.BookCheck

/- Small, executable primality test for the prime moduli and exponent keys. -/
def primeTrial (q : Nat) : Bool :=
  decide (2 ≤ q) && (List.range (q.sqrt+1)).all (fun d => decide (d < 2 ∨ q%d ≠ 0))

/- Prime exponent keys in the half-open interval [lo, hi). -/
def primeKeys (lo hi : Nat) : List Nat :=
  (List.range' lo (hi-lo)).filter primeTrial

/- Arithmetic conditions on the entries of a packed witness table. -/
def fastValidBook (M : Nat) (book : Book) : Bool :=
  book.all (fun e => e.2.all (fun q => primeTrial q && decide (e.1 ∣ q-1 ∧ q ∣ M)))

end OeisA113258.BookCheck
end

section
/- Soundness of the packed residue-table verifier. -/

namespace OeisA113258.BookCheck

/- Check each modulus for primality, exponent compatibility and divisibility of
the common modulus used to compute all residues at once. -/
def validBook (M : ℕ) (book : Book) : Bool :=
  book.all (fun e => e.2.all (fun q => decide (q.Prime ∧ e.1 ∣ q-1 ∧ q ∣ M)))

theorem validBook_entry {M : ℕ} {book : Book} (h : validBook M book = true)
    {e : ℕ × List ℕ} (he : e ∈ book) {q : ℕ} (hq : q ∈ e.2) :
    q.Prime ∧ e.1 ∣ q-1 ∧ q ∣ M := by
  have h' := List.all_eq_true.mp (List.all_eq_true.mp h e he) q hq
  simpa using h'

private lemma PackedBookSound_cells_have_witness {p : ℕ} {qs : List ℕ} :
    ∀ (rs : List ℕ) (start i : ℕ) (hi : i < rs.length),
    cells p qs start rs = true → 9 ≤ start+i → start+i ≤ p →
    ∃ q ∈ qs, goodResidue p rs[i] q = true := by
  intro rs
  induction rs with
  | nil => simp
  | cons r rs ih =>
    intro start i hi hc hlo hle
    rw [cells, Bool.and_eq_true] at hc
    rcases i with _ | i
    · simp only [Nat.add_zero] at hlo hle
      have hskip : ¬ (start < 9 ∨ p < start) := by omega
      have hgood : qs.any (goodResidue p r) = true := by simpa [hskip] using hc.1
      exact List.any_eq_true.mp hgood
    · have hi' : i < rs.length := by simpa using hi
      exact ih (start+1) i hi' hc.2 (by omega) (by omega)

/- Turn an accepted block into the modular witness for an arbitrary sequence
whose residues agree with the packed entries. -/
theorem witness_of_checked
    (hpow : ∀ m b e, PackedCompute.power m b e = b^e % m)
    {M start n p : ℕ} {book : Book} {rs : List ℕ} {f : ℕ → ℕ}
    (hcheck : checked start rs book = true) (hvalid : validBook M book = true)
    (hres : ∀ i : Fin rs.length, f (start+i.val) % M = rs[i.val])
    (hmem : p ∈ book.map Prod.fst) (hs : start ≤ n) (hne : n < start+rs.length)
    (h9 : 9 ≤ n) (hnp : n ≤ p) :
    ∃ q : ℕ, q.Prime ∧ p ∣ q-1 ∧ (f n : ZMod q) ≠ 0 ∧
      (f n : ZMod q)^((q-1)/p) ≠ 1 := by
  obtain ⟨e, he, hep⟩ := List.mem_map.mp hmem
  rcases e with ⟨p',qs⟩
  change p' = p at hep
  subst p'
  have hc : cells p qs start rs = true := List.all_eq_true.mp hcheck _ he
  have hi : n-start < rs.length := by omega
  have hn : start + (n-start) = n := by omega
  obtain ⟨q, hq, hg⟩ := PackedBookSound_cells_have_witness rs start (n-start) hi hc (by omega) (by omega)
  obtain ⟨hprime, hd, hqM⟩ := validBook_entry hvalid he hq
  have heq := hres ⟨n-start,hi⟩
  change f (start+(n-start)) % M = rs[n-start] at heq
  rw [hn] at heq
  let t := rs[n-start] % q
  have ht : t = f n % q := by
    dsimp [t]
    rw [← heq, Nat.mod_mod_of_dvd _ hqM]
  change (decide (t ≠ 0) && decide (PackedCompute.power q t ((q-1)/p) ≠ 1)) = true at hg
  rw [Bool.and_eq_true] at hg
  obtain ⟨ht0, ht1⟩ := hg
  have not0 : t ≠ 0 := of_decide_eq_true ht0
  have not1 : t^((q-1)/p) % q ≠ 1 := by
    rw [← hpow]
    exact of_decide_eq_true ht1
  have cast_t : (t:ZMod q) = f n := by rw [ht,ZMod.natCast_mod]
  refine ⟨q,hprime,hd,?_,?_⟩
  · intro hz
    exact not0 (ht.trans (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp hz)))
  · intro hz
    let _ : Fact (1 < q) := ⟨hprime.one_lt⟩
    rw [← cast_t, ← Nat.cast_pow] at hz
    exact not1 (by simpa only [ZMod.val_natCast, ZMod.val_one] using congrArg ZMod.val hz)

end OeisA113258.BookCheck
end

section
namespace OeisA113258.BookCheck

theorem primeTrial_iff {q : ℕ} : primeTrial q = true ↔ q.Prime := by
  rw [primeTrial, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Nat.prime_def_le_sqrt]
  constructor
  · rintro ⟨h2,h⟩
    refine ⟨h2, ?_⟩
    intro d hd hq hdvd
    have hr := of_decide_eq_true (h d (List.mem_range.mpr (by omega)))
    exact (hr.resolve_left (by omega)) (Nat.mod_eq_zero_of_dvd hdvd)
  · rintro ⟨h2,h⟩
    refine ⟨h2, ?_⟩
    intro d hd
    rw [decide_eq_true_eq]
    by_cases hsmall : d<2
    · exact Or.inl hsmall
    · exact Or.inr (fun hz => h d (by omega) (by have := List.mem_range.mp hd; omega)
          (Nat.dvd_of_mod_eq_zero hz))

theorem mem_primeKeys {lo hi p : ℕ} :
    p ∈ primeKeys lo hi ↔ lo ≤ p ∧ p < hi ∧ p.Prime := by
  simp only [primeKeys, List.mem_filter, List.mem_range'_1, primeTrial_iff]
  constructor
  · rintro ⟨⟨hle,hlt⟩,hprime⟩
    exact ⟨hle, by omega, hprime⟩
  · rintro ⟨hle,hlt,hprime⟩
    exact ⟨⟨hle,by omega⟩,hprime⟩

theorem validBook_of_fast {M : ℕ} {book : Book} (h : fastValidBook M book = true) :
    validBook M book = true := by
  rw [validBook, List.all_eq_true]
  intro e he
  rw [List.all_eq_true]
  intro q hq
  have hw := List.all_eq_true.mp (List.all_eq_true.mp h e he) q hq
  simpa only [Bool.and_eq_true, primeTrial_iff, decide_eq_true_eq] using hw

end OeisA113258.BookCheck
end


section
namespace OeisA113258.PackedCompute

def seq (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (i+1).factorial ^ (n-i).factorial

theorem powerAux_eq (m b : ℕ) (k e : ℕ) : powerAux m b k e = b^e % m := by
  induction k generalizing e with
  | zero => rfl
  | succ k ih =>
    rw [powerAux]
    split
    · rfl
    · rw [ih]
      dsimp only
      rw [← Nat.pow_mod, ← Nat.mul_mod, ← pow_mul, ← pow_add]
      congr 2
      omega

theorem power_eq (m b e : ℕ) : power m b e = b^e % m := by
  change (((b^(e/16) % m)^16 * b^(e%16)) % m) = _
  calc
    _ = (((b^(e/16))^16 % m) * (b^(e%16) % m)) % m := by
      rw [Nat.mul_mod _ _ m, ← Nat.pow_mod]
    _ = ((b^(e/16))^16 * b^(e%16)) % m := (Nat.mul_mod _ _ _).symm
    _ = _ := by
      rw [← Nat.pow_mul, ← Nat.pow_add]
      congr 2
      omega

theorem update_ofFn (m j : ℕ) {n : ℕ} (f : Fin n → ℕ) :
    update m j (List.ofFn f) = List.ofFn (fun i => power m (f i) (j+i.val)) := by
  induction n generalizing j with
  | zero => simp [update]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [update, Fin.val_zero, Nat.add_zero, List.cons.injEq, true_and]
    rw [ih]
    congr 1
    funext i
    simp only [Fin.val_succ]
    congr 1
    omega

theorem state_eq (m n : ℕ) : state m n =
    (n.factorial%m,List.ofFn (fun i : Fin n => (n-i.val).factorial^(i.val+1).factorial % m)) := by
  induction n with
  | zero => simp [state]
  | succ n ih =>
    rw [state, ih, step]
    simp only
    rw [Nat.factorial_succ, Nat.mod_mul_mod, Nat.mul_comm n.factorial, update_ofFn, List.ofFn_succ]
    simp only [Fin.val_zero, Nat.sub_zero, Nat.zero_add, Nat.factorial_one, pow_one,
      Prod.mk.injEq, List.cons.injEq, true_and, Nat.factorial_succ n]
    congr 1
    funext i
    rw [power_eq, ← Nat.pow_mod, ← pow_mul]
    simp only [Fin.val_succ, Nat.add_sub_add_right]
    congr 2
    rw [Nat.factorial_succ (i.val+1), Nat.mul_comm]
    congr 1
    omega

theorem state_sum (m n : ℕ) : (state m n).2.sum % m = seq n % m := by
  rw [state_eq, List.sum_ofFn, ← Finset.sum_nat_mod]
  unfold seq
  rw [← Fin.sum_univ_eq_sum_range]
  congr 1
  calc
    _ = ∑ i : Fin n, ((Fin.rev i).val+1).factorial ^ (n-(Fin.rev i).val).factorial := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.val_rev]
      congr 2 <;> omega
    _ = _ := Equiv.sum_comp Fin.revPerm (fun i : Fin n => (i.val+1).factorial ^ (n-i.val).factorial)

theorem replay_sound {m start : ℕ} {rs : List ℕ}
    (hr : replay m start (state m start) rs = true) :
    ∀ i : Fin rs.length, seq (start+i.val+1) % m = rs[i] := by
  induction rs generalizing start with
  | nil => intro i; exact Fin.elim0 i
  | cons r rs ih =>
    change ((_ == r) && _) = true at hr
    obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp hr
    have h0 := (state_sum m (start+1)).symm.trans (beq_iff_eq.mp head)
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using h0
    · have h := ih (start := start+1) tail j
      simpa [Nat.add_assoc, Nat.add_comm 1, Nat.add_left_comm] using h

end OeisA113258.PackedCompute
end

section
namespace OeisA113258.PackedCompute
abbrev State := Nat × List Nat

def reduceState (m : Nat) (s : State) : State := (s.1 % m, s.2.map (· % m))

/- Check the residue emitted at each index and the full state passed to the next chunk. -/
def checkpoint (m : Nat) (last : State) : Nat → State → List Nat → Bool
  | _, s, [] => s == last
  | n, s, r::rs =>
    let t := step m (n+1) s
    t.2.sum % m == r && checkpoint m last (n+1) t rs

end OeisA113258.PackedCompute
end

section
/- # One-pass packed residual trace and its equivalent checkpoint verifier -/
namespace OeisA113258.Compact
open PackedCompute

/- Compute all residues of a certified block and its outgoing state together.
The block is traversed once when its result is materialized. -/
noncomputable def blockResult (m : Nat) : Nat → Nat → State → List Nat × State
  | 0,_,s => ([],s)
  | k+1,n,s =>
    let t := step m (n+1) s
    let tail := blockResult m k (n+1) t
    (t.2.sum % m :: tail.1, tail.2)

/- The computed residues and outgoing state always pass the existing
checkpoint verifier, for every modulus, number of steps, and incoming state. -/
theorem blockResult_spec (m k n : Nat) (s : State) :
    (blockResult m k n s).1.length = k ∧
    checkpoint m (blockResult m k n s).2 n s (blockResult m k n s).1 = true := by
  induction k generalizing n s with
  | zero => simp [blockResult,checkpoint]
  | succ k ih =>
    obtain ⟨hlen,hrun⟩ := ih (n+1) (step m (n+1) s)
    simp only [blockResult,List.length_cons, hlen,checkpoint,beq_self_eq_true,Bool.true_and,hrun,and_self]

/- Project the proof attached to a materialized result into the exact two
hypotheses used by both the initial and subsequent prefix-chain blocks. -/
theorem verified_block {m k n : Nat} {s : State} {v : List Nat × State}
    (h : blockResult m k n s = v) :
    v.1.length = k ∧ checkpoint m v.2 n s v.1 = true := by
  rw [← h]
  exact blockResult_spec m k n s

end OeisA113258.Compact
end

section
namespace OeisA113258.PackedCompute

theorem checkpoint_sound {m n : Nat} {last : State} {rs : List Nat}
    (h : checkpoint m last n (state m n) rs = true) :
    replay m n (state m n) rs = true ∧ state m (n + rs.length) = last := by
  induction rs generalizing n with
  | nil => exact ⟨rfl,by simpa using (beq_iff_eq.mp h)⟩
  | cons r rs ih =>
    change ((_ == r) && _) = true at h
    obtain ⟨hhead,htail⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hr,hend⟩ := ih (n:=n+1) htail
    constructor
    · exact Bool.and_eq_true_iff.mpr ⟨hhead,hr⟩
    · simpa [Nat.add_assoc,Nat.add_comm 1] using hend

theorem reduceState_correct {m k : Nat} (h : k ∣ m) (n : Nat) :
    reduceState k (state m n) = state k n := by
  rw [state_eq,state_eq,reduceState]
  simp only [Nat.mod_mod_of_dvd _ h, List.map_ofFn, Function.comp_def]

end OeisA113258.PackedCompute
end

section
namespace OeisA113258.Interval9To100
open PackedCompute OeisA113258.Compact
def modulus : Nat := 3459514068906069830533040149019041282518384597395812302645929377390059746531332823026963879246270584432559688196701351560997078660164524556367946916343269127328702865646621523854507954635392155088744023928215241773430913553558949533052429983977292739476106547913526120746681659201878229194608653994575651313697295208195037779955927289725625161435066418862536040690867023294172365458934927843477348202608100888213278641363168426104561198715997697488564799140487439363620918228997027039918167628110287037424487133956888772999447432649284929055415297284545608384468732454076403314680283753284327974572312030845458347966584300577217145149140578766809746240826440594425326476389375709488494814182037411923456564485113578270793498491673889040984621103595074490429013468635669664261024066886127358683046785505020801243304469580108771496729051845411299005991144291980906812542796335957023088439013149689470712372003245703444543602951672154358751488117831774935663761564782050435016469324052778415679582072651379494715855702504862747380259391128221437389139826878381673672937125505785798093834032836854625817831402719162389314016683973272597064061829743890099029969481522694155857963919049264971893611866474662255443950431859387054889721487579025482447770591180721438479872466959110210072351570092485809416438241363436150603128278844042718092015467776460971904372734613374600602131603125267245381161730940443435752560964033610223228894509523825539526493746371167147813092563152536862510485430833138119208086452541381991346992814126339201180325796622258150867713625182094278483527789359007358097240250667545084026192242787402924999691209968955673944163235795072618570856661016820157057823125173960452320287431790718606781866603240285725097304305537619422905171778724047175524943135792010508674405372163303626499104002648054168268596857333217618760619718274037546006084328134606493749156343615486677916649564447164771549451981902489885624966625128540508279266472566996557436373351519625743877177764087571204103331736112104667249610764686758941773510717345518985280379785976098493172261040060183171072467400768670091570598610372596015561347138530182977308582363542289871602723678520604749082789529194342512768123857118935342434056254009611126395406908221132898297267139134255082132134070544847999608867909146103897707995897739646155274162432574188310152668090784243403147996088053917672286583091070781713886636958915738996727268689537068291383114605943534610287999689069650128669640828870447460450854392917435058133195880294202301658927618501068449305622764035161091784129525699917344988406712639416938725120930777068688052040170001172149026807239351235757661940527991635740099616183382754584189970934432010754860529699580441891565829276510507588820080555071901169765371636854316232703695105818920835560504232705847651364650162884374196028994407076427304141232548969516134078764156479126624687784621925801905208776251716841443783907552697731820803136188905022922823157701468533734638798204463042782852881096441151474461289645859363416524884648509621582578399837297979144138909630791699914388011024025642826701301665881728799153988022933904477196279121632201982069865148428504285936923663736694721272285011288726223268417205693519021980879355645403392608477718167816710579339546841012718611724937642336419136275264041957971812154141083899691983031321656033213366598090689281656262602463230110048581987983091599790341428148212205394959303002403910571691676167283868249199823314213348874058948582204720967407643
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def trace : { v : List Nat × State // blockResult modulus 100 0 (state modulus 0) = v } := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def values := trace.val.1
noncomputable def active := values.drop 8
theorem replayValues : replay modulus 0 (state modulus 0) values = true :=
  (checkpoint_sound (verified_block trace.property).2).1
theorem lengthValues : values.length = 100 := (verified_block trace.property).1
theorem lengthActive : active.length = 92 := by simp [active,lengthValues]
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book0 : Book := [(11,[23,67]),(13,[53]),(17,[103,137]),(19,[191]),(23,[47]),(29,[59,233]),(31,[311]),(37,[149,223]),(41,[83,739]),(43,[173,431]),(47,[283,659]),(53,[107]),(59,[709]),(61,[367]),(67,[269]),(71,[569,853]),(73,[293]),(79,[317,1423]),(83,[167]),(89,[179,1069]),(97,[389]),(101,[607]),(103,[619]),(107,[643,857]),(109,[1091]),(113,[227,1583]),(127,[509,2287]),(131,[263,787]),(137,[823]),(139,[557]),(149,[1193]),(151,[907]),(157,[1571,3769]),(163,[653,2609]),(167,[2339,5011]),(173,[347,1039])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 9 active book0 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book1 : Book := [(179,[359,1433]),(181,[1087,1811]),(191,[383,2293]),(193,[773,1931]),(197,[3547]),(199,[797,2389]),(211,[2111]),(223,[2677,6691]),(227,[5449,5903]),(229,[2749]),(233,[467]),(239,[479]),(241,[1447]),(251,[503]),(257,[1543]),(263,[1579]),(269,[2153]),(271,[1627]),(277,[1109,1663]),(281,[563]),(283,[1699]),(293,[587]),(307,[1229]),(311,[1867]),(313,[1879]),(317,[8243]),(331,[1987]),(337,[3371]),(347,[2083]),(349,[3491]),(353,[4943]),(359,[719]),(367,[2203]),(373,[1493,2239]),(379,[4549]),(383,[4597])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 9 active book1 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book2 : Book := [(389,[9337]),(397,[2383]),(401,[3209]),(409,[1637]),(419,[839,5867]),(421,[4211]),(431,[863]),(433,[1733]),(439,[4391]),(443,[887]),(449,[3593]),(457,[13711]),(461,[2767]),(463,[5557]),(467,[2803]),(479,[3833,5749]),(487,[1949,4871]),(491,[983]),(499,[1997]),(503,[3019]),(509,[1019]),(521,[16673]),(523,[5231,6277]),(541,[9739]),(547,[5471]),(557,[3343]),(563,[7883]),(569,[6829,10243]),(571,[5711]),(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 9 active book2 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book3 : Book := [(617,[4937]),(619,[2477]),(631,[6311,7573]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967,7933]),(673,[2693]),(677,[5417,9479]),(683,[1367]),(691,[6911]),(701,[12619,21031]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619,6473]),(811,[8111]),(821,[6569]),(823,[8231,19753]),(827,[11579]),(829,[8291]),(839,[10069,25171]),(853,[3413]),(857,[6857])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 9 active book3 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book4 : Book := [(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells4 : checked 9 active book4 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book5 : Book := [(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579,10313]),(1291,[12911]),(1297,[5189]),(1301,[26021]),(1303,[20849]),(1307,[10457]),(1319,[23743]),(1321,[7927]),(1327,[5309]),(1361,[8167]),(1367,[10937]),(1373,[16477])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells5 : checked 9 active book5 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book6 : Book := [(1381,[8287]),(1399,[25183]),(1409,[2819]),(1423,[5693,8539]),(1427,[8563]),(1429,[5717]),(1433,[8599]),(1439,[2879]),(1447,[34729]),(1451,[2903]),(1453,[5813]),(1459,[14591]),(1471,[23537]),(1481,[2963]),(1483,[14831]),(1487,[8923]),(1489,[14891]),(1493,[20903]),(1499,[2999]),(1511,[3023]),(1523,[21323]),(1531,[9187]),(1543,[6173]),(1549,[6197]),(1553,[9319]),(1559,[3119]),(1567,[6269]),(1571,[12569]),(1579,[6317]),(1583,[3167]),(1597,[6389]),(1601,[3203]),(1607,[9643]),(1609,[16091]),(1613,[9679]),(1619,[12953])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells6 : checked 9 active book6 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book7 : Book := [(1621,[29179]),(1627,[29287]),(1637,[62207]),(1657,[26513]),(1663,[6653]),(1667,[13337]),(1669,[16691]),(1693,[10159]),(1697,[13577]),(1699,[20389]),(1709,[20509]),(1721,[34421]),(1723,[17231]),(1733,[3467,10399]),(1741,[38303]),(1747,[17471]),(1753,[7013]),(1759,[31663]),(1777,[7109]),(1783,[21397]),(1787,[10723]),(1789,[17891,32203]),(1801,[21613]),(1811,[3623]),(1823,[10939]),(1831,[10987]),(1847,[11083]),(1861,[74441]),(1867,[18671]),(1871,[14969]),(1873,[11239]),(1877,[15017]),(1879,[7517,22549]),(1889,[3779]),(1901,[3803,68437]),(1907,[11443])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells7 : checked 9 active book7 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book8 : Book := [(1913,[26783,38261]),(1931,[3863]),(1933,[23197]),(1949,[35083]),(1951,[42923]),(1973,[3947]),(1979,[39581]),(1987,[7949]),(1993,[11959]),(1997,[87869]),(1999,[19991]),(2003,[4007]),(2011,[24133]),(2017,[8069]),(2027,[12163]),(2029,[8117]),(2039,[4079]),(2053,[94439]),(2063,[4127]),(2069,[4139,16553]),(2081,[12487]),(2083,[33329]),(2087,[37567]),(2089,[45959]),(2099,[25189]),(2111,[16889]),(2113,[25357]),(2129,[4259]),(2131,[59669]),(2137,[12823]),(2141,[4283]),(2143,[8573]),(2153,[12919]),(2161,[12967]),(2179,[47939]),(2203,[13219])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells8 : checked 9 active book8 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book9 : Book := [(2207,[17657]),(2213,[26557]),(2221,[13327]),(2237,[31319]),(2239,[22391]),(2243,[71777]),(2251,[22511]),(2267,[45341]),(2269,[22691]),(2273,[4547]),(2281,[13687]),(2287,[13723]),(2293,[9173]),(2297,[32159]),(2309,[32327]),(2311,[27733]),(2333,[13999]),(2339,[4679]),(2341,[42139]),(2347,[14083]),(2351,[4703]),(2357,[14143]),(2371,[52163]),(2377,[42787]),(2381,[28573]),(2383,[9533]),(2389,[28669,43003]),(2393,[4787]),(2399,[4799]),(2411,[19289]),(2417,[14503]),(2423,[29077]),(2437,[9749]),(2441,[48821]),(2447,[14683]),(2459,[4919])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells9 : checked 9 active book9 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book10 : Book := [(2467,[24671]),(2473,[39569]),(2477,[34679]),(2503,[25031]),(2521,[30253]),(2531,[15187]),(2539,[25391]),(2543,[5087]),(2549,[5099]),(2551,[15307]),(2557,[46027]),(2579,[30949]),(2591,[46639]),(2593,[15559]),(2609,[20873]),(2617,[26171]),(2621,[15727]),(2633,[94789]),(2647,[10589]),(2657,[37199]),(2659,[26591]),(2663,[31957]),(2671,[26711]),(2677,[10709]),(2683,[10733,42929]),(2687,[37619]),(2689,[26891]),(2693,[5387]),(2699,[5399]),(2707,[43313]),(2711,[16267]),(2713,[10853]),(2719,[27191]),(2729,[32749]),(2731,[60083]),(2741,[5483])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells10 : checked 9 active book10 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book11 : Book := [(2749,[82471]),(2753,[5507]),(2767,[11069,16603]),(2777,[55541]),(2789,[33469]),(2791,[16747]),(2797,[44753]),(2801,[22409]),(2803,[11213]),(2819,[5639,33829]),(2833,[33997]),(2837,[22697]),(2843,[90977]),(2851,[17107]),(2857,[28571]),(2861,[17167]),(2879,[34549]),(2887,[11549]),(2897,[17383]),(2903,[5807,17419]),(2909,[52363]),(2917,[70009]),(2927,[23417]),(2939,[5879]),(2953,[11813]),(2957,[41399]),(2963,[5927]),(2969,[5939]),(2971,[17827]),(2999,[23993]),(3001,[30011]),(3011,[96353]),(3019,[36229]),(3023,[6047]),(3037,[12149]),(3041,[24329])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells11 : checked 9 active book11 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book12 : Book := [(3049,[12197]),(3061,[18367]),(3067,[12269]),(3079,[73897]),(3083,[36997]),(3089,[55603,61781]),(3109,[12437]),(3119,[24953,74857]),(3121,[49937]),(3137,[25097]),(3163,[12653]),(3167,[114013]),(3169,[95071]),(3181,[19087]),(3187,[50993,57367]),(3191,[95731]),(3203,[19219]),(3209,[25673]),(3217,[51473]),(3221,[38653]),(3229,[12917]),(3251,[19507]),(3253,[32531,110603]),(3257,[19543,45599]),(3259,[13037]),(3271,[71963]),(3299,[6599]),(3301,[52817,59419]),(3307,[13229]),(3313,[99391]),(3319,[33191]),(3323,[39877]),(3329,[6659]),(3331,[33311]),(3343,[73547]),(3347,[26777])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells12 : checked 9 active book12 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book13 : Book := [(3359,[6719]),(3361,[53777]),(3371,[60679]),(3373,[80953]),(3389,[6779]),(3391,[20347]),(3407,[20443]),(3413,[6827]),(3433,[20599]),(3449,[6899]),(3457,[13829]),(3461,[27689]),(3463,[34631]),(3467,[27737]),(3469,[13877]),(3491,[6983]),(3499,[13997]),(3511,[21067]),(3517,[35171]),(3527,[21163]),(3529,[35291]),(3533,[42397]),(3539,[7079]),(3541,[21247]),(3547,[21283]),(3557,[85369]),(3559,[35591]),(3571,[42853]),(3581,[21487]),(3583,[21499]),(3593,[7187]),(3607,[57713]),(3613,[36131]),(3617,[72341]),(3623,[7247]),(3631,[21787])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells13 : checked 9 active book13 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book14 : Book := [(3637,[14549]),(3643,[21859]),(3659,[73181]),(3671,[22027,44053]),(3673,[22039]),(3677,[22063]),(3691,[22147,44293]),(3697,[88729]),(3701,[74021]),(3709,[66763]),(3719,[29753]),(3727,[89449]),(3733,[44797]),(3739,[14957]),(3761,[7523,22567]),(3767,[30137]),(3769,[15077]),(3779,[7559]),(3793,[15173]),(3797,[22783]),(3803,[7607]),(3821,[7643]),(3823,[38231]),(3833,[229981]),(3847,[61553]),(3851,[7703]),(3853,[15413]),(3863,[7727]),(3877,[108557]),(3881,[46573]),(3889,[38891]),(3907,[15629]),(3911,[7823]),(3917,[31337]),(3919,[39191]),(3923,[23539])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells14 : checked 9 active book14 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book15 : Book := [(3929,[47149]),(3931,[62897]),(3943,[15773]),(3947,[55259]),(3967,[39671,63473]),(3989,[47869]),(4001,[24007]),(4003,[24019]),(4007,[24043]),(4013,[48157]),(4019,[8039]),(4021,[72379]),(4027,[64433]),(4049,[48589]),(4051,[64817]),(4057,[16229]),(4073,[8147]),(4079,[32633]),(4091,[24547]),(4093,[49117]),(4099,[73783]),(4111,[49333]),(4127,[24763]),(4129,[49549]),(4133,[24799]),(4139,[33113]),(4153,[24919]),(4157,[24943]),(4159,[91499]),(4177,[41771]),(4201,[67217]),(4211,[8423]),(4217,[25303]),(4219,[168761]),(4229,[59207]),(4231,[50773])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells15 : checked 9 active book15 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book16 : Book := [(4241,[25447]),(4243,[101833,127291]),(4253,[85061]),(4259,[51109]),(4261,[42611]),(4271,[8543]),(4273,[17093]),(4283,[85661]),(4289,[34313]),(4297,[17189]),(4327,[43271]),(4337,[60719]),(4339,[43391]),(4349,[8699]),(4357,[78427]),(4363,[69809]),(4373,[8747]),(4391,[8783]),(4397,[61559]),(4409,[8819]),(4421,[79579]),(4423,[26539]),(4441,[26647]),(4447,[17789]),(4451,[89021]),(4457,[115883]),(4463,[62483]),(4481,[8963]),(4483,[98627]),(4493,[26959]),(4507,[27043]),(4513,[45131]),(4517,[27103]),(4519,[18077]),(4523,[54277]),(4547,[27283])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells16 : checked 9 active book16 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book17 : Book := [(4549,[45491]),(4561,[27367]),(4567,[18269]),(4583,[119159]),(4591,[128549]),(4597,[27583]),(4603,[18413]),(4621,[101663]),(4637,[27823]),(4639,[102059]),(4643,[55717]),(4649,[111577]),(4651,[46511]),(4657,[27943]),(4663,[74609]),(4673,[65423]),(4679,[56149]),(4691,[37529]),(4703,[28219]),(4721,[84979]),(4723,[160583]),(4729,[18917]),(4733,[9467,123059]),(4751,[95021]),(4759,[19037]),(4783,[57397]),(4787,[28723]),(4789,[19157]),(4793,[9587]),(4799,[38393]),(4801,[28807]),(4813,[28879]),(4817,[125243]),(4831,[48311]),(4861,[29167]),(4871,[9743])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells17 : checked 9 active book17 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book18 : Book := [(4877,[68279]),(4889,[39113]),(4903,[49031]),(4909,[58909]),(4919,[9839]),(4931,[29587]),(4933,[29599]),(4937,[69119]),(4943,[9887]),(4951,[89119]),(4957,[89227]),(4967,[29803]),(4969,[59629]),(4973,[69623]),(4987,[19949]),(4993,[19973]),(4999,[19997]),(5003,[10007]),(5009,[90163]),(5011,[50111]),(5021,[40169]),(5023,[30139]),(5039,[10079]),(5051,[10103]),(5059,[50591]),(5077,[81233]),(5081,[10163]),(5087,[40697]),(5099,[71387]),(5101,[112223]),(5107,[30643]),(5113,[51131]),(5119,[20477,92143]),(5147,[41177]),(5153,[61837]),(5167,[186013])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells18 : checked 9 active book18 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book19 : Book := [(5171,[10343]),(5179,[20717]),(5189,[41513]),(5197,[20789]),(5209,[93763]),(5227,[397253,407707]),(5231,[10463]),(5233,[115127]),(5237,[41897]),(5261,[31567]),(5273,[63277]),(5279,[10559]),(5281,[31687]),(5297,[74159]),(5303,[10607]),(5309,[42473]),(5323,[53231]),(5333,[10667,63997]),(5347,[32083]),(5351,[107021]),(5381,[43049]),(5387,[32323]),(5393,[32359]),(5399,[10799]),(5407,[32443]),(5413,[32479]),(5417,[32503]),(5419,[65029]),(5431,[32587,54311]),(5437,[54371]),(5441,[10883]),(5443,[21773]),(5449,[185267]),(5471,[98479]),(5477,[76679]),(5479,[120539])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells19 : checked 9 active book19 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book20 : Book := [(5483,[109661]),(5501,[11003]),(5503,[22013]),(5507,[132169,165211]),(5519,[77267]),(5521,[88337]),(5527,[22109]),(5531,[44249]),(5557,[22229]),(5563,[55631]),(5569,[22277]),(5573,[66877]),(5581,[33487]),(5591,[33547]),(5623,[33739]),(5639,[11279]),(5641,[327179]),(5647,[90353]),(5651,[101719]),(5653,[22613]),(5657,[147083]),(5659,[22637]),(5669,[79367]),(5683,[136393]),(5689,[56891]),(5693,[34159]),(5701,[125423]),(5711,[11423]),(5717,[34303]),(5737,[160637]),(5741,[11483]),(5743,[22973]),(5749,[103483]),(5779,[23117]),(5783,[80963]),(5791,[34747])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells20 : checked 9 active book20 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book21 : Book := [(5801,[34807]),(5807,[34843]),(5813,[209269]),(5821,[58211]),(5827,[34963]),(5839,[23357]),(5843,[35059]),(5849,[11699]),(5851,[35107]),(5857,[163997]),(5861,[46889,105499]),(5867,[82139]),(5869,[70429]),(5879,[70549]),(5881,[70573]),(5897,[82559]),(5903,[11807]),(5923,[130307]),(5927,[47417]),(5939,[47513]),(5953,[23813]),(5981,[215317]),(5987,[35923])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells21 : checked 9 active book21 = true := by decide +kernel
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100
open PackedCompute BookCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def book : Book := book0 ++ book1 ++ book2 ++ book3 ++ book4 ++ book5 ++ book6 ++ book7 ++ book8 ++ book9 ++ book10 ++ book11 ++ book12 ++ book13 ++ book14 ++ book15 ++ book16 ++ book17 ++ book18 ++ book19 ++ book20 ++ book21
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 9 active book = true := by
  simp only [book, checked_append, cells0, cells1, cells2, cells3, cells4, cells5, cells6, cells7, cells8, cells9, cells10, cells11, cells12, cells13, cells14, cells15, cells16, cells17, cells18, cells19, cells20, cells21, Bool.and_self]
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.BookCheck

/- The factorials are literal integers so that all trial checks share them. -/
def fac80 : Nat := 0x71864253b6affa79c2ea1bc52a6a1d446ca57e6ffc4196e88af1b894823817f63f40c910e81fcc940000000000000000000
def fac1024 : Nat := 0x2022f598887b1b677793eea7338140b96edd924fcab3a183421f3dcfe257e91fdb9fbda6fdc765c78087e0afb0469ee9dc04e88b57dbc8a8850c431640a70a5553f274cf95cf31ef50ff773bb46b4f14badbef976885d017edb30ca9d17100464466d8e2c424c4eb35a8ad96698ab9da18c5941a808585b16d700ea60fe4742b55d151d2fa72fb5314bf93374f6ba357b7e7b81928b2fcef3b564380dc3bd2d0d3580a28d5aead0d707cdd521cb09f953e45849e4ea04445db770f4473bfd62494ba215e1370df02adb30f0aec0dc9adccc96284cf6d8ffed1dd2833033d53dbb87f602c4c286f1c03b25795d45d8fd8d989a47ec52b856055b878c7329f655f487052c38bcd4a790b30277c68153bcb18a167e393143051e069b23b51d05cb8b0040c7086c76707d0d69400443d00223aaa1c24dc6aa22eeb60f1402efea0babf3f916fe20dfeca617d4a72b2818db64445eb896f589524c9803c6b97c05803e5333357ef9281627249eba91582c91ef846f3f0a84b92a079c62b33dd2419af649fbcc579686ae8fb54746b82b83fc3402833941f035b655216b02bb7a0b42ba292f70af8fd3c6922a2c065dd523c7723b37f1bba4f2411f9d917091b4c99c676242826777b15c868fa3e528596e5ce1ebe1634565a393a60c8d7daaa16b1bd7679f6f5e923569eefc0fbcea6da292fef18f19bc4b6306fc70161c9f19b75c55710ddd3a2d4edfa892b7184e2a601bf85b047b9b256a8338739e257ee896dadbfa43e08360591f78cd6a3d40e8c04beebd2e22f357d2fcf22ec25cb48ed2cee17f7a638ce99a83b6db18a25e6418e162c55479577a5b781703c46174b9b929095e732845329dde20b46d0ec7e74e90aff69906f485a24d40bae6190296d0218ce544d19db6fcdc55a624493b698ecbb01751e1a1ad46d2cf590df06e631bb6048680bd616f3e4d80b5c562d5660cf611154ad88ef87290d24ba9e89eebc2fd3cce8560a034f23134f9813c48debd014e2ccda5d947ecf35e2f40464199f5fa75900d1a2c47c50d1982caea69002fb8057c97f6eec6e1040202741885d11ad136965f70bbaa24ee85dd09dace0b2bc1008b3180a501be1e791f016fbf750ce18f1a4352b2caf0f01fa1d7020ea70f9bb3cdfce1b26b73172809e1dfa5ef33f4c89a3f6e4219d024f29cf91ecf25ae7620cdd6453351bf2e64e97212b56d7bdeb9c7fa700468ab881cda84380998f47e46a537948431b47f258fd092c739d207eeb3b91fe231adab484d6161b750c2cd6f77f650f76a8deac564d2da13a26650ee9aa992797601b1629d7ac4e540699eeb66183724dede658673e0a3b3b5c06a3c741c1c4aa746d7458000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

/- A single gcd with k! detects compositeness when sqrt(q) ≤ k < q. -/
def gcdPrime (q : Nat) : Bool :=
  if q ≤ 80 then primeTrial q
  else if q.sqrt ≤ 80 then decide (Nat.gcd q fac80 = 1)
  else if q ≤ 1024 then primeTrial q
  else if q.sqrt ≤ 1024 then decide (Nat.gcd q fac1024 = 1)
  else primeTrial q

def gcdPrimeKeys (lo hi : Nat) := (List.range' lo (hi-lo)).filter gcdPrime
def gcdValidBook (M : Nat) (book : Book) :=
  book.all (fun e => e.2.all (fun q => gcdPrime q && decide (e.1 ∣ q-1 ∧ q ∣ M)))

end OeisA113258.BookCheck
end

section
namespace OeisA113258.Interval9To100
open BookCheck

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validByGcd : gcdValidBook modulus book = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem keysByGcd : book.map Prod.fst = gcdPrimeKeys 9 6000 := by decide +kernel

end OeisA113258.Interval9To100
end

section
namespace OeisA113258.BookCheck

private theorem GcdPrimeSound_prime_of_coprime_factorial {q k : ℕ} (h2 : 2 ≤ q) (hk : k < q)
    (hs : q.sqrt ≤ k) : Nat.gcd q k.factorial = 1 ↔ q.Prime := by
  constructor
  · intro hc
    refine Nat.prime_def_le_sqrt.mpr ⟨h2, ?_⟩
    intro d hd hds hdq
    have hfac : d ∣ k.factorial := Nat.dvd_factorial (by omega) (hds.trans hs)
    have h := Nat.dvd_gcd hdq hfac
    rw [hc, Nat.dvd_one] at h
    omega
  · intro hp
    change q.Coprime k.factorial
    exact hp.coprime_iff_not_dvd.mpr (fun h => (not_le_of_gt hk) (hp.dvd_factorial.mp h))

set_option maxRecDepth 10000 in
private theorem GcdPrimeSound_fac80_eq : fac80 = Nat.factorial 80 := by decide +kernel

set_option maxRecDepth 10000 in
private theorem GcdPrimeSound_fac1024_eq : fac1024 = Nat.factorial 1024 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gcdPrime_iff {q : ℕ} : gcdPrime q = true ↔ q.Prime := by
  unfold gcdPrime
  split
  · exact primeTrial_iff
  split
  · rw [decide_eq_true_eq, GcdPrimeSound_fac80_eq]
    exact GcdPrimeSound_prime_of_coprime_factorial (by omega) (by omega) (by assumption)
  split
  · exact primeTrial_iff
  split
  · rw [decide_eq_true_eq, GcdPrimeSound_fac1024_eq]
    exact GcdPrimeSound_prime_of_coprime_factorial (by omega) (by omega) (by assumption)
  · exact primeTrial_iff

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gcdPrime_eq : gcdPrime = primeTrial := by
  funext q
  exact Bool.eq_iff_iff.mpr (gcdPrime_iff.trans primeTrial_iff.symm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gcdPrimeKeys_eq (lo hi : ℕ) : gcdPrimeKeys lo hi = primeKeys lo hi := by
  simp only [gcdPrimeKeys, primeKeys, gcdPrime_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gcdValidBook_eq (M : ℕ) (book : Book) : gcdValidBook M book = fastValidBook M book := by
  simp only [gcdValidBook, fastValidBook, gcdPrime_eq]

end OeisA113258.BookCheck
end

section
namespace OeisA113258.Interval9To100
open BookCheck
theorem fastValid : fastValidBook modulus book = true := by
  exact (gcdValidBook_eq modulus book).symm.trans validByGcd
theorem keyList : book.map Prod.fst = primeKeys 9 6000 := by
  exact keysByGcd.trans (gcdPrimeKeys_eq 9 6000)
end OeisA113258.Interval9To100
end

section
namespace OeisA113258.Interval9To100

open PackedCompute BookCheck

private theorem Range100Verified_active_residue (i : Fin active.length) :
    seq (9+i.val) % modulus = active[i.val] := by
  have hi : i.val < 92 := by simpa only [lengthActive] using i.isLt
  have hi' : 8+i.val < values.length := by rw [lengthValues]; omega
  have h := replay_sound replayValues ⟨8+i.val,hi'⟩
  change seq (0+(8+i.val)+1) % modulus = values[8+i.val] at h
  rw [show 0+(8+i.val)+1 = 9+i.val by omega] at h
  simpa only [active, List.getElem_drop] using h

theorem certificates_up_to_100 (n p : ℕ) (hn : 9 ≤ n) (h100 : n ≤ 100)
    (hp : p.Prime) (hnp : n ≤ p) (h6 : p < 6000) :
    ∃ q : ℕ, q.Prime ∧ p ∣ q-1 ∧ (seq n : ZMod q) ≠ 0 ∧
      (seq n : ZMod q)^((q-1)/p) ≠ 1 := by
  have hkey : p ∈ book.map Prod.fst := by
    rw [keyList, mem_primeKeys]
    exact ⟨by omega, h6, hp⟩
  exact witness_of_checked power_eq allCells (validBook_of_fast fastValid)
    Range100Verified_active_residue hkey hn (by rw [lengthActive]; omega) hn hnp

end OeisA113258.Interval9To100
end

section
namespace OeisA113258

/- Unconditionally exclude every exponent with a prime factor below 6000
for all indices 5 through 100. -/
theorem no_perfect_power_through_100_of_small_factor {n b e p : ℕ}
    (hn : 5 ≤ n) (h100 : n ≤ 100) (he : 2 ≤ e) (hp : p.Prime)
    (hd : p ∣ e) (h6 : p < 6000) : a n ≠ b^e := by
  intro heq
  by_cases hs : n ≤ 8
  · exact ne_power_five_to_eight hn hs he heq
  have hnp := exponent_factors_ge_index hn hp hd he heq
  obtain ⟨j, hj⟩ := hd
  have hpow : a n = (b^j)^p := by rw [heq, hj, ← pow_mul, Nat.mul_comm p j]
  obtain ⟨q, hq, hpq, hz, hw⟩ :=
    Interval9To100.certificates_up_to_100 n p (by omega) h100 hp hnp h6
  exact exclude_power_by_witness (t := a n) hq hpq hz hw _ hpow

/- At every index from 5 to 100, the stated special case of Laurent's
Corollary 2 alone suffices to exclude all nontrivial powers. -/
end OeisA113258
end

section
/- Elementary explicit parameters for the A113258 determinant argument.
All logarithms are natural. The computations here use real inequalities alone. -/
open Real
namespace OeisA113258.Direct

theorem log_five_bounds : (1.6 : ℝ) < log 5 ∧ log 5 < 1.62 := by
  have h₁ := Real.log_lt_log (by positivity : (0:ℝ)<2^37)
    (by norm_num : (2:ℝ)^37 < 5^16)
  have h₂ := Real.log_lt_log (by positivity : (0:ℝ)<5^3)
    (by norm_num : (5:ℝ)^3 < 2^7)
  rw [Real.log_pow, Real.log_pow] at h₁ h₂
  norm_num1 at h₁ h₂
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

private theorem DirectParameters_log_three_thousand : log (3000:ℝ) < 8.05 := by
  have hpow : (3000:ℝ) = 3*(2*5)^3 := by norm_num
  rw [hpow, Real.log_mul (by norm_num) (by norm_num), Real.log_pow,
    Real.log_mul (by norm_num) (by norm_num)]
  -- 3*log(2)+3*log(5)+log(3)<8.05 using 3*log(5)<7*log(2).
  have h := Real.log_lt_log (by norm_num : 0<(5:ℝ)^3) (by norm_num : (5:ℝ)^3<2^7)
  rw [Real.log_pow,Real.log_pow] at h
  norm_num1 at h ⊢
  linarith [Real.log_three_lt_d9,Real.log_two_lt_d9]

private theorem DirectParameters_log_six_thousand : log (6000:ℝ) < 9 := by
  rw [show (6000:ℝ) = 3000*2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
  linarith [DirectParameters_log_three_thousand,Real.log_two_lt_d9]

noncomputable def rows (p : ℝ) : ℕ := ⌊2*log p⌋₊+8
noncomputable def halfColumns (L : ℕ) (v : ℝ) : ℕ := ⌈3*L*v⌉₊

theorem rows_bounds {p : ℝ} (hp : 1 ≤ p) :
    2*log p+7 ≤ (rows p : ℝ) ∧ (rows p : ℝ) ≤ 2*log p+8 := by
  have hz : 0 ≤ 2*log p := by have := Real.log_nonneg hp; linarith
  dsimp [rows]
  push_cast
  constructor
  · linarith [Nat.lt_floor_add_one (2*log p)]
  · linarith [Nat.floor_le hz]

theorem columns_bounds (L : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    6*L*v ≤ (2*halfColumns L v : ℕ) ∧ (2*halfColumns L v : ℕ) ≤ 6*L*v+2 := by
  dsimp [halfColumns]
  push_cast
  have hz : 0 ≤ 3*(L:ℝ)*v := by positivity
  constructor
  · linarith [Nat.le_ceil (3*(L:ℝ)*v)]
  · linarith [Nat.ceil_lt_add_one hz]

private theorem DirectParameters_row_envelope {x k c : ℝ} (hk : 0 < k) (hx : k ≤ x)
    (hc : 8 ≤ c) (hlog : 2*log k+8 ≤ c) :
    (rows x : ℝ)^2*k ≤ c^2*x ∧ (rows x : ℝ)*k ≤ c*x := by
  have hx0 := hk.trans_le hx
  have hy : 0 < x/k := div_pos hx0 hk
  let s := √(x/k)
  have hs : 1 ≤ s := Real.one_le_sqrt.mpr ((le_div_iff₀ hk).mpr (by linarith))
  have hs2 : s^2*k = x := by dsimp [s]; rw [Real.sq_sqrt hy.le]; field_simp
  have hr := Real.log_le_sub_one_of_pos (show 0 < s by linarith)
  have hslog : log s = log (x/k)/2 := Real.log_sqrt hy.le
  rw [Real.log_div hx0.ne' hk.ne'] at hslog
  have hL : (rows x : ℝ) ≤ c*s := by
    by_cases h1 : 1 ≤ x
    · have hh := (rows_bounds h1).2
      nlinarith [mul_nonneg (by linarith : 0≤c-4) (by linarith : (0 : ℝ) ≤ s - 1)]
    · have h0 : 2*log x ≤ 0 := by nlinarith [Real.log_nonpos hx0.le (by linarith : x≤1)]
      have he : rows x = 8 := by simp [rows,Nat.floor_of_nonpos h0]
      rw [he]; push_cast
      nlinarith [mul_nonneg (by linarith : 0≤c) (by linarith : (0 : ℝ) ≤ s - 1)]
  have h0 : 0 ≤ (rows x : ℝ) := by positivity
  have hsq := mul_self_le_mul_self h0 hL
  constructor
  · calc
      (rows x : ℝ)^2 * k ≤ (c*s)^2*k := mul_le_mul_of_nonneg_right (by nlinarith) hk.le
      _ = c^2*x := by rw [← hs2]; ring
  · calc
      (rows x : ℝ)*k ≤ (c*s)*k := mul_le_mul_of_nonneg_right hL hk.le
      _ ≤ c*x := by rw [← hs2]; nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hk.le) (by linarith) : 0≤c*k*s) (by linarith : (0 : ℝ) ≤ s - 1)]

/- Above either endpoint, the determinant exponent is smaller than the
negative logarithm forced by the factorial gap. -/
theorem endpoint_small {p : ℝ} (hp : 3000 ≤ p) :
    0.81 * (6*(rows p : ℝ)^2 + 2*rows p) < 0.96*(p-1) := by
  obtain ⟨h,h'⟩ := DirectParameters_row_envelope (by norm_num : (0:ℝ)<3000) hp
    (by norm_num : (8:ℝ)≤24.1) (by linarith [DirectParameters_log_three_thousand] : 2*log 3000+8 ≤ 24.1)
  nlinarith

theorem endpoint_large {p : ℝ} (hp : 6000 ≤ p) :
    0.81 * (6*(rows p : ℝ)^2 + 2*rows p) < 0.6*(p-1) := by
  obtain ⟨h,h'⟩ := DirectParameters_row_envelope (by norm_num : (0:ℝ)<6000) hp
    (by norm_num : (8:ℝ)≤26) (by linarith [DirectParameters_log_six_thousand] : 2*log 6000+8 ≤ 26)
  nlinarith

end OeisA113258.Direct
end

section
namespace OeisA113258.Direct

/- The positive logarithmic discrepancy bound needed for the direct cutoff. -/
def LogBound : Prop :=
  ∀ (H p b : ℕ), 3000 ≤ p → 3 ≤ b → p.Coprime H →
    0 < (p:ℝ)*Real.log b - H*Real.log 2 →
      -(0.81:ℝ)*(6*(rows p : ℝ)^2+2*rows p)*Real.log b <
        Real.log ((p:ℝ)*Real.log b-H*Real.log 2)

end OeisA113258.Direct
end

section
namespace OeisA113258.Direct
open Real

/- An upper estimate for a logarithmic discrepancy from a certified integer gap. -/
theorem discrepancy_of_gap {N F p b : ℕ} (hb : 3 ≤ b)
    (hF : 4*F ≤ N)
    (hlo : (2:ℕ)^N < b^p) (hhi : b^p < 2^N+2^(4*F)) :
    let L : ℝ := (p:ℝ)*log b - N*log 2
    0 < L ∧ log L < ((4:ℝ)*F - N)*log 2 ∧ (p:ℝ)*log b < (N+1)*log 2 := by
  dsimp only
  have hB : 0 < (b:ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hS : 0 < (2:ℝ)^N := by positivity
  have hT : 0 < (2:ℝ)^(4*F) := by positivity
  have hY : 0 < (b:ℝ)^p := by positivity
  have low : (2:ℝ)^N < (b:ℝ)^p := by exact_mod_cast hlo
  have high : (b:ℝ)^p < 2^N + 2^(4*F) := by exact_mod_cast hhi
  have small : (2:ℝ)^(4*F) ≤ 2^N := pow_le_pow_right₀ (by norm_num) hF
  have high2 : (b:ℝ)^p < 2^(N+1) := by rw [pow_succ]; linarith
  have lp := Real.log_lt_log hS low
  rw [Real.log_pow,Real.log_pow] at lp
  have lu := Real.log_lt_log hY high2
  rw [Real.log_pow, Real.log_pow, Nat.cast_add, Nat.cast_one] at lu
  refine ⟨sub_pos.mpr lp, ?_, lu⟩
  have hratio : log ((b:ℝ)^p / 2^N) = (p:ℝ)*log b - N*log 2 := by
    rw [Real.log_div hY.ne' hS.ne', Real.log_pow, Real.log_pow]
  have hinc := Real.log_le_sub_one_of_pos (div_pos hY hS)
  rw [hratio] at hinc
  have hratio' : (b:ℝ)^p / 2^N - 1 < (2:ℝ)^(4*F) / 2^N := by
    rw [sub_lt_iff_lt_add]
    calc
      (b:ℝ)^p / 2^N < ((2:ℝ)^(4*F) + 2^N) / 2^N := div_lt_div_of_pos_right (by linarith) hS
      _ = _ := by rw [add_div, div_self hS.ne']
  have l2 := Real.log_lt_log (sub_pos.mpr lp) (hinc.trans_lt hratio')
  rw [Real.log_div hT.ne' hS.ne', Real.log_pow, Real.log_pow, Nat.cast_mul,
    Nat.cast_ofNat] at l2
  linarith

end OeisA113258.Direct
end

section
namespace OeisA113258.Direct
open Real

/- A logarithmic lower bound is incompatible with a factorial exponential gap
as soon as the determinant size falls below the stated fraction of p−1. -/
theorem endpoint_contradiction (h : LogBound) {N F p b : ℕ} {d : ℝ}
    (hthree : 3000 ≤ p) (hb : 3 ≤ b) (hc : p.Coprime N) (hd : 0 ≤ d)
    (hsize : d*N ≤ (N:ℝ)-4*F)
    (hrows : 0.81*(6*(rows p:ℝ)^2+2*rows p) < d*((p:ℝ)-1))
    (hF : 4*F ≤ N) (hlo : (2:ℕ)^N < b^p) (hhi : b^p < 2^N+2^(4*F)) : False := by
  obtain ⟨hpos,hgap,hup⟩ := discrepancy_of_gap hb hF hlo hhi
  have hl := h N p b hthree hb hc hpos
  have h2 : (0:ℝ) < log 2 := Real.log_pos (by norm_num)
  have h2b : log 2 ≤ log (b:ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2≤b))
  have hb0 := h2.trans_le h2b
  have hbp : ((p:ℝ)-1)*log b ≤ (N:ℝ)*log 2 := by linarith only [hup,h2b]
  have hchain := calc
    0.81*(6*(rows p:ℝ)^2+2*rows p)*log b < (d*((p:ℝ)-1))*log b :=
      mul_lt_mul_of_pos_right hrows hb0
    _ = d*(((p:ℝ)-1)*log b) := by ring
    _ ≤ d*((N:ℝ)*log 2) := mul_le_mul_of_nonneg_left hbp hd
    _ = (d*N)*log 2 := by ring
    _ ≤ ((N:ℝ)-4*F)*log 2 := mul_le_mul_of_nonneg_right hsize h2.le
  linarith only [hl,hgap,hchain]

end OeisA113258.Direct
end

section
namespace OeisA113258.ValEval
def powAux (m b : Nat) : Nat → Nat → Nat
  | 0, _ => 1 % m
  | k+1, e =>
    if e = 0 then 1 % m else
      let s := (powAux m b k (e/2))^2
      if e%2 = 0 then s % m else s*b % m

def powMod (m b e : Nat) : Nat := powAux m b e e

def factStream (m : Nat) : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | k+1, i, f =>
    let g := (i+1)*f % m
    g :: factStream m k (i+1) g

def residueTerms (m d n : Nat) : List Nat :=
  List.zipWith (powMod m) (factStream m n 0 (1%m)) (factStream d n 0 (1%d)).reverse

def rawResidue (m d n : Nat) : Nat := (residueTerms m d n).sum % m

def check (n q : Nat) : Bool :=
  match rawResidue (q^2) (q*(q-1)) n with
  | 0 => false
  | k+1 => (k+1)%q == 0

end OeisA113258.ValEval
end

section
namespace OeisA113258.ValEval

theorem powAux_eq (m b : Nat) : ∀ k e : Nat, e ≤ k → powAux m b k e = b^e % m := by
  intro k
  induction k with
  | zero => intro e h; have := Nat.eq_zero_of_le_zero h; subst e; rfl
  | succ k ih =>
    intro e h
    rw [powAux]
    split
    · rename_i hz; subst e; simp
    · rename_i hz
      rw [ih (e/2) (by omega)]
      split
      · rename_i he
        conv_rhs => rw [show e = (e/2)*2 by omega, pow_mul]
        exact (Nat.pow_mod _ _ _).symm
      · rename_i he
        conv_rhs => rw [show e = (e/2)*2+1 by omega, pow_succ, pow_mul]
        rw [Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod]

theorem powMod_eq (m b e : Nat) : powMod m b e = b^e % m :=
  powAux_eq m b e e (le_refl _)

theorem factStream_eq (m : Nat) (k i : Nat) :
    factStream m k i (i.factorial%m) =
    List.ofFn (fun x : Fin k => (i+1+x.val).factorial % m) := by
  induction k generalizing i with
  | zero => simp [factStream]
  | succ k ih =>
    rw [factStream, List.ofFn_succ]
    have hg : (i+1)*(i.factorial%m)%m = (i+1).factorial%m := by
      rw [Nat.factorial_succ, Nat.mul_mod_mod]
    rw [hg, ih]
    simp only [Fin.val_zero, Nat.add_zero, List.cons.injEq, true_and]
    congr 1
    funext j
    congr 2
    simp only [Fin.val_succ]
    omega

theorem residueTerms_eq (m d n : Nat) :
    residueTerms m d n = List.ofFn (fun i : Fin n =>
      powMod m ((i.val+1).factorial%m) ((n-i.val).factorial%d)) := by
  unfold residueTerms
  rw [← Nat.factorial_zero, factStream_eq, factStream_eq]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_zipWith, List.getElem_ofFn, List.getElem_reverse, List.length_ofFn]
    have hii : i < n := by simpa using hj
    simp only [Nat.factorial_zero, Nat.zero_add]
    have he : 1 + (n-1-i) = n-i := by omega
    rw [Nat.add_comm 1 i, he]

theorem rawResidue_eq (m d n : Nat)
    (hc : ∀ i : Fin n, (((i.val+1).factorial : Nat) : ZMod m)^d = 1) :
    rawResidue m d n =
      (∑ i ∈ Finset.range n, (i+1).factorial ^ (n-i).factorial)%m := by
  unfold rawResidue
  rw [residueTerms_eq, List.sum_ofFn, ← Fin.sum_univ_eq_sum_range]
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [powMod_eq, ZMod.natCast_mod, Nat.cast_pow, ZMod.natCast_mod,
      ← pow_eq_pow_mod _ (hc i)]

def seq (n : Nat) : Nat := ∑ i ∈ Finset.range n, (i+1).factorial ^ (n-i).factorial

/- Evaluate the exact sequence in the upstream statement for a prime q above the index. -/
theorem squareResidue_eq {q n : Nat} (hq : q.Prime) (hnq : n < q) :
    rawResidue (q^2) (q*(q-1)) n = seq n % (q^2) := by
  apply rawResidue_eq
  intro i
  have hc : (i.val+1).factorial.Coprime q :=
    (hq.coprime_iff_not_dvd.mpr (by rw [hq.dvd_factorial]; omega)).symm
  have hm := (ZMod.natCast_eq_natCast_iff _ _ (q^2)).mpr (Nat.ModEq.pow_totient (hc.pow_right 2))
  simpa [Nat.totient_prime_pow_succ hq] using hm

/- A witness with a single factor q automatically handles every p at its index. -/
theorem not_power_of_squareResidue {q n : Nat} (hq : q.Prime) (hnq : n < q)
    (hz : rawResidue (q^2) (q*(q-1)) n ≠ 0)
    (hd : q ∣ rawResidue (q^2) (q*(q-1)) n)
    {p b : Nat} (hp : 2 ≤ p) : seq n ≠ b^p := by
  rw [squareResidue_eq hq hnq] at hz hd
  have hqq : q ∣ q^2 := by exact dvd_pow_self _ (by decide)
  have hdiv : q ∣ seq n := (Nat.dvd_mod_iff hqq).1 hd
  intro he
  rw [he] at hdiv
  have hq2 := pow_dvd_pow_of_dvd_of_le (hq.dvd_of_dvd_pow hdiv) hp
  exact hz (Nat.mod_eq_zero_of_dvd (he ▸ hq2))



end OeisA113258.ValEval
end

section
namespace OeisA113258.ValEval
def rows0 : List (Nat × Nat) := [(9,113),(10,11069)]
theorem checked0 : rows0.all (fun x => check x.1 x.2) = true := by decide +kernel
end OeisA113258.ValEval
end

section
namespace OeisA113258.ValEval
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valCheck_sound {n q : Nat} (hp : q.Prime) (hn : n<q) (hc : ValEval.check n q = true)
    {e b : Nat} (he : 2 ≤ e) : seq n ≠ b^e := by
  unfold ValEval.check at hc
  cases h : rawResidue (q^2) (q*(q-1)) n with
  | zero => simp [h] at hc
  | succ k =>
    have hk : (k+1)%q = 0 := by simpa only [h, beq_iff_eq] using hc
    apply not_power_of_squareResidue hp hn _ _ he
    · rw [h]; exact Nat.succ_ne_zero _
    · rw [h]; exact Nat.dvd_of_mod_eq_zero hk
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def isPrimeTrial (q : Nat) : Bool :=
  decide (2 ≤ q) && (List.range (q.sqrt+1)).all (fun d => decide (d < 2 ∨ q%d ≠ 0))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem isPrimeTrial_sound {q : Nat} (h : isPrimeTrial q = true) : q.Prime := by
  rcases Bool.and_eq_true_iff.mp h with ⟨h1,h2⟩
  refine Nat.prime_def_le_sqrt.mpr ⟨of_decide_eq_true h1, ?_⟩
  intro d hd hq hdvd
  have hle : d < q.sqrt+1 := by omega
  have := List.all_eq_true.mp h2 d (List.mem_range.mpr hle)
  have hr : d<2 ∨ q%d ≠ 0 := of_decide_eq_true this
  exact (hr.resolve_left (by omega)) (Nat.mod_eq_zero_of_dvd hdvd)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def tableWellFormed (xs : List (Nat × Nat)) : Bool :=
  xs.all (fun x => isPrimeTrial x.2 && decide (x.1<x.2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem notPower_of_valuationTable (rows : List (Nat × Nat))
    (arith : rows.all (fun x => ValEval.check x.1 x.2) = true)
    (domain : tableWellFormed rows = true)
    {n q : Nat} (hmem : (n,q) ∈ rows) {e b : Nat} (he : 2 ≤ e) :
    (∑ i ∈ Finset.range n, (i+1).factorial ^ (n-i).factorial) ≠ b^e := by
  have ha := List.all_eq_true.mp arith (n,q) hmem
  have ht := List.all_eq_true.mp domain (n,q) hmem
  have hh := Bool.and_eq_true_iff.mp ht
  have ht' : q.Prime ∧ n < q := ⟨isPrimeTrial_sound hh.1, of_decide_eq_true hh.2⟩
  exact valCheck_sound ht'.1 ht'.2 ha he

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem firstValuationTable_correct {n q : Nat} (hmem : (n,q) ∈ ValEval.rows0)
    {e b : Nat} (he : 2 ≤ e) :
    (∑ i ∈ Finset.range n, (i+1).factorial ^ (n-i).factorial) ≠ b^e :=
  notPower_of_valuationTable _ ValEval.checked0 (by decide +kernel) hmem he

end OeisA113258.ValEval
end

section
/- Reduction of the A113258 exponent cutoff to the direct determinant inequality. -/
namespace OeisA113258.Direct
open Real

private theorem DirectSequence_odd_partial_sum (n t : ℕ) : Odd (FactorialSeries.partialSum n (t+1)) := by
  induction t with
  | zero => simp [FactorialSeries.partialSum]
  | succ t ih =>
    change Odd (FactorialSeries.partialSum n (t+1) + (t+2).factorial ^ (n-(t+1)).factorial)
    apply ih.add_even
    apply Even.pow_of_ne_zero _ (Nat.factorial_pos _).ne'
    exact even_iff_two_dvd.mpr (Nat.dvd_factorial (by decide) (by omega))

/- The direct logarithmic estimate supplies the complete finite exponent cutoff. -/
theorem analyticCutoff_of_logBound (h : LogBound) : AnalyticCutoff := by
  intro n p b hn hp hab
  by_cases hsmall : n ≤ 10
  · have hor : n = 9 ∨ n = 10 := by omega
    rcases hor with rfl | rfl
    · exact False.elim (ValEval.firstValuationTable_correct (n:=9) (q:=113) (by decide +kernel) hp.two_le hab)
    · exact False.elim (ValEval.firstValuationTable_correct (n:=10) (q:=11069) (by decide +kernel) hp.two_le hab)
  have hnp := exponent_factors_ge_index (by omega : 4 < n) hp (dvd_refl p) hp.two_le hab
  have hterm : FactorialSeries.term n = a n := by
    simp only [FactorialSeries.term, FactorialSeries.partialSum_eq, a]
  have ht : Odd (FactorialSeries.term n) := by
    simpa only [show n-1+1 = n by omega, FactorialSeries.term] using DirectSequence_odd_partial_sum n (n-1)
  rw [hterm, hab] at ht
  have hodd := (Nat.odd_pow_iff hp.ne_zero).mp ht
  obtain ⟨hlo,hi⟩ := FactorialSeries.gap_bounds hn
  rw [hterm, hab] at hlo hi
  have hbase : 1 < b := by
    by_contra! hb
    have hsmall := Nat.pow_le_pow_left hb p
    simp only [one_pow] at hsmall
    have hpos : 0 < 2^(n-1).factorial := by positivity
    omega
  have hb : 3 ≤ b := by obtain ⟨k,hk⟩ := hodd; omega
  have hc : p.Coprime (n-1).factorial := hp.coprime_iff_not_dvd.mpr (by
    rw [hp.dvd_factorial]; omega)
  have hfac : (n-1).factorial = (n-1)*(n-2).factorial := by
    rw [show n-1 = n-2+1 by omega, Nat.factorial_succ]
  have hten : 10*(n-2).factorial ≤ (n-1).factorial := by
    rw [hfac]; exact Nat.mul_le_mul_right _ (by omega)
  have hfour : 4*(n-2).factorial ≤ (n-1).factorial := by omega
  constructor
  · by_contra! hp6
    have hr : 6000 ≤ (p:ℝ) := by exact_mod_cast hp6
    have htR : 10*((n-2).factorial:ℝ) ≤ (n-1).factorial := by exact_mod_cast hten
    exact endpoint_contradiction h (by omega) hb hc (by norm_num : (0:ℝ)≤0.6)
      (by linarith only [htR]) (endpoint_large hr) hfour hlo hi
  · by_cases h100 : n ≤ 100
    · exact Or.inr h100
    left
    by_contra! hp3
    have hr : 3000 ≤ (p:ℝ) := by exact_mod_cast hp3
    have hhundred : 100*(n-2).factorial ≤ (n-1).factorial := by
      rw [hfac]; exact Nat.mul_le_mul_right _ (by omega)
    have htR : 100*((n-2).factorial:ℝ) ≤ (n-1).factorial := by exact_mod_cast hhundred
    exact endpoint_contradiction h hp3 hb hc (by norm_num : (0:ℝ)≤0.96)
      (by linarith only [htR]) (endpoint_small hr) hfour hlo hi

/- Published-problem statement reduced to the direct logarithm inequality and finite residues. -/
end OeisA113258.Direct
end

section
open Real
namespace OeisA113258.Direct

private theorem DirectAdmissible_logK_small {K : ℝ} (hK : 100 ≤ K) : log K ≤ K/20 := by
  have h100 : log (100:ℝ) < 5 := by
    rw [show (100:ℝ) = (2*5)^2 by norm_num, log_pow, log_mul (by norm_num) (by norm_num)]
    norm_num1
    linarith [Real.log_two_lt_d9, log_five_bounds.2]
  have hr := Real.log_le_sub_one_of_pos (by linarith : 0 < K/100)
  rw [Real.log_div (by linarith) (by norm_num)] at hr
  linarith

/- A conservative upper bound for the normalized contribution of N!, where
N=KL, and the exp(N) cost from summing the Taylor terms. -/
private theorem DirectAdmissible_log_dimension_overhead {K L : ℝ} (hK : 100 ≤ K) (hL : 0 < L) (hle : L ≤ K) :
    (2*log (K*L)+2)/K ≤ 0.22 := by
  have hK0 : 0 < K := by linarith
  have hl := Real.log_le_log hL hle
  rw [Real.log_mul hK0.ne' hL.ne']
  apply (div_le_iff₀ hK0).mpr
  linarith [DirectAdmissible_logK_small hK]

/- Establish the strict determinant parameter inequality after normalization.
Here v=log b, H=(n−1)!, B=((R−1)p+(S−1)H)/2, S=2L, R≤K/2+L.
The parameter F is log of the product of j! for j<K. -/
theorem parameter_inequality {p H v K L R F B : ℝ}
    (hp : 3000 ≤ p) (hv : 1 ≤ v) (hL : 17 ≤ L) (hlog : 2*log p+7 ≤ L)
    (hK : 6*L*v ≤ K) (hR : 0<R) (hRK : R ≤ K/2+L)
    (hH : H*log 2 ≤ p*v) (hB : 0<B)
    (hBval : 2*B ≤ R*p + 2*L*H)
    (hfac : K*(K-1)*log K - 2*K*(K-1) ≤ 2*F) :
    K*(7/8*L-1)*log 5 >
      2*log (K*L)+2 + (K-1)*log B - 2/K*F +
      (1/4 - K/(24*R))*L*(R*(6*log 2) + 2*L*(6*v)) := by
  have hL0 : 0 < L := by linarith
  have hP0 : 0 < p := by linarith
  have h6 : 6*L ≤ K := by nlinarith [mul_nonneg hL0.le (by linarith : 0 ≤ v-1)]
  have hK0 : 0 < K := by linarith
  have hRmax : R ≤ 2/3*K := by linarith
  have hcor : 1/4 - K/(24*R) ≤ 3/16 := by
    have hh : 1/16 ≤ K/(24*R) := (le_div_iff₀ (by positivity)).mpr (by linarith)
    linarith
  have harg : 0 ≤ L*(R*(6*log 2)+2*L*(6*v)) := by
    have hl := Real.log_two_gt_d9
    positivity
  have hlog2 : log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  have hsum : R*(6*log 2) + 2*L*(6*v) ≤ 4.8*K := by
    nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hlog2)]
  have hg : (1/4 - K/(24*R))*L*(R*(6*log 2) + 2*L*(6*v)) ≤ 0.9*K*L := by
    have h := mul_le_mul_of_nonneg_right hcor harg
    have h' := mul_le_mul_of_nonneg_left hsum hL0.le
    nlinarith only [h,h']
  have hH' : H ≤ 1.5*p*v := by
    by_cases hh : 0 ≤ H
    · nlinarith [mul_nonneg hh (sub_nonneg.mpr (le_of_lt (by linarith [Real.log_two_gt_d9] : 2/3<log 2)))]
    · have hpos : 0 ≤ p*v := mul_nonneg hP0.le (by linarith)
      linarith
  have hB' : B ≤ (3/5)*K*p := by
    have he := mul_le_mul_of_nonneg_right hRmax hP0.le
    have hf := mul_le_mul_of_nonneg_left hH' hL0.le
    have hj := mul_le_mul_of_nonneg_right hK hP0.le
    have hkp := mul_pos hK0 hP0
    nlinarith only [he,hf,hj,hBval,hkp]
  have hlogB : log B ≤ log K + log p-0.4 := by
    have hh := Real.log_le_log hB hB'
    rw [Real.log_mul (by positivity) hP0.ne',Real.log_mul (by norm_num) hK0.ne'] at hh
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3/5)]
  have hFI : (K-1)*log K-2*(K-1) ≤ 2/K*F := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hK0).mpr (by linarith only [hfac])
  have hK100 : 100 ≤ K := by linarith
  have hOF := (div_le_iff₀ hK0).mp (DirectAdmissible_log_dimension_overhead hK100 hL0 (by linarith))
  have hcoeff := mul_le_mul_of_nonneg_left hlogB (by linarith : 0 ≤ K-1)
  have hlogp : 0.4 ≤ log p := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : 2≤p)
    linarith [Real.log_two_gt_d9]
  have hcut : (7/8*L-1)*log 5 > 0.9*L+log p+1.82 := by
    have q₁ := mul_le_mul_of_nonneg_left (log_five_bounds.1.le) hL0.le
    nlinarith [log_five_bounds.2]
  have hfinish := mul_lt_mul_of_pos_left hcut hK0
  nlinarith only [hfinish,hOF,hcoeff,hFI,hg,hlogp]

end OeisA113258.Direct
end

section
namespace OeisA113258.Analysis
open Real Finset

/- A single factorial dominates the corresponding term in the exponential series. -/
theorem log_factorial_lower (j : ℕ) (hj : 0 < j) :
    (j:ℝ)*log j-j ≤ log (j.factorial : ℝ) := by
  have hjp : 0 < (j:ℝ) := by exact_mod_cast hj
  have hfp : 0 < (j.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos j
  have h := Real.log_le_log (by positivity) (Real.pow_div_factorial_le_exp (x:=(j:ℝ)) (by positivity) j)
  rw [Real.log_div (by positivity) hfp.ne', Real.log_pow, Real.log_exp] at h
  linarith

/- Uniform factorial lower bound with a common logarithm on each summand. -/
theorem log_factorial_lower_at (j K : ℕ) (hj : 0 < j) (hK : 0 < K) :
    (j:ℝ)*log K-K ≤ log (j.factorial:ℝ) := by
  have hjp : 0 < (j:ℝ) := by exact_mod_cast hj
  have hKp : 0 < (K:ℝ) := by exact_mod_cast hK
  have h := Real.log_le_sub_one_of_pos (show 0 < (K:ℝ)/j by positivity)
  rw [Real.log_div hKp.ne' hjp.ne'] at h
  have hm := mul_le_mul_of_nonneg_right h hjp.le
  simp only [sub_mul, div_mul_cancel₀ _ hjp.ne', one_mul] at hm
  nlinarith [log_factorial_lower j hj]

/- Twice the logarithm of the product of the factorials 0!,..., (K−1)!. -/
theorem log_product_factorials_lower (K : ℕ) (hK : 1 ≤ K) :
    (K:ℝ)*(K-1)*log K-2*(K:ℝ)*(K-1) ≤ 2*log (∏ j ∈ range K, (j.factorial : ℝ)) := by
  cases K with
  | zero => omega
  | succ k =>
    rw [Real.log_prod (fun i _ => (show (i.factorial:ℝ) ≠ 0 by positivity)), Finset.sum_range_succ']
    simp only [Nat.factorial_zero, Nat.cast_one, Real.log_one, add_zero]
    have ht : 2*(∑ j ∈ range k, ((j:ℝ)+1)) = (k:ℝ)*(k+1) := by
      induction k with
      | zero => simp
      | succ q ih => rw [Finset.sum_range_succ]; push_cast; linarith [ih (by omega)]
    have hs := Finset.sum_le_sum (s:=range k) (fun j _ => log_factorial_lower_at (j+1) (k+1) (by omega) (by omega))
    simp only [Nat.cast_add, Nat.cast_one, Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul] at hs
    push_cast
    nlinarith [congrArg (fun x : ℝ => x * log ((k:ℝ)+1)) ht]

end OeisA113258.Analysis
end

section
open Real Finset
namespace OeisA113258.Direct

theorem seventeen_rows {p : ℝ} (hp : 3000 ≤ p) : 17 ≤ (rows p : ℝ) := by
  have h : log ((3:ℝ)^5) ≤ log p := Real.log_le_log (by positivity) (by norm_num; linarith)
  rw [log_pow] at h
  norm_num1 at h
  linarith [(rows_bounds (by linarith : 1≤p)).1, Real.log_three_gt_d9]

theorem row_square {p : ℝ} (hp : 3000 ≤ p) : (rows p : ℝ)^2 ≤ p := by
  have hz : 0 ≤ (rows p : ℝ) := by positivity
  nlinarith [endpoint_small hp]

noncomputable def radiusScale (p H R L : ℕ) : ℝ :=
  ((p:ℝ)*((R:ℝ)-1) + (H:ℝ)*(2*(L:ℝ)-1))/2

/- This is the actual parameter premise of the specialized determinant bound.
The polynomial grid uses R=L+J−1, S=2L, K=2J. -/
theorem parameters_for_sequence (p H b : ℕ) (hp : 3000 ≤ p) (hb : 3 ≤ b)
    (horder : (H:ℝ)*log 2 ≤ p*log b) :
    let L := rows p
    let J := halfColumns L (log b)
    let K := 2*J
    let R := L+J-1
    let B := radiusScale p H R L
    0<J ∧ 0<L ∧ 1<R ∧ 2*L ≤ p ∧ 0<B ∧
    (K:ℝ)*(7/8*(L:ℝ)-1)*log 5 >
      2*log ((K:ℝ)*L)+2+((K:ℝ)-1)*log B -
      2/(K:ℝ)*(∑ j ∈ range K, log (j.factorial:ℝ)) +
      (1/4-(K:ℝ)/(24*R))*L*((R:ℝ)*(6*log 2)+2*L*(6*log b)) := by
  intro L J K R B
  have hp' : (3000:ℝ) ≤ p := by exact_mod_cast hp
  have hv : 1 ≤ log (b:ℝ) := by
    have h := log_le_log (by norm_num : (0:ℝ)<3) (by exact_mod_cast hb : (3:ℝ)≤b)
    linarith [Real.log_three_gt_d9]
  have hl : 17 ≤ (L:ℝ) := seventeen_rows hp'
  have hK : 6*(L:ℝ)*log b ≤ K := (columns_bounds L (by linarith : 0≤log b)).1
  have hKcast : (K:ℝ) = 2*(J:ℝ) := by dsimp [K]; push_cast; rfl
  have hLpos : 0<L := by exact_mod_cast (by linarith : (0:ℝ)<L)
  have hJpos : 0<J := by
    by_contra! he
    have he0 : J=0 := by omega
    rw [hKcast,he0] at hK
    norm_num1 at hK
    nlinarith [mul_nonneg (by linarith : 0 ≤ (L:ℝ)) (by linarith : 0 ≤ log b-1)]
  have hRcast : (R:ℝ) = (L:ℝ)+J-1 := by
    dsimp [R]; rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  have hRgt : 1 < R := by
    have : 1 < L := by exact_mod_cast (by linarith : (1:ℝ)<L)
    dsimp [R]; omega
  have hRgt' : (1:ℝ)<R := by exact_mod_cast hRgt
  have hs : 2*L ≤ p := by
    have hsq : (L:ℝ)^2 ≤ p := row_square hp'
    exact_mod_cast (by nlinarith [mul_nonneg (by linarith : 0≤(L:ℝ)) (by linarith : 0≤(L:ℝ)-2)] : (2:ℝ)*L≤p)
  have hBpos : 0<B := by
    dsimp only [B,radiusScale]; have hp0 : (0:ℝ)<p := by linarith
    exact div_pos (add_pos_of_pos_of_nonneg (mul_pos hp0 (by linarith)) (mul_nonneg (Nat.cast_nonneg _) (by linarith))) (by norm_num)
  refine ⟨hJpos,hLpos,hRgt,hs,hBpos,?_⟩
  have hf := Analysis.log_product_factorials_lower K (by dsimp [K]; omega)
  rw [Real.log_prod (fun j _ => by exact_mod_cast (Nat.factorial_pos j).ne')] at hf
  apply parameter_inequality (H := (H:ℝ)) hp' hv hl (rows_bounds (by linarith : 1≤(p:ℝ))).1 hK (by linarith) (by linarith) horder hBpos _ hf
  dsimp only [B,radiusScale]
  nlinarith [Nat.cast_nonneg (α:=ℝ) H]

end OeisA113258.Direct
end

section
/- A zero estimate for the product of the additive and multiplicative groups.
Translating the polynomial in its first coordinate preserves every column's
leading coefficient. The leading coefficient matrix is a scaled Vandermonde. -/
open Finset Polynomial Matrix
namespace LaurentTwoLog
variable {F : Type*} [Field F] {L : ℕ}

private theorem ZeroEstimate_coeff_det_columns (A : Matrix (Fin L) (Fin L) F[X])
    (d : Fin L → ℕ) (hn : ∀ i j, A i j ≠ 0)
    (hd : ∀ i j, (A i j).natDegree = d j) :
    A.det.coeff (∑ j, d j) = (Matrix.of fun i j => (A i j).leadingCoeff).det := by
  classical
  rw [Matrix.det_apply, finsetSum_coeff, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro g _
  rw [coeff_smul]
  congr 1
  have h : (∏ j, A (g j) j).natDegree = ∑ j, d j := by
    rw [natDegree_prod]
    · simp only [hd]
    · exact fun j _ => hn _ _
  rw [← h, ← leadingCoeff, leadingCoeff_prod]
  rfl

private theorem ZeroEstimate_degree_det_columns (A : Matrix (Fin L) (Fin L) F[X])
    (d : Fin L → ℕ) (hd : ∀ i j, (A i j).natDegree ≤ d j) :
    A.det.natDegree ≤ ∑ j, d j := by
  classical
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro g _
  exact (natDegree_smul_le _ _).trans ((natDegree_prod_le _ _).trans
    (Finset.sum_le_sum fun j _ => hd _ j))

/- A polynomial of partial degrees at most d and less than L cannot vanish
on every sum of two sets of points in Ga × Gm when the first set has L
distinct multiplicative coordinates and the second has more than Ld
distinct additive coordinates. -/
theorem additive_multiplicative_zero_estimate {ι : Type*} [Fintype ι]
    (d : ℕ) (x y : Fin L → F) (t u : ι → F)
    (hy : Function.Injective y) (hy0 : ∀ i, y i ≠ 0)
    (ht : Function.Injective t) (hu : ∀ j, u j ≠ 0)
    (hcard : L*d < Fintype.card ι)
    (p : Fin L → F[X]) (hdeg : ∀ j, (p j).natDegree ≤ d)
    (hvan : ∀ i k, ∑ j, (p j).eval (t k+x i) * (y i*u k)^j.val = 0) :
    ∀ j, p j = 0 := by
  classical
  by_contra! hn
  obtain ⟨z,hz⟩ := hn
  let q (j : Fin L) : F[X] := if p j = 0 then 1 else p j
  have hq (j) : q j ≠ 0 := by simp [q]; split <;> simp_all
  have hqd (j) : (q j).natDegree ≤ d := by
    by_cases h : p j = 0 <;> simp [q,h,hdeg]
  let A : Matrix (Fin L) (Fin L) F[X] := Matrix.of fun i j =>
    C (y i ^ j.val) * taylor (x i) (q j)
  have ha (i j) : A i j ≠ 0 := by
    change C _ * _ ≠ 0
    simp [hy0,hq]
  have hdegA (i j) : (A i j).natDegree = (q j).natDegree := by
    change (C _ * _).natDegree = _
    rw [natDegree_C_mul (pow_ne_zero _ (hy0 i))]
    exact natDegree_taylor _ _
  have hnz : A.det ≠ 0 := by
    intro he
    have hc := ZeroEstimate_coeff_det_columns A (fun j => (q j).natDegree) ha hdegA
    rw [he] at hc
    have hmat : (Matrix.of fun i j => (A i j).leadingCoeff) =
        Matrix.of (fun i j => (q j).leadingCoeff * Matrix.vandermonde y i j) := by
      ext i j
      simp [A, leadingCoeff_mul, mul_comm, Matrix.vandermonde_apply]
    rw [hmat, Matrix.det_mul_row (fun j => (q j).leadingCoeff) (Matrix.vandermonde y)] at hc
    have hprod : (∏ j, (q j).leadingCoeff) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => leadingCoeff_ne_zero.mpr (hq j))
    exact (mul_ne_zero hprod (Matrix.det_vandermonde_ne_zero_iff.mpr hy)) (by simpa using hc.symm)
  apply hnz
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero A.det ht
  · intro k
    change (evalRingHom (t k)) A.det = 0
    rw [RingHom.map_det]
    by_contra h
    let w (j : Fin L) := if p j = 0 then (0 : F) else (u k)^j.val
    have hw : (A.map (evalRingHom (t k))).mulVec w = 0 := by
      funext i
      change ∑ j : Fin L, (evalRingHom (t k)) (A i j) * w j = (0 : F)
      rw [← hvan i k]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : p j = 0
      · simp [A,w,q,hj]
      · simp [A,w,q,hj,taylor_eval,mul_pow,mul_comm,mul_left_comm,mul_assoc]
    have zero := congrFun (Matrix.eq_zero_of_mulVec_eq_zero h hw) z
    simp [w,hz,hu] at zero
  · refine lt_of_le_of_lt ((ZeroEstimate_degree_det_columns A _ (fun i j => (hdegA i j).le)).trans ?_) hcard
    calc
      ∑ j, (q j).natDegree ≤ ∑ _j : Fin L, d := Finset.sum_le_sum fun j _ => hqd j
      _ = L*d := by simp

end LaurentTwoLog
end

section
open Finset Polynomial Matrix
namespace LaurentTwoLog

/- Express the Newton binomial basis over the rationals. -/
private noncomputable def BinomialRank_newtonCombination {K : ℕ} (c : Fin K → ℚ) : ℚ[X] :=
  ∑ j, C (c j / (j.val.factorial : ℚ)) * descPochhammer ℚ j.val

private theorem BinomialRank_newton_degree {K : ℕ} (c : Fin K → ℚ) :
    (BinomialRank_newtonCombination c).natDegree ≤ K-1 := by
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_C_mul_le _ _).trans ((descPochhammer_natDegree ℚ j.val).le.trans (by omega))

private theorem BinomialRank_newton_eval {K : ℕ} (c : Fin K → ℚ) (n : ℕ) :
    (BinomialRank_newtonCombination c).eval (n : ℚ) = ∑ j, c j * (n.choose j.val : ℚ) := by
  simp only [BinomialRank_newtonCombination, eval_finsetSum, eval_mul, eval_C, Nat.cast_choose_eq_descPochhammer_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/- At 0,1,... the matrix of binomial coefficients is triangular with diagonal one. -/
private theorem BinomialRank_newton_injective {K : ℕ} (c : Fin K → ℚ) (h : BinomialRank_newtonCombination c = 0) :
    ∀ j, c j = 0 := by
  suffices hs : ∀ n, ∀ hn : n < K, c ⟨n,hn⟩ = 0 from fun j => hs j.val j.isLt
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    let z : Fin K := ⟨n,hn⟩
    have he := BinomialRank_newton_eval c n
    rw [h,eval_zero] at he
    have hs : (∑ j : Fin K, c j * (n.choose j.val : ℚ)) =
        c z * (n.choose z.val : ℚ) := by
      apply Finset.sum_eq_single z
      · intro j _ hne
        have hne' : j.val ≠ n := fun hj => hne (Fin.ext hj)
        rcases lt_or_gt_of_ne hne' with hj|hj
        · simp [ih j.val hj j.isLt]
        · simp [Nat.choose_eq_zero_of_lt hj]
      · simp
    rw [hs] at he
    simpa [z] using he.symm

/- Coefficient-vector form of the LMN rank estimate. The selected grids may
have arbitrary shapes. The first has distinct powers, the second distinct
linear arguments. Over their sum the binomial interpolation rows are independent. -/
theorem binomial_grid_coefficients {ι : Type*} [Fintype ι] {L K : ℕ}
    (x : Fin L → ℕ) (y : Fin L → ℚ) (t : ι → ℕ) (u : ι → ℚ)
    (hy : Function.Injective y) (hy0 : ∀ i, y i ≠ 0)
    (ht : Function.Injective t) (hu : ∀ j, u j ≠ 0)
    (hcard : L*(K-1) < Fintype.card ι) (c : Fin L → Fin K → ℚ)
    (h : ∀ i k, ∑ l, ∑ j, c l j * ((t k + x i).choose j.val : ℚ) *
                            (y i * u k)^l.val = 0) : ∀ l j, c l j = 0 := by
  have ht' : Function.Injective (fun k => (t k : ℚ)) :=
    ((Nat.cast_injective (R := ℚ)).comp ht)
  have hp := additive_multiplicative_zero_estimate (K-1) (fun i => (x i : ℚ)) y
    (fun k => (t k : ℚ)) u hy hy0 ht' hu hcard (fun l => BinomialRank_newtonCombination (c l))
    (fun l => BinomialRank_newton_degree _) (by
      intro i k
      simpa only [← Nat.cast_add, BinomialRank_newton_eval, Finset.sum_mul] using h i k)
  exact fun l => BinomialRank_newton_injective _ (hp l)

end LaurentTwoLog
end

section
open Matrix Set Submodule Module
namespace LaurentTwoLog

/- A full-row-rank matrix contains a nonsingular square minor using every row. -/
theorem select_nonsingular_minor {F m n : Type*} [Field F] [Fintype m] [DecidableEq m]
    [Fintype n] (A : Matrix m n F) (h : LinearIndependent F A.row) :
    ∃ g : m → n, Function.Injective g ∧ (A.submatrix id g).det ≠ 0 := by
  classical
  have hd : finrank F (span F (range A.col)) = Fintype.card m :=
    (rank_eq_finrank_span_cols A).symm.trans h.rank_matrix
  obtain ⟨f,hf,_,hli⟩ := exists_fun_fin_finrank_span_eq F (range A.col)
  let e := (Fintype.equivFin m).trans (finCongr hd.symm)
  choose i hi using hf
  let g (j : m) := i (e j)
  have hcol : (A.submatrix id g).col = f ∘ e := by
    funext j
    exact hi (e j)
  have hi' : LinearIndependent F (A.submatrix id g).col := by
    rw [hcol]
    exact hli.comp _ e.injective
  refine ⟨g,?_,?_⟩
  · intro j k eq
    apply hi'.injective
    funext a
    change A a (g j) = A a (g k)
    rw [eq]
  · have hu := Matrix.mulVec_injective_iff_isUnit.mp (Matrix.mulVec_injective_iff.mpr hi')
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

end LaurentTwoLog
end

section
/-
# Lowest possible degree in Laurent's interpolation determinant

Formalizes the identical-row cancellation in the proof of Lemma 4 (M. Laurent,
Acta Arithmetica 133 (2008), pp. 332–333). The row function is arbitrary,
so the result applies to each row-scaled monomial in the Taylor expansion.
-/

namespace LaurentTwoLog

/- A set of (v) distinct nonnegative degrees has total at least `v.choose 2`. -/
theorem choose_card_le_sum (s : Finset ℕ) : s.card.choose 2 ≤ ∑ i ∈ s, i := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hn : a ∉ s := fun h => (ha a h).false
    have hc : s.card ≤ a := by
      simpa using Finset.card_le_card (show s ⊆ Finset.range a from
        fun i hi => Finset.mem_range.mpr (ha i hi))
    rw [Finset.card_insert_of_notMem hn, Finset.sum_insert hn, Nat.choose_succ_succ,
      Nat.choose_one_right]
    simp only [show Nat.succ 1 = 2 from rfl]
    omega

/- If the scaled interpolation coefficient is nonzero, within each group of
rows with the same exponent label the Taylor degrees must be distinct. -/
theorem taylor_degree_of_det_ne_zero
    {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [CommRing R] (label : ι → κ) (degree : ι → ℕ)
    (scale : ι → R) (row : κ → ℕ → ι → R)
    (hd : (Matrix.of (fun i j => scale i * row (label i) (degree i) j)).det ≠ 0) :
    (∑ k, ((Finset.univ.filter (fun i => label i = k)).card.choose 2)) ≤ ∑ i, degree i := by
  classical
  let M : Matrix ι ι R := Matrix.of fun i j => row (label i) (degree i) j
  have hM : M.det ≠ 0 := by
    intro h
    exact hd (by rw [show (Matrix.of (fun i j => scale i * row (label i) (degree i) j)).det =
       (∏ i, scale i) * M.det from Matrix.det_mul_column scale M, h, mul_zero])
  rw [← Finset.sum_fiberwise Finset.univ label degree]
  apply Finset.sum_le_sum
  intro k _
  let S := Finset.univ.filter fun i => label i = k
  change S.card.choose 2 ≤ ∑ i ∈ S, degree i
  have hinj : Set.InjOn degree (S : Set ι) := by
    intro i hi j hj he
    by_contra hne
    have hlabel : label i = label j :=
      (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
    exact hM (Matrix.det_zero_of_row_eq hne (by
      funext u
      change row (label i) (degree i) u = row (label j) (degree j) u
      rw [hlabel,he]))
  have h := choose_card_le_sum (S.image degree)
  rwa [Finset.card_image_of_injOn hinj, Finset.sum_image hinj] at h

end LaurentTwoLog
end

section
/-
# The integer arithmetic in Laurent's interpolation minor

Common powers of the two integer bases divide each signed permutation term of
the minor. This includes the actual matrix in Laurent's 2008 proof by taking
the scalar coefficient to be the integral binomial factor.
-/

namespace LaurentTwoLog

/- The lower exponent bounds may be proved separately, without any
coprimality assumption on the two bases. -/
theorem pow_mul_pow_dvd_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ℤ) (e f : ℕ) (u v : ι → ι → ℕ) (c : ι → ι → ℤ)
    (he : ∀ π : Equiv.Perm ι, e ≤ ∑ i, u (π i) i)
    (hf : ∀ π : Equiv.Perm ι, f ≤ ∑ i, v (π i) i) :
    a ^ e * b ^ f ∣ (Matrix.of fun i j => c i j * (a ^ u i j * b ^ v i j)).det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro π _
  apply dvd_mul_of_dvd_right
  simp only [Matrix.of_apply, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  exact dvd_mul_of_dvd_right (mul_dvd_mul (pow_dvd_pow a (he π)) (pow_dvd_pow b (hf π))) _

/- Absolute arithmetic lower bound for an actual nonzero binomial interpolation
minor of positive natural integer bases (including `2` and an odd integer). -/
theorem integer_minor_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b b₁ b₂ e f : ℕ) (l k r s : ι → ℕ)
    (he : ∀ π : Equiv.Perm ι, e ≤ ∑ i, l (π i) * r i)
    (hf : ∀ π : Equiv.Perm ι, f ≤ ∑ i, l (π i) * s i)
    (h : (Matrix.of fun i j =>
         (((r j*b₂+s j*b₁).choose (k i) : ℕ) : ℤ) *
         ((a : ℤ) ^ (l i*r j) * (b : ℤ) ^ (l i*s j))).det ≠ 0) :
    (a : ℤ)^e * (b : ℤ)^f ≤ |(Matrix.of fun i j =>
         (((r j*b₂+s j*b₁).choose (k i) : ℕ) : ℤ) *
         ((a : ℤ) ^ (l i*r j) * (b : ℤ) ^ (l i*s j))).det| :=
  Int.le_abs_of_dvd h (pow_mul_pow_dvd_det _ _ _ _ _ _ _ he hf)

end LaurentTwoLog
end

section
/- # The centered exponent bound for Laurent's integer minor -/
open Finset
namespace LaurentTwoLog

/- Distinct labels with at most `K` occurrences per value have a lower bound
on their first LaurentExponent_moment, allowing partial occupation at the last value. -/
private theorem LaurentExponent_moment_aux (K : ℝ) (c : ℕ → ℝ) (hn : ∀ j, 0 ≤ c j)
    (hc : ∀ j, c j ≤ K) (L : ℕ) :
    (∑ j ∈ range L, c j)^2 ≤ K * (∑ j ∈ range L, c j) +
      2*K*(∑ j ∈ range L, (j:ℝ)*c j) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hb : (∑ j ∈ range L, c j) ≤ (L:ℝ)*K := by
      calc
        _ ≤ ∑ _j ∈ range L, K := sum_le_sum (fun j _ => hc j)
        _ = _ := by simp
    simp only [sum_range_succ] at *
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (hn L),
      mul_nonneg (sub_nonneg.mpr (hc L)) (hn L)]

private theorem LaurentExponent_moment {ι : Type*} [DecidableEq ι] (U : Finset ι)
    (l : ι → ℕ) (K L : ℕ) (hl : ∀ i ∈ U, l i < L)
    (hK : ∀ j, (U.filter fun i => l i = j).card ≤ K) :
    (U.card:ℝ)^2 ≤ (K:ℝ)*U.card+2*K*(∑ i ∈ U, (l i:ℝ)) := by
  classical
  let c (j : ℕ) : ℝ := (U.filter fun i => l i = j).card
  have htotal : ∑ j ∈ range L, c j = (U.card:ℝ) := by
    dsimp [c]
    exact_mod_cast card_eq_sum_card_fiberwise (s := U) (t := range L) (f := l)
      (fun i hi => mem_range.mpr (hl i hi)) |>.symm
  have hfirst : ∑ j ∈ range L, (j:ℝ)*c j = ∑ i ∈ U, (l i:ℝ) := by
    rw [← sum_fiberwise_of_maps_to (s := U) (t := range L) (g := l)
      (fun i hi => mem_range.mpr (hl i hi)) (fun i => (l i : ℝ))]
    apply sum_congr rfl
    intro j _
    calc
      _ = ∑ _i ∈ U.filter (fun i => l i = j), (j:ℝ) := by simp [c,mul_comm]
      _ = _ := sum_congr rfl (fun i hi => by rw [(mem_filter.mp hi).2])
  have hh := LaurentExponent_moment_aux (K:ℝ) c (fun _ => Nat.cast_nonneg _) (fun j => by dsimp [c]; exact_mod_cast hK j) L
  rwa [htotal,hfirst] at hh

private theorem LaurentExponent_cubic_step (u v N S : ℝ) (hlo : 0 ≤ u-v) (hhi : u-v ≤ S) :
    2*((u-N/2)^3-(v-N/2)^3) ≤ 3*S*((u-N/2)^2+(v-N/2)^2) := by
  calc
    _ ≤ 3*(u-v)*((u-N/2)^2+(v-N/2)^2) := by
      nlinarith [mul_nonneg hlo (sq_nonneg (u-v))]
    _ ≤ _ := by gcongr

private theorem LaurentExponent_sum_step (f : ℕ → ℝ) (R : ℕ) :
    (∑ t ∈ range R, (f t-f (t+1))) = f 0-f R := by
  induction R with
  | zero => simp
  | succ R ih => rw [sum_range_succ, ih]; ring

/- The correction N³/(12S) follows by telescoping a cubic along the counts of
columns above successive levels, whose downward jumps are at most S. -/
private theorem LaurentExponent_tail_variance (u : ℕ → ℝ) (N S : ℝ) (R : ℕ)
    (hs : 0 < S) (h0 : u 0 = N) (hR : u R = 0)
    (hlo : ∀ t < R, 0 ≤ u t-u (t+1)) (hhi : ∀ t < R, u t-u (t+1) ≤ S) :
    (∑ t ∈ range R, (N*u (t+1)-(u (t+1))^2)) ≤
      (R:ℝ)*N^2/4 - N^3/(12*S) := by
  let P (t : ℕ) := N*u t - (u t)^2
  let F (t : ℕ) := (u t-N/2)^3
  have hsum := sum_le_sum (s := range R) (fun t ht => LaurentExponent_cubic_step (u t) (u (t+1)) N S
    (hlo t (mem_range.mp ht)) (hhi t (mem_range.mp ht)))
  have he : ∀ t, (u t-N/2)^2+(u (t+1)-N/2)^2 = N^2/2-(P t+P (t+1)) := by
    intro t; dsimp [P]; ring
  change ∑ t ∈ range R, 2*(F t-F (t+1)) ≤ _ at hsum
  simp_rw [he] at hsum
  rw [← mul_sum, LaurentExponent_sum_step, ← mul_sum, sum_sub_distrib, sum_add_distrib] at hsum
  have hbal := LaurentExponent_sum_step P R
  rw [sum_sub_distrib] at hbal
  have hP₀ : P 0 = 0 := by dsimp [P]; rw [h0]; ring
  have hPR : P R = 0 := by dsimp [P]; rw [hR]; ring
  rw [hP₀,hPR,sub_self,sub_eq_zero] at hbal
  rw [hbal] at hsum
  simp only [sum_const, card_range, nsmul_eq_mul, F, h0, hR] at hsum
  change (∑ t ∈ range R, P (t+1)) ≤ _
  field_simp [ne_of_gt hs] at *
  nlinarith

private theorem LaurentExponent_layer_sum {ι : Type*} [Fintype ι] (r : ι → ℕ)
    (R : ℕ) (hr : ∀ i, r i ≤ R) (w : ι → ℝ) :
    (∑ t ∈ range R, ∑ i ∈ univ.filter (fun i => t < r i), w i) =
        ∑ i, (r i:ℝ)*w i := by
  classical
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [← sum_filter]
  have hset : (range R).filter (fun t => t < r i) = range (r i) := by
    ext t
    simp only [mem_filter, mem_range, and_iff_right_iff_imp]
    exact fun h => h.trans_le (hr i)
  simp [hset]

/- The sharp one-coordinate exponent estimate in Laurent's arithmetic bound.
The labels represent the (L) row levels, each appearing at most (K) times.
The column coordinates repeat at most (S) times in an (R)-wide grid. -/
theorem centered_exponent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l r : ι → ℕ) (K L R S : ℕ) (hcard : Fintype.card ι = K*L)
    (hK : 0 < K) (hS : 0 < S) (hl : ∀ i, l i < L) (hr : ∀ i, r i < R)
    (hrow : ∀ j, (univ.filter fun i => l i = j).card ≤ K)
    (hcol : ∀ j, (univ.filter fun i => r i = j).card ≤ S) :
    ((L:ℝ)-1)/2 * (∑ i, (r i:ℝ)) -
      ((L:ℝ)*R*(Fintype.card ι)/8 - (L:ℝ)*(Fintype.card ι)^2/(24*S)) ≤
      ∑ i, (l i:ℝ)*(r i:ℝ) := by
  classical
  let N : ℝ := Fintype.card ι
  let U (t : ℕ) := univ.filter fun i => t ≤ r i
  let u (t : ℕ) : ℝ := (U t).card
  let W (t : ℕ) : ℝ := ∑ i ∈ U t, (l i:ℝ)
  have hKL : N = (K:ℝ)*L := by dsimp [N]; exact_mod_cast hcard
  have h0 : u 0 = N := by simp [u,U,N]
  have hR : u R = 0 := by
    have he : U R = ∅ := filter_eq_empty_iff.mpr (fun i _ => (hr i).not_ge)
    simp [u,he]
  have hlo (t : ℕ) : 0 ≤ u t-u (t+1) := by
    apply sub_nonneg.mpr
    change ((U (t+1)).card:ℝ) ≤ (U t).card
    exact_mod_cast card_le_card (show U (t+1) ⊆ U t from fun i hi =>
      mem_filter.mpr ⟨mem_univ i, Nat.le_trans (Nat.le_succ _) (mem_filter.mp hi).2⟩)
  have hhi (t : ℕ) : u t-u (t+1) ≤ S := by
    have hh : U t ⊆ U (t+1) ∪ (univ.filter fun i => r i = t) := by
      intro i hi
      have h := (mem_filter.mp hi).2
      rcases eq_or_lt_of_le h with h|h
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ i,h.symm⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ i,h⟩)
    have hc := (card_le_card hh).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left (hcol t) _))
    apply sub_le_iff_le_add.mpr
    change ((U t).card:ℝ) ≤ (S:ℝ)+(U (t+1)).card
    exact_mod_cast hc.trans_eq (Nat.add_comm _ _)
  have hbound (t : ℕ) :
         (K:ℝ)*((L:ℝ)-1)*u (t+1) - (2*K)*W (t+1) ≤ N*u (t+1)-(u (t+1))^2 := by
    have h := LaurentExponent_moment (U (t+1)) l K L (fun i _ => hl i)
      (fun j => (card_le_card (show (U (t+1)).filter (fun i => l i = j) ⊆
             univ.filter (fun i => l i = j) from
        fun i hi => mem_filter.mpr ⟨mem_univ i, (mem_filter.mp hi).2⟩)).trans (hrow j))
    change (u (t+1))^2 ≤ _ + _ * W (t+1) at h
    rw [hKL]
    change (u (t+1))^2 ≤ (K:ℝ)*u (t+1)+2*K*W (t+1) at h
    linarith only [h]
  have hm := sum_le_sum (s := range R) (fun t _ => hbound t)
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum] at hm
  have hv := LaurentExponent_tail_variance u N S R (by exact_mod_cast hS) h0 hR
    (fun t _ => hlo t) (fun t _ => hhi t)
  have hall := hm.trans hv
  have hi : (∑ t ∈ range R, u (t+1)) = ∑ i, (r i:ℝ) := by
    simpa [u,U] using LaurentExponent_layer_sum r R (fun i => (hr i).le) (fun _ => (1:ℝ))
  have hw : (∑ t ∈ range R, W (t+1)) = ∑ i, (l i:ℝ)*(r i:ℝ) := by
    simpa [W,U,mul_comm] using LaurentExponent_layer_sum r R (fun i => (hr i).le) (fun i => (l i:ℝ))
  rw [hi,hw] at hall
  change ((L:ℝ)-1)/2 * _ - ((L:ℝ)*R*N/8-(L:ℝ)*N^2/(24*S)) ≤ _
  have hid : 2*(K:ℝ)*((L:ℝ)*R*N/8-(L:ℝ)*N^2/(24*S)) =
      (R:ℝ)*N^2/4-N^3/(12*S) := by
    rw [hKL]
    ring
  rw [← hid] at hall
  apply le_of_mul_le_mul_left (a := 2*(K:ℝ)) _ (by positivity)
  linarith only [hall]

end LaurentTwoLog
end

section
/- # The arithmetic lower bound in Laurent 2008, Lemma 1, for integer bases -/

open Finset
namespace LaurentTwoLog

/- Laurent's unnormalized binomial interpolation minor. -/
def integerMinor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b b₁ b₂ : ℕ) (l k r s : ι → ℕ) : ℤ :=
  (Matrix.of fun i j => (((r j*b₂+s j*b₁).choose (k i) : ℕ) : ℤ) *
         ((a:ℤ)^(l i*r j)*(b:ℤ)^(l i*s j))).det

/- `M-G` for one coordinate, equal to the central exponent minus Laurent's
grid correction `(1/4 - N/(12*R*S))*L*R*N/2`. -/
noncomputable def lowerExponent {ι : Type*} [Fintype ι] (L R S : ℕ) (r : ι → ℕ) : ℝ :=
  ((L:ℝ)-1)/2*(∑ i, (r i:ℝ)) -
    ((L:ℝ)*R*(Fintype.card ι)/8-(L:ℝ)*(Fintype.card ι)^2/(24*S))

private theorem LaurentIntegerLower_exponent_for_perm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l r : ι → ℕ) (K L R S : ℕ) (hcard : Fintype.card ι = K*L)
    (hK : 0 < K) (hS : 0 < S) (hl : ∀ i, l i < L) (hr : ∀ i, r i < R)
    (hrow : ∀ j, (univ.filter fun i => l i = j).card ≤ K)
    (hcol : ∀ j, (univ.filter fun i => r i = j).card ≤ S)
    (π : Equiv.Perm ι) :
    ⌈lowerExponent L R S r⌉₊ ≤ ∑ i, l (π i)*r i := by
  classical
  have hp (j : ℕ) : (univ.filter fun i => l (π i)=j).card ≤ K := by
    have hh : (univ.filter (fun i => l (π i)=j)).image π = univ.filter (fun i => l i=j) := by
      ext x
      constructor
      · intro hx
        obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
        exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hz).2⟩
      · intro hx
        apply mem_image.mpr
        refine ⟨π.symm x, mem_filter.mpr ⟨mem_univ _, ?_⟩, π.apply_symm_apply x⟩
        simpa using (mem_filter.mp hx).2
    have eq := congrArg Finset.card hh
    rw [card_image_of_injective _ π.injective] at eq
    exact eq.trans_le (hrow j)
  have h := centered_exponent (fun i => l (π i)) r K L R S hcard hK hS
      (fun i => hl (π i)) hr hp hcol
  apply Nat.ceil_le.mpr
  push_cast
  exact h

/- The full centered arithmetic lower bound for a nonzero binomial
interpolation minor with positive integer bases. Row multiplicities and the
two column-coordinate multiplicities are the ones supplied by Laurent's grid. -/
theorem integer_log_minor_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b b₁ b₂ K L R S : ℕ) (l k r s : ι → ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hcard : Fintype.card ι = K*L)
    (hK : 0 < K) (hR : 0 < R) (hS : 0 < S)
    (hl : ∀ i, l i < L) (hr : ∀ i, r i < R) (hs : ∀ i, s i < S)
    (hrow : ∀ j, (univ.filter fun i => l i = j).card ≤ K)
    (hrcol : ∀ j, (univ.filter fun i => r i = j).card ≤ S)
    (hscol : ∀ j, (univ.filter fun i => s i = j).card ≤ R)
    (hdet : integerMinor a b b₁ b₂ l k r s ≠ 0) :
    lowerExponent L R S r * Real.log a + lowerExponent L S R s * Real.log b ≤
      Real.log |(integerMinor a b b₁ b₂ l k r s : ℝ)| := by
  let E := lowerExponent L R S r
  let F := lowerExponent L S R s
  have hd := integer_minor_lower a b b₁ b₂ ⌈E⌉₊ ⌈F⌉₊ l k r s
    (LaurentIntegerLower_exponent_for_perm l r K L R S hcard hK hS hl hr hrow hrcol)
    (LaurentIntegerLower_exponent_for_perm l s K L S R hcard hK hR hl hs hrow hscol) hdet
  change (a:ℤ)^⌈E⌉₊*(b:ℤ)^⌈F⌉₊ ≤ |integerMinor a b b₁ b₂ l k r s| at hd
  have hd' : (a:ℝ)^⌈E⌉₊*(b:ℝ)^⌈F⌉₊ ≤ |(integerMinor a b b₁ b₂ l k r s : ℝ)| := by
    exact_mod_cast hd
  have ha' : (1:ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (1:ℝ) ≤ b := by exact_mod_cast hb
  have ha₀ : (0:ℝ) < a := by linarith
  have hb₀ : (0:ℝ) < b := by linarith
  have hlog := Real.log_le_log (by positivity) hd'
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  exact (add_le_add
    (mul_le_mul_of_nonneg_right (Nat.le_ceil E) (Real.log_nonneg ha'))
    (mul_le_mul_of_nonneg_right (Nat.le_ceil F) (Real.log_nonneg hb'))).trans hlog

theorem grid_fiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R S : ℕ} (P : ι → Fin R × Fin S) (hP : Function.Injective P) (j : ℕ) :
    (univ.filter fun i => (P i).1.val = j).card ≤ S := by
  classical
  let U := univ.filter fun i => (P i).1.val = j
  have hinj : Set.InjOn (fun i => (P i).2) (U : Set ι) := by
    intro x hx y hy e
    apply hP
    apply Prod.ext _ e
    exact Fin.ext ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
  change U.card ≤ S
  rw [← card_image_of_injOn hinj]
  simpa using (card_le_card (subset_univ (U.image fun i => (P i).2)))

/- Laurent's exact integer-base arithmetic lemma for a square minor cut from
the rectangular interpolation matrix. Distinct selected column pairs give
both coordinate caps. A bijection numbers all rows of the `L × K` grid. -/
theorem integer_grid_log_minor_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b b₁ b₂ K L R S : ℕ) (row : ι ≃ Fin L × Fin K) (col : ι ↪ Fin R × Fin S)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hK : 0 < K) (hR : 0 < R) (hS : 0 < S)
    (hdet : integerMinor a b b₁ b₂ (fun i => (row i).1) (fun i => (row i).2)
      (fun i => (col i).1) (fun i => (col i).2) ≠ 0) :
    lowerExponent L R S (fun i => (col i).1) * Real.log a +
      lowerExponent L S R (fun i => (col i).2) * Real.log b ≤
        Real.log |(integerMinor a b b₁ b₂ (fun i => (row i).1) (fun i => (row i).2)
          (fun i => (col i).1) (fun i => (col i).2) : ℝ)| := by
  have hcard : Fintype.card ι = K*L := by
    simpa [Nat.mul_comm] using Fintype.card_congr row
  exact integer_log_minor_lower a b b₁ b₂ K L R S _ _ _ _ ha hb hcard hK hR hS
    (fun i => (row i).1.isLt) (fun i => (col i).1.isLt) (fun i => (col i).2.isLt)
    (grid_fiber row row.injective) (grid_fiber col col.injective)
    (grid_fiber (fun i => (col i).swap) (Prod.swap_injective.comp col.injective)) hdet

end LaurentTwoLog
end

section
/- # Existence of Laurent's integer interpolation minor
The two image-cardinality conditions are precisely those in Theorem 1.
All grid columns occur in the original rectangle, and every row occurs exactly once. -/
open Finset Matrix
namespace LaurentTwoLog
private abbrev InterpolationRank_Rect (r s : ℕ) := Fin r × Fin s

private theorem InterpolationRank_representatives {I A : Type*} [Fintype I] [DecidableEq A] (f : I → A)
    (v : (Finset.univ.image f : Finset A)) : ∃ i, f i = v.val := by
  simpa using (Finset.mem_image.mp v.property)

theorem integer_interpolation_minor (a b b₁ b₂ K L R₁ R₂ S₁ S₂ : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : L ≤ (univ.image (fun z : InterpolationRank_Rect R₁ S₁ => a^z.1.val*b^z.2.val)).card)
    (h₂ : L*(K-1) < (univ.image (fun z : InterpolationRank_Rect R₂ S₂ => z.1.val*b₂+z.2.val*b₁)).card) :
    ∃ col : InterpolationRank_Rect L K ↪ InterpolationRank_Rect (R₁+R₂-1) (S₁+S₂-1),
      integerMinor a b b₁ b₂ (fun i : InterpolationRank_Rect L K => i.1.val) (fun i => i.2.val)
        (fun i => (col i).1.val) (fun i => (col i).2.val) ≠ 0 := by
  classical
  let powerCoord (r s : ℕ) := a^r*b^s
  let addCoord (r s : ℕ) := r*b₂+s*b₁
  let y₁ (z : InterpolationRank_Rect R₁ S₁) := powerCoord z.1.val z.2.val
  let x₂ (z : InterpolationRank_Rect R₂ S₂) := addCoord z.1.val z.2.val
  let Y := univ.image y₁
  let T := univ.image x₂
  obtain ⟨e⟩ : Nonempty (Fin L ↪ Y) :=
    Function.Embedding.nonempty_of_card_le (by simpa [Y,y₁,powerCoord] using h₁)
  choose first hfirst using InterpolationRank_representatives y₁
  choose second hsecond using InterpolationRank_representatives x₂
  let f (i : Fin L) : InterpolationRank_Rect R₁ S₁ := first (e i)
  let g (k : T) : InterpolationRank_Rect R₂ S₂ := second k
  let x (i : Fin L) := addCoord (f i).1.val (f i).2.val
  let y (i : Fin L) : ℚ := powerCoord (f i).1.val (f i).2.val
  let t (k : T) := addCoord (g k).1.val (g k).2.val
  let u (k : T) : ℚ := powerCoord (g k).1.val (g k).2.val
  let A : Matrix (InterpolationRank_Rect L K) (InterpolationRank_Rect (R₁+R₂-1) (S₁+S₂-1)) ℚ := Matrix.of fun i z =>
    ((addCoord z.1.val z.2.val).choose i.2.val : ℚ) *
      (powerCoord z.1.val z.2.val : ℚ)^i.1.val
  have hy (i : Fin L) : y i = ((e i).val : ℚ) := congrArg Nat.cast (hfirst (e i))
  have ht (k : T) : t k = k.val := hsecond k
  have hA : LinearIndependent ℚ A.row := by
    apply Fintype.linearIndependent_iff.mpr
    intro c h i
    have hz := binomial_grid_coefficients x y t u
      (fun i j h => e.injective (Subtype.ext (Nat.cast_injective (R := ℚ) (by simpa only [hy] using h))))
      (fun i => by simp [y,powerCoord,ha,hb]) (fun i j h => Subtype.ext (by simpa [ht] using h))
      (fun k => by simp [u,powerCoord,ha,hb]) (by simpa [T,x₂,addCoord] using h₂)
      (fun l j => c (l,j)) (by
        intro i k
        let z : InterpolationRank_Rect (R₁+R₂-1) (S₁+S₂-1) :=
          (⟨(f i).1.val + (g k).1.val, by have := (f i).1.isLt; have := (g k).1.isLt; omega⟩,
           ⟨(f i).2.val + (g k).2.val, by have := (f i).2.isLt; have := (g k).2.isLt; omega⟩)
        have hsum := congrFun h z
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
          Matrix.row_apply, A, Matrix.of_apply, Fintype.sum_prod_type] at hsum
        have hx : addCoord z.1.val z.2.val = t k + x i := by dsimp [z,t,x,addCoord]; ring
        have hv : (powerCoord z.1.val z.2.val : ℚ) = y i * u k := by
          dsimp [z,y,u,powerCoord]; push_cast; simp only [pow_add]; ring
        simpa only [hx,hv,mul_assoc] using hsum)
    exact hz i.1 i.2
  obtain ⟨col,hinj,hnz⟩ := select_nonsingular_minor A hA
  refine ⟨⟨col,hinj⟩,?_⟩
  intro he
  apply hnz
  have he' := congrArg (Int.castRingHom ℚ) he
  simp only [integerMinor, RingHom.map_det, map_zero] at he'
  convert he' using 1
  congr 1
  ext i j
  simp [A,addCoord,powerCoord,mul_pow,← pow_mul,submatrix_apply, mul_comm]

end LaurentTwoLog
end

section
open Finset Matrix
namespace OeisA113258.Direct
open LaurentTwoLog
/- The small rectangle uses only powers of two. The large rectangle has
distinct linear arguments because its second side is at most p. -/
private theorem DirectRank_distinct_arguments {J S p H : ℕ} (hp : 0<p) (hcop : p.Coprime H)
    (hs : S ≤ p) : Function.Injective (fun z : Fin J × Fin S =>
        z.1.val*p+z.2.val*H) := by
  intro z w hw
  have hh : z.2.val*H ≡ w.2.val*H [MOD p] := by
    have he := congrArg (· % p) hw
    simpa [Nat.add_mod, Nat.ModEq] using he
  have hy := (Nat.ModEq.cancel_right_of_coprime hcop hh).eq_of_lt_of_lt
    (z.2.isLt.trans_le hs) (w.2.isLt.trans_le hs)
  have hx : z.1.val = w.1.val := by
    have he : z.1.val*p = w.1.val*p := Nat.add_right_cancel (m := w.2.val*H) (by simpa only [hy] using hw)
    exact Nat.eq_of_mul_eq_mul_right hp he
  exact Prod.ext (Fin.ext hx) (Fin.ext hy)

theorem direct_minor {J L H p b : ℕ} (hJ : 0<J) (hL : 0<L) (hp : 0<p)
    (hb : b ≠ 0) (hcop : p.Coprime H) (hs : 2*L ≤ p) :
    ∃ col : (Fin (2*J) × Fin L) ↪ (Fin (L+J-1) × Fin (2*L)),
      integerMinor 2 b H p
        (fun i : Fin (2*J) × Fin L => i.2.val) (fun i => i.1.val)
        (fun i => (col i).1.val) (fun i => (col i).2.val) ≠ 0 := by
  classical
  have hfir : Function.Injective (fun z : Fin L × Fin 1 =>
      2^z.1.val*b^z.2.val) := by
    intro z w he
    have hz := z.2.isLt
    have hw := w.2.isLt
    have he' : (2:ℕ)^z.1.val = 2^w.1.val := by
      simpa [show z.2.val=0 by omega, show w.2.val=0 by omega] using he
    exact Prod.ext (Fin.ext (Nat.pow_right_injective (by decide : 1<2) he')) (Subsingleton.elim _ _)
  have hc1 : L ≤ (univ.image fun z : Fin L × Fin 1 => 2^z.1.val*b^z.2.val).card := by
    rw [card_image_of_injective _ hfir]; simp
  have hc2 : L*(2*J-1) < (univ.image fun z : Fin J × Fin (2*L) => z.1.val*p+z.2.val*H).card := by
    rw [card_image_of_injective _ (DirectRank_distinct_arguments hp hcop hs)]
    simp only [card_univ, Fintype.card_prod, Fintype.card_fin]
    have e : (2*J-1)+1=2*J := by omega
    nlinarith [congrArg (L*·) e]
  have h := integer_interpolation_minor 2 b H p (2*J) L L J 1 (2*L) (by decide) hb hc1 hc2
  rw [show 1+2*L-1 = 2*L by omega] at h
  obtain ⟨f,hn⟩ := h
  let e := Equiv.prodComm (Fin (2*J)) (Fin L)
  refine ⟨e.toEmbedding.trans f,?_⟩
  have hd := Matrix.det_submatrix_equiv_self e (Matrix.of fun (i j : Fin L × Fin (2*J)) =>
      ((((f j).1.val*p+(f j).2.val*H).choose i.2.val : ℕ) : ℤ) *
      ((2:ℤ)^(i.1.val*(f j).1.val)*(b:ℤ)^(i.1.val*(f j).2.val)))
  exact fun hz => hn (hd.symm.trans hz)

end OeisA113258.Direct
end

section
/- # The two-sided grid exponent bound for Laurent's analytic Lemma 4 -/
open Finset
namespace LaurentTwoLog

/- Laurent's `G₁` for the first coordinate of an `R × S` grid. -/
noncomputable def gridCorrection (L R S N : ℕ) : ℝ :=
  (L:ℝ)*R*N/8-(L:ℝ)*(N:ℝ)^2/(24*S)

private theorem LaurentGridGrowth_reflected_val {L : ℕ} (v : Fin L) :
    (v.rev.val:ℝ) = (L:ℝ)-1-v.val := by
  rw [Fin.val_rev, Nat.cast_sub (Nat.succ_le_of_lt v.isLt)]
  push_cast
  ring

/- Reflection in the row levels supplies the opposite direction of the
centered exponent estimate with precisely the same grid correction. -/
theorem abs_grid_exponent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K L R S : ℕ} (row : ι ≃ Fin L × Fin K) (r : ι → ℕ)
    (hK : 0 < K) (hS : 0 < S) (hr : ∀ i, r i < R)
    (hcol : ∀ j, (univ.filter fun i => r i=j).card ≤ S) :
    |∑ i, (((row i).1.val:ℝ)-((L:ℝ)-1)/2)*(r i:ℝ)| ≤
       gridCorrection L R S (Fintype.card ι) := by
  let flip := row.trans ((Fin.revPerm : Equiv.Perm (Fin L)).prodCongr (Equiv.refl (Fin K)))
  have hc : Fintype.card ι = K*L := by simpa [Nat.mul_comm] using Fintype.card_congr row
  have low (p : ι ≃ Fin L × Fin K) := centered_exponent (fun i => (p i).1.val) r
      K L R S hc hK hS (fun i => (p i).1.isLt) hr (grid_fiber p p.injective) hcol
  have h₁ := low row
  have h₂ := low flip
  have hh (i : ι) : ((flip i).1.val:ℝ) = (L:ℝ)-1-(row i).1.val := LaurentGridGrowth_reflected_val (row i).1
  simp_rw [hh,sub_mul] at h₂
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum] at h₂
  simp_rw [sub_mul]
  rw [sum_sub_distrib, ← mul_sum,abs_le]
  dsimp [gridCorrection]
  constructor <;> linarith

theorem centered_sum_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K L : ℕ} (row : ι ≃ Fin L × Fin K) :
    (∑ i, (((row i).1.val:ℝ)-((L:ℝ)-1)/2)) = 0 := by
  let flip := row.trans ((Fin.revPerm : Equiv.Perm (Fin L)).prodCongr (Equiv.refl (Fin K)))
  let f (j : Fin L × Fin K) := (j.1.val:ℝ)-((L:ℝ)-1)/2
  have h : (∑ i, f (flip i)) = ∑ i, f (row i) := (Equiv.sum_comp flip f).trans
    (Equiv.sum_comp row f).symm
  have hh (i : ι) : f (flip i) = -f (row i) := by
    change (((row i).1.rev.val:ℝ)-((L:ℝ)-1)/2) = -(((row i).1.val:ℝ)-((L:ℝ)-1)/2)
    rw [LaurentGridGrowth_reflected_val]
    ring
  simp_rw [hh] at h
  rw [sum_neg_distrib] at h
  change (∑ i, f (row i)) = 0
  linarith

/- The real phase in the exponential factors of Laurent (2008), p.333, after
centering at any `η`. The bound is valid for any injection of chosen columns,
so it applies after every permutation in the determinant expansion. -/
theorem abs_phase_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K L R S : ℕ} (row : ι ≃ Fin L × Fin K) (col : ι ↪ Fin R × Fin S)
    (hK : 0 < K) (hR : 0 < R) (hS : 0 < S) (β η : ℝ) (hβ : 0 ≤ β) :
    |∑ i, (((row i).1.val:ℝ)-((L:ℝ)-1)/2)*
        ((col i).1.val+β*(col i).2.val-η)| ≤
         gridCorrection L R S (Fintype.card ι)+β*gridCorrection L S R (Fintype.card ι) := by
  let w (i : ι) := ((row i).1.val:ℝ)-((L:ℝ)-1)/2
  let r (i : ι) : ℝ := (col i).1.val
  let s (i : ι) : ℝ := (col i).2.val
  have h₁ := abs_grid_exponent row (fun i => (col i).1.val) hK hS
    (fun i => (col i).1.isLt) (grid_fiber col col.injective)
  have h₂ := abs_grid_exponent row (fun i => (col i).2.val) hK hR
    (fun i => (col i).2.isLt) (grid_fiber (fun i => (col i).swap) (Prod.swap_injective.comp col.injective))
  have hz : ∑ i, w i = 0 := centered_sum_zero row
  change |∑ i, w i*(r i+β*s i-η)| ≤ _
  have h (i : ι) : w i*(r i+β*s i-η) = w i*r i + β*(w i*s i) - w i*η := by ring
  simp_rw [h]
  rw [sum_sub_distrib,sum_add_distrib,← mul_sum,← sum_mul,hz,zero_mul,sub_zero]
  exact (abs_add_le _ _).trans (add_le_add h₁ (by rw [abs_mul,abs_of_nonneg hβ]; exact mul_le_mul_of_nonneg_left h₂ hβ))

end LaurentTwoLog
end

section
/-
# Divisibility of a finite Taylor interpolation determinant

For every truncation of the Taylor series in Laurent's proof of Lemma 4,
the full determinant is divisible by the power predicted by the sizes of the
exponent classes. This result works over arbitrary commutative coefficient rings.
-/

namespace LaurentTwoLog

/- Specializing `x` to the indeterminate proves the order of vanishing bound
for a determinant whose entries have been Taylor-expanded to any fixed degree. -/
theorem pow_dvd_truncated_det {ι κ R : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [CommRing R] (D : ℕ) (x : R)
    (label : ι → κ) (coef : ι → Fin D → R) (row : κ → ℕ → ι → R) :
    x ^ (∑ k, ((Finset.univ.filter fun i => label i = k).card.choose 2)) ∣
      (Matrix.of (fun i j => ∑ h : Fin D, x^h.val * (coef i h * row (label i) h.val j))).det := by
  classical
  let T := ∑ k, ((Finset.univ.filter fun i => label i = k).card.choose 2)
  let g (i : ι) (h : Fin D) (j : ι) := x^h.val * (coef i h * row (label i) h.val j)
  let A := (Matrix.detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R).toMultilinearMap
  have hexpand : (Matrix.of (fun i j => ∑ h : Fin D, g i h j)).det =
      ∑ d : ι → Fin D, (Matrix.of fun i j => g i (d i) j).det := by
    convert A.map_sum g using 1
    change (Matrix.of (fun i j => ∑ h, g i h j)).det =
      (Matrix.of (fun i => ∑ h, g i h)).det
    congr 1
    ext i j
    simp
    rfl
  change x^T ∣ (Matrix.of (fun i j => ∑ h : Fin D, g i h j)).det
  rw [hexpand]
  apply Finset.dvd_sum
  intro d _
  let M := Matrix.of (fun i j => coef i (d i) * row (label i) (d i).val j)
  change x^T ∣ (Matrix.of (fun i j => x^(d i).val * M i j)).det
  rw [Matrix.det_mul_column]
  by_cases hM : M.det = 0
  · simp [hM]
  have hT := taylor_degree_of_det_ne_zero label (fun i => (d i).val) (fun i => coef i (d i)) row hM
  rw [Finset.prod_pow_eq_pow_sum]
  exact dvd_mul_of_dvd_left (pow_dvd_pow x hT) M.det

end LaurentTwoLog
end

section
/-
# Order of vanishing for Laurent's interpolation determinant

For the coefficient shape used in the proof of Lemma 4 of Laurent (2008), the
determinant of the formal Taylor expansions vanishes to order at least the sum
of the binomial occupancy numbers. Individual power series may be infinite.
-/

open scoped PowerSeries

namespace LaurentTwoLog

theorem dvd_det_of_entry_congr {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] {d : R} {A B : Matrix ι ι R}
    (h : ∀ i j, d ∣ A i j - B i j) (hb : d ∣ B.det) : d ∣ A.det := by
  let f : R →+* R ⧸ Ideal.span ({d} : Set R) := Ideal.Quotient.mk _
  have hab : f.mapMatrix A = f.mapMatrix B := by
    ext i j
    change f (A i j) = f (B i j)
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (Ideal.Quotient.eq_zero_iff_dvd _ _).mpr (h i j)
  apply (Ideal.Quotient.eq_zero_iff_dvd _ _).mp
  change f A.det = 0
  rw [f.map_det, hab, ← f.map_det]
  exact (Ideal.Quotient.eq_zero_iff_dvd _ _).mpr hb

/- Every formal interpolation determinant with Laurent's grouped row
coefficients vanishes through Taylor degree `∑ choose 2 - 1`. -/
end LaurentTwoLog
end

section
/- # Taylor divisibility and the Schwarz bound for entire interpolation determinants

For the coefficient determinant in Laurent's 2008 Lemma 4, we work in the
ring of entire functions. Repeated divided differences give a finite Taylor
expansion with an entire remainder. This gives a global analytic factor,
to which the maximum modulus principle applies directly.
-/

open Finset Metric Set
open scoped Topology
namespace LaurentTwoLog

noncomputable section

/- The ring of entire complex functions. -/
def entireRing : Subring (ℂ → ℂ) where
  carrier := {f | Differentiable ℂ f}
  zero_mem' := differentiable_const _
  one_mem' := differentiable_const _
  add_mem' := fun hf hg => hf.add hg
  mul_mem' := fun hf hg => hf.mul hg
  neg_mem' := fun hf => hf.neg

abbrev Entire := ↥entireRing

namespace Entire

def C (a : ℂ) : Entire := ⟨fun _ => a, differentiable_const _⟩
def X : Entire := ⟨id, differentiable_id⟩
def E (z : ℂ) : Entire →+* ℂ where
  toFun f := f.val z
  map_one' := rfl
  map_zero' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp] theorem E_C (z a : ℂ) : E z (C a) = a := rfl
@[simp] theorem E_X (z : ℂ) : E z X = z := rfl

def dilate (f : Entire) (c : ℂ) : Entire :=
  ⟨fun z => f.val (z*c), (f.property : Differentiable ℂ _).comp
    (differentiable_id.mul_const c)⟩

@[simp] theorem E_dilate (z c : ℂ) (f : Entire) : E z (dilate f c) = E (z*c) f := rfl

def next (f : Entire) : Entire :=
  ⟨dslope f.val 0, differentiableOn_univ.mp ((Complex.differentiableOn_dslope
    (s := univ) (c := 0) Filter.univ_mem).mpr (f.property : Differentiable ℂ _).differentiableOn)⟩

theorem split (f : Entire) (z : ℂ) : E z f = E 0 f + z*E z (next f) := by
  have h := sub_smul_dslope f.val 0 z
  simp only [sub_zero,smul_eq_mul] at h
  change f.val z = f.val 0 + z * dslope f.val 0 z
  linear_combination -h

def tail (f : Entire) : ℕ → Entire
  | 0 => f
  | n+1 => next (tail f n)

theorem expand (f : Entire) (z : ℂ) (n : ℕ) :
    E z f = (∑ t ∈ range n, z^t*E 0 (tail f t)) + z^n*E z (tail f n) := by
  induction n with
  | zero => simp [tail]
  | succ n ih =>
    rw [sum_range_succ, ih, split (tail f n) z]
    simp only [tail, pow_succ]
    ring

/- Sharp Schwarz estimate at 1 for an entire function divisible by (X^t).
Here it follows by maximum modulus applied to the entire quotient. -/
theorem bound_one_of_dvd {f : Entire} {ρ B : ℝ} (t : ℕ) (hρ : 1 < ρ)
    (hd : X^t ∣ f) (hB : ∀ z : ℂ, ‖z‖ = ρ → ‖E z f‖ ≤ B) :
    ‖E 1 f‖ ≤ B/ρ^t := by
  obtain ⟨g,hg⟩ := hd
  have he (z : ℂ) : E z f = z^t * E z g := by simp [hg]
  rw [he]
  simp only [one_pow,one_mul]
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball 0 ρ) isBounded_ball
    (g.property : Differentiable ℂ _).diffContOnCl
  · intro z hz
    have hs := frontier_ball_subset_sphere hz
    rw [mem_sphere_iff_norm, sub_zero] at hs
    have hu := hB z hs
    rw [he,norm_mul,norm_pow,hs,mul_comm] at hu
    exact (le_div_iff₀ (pow_pos (lt_trans zero_lt_one hρ) t)).mpr hu
  · apply subset_closure
    simpa [mem_ball_iff_norm] using hρ

end Entire

/- `A(z)` is the determinant appearing in Laurent Lemma 4, with arbitrary
entire row functions and arbitrary scalar, column and grouped row factors. -/
theorem entire_interpolation_dvd {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (f : ι → Entire) (z scale : ι → ℂ)
    (label : ι → κ) (w : κ → ι → ℂ) :
    Entire.X ^ (∑ k, ((univ.filter fun i => label i=k).card.choose 2)) ∣
      (Matrix.of fun i j => Entire.C (scale i * w (label i) j) *
        Entire.dilate (f i) (z j)).det := by
  classical
  let T := ∑ k, ((univ.filter fun i => label i=k).card.choose 2)
  let c (i : ι) (h : Fin T) := Entire.C (scale i * Entire.E 0 (Entire.tail (f i) h.val))
  let v (k : κ) (h : ℕ) (j : ι) := Entire.C (w k j * (z j)^h)
  let B : Matrix ι ι Entire := Matrix.of fun i j => ∑ h : Fin T, Entire.X^h.val * (c i h * v (label i) h.val j)
  have hb : Entire.X^T ∣ B.det := pow_dvd_truncated_det T Entire.X label c v
  apply dvd_det_of_entry_congr (B := B) _ hb
  intro i j
  refine ⟨Entire.C (scale i * w (label i) j * (z j)^T) * Entire.dilate (Entire.tail (f i) T) (z j), ?_⟩
  apply Subtype.ext
  funext x
  change Entire.E x (_ - B i j) = Entire.E x (Entire.X^T * _)
  simp only [B,c,v,Matrix.of_apply,map_sub,map_mul,map_sum,map_pow,Entire.E_X,
    Entire.E_C,Entire.E_dilate]
  rw [Entire.expand (f i) (x*z j) T]
  have eq : (∑ h : Fin T, x^h.val * ((scale i * Entire.E 0 (Entire.tail (f i) h.val)) *
      (w (label i) j * z j ^ h.val))) = scale i * w (label i) j *
      ∑ t ∈ range T, (x*z j)^t*Entire.E 0 (Entire.tail (f i) t) := by
    rw [mul_sum, ← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro h _
    rw [mul_pow]
    ring
  rw [eq,mul_pow]
  ring

/- Schwarz's factor (ρ^{-T}) for the actual analytic interpolation determinant. -/
theorem entire_interpolation_bound {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (f : ι → Entire) (z scale : ι → ℂ)
    (label : ι → κ) (w : κ → ι → ℂ) {ρ B : ℝ} (hρ : 1 < ρ)
    (hB : ∀ x : ℂ, ‖x‖ = ρ → ‖(Matrix.of fun i j =>
      scale i * w (label i) j * Entire.E (x*z j) (f i)).det‖ ≤ B) :
    ‖(Matrix.of fun i j => scale i * w (label i) j * Entire.E (z j) (f i)).det‖ ≤
      B/ρ^(∑ k, ((univ.filter fun i => label i=k).card.choose 2)) := by
  let A := Matrix.of fun i j => Entire.C (scale i * w (label i) j) * Entire.dilate (f i) (z j)
  have he (x : ℂ) : Entire.E x A.det = (Matrix.of fun i j =>
      scale i * w (label i) j * Entire.E (x*z j) (f i)).det := by
    rw [(Entire.E x).map_det]
    congr 1
  have hh := Entire.bound_one_of_dvd _ hρ (entire_interpolation_dvd f z scale label w)
    (fun x hx => (congrArg norm (he x)).trans_le (hB x hx))
  change ‖Entire.E 1 A.det‖ ≤ _ at hh
  simpa only [he, one_mul] using hh

end
end LaurentTwoLog
end

section
/- # Boundary estimate for the determinant in Laurent's analytic Lemma 4 -/

open Finset
namespace LaurentTwoLog

theorem norm_det_le_factorial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (A : ℝ)
    (h : ∀ π : Equiv.Perm ι, (∏ i, ‖M (π i) i‖) ≤ A) :
    ‖M.det‖ ≤ ((Fintype.card ι).factorial:ℝ)*A := by
  classical
  rw [Matrix.det_apply]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _π : Equiv.Perm ι, A := by
      apply sum_le_sum
      intro π _
      rcases Int.units_eq_one_or (Equiv.Perm.sign π) with e|e <;> simpa [e,norm_prod] using h π
    _ = _ := by simp [Fintype.card_perm]

end LaurentTwoLog
end

section
/-
# Laurent's interpolation determinant occupancy bound

This is Lemma 3 of Michel Laurent, *Linear forms in two logarithms and
interpolation determinants II*, Acta Arithmetica 133 (2008), 330–331.
The zero-based index `i` here is the paper's `k-1`. Completing squares in
the first two coordinates avoids using the existence of a constrained minimizer.
-/

namespace LaurentTwoLog

/- With the tail mass (z), the first two coordinates control the entire bound. -/
private theorem LaurentOccupancy_first_two (μ N x y z : ℝ) (hμ : 1/3 ≤ μ) (hN : 0 ≤ N)
    (hz : 0 ≤ z) (hmass : N = x+y+z) :
    ((1+2*μ-μ^2)/2)*N^2 ≤ x^2 + y^2 + 2*μ*N*(y+2*z) := by
  have hcoef : 0 ≤ 3*μ-1 := by linarith
  have hrest := mul_nonneg (mul_nonneg hcoef hN) hz
  have hx := sq_nonneg (x - N*(1+μ)/2)
  have hy := sq_nonneg (y - N*(1-μ)/2)
  rw [hmass] at *
  nlinarith only [hx,hy,hrest]

/- A real-valued form that also permits zero occupancies. -/
theorem occupancy_squares (m : ℕ) (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i)
    (μ : ℝ) (hμ : 1/3 ≤ μ) (_hμ' : μ ≤ 1) :
    ((1 + 2*μ - μ^2)/2)*(∑ i, a i)^2 ≤
      (∑ i, (a i)^2) + 2*μ*(∑ i, a i)* ∑ i, (i.val:ℝ)*a i := by
  cases m with
  | zero => simp
  | succ m =>
    cases m with
    | zero =>
      simp
      nlinarith only [sq_nonneg ((1-μ)*a 0)]
    | succ n =>
      let x := a 0
      let y := a (Fin.succ 0)
      let t := fun (j : Fin n) => a j.succ.succ
      let z := ∑ j, t j
      let N := ∑ j, a j
      have hz : 0 ≤ z := Finset.sum_nonneg (fun j _ => ha j.succ.succ)
      have hn : 0 ≤ N := Finset.sum_nonneg (fun j _ => ha j)
      have hmass : N = x+y+z := by
        dsimp [N,x,y,z,t]
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun j => a j.succ)]
        simp [Fin.succ_zero_eq_one, add_assoc]
      have hsquare : x^2 + y^2 ≤ ∑ j, (a j)^2 := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun j => (a j.succ)^2)]
        dsimp [x,y]
        have ht : 0 ≤ ∑ j : Fin n, (a j.succ.succ)^2 :=
          Finset.sum_nonneg (fun j _ => sq_nonneg _)
        linarith
      have htail : 2*z ≤ ∑ j : Fin n, ((j.succ.succ.val:ℕ):ℝ) * t j := by
        dsimp [z]
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_right _ (ha j.succ.succ)
        exact_mod_cast (show 2 ≤ j.val+1+1 by omega)
      have hweight : y + 2*z ≤ ∑ j, (j.val:ℝ)*a j := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun j => (j.succ.val:ℝ)*a j.succ)]
        simp only [Fin.val_zero, Nat.cast_zero, zero_mul, zero_add, Fin.val_succ,
          Nat.cast_add, Nat.cast_one, one_mul] at *
        exact add_le_add (le_refl _) htail
      have hfactor : 0 ≤ 2*μ*N := by
        have : 0 ≤ μ := by linarith
        positivity
      exact (LaurentOccupancy_first_two μ N x y z hμ hn hz hmass).trans
        (add_le_add hsquare (mul_le_mul_of_nonneg_left hweight hfactor))

/- Laurent's Lemma 3, including its exact coefficient σ and the binomial terms. -/
theorem occupancy (m : ℕ) (ν : Fin m → ℕ) (μ : ℝ) (hμ : 1/3 ≤ μ) (hμ' : μ ≤ 1) :
    let N : ℝ := ∑ i, (ν i : ℝ)
    (((1 + 2*μ - μ^2)/2)*N^2 - N)/2 ≤
      (∑ i, ((ν i).choose 2 : ℝ)) + μ*N*∑ i, (i.val:ℝ)*(ν i : ℝ) := by
  dsimp only
  have h := occupancy_squares m (fun i => (ν i : ℝ)) (fun i => Nat.cast_nonneg _)
    μ hμ hμ'
  have hchoose : 2*(∑ i, ((ν i).choose 2 : ℝ)) =
      ∑ i, (ν i : ℝ)^2 - ∑ i, (ν i : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_choose_two]
    ring
  linarith

end LaurentTwoLog
end

section
/- # A direct summation of Laurent's analytic determinant terms

Taking one occupancy class for every Taylor degree, including empty classes,
allows the entire gain to be taken before summing reciprocal factorials.
-/

open Finset
namespace LaurentTwoLog

noncomputable def gainExponent (N : ℕ) (μ : ℝ) : ℝ :=
  (((1+2*μ-μ^2)/2)*(N:ℝ)^2-N)/2

def collisions {ι : Type*} [Fintype ι] (D : ℕ) (d : ι → Fin D) : ℕ :=
  ∑ j, ((univ.filter fun i => d i=j).card.choose 2)

/- Empty degree classes may be left in the table, giving an exact raw-degree
bound for every rectangular truncation of the multivariate Taylor expansion. -/
theorem raw_degree_gain {ι : Type*} [Fintype ι] (D : ℕ) (d : ι → Fin D)
    (μ : ℝ) (hμ : 1/3 ≤ μ) (hμ' : μ ≤ 1) :
    gainExponent (Fintype.card ι) μ ≤ (collisions D d:ℝ)+
      μ*(Fintype.card ι)*(∑ i, ((d i).val:ℝ)) := by
  classical
  let ν (j : Fin D) := (univ.filter fun i => d i=j).card
  have hN : ∑ j, (ν j:ℝ) = (Fintype.card ι:ℝ) := by
    dsimp [ν]
    exact_mod_cast (card_eq_sum_card_fiberwise (s := (univ : Finset ι)) (t := univ)
      (f := d) (fun _ _ => mem_univ _)).symm.trans (card_univ)
  have hW : ∑ j, (j.val:ℝ)*(ν j:ℝ) = ∑ i, ((d i).val:ℝ) := by
    rw [← sum_fiberwise univ d (fun i => ((d i).val:ℝ))]
    apply sum_congr rfl
    intro j _
    calc
      _ = ∑ _i ∈ univ.filter (fun i => d i=j), (j.val:ℝ) := by simp [ν,mul_comm]
      _ = _ := sum_congr rfl (fun i hi => by rw [(mem_filter.mp hi).2])
  have h := occupancy D ν μ hμ hμ'
  dsimp only at h
  rw [hN,hW] at h
  simpa [gainExponent,collisions,ν] using h

theorem raw_term_gain {ι : Type*} [Fintype ι] (D : ℕ) (d : ι → Fin D)
    (μ ρ a : ℝ) (hμ : 1/3 ≤ μ) (hμ' : μ ≤ 1) (hρ : 1 < ρ) (ha : 0 ≤ a)
    (hsmall : a ≤ ρ^(-μ*(Fintype.card ι))) :
    a^(∑ i, (d i).val)/ρ^(collisions D d) ≤ ρ^(-gainExponent (Fintype.card ι) μ) := by
  have hp : 0 < ρ := lt_trans zero_lt_one hρ
  have h := raw_degree_gain D d μ hμ hμ'
  calc
    _ ≤ (ρ^(-μ*(Fintype.card ι)))^(∑ i, (d i).val)/ρ^(collisions D d) := by gcongr
    _ = ρ^((-μ*(Fintype.card ι))*((∑ i, (d i).val:ℕ):ℝ)-(collisions D d:ℝ)) := by
      rw [Real.rpow_sub hp,Real.rpow_mul_natCast hp.le (-μ*(Fintype.card ι)) _,Real.rpow_natCast]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le hρ.le
      push_cast
      linarith

theorem factorial_weight_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ℕ) :
    (∑ d : ι → Fin D, ∏ i, ((d i).val.factorial:ℝ)⁻¹) ≤
      (Real.exp 1)^(Fintype.card ι) := by
  classical
  rw [← Fintype.prod_sum (fun (_ : ι) (j : Fin D) => (j.val.factorial:ℝ)⁻¹), prod_const,card_univ]
  have hle := Real.sum_le_exp_of_nonneg (x := 1) (by norm_num) D
  apply pow_le_pow_left₀ (sum_nonneg (fun _ _ => by positivity))
  rw [Fin.sum_univ_eq_sum_range (fun j => (j.factorial:ℝ)⁻¹)]
  simpa only [one_pow,one_div] using hle

/- Uniform truncation estimate, with the cost `e^N` from the sum of
reciprocal factorials. The term bound is exactly the output of the analytic
interpolation determinant estimate before summing the outer Taylor indices. -/
theorem sum_row_terms_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ℕ)
    (μ ρ a Ω : ℝ) (hμ : 1/3 ≤ μ) (hμ' : μ ≤ 1) (hρ : 1 < ρ) (ha : 0 ≤ a)
    (hΩ : 0 ≤ Ω) (hs : a ≤ ρ^(-μ*(Fintype.card ι))) (term : (ι → Fin D) → ℂ)
    (ht : ∀ d, ‖term d‖ ≤ Ω*(a^(∑ i,(d i).val)/ρ^(collisions D d))*
      (∏ i, ((d i).val.factorial:ℝ)⁻¹)) :
    ‖∑ d, term d‖ ≤ Ω*ρ^(-gainExponent (Fintype.card ι) μ)*(Real.exp 1)^(Fintype.card ι) := by
  classical
  calc
    _ ≤ ∑ d, ‖term d‖ := norm_sum_le _ _
    _ ≤ ∑ d : ι → Fin D, Ω*ρ^(-gainExponent (Fintype.card ι) μ)*
          (∏ i, ((d i).val.factorial:ℝ)⁻¹) := by
      apply sum_le_sum
      intro d _
      exact (ht d).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (raw_term_gain D d μ ρ a hμ hμ' hρ ha hs) hΩ)
        (prod_nonneg (fun _ _ => by positivity)))
    _ ≤ _ := by
      rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left (factorial_weight_sum D)
      exact mul_nonneg hΩ (Real.rpow_nonneg (by linarith) _)

end LaurentTwoLog
end

section
/- # A uniform analytic upper bound for the two-variable interpolation determinant

This is the analytic mechanism of Laurent (2008), pp.332–335. The phase
and polynomial growth of the chosen entire row functions are summarized
by their product bound on the boundary circle. The second-variable
exponentials are expanded diagonally through finite rectangular truncations,
so no rearrangement of an infinite multivariate series is necessary.
-/

open Finset Filter
open scoped Topology
namespace LaurentTwoLog

private theorem LaurentAnalyticUpper_det_sum_rows {ι τ R : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [CommRing R] (g : ι → τ → ι → R) :
    (Matrix.of (fun i j => ∑ h, g i h j)).det =
      ∑ d : ι → τ, (Matrix.of fun i j => g i (d i) j).det := by
  classical
  let A := (Matrix.detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R).toMultilinearMap
  convert A.map_sum g using 1
  · change (Matrix.of (fun i j => ∑ h, g i h j)).det = (Matrix.of (fun i => ∑ h, g i h)).det
    congr 1
    ext i j
    simp
  · rfl

/- The uniform product bound for the unperturbed row functions controls the
full exponential determinant with the exact `ρ^{-gainExponent N μ}` saving. -/
theorem analytic_upper {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Entire) (z b w : ι → ℂ) (ρ a H μ : ℝ)
    (hρ : 1 < ρ) (ha : 0 ≤ a) (hH : 0 ≤ H) (hμ : 1/3 ≤ μ) (hμ' : μ ≤ 1)
    (hsmall : a ≤ ρ^(-μ*(Fintype.card ι)))
    (hbw : ∀ i j, ‖b i * w j‖ ≤ a)
    (hbase : ∀ x : ℂ, ‖x‖ = ρ → ∀ π : Equiv.Perm ι,
      (∏ i, ‖Entire.E (x*z i) (f (π i))‖) ≤ H) :
    ‖(Matrix.of fun i j => Complex.exp (b i*w j)*Entire.E (z j) (f i)).det‖ ≤
      ((Fintype.card ι).factorial:ℝ)*H*ρ^(-gainExponent (Fintype.card ι) μ)*
        (Real.exp 1)^(Fintype.card ι) := by
  classical
  let g (i : ι) (h : ℕ) (j : ι) := (b i*w j)^h/(h.factorial:ℂ)*Entire.E (z j) (f i)
  let M (D : ℕ) : Matrix ι ι ℂ := Matrix.of fun i j => ∑ h : Fin D, g i h.val j
  have finite_bound (D : ℕ) : ‖(M D).det‖ ≤
      ((Fintype.card ι).factorial:ℝ)*H*ρ^(-gainExponent (Fintype.card ι) μ)*
        (Real.exp 1)^(Fintype.card ι) := by
    change ‖(Matrix.of fun i j => ∑ h : Fin D, g i h.val j).det‖ ≤ _
    rw [LaurentAnalyticUpper_det_sum_rows (fun i (h : Fin D) j => g i h.val j)]
    apply sum_row_terms_bound D μ ρ a (((Fintype.card ι).factorial:ℝ)*H) hμ hμ' hρ ha
      (mul_nonneg (Nat.cast_nonneg _) hH) hsmall
    intro d
    let C (i : ι) := (b i)^(d i).val/((d i).val.factorial:ℂ)
    let W (h : Fin D) (j : ι) := (w j)^h.val
    let fac : ℝ := ∏ i, ((d i).val.factorial:ℝ)⁻¹
    let P := a^(∑ i,(d i).val)*fac
    have hprod (π : Equiv.Perm ι) :
        (∏ i, ‖C (π i)*W (d (π i)) i‖) ≤ P := by
      dsimp only [P,fac]
      conv_rhs => rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib, ← Equiv.prod_comp π]
      apply prod_le_prod (fun _ _ => norm_nonneg _)
      intro i _
      simp only [C,W,norm_mul,norm_pow,div_eq_mul_inv,norm_inv,Complex.norm_natCast]
      have hh := pow_le_pow_left₀ (norm_nonneg _) (hbw (π i) i) (d (π i)).val
      rw [norm_mul,mul_pow] at hh
      calc
        _ = (‖b (π i)‖ ^ (d (π i)).val * ‖w i‖ ^ (d (π i)).val) * ((d (π i)).val.factorial:ℝ)⁻¹ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hh (by positivity)
    have hB (x : ℂ) (hx : ‖x‖ = ρ) :
      ‖(Matrix.of fun i j => C i*W (d i) j*Entire.E (x*z j) (f i)).det‖ ≤
        ((Fintype.card ι).factorial:ℝ)*(P*H) := by
      apply norm_det_le_factorial
      intro π
      simp only [Matrix.of_apply,norm_mul,prod_mul_distrib]
      have hleft : (∏ i, ‖C (π i)‖) * (∏ i, ‖W (d (π i)) i‖) ≤ P := by
        simpa only [norm_mul,prod_mul_distrib] using hprod π
      exact mul_le_mul hleft (hbase x hx π) (prod_nonneg (fun _ _ => norm_nonneg _))
        ((prod_nonneg (fun _ _ => norm_nonneg _)).trans (hprod π))
    have hbound := entire_interpolation_bound f z C d W hρ hB
    have hmatrix : (Matrix.of fun i j => g i (d i).val j) =
        (Matrix.of fun i j => C i*W (d i) j*Entire.E (z j) (f i)) := by
      ext i j
      simp only [Matrix.of_apply,g,C,W,mul_pow]
      ring
    rw [hmatrix]
    convert hbound using 1
    dsimp [P,fac,collisions]
    ring
  let A := Matrix.of fun i j => Complex.exp (b i*w j)*Entire.E (z j) (f i)
  have hmat : Tendsto M atTop (𝓝 A) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have h := (NormedSpace.expSeries_div_hasSum_exp (b i*w j)).tendsto_sum_nat
    rw [← Complex.exp_eq_exp_ℂ] at h
    have ee (D : ℕ) : (∑ h : Fin D, (b i*w j)^h.val/(h.val.factorial:ℂ)) =
        ∑ h ∈ range D, (b i*w j)^h/(h.factorial:ℂ) :=
      Fin.sum_univ_eq_sum_range (fun h => (b i*w j)^h/(h.factorial:ℂ)) D
    simpa only [M,A,g,Matrix.of_apply,← sum_mul,ee] using
      h.mul (tendsto_const_nhds (x := Entire.E (z j) (f i)))
  have hd : Tendsto (fun D => ‖(M D).det‖) atTop (𝓝 ‖A.det‖) :=
    ((continuous_id.matrix_det.continuousAt.tendsto).comp hmat).norm
  exact le_of_tendsto' hd finite_bound

end LaurentTwoLog
end

section
/- # The centered analytic grid estimate for Laurent's real logarithms -/
open Finset
namespace LaurentTwoLog

noncomputable section

/- The exact finite-product version of the upper bound for Laurent's centered
grid determinant. The perturbation coefficient is `δ = Λ/b₂`. The choice
`c_i=b₂^k_i/k_i!` gives Laurent's polynomial normalization. -/
theorem centered_grid_upper {ι : Type*} [Fintype ι] [DecidableEq ι] {K L R S : ℕ}
    (row : ι ≃ Fin L × Fin K) (col : ι ↪ Fin R × Fin S)
    (hK : 0 < K) (hR : 0 < R) (hS : 0 < S) (β η γ ρ Z μ : ℝ)
    (δ : ℂ) (c : ι → ℂ) (hβ : 0 ≤ β) (hρ : 1 < ρ) (hZ₀ : 0 ≤ Z)
    (hμ : 1/3 ≤ μ) (hμ' : μ ≤ 1)
    (hsmall : ‖δ‖*((L:ℝ)/2)*S ≤ ρ^(-μ*(Fintype.card ι)))
    (hZ : ∀ j, |((col j).1.val:ℝ)+β*(col j).2.val-η| ≤ Z) :
    let z (j : ι) := ((col j).1.val:ℝ)+β*(col j).2.val-η
    let ell (i : ι) := ((row i).1.val:ℝ)-((L:ℝ)-1)/2
    let k (i : ι) := (row i).2.val
    let G := gridCorrection L R S (Fintype.card ι)+β*gridCorrection L S R (Fintype.card ι)
    ‖(Matrix.of fun i j => Complex.exp (δ*(ell i:ℂ)*((col j).2.val:ℂ))*
      (c i*(z j:ℂ)^(k i)*Complex.exp ((γ*ell i:ℝ)*(z j:ℂ)))).det‖ ≤
      ((Fintype.card ι).factorial:ℝ)*((∏ i, ‖c i‖*(ρ*Z)^k i)*Real.exp (ρ*(|γ| *G)))*
       ρ^(-gainExponent (Fintype.card ι) μ)*(Real.exp 1)^(Fintype.card ι) := by
  classical
  intro z ell k G
  let f (i : ι) : Entire := ⟨fun y => c i*y^k i * Complex.exp ((γ*ell i:ℝ)*y), by
    change Differentiable ℂ (fun y : ℂ => c i*y^k i * Complex.exp ((γ*ell i:ℝ)*y))
    fun_prop⟩
  have hρ₀ : 0 ≤ ρ := by linarith
  apply analytic_upper f (fun j => (z j:ℂ)) (fun i => δ*(ell i:ℂ))
    (fun j => ((col j).2.val:ℂ)) ρ (‖δ‖*((L:ℝ)/2)*S) _ μ hρ (by positivity)
    (by positivity) hμ hμ' hsmall
  · intro i j
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast]
    have hb : |ell i| ≤ (L:ℝ)/2 := by
      have hi := (row i).1.isLt
      have hf : ((row i).1.val:ℝ)+1 ≤ L := by exact_mod_cast hi
      dsimp only [ell]
      rw [abs_le]
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (row i).1.val]
    gcongr
    exact_mod_cast (col j).2.isLt.le
  · intro x hx π
    have he (i : ι) : ‖Entire.E (x*(z i:ℂ)) (f (π i))‖ =
        (‖c (π i)‖*(ρ*|z i|)^k (π i)) *
        Real.exp ((γ*ell (π i)*z i)*x.re) := by
      change ‖c (π i)*(x*(z i:ℂ))^k (π i)*Complex.exp _‖ = _
      simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,
        Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,mul_zero,zero_mul,sub_zero,hx]
      congr 2
      ring
    simp_rw [he]
    rw [prod_mul_distrib,← Real.exp_sum]
    apply mul_le_mul _ _ (Real.exp_pos _).le (prod_nonneg (fun _ _ => by positivity))
    · conv_rhs => rw [← Equiv.prod_comp π]
      apply prod_le_prod (fun _ _ => by positivity)
      intro i _
      gcongr
      exact hZ i
    · apply Real.exp_le_exp.mpr
      have hph := abs_phase_bound (π.trans row) col hK hR hS β η hβ
      have eq : (∑ i, γ*ell (π i)*z i*x.re) = x.re*γ*∑ i, ell (π i)*z i := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        ring
      rw [eq]
      calc
        _ ≤ |x.re*γ*∑ i, ell (π i)*z i| := le_abs_self _
        _ = |x.re| * |γ| * |∑ i, ell (π i)*z i| := by rw [abs_mul,abs_mul]
        _ ≤ ‖x‖ * |γ| * G := by
          exact mul_le_mul (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (abs_nonneg _))
            hph (abs_nonneg _) (mul_nonneg (norm_nonneg _) (abs_nonneg _))
        _ = _ := by rw [hx]; ring

end
end LaurentTwoLog
end

section
/- # Monic row changes for Laurent's binomial interpolation determinant -/
open Finset Polynomial
namespace LaurentTwoLog

/- Replace each monic polynomial of degree `k` by the monomial of degree
`k` inside each fixed exponent block of interpolation rows. Arbitrary
column factors for that block are allowed. -/
theorem det_monic_blocks {R : Type*} [CommRing R] (K L : ℕ)
    (p : Fin K → R[X]) (hdeg : ∀ k, (p k).natDegree=k.val) (hmon : ∀ k, (p k).Monic)
    (z : Fin K × Fin L → R) (w : Fin L → Fin K × Fin L → R) :
    (Matrix.of (fun (i j : Fin K × Fin L) => (p i.1).eval (z j)*w i.2 j)).det =
    (Matrix.of (fun (i j : Fin K × Fin L) => (z j)^i.1.val*w i.2 j)).det := by
  classical
  let P : Matrix (Fin K) (Fin K) R := (Matrix.of fun (i j : Fin K) => (p j).coeff i.val).transpose
  let B := Matrix.blockDiagonal (fun _ : Fin L => P)
  let V := Matrix.of (fun (i j : Fin K × Fin L) => (z j)^i.1.val*w i.2 j)
  have hP : P.det = 1 := by
    rw [show P = (Matrix.of fun (i j : Fin K) => (p j).coeff i.val).transpose from rfl,
      Matrix.det_transpose, Matrix.det_matrixOfPolynomials p hdeg hmon]
  have hB : B.det = 1 := by simp [B,Matrix.det_blockDiagonal,hP]
  have he : (Matrix.of (fun (i j : Fin K × Fin L) => (p i.1).eval (z j)*w i.2 j)) = B*V := by
    ext i j
    simp only [Matrix.of_apply,Matrix.mul_apply,B,V,Matrix.blockDiagonal_apply,Fintype.sum_prod_type]
    simp only [ite_mul,zero_mul,sum_ite_eq,mem_univ,if_true]
    rw [(p i.1).eval_eq_sum_range' (show (p i.1).natDegree < K by rw [hdeg]; exact i.1.isLt),
      ← Fin.sum_univ_eq_sum_range, sum_mul]
    apply sum_congr rfl
    intro m _
    change (p i.1).coeff m.val * (z j)^m.val * w i.2 j =
      (p i.1).coeff m.val * ((z j)^m.val * w i.2 j)
    ring
  rw [he,Matrix.det_mul,hB,one_mul]

/- Laurent's replacement of `choose(t,k)` by `(t−η)^k/k!` in the chosen
minor. The translation parameter may be arbitrary and complex. -/
theorem det_binomial_recenter (K L : ℕ) (t : Fin K × Fin L → ℕ) (η : ℂ)
    (w : Fin L → Fin K × Fin L → ℂ) :
    (Matrix.of (fun (i j : Fin K × Fin L) => ((t j).choose i.1.val:ℂ)*w i.2 j)).det =
    (Matrix.of (fun (i j : Fin K × Fin L) => ((t j:ℂ)-η)^i.1.val/(i.1.val.factorial:ℂ)*w i.2 j)).det := by
  let p (k : Fin K) := taylor η (descPochhammer ℂ k.val)
  have hd (k : Fin K) : (p k).natDegree = k.val := by
    simp [p,natDegree_taylor,descPochhammer_natDegree]
  have hm (k : Fin K) : (p k).Monic := by
    change (taylor η (descPochhammer ℂ k.val)).leadingCoeff = 1
    rw [leadingCoeff_taylor]
    exact monic_descPochhammer ℂ _
  have h := det_monic_blocks K L p hd hm (fun j => (t j:ℂ)-η) w
  have hev (k : Fin K) (j : Fin K × Fin L) :
     (p k).eval ((t j:ℂ)-η) = (k.val.factorial:ℂ)*((t j).choose k.val:ℂ) := by
    rw [show p k = _ from rfl,taylor_eval,sub_add_cancel,descPochhammer_eval_eq_descFactorial]
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose (t j) k.val
  simp_rw [hev] at h
  let d (i : Fin K × Fin L) : ℂ := (i.1.val.factorial:ℂ)
  have hd₀ : (∏ i, d i) ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => by dsimp [d]; exact_mod_cast Nat.factorial_ne_zero _)
  apply mul_left_cancel₀ hd₀
  rw [← Matrix.det_mul_column d, ← Matrix.det_mul_column d]
  convert h using 2
  · congr 1
    ext i j
    change (i.1.val.factorial:ℂ)*(((t j).choose i.1.val:ℂ)*w i.2 j) =
      (i.1.val.factorial:ℂ)*((t j).choose i.1.val:ℂ)*w i.2 j
    ring
  · congr 1
    ext i j
    change (i.1.val.factorial:ℂ)*(((t j:ℂ)-η)^i.1.val/(i.1.val.factorial:ℂ)*w i.2 j) = _
    have hf : (i.1.val.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp [hf]

end LaurentTwoLog
end

section
/- # Exact recentering of the exponential interpolation determinant
This is the identity on pp.331–332 of Laurent (2008). -/
open Finset
namespace LaurentTwoLog

/- Exact exponential normalization, including the cancellation of the row
factors involving the translated origin `η`. The uncentered abscissae are
`t_j = b₀(r_j+βs_j)`. -/
theorem exponential_recenter (K L : ℕ) (t : Fin K × Fin L → ℕ)
    (r s : Fin K × Fin L → ℝ) (b₀ β η γ θ : ℝ)
    (ht : ∀ j, (t j:ℝ) = b₀*(r j+β*s j)) :
    let m := ((L:ℝ)-1)/2
    let ell (i : Fin K × Fin L) := (i.2.val:ℝ)-m
    let z (j : Fin K × Fin L) := r j+β*s j-η
    let c (i : Fin K × Fin L) := (b₀:ℂ)^i.1.val/(i.1.val.factorial:ℂ)
    (Matrix.of (fun (i j : Fin K × Fin L) => ((t j).choose i.1.val:ℂ) *
      Complex.exp (((i.2.val:ℝ)*(r j*γ+s j*θ):ℝ):ℂ))).det =
    (∏ j, Complex.exp ((m*(r j*γ+s j*θ):ℝ):ℂ)) *
      (Matrix.of (fun (i j : Fin K × Fin L) =>
        Complex.exp ((((θ-β*γ)*ell i*s j:ℝ):ℂ)) *
          (c i*(z j:ℂ)^i.1.val*Complex.exp ((γ*ell i*z j:ℝ):ℂ)))).det := by
  intro m ell z c
  let RF (i : Fin K × Fin L) := Complex.exp ((γ*η*ell i:ℝ):ℂ)
  let CF (j : Fin K × Fin L) := Complex.exp ((m*(r j*γ+s j*θ):ℝ):ℂ)
  let w (l : Fin L) (j : Fin K × Fin L) := Complex.exp (((l.val:ℝ)*(r j*γ+s j*θ):ℝ):ℂ)
  let T := Matrix.of (fun (i j : Fin K × Fin L) => Complex.exp (((θ-β*γ)*ell i*s j:ℝ):ℂ) *
      (c i*(z j:ℂ)^i.1.val*Complex.exp ((γ*ell i*z j:ℝ):ℂ)))
  change (Matrix.of (fun (i j : Fin K × Fin L) => ((t j).choose i.1.val:ℂ)*w i.2 j)).det =
    (∏ j, CF j)*T.det
  rw [det_binomial_recenter K L t ((b₀*η:ℝ):ℂ) w]
  have hc : ∑ i, ell i = 0 := centered_sum_zero (Equiv.prodComm (Fin K) (Fin L))
  have hRF : ∏ i, RF i = 1 := by
    simp only [RF, ← Complex.exp_sum, ← Complex.ofReal_sum, ← mul_sum, hc, mul_zero,
      Complex.ofReal_zero, Complex.exp_zero]
  have hmat :
      (Matrix.of fun (i j : Fin K × Fin L) => ((t j:ℂ)-((b₀*η:ℝ):ℂ))^i.1.val/(i.1.val.factorial:ℂ)*w i.2 j) =
      Matrix.of fun i j => RF i * (CF j*T i j) := by
    ext i j
    have hp : (t j:ℂ)-((b₀*η:ℝ):ℂ) = (b₀:ℂ)*(z j:ℂ) := by
      exact_mod_cast (show (t j:ℝ)-b₀*η=b₀*z j by rw [ht]; dsimp [z]; ring)
    have hexp : w i.2 j = RF i * CF j * Complex.exp (((θ-β*γ)*ell i*s j:ℝ):ℂ) *
      Complex.exp ((γ*ell i*z j:ℝ):ℂ) := by
      dsimp only [w,RF,CF]
      simp only [← Complex.exp_add, ← Complex.ofReal_add]
      congr 2
      dsimp [ell,z]
      ring
    simp only [Matrix.of_apply,hp,hexp,T,c,mul_pow]
    ring
  rw [hmat]
  let U := Matrix.of fun i j => CF j*T i j
  change (Matrix.of fun i j => RF i * U i j).det = _
  rw [Matrix.det_mul_column RF U,hRF,one_mul]
  exact Matrix.det_mul_row CF T

end LaurentTwoLog
end

section
/- # Conversion of the integer interpolation minor to a centered analytic determinant -/
open Finset
namespace LaurentTwoLog

theorem natural_powers_exp (a m : ℕ) (ha : 0 < a) :
    (a:ℂ)^m = Complex.exp (((m:ℝ)*Real.log a:ℝ):ℂ) := by
  rw [← Complex.ofReal_exp,Real.exp_nat_mul,Real.exp_log (by exact_mod_cast ha)]
  push_cast
  rfl

/- Identify the exact integer determinant used for the arithmetic lower bound
with the real-exponential model, then factor out its central column term. -/
theorem integer_minor_normalization (a b b₁ b₂ K L : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h₂ : 0 < b₂) (η : ℝ) (r s : Fin K × Fin L → ℕ) :
    let β := (b₁:ℝ)/b₂
    let γ := Real.log a
    let θ := Real.log b
    let m := ((L:ℝ)-1)/2
    let ell (i : Fin K × Fin L) := (i.2.val:ℝ)-m
    let z (j : Fin K × Fin L) := (r j:ℝ)+β*(s j:ℝ)-η
    let c (i : Fin K × Fin L) := (b₂:ℂ)^i.1.val/(i.1.val.factorial:ℂ)
    (integerMinor a b b₁ b₂ (fun i : Fin K × Fin L => i.2.val) (fun i => i.1.val) r s:ℂ) =
      (∏ j, Complex.exp ((m*((r j:ℝ)*γ+(s j:ℝ)*θ):ℝ):ℂ)) *
        (Matrix.of (fun (i j : Fin K × Fin L) =>
          Complex.exp (((θ-β*γ)*ell i*(s j:ℝ):ℝ):ℂ) *
            (c i*(z j:ℂ)^i.1.val*Complex.exp ((γ*ell i*z j:ℝ):ℂ)))).det := by
  intro β γ θ m ell z c
  let t (j : Fin K × Fin L) := r j*b₂+s j*b₁
  have ht (j : Fin K × Fin L) : (t j:ℝ) = (b₂:ℝ)*((r j:ℝ)+β*(s j:ℝ)) := by
    dsimp [t,β]
    push_cast
    have h : (b₂:ℝ) ≠ 0 := by exact_mod_cast h₂.ne'
    field_simp
  have hf := exponential_recenter K L t (fun j => (r j:ℝ)) (fun j => (s j:ℝ))
    (b₂:ℝ) β η γ θ ht
  refine Eq.trans ?_ hf
  dsimp only [integerMinor]
  rw [Int.cast_det]
  congr 1
  ext i j
  simp only [Matrix.map_apply,Matrix.of_apply,Int.cast_mul,Int.cast_natCast,Int.cast_pow]
  rw [natural_powers_exp a _ ha,natural_powers_exp b _ hb,← Complex.exp_add,← Complex.ofReal_add]
  congr 3
  dsimp [γ,θ,t]
  push_cast
  ring

/- The radius used by Laurent's centered grid coordinates. -/
noncomputable def gridRadius (R S : ℕ) (β : ℝ) : ℝ :=
    (((R:ℝ)-1)+β*((S:ℝ)-1))/2

theorem abs_sub_gridRadius {R S : ℕ} (r : Fin R) (s : Fin S) {β : ℝ} (hβ : 0 ≤ β) :
    |(r.val:ℝ)+β*s.val-gridRadius R S β| ≤ gridRadius R S β := by
  have hr : (r.val:ℝ)+1 ≤ R := by exact_mod_cast r.isLt
  have hs : (s.val:ℝ)+1 ≤ S := by exact_mod_cast s.isLt
  dsimp [gridRadius]
  rw [abs_le]
  constructor
  · linarith [Nat.cast_nonneg (α := ℝ) r.val, mul_nonneg hβ (Nat.cast_nonneg (α := ℝ) s.val)]
  · nlinarith [mul_nonneg hβ (sub_nonneg.mpr hs)]

end LaurentTwoLog
end

section
/- # The logarithm of the polynomial part of Laurent's grid bound -/
open Finset
namespace LaurentTwoLog

theorem sum_fin_real (K : ℕ) : (∑ k : Fin K, (k.val:ℝ)) = (K:ℝ)*((K:ℝ)-1)/2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (j:ℝ))]
  induction K with
  | zero => simp
  | succ n ih => rw [sum_range_succ,ih]; push_cast; ring

/- Laurent's total polynomial degree and the complete product of reciprocal
factorials, with each degree occurring once for each of the `L` row levels. -/
theorem log_grid_polynomial_product (K L b₂ : ℕ) {ρ Z : ℝ} (hb : 0 < b₂)
    (hρ : 0 < ρ) (hZ : 0 < Z) :
    Real.log (∏ i : Fin K × Fin L, ‖(b₂:ℂ)^i.1.val/(i.1.val.factorial:ℂ)‖*
      (ρ*Z)^i.1.val) =
      ((K:ℝ)-1)*((K:ℝ)*L)/2*Real.log (ρ*((b₂:ℝ)*Z)) -
        (L:ℝ)*∑ j ∈ range K, Real.log (j.factorial:ℝ) := by
  have hbr : (0:ℝ) < b₂ := by exact_mod_cast hb
  have hfac (k : ℕ) : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hterm (i : Fin K × Fin L) : Real.log (‖(b₂:ℂ)^i.1.val/(i.1.val.factorial:ℂ)‖*
      (ρ*Z)^i.1.val) =
      ((i.1.val:ℝ)*Real.log (ρ*((b₂:ℝ)*Z)) - Real.log (i.1.val.factorial:ℝ)) := by
    simp only [norm_div,norm_pow,Complex.norm_natCast]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (hfac _).ne',
      Real.log_pow, Real.log_pow, Real.log_mul hρ.ne' hZ.ne', Real.log_mul hρ.ne' (by positivity),
      Real.log_mul hbr.ne' hZ.ne']
    ring
  rw [Real.log_prod (fun i _ => by
    simp only [norm_div,norm_pow,Complex.norm_natCast]; positivity)]
  simp_rw [hterm]
  rw [Fintype.sum_prod_type]
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp_rw [mul_sub]
  rw [sum_sub_distrib,← mul_sum,← mul_sum,← sum_mul,sum_fin_real]
  rw [Fin.sum_univ_eq_sum_range (fun t => Real.log (t.factorial:ℝ))]
  ring

end LaurentTwoLog
end

section
/- # The explicit integer-base determinant competition for two logarithms -/

open Finset
namespace LaurentTwoLog

theorem gridCorrection_nonneg (L R S N : ℕ) (hS : 0 < S) (hN : N ≤ R*S) :
    0 ≤ gridCorrection L R S N := by
  have hs : (0:ℝ) < S := by exact_mod_cast hS
  have hN' : (N:ℝ) ≤ R*S := by exact_mod_cast hN
  have he : gridCorrection L R S N = (L:ℝ)*N/(24*S)*(3*(R:ℝ)*S-N) := by
    dsimp [gridCorrection]
    field_simp
    ring
  rw [he]
  apply mul_nonneg (by positivity)
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) R) (Nat.cast_nonneg (α := ℝ) S)]

/- If a nonzero minor exists and the linear form is small, the numeric
Laurent parameter inequality must point in the indicated direction. Its
strict reverse excludes that small linear form. All quantities are explicit. -/
theorem integer_grid_condition_of_small
    (a b b₁ b₂ K L R S : ℕ) (μ ρ : ℝ)
    (col : Fin K × Fin L ↪ Fin R × Fin S)
    (ha : 0 < a) (hb : 0 < b) (h₂ : 0 < b₂)
    (hK : 0 < K) (hR : 0 < R) (hS : 0 < S)
    (hρ : 1 < ρ) (hμ : 1/3 ≤ μ) (hμ' : μ ≤ 1)
    (hZ : 0 < gridRadius R S ((b₁:ℝ)/b₂))
    (horder : ((b₁:ℝ)/b₂)*Real.log a ≤ Real.log b)
    (hdet : integerMinor a b b₁ b₂ (fun i : Fin K × Fin L => i.2.val) (fun i => i.1.val)
      (fun j => (col j).1.val) (fun j => (col j).2.val) ≠ 0)
    (hsmall : |Real.log b-((b₁:ℝ)/b₂)*Real.log a| * ((L:ℝ)/2)*S ≤ ρ^(-μ*((K*L:ℕ):ℝ))) :
    let N := K*L
    let G₁ := gridCorrection L R S N
    let G₂ := gridCorrection L S R N
    let Z := gridRadius R S ((b₁:ℝ)/b₂)
    gainExponent N μ * Real.log ρ ≤
      Real.log (N.factorial:ℝ) + ((K:ℝ)-1)*(N:ℝ)/2*Real.log (ρ*((b₂:ℝ)*Z)) -
        (L:ℝ)*∑ k ∈ range K, Real.log (k.factorial:ℝ) + N +
        (ρ+1)*(G₁*Real.log a+G₂*Real.log b) := by
  classical
  intro N G₁ G₂ Z
  let r (j : Fin K × Fin L) := (col j).1.val
  let s (j : Fin K × Fin L) := (col j).2.val
  let γ := Real.log a
  let θ := Real.log b
  let β := (b₁:ℝ)/b₂
  let m := ((L:ℝ)-1)/2
  let z (j : Fin K × Fin L) := (r j:ℝ)+β*(s j:ℝ)-Z
  let ell (i : Fin K × Fin L) := (i.2.val:ℝ)-m
  let c (i : Fin K × Fin L) := (b₂:ℂ)^i.1.val/(i.1.val.factorial:ℂ)
  let Δ := integerMinor a b b₁ b₂ (fun i : Fin K × Fin L => i.2.val) (fun i => i.1.val) r s
  let T := (Matrix.of fun (i j : Fin K × Fin L) =>
      Complex.exp ((((θ-β*γ)*ell i*(s j:ℝ):ℝ):ℂ)) *
      (c i*(z j:ℂ)^i.1.val*Complex.exp ((γ*ell i*z j:ℝ):ℂ))).det
  let P := ∏ i : Fin K × Fin L, ‖c i‖*(ρ*Z)^i.1.val
  let Xr := m*(∑ j, (r j:ℝ))
  let Xs := m*(∑ j, (s j:ℝ))
  let M := Xr*γ+Xs*θ
  have hcard : Fintype.card (Fin K × Fin L) = N := by simp [N]
  have hρ₀ : 0 < ρ := lt_trans zero_lt_one hρ
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hg : 0 ≤ γ := Real.log_nonneg (by exact_mod_cast ha)
  have hc : (∑ j : Fin K × Fin L, m*((r j:ℝ)*γ+(s j:ℝ)*θ)) = M := by
    dsimp only [M,Xr,Xs]
    simp_rw [mul_add]
    rw [sum_add_distrib,← mul_sum,← mul_sum,← sum_mul,← sum_mul]
    ring
  have hn := integer_minor_normalization a b b₁ b₂ K L ha hb h₂ Z r s
  change (Δ:ℂ) = (∏ j, Complex.exp ((m*((r j:ℝ)*γ+(s j:ℝ)*θ):ℝ):ℂ))*T at hn
  have heval : ‖(Δ:ℂ)‖ = Real.exp M * ‖T‖ := by
    rw [hn,norm_mul,norm_prod]
    simp only [Complex.norm_exp,Complex.ofReal_re,← Real.exp_sum,hc]
  have hsm : ‖((θ-β*γ:ℝ):ℂ)‖*((L:ℝ)/2)*S ≤ ρ^(-μ*(Fintype.card (Fin K × Fin L))) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,hcard] using hsmall
  have hu := centered_grid_upper (Equiv.prodComm (Fin K) (Fin L)) col hK hR hS
    β Z γ ρ Z μ ((θ-β*γ:ℝ):ℂ) c hβ hρ hZ.le hμ hμ' hsm
    (fun j => abs_sub_gridRadius (col j).1 (col j).2 hβ)
  dsimp only at hu
  have hu' : ‖T‖ ≤ (N.factorial:ℝ)*(P*Real.exp (ρ*(γ*(G₁+β*G₂))))*
      ρ^(-gainExponent N μ)*(Real.exp 1)^N := by
    simpa only [T,z,ell,m,r,s,Equiv.prodComm_apply,Prod.swap,hcard,abs_of_nonneg hg,Complex.ofReal_mul,
      Complex.ofReal_natCast,G₁,G₂,P] using hu
  have hupper := mul_le_mul_of_nonneg_left hu' (Real.exp_pos M).le
  rw [← heval] at hupper
  have hΔ₀ : (0:ℝ) < ‖(Δ:ℂ)‖ := norm_pos_iff.mpr (by exact_mod_cast hdet)
  have hlog := Real.log_le_log hΔ₀ hupper
  have hP : 0 < P := by
    apply prod_pos
    intro i _
    dsimp only [c]
    rw [norm_div,norm_pow,Complex.norm_natCast,Complex.norm_natCast]
    have hf : 0 < (i.1.val.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos _
    positivity
  have hfact : 0 < (N.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [Real.log_mul (by positivity) (by positivity),Real.log_exp,
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp,Real.log_rpow hρ₀,Real.log_pow,Real.log_exp,mul_one] at hlog
  have hpoly := log_grid_polynomial_product K L b₂ h₂ hρ₀ hZ
  change Real.log P = _ at hpoly
  rw [hpoly] at hlog
  have hlow := integer_grid_log_minor_lower a b b₁ b₂ K L R S (Equiv.prodComm (Fin K) (Fin L))
    col ha hb hK hR hS hdet
  have hrr : lowerExponent L R S r = Xr-G₁ := by simp [lowerExponent,Xr,m,G₁,gridCorrection,hcard]
  have hss : lowerExponent L S R s = Xs-G₂ := by simp [lowerExponent,Xs,m,G₂,gridCorrection,hcard]
  have habs : ‖(Δ:ℂ)‖ = |(Δ:ℝ)| := by
    change ‖((Δ:ℝ):ℂ)‖ = _
    rw [Complex.norm_real,Real.norm_eq_abs]
  change lowerExponent L R S r*γ + lowerExponent L S R s*θ ≤ Real.log |(Δ:ℝ)| at hlow
  rw [hrr,hss,← habs] at hlow
  have hncap : N ≤ S*R := by
    have h := Fintype.card_le_of_injective _ col.injective
    simpa [hcard,N,Nat.mul_comm] using h
  have hG₂ : 0 ≤ G₂ := gridCorrection_nonneg L S R N hR hncap
  have hph : ρ*γ*(β*G₂) ≤ ρ*θ*G₂ := by
    have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right horder hG₂) hρ₀.le
    change ρ*(β*γ*G₂) ≤ ρ*(θ*G₂) at h
    linarith
  dsimp only [M] at hlog
  have hNr : (N:ℝ) = (K:ℝ)*L := by simp [N]
  rw [← hNr] at hlog
  change gainExponent N μ*Real.log ρ ≤ Real.log (N.factorial:ℝ) + ((K:ℝ)-1)*N/2*Real.log (ρ*((b₂:ℝ)*Z)) - (L:ℝ)*∑ k ∈ range K, Real.log (k.factorial:ℝ) + N + (ρ+1)*(G₁*γ+G₂*θ)
  linarith only [hlow,hlog,hph]

end LaurentTwoLog
end

section
/- # The choice of `ρ=5`, `μ=1/2` for the A113258 determinant bound -/
open Finset
namespace LaurentTwoLog

/- The contrapositive of the determinant competition with the parameters
used for the factorial-power application. -/
theorem five_excludes_small
    (b H p K L R : ℕ) (col : Fin K × Fin L ↪ Fin R × Fin (2*L))
    (hb : 0 < b) (hp : 0 < p) (hK : 0 < K) (hL : 0 < L) (hR : 0 < R)
    (horder : ((H:ℝ)/p)*Real.log 2 ≤ Real.log b)
    (hdet : integerMinor 2 b H p (fun i : Fin K × Fin L => i.2.val) (fun i => i.1.val)
      (fun j => (col j).1.val) (fun j => (col j).2.val) ≠ 0)
    (B : ℝ) (hB : 0 < B) (hBdef : B = (p:ℝ)*gridRadius R (2*L) ((H:ℝ)/p))
    (hparam : (K:ℝ)*(7/8*(L:ℝ)-1)*Real.log 5 >
      2*Real.log ((K:ℝ)*L)+2 + ((K:ℝ)-1)*Real.log B -
        2/(K:ℝ)*(∑ k ∈ range K, Real.log (k.factorial:ℝ)) +
      (1/4-(K:ℝ)/(24*R))*L*(R*(6*Real.log 2)+2*L*(6*Real.log b))) :
    (5:ℝ)^(-(1/2:ℝ)*((K*L:ℕ):ℝ)) <
      |Real.log b-((H:ℝ)/p)*Real.log 2| * ((L:ℝ)/2)*(2*L) := by
  by_contra! hs
  let N := K*L
  let F := ∑ j ∈ range K, Real.log (j.factorial:ℝ)
  let g := 1/4-(K:ℝ)/(24*R)
  have hk : (0:ℝ)<K := by exact_mod_cast hK
  have hl : (0:ℝ)<L := by exact_mod_cast hL
  have hr : (0:ℝ)<R := by exact_mod_cast hR
  have hn : (0:ℝ)<N := by dsimp [N]; positivity
  have hN : (N:ℝ) = (K:ℝ)*L := by dsimp [N]; push_cast; rfl
  have hZ : 0 < gridRadius R (2*L) ((H:ℝ)/p) := by
    rw [hBdef] at hB
    exact pos_of_mul_pos_right hB (Nat.cast_nonneg p)
  have hh := integer_grid_condition_of_small 2 b H p K L R (2*L) (1/2) 5 col (by decide) hb hp hK hR
    (by omega) (by norm_num) (by norm_num) (by norm_num) hZ horder hdet (by simpa using hs)
  dsimp only at hh
  rw [← hBdef,Real.log_mul (by norm_num) hB.ne'] at hh
  have he : gainExponent N (1/2) = ((7/8:ℝ)*(N:ℝ)^2-N)/2 := by
    dsimp [gainExponent]
    ring
  have h₁ : gridCorrection L R (2*L) N = (N:ℝ)/2 * (g*L*R) := by
    dsimp [gridCorrection,g]
    push_cast
    rw [hN]
    field_simp
    ring
  have h₂ : gridCorrection L (2*L) R N = (N:ℝ)/2 * (g*L*(2*L)) := by
    dsimp [gridCorrection,g]
    push_cast
    rw [hN]
    field_simp
    ring
  change gainExponent N (1/2)*Real.log 5 ≤ Real.log (N.factorial:ℝ)+
    ((K:ℝ)-1)*N/2*(Real.log 5+Real.log B) - (L:ℝ)*F + N +
      (5+1)*(gridCorrection L R (2*L) N*Real.log 2+
        gridCorrection L (2*L) R N*Real.log b) at hh
  rw [he,h₁,h₂] at hh
  have hfact := Real.log_le_log (show 0 < (N.factorial:ℝ) by exact_mod_cast Nat.factorial_pos N)
    (show (N.factorial:ℝ) ≤ (N:ℝ)^N by exact_mod_cast N.factorial_le_pow)
  rw [Real.log_pow] at hfact
  have hcmp := mul_lt_mul_of_pos_left hparam (show 0<(N:ℝ)/2 by positivity)
  change (N:ℝ)/2*(2*Real.log ((K:ℝ)*L)+2+((K:ℝ)-1)*Real.log B-2/(K:ℝ)*F+
    g*L*(R*(6*Real.log 2)+2*L*(6*Real.log b))) <
    (N:ℝ)/2*((K:ℝ)*(7/8*(L:ℝ)-1)*Real.log 5) at hcmp
  rw [← hN] at hcmp
  have hf : (N:ℝ)/2*(2/(K:ℝ)*F) = (L:ℝ)*F := by rw [hN]; field_simp
  have ht : (N:ℝ)/2*((K:ℝ)*(7/8*(L:ℝ)-1)*Real.log 5) =
      ((7/8:ℝ)*(N:ℝ)^2-N)/2*Real.log 5 - ((K:ℝ)-1)*N/2*Real.log 5 := by
    rw [hN]
    ring
  rw [ht] at hcmp
  linarith only [hh,hfact,hcmp,hf]

end LaurentTwoLog
end

section
/- # Effective lower bound for the A113258 logarithmic discrepancy -/
open Real Finset LaurentTwoLog
namespace OeisA113258.Direct

/- Kernel-checked effective bound for the moving odd base and coprime
exponents. This follows from the explicit interpolation grid. -/
theorem direct_log_bound : LogBound := by
  intro H p b hp hb hcop hδ
  let L := rows p
  let J := halfColumns L (log b)
  let K := 2*J
  let R := L+J-1
  let B := radiusScale p H R L
  let v := log (b:ℝ)
  let D := (p:ℝ)*v-(H:ℝ)*log 2
  have horder : (H:ℝ)*log 2 ≤ p*log b := by linarith
  obtain ⟨hJ,hL,hR,hS,hB,hpar⟩ := parameters_for_sequence p H b hp hb horder
  change 0 < J at hJ
  change 0 < L at hL
  change 1 < R at hR
  change 2*L ≤ p at hS
  change 0 < B at hB
  have hp₀ : 0 < p := by omega
  have hpr : (0:ℝ) < p := by exact_mod_cast hp₀
  have hLr : (0:ℝ) < L := by exact_mod_cast hL
  have hv : 1 ≤ v := by
    have h := log_le_log (by norm_num : (0:ℝ)<3) (by exact_mod_cast hb : (3:ℝ)≤b)
    dsimp [v]
    linarith [Real.log_three_gt_d9]
  have hδ₀ : 0 < D := hδ
  have horder' : ((H:ℝ)/p)*log 2 ≤ log b := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hpr).mpr (by linarith)
  obtain ⟨col,hdet⟩ := direct_minor (H := H) (p := p) (b := b) hJ hL hp₀
    (by omega) hcop hS
  have hBdef : B = (p:ℝ)*gridRadius R (2*L) ((H:ℝ)/p) := by
    dsimp only [B,radiusScale,gridRadius]
    push_cast
    field_simp
  have hbound := five_excludes_small b H p K L R col (by omega) hp₀ (by dsimp [K]; omega)
    hL (by omega) horder' hdet B hB hBdef hpar
  have hD : log b-((H:ℝ)/p)*log 2 = D/p := by
    dsimp only [D,v]
    field_simp
  have hscaled : |log b-((H:ℝ)/p)*log 2| * ((L:ℝ)/2)*(2*L) ≤ D := by
    rw [hD,abs_of_nonneg (div_nonneg hδ₀.le hpr.le)]
    have hsquare : (L:ℝ)^2 ≤ p := row_square (by exact_mod_cast hp)
    have hle := mul_le_mul_of_nonneg_left hsquare hδ₀.le
    apply (le_of_mul_le_mul_right (a := (p:ℝ)) _ hpr)
    field_simp
    linarith only [hsquare,hle]
  have hlog := log_lt_log (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<5) _) (hbound.trans_le hscaled)
  rw [log_rpow (by norm_num)] at hlog
  have hK : (K:ℝ) ≤ 6*(L:ℝ)*v+2 := (columns_bounds L (by linarith : 0≤v)).2
  have hn : ((K*L:ℕ):ℝ) = (K:ℝ)*L := by push_cast; rfl
  rw [hn] at hlog
  have hKL : (K:ℝ)*L*log 5 ≤ (6*(L:ℝ)^2+2*L)*v*1.62 := by
    calc
      (K:ℝ)*L*log 5 ≤ ((6*(L:ℝ)*v+2)*L)*1.62 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hK hLr.le) log_five_bounds.2.le
          (by linarith [log_five_bounds.1]) (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hLr.le (sub_nonneg.mpr hv)]
  change -0.81*(6*(L:ℝ)^2+2*L)*v < log D
  linarith only [hlog,hKL]

end OeisA113258.Direct
end

section
/- Unconditional consequences of the direct determinant inequality for A113258. -/
namespace OeisA113258.Direct

/- The complete prime-exponent cutoff with no analytic premise. -/
theorem exponent_cutoff : AnalyticCutoff := analyticCutoff_of_logBound direct_log_bound

/- Every A113258 term from index 5 through index 100 is not a nontrivial integer power. -/
theorem no_perfect_power_through_100 {n b e : ℕ} (hn : 5 ≤ n) (h100 : n ≤ 100)
    (he : 2 ≤ e) : a n ≠ b^e := by
  intro h
  by_cases h8 : n ≤ 8
  · exact ne_power_five_to_eight hn h8 he h
  let p := e.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega : e ≠ 1)
  have hd : p ∣ e := Nat.minFac_dvd e
  obtain ⟨j, hj⟩ := hd
  have hpow : a n = (b^j)^p := by rw [h,hj,← pow_mul,Nat.mul_comm p j]
  have h6 := (exponent_cutoff n p (b^j) (by omega) hp hpow).1
  exact no_perfect_power_through_100_of_small_factor hn h100 he hp ⟨j,hj⟩ h6 h

/- The only remaining input for the global negative answer is the finite certificate. -/
end OeisA113258.Direct
end

section
/- The sharper determinant window for terms of index above 100. -/
namespace OeisA113258.Direct
open Real

/- The fixed-grid endpoint contradiction used on 1300 ≤ p < 3000. -/
def FixedWindowEndpoint : Prop :=
  ∀ {N F p b : ℕ}, 1300 ≤ p → p < 3000 → 3 ≤ b → 1000 ≤ log (b:ℝ) → p.Coprime N →
    (0.96:ℝ)*N ≤ (N:ℝ)-4*F → 4*F ≤ N → (2:ℕ)^N < b^p → b^p < 2^N+2^(4*F) → False

/- For n ≥ 101 the moving-base logarithm exceeds 1000 in the unresolved window. -/
theorem cutoff_1300_of_endpoint (hcoarse : AnalyticCutoff) (hfixed : FixedWindowEndpoint)
    {n p b : ℕ} (hn : 101 ≤ n) (hp : p.Prime) (hab : a n = b^p) : p < 1300 := by
  obtain ⟨_,hlo3⟩ := hcoarse n p b (by omega) hp hab
  have hp3 := hlo3.resolve_right (by omega)
  by_contra! h1300
  have hnp := exponent_factors_ge_index (by omega : 4<n) hp (dvd_refl p) hp.two_le hab
  have hc : p.Coprime (n-1).factorial := hp.coprime_iff_not_dvd.mpr (by rw [hp.dvd_factorial]; omega)
  have hterm : FactorialSeries.term n = a n := by
    simp only [FactorialSeries.term, FactorialSeries.partialSum_eq, a]
  obtain ⟨hlo,hhi⟩ := FactorialSeries.gap_bounds (by omega : 9≤n)
  rw [hterm,hab] at hlo hhi
  have hN : 5000000 ≤ (n-1).factorial :=
    (by decide : 5000000 ≤ Nat.factorial 11).trans (Nat.factorial_le (by omega))
  have hb : 3 ≤ b := by
    by_contra! hsmall
    have hmono := Nat.pow_le_pow_left (show b ≤ 2 by omega) p
    have hexp := Nat.pow_le_pow_right (by decide : 0<2) (show p ≤ (n-1).factorial by omega)
    exact (not_lt_of_ge (hmono.trans hexp)) hlo
  have hfac : (n-1).factorial = (n-1)*(n-2).factorial := by
    rw [show n-1=n-2+1 by omega,Nat.factorial_succ]
  have hh : 100*(n-2).factorial ≤ (n-1).factorial := by
    rw [hfac]; exact Nat.mul_le_mul_right _ (by omega)
  have hF : 4*(n-2).factorial ≤ (n-1).factorial := by omega
  have hhR : 100*((n-2).factorial:ℝ) ≤ (n-1).factorial := by exact_mod_cast hh
  have hdelta := (discrepancy_of_gap hb hF hlo hhi).1
  have hpR : (p:ℝ) < 3000 := by exact_mod_cast hp3
  have hNR : (5000000:ℝ) ≤ (n-1).factorial := by exact_mod_cast hN
  have hlog : 1000 ≤ log (b:ℝ) := by
    by_contra! hl
    have hbl : 0 ≤ log (b:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤b))
    have hsm : (p:ℝ)*log b ≤ 3000*1000 := mul_le_mul hpR.le hl.le hbl (by norm_num)
    have hlg : (0.6:ℝ) ≤ log 2 := by linarith [Real.log_two_gt_d9]
    have hbig : (5000000:ℝ)*0.6 ≤ ((n-1).factorial:ℝ)*log 2 := mul_le_mul hNR hlg (by norm_num) (by positivity)
    linarith only [hsm,hbig,hdelta]
  exact hfixed h1300 hp3 hb hlog hc (by linarith only [hhR]) hF hlo hhi

/- Modular witnesses remaining after the first hundred indices and the fixed-grid bound. -/
def TailCoverage1300 : Prop :=
  ∀ n p : ℕ, 101 ≤ n → p.Prime → n ≤ p → p < 1300 →
    ∃ q : ℕ, q.Prime ∧ p ∣ q-1 ∧ (a n : ZMod q) ≠ 0 ∧ (a n : ZMod q)^((q-1)/p) ≠ 1

end OeisA113258.Direct
end

section
/- # The fixed 16-level grid at large integer base -/
open Real Finset LaurentTwoLog
namespace OeisA113258.Direct

/- Consequence of the fixed-grid parameter inequality. The logarithm of the
moving integer base is large enough to absorb the rounding in `K=2J`. -/
theorem fixed_log_of_parameters (H p b : ℕ) (hp : 1300 ≤ p) (hb : 3 ≤ b)
    (hv : 1000 ≤ log (b:ℝ)) (hcop : p.Coprime H)
    (hδ : 0 < (p:ℝ)*log b - H*log 2)
    (hpgrid :
      let L : ℕ := 16
      let J := halfColumns L (log b)
      let K := 2*J
      let R := L+J-1
      let B := radiusScale p H R L
      0<J ∧ 0<L ∧ 1<R ∧ 2*L ≤ p ∧ 0<B ∧
        (K:ℝ)*(7/8*(L:ℝ)-1)*log 5 >
          2*log ((K:ℝ)*L)+2+((K:ℝ)-1)*log B -
            2/(K:ℝ)*(∑ j ∈ range K, log (j.factorial:ℝ)) +
          (1/4-(K:ℝ)/(24*R))*L*((R:ℝ)*(6*log 2)+2*L*(6*log b))) :
    -1245*log b < log ((p:ℝ)*log b-H*log 2) := by
  let L : ℕ := 16
  let J := halfColumns L (log b)
  let K := 2*J
  let R := L+J-1
  let B := radiusScale p H R L
  let v := log (b:ℝ)
  let D := (p:ℝ)*v-(H:ℝ)*log 2
  obtain ⟨hJ,hL,hR,hS,hB,hpar⟩ := hpgrid
  change 0 < J at hJ
  change 0 < L at hL
  change 1 < R at hR
  change 2*L ≤ p at hS
  change 0 < B at hB
  have hp₀ : 0 < p := by omega
  have hpr : (0:ℝ) < p := by exact_mod_cast hp₀
  have hδ₀ : 0 < D := hδ
  have horder' : ((H:ℝ)/p)*log 2 ≤ log b := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hpr).mpr (by linarith)
  obtain ⟨col,hdet⟩ := direct_minor (H := H) (p := p) (b := b) hJ hL hp₀
    (by omega) hcop hS
  have hBdef : B = (p:ℝ)*gridRadius R (2*L) ((H:ℝ)/p) := by
    dsimp only [B,radiusScale,gridRadius]
    push_cast
    field_simp
  have hbound := five_excludes_small b H p K L R col (by omega) hp₀ (by dsimp [K]; omega)
    hL (by omega) horder' hdet B hB hBdef hpar
  have hD : log b-((H:ℝ)/p)*log 2 = D/p := by
    dsimp only [D,v]
    field_simp
  have hscaled : |log b-((H:ℝ)/p)*log 2| * ((L:ℝ)/2)*(2*L) ≤ D := by
    rw [hD,abs_of_nonneg (div_nonneg hδ₀.le hpr.le)]
    have hsquare : (L:ℝ)^2 ≤ p := by
      norm_num [L]
      exact_mod_cast (by omega : 256 ≤ p)
    have hle := mul_le_mul_of_nonneg_left hsquare hδ₀.le
    apply (le_of_mul_le_mul_right (a := (p:ℝ)) _ hpr)
    field_simp
    linarith only [hsquare,hle]
  have hlog := log_lt_log (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<5) _) (hbound.trans_le hscaled)
  rw [log_rpow (by norm_num)] at hlog
  have hv' : 1000 ≤ v := hv
  have hK : (K:ℝ) ≤ 96*v+2 := by
    have h := (columns_bounds L (by linarith only [hv'] : 0≤v)).2
    change (K:ℝ) ≤ 6*(16:ℝ)*v+2 at h
    linarith only [h]
  have hn : ((K*L:ℕ):ℝ) = (K:ℝ)*16 := by simp [L]
  rw [hn] at hlog
  have hKL : (K:ℝ)*16*log 5 ≤ 2490*v := by
    calc
      (K:ℝ)*16*log 5 ≤ ((96*v+2)*16)*1.62 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hK (by norm_num)) log_five_bounds.2.le
          (by linarith [log_five_bounds.1]) (by positivity)
      _ ≤ _ := by linarith only [hv']
  change -1245*v < log D
  linarith only [hlog,hKL]

end OeisA113258.Direct
end

section
/- A fixed 16-row grid excludes the entire high-exponent window once
the unknown base has logarithm at least 1000. -/
open Real Finset
namespace OeisA113258.Direct

private theorem DirectFixedParameters_fixed_inequality {p H v K R F B : ℝ}
    (hp : 1300 ≤ p) (hhi : p < 3000) (hv : 1000 ≤ v)
    (hK : 96*v ≤ K) (hR : 0<R) (hRK : R ≤ K/2+16)
    (hH : H*log 2 ≤ p*v) (hB : 0<B)
    (hBval : 2*B ≤ R*p + 32*H)
    (hfac : K*(K-1)*log K - 2*K*(K-1) ≤ 2*F) :
    K*(7/8*16-1)*log 5 >
      2*log (K*16)+2+(K-1)*log B-2/K*F+
      (1/4-K/(24*R))*16*(R*(6*log 2)+2*16*(6*v)) := by
  have hK0 : 0<K := by linarith
  have hp0 : 0<p := by linarith
  have hrmax : R ≤ 0.501*K := by linarith
  have hcor : 1/4-K/(24*R) ≤ 0.167 := by
    have hh : 0.083 ≤ K/(24*R) := (le_div_iff₀ (by positivity)).mpr (by linarith)
    linarith
  have hlog2 : log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  have hsum : R*(6*log 2) + 2*16*(6*v) ≤ 4.105*K := by
    nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hlog2)]
  have harg : 0 ≤ 16*(R*(6*log 2)+2*16*(6*v)) := by
    have : 0 < log 2 := by linarith [Real.log_two_gt_d9]
    positivity
  have hg : (1/4-K/(24*R))*16*(R*(6*log 2)+2*16*(6*v)) ≤ 10.97*K := by
    have h := mul_le_mul_of_nonneg_right hcor harg
    nlinarith only [h,hsum,hK0]
  have hH' : H ≤ 1.5*p*v := by
    by_cases hh : 0 ≤ H
    · nlinarith [mul_nonneg hh (sub_nonneg.mpr (le_of_lt (by linarith [Real.log_two_gt_d9] : 2/3<log 2)))]
    · have hpos : 0 ≤ p*v := mul_nonneg hp0.le (by linarith)
      linarith
  have hB' : B ≤ 0.501*K*p := by
    nlinarith only [mul_le_mul_of_nonneg_right hrmax hp0.le,
      mul_le_mul_of_nonneg_right hK hp0.le,hH',hBval,mul_pos hK0 hp0]
  have hlogB : log B ≤ log K+log p-0.499 := by
    have hh := log_le_log hB hB'
    rw [log_mul (by positivity) hp0.ne', log_mul (by norm_num) hK0.ne'] at hh
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<0.501)]
  have hlogp : log p < 8.05 := by
    have hh := log_lt_log hp0 hhi
    have h3 := Real.log_lt_log (by norm_num : 0<(5:ℝ)^3) (by norm_num : (5:ℝ)^3<2^7)
    rw [log_pow,log_pow] at h3
    rw [show (3000:ℝ) = 3*(2*5)^3 by norm_num,log_mul (by norm_num) (by norm_num),
      log_pow,log_mul (by norm_num) (by norm_num)] at hh
    norm_num1 at h3 hh
    linarith [Real.log_three_lt_d9,Real.log_two_lt_d9]
  have hm : log 10000 < 10 := by
    rw [show (10000:ℝ) = (2*5)^4 by norm_num,log_pow, log_mul (by norm_num) (by norm_num)]
    norm_num1
    linarith [Real.log_two_lt_d9,log_five_bounds.2]
  have hr := Real.log_le_sub_one_of_pos (by linarith : 0<K/10000)
  rw [log_div hK0.ne' (by norm_num)] at hr
  have hOF : 2*log (K*16)+2 ≤ 0.02*K := by
    rw [log_mul hK0.ne' (by norm_num)]
    have h16 := log_le_log (by norm_num : (0:ℝ)<16) (by linarith : 16≤K)
    linarith
  have hFI : (K-1)*log K-2*(K-1) ≤ 2/K*F := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hK0).mpr (by linarith only [hfac])
  have ha : log B ≤ log K+7.551 := by linarith
  have hcoeff := mul_le_mul_of_nonneg_left ha (by linarith : 0 ≤ K-1)
  have h5 := mul_lt_mul_of_pos_right log_five_bounds.1 hK0
  nlinarith only [h5,hOF,hcoeff,hFI,hg,hK0]

theorem parameters_full (p H b : ℕ) (hp : 1300 ≤ p) (hhi : p < 3000)
    (hv : 1000 ≤ log (b:ℝ)) (horder : (H:ℝ)*log 2 ≤ p*log b) :
    let L : ℕ := 16
    let J := halfColumns L (log b)
    let K := 2*J
    let R := L+J-1
    let B := radiusScale p H R L
    0<J ∧ 0<L ∧ 1<R ∧ 2*L ≤ p ∧ 0<B ∧
    (K:ℝ)*(7/8*(L:ℝ)-1)*log 5 >
      2*log ((K:ℝ)*L)+2+((K:ℝ)-1)*log B -
      2/(K:ℝ)*(∑ j ∈ range K, log (j.factorial:ℝ)) +
      (1/4-(K:ℝ)/(24*R))*L*((R:ℝ)*(6*log 2)+2*L*(6*log b)) := by
  intro L J K R B
  have hp' : (1300:ℝ) ≤ p := by exact_mod_cast hp
  have hhi' : (p:ℝ)<3000 := by exact_mod_cast hhi
  have hl : (L:ℝ)=16 := by norm_num [L]
  have hK' : 6*(L:ℝ)*log b ≤ K := (columns_bounds L (by linarith : 0≤log b)).1
  have hK : 96*log (b:ℝ) ≤ K := by linarith only [hK',hl, (congrArg (fun x : ℝ => 6*x*log b) hl)]
  have hc : (K:ℝ) = 2*(J:ℝ) := by dsimp [K]; push_cast; rfl
  have hj : 0<J := by exact_mod_cast (by linarith : (0:ℝ)<J)
  have hr : 1<R := by dsimp [R,L]; omega
  have hr' : (1:ℝ)<R := by exact_mod_cast hr
  have hRcast : (R:ℝ) = (L:ℝ)+J-1 := by
    dsimp [R]; rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  have hBpos : 0<B := by
    dsimp only [B,radiusScale]
    exact div_pos (add_pos_of_pos_of_nonneg (mul_pos (by linarith) (by linarith)) (mul_nonneg (Nat.cast_nonneg _) (by linarith))) (by norm_num)
  refine ⟨hj,by decide,hr,by dsimp [L]; omega,hBpos,?_⟩
  have hf := Analysis.log_product_factorials_lower K (by dsimp [K]; omega)
  rw [Real.log_prod (fun j _ => by exact_mod_cast (Nat.factorial_pos j).ne')] at hf
  rw [hl]
  apply DirectFixedParameters_fixed_inequality (H := (H:ℝ)) hp' hhi' hv hK (by linarith) (by linarith) horder hBpos _ hf
  dsimp only [B,radiusScale]
  rw [hl]
  nlinarith [Nat.cast_nonneg (α:=ℝ) H]

end OeisA113258.Direct
end

section
open Real
namespace OeisA113258.Direct

/- The effective lower bound at fixed row height 16, for (1300 ≤ p < 3000)
and `log b ≥ 1000`. -/
theorem direct_fixed_log_bound (H p b : ℕ) (hp1300 : 1300 ≤ p) (hp3000 : p < 3000)
    (hb : 3 ≤ b) (hlog : 1000 ≤ Real.log (b:ℝ)) (hcop : p.Coprime H)
    (hpos : 0 < (p:ℝ)*Real.log b-H*Real.log 2) :
    -1245*Real.log b < Real.log ((p:ℝ)*Real.log b-H*Real.log 2) :=
  fixed_log_of_parameters H p b hp1300 hb hlog hcop hpos
    (parameters_full p H b hp1300 hp3000 hlog (by linarith))

/- The fixed-grid logarithm bound contradicts the gap inherited from two
successive factorial indices when at least 96 percent of the exponent remains. -/
theorem fixed_endpoint_contradiction {N F p b : ℕ} (hp1300 : 1300 ≤ p) (hp3000 : p < 3000)
    (hb : 3 ≤ b) (hlog : 1000 ≤ Real.log (b:ℝ)) (hcop : p.Coprime N)
    (hsize : 0.96*N ≤ (N:ℝ)-4*F)
    (hF : 4*F ≤ N) (hlo : (2:ℕ)^N < b^p) (hhi : b^p < 2^N+2^(4*F)) : False := by
  obtain ⟨hpos,hgap,hup⟩ := discrepancy_of_gap hb hF hlo hhi
  have hl := direct_fixed_log_bound N p b hp1300 hp3000 hb hlog hcop hpos
  have h2 : (0:ℝ) < log 2 := Real.log_pos (by norm_num)
  have h2b : log 2 ≤ log (b:ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2≤b))
  have hbp : ((p:ℝ)-1)*log b ≤ (N:ℝ)*log 2 := by linarith only [hup,h2b]
  have hnum : 1245 < 0.96*((p:ℝ)-1) := by
    have h : (1300:ℝ) ≤ p := by exact_mod_cast hp1300
    linarith
  have hchain := calc
    1245*log b < (0.96*((p:ℝ)-1))*log b := mul_lt_mul_of_pos_right hnum (by linarith)
    _ = 0.96*(((p:ℝ)-1)*log b) := by ring
    _ ≤ 0.96*((N:ℝ)*log 2) := mul_le_mul_of_nonneg_left hbp (by norm_num)
    _ = (0.96*N)*log 2 := by ring
    _ ≤ ((N:ℝ)-4*F)*log 2 := mul_le_mul_of_nonneg_right hsize h2.le
  linarith only [hl,hgap,hchain]

end OeisA113258.Direct
end

section
namespace OeisA113258.Chain

open PackedCompute

/- A witness excludes the p-th power representation for term n. -/
def Witness (n p : ℕ) : Prop :=
  ∃ q : ℕ, q.Prime ∧ p ∣ q-1 ∧ (seq n : ZMod q) ≠ 0 ∧
    (seq n : ZMod q)^((q-1)/p) ≠ 1

/- Correct recurrence state and proofs for all eligible rows through n. -/
end OeisA113258.Chain
end

section
namespace OeisA113258.Chain1300

open PackedCompute

abbrev Witness := Chain.Witness

/- Correct recurrence state and proofs for all eligible rows through n. -/
def Prefix (n m : ℕ) (last : State) : Prop :=
  state m n = last ∧
    ∀ k p : ℕ, 9 ≤ k → k ≤ n → p.Prime → k ≤ p → p < 6000 →
      (p < 1300 ∨ k ≤ 100) → Witness k p

/- The first hundred rows use the separately verified full-range witnesses.
The packed state is recomputed for the smaller modulus of the late checks. -/
theorem start {m : ℕ} {last : State} {rs : List ℕ}
    (hrun : checkpoint m last 0 (reduceState m (1, [])) rs = true)
    (hlen : rs.length = 100) : Prefix 100 m last := by
  have hst : reduceState m (1, []) = state m 0 := rfl
  rw [hst] at hrun
  obtain ⟨_,hend⟩ := checkpoint_sound hrun
  rw [Nat.zero_add, hlen] at hend
  refine ⟨hend, ?_⟩
  intro k p h9 h100 hp hkp h6 _
  exact Interval9To100.certificates_up_to_100 k p h9 h100 hp hkp h6

/- A segment may discard modulus factors once all its future checks are covered by the remainder. -/
theorem extend {n0 old newM : ℕ} {start last : State}
    {rs : List ℕ} {book : BookCheck.Book}
    (hpref : Prefix n0 old start) (hdiv : newM ∣ old)
    (hrun : checkpoint newM last n0 (reduceState newM start) rs = true)
    (hchecks : BookCheck.checked (n0+1) rs book = true)
    (hvalid : BookCheck.validBook newM book = true)
    (hcover : ∀ p : ℕ, p.Prime → max 9 (n0+1) ≤ p →
        p < (if n0 < 100 then 6000 else 1300) → p ∈ book.map Prod.fst) :
    Prefix (n0+rs.length) newM last := by
  obtain ⟨hst,hold⟩ := hpref
  rw [← hst, reduceState_correct hdiv] at hrun
  obtain ⟨hr, hlast⟩ := checkpoint_sound hrun
  refine ⟨hlast, ?_⟩
  intro k p h9 hlen hprime hkp h6 h3
  by_cases hprevious : k ≤ n0
  · exact hold k p h9 hprevious hprime hkp h6 h3
  · have hstart : n0+1 ≤ k := by omega
    have hend : k < (n0+1)+rs.length := by omega
    have hmax : max 9 (n0+1) ≤ p := by omega
    have hbound : p < (if n0 < 100 then 6000 else 1300) := by
      split <;> omega
    have hres : ∀ i : Fin rs.length, seq ((n0+1)+i.val) % newM = rs[i.val] := by
      intro i
      have h := replay_sound hr i
      have hh : rs[i] = rs[i.val] := by cases i; rfl
      rw [Nat.add_right_comm n0 1 i.val]
      exact h.trans hh
    exact BookCheck.witness_of_checked power_eq hchecks hvalid hres
      (hcover p hprime hmax hbound) hstart hend h9 hkp

/- Beyond row 1299 the analytic domain is empty since then n ≤ p < 1300. -/
theorem finish {m : ℕ} {s : State} (h : Prefix 1299 m s) :
    ∀ n p : ℕ, 9 ≤ n → p.Prime → n ≤ p → p < 6000 →
      (p < 1300 ∨ n ≤ 100) → Witness n p := by
  intro n p hn hp hnp h6 h3
  exact h.2 n p hn (by omega) hp hnp h6 h3

end OeisA113258.Chain1300
end

section
/- Unconditional sharper cutoff and the reduction to the remaining modular certificates. -/
namespace OeisA113258.Direct

/- Above index 100, every hypothetical prime exponent is below 1300. -/
theorem exponent_cutoff_1300 {n p b : ℕ} (hn : 101 ≤ n) (hp : p.Prime)
    (hab : a n = b^p) : p < 1300 :=
  cutoff_1300_of_endpoint exponent_cutoff (by intro N F p b; exact @fixed_endpoint_contradiction N F p b) hn hp hab

/- Every term from index 1300 onward is unconditionally free of nontrivial powers. -/
theorem no_perfect_power_of_tail1300 (hc : TailCoverage1300) :
    ¬ (∃ n > 4, ∃ b > 1, ∃ e > 1, a n = b^e) := by
  rintro ⟨n,hn,b,_,e,he,hab⟩
  by_cases hs : n ≤ 100
  · exact no_perfect_power_through_100 hn hs he hab
  let p := e.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega : e ≠ 1)
  have hdiv : p ∣ e := Nat.minFac_dvd e
  have hnp := exponent_factors_ge_index hn hp hdiv he hab
  obtain ⟨j,hj⟩ := hdiv
  have hpow : a n = (b^j)^p := by rw [hab,hj,← pow_mul,Nat.mul_comm p j]
  have h101 : 101 ≤ n := by omega
  have h1300 := exponent_cutoff_1300 h101 hp hpow
  obtain ⟨q,hq,hd,hz,hw⟩ := hc n p h101 hp hnp h1300
  exact exclude_power_by_witness hq hd hz hw _ hpow

/- Kernel replay of the final packed numerical prefix completes the exact upstream claim. -/
theorem no_perfect_power_of_prefix1300 {m : ℕ} {s : PackedCompute.State}
    (h : Chain1300.Prefix 1299 m s) : ¬ (∃ n > 4, ∃ b > 1, ∃ e > 1, a n = b ^ e) := by
  apply no_perfect_power_of_tail1300
  intro n p hn hp hnp hp13
  exact Chain1300.finish h n p (by omega) hp hnp (by omega) (Or.inl hp13)

end OeisA113258.Direct
end

section
namespace OeisA113258.Compact
open PackedCompute BookCheck

theorem certifyBlock {n old m k : ℕ} {s : State} {v : List Nat × State} {book : Book}
    (hn : 100 ≤ n) (prev : Chain1300.Prefix n old s) (hd : m ∣ old)
    (block : blockResult m k n (reduceState m s) = v)
    (hc : checked (n+1) v.1 book = true)
    (hg : gcdValidBook m book = true) (hk : book.map Prod.fst = gcdPrimeKeys (n+1) 1300) :
    Chain1300.Prefix (n+k) m v.2 := by
  have hv := verified_block block
  have hp := Chain1300.extend prev hd hv.2 hc
    (validBook_of_fast (by rw [← gcdValidBook_eq]; exact hg)) (by
      intro p hprime hlo hhi
      have hlo' : n+1 ≤ p := by omega
      have hhi' : p < 1300 := by simpa [if_neg (not_lt.mpr hn)] using hhi
      rw [hk,gcdPrimeKeys_eq,mem_primeKeys]
      exact ⟨hlo',hhi',hprime⟩)
  rw [hv.1] at hp
  exact hp

end OeisA113258.Compact
end

section
namespace OeisA113258.BookCheck

theorem checked_append_true {n : Nat} {rs : List Nat} {a b : Book}
    (ha : checked n rs a = true) (hb : checked n rs b = true) :
    checked n rs (a++b) = true := by
  rw [checked_append, ha, hb]
  rfl

end OeisA113258.BookCheck
end

namespace OeisA113258.Block0
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x4ae4d779acb0f65df78a4407a98af9b85eecf0679bad9e1de4cac6483ee0b4f5f82b885acfabf62f91506489c4bbbb8c71d3c2de43eb7ec32c4dc23395972ab34dee198e4c5c24afcf36e88cfbd8e436612fb4836ff22f70dce5370b8a773b99c6c20b5941af37e21941d107b481cc0877172d8988d446c7c5366494d7130bdc9f25537fc3cee54d954cdc3eb8b45b9fccb76bdb7a894ffd1b1431b4136ba1f704e974ced414f1dd52ff763e1ee40f6e49196c03d1e0bbbc3e854d9602a18d7a422783f4da2449af9f7be7e0426366c167a359d9646e2518afeae015646a99f818003a726b288419f961868bcc1ca741478d20e5b1591a9d83acf11f1b4383ffee4a2b7b9a01f9e51f272af89e7f806e156bc8c6162df56a97672a84fa86481fa170b370b615088d1ecd28c8586807f3ab6152c173f98379b40deed53cfae38b6c755f21be93d14b59a590091eb5f69dee8fe6ea68237ad56dc5217d7202d9847258a8a67044e8610447c07a005bcc9a4359a63684668b109f47c25239e2d4a30c6cbca46f39f49dd7dd41d18cdf6ea626358ac30b9bbdf370591b7d8a818474a9a01fc977cf12e522a2cbce6bbf6ed80777c055422ea235116cdf62e1ef37702aef61523f3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 100 0 (reduceState modulus (1,[])) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
theorem verified : Chain1300.Prefix 100 modulus last :=
  Chain1300.start (verified_block data.property).2 (verified_block data.property).1
end OeisA113258.Block0
namespace OeisA113258.Block1
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x4ae4d779acb0f65df78a4407a98af9b85eecf0679bad9e1de4cac6483ee0b4f5f82b885acfabf62f91506489c4bbbb8c71d3c2de43eb7ec32c4dc23395972ab34dee198e4c5c24afcf36e88cfbd8e436612fb4836ff22f70dce5370b8a773b99c6c20b5941af37e21941d107b481cc0877172d8988d446c7c5366494d7130bdc9f25537fc3cee54d954cdc3eb8b45b9fccb76bdb7a894ffd1b1431b4136ba1f704e974ced414f1dd52ff763e1ee40f6e49196c03d1e0bbbc3e854d9602a18d7a422783f4da2449af9f7be7e0426366c167a359d9646e2518afeae015646a99f818003a726b288419f961868bcc1ca741478d20e5b1591a9d83acf11f1b4383ffee4a2b7b9a01f9e51f272af89e7f806e156bc8c6162df56a97672a84fa86481fa170b370b615088d1ecd28c8586807f3ab6152c173f98379b40deed53cfae38b6c755f21be93d14b59a590091eb5f69dee8fe6ea68237ad56dc5217d7202d9847258a8a67044e8610447c07a005bcc9a4359a63684668b109f47c25239e2d4a30c6cbca46f39f49dd7dd41d18cdf6ea626358ac30b9bbdf370591b7d8a818474a9a01fc977cf12e522a2cbce6bbf6ed80777c055422ea235116cdf62e1ef37702aef61523f3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 50 100 (reduceState modulus Block0.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(101,[607]),(103,[619]),(107,[643]),(109,[1091]),(113,[227,1583]),(127,[509]),(131,[263]),(137,[823]),(139,[557]),(149,[1193]),(151,[907]),(157,[1571]),(163,[653]),(167,[2339,5011]),(173,[347,1039]),(179,[359]),(181,[1087]),(191,[383,2293]),(193,[773,1931]),(197,[3547])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 101 rs part0 = true := rfl
noncomputable def part1 : Book := [(199,[797]),(211,[2111,4643]),(223,[2677]),(227,[5449]),(229,[2749]),(233,[467,1399]),(239,[479]),(241,[1447]),(251,[503]),(257,[1543]),(263,[1579]),(269,[2153]),(271,[1627]),(277,[1109]),(281,[563,3373]),(283,[1699]),(293,[587,1759]),(307,[1229,5527]),(311,[1867]),(313,[1879])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 101 rs part1 = true := rfl
noncomputable def part2 : Book := [(317,[8243]),(331,[1987,5297]),(337,[3371]),(347,[2083]),(349,[3491]),(353,[4943]),(359,[719]),(367,[2203]),(373,[1493]),(379,[4549]),(383,[4597]),(389,[9337]),(397,[2383]),(401,[3209]),(409,[1637]),(419,[839]),(421,[4211]),(431,[863]),(433,[1733]),(439,[4391])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 101 rs part2 = true := rfl
noncomputable def part3 : Book := [(443,[887,2659]),(449,[3593]),(457,[13711]),(461,[2767]),(463,[5557]),(467,[2803]),(479,[3833]),(487,[1949]),(491,[983]),(499,[1997]),(503,[3019]),(509,[1019]),(521,[16673]),(523,[5231]),(541,[9739]),(547,[5471]),(557,[3343]),(563,[7883]),(569,[6829]),(571,[5711])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 101 rs part3 = true := rfl
noncomputable def part4 : Book := [(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131]),(617,[4937,23447]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells4 : checked 101 rs part4 = true := rfl
noncomputable def part5 : Book := [(701,[12619,21031]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523,4567]),(769,[7691]),(773,[4639,9277]),(787,[4723]),(797,[4783,11159]),(809,[1619]),(811,[8111]),(821,[6569,14779]),(823,[8231]),(827,[11579]),(829,[8291,9949])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells5 : checked 101 rs part5 = true := rfl
noncomputable def part6 : Book := [(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433,11149]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817,13679])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells6 : checked 101 rs part6 = true := rfl
noncomputable def part7 : Book := [(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211,12253]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691,12829]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells7 : checked 101 rs part7 = true := rfl
noncomputable def part8 : Book := [(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027,25763]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491,22483]),(1259,[17627])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells8 : checked 101 rs part8 = true := rfl
noncomputable def part9 : Book := [(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells9 : checked 101 rs part9 = true := rfl
noncomputable def book : Book := (((part0 ++ part1) ++ (part2 ++ (part3 ++ part4))) ++ ((part5 ++ part6) ++ (part7 ++ (part8 ++ part9))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 101 rs book = true := (checked_append_true (a := ((part0 ++ part1) ++ (part2 ++ (part3 ++ part4)))) (b := ((part5 ++ part6) ++ (part7 ++ (part8 ++ part9)))) (checked_append_true (a := (part0 ++ part1)) (b := (part2 ++ (part3 ++ part4))) (checked_append_true (a := part0) (b := part1) cells0 cells1) (checked_append_true (a := part2) (b := (part3 ++ part4)) cells2 (checked_append_true (a := part3) (b := part4) cells3 cells4))) (checked_append_true (a := (part5 ++ part6)) (b := (part7 ++ (part8 ++ part9))) (checked_append_true (a := part5) (b := part6) cells5 cells6) (checked_append_true (a := part7) (b := (part8 ++ part9)) cells7 (checked_append_true (a := part8) (b := part9) cells8 cells9))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 150 modulus last :=
  certifyBlock (by decide) Block0.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block1
namespace OeisA113258.Block2
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0xab4b3bacde565bb75ed72279d5291e47e962edc465a111981d6c5844cfea1ae40a21503ea3a34007c96169143532a0854cf7d50fbe44dc6378be3ec6c17fc261a7a4e7c43205f338c09ee423d238f9606e9331b86baa1b4c385c30b0c48f8972acda527c9f2884d57d1d54963c69b4b6b3ff931a60daf068822b8b6b72e3377b0da4cd1962c28ddcbd665f0d7292044ec8e60c41b9ec9f80f844054038cd125f598648d79339f8767d102750fc5f6d72b7c90a1ede143f673a2ad3efed4644a8a9b78afcf47fc61320185f109c67a60e0a55101c0bc2891199af09c3e0d2bafe594becb8de8b846e9fab88f86aa9c37a750186ee00eb9b28a247ccd66c55cfe1e4823a1860f8524cd3a33ce472b1124a8617bbb1dcdf33e2f5c5df10db076d0cb57ac0b84f03bb8e7a5622b960cffc3eb3a5573f7531feda4048e4250e9d0f59a436dd141c599ccb1d94c4346db9fc47f888c07474cbb2c093b7599103b341888a5ba6acfd327aa4a66e158d8a9e1e17524ab2da0ba0985238085c5a646b7ec1953fd16f366edff76d113d2a0e65f17b6219c8d314f25afa02cb3fb9fa7dc4c2e23463046de3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 50 150 (reduceState modulus Block1.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(151,[907]),(157,[1571]),(163,[653]),(167,[2339]),(173,[347]),(179,[359]),(181,[1087]),(191,[383]),(193,[773]),(197,[3547]),(199,[797]),(211,[2111,4643]),(223,[2677]),(227,[5449]),(229,[2749]),(233,[467]),(239,[479]),(241,[1447]),(251,[503,4519]),(257,[1543])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 151 rs part0 = true := rfl
noncomputable def part1 : Book := [(263,[1579]),(269,[2153,3229]),(271,[1627]),(277,[1109]),(281,[563,3373]),(283,[1699]),(293,[587]),(307,[1229]),(311,[1867,3733]),(313,[1879]),(317,[8243]),(331,[1987]),(337,[3371]),(347,[2083]),(349,[3491]),(353,[4943]),(359,[719]),(367,[2203]),(373,[1493]),(379,[4549])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 151 rs part1 = true := rfl
noncomputable def part2 : Book := [(383,[4597]),(389,[9337]),(397,[2383]),(401,[3209]),(409,[1637]),(419,[839]),(421,[4211]),(431,[863]),(433,[1733,5197]),(439,[4391]),(443,[887]),(449,[3593,6287]),(457,[13711,16453]),(461,[2767]),(463,[5557]),(467,[2803]),(479,[3833]),(487,[1949,4871]),(491,[983]),(499,[1997])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 151 rs part2 = true := rfl
noncomputable def part3 : Book := [(503,[3019]),(509,[1019,4073]),(521,[16673]),(523,[5231]),(541,[9739]),(547,[5471]),(557,[3343]),(563,[7883,11261]),(569,[6829]),(571,[5711,9137]),(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131]),(617,[4937]),(619,[2477]),(631,[6311])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 151 rs part3 = true := rfl
noncomputable def part4 : Book := [(641,[1283]),(643,[7717,10289]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells4 : checked 151 rs part4 = true := rfl
noncomputable def part5 : Book := [(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells5 : checked 151 rs part5 = true := rfl
noncomputable def part6 : Book := [(911,[1823,23687]),(919,[3677]),(929,[7433]),(937,[5623,9371]),(941,[5647]),(947,[5683]),(953,[1907,11437]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells6 : checked 151 rs part6 = true := rfl
noncomputable def part7 : Book := [(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497,16619])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells7 : checked 151 rs part7 = true := rfl
noncomputable def part8 : Book := [(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells8 : checked 151 rs part8 = true := rfl
noncomputable def book : Book := (((part0 ++ part1) ++ (part2 ++ part3)) ++ ((part4 ++ part5) ++ (part6 ++ (part7 ++ part8))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 151 rs book = true := (checked_append_true (a := ((part0 ++ part1) ++ (part2 ++ part3))) (b := ((part4 ++ part5) ++ (part6 ++ (part7 ++ part8)))) (checked_append_true (a := (part0 ++ part1)) (b := (part2 ++ part3)) (checked_append_true (a := part0) (b := part1) cells0 cells1) (checked_append_true (a := part2) (b := part3) cells2 cells3)) (checked_append_true (a := (part4 ++ part5)) (b := (part6 ++ (part7 ++ part8))) (checked_append_true (a := part4) (b := part5) cells4 cells5) (checked_append_true (a := part6) (b := (part7 ++ part8)) cells6 (checked_append_true (a := part7) (b := part8) cells7 cells8))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 200 modulus last :=
  certifyBlock (by decide) Block1.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block2
namespace OeisA113258.Block3
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0xb6651cb3282ef5920604917ffcb681c1aacc0a62199a57d9ec6d97ff9dc62691b14cdc130677cef50235e4cf571aa8ce729d3ed3f9c8f71518acd31add4cc150b02f1f6f21a4ee3839ee67e983aea5601278aebd0d8ba7a7907e3d110eff2889390558de462ddf74bcf6bcbbbea2f0bff3b8016d2bbd2a8896a9f13dce8d41355ccd82ad316685615cfeb8b11db9ec30c8903fd9d8abbb7ae86789b91547ae199b3bd104fe91821748967886bee3e4df07419581e710278d62458604b91296a612359749cf9497eb85f5f72dbad5a4e33b881959e1556aab2f87cbd1e298a5ef4a6543f6123b6c9d3a944402564fafd6657e5806bb2f4a8d42a4d8183416a030a729b932591d1e66e61d921339683f3bd13fe96336c7e78c3bbf4de3aee5c6da1d571661e2f4e4f7b62a275bb2a8fa153bb9b68d4bfa6b71effd2e79d5b560a12a43d7011066fafe9430eccd9122b6c704b5d85fec87d3a471f13b35a303a91d02e125a37ccc06f8bf20711b02cf33de8520109c60a3badf0a806a6115119be33f8cbb7edd24b696d61f
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 39 200 (reduceState modulus Block2.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(211,[2111]),(223,[2677]),(227,[5449]),(229,[2749]),(233,[467]),(239,[479]),(241,[1447]),(251,[503,4519]),(257,[1543]),(263,[1579]),(269,[2153]),(271,[1627]),(277,[1109]),(281,[563]),(283,[1699]),(293,[587]),(307,[1229]),(311,[1867,3733]),(313,[1879]),(317,[8243]),(331,[1987]),(337,[3371,5393]),(347,[2083]),(349,[3491]),(353,[4943])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 201 rs part0 = true := rfl
noncomputable def part1 : Book := [(359,[719,10771]),(367,[2203]),(373,[1493]),(379,[4549]),(383,[4597]),(389,[9337]),(397,[2383]),(401,[3209]),(409,[1637]),(419,[839]),(421,[4211]),(431,[863]),(433,[1733]),(439,[4391]),(443,[887]),(449,[3593]),(457,[13711]),(461,[2767]),(463,[5557]),(467,[2803]),(479,[3833]),(487,[1949]),(491,[983]),(499,[1997]),(503,[3019])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 201 rs part1 = true := rfl
noncomputable def part2 : Book := [(509,[1019]),(521,[16673]),(523,[5231]),(541,[9739]),(547,[5471]),(557,[3343]),(563,[7883]),(569,[6829]),(571,[5711]),(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131]),(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 201 rs part2 = true := rfl
noncomputable def part3 : Book := [(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911,8293]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957,17737]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523,4567]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 201 rs part3 = true := rfl
noncomputable def part4 : Book := [(853,[3413]),(857,[6857]),(859,[18899,25771]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells4 : checked 201 rs part4 = true := rfl
noncomputable def part5 : Book := [(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367,27673]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells5 : checked 201 rs part5 = true := rfl
noncomputable def part6 : Book := [(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447,17123]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791,15349]),(1283,[7699]),(1289,[2579,10313]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells6 : checked 201 rs part6 = true := rfl
noncomputable def book : Book := ((part0 ++ (part1 ++ part2)) ++ ((part3 ++ part4) ++ (part5 ++ part6)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 201 rs book = true := (checked_append_true (a := (part0 ++ (part1 ++ part2))) (b := ((part3 ++ part4) ++ (part5 ++ part6))) (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2)) (checked_append_true (a := (part3 ++ part4)) (b := (part5 ++ part6)) (checked_append_true (a := part3) (b := part4) cells3 cells4) (checked_append_true (a := part5) (b := part6) cells5 cells6)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 239 modulus last :=
  certifyBlock (by decide) Block2.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block3
namespace OeisA113258.Block4
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x34cb4ba371f6144d7179f6ef3dda5c631e76c90c78ed58af6cdc5e930cb69aaa8bbe510e98a72fb1851f4853f4035b67fd2e65e6c1cc3e0037e6d4d7ef48c84cc7af91aa54de681512339307a6841dc0b08e5f683de61c087c8d0005da6050c2f1d8a79710beae41c0fc8dcdc084c5facaad7d41a66e575fa4975a3d32f9724b093e56be5ee88271a235f42ec4ccb4c7d90b4d743186d12abaccb9722b65cc09e44edd25a26a2c64037252a7df1623501e653f8c6c56156457e67861d50359ae4595d13076a49664889234436e312d13cca5c18549d4a584059f468f172243f4e9d898a5122869223c8ead88f1a46c0170df120e90f3a6b96ed1cf2f8542f97a559f67cde9d5ea788654041d2b3c3acb0c603958989151ec0cf830a11ce5bee58aca8bbcde66701a36d27e4b48cefdadc2ea662f7782b55c2851720d6dd0cb02f16d4cb37de0f1153c690f8d133fdad3da41bf880d2d0565ac4e398180bf26e2c348644b204ba1b69904bfc23b183085c3d990b
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 33 239 (reduceState modulus Block3.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(241,[1447]),(251,[503]),(257,[1543]),(263,[1579]),(269,[2153]),(271,[1627,2711]),(277,[1109]),(281,[563]),(283,[1699]),(293,[587,1759]),(307,[1229]),(311,[1867]),(313,[1879]),(317,[8243]),(331,[1987]),(337,[3371]),(347,[2083,2777]),(349,[3491]),(353,[4943]),(359,[719]),(367,[2203]),(373,[1493]),(379,[4549]),(383,[4597]),(389,[9337]),(397,[2383]),(401,[3209]),(409,[1637]),(419,[839]),(421,[4211])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 240 rs part0 = true := rfl
noncomputable def part1 : Book := [(431,[863,3449]),(433,[1733]),(439,[4391]),(443,[887]),(449,[3593]),(457,[13711]),(461,[2767]),(463,[5557]),(467,[2803]),(479,[3833]),(487,[1949]),(491,[983]),(499,[1997]),(503,[3019]),(509,[1019]),(521,[16673]),(523,[5231]),(541,[9739]),(547,[5471]),(557,[3343]),(563,[7883]),(569,[6829]),(571,[5711]),(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 240 rs part1 = true := rfl
noncomputable def part2 : Book := [(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967,7933]),(673,[2693,24229]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837,12763]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 240 rs part2 = true := rfl
noncomputable def part3 : Book := [(823,[8231,19753]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647,7529]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827,19421]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989,23929]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 240 rs part3 = true := rfl
noncomputable def part4 : Book := [(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613,18919]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027,25763]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells4 : checked 240 rs part4 = true := rfl
noncomputable def part5 : Book := [(1237,[19793,44533]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells5 : checked 240 rs part5 = true := rfl
noncomputable def book : Book := ((part0 ++ (part1 ++ part2)) ++ (part3 ++ (part4 ++ part5)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 240 rs book = true := (checked_append_true (a := (part0 ++ (part1 ++ part2))) (b := (part3 ++ (part4 ++ part5))) (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2)) (checked_append_true (a := part3) (b := (part4 ++ part5)) cells3 (checked_append_true (a := part4) (b := part5) cells4 cells5)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 272 modulus last :=
  certifyBlock (by decide) Block3.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block4
namespace OeisA113258.Block5
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x39913e2a66319c3ab8e5cb250875665cb429a4b56d33939a7f4f33643d5d78eeb327dbca9559559394b4bbb62f074319e90ceeadd99a8fabe61b26d069e57fea80d7f2c58fba60721ef19e37f3942abd320d49526e8438464ca5e3dbc9b582573e6be8867c08ca02f67f9fe6b178fb50cbc41d2eba0eb3b17cb430a057e785372b4c5b8e81400cfe8c2bb014f3fc2ef7442681e5181a851098c34b651255aa297d0472cdd148fbb7ab22227caa8ff8bd38cb35862408edbdad107b44685f222717c1c09028723176d99d81d4099462733d39ec702c89e851fd2d53498f61a2868b7f6bf89ff5f5842778d8cc1c03ccff4dd1ace24bc788e3dfe8a9d00110b3ab56e0b9c02ead0fd2a3708cb53c43221751e4e8a3ca213fa925bd9a4a4a1ca2617aea4a2c2df82c53ae9a1052e2eec391a57df3ea005f8beb23e810b63b3ab8a764377a4b9fa61ef7ab7c1aea1fe29d481bcab586a7c815270c5f7900cbdd45cad
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 29 272 (reduceState modulus Block4.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(277,[1109]),(281,[563]),(283,[1699]),(293,[587]),(307,[1229]),(311,[1867]),(313,[1879]),(317,[8243]),(331,[1987]),(337,[3371]),(347,[2083]),(349,[3491]),(353,[4943,14827]),(359,[719]),(367,[2203]),(373,[1493]),(379,[4549]),(383,[4597]),(389,[9337]),(397,[2383]),(401,[3209]),(409,[1637,4091]),(419,[839]),(421,[4211]),(431,[863]),(433,[1733]),(439,[4391]),(443,[887]),(449,[3593]),(457,[13711]),(461,[2767]),(463,[5557]),(467,[2803]),(479,[3833])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 273 rs part0 = true := rfl
noncomputable def part1 : Book := [(487,[1949]),(491,[983]),(499,[1997]),(503,[3019]),(509,[1019]),(521,[16673]),(523,[5231]),(541,[9739]),(547,[5471]),(557,[3343]),(563,[7883]),(569,[6829]),(571,[5711]),(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131]),(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417,9479]),(683,[1367]),(691,[6911]),(701,[12619])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 273 rs part1 = true := rfl
noncomputable def part2 : Book := [(709,[2837,12763]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 273 rs part2 = true := rfl
noncomputable def part3 : Book := [(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039,32609]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 273 rs part3 = true := rfl
noncomputable def part4 : Book := [(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells4 : checked 273 rs part4 = true := rfl
noncomputable def book : Book := ((part0 ++ part1) ++ (part2 ++ (part3 ++ part4)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 273 rs book = true := (checked_append_true (a := (part0 ++ part1)) (b := (part2 ++ (part3 ++ part4))) (checked_append_true (a := part0) (b := part1) cells0 cells1) (checked_append_true (a := part2) (b := (part3 ++ part4)) cells2 (checked_append_true (a := part3) (b := part4) cells3 cells4)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 301 modulus last :=
  certifyBlock (by decide) Block4.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block5
namespace OeisA113258.Block6
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x905e0a552260eb803d4acfc5cb48ede7129d3f13dc589f9729277a74cf067ffa205ff85a7ca114310fbaa49e6dfc89e6b68ac05dc35069163a206d4f4166c19332352ee4844b2ba9c1c0cf0373ce4130df6c5bd74beb7e658f11b16cb89070f0b30d8f67db107cd576836f2268407952c4a520c396956ef56d508f2a743c54ce411f42ffea06484059a1db7c100308ba8a712e92c5086324584fd986ec299c418a62c796a38a97ef12156bc32ddd48f0f41446008e3c90428955ae8c324f541b2b5cb5f702f608f74bc5d23329a465dfb67926d29b3945660b500e60484de26677fc22c74694f50cbd47cc2384c480ddbb35b36b0a1d09d07114aedba7426d7adb3b644fba0338ff8653a4faaba91a38915d381724d4f5136b8ba8449ad2821175559331d9e82190ade390d82e40f7a0957f3ca106f10fe2dba8344f9ebc2fb3e5a7f8f0e2ff567bf80735624ed55ab72b2501e0533b1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 26 301 (reduceState modulus Block5.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(307,[1229]),(311,[1867]),(313,[1879]),(317,[8243]),(331,[1987]),(337,[3371]),(347,[2083]),(349,[3491]),(353,[4943]),(359,[719]),(367,[2203]),(373,[1493]),(379,[4549]),(383,[4597]),(389,[9337]),(397,[2383]),(401,[3209]),(409,[1637]),(419,[839]),(421,[4211]),(431,[863]),(433,[1733]),(439,[4391]),(443,[887,2659]),(449,[3593]),(457,[13711]),(461,[2767]),(463,[5557]),(467,[2803]),(479,[3833]),(487,[1949]),(491,[983]),(499,[1997]),(503,[3019]),(509,[1019]),(521,[16673])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 302 rs part0 = true := rfl
noncomputable def part1 : Book := [(523,[5231]),(541,[9739]),(547,[5471]),(557,[3343]),(563,[7883]),(569,[6829]),(571,[5711]),(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131]),(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 302 rs part1 = true := rfl
noncomputable def part2 : Book := [(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899,25771]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443,27211]),(911,[1823]),(919,[3677]),(929,[7433,11149]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 302 rs part2 = true := rfl
noncomputable def part3 : Book := [(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 302 rs part3 = true := rfl
noncomputable def part4 : Book := [(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells4 : checked 302 rs part4 = true := rfl
noncomputable def book : Book := ((part0 ++ part1) ++ (part2 ++ (part3 ++ part4)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 302 rs book = true := (checked_append_true (a := (part0 ++ part1)) (b := (part2 ++ (part3 ++ part4))) (checked_append_true (a := part0) (b := part1) cells0 cells1) (checked_append_true (a := part2) (b := (part3 ++ part4)) cells2 (checked_append_true (a := part3) (b := part4) cells3 cells4)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 327 modulus last :=
  certifyBlock (by decide) Block5.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block6
namespace OeisA113258.Block7
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x2a23a2276ce4671a1ac788c7eb6de2ed992a0ea7d409b7578ac4f607054374b8aaf203b2a225df10c950fe980f1f80c8222e04ca1d562d67c625d81acc3b8a69714f9f54a4708d7ca25944cb1055e8328046a8d1040fcdc48d44a1b82f4af40a82f35ebdda7652985694210f3703ddce768a99242525212b223000ba7c95c103321ccadb864001ce50861c8b78cf8cd89c46253ed4d8b8be0abb45746de4ce557a96ccecfcd4ba7cfb9e1d5740d127f56cf4d62819f9d793e2438729dbed5a0a26be32463ca597af02a55f06ce660c1659512caa3bb24510ea8770929a787e3c95f7c69a0755d327daa5ed529492eafa7022f80c74bf85056a94f71dad28d0d166f8ca02566cb8ebccca220d16d9368911613f4f09d9496b59e7a7c811a63fdcdbc7d742b6f9f5c15e93182eac220a905515f7ba68feca5a855f24e7773b42f551506374f23b168e5be9e4c9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 24 327 (reduceState modulus Block6.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(331,[1987]),(337,[3371]),(347,[2083]),(349,[3491,8377]),(353,[4943]),(359,[719]),(367,[2203]),(373,[1493]),(379,[4549]),(383,[4597]),(389,[9337]),(397,[2383]),(401,[3209]),(409,[1637]),(419,[839]),(421,[4211]),(431,[863]),(433,[1733]),(439,[4391]),(443,[887]),(449,[3593]),(457,[13711]),(461,[2767,9221]),(463,[5557]),(467,[2803]),(479,[3833]),(487,[1949]),(491,[983]),(499,[1997,10979]),(503,[3019]),(509,[1019]),(521,[16673]),(523,[5231]),(541,[9739]),(547,[5471]),(557,[3343])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 328 rs part0 = true := rfl
noncomputable def part1 : Book := [(563,[7883]),(569,[6829]),(571,[5711]),(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131]),(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331,16127]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 328 rs part1 = true := rfl
noncomputable def part2 : Book := [(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 328 rs part2 = true := rfl
noncomputable def part3 : Book := [(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 328 rs part3 = true := rfl
noncomputable def part4 : Book := [(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells4 : checked 328 rs part4 = true := rfl
noncomputable def book : Book := ((part0 ++ part1) ++ (part2 ++ (part3 ++ part4)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 328 rs book = true := (checked_append_true (a := (part0 ++ part1)) (b := (part2 ++ (part3 ++ part4))) (checked_append_true (a := part0) (b := part1) cells0 cells1) (checked_append_true (a := part2) (b := (part3 ++ part4)) cells2 (checked_append_true (a := part3) (b := part4) cells3 cells4)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 351 modulus last :=
  certifyBlock (by decide) Block6.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block7
namespace OeisA113258.Block8
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0xb4851b89ed45e646cdabc8b0a510f67b01cc4f61ea38597e156a1d8b2ebdd78ded97afd0545ce729fd2fb35f46accc235530c83b42801a97eacd1c3f093bef12e52ce9f1a311714300fa80a5d0f5026006173b126d69dc71bf0d87da9e1883971e914d7eec077c6f63cf0aa6e43651f86e3746b641745c6cce28c18953c40aaf34c099f1255f5a1acb23abeb8452a4f71ebf04ba5e0bb3cc668b40e0905700b3785d0db9416f8bb9e76b32f6b9ed324d878e733a51aa9a228593e828da1f32259ad0d5f2baf14cea8627e76feff7589f993d4590237c4c365d977d8457a416539b8cebf14d47ae974d8be7f4135db08a3fc6369e2386a71a6d85ba5a9e4e532c71b52e527180fa63be726c465328fdc6adf819a1ebab791cd560539dcc05f419c5628c0e74d4969ae79f8585f9166daa0fabba7e66237f956dfd2bb5f4ddd7611d
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 22 351 (reduceState modulus Block7.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(353,[4943]),(359,[719]),(367,[2203]),(373,[1493]),(379,[4549]),(383,[4597]),(389,[9337]),(397,[2383,6353]),(401,[3209]),(409,[1637]),(419,[839,5867]),(421,[4211]),(431,[863]),(433,[1733]),(439,[4391]),(443,[887]),(449,[3593]),(457,[13711]),(461,[2767,9221]),(463,[5557]),(467,[2803]),(479,[3833]),(487,[1949]),(491,[983]),(499,[1997]),(503,[3019]),(509,[1019,4073]),(521,[16673]),(523,[5231]),(541,[9739]),(547,[5471]),(557,[3343]),(563,[7883]),(569,[6829]),(571,[5711]),(577,[2309])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 352 rs part0 = true := rfl
noncomputable def part1 : Book := [(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131]),(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 352 rs part1 = true := rfl
noncomputable def part2 : Book := [(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677,20219]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 352 rs part2 = true := rfl
noncomputable def part3 : Book := [(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027,25763]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 352 rs part3 = true := rfl
noncomputable def book : Book := ((part0 ++ part1) ++ (part2 ++ part3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 352 rs book = true := (checked_append_true (a := (part0 ++ part1)) (b := (part2 ++ part3)) (checked_append_true (a := part0) (b := part1) cells0 cells1) (checked_append_true (a := part2) (b := part3) cells2 cells3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 373 modulus last :=
  certifyBlock (by decide) Block7.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block8
namespace OeisA113258.Block9
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0xb011311c8777ff01fcd825095c6445f422c80c1592583a4192c253707f767ffe215ddfe7260529bc567fc2091b690d6aee0205baf3e58d74d2426466c524de094a50da25a4d8a09858849b9d8161af16083d5c62247ef369fe2f50bc152123d553ab5a7cab988ee53de85b79bdb48d126d7b46da87e9a6f86614446c181cc01be5d492d0b38ec5075d006336ed645270f72a6868bb72fd6ce00ae0fee6b9388675287e030d08a63e65f2c1a3ab21093f801bef85681245a033dc11497e6aa7d2450e2164e729b2a3709d5bdf261f9303221d607f15e981fb6794e6eeb93e6c382e699b514ac63757da3bffdb654cf7d57508265dc5eb77d50e4fefc12711ecc818c4004a8237f41f102988551b334aa2d4968973750876dc403219311dc4e95515b1c1b7592afc02db69c56f6826e71e60f8b9dd27
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 21 373 (reduceState modulus Block8.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(379,[4549]),(383,[4597]),(389,[9337]),(397,[2383]),(401,[3209]),(409,[1637]),(419,[839]),(421,[4211]),(431,[863,3449]),(433,[1733]),(439,[4391]),(443,[887]),(449,[3593,6287]),(457,[13711,16453]),(461,[2767]),(463,[5557,11113]),(467,[2803]),(479,[3833,5749]),(487,[1949]),(491,[983]),(499,[1997]),(503,[3019]),(509,[1019]),(521,[16673]),(523,[5231]),(541,[9739]),(547,[5471]),(557,[3343]),(563,[7883]),(569,[6829]),(571,[5711]),(577,[2309,3463]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 374 rs part0 = true := rfl
noncomputable def part1 : Book := [(607,[3643]),(613,[6131]),(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291,9949]),(839,[10069])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 374 rs part1 = true := rfl
noncomputable def part2 : Book := [(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 374 rs part2 = true := rfl
noncomputable def part3 : Book := [(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 374 rs part3 = true := rfl
noncomputable def book : Book := ((part0 ++ part1) ++ (part2 ++ part3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 374 rs book = true := (checked_append_true (a := (part0 ++ part1)) (b := (part2 ++ part3)) (checked_append_true (a := part0) (b := part1) cells0 cells1) (checked_append_true (a := part2) (b := part3) cells2 cells3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 394 modulus last :=
  certifyBlock (by decide) Block8.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block9
namespace OeisA113258.Block10
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x31f29c13793fdc60d74f2c9edf8b6663bab17ce7f6524604e002fef1485488f29ec0451606442aeed845a0efff23bc9d31c8e0e69e21e2a4fbfb3697927fa85ac289a44761424551c8c465c14f28e69f3cd46df0a63ca97bfdb310a9c17a31e0950560db6454bc37570a7a8972c7f5ebdb9a83b8752147846c29ed8bae5f5edaecc14549addf5232c16d0b31e0b4e9a38f25e948b3497942acd39f26d6e8623f630af40cbdd6cc79844627b868f75ac35dd19853c4596ee06f1cd44d3b4f81882038e7facfaa7248d7eef755c7c5d9645a91e50b7be61f5934fda570b0dfabd8b157d373e29a0d1f7dc46926aecd9382deea731a89172d0aa5c2deb2990ce657a8baba7aad6c7c6c24e226861ce78a8628e7b567ea5497ec0463026140ecf336915a39014bc2da3ff
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 20 394 (reduceState modulus Block9.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(397,[2383]),(401,[3209]),(409,[1637]),(419,[839]),(421,[4211]),(431,[863]),(433,[1733,5197]),(439,[4391]),(443,[887]),(449,[3593]),(457,[13711]),(461,[2767]),(463,[5557]),(467,[2803]),(479,[3833]),(487,[1949]),(491,[983]),(499,[1997]),(503,[3019]),(509,[1019,4073]),(521,[16673]),(523,[5231]),(541,[9739]),(547,[5471]),(557,[3343]),(563,[7883]),(569,[6829]),(571,[5711]),(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131]),(617,[4937])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 395 rs part0 = true := rfl
noncomputable def part1 : Book := [(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059,12941]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417,9479]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 395 rs part1 = true := rfl
noncomputable def part2 : Book := [(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 395 rs part2 = true := rfl
noncomputable def part3 : Book := [(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217,48847]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 395 rs part3 = true := rfl
noncomputable def book : Book := ((part0 ++ part1) ++ (part2 ++ part3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 395 rs book = true := (checked_append_true (a := (part0 ++ part1)) (b := (part2 ++ part3)) (checked_append_true (a := part0) (b := part1) cells0 cells1) (checked_append_true (a := part2) (b := part3) cells2 cells3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 414 modulus last :=
  certifyBlock (by decide) Block9.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block10
namespace OeisA113258.Block11
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0xd952adacb58ac8471f9c1da0482549b76041bdc1d21a733624f49b7e6ff657620f0c4c6f386d294f67b8d29ebfbc0700916d16a51172658840068d311496d0762f45ca84b35b05cc5c8dfd354db0af6e05ace9c4b00aaf682cf5234216b82a135d5bec1380b1473786c0b7f55d126af84f870c3990e2af2956efaf308e8eaef82cdefe9bf260b0fd34ea0493bd3790dcbdff27d01403c7c9116fc50407d548848c1cc148e7e0589c0a46601e0e2b9cab4995f40e8aa262f9a99d7bae049949b882317dc2af1f7c7e7cb9fa02629d955dcefde57677b9b736e2d3a8b07ca6fa90c90a0556601f57b146e4c0a533af8e3bc14c1e27546c1a2e783b22d56c9a886851b9aca17ee5a5c65ec3124a3e0a12e3b7a04afd8ad08125b9dbc72ae584768841
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 19 414 (reduceState modulus Block10.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(419,[839]),(421,[4211]),(431,[863,3449]),(433,[1733]),(439,[4391,13171]),(443,[887]),(449,[3593]),(457,[13711]),(461,[2767]),(463,[5557]),(467,[2803]),(479,[3833]),(487,[1949]),(491,[983]),(499,[1997]),(503,[3019]),(509,[1019]),(521,[16673]),(523,[5231]),(541,[9739]),(547,[5471]),(557,[3343]),(563,[7883]),(569,[6829]),(571,[5711]),(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131]),(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 415 rs part0 = true := rfl
noncomputable def part1 : Book := [(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 415 rs part1 = true := rfl
noncomputable def part2 : Book := [(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367,21221]),(1063,[4253]),(1069,[10691]),(1087,[4349,17393]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 415 rs part2 = true := rfl
noncomputable def part3 : Book := [(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 415 rs part3 = true := rfl
noncomputable def book : Book := ((part0 ++ part1) ++ (part2 ++ part3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 415 rs book = true := (checked_append_true (a := (part0 ++ part1)) (b := (part2 ++ part3)) (checked_append_true (a := part0) (b := part1) cells0 cells1) (checked_append_true (a := part2) (b := part3) cells2 cells3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 433 modulus last :=
  certifyBlock (by decide) Block10.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block11
namespace OeisA113258.Block12
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x10b398ec44a560d15710171c62e4d40497dd7fc976c4676cbeae10a7a28b93e9103b4cf2bbdfa3626955ad75db22b58ec9051543cf4b3a6f65c01dab8a875ed78b92b672a423302fd32e9af89283bac837cc0765583cec186ffadc39ca3b0c7ca3ece3412db413e30bc4b244972a0426ebebd177ff8c81430dee9e60a950149aa6c038abb61c37e01539f8fc3e03aa13a756840a625662022ca1b9399f813bb7bed9d2ff9edcddc0626f0a5d3c00c50eb26224508c313108120e0e56a85c40c991a5c2523fe7b2a1f421ee1bf8d32582dc1816c27d53519aa86b2203379dc14090da9ed3077e1f6f0929718a3df35d9c05918497830782960b58bafca18cc53ec9e05e8636655565ea8b7259a25bae5b47daaf77436f0961b5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 18 433 (reduceState modulus Block11.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(439,[4391]),(443,[887]),(449,[3593]),(457,[13711]),(461,[2767]),(463,[5557]),(467,[2803]),(479,[3833]),(487,[1949]),(491,[983]),(499,[1997]),(503,[3019]),(509,[1019]),(521,[16673]),(523,[5231]),(541,[9739]),(547,[5471]),(557,[3343]),(563,[7883]),(569,[6829]),(571,[5711]),(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131]),(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319,5273])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 434 rs part0 = true := rfl
noncomputable def part1 : Book := [(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231,19753]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 434 rs part1 = true := rfl
noncomputable def part2 : Book := [(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473,23209]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133,6199]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 434 rs part2 = true := rfl
noncomputable def part3 : Book := [(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 434 rs part3 = true := rfl
noncomputable def book : Book := ((part0 ++ part1) ++ (part2 ++ part3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 434 rs book = true := (checked_append_true (a := (part0 ++ part1)) (b := (part2 ++ part3)) (checked_append_true (a := part0) (b := part1) cells0 cells1) (checked_append_true (a := part2) (b := part3) cells2 cells3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 451 modulus last :=
  certifyBlock (by decide) Block11.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block12
namespace OeisA113258.Block13
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x1101b5227fa966784e1a5b0dc4174cc460fd37d84a27ef26a8b1bcdcdbb90dedc095664625e1520ada853c55156b4926382095f303d66fa3498151704292c2c83c6568f1ae816060cc4a97d293d369bc4b15d645a6e73f5a2cb361f537f29ab58aea55a967f9c3bf33927d6a23c5d6e48241204169a768e7e549cbed048cb13bbf37e2ec00d3130000de7701a71c289ee03209c236a1abf77572cb3ccad213297b4a7bef79442d995c04a32724a7393bb6245f55946e2038323d42cad9bf51c63419bc222529f62505413f90eecf99eec012cd0f9cda0507a78a49f6430529755a0826744d08fad23e4d9b0edc1550686ab24d80c1daeb82cb856de431a9e69931cd3fb5be40e245a71aa99ec2f9ec526890e5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 17 451 (reduceState modulus Block12.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(457,[13711]),(461,[2767]),(463,[5557]),(467,[2803]),(479,[3833]),(487,[1949]),(491,[983]),(499,[1997]),(503,[3019]),(509,[1019]),(521,[16673]),(523,[5231]),(541,[9739]),(547,[5471]),(557,[3343]),(563,[7883]),(569,[6829]),(571,[5711]),(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607,6011]),(607,[3643]),(613,[6131]),(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 452 rs part0 = true := rfl
noncomputable def part1 : Book := [(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639,15461]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 452 rs part1 = true := rfl
noncomputable def part2 : Book := [(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 452 rs part2 = true := rfl
noncomputable def part3 : Book := [(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 452 rs part3 = true := rfl
noncomputable def book : Book := ((part0 ++ part1) ++ (part2 ++ part3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 452 rs book = true := (checked_append_true (a := (part0 ++ part1)) (b := (part2 ++ part3)) (checked_append_true (a := part0) (b := part1) cells0 cells1) (checked_append_true (a := part2) (b := part3) cells2 cells3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 468 modulus last :=
  certifyBlock (by decide) Block12.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block13
namespace OeisA113258.Block14
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x1765ce99d20e3f2fc2e78f23ce6784c8ea9906811eab0f84fb28102ec3fd4da990179d676115742095158eecf233439ece2b2c5de55a6a559c184301869a8dae6b27966024596c0ccb3d07599ab4663e7688f4d7e758a2b097cfa3dfe510bb26753457a889ff2d00ac9b1014ac666df507e3a2dfb07746117fba9f8762d351d03481dcef2af42e1a9764d70451f7989f8981e82da84e0a789576926fe568154417f5831265f969c7afc7dd1239cbc5539c3f1b4babf01eeea22609f6b1e4e5b537d5dc0f680fbf5015935d10a9e3ad6e2f67ebda2e492cc83cbb07a66408c82a3f62e5ba5a4ad17fb113e4a6f48be3afefaa3db1fef12ebbc916c75a51d47202b574e4b9348c597363d
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 17 468 (reduceState modulus Block13.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(479,[3833]),(487,[1949]),(491,[983]),(499,[1997]),(503,[3019]),(509,[1019]),(521,[16673]),(523,[5231]),(541,[9739]),(547,[5471]),(557,[3343]),(563,[7883]),(569,[6829]),(571,[5711]),(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131]),(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 469 rs part0 = true := rfl
noncomputable def part1 : Book := [(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 469 rs part1 = true := rfl
noncomputable def part2 : Book := [(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349,17393]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 469 rs part2 = true := rfl
noncomputable def part3 : Book := [(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 469 rs part3 = true := rfl
noncomputable def book : Book := ((part0 ++ part1) ++ (part2 ++ part3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 469 rs book = true := (checked_append_true (a := (part0 ++ part1)) (b := (part2 ++ part3)) (checked_append_true (a := part0) (b := part1) cells0 cells1) (checked_append_true (a := part2) (b := part3) cells2 cells3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 485 modulus last :=
  certifyBlock (by decide) Block13.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block14
namespace OeisA113258.Block15
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x5e35e50853c3fe11f28cbd05b71cf4a40fadb0c0ec4a825d6495dea1fc414b87099acae3ad114358012e731421291a92c57241715c6ab8639cc6aee4d9ff7aff2c9d97a720e2f3646a675006e275e1551a6591033bf6b93bdcd7f2e25764efece70b8a21aa48db888baece38ea5521b5ee93ca3e8c3dedb758661b4e931dcc9df4e308d505018f87fe730d8a8b5e342514a5dbbf0d06840652770edaa62edbf61c1eef038ea18f6781479f2e35b490b979977ce811208a097ae8fbfade17bf0f8aeee32acf5197b1016d3514e048233eb768f8af22abe5e5da0cdf2cb24c2627f57236a50085fc6676c9ac28e83182577cecaff017eead4c59f4926fa1db3e46c3657a0d85b5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 16 485 (reduceState modulus Block14.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(487,[1949]),(491,[983]),(499,[1997]),(503,[3019]),(509,[1019]),(521,[16673]),(523,[5231]),(541,[9739]),(547,[5471]),(557,[3343,4457]),(563,[7883]),(569,[6829]),(571,[5711]),(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643,18211]),(613,[6131]),(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 486 rs part0 = true := rfl
noncomputable def part1 : Book := [(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 486 rs part1 = true := rfl
noncomputable def part2 : Book := [(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613,18919]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 486 rs part2 = true := rfl
noncomputable def part3 : Book := [(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 486 rs part3 = true := rfl
noncomputable def book : Book := ((part0 ++ part1) ++ (part2 ++ part3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 486 rs book = true := (checked_append_true (a := (part0 ++ part1)) (b := (part2 ++ part3)) (checked_append_true (a := part0) (b := part1) cells0 cells1) (checked_append_true (a := part2) (b := part3) cells2 cells3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 501 modulus last :=
  certifyBlock (by decide) Block14.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block15
namespace OeisA113258.Block16
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x4bb9ae3f7c17db1a96a9c3a0381d4692867c51dee6fefba1ae5dd95a9b2e85181d8c6df7b82952c06459989b8d07f357eb40c3c585ec0ce1ec9121d688edea8bbefaba4298e998302b9dc526f2b36bd7c220311c2e093d682bc94dbf4ea111b6929e146c4a1f6f5df53ecc12ed025c85cc2f12f9f5523fcdf33094d2e422d02608a7a35f08339b45c1a002b5089d5a0e62ac516eb19ff14ccf32e206205a0c3bf504424552cdf47c53565e14782bd8fe6e2e43778e9f4469848185a881b8f9c35360ca0302a86798f2a3331c448fd1df85b775a70b8451812955658390d148fae7c3b9deb7ed6c5ba80ac5e8c012392f9fa62b293cf4b70e82d81f8427
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 15 501 (reduceState modulus Block15.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(503,[3019]),(509,[1019]),(521,[16673]),(523,[5231]),(541,[9739]),(547,[5471]),(557,[3343]),(563,[7883]),(569,[6829]),(571,[5711]),(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131]),(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 502 rs part0 = true := rfl
noncomputable def part1 : Book := [(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 502 rs part1 = true := rfl
noncomputable def part2 : Book := [(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 502 rs part2 = true := rfl
noncomputable def part3 : Book := [(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911,15493]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 502 rs part3 = true := rfl
noncomputable def book : Book := ((part0 ++ part1) ++ (part2 ++ part3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 502 rs book = true := (checked_append_true (a := (part0 ++ part1)) (b := (part2 ++ part3)) (checked_append_true (a := part0) (b := part1) cells0 cells1) (checked_append_true (a := part2) (b := part3) cells2 cells3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 516 modulus last :=
  certifyBlock (by decide) Block15.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block16
namespace OeisA113258.Block17
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x6d2e6744f09bcff9fc9fb28df4e657d6bc52be6da41848f0c053f3239ea91490cda624a049661a03afee1259aae184c5eaf64a60667afe74323d3e69527f024d5715cd531c45b5052bff837e613e9920fee7fc636772f61467dd6e568e37826cfacc093dc59046bc5f0ae54bc1fd38b769ce544cbb113a7aebfbb94939fa3033ea1342a204356138e2f1686a073258d7eebc14dc4d8d4fc5b98c1f7595bca6eb567dda6878a6efcf46d4ccadccd1e50b7d8ea06b9a34f7a0cc0e8995dafbb5d064747ca189c68991991818e95e510718d4f5d3a4125be513f3590fecb67ecf90763bb7204105836149168a12303b7a7263e0327c14476b3a3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 15 516 (reduceState modulus Block16.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(521,[16673]),(523,[5231]),(541,[9739]),(547,[5471]),(557,[3343]),(563,[7883]),(569,[6829]),(571,[5711]),(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131]),(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283,3847]),(643,[7717]),(647,[9059]),(653,[1307,3919]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909,4363]),(733,[7331]),(739,[2957]),(743,[1487,19319]),(751,[4507])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 517 rs part0 = true := rfl
noncomputable def part1 : Book := [(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 517 rs part1 = true := rfl
noncomputable def part2 : Book := [(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691,12829]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907,9209]),(1153,[25367]),(1163,[37217,48847]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 517 rs part2 = true := rfl
noncomputable def part3 : Book := [(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 517 rs part3 = true := rfl
noncomputable def book : Book := ((part0 ++ part1) ++ (part2 ++ part3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 517 rs book = true := (checked_append_true (a := (part0 ++ part1)) (b := (part2 ++ part3)) (checked_append_true (a := part0) (b := part1) cells0 cells1) (checked_append_true (a := part2) (b := part3) cells2 cells3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 531 modulus last :=
  certifyBlock (by decide) Block16.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block17
namespace OeisA113258.Block18
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0xa91ee22f856ecb1f4017d3958c04ad2403b17156af201717996b93578113e80ea6f8c0ba87ab980b974b61db24877305bfb077b0efcbfda2b3082e46ab22448e982767207220a0b93875f68289e9f653a1b0ff2849d7af1d23e152337839ca7cc71961e17e422a0fd36aabb5d533cd690bd5d2931b5d1d394673721a8e4432a90a94ebc9fd7932c8e3d174809f9bc418b8ebb75ee772b4630fd18c4d9f733b14efcedcd77155c742d991ebd675c83c481adfc03fa9a37f73000fe00dd47d3b600df29b0e07a1cf179082db0972ae5481f65fec5bd6ff1115fa4586655c2f3a6a1ff173a1ed12ac2d09e8da5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 15 531 (reduceState modulus Block17.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(541,[9739]),(547,[5471]),(557,[3343]),(563,[7883]),(569,[6829]),(571,[5711]),(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131]),(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 532 rs part0 = true := rfl
noncomputable def part1 : Book := [(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291,9949]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 532 rs part1 = true := rfl
noncomputable def part2 : Book := [(1021,[10211]),(1031,[2063]),(1033,[4133,6199]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493,13477]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447,17123]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 532 rs part2 = true := rfl
noncomputable def part3 : Book := [(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 532 rs part3 = true := rfl
noncomputable def book : Book := ((part0 ++ part1) ++ (part2 ++ part3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 532 rs book = true := (checked_append_true (a := (part0 ++ part1)) (b := (part2 ++ part3)) (checked_append_true (a := part0) (b := part1) cells0 cells1) (checked_append_true (a := part2) (b := part3) cells2 cells3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 546 modulus last :=
  certifyBlock (by decide) Block17.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block18
namespace OeisA113258.Block19
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x159e1fb76b943b0a0730a7edc99c6d993bc1ef17255d121a4a08dfc6b69f3fa0c882312cb97b9e750183cd26f4543c4cd0bbbdf0e508c82d02b3296cfd99fe8d47944c94e481c9921b227233f5d4e6e71e8609c3c1e72e781d6e03880bcedab8f0e9e563cf344c36d09735104554057a4af3a370e92e9148b3fdb9e184ac5c4c354d387de2a700b499c763ea2ecfb84cfe60cd4dac4cf4fd1dcab8bfb24bc693befcc09798e6ec1b60a29a6a0fd97abe8877251a9874c4e31c477ff334a3204f07bb4a91e66ae6459baa19ef124cdbac8e6442bf1b3a19efea03c729ece811cbcf5e78f04e228c4a3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 14 546 (reduceState modulus Block18.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(547,[5471]),(557,[3343]),(563,[7883]),(569,[6829,10243]),(571,[5711]),(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131]),(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059,12941]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367,4099]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 547 rs part0 = true := rfl
noncomputable def part1 : Book := [(773,[4639]),(787,[4723]),(797,[4783,11159]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 547 rs part1 = true := rfl
noncomputable def part2 : Book := [(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 547 rs part2 = true := rfl
noncomputable def part3 : Book := [(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 547 rs part3 = true := rfl
noncomputable def book : Book := ((part0 ++ part1) ++ (part2 ++ part3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 547 rs book = true := (checked_append_true (a := (part0 ++ part1)) (b := (part2 ++ part3)) (checked_append_true (a := part0) (b := part1) cells0 cells1) (checked_append_true (a := part2) (b := part3) cells2 cells3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 560 modulus last :=
  certifyBlock (by decide) Block18.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block19
namespace OeisA113258.Block20
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0xebabee9c3e04836f8ee898714c64520307203dc45b9ffe6cb0e8c7168b60d6dc1c792cff377271ec61f9707721794dfef1354b61c7cabb9f2d81ce0394ff9a406152b38580c6aed871ef9af6d6b343c0d5e9868f81098499b95902744156420f24b7d8cf9df7eb143cb1ca9500d509dfe8673acc62fdb7abdb5e5d234c57bf23f8c0f2d02bf6a58c0848405581f0de12e5b17daf7665546267ce8f506465f9851af456cf57f8caf67a6953e68f7386a3577a2201e4434fc28186ed72692e548cfdf448a11d79edb35a058719dc29a93a0418ef5c3e047c57e542f312fb5d1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 14 560 (reduceState modulus Block19.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(563,[7883]),(569,[6829]),(571,[5711]),(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131]),(617,[4937,23447]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417,9479]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 561 rs part0 = true := rfl
noncomputable def part1 : Book := [(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 561 rs part1 = true := rfl
noncomputable def part2 : Book := [(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 561 rs part2 = true := rfl
noncomputable def part3 : Book := [(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells3 : checked 561 rs part3 = true := rfl
noncomputable def book : Book := ((part0 ++ part1) ++ (part2 ++ part3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 561 rs book = true := (checked_append_true (a := (part0 ++ part1)) (b := (part2 ++ part3)) (checked_append_true (a := part0) (b := part1) cells0 cells1) (checked_append_true (a := part2) (b := part3) cells2 cells3))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 574 modulus last :=
  certifyBlock (by decide) Block19.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block20
namespace OeisA113258.Block21
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x3f9f92718a773cd4825120584180feb02125f7bb42c05012564dc7c8bdcf67646cd9da680e3bc958d98af608c786414c76de006700f6a053273f31c46eedb8523f0a2ac451d5a8b5403b3d57be9a0a74e1f63d450c38cbc4dfc9b3e81314eb80c99a7cb48f205f638e6021a0d05fd7e3d02c7c3cfff7db0378a100bd764347a20d50bfd57fb6e680b8c5a79487c53dbb246a43f484a0212b5688b29128e6762fb7109f7e56a91bd666ca8f0a9d17ee6a7df14cd44320dd3579ee4d2ee59a6e9ced199f29379944e8c4b994baad99595743b43c8c74831
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 13 574 (reduceState modulus Block20.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(577,[2309]),(587,[8219]),(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131]),(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693,24229]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 575 rs part0 = true := rfl
noncomputable def part1 : Book := [(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 575 rs part1 = true := rfl
noncomputable def part2 : Book := [(1061,[6367,21221]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 575 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 575 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 587 modulus last :=
  certifyBlock (by decide) Block20.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block21
namespace OeisA113258.Block22
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x1d5d791501cffa85d71e1c137cb130e8516d5b48e31efc50a550430fa84adab6c0ee246c0f1ee1193858650e1050918f8e61311bb56bb1f59df8d3c97f30894ed4601ae4b265772ca02de0061097e204b0590a43674a172b3e73bf1f25cfea22058f3927e66895ea2e412bb5f805cd1d6299db94c1a2ca24f598bf2fc1e05e6c1df2df637739d39c2b6b4828082464f6a976db55cbcd45c2eda52c603007852076ccdc2012332e0c17bc6279759e958bb92125bb57a049f984f991a44e44f008062143c604ccf6b765d63f1e1e447d1f
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 13 587 (reduceState modulus Block21.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(593,[1187]),(599,[4793]),(601,[3607]),(607,[3643]),(613,[6131]),(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 588 rs part0 = true := rfl
noncomputable def part1 : Book := [(827,[11579]),(829,[8291,9949]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 588 rs part1 = true := rfl
noncomputable def part2 : Book := [(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207,6619]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 588 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 588 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 600 modulus last :=
  certifyBlock (by decide) Block21.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block22
namespace OeisA113258.Block23
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x160fd4c8f89b2cb5d78dce8ced9126575eda437f40d8fd36daf04019711ce7abef1be31e6cc7d8736e4db7c3172fca6246fec1af35fcf0bb266c57342526aa022c41e3b2f4c7fb4c0cb29b13f7f1c3b8ede09c0ec57b19ac5cfd62ec8cb07c7c57f34c3e75b4aadf4f8c8dbe4b0e3e00d66663b3e8ec0314fa05d1bc7afdd5f33ee3b23f66b7e65727ca9a83b69b877801813e00a0d96dc7e748b8868c9882df1b09e4a1d6a7f1ae9f975cf2a0c9bd08515040103bde51acad8add60f8842d5cd4fba2083183787a21b3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 13 600 (reduceState modulus Block22.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(601,[3607]),(607,[3643]),(613,[6131]),(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 601 rs part0 = true := rfl
noncomputable def part1 : Book := [(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907,11437]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 601 rs part1 = true := rfl
noncomputable def part2 : Book := [(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 601 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 601 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 613 modulus last :=
  certifyBlock (by decide) Block22.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block23
namespace OeisA113258.Block24
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x12d189153405017bedabcf74067af5f356c19d90f141954717e4b07478eebcf3887d6f4ddea71c8b2d5d144e93949ec4086fc41f3d079013753f8de9fe3a4686a0a44f920028520c74276bd6bde007dbb40f23a5c5982eba0a4092e4f7ab0f286380f9697ee985eec2642ef6208dc2e1d5dd8c6fd33b019b935681d14e725b2e8a264a0d4f404b409eb2c992c5a468d8439169529034981cb7f1a3b7101fefbd1d8b352096690c568219735f0d53ed27fb29b4bc0ae01d0b61936663a39528389b6f6fafbc5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 13 613 (reduceState modulus Block23.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(617,[4937]),(619,[2477]),(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 614 rs part0 = true := rfl
noncomputable def part1 : Book := [(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 614 rs part1 = true := rfl
noncomputable def part2 : Book := [(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 614 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 614 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 626 modulus last :=
  certifyBlock (by decide) Block23.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block24
namespace OeisA113258.Block25
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x19d14da6f2de2c20bd2e9f5883ad3ee20ab5e641f8427c06bc210e162112c05caf1b893ac8e2744dbb94ddaa3606a0d90ccfe2945dc3ccf7aae778e19246227762e281e0946330db476724749625f6cc855773c2d232bec50f53eefd9c8cc8ff558f38fd15a74b5dd2fbc829273954c6608f19f1f7bec28838e37a75cc3a10100cb20fb6c5ea6bf3fa8c701a59036375f24f0bdf45f32332dc05db0f68d9ad2f41c93876687567e5117a6be87b4228dd07903c95f10f7e45e030765935a311d3b18b1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 12 626 (reduceState modulus Block24.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(631,[6311]),(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 627 rs part0 = true := rfl
noncomputable def part1 : Book := [(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 627 rs part1 = true := rfl
noncomputable def part2 : Book := [(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 627 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 627 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 638 modulus last :=
  certifyBlock (by decide) Block24.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block25
namespace OeisA113258.Block26
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x10c19b41a3d5703e23159e77063d6944dd4ac6869271537519462bc8c121f3fc102218e4a44a722ea333a1d6080c6a2ddeb25388548b92c7c3e7281f3315f390c7d338d4ee9b28eacdc25a975c37a16fafbe17c7181a1ec2aa56aed33fc234006111625c4c32a71e5979444ae64e57642777722700716c72dc074999144ebc2d4d3d40454c689ac3197718b06fa4172d5b444caa0f4cf54c5f426411f3a7092a64dd9f83a6e4f6b9428d31781927bc1692a3ca063580b49b32de590fc0cf1596e7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 12 638 (reduceState modulus Block25.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(641,[1283]),(643,[7717]),(647,[9059]),(653,[1307]),(659,[1319,5273]),(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 639 rs part0 = true := rfl
noncomputable def part1 : Book := [(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827,19421]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 639 rs part1 = true := rfl
noncomputable def part2 : Book := [(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 639 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 639 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 650 modulus last :=
  certifyBlock (by decide) Block25.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block26
namespace OeisA113258.Block27
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x21a6f15b79b18b52cbcf0ca20672c7c7862e1b5adb4b35891fe8b24075470efcf605373815503cf4ccff70624b22753d2eb375305cfa5cf640b6e4618c67064558c99ef208535deda8407b437e0799c16291cdfa7706ad0f79fc56654e1ca73567d9ea68e1c9c3feeb95f14a30260ca5245a177f0046326175414b231202d76a89d11afb529eb3d4a68a6efd8ac9b00dc770298908f5923261d6323600cf9873302e72769becd699008a3fafbc2e0444bc52c592f3a8c12ad7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 12 650 (reduceState modulus Block26.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(653,[1307]),(659,[1319]),(661,[3967]),(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 651 rs part0 = true := rfl
noncomputable def part1 : Book := [(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 651 rs part1 = true := rfl
noncomputable def part2 : Book := [(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 651 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 651 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 662 modulus last :=
  certifyBlock (by decide) Block26.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block27
namespace OeisA113258.Block28
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x1522675c9dec0a16e2df5659502d62a97e08d505aadc757f6bb45578602dcd6e93216d1ceacd3da77ad0933d0fd4b8a61d5aa07824540d9dd623271bfdf3cd0b9d5566c721c266af8c6882d1c2333474ad264c321dfaf12380958e6c6d2625fe4f4ee28578d50825fdfc3744a3774e0f704651db69c7ef0cc9a113769c8579e80228804ccde1c0301eb69881c67b8285f39f4aaf3aadca313801309b0107e0a04e04e8f3314dcce94dbc74d71be8934cfd8adaf6fd
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 12 662 (reduceState modulus Block27.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(673,[2693]),(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 663 rs part0 = true := rfl
noncomputable def part1 : Book := [(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133,6199]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359,32911]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217,48847]),(1171,[7027])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 663 rs part1 = true := rfl
noncomputable def part2 : Book := [(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 663 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 663 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 674 modulus last :=
  certifyBlock (by decide) Block27.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block28
namespace OeisA113258.Block29
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x20251e1d443aff7875ae91f9711b7d0fdd11e6bf53eb062cf03ede353c417b618d2ca9618081a64e7d63a4b945fe3ec6da3a8f7eeeb911f4275fc4d91b97213ed1d512944e5841af458a54b5c52d15e451faf06c2af00956395ade846745e7d82a4baf0a51b001bf27ff916051521f14ea44bd86613323275148a5bb27ac4f54245d296d7f7cd10a5aa1f09c51b9dc1a29d29fcb1d4407845f72d66db4f2ca4acd2be05d129e72e3a885c7abc05c224c9ad3019
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 11 674 (reduceState modulus Block28.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(677,[5417]),(683,[1367]),(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 675 rs part0 = true := rfl
noncomputable def part1 : Book := [(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 675 rs part1 = true := rfl
noncomputable def part2 : Book := [(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 675 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 675 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 685 modulus last :=
  certifyBlock (by decide) Block28.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block29
namespace OeisA113258.Block30
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x48d449e026421c61940077a1c5cfeb3541f00910a00e735a2a2932965a24a25465123ff76c08e3cb937f946c873e521c9e5e778172cae7724323fa88f558acb31a818675b5ad4afe8fe118f901c4453199f7eceef8286d0ac8e76e40de3f51c7620f28083e19026a1b286289ac0a70573080ed5117ff57c50179c01189355807a3b9a714b020fffcb458a60367b500e9c6b48fa15d07dd7738d567eae8a1518f1174b3f530ac6dce1559c92728d513a77
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 11 685 (reduceState modulus Block29.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(691,[6911]),(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 686 rs part0 = true := rfl
noncomputable def part1 : Book := [(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 686 rs part1 = true := rfl
noncomputable def part2 : Book := [(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189,20753])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 686 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 686 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 696 modulus last :=
  certifyBlock (by decide) Block29.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block30
namespace OeisA113258.Block31
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x884f0eab99c75b87f0d3dbface0ca7a94f07636c974135a84b75659c8c91d948d3fdc11fe40ed21cca6feff4f2706c256b8de34a184610126437d2e8a9614a302d497ac685133dba3fee450fae429c8a3b3463e868e17e61f73ea99b6790bd77dcb68e2d6cf86c2a6e27d639040f8bda7daf8e02dd40d8b3071990e4a5ca601040251583a70ca6d3f62031a2470d55c264138fd7d138cce70a64f580076a20dc5ed326f5fef65eb38bf9306ff9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 11 696 (reduceState modulus Block30.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(701,[12619]),(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433,11149]),(937,[5623]),(941,[5647]),(947,[5683])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 697 rs part0 = true := rfl
noncomputable def part1 : Book := [(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 697 rs part1 = true := rfl
noncomputable def part2 : Book := [(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 697 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 697 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 707 modulus last :=
  certifyBlock (by decide) Block30.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block31
namespace OeisA113258.Block32
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x10413de8e3f4d5f390975c067e6d1248a650820832f0557cd2111391bc74f01eba72e5bd51b44d58913c829f972657309da113bd27f81c773e166435cc80f7a1f3f4b9b9c9dbe402e553c69869f647b4935df7ceacff7aea93d67bb367d91939440543c9de4af2b77ef7d38555cea894de6e2f60ce8ad720a5bd0ec16840e23c0e4213c7c11f5d4414586553abd29680221f153fa0786af320725e23d8d3a8902394a7045b0a456bca37
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 11 707 (reduceState modulus Block31.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(709,[2837]),(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 708 rs part0 = true := rfl
noncomputable def part1 : Book := [(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 708 rs part1 = true := rfl
noncomputable def part2 : Book := [(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 708 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 708 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 718 modulus last :=
  certifyBlock (by decide) Block31.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block32
namespace OeisA113258.Block33
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x1777e97db8a684f01f2c489624e3dbf44e0ea13541836a30a6217f6c5a88e39185064237dda4efce496ebc0cc37cbf36c28e249eae1c7ea466460c08bbb259867964f05aa7181d9d2196d26350e313e0b50095dff300c8907d5fe5947b95a9e070a4f91b832cc5bfed2f4db9328651df252ac4b829ee438013d5da4a0a4aba67da1cce810b46a3b61eff943040b6c3d02fd1eb3e5b1884087c168c6dde0068c3d529ffd8166fbe31b
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 11 718 (reduceState modulus Block32.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(719,[1439]),(727,[2909]),(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907,11437]),(967,[15473])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 719 rs part0 = true := rfl
noncomputable def part1 : Book := [(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 719 rs part1 = true := rfl
noncomputable def part2 : Book := [(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 719 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 719 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 729 modulus last :=
  certifyBlock (by decide) Block32.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block33
namespace OeisA113258.Block34
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x21af904eb55ccedd5e7886efcd887a02f9ed804e798d1728a5da2be4a0e475544a7e77b9fbbcd4da16e2440670ec8d2f8a71b063574452922321574824576028d6bcfdfb8defe48e729f5798e149c5780db29323edb23de2f04128016a65f84f24d508cdf57da87786a706a5e9450c9dd58a33667f75277a425f1af21c6cf1e8dc8817fc01c4017a3bd0d0c9ba1c3ec2b29ec764e9f9f40d4090f1b31fcefc70bd16610d
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 10 729 (reduceState modulus Block33.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(733,[7331]),(739,[2957]),(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 730 rs part0 = true := rfl
noncomputable def part1 : Book := [(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 730 rs part1 = true := rfl
noncomputable def part2 : Book := [(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 730 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 730 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 739 modulus last :=
  certifyBlock (by decide) Block33.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block34
namespace OeisA113258.Block35
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x1a12174f9ae5b87603ba1c005e3d84ca0bf928909d9bc086b966702191a8e2e47a1c405a2e84761a33d469136fdf5a5aca7651d629e5f6cc6818c5f99c3a93b6591e80171936a4395f19bf6c759ac3c2fa5a47ea60984fe633470598bae562fea78068f203ab342173c948e41fefb8ecf65048cb1590c34bc68e73ea1083470304a6e7644dd21c4c0a17326d24d85ceac73800f1c3afd6d5a57ccc707a7cc0f58b
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 10 739 (reduceState modulus Block34.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(743,[1487]),(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111,9733]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 740 rs part0 = true := rfl
noncomputable def part1 : Book := [(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133,6199]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 740 rs part1 = true := rfl
noncomputable def part2 : Book := [(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 740 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 740 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 749 modulus last :=
  certifyBlock (by decide) Block34.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block35
namespace OeisA113258.Block36
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x1e38acb3596d46cca2b3fb2d043c8a327aed17765e7964ac2b9c689beb4e9f211c77c2f708eca091aa94d12dce720a2230132bd58ebb3f4f594ae7d495cb376558004711eb2ef52819789755283e08121393daa5b215ad6e18db3f4bcfb77b5087a54505c10352ac1373d8296e5fb4238ff309e224533ea14777469930aad8f16e0a9a7b786bd5987560a8f6cad7bdaff13a022a6b04d083dcd6e1256b81
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 10 749 (reduceState modulus Block35.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(751,[4507]),(757,[12113]),(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 750 rs part0 = true := rfl
noncomputable def part1 : Book := [(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359,32911]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 750 rs part1 = true := rfl
noncomputable def part2 : Book := [(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 750 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 750 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 759 modulus last :=
  certifyBlock (by decide) Block35.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block36
namespace OeisA113258.Block37
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x127e7f1def5bea274824f6629e567a65eff7e6210478515c0442934cb7f4fffb6f904b0133c907afb527a55fa1c82a00f29e63a0649fbad393404b2d78363642d1b51d53d7055f29078a14e56acaf6bc44177bd571a1d03cb4750f700cea01ba0390e42cd4c95eb57f56d0bfd71e20b3b25dec5b457ab858c27a6dc0c0138a6ddbd788f544139bea6f3190f663e6ebb0e58398d8482e25ba2d
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 10 759 (reduceState modulus Block36.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(761,[1523]),(769,[7691]),(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 760 rs part0 = true := rfl
noncomputable def part1 : Book := [(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373,17489]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491,22483]),(1259,[17627]),(1277,[25541])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 760 rs part1 = true := rfl
noncomputable def part2 : Book := [(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 760 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 760 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 769 modulus last :=
  certifyBlock (by decide) Block36.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block37
namespace OeisA113258.Block38
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x4d36d0271d3060c3bc10bf3644215dd3e992f58508d70f45885ea175a1c9b450a11b461fb694b289b69c2f13d72fc1d56bc4b3424299bf73ab1b5bca69dc4e79dd1ae4aaeaea3b5822e23661ce00447552f1b0992c4fa956813185215fd3aa48e7138dc9b98dccf101f62aedd164d91d5b0b9e17be01534c4832599a6e2d77042fcc4ea24125067bc4f326448be437c9b37b206f
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 10 769 (reduceState modulus Block37.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(773,[4639]),(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 770 rs part0 = true := rfl
noncomputable def part1 : Book := [(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 770 rs part1 = true := rfl
noncomputable def part2 : Book := [(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 770 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 770 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 779 modulus last :=
  certifyBlock (by decide) Block37.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block38
namespace OeisA113258.Block39
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x442d160b06f45bd6ede6f19035f99754306826ddfb556c3c4a45fa8e61b5ae7eb4fcfc697adb41898ac67ea9466a1210600972a0276149bd27a9589b529921960940db8f927073165c0e18110b88d138d998f9141309943f5b0f31814bd5fc2af53235c8765cdd5904e0a348681825a0675857ef70157a62cee4e1e7c48ec9376783557cff1446668cacf81fd3c1b949847b1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 10 779 (reduceState modulus Block38.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(787,[4723]),(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473,23209]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 780 rs part0 = true := rfl
noncomputable def part1 : Book := [(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 780 rs part1 = true := rfl
noncomputable def part2 : Book := [(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 780 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 780 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 789 modulus last :=
  certifyBlock (by decide) Block38.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block39
namespace OeisA113258.Block40
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0xa6f451128996b9658d21717ca025d50765bcf19ec544ae8f73073f38d4a7f57001065456049fe5e689759923c93ed74f2696390dc852c815f277f97db2e65675b57fd012a7c45cb556a85b095928ce3d490dcab193e811b609b7e6b551940ba93e00fd3ef3c8cb83a34b67f5074e8b998b3d47f7e985011d6c03a16601af4c5e35e7895c838bc35f924fcc9c570fd3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 10 789 (reduceState modulus Block39.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(797,[4783]),(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 790 rs part0 = true := rfl
noncomputable def part1 : Book := [(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 790 rs part1 = true := rfl
noncomputable def part2 : Book := [(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells2 : checked 790 rs part2 = true := rfl
noncomputable def book : Book := (part0 ++ (part1 ++ part2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 790 rs book = true := (checked_append_true (a := part0) (b := (part1 ++ part2)) cells0 (checked_append_true (a := part1) (b := part2) cells1 cells2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 799 modulus last :=
  certifyBlock (by decide) Block39.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block40
namespace OeisA113258.Block41
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x8ef95de33c9c43c74f45b1189147d8342686b8f893f3f3d934be89f541e9ce6260e5c9cd2b3150777ea7658bac127d66bb82f2813b6b728f1330186613ee850603515ae4089408872ae6588ee21c335f762bd147a06f63099cf49f3f972984eda28d65f525c357f345c74ad781f2df46a2611dffd1584352bba9d533a7bd07dca4205bf0cfb54b1757fdafeae1d
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 10 799 (reduceState modulus Block40.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(809,[1619]),(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 800 rs part0 = true := rfl
noncomputable def part1 : Book := [(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027,25763]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 800 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 800 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 809 modulus last :=
  certifyBlock (by decide) Block40.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block41
namespace OeisA113258.Block42
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x169b7e0175e5cb26f271cca01c0832a19ff1e21c3cb6263ddbbfe3371138bc39eebf9c59ff8e5c19da276f6784ad1031223c3c7b87bc3c7db815850b3d2eba6e0e1f85c112977c8696acb968579dfef3bd4ca913b4cd76480ae745ede8c81b580432d1face276d4130822e4e08d8c3f5081fcd15a249ba00bf974bee3c5c81a37113d2738ebd00a59bbfc0bcf
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 9 809 (reduceState modulus Block41.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(811,[8111]),(821,[6569]),(823,[8231]),(827,[11579,14887]),(829,[8291]),(839,[10069,25171]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 810 rs part0 = true := rfl
noncomputable def part1 : Book := [(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 810 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 810 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 818 modulus last :=
  certifyBlock (by decide) Block41.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block42
namespace OeisA113258.Block43
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x82dab775ce56f33671004d54e0229ac930fd72e023d66e4fb32e85282837af70392273ea5de626eba5f51f1aaaf62c232335d137b738085590c0ab4575a669fd4eb060285bc89f9510ec0bdbc3c91a1689ea6e8639a9cc1b2ae32b0e270ca720e2127194a5322b7b8991c8088dbac6b886d6eef40d6c9d6c4caa6235cfaac7d577b6ecd0505f8d
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 9 818 (reduceState modulus Block42.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(821,[6569]),(823,[8231]),(827,[11579]),(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179,10357]),(877,[14033]),(881,[15859,22907]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839,21803]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 819 rs part0 = true := rfl
noncomputable def part1 : Book := [(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 819 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 819 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 827 modulus last :=
  certifyBlock (by decide) Block42.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block43
namespace OeisA113258.Block44
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x30d9145be3d1c6675b1d6a4177ffbca6e2327c9285f44dd8a89689555db246d05610f99c9c77a6e8a072c3050cb2a8fd60a68c4b5edbd3a18e6fe24b57d96ac63794c381406e1c86bf69bb8d9a98c17d9e85d280ac59cb50e0bb9c5a1817dfef1eb05e76788bb97d298b395651c54e13ac000ed9b5b4cf107ca005e31d
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 9 827 (reduceState modulus Block43.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(829,[8291]),(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 828 rs part0 = true := rfl
noncomputable def part1 : Book := [(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 828 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 828 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 836 modulus last :=
  certifyBlock (by decide) Block43.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block44
namespace OeisA113258.Block45
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x1821e15cbb0647c5a2211ea9de779c47f282f916a4ebed07068efa543a44de5849e3e3c5a2cc2bccce9a34704af1796f00e876f5a76fe79c3bdeb81c150b9980371fd73eb6335f547272caa3e24851042a5fd0d24b93169a825a861e1edc75eac112dcdfe79172c387d9544e5686f5824ae848cba4d4763a796867f
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 9 836 (reduceState modulus Block44.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(839,[10069]),(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 837 rs part0 = true := rfl
noncomputable def part1 : Book := [(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 837 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 837 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 845 modulus last :=
  certifyBlock (by decide) Block44.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block45
namespace OeisA113258.Block46
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x9d11e879b54246abc58d4d1c011bd8d8463f55b8fcb7e5889ed3a47a3283e954208a67d31ed82794c64419207dbc8f447dd005d6bf3dbf1253eb5ba85cd7214946daaed662949d70b7f1040a204c189d7d431dc798f4da9d07f8a13ee5987812f17422e14d334cffc470485dee884361eedefe63a27306cce83
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 9 845 (reduceState modulus Block45.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(853,[3413]),(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 846 rs part0 = true := rfl
noncomputable def part1 : Book := [(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 846 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 846 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 854 modulus last :=
  certifyBlock (by decide) Block45.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block46
namespace OeisA113258.Block47
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0xbc809a2f811928a2578559770ab4e255fcd8b915cfceabcea3c2109fda36f2f7d3a4fa506705f60be16a8d9dbad3be03bd77f6ce443f00760140dc69253cafdc54221f753fa0ba8bed072506ad52d9359e0e1749b2fd7fdfa25b36f9a68e53a59f7c268f536c724f60e9297827a481c5906266ed55ac2c77
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 9 854 (reduceState modulus Block46.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(857,[6857]),(859,[18899]),(863,[5179]),(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 855 rs part0 = true := rfl
noncomputable def part1 : Book := [(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 855 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 855 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 863 modulus last :=
  certifyBlock (by decide) Block46.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block47
namespace OeisA113258.Block48
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x134d08491c1036fbf21a4108cb8e5aa4b6844519d827cb901e74b5635f1b77c84b298dd27a84bf636bf043b85be5d9db63d5535e5916d16a1629966d964ff6f49c50ba98fdced368da52eeda4d07e7a68e2d999d2a1b4202b13f75a97559653e7928fe04e9da34c98242afbdfa1f93dfcec40df
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 9 863 (reduceState modulus Block47.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 864 rs part0 = true := rfl
noncomputable def part1 : Book := [(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 864 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 864 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 872 modulus last :=
  certifyBlock (by decide) Block47.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block48
namespace OeisA113258.Block49
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x134d08491c1036fbf21a4108cb8e5aa4b6844519d827cb901e74b5635f1b77c84b298dd27a84bf636bf043b85be5d9db63d5535e5916d16a1629966d964ff6f49c50ba98fdced368da52eeda4d07e7a68e2d999d2a1b4202b13f75a97559653e7928fe04e9da34c98242afbdfa1f93dfcec40df
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 9 872 (reduceState modulus Block48.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(877,[14033]),(881,[15859]),(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623,9371]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 873 rs part0 = true := rfl
noncomputable def part1 : Book := [(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207,12011]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 873 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 873 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 881 modulus last :=
  certifyBlock (by decide) Block48.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block49
namespace OeisA113258.Block50
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x3785a9d4fc361cb81995a5886b64c34b61be8a9e5980a7d9562b96abb8685242b7021c12f8bb8c69bdaa50bf0c406e6d40f628f2d2686c9775bb38d5a253203855146498d3668d31a6cf808d549c424a2aad7082e25f21a7ff688365519b74115a709e70e51d0a2888997d8ad
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 9 881 (reduceState modulus Block49.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(883,[3533]),(887,[5323]),(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 882 rs part0 = true := rfl
noncomputable def part1 : Book := [(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 882 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 882 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 890 modulus last :=
  certifyBlock (by decide) Block49.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block50
namespace OeisA113258.Block51
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x31883112bf6cb3b36126045ee1b2cedae235839edfb752bd89739ea5de07528dfaa4a277841dd98d4dcb21055a1f7ff1de00878c5abc23ac103b9709aab357ed34c460d571b626cdaa5840649dd97ff73b9a38f2c8b0bc56d9962a322cc570dfcfd68c8b3a812498803
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 8 890 (reduceState modulus Block50.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 891 rs part0 = true := rfl
noncomputable def part1 : Book := [(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 891 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 891 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 898 modulus last :=
  certifyBlock (by decide) Block50.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block51
namespace OeisA113258.Block52
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x31883112bf6cb3b36126045ee1b2cedae235839edfb752bd89739ea5de07528dfaa4a277841dd98d4dcb21055a1f7ff1de00878c5abc23ac103b9709aab357ed34c460d571b626cdaa5840649dd97ff73b9a38f2c8b0bc56d9962a322cc570dfcfd68c8b3a812498803
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 8 898 (reduceState modulus Block51.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373,17489]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 899 rs part0 = true := rfl
noncomputable def part1 : Book := [(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 899 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 899 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 906 modulus last :=
  certifyBlock (by decide) Block51.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block52
namespace OeisA113258.Block53
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x31883112bf6cb3b36126045ee1b2cedae235839edfb752bd89739ea5de07528dfaa4a277841dd98d4dcb21055a1f7ff1de00878c5abc23ac103b9709aab357ed34c460d571b626cdaa5840649dd97ff73b9a38f2c8b0bc56d9962a322cc570dfcfd68c8b3a812498803
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 8 906 (reduceState modulus Block52.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(907,[5443]),(911,[1823]),(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 907 rs part0 = true := rfl
noncomputable def part1 : Book := [(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 907 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 907 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 914 modulus last :=
  certifyBlock (by decide) Block52.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block53
namespace OeisA113258.Block54
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x53bfcc9358d219ea0c170b419b957aebadd7a34e29796c04ea548a9bf0b37e15109e82dd11c5a83fae6424972132adefd5637850097a7158683a09958768168d2514e51e8327b1b55c753a24d10c8d07a8b6c9092ab5fd922ce3ce18d2cd1fa3fa4cc80c4f69f
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 8 914 (reduceState modulus Block53.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(919,[3677]),(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 915 rs part0 = true := rfl
noncomputable def part1 : Book := [(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 915 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 915 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 922 modulus last :=
  certifyBlock (by decide) Block53.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block54
namespace OeisA113258.Block55
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x5d4ae5f9d78f0bf2f6b388d06dd154c7e013a5d4e02775559c40607a77d5a957b9f42d3dd4ff8c6d1733bfc51ae2bff272793f7ed2a6e3c522b725c258df72074346b046bfe9615ad75d0f2101609f5412571118e6d2aa5fdb1dedddf7902f7fdeea61f12b
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 8 922 (reduceState modulus Block54.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(929,[7433]),(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 923 rs part0 = true := rfl
noncomputable def part1 : Book := [(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 923 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 923 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 930 modulus last :=
  certifyBlock (by decide) Block54.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block55
namespace OeisA113258.Block56
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x3368d11ccf177ae452e838617f6f4136ba17b53d33b645f635ef78271b7f010cc3bcbb143174d0f283beb3090c069cd0aef21e831f63fd88036ccfc0d1e1de55138adde22c8499cd6c08fcbaf2e11adf6c811f2761794a036effb84a195085a17dd5d93
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 8 930 (reduceState modulus Block55.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(937,[5623]),(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039,32609]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 931 rs part0 = true := rfl
noncomputable def part1 : Book := [(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 931 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 931 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 938 modulus last :=
  certifyBlock (by decide) Block55.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block56
namespace OeisA113258.Block57
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x4b4322c71fe83269ff180d17d98b053bb07e692031806a4b0623f8686e7ad31c92cb07affbcf4b143404ebecf6e5883257bfda694060ce8c9f8030feae63cf0a2e4c72b8d7ae8c567810d92478cbb903e01d486ae41f86264fba23a3383b7d65
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 8 938 (reduceState modulus Block56.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(941,[5647]),(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 939 rs part0 = true := rfl
noncomputable def part1 : Book := [(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 939 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 939 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 946 modulus last :=
  certifyBlock (by decide) Block56.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block57
namespace OeisA113258.Block58
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x36973dcf66e2b8a0a9129420b6745764306978e7e2fccf7a8dff299851393857181a7f29498788bd1943cecde15eb9bd3ec97295b17bf042753bd7ebd267acfa31448d6bd3579314c9260400860a39c428e2261c7b3747826116a1c29894b
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 8 946 (reduceState modulus Block57.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(947,[5683]),(953,[1907]),(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133,6199]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373,17489]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 947 rs part0 = true := rfl
noncomputable def part1 : Book := [(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 947 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 947 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 954 modulus last :=
  certifyBlock (by decide) Block57.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block58
namespace OeisA113258.Block59
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0xd13fd6ec9075f574a634e0e4f2c79c7a8c90a7cfdae9c4e6cb859f6bdeaa26ee50673299853e0c00ff2e5c126ffb87b2c87e99d930f59c64de34bd22db1290107d27e090abb75c08343fcc111fbf5424da56175c03012775
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 8 954 (reduceState modulus Block58.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 955 rs part0 = true := rfl
noncomputable def part1 : Book := [(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 955 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 955 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 962 modulus last :=
  certifyBlock (by decide) Block58.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block59
namespace OeisA113258.Block60
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0xd13fd6ec9075f574a634e0e4f2c79c7a8c90a7cfdae9c4e6cb859f6bdeaa26ee50673299853e0c00ff2e5c126ffb87b2c87e99d930f59c64de34bd22db1290107d27e090abb75c08343fcc111fbf5424da56175c03012775
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 8 962 (reduceState modulus Block59.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(967,[15473]),(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 963 rs part0 = true := rfl
noncomputable def part1 : Book := [(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 963 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 963 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 970 modulus last :=
  certifyBlock (by decide) Block59.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block60
namespace OeisA113258.Block61
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x37646f5c49c7b4038c0a9f6ea7ce86e6e1974fc7939312b8283e3dd2ff114377f3885544167fc5c34778f4c0801e95413eda521f412070dfeae08312714931e66b273a8966c0725dff0a4971b692a46548464e9e12d45
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 8 970 (reduceState modulus Block60.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(971,[5827]),(977,[7817]),(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 971 rs part0 = true := rfl
noncomputable def part1 : Book := [(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 971 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 971 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 978 modulus last :=
  certifyBlock (by decide) Block60.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block61
namespace OeisA113258.Block62
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x14670d381402ffedc2b88c812a4b9e34b1cd8ba8c19f819fa4b731edb2f9cd8d586bad4ba8297c04a9872ee0af1fc455054e6ecaecfe7d7cb26aad3d2f70b334957a3dba63d0e0d297389d9f5e80ef5749792df
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 8 978 (reduceState modulus Block61.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(983,[13763]),(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 979 rs part0 = true := rfl
noncomputable def part1 : Book := [(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 979 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 979 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 986 modulus last :=
  certifyBlock (by decide) Block61.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block62
namespace OeisA113258.Block63
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x6126e11b19ede1b6ba20b59040cc2073cdbb94a6c4140b607e9e2d9a626e41894c7f8cbe8c2a1cb1c69557874d9428f0b74c5ec4c68d47d471f5b7e391606de736db8e6e9881076ec087120ca863d5f30b5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 8 986 (reduceState modulus Block62.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(991,[17839]),(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 987 rs part0 = true := rfl
noncomputable def part1 : Book := [(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 987 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 987 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 994 modulus last :=
  certifyBlock (by decide) Block62.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block63
namespace OeisA113258.Block64
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x164e95b36b7be3dd52e00f836159d2188d435da4c33e4701d23fabdf325e74f72f83ad91a7aab9d3c704c569c2f880aeaade7d83b37e9f47f4a007c7fdacf3892b4354de39f2d5349868d5341d4eacdb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 8 994 (reduceState modulus Block63.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(997,[3989]),(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027,25763]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 995 rs part0 = true := rfl
noncomputable def part1 : Book := [(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 995 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 995 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1002 modulus last :=
  certifyBlock (by decide) Block63.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block64
namespace OeisA113258.Block65
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x3a4442f859afd811479fb69be4ae2543b16574291a915fbbbdb0b0de2c8f68b2588f78e9724c503bcb9e76dd82cd6d9137fade37f6c931fc3db35001a0a3cff7cedd1ffc6dd6101cc07eda285
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1002 (reduceState modulus Block64.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1009,[10091]),(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1003 rs part0 = true := rfl
noncomputable def part1 : Book := [(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 1003 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1003 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1009 modulus last :=
  certifyBlock (by decide) Block64.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block65
namespace OeisA113258.Block66
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x17a69a9660d57180e9a63aa59dfefe5b5b42ee2e0fcea1983c8ea6ed11b4ebcf548775c0cf2218b3efb5e85a1d9a099de901e65d4b07f81430b04a488e87a6142aaa95033e6aee5d0109cf
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1009 (reduceState modulus Block65.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1013,[2027]),(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1010 rs part0 = true := rfl
noncomputable def part1 : Book := [(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 1010 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1010 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1016 modulus last :=
  certifyBlock (by decide) Block65.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block66
namespace OeisA113258.Block67
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x2fcaa928ccc4668f0ac8c44e8a28a76e37d8748e149345c7a52ee8fdbd7b3b19ccc879c1397b147da9482e2d7280a4ecbf7a6e1b9e902a9830e0e2e4b56b86692961cabaa6cbb3710ad
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1016 (reduceState modulus Block66.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1019,[2039]),(1021,[10211]),(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217,48847]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1017 rs part0 = true := rfl
noncomputable def part1 : Book := [(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 1017 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1017 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1023 modulus last :=
  certifyBlock (by decide) Block66.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block67
namespace OeisA113258.Block68
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x33ab36a2ca7c0b39964d4a81c7e566ee942fb494df7fd1df2dc793e32ab9a23341d779947baefa89b6aec10ec28c0ed8c4d8b337aaf1575bfd4c7f77cde209e9c77430027
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1023 (reduceState modulus Block67.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159,16703]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1024 rs part0 = true := rfl
noncomputable def part1 : Book := [(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 1024 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1024 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1030 modulus last :=
  certifyBlock (by decide) Block67.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block68
namespace OeisA113258.Block69
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0xcaba618cef7699c00034261939d944c77e64d3c3f931363293096c937bc98849b7ed2450eb6696cf2a24f40aa5212a155122656d1fda97e2e63e5efdbec54852a1f19
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1030 (reduceState modulus Block68.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1031,[2063]),(1033,[4133]),(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1031 rs part0 = true := rfl
noncomputable def part1 : Book := [(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 1031 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1031 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1037 modulus last :=
  certifyBlock (by decide) Block68.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block69
namespace OeisA113258.Block70
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x18ee797ae8863504150ea4264b227e602d1ab7083721aabf56cc14a322dbdf2d4f91fa3f417c5447e2cf2994f68fc62198608da9c6ccb5c78cfa36d531599dcb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1037 (reduceState modulus Block69.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1039,[4157]),(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1038 rs part0 = true := rfl
noncomputable def part1 : Book := [(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells1 : checked 1038 rs part1 = true := rfl
noncomputable def book : Book := (part0 ++ part1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1038 rs book = true := (checked_append_true (a := part0) (b := part1) cells0 cells1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1044 modulus last :=
  certifyBlock (by decide) Block69.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block70
namespace OeisA113258.Block71
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x1890d15cb70c55fc434e0a9dd173f44cc85ecd98622b654d20bf3b900da7cf66986cdb3b6ee5892ce79c264316c8e82c6ef97695ac2c4ce26db7e9aa57ea7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1044 (reduceState modulus Block70.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1049,[2099]),(1051,[12613]),(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1045 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1045 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1051 modulus last :=
  certifyBlock (by decide) Block70.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block71
namespace OeisA113258.Block72
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0xf9145e28ac394a2d7c2b7965aba0cf107c2aba6f93b509adccc69f522623660f66bdbb8eb8f29c226fbe383f87f7fd8454a4f5742fb1cfeb86cc19
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1051 (reduceState modulus Block71.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1052 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1052 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1058 modulus last :=
  certifyBlock (by decide) Block71.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block72
namespace OeisA113258.Block73
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0xf9145e28ac394a2d7c2b7965aba0cf107c2aba6f93b509adccc69f522623660f66bdbb8eb8f29c226fbe383f87f7fd8454a4f5742fb1cfeb86cc19
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1058 (reduceState modulus Block72.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1061,[6367]),(1063,[4253]),(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1059 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1059 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1065 modulus last :=
  certifyBlock (by decide) Block72.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block73
namespace OeisA113258.Block74
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x9a526c91feda5f8608d964f8a6cca22dfec3d3c768c1b4ba2e9d7b8725a0ca3a4548be625181d1f318f15a7ee57f419ba490253cff5041f3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1065 (reduceState modulus Block73.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1069,[10691]),(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1066 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1066 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1072 modulus last :=
  certifyBlock (by decide) Block73.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block74
namespace OeisA113258.Block75
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x3b1ff0209061d70ffc1c681a7e67106c6c3d2360df44ebff352dcd01cde84f33e5c4da3dda689286c10693a541588748eba58ace8d411
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1072 (reduceState modulus Block74.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1073 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1073 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1079 modulus last :=
  certifyBlock (by decide) Block74.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block75
namespace OeisA113258.Block76
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x3b1ff0209061d70ffc1c681a7e67106c6c3d2360df44ebff352dcd01cde84f33e5c4da3dda689286c10693a541588748eba58ace8d411
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1079 (reduceState modulus Block75.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579,10313]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1080 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1080 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1086 modulus last :=
  certifyBlock (by decide) Block75.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block76
namespace OeisA113258.Block77
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x177b85070ce2d1ae20a95af7c7f5e5ce5f77081e5526919c57f1d2475cecef467b475b783594d7c5b7939a7b5f622303aac42b1d89
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1086 (reduceState modulus Block76.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1087,[4349]),(1091,[6547]),(1093,[4373]),(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1087 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1087 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1093 modulus last :=
  certifyBlock (by decide) Block76.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block77
namespace OeisA113258.Block78
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0xcf5d20d4795234081b7f06025642de90fe87c1ca0a09ce9855bb57972f414f59141b0e2ee8d69b21db5bbfa5514464b3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1093 (reduceState modulus Block77.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1097,[15359]),(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1094 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1094 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1100 modulus last :=
  certifyBlock (by decide) Block77.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block78
namespace OeisA113258.Block79
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x374cf4b4346c20be70e805782e56deeea5b807cf9b7868083921d7ebea221e42ece07efd8f1dbf329d78f51f1a74d
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1100 (reduceState modulus Block78.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1103,[2207]),(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1101 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1101 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1107 modulus last :=
  certifyBlock (by decide) Block78.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block79
namespace OeisA113258.Block80
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x66a21418f88c5bdb3c7dc71b2174cc7d1566b639801e72e4ec6908526dfa6b6ea2dc267e146611c420e432cc93
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1107 (reduceState modulus Block79.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1109,[13309]),(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1108 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1108 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1114 modulus last :=
  certifyBlock (by decide) Block79.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block80
namespace OeisA113258.Block81
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x1f9627764487c1a2522197d11b47f939c9eb40b7e342c9aab020a1fb52cce7f458d2b589e1ec70a54ebbfcf
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1114 (reduceState modulus Block80.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1117,[6703]),(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1115 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1115 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1121 modulus last :=
  certifyBlock (by decide) Block80.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block81
namespace OeisA113258.Block82
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x134d341bd082024c0b89a97f82e70b678fd1b6936da7ccc5a4a58739e7d1321e3b16da195d2dfc0a6c61
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1121 (reduceState modulus Block81.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1123,[4493]),(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1122 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1122 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1128 modulus last :=
  certifyBlock (by decide) Block81.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block82
namespace OeisA113258.Block83
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x119899b5dfc204425ce8635df75d501491783ef8ed2b10423973f998c8d99acd372dbb601c6cb2f25
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1128 (reduceState modulus Block82.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1129,[4517]),(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1129 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1129 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1135 modulus last :=
  certifyBlock (by decide) Block82.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block83
namespace OeisA113258.Block84
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0xff4c190b09b13c9b1d189e1ee88deb100247eb3239303eb1ed85c94bef8aba8767fba84612f81
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1135 (reduceState modulus Block83.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1136 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1136 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1142 modulus last :=
  certifyBlock (by decide) Block83.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block84
namespace OeisA113258.Block85
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0xff4c190b09b13c9b1d189e1ee88deb100247eb3239303eb1ed85c94bef8aba8767fba84612f81
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1142 (reduceState modulus Block84.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1143 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1143 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1148 modulus last :=
  certifyBlock (by decide) Block84.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block85
namespace OeisA113258.Block86
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0xff4c190b09b13c9b1d189e1ee88deb100247eb3239303eb1ed85c94bef8aba8767fba84612f81
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1148 (reduceState modulus Block85.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1151,[6907]),(1153,[25367]),(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1149 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1149 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1154 modulus last :=
  certifyBlock (by decide) Block85.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block86
namespace OeisA113258.Block87
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x18722bd8ff00b0aed445987dc2b88346fe97d901049d03350bf526e2662621dea885ac5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1154 (reduceState modulus Block86.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1155 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1155 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1160 modulus last :=
  certifyBlock (by decide) Block86.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block87
namespace OeisA113258.Block88
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x18722bd8ff00b0aed445987dc2b88346fe97d901049d03350bf526e2662621dea885ac5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1160 (reduceState modulus Block87.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1163,[37217]),(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1161 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1161 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1166 modulus last :=
  certifyBlock (by decide) Block87.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block88
namespace OeisA113258.Block89
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x2b0c1cb44b5dcecf64165f5ce9f52b0bcd03d3137dc11544d568ad6963407c5afe5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1166 (reduceState modulus Block88.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1171,[7027]),(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1167 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1167 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1172 modulus last :=
  certifyBlock (by decide) Block88.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block89
namespace OeisA113258.Block90
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x191790340c99a05e12ec1222b4743d6063af0566544db818ad110b34a66ae147
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1172 (reduceState modulus Block89.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1173 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1173 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1178 modulus last :=
  certifyBlock (by decide) Block89.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block90
namespace OeisA113258.Block91
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x191790340c99a05e12ec1222b4743d6063af0566544db818ad110b34a66ae147
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1178 (reduceState modulus Block90.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1181,[14173]),(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1179 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1179 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1184 modulus last :=
  certifyBlock (by decide) Block90.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block91
namespace OeisA113258.Block92
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x74069413ceaebe4ed76a31248c755be41b137a862340c17f7346978e64f3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1184 (reduceState modulus Block91.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1187,[9497]),(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1185 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1185 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1190 modulus last :=
  certifyBlock (by decide) Block91.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block92
namespace OeisA113258.Block93
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x320a8bef344ad3a0f068e3234e6590160aa7476a9db173fd7fa5aefeb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1190 (reduceState modulus Block92.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1193,[7159]),(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1191 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1191 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1196 modulus last :=
  certifyBlock (by decide) Block92.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block93
namespace OeisA113258.Block94
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x1ca183e0cab50e8e5bb4d75964f5ea85b10f5b75bff56370d1c6ad
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1196 (reduceState modulus Block93.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1201,[7207]),(1213,[14557]),(1217,[29209]),(1223,[2447,17123]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1197 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1197 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1202 modulus last :=
  certifyBlock (by decide) Block93.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block94
namespace OeisA113258.Block95
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x3e4764900c71c69c66d0ef9d6da398440a5e9df4ea0dbb9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1202 (reduceState modulus Block94.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1203 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1203 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1208 modulus last :=
  certifyBlock (by decide) Block94.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block95
namespace OeisA113258.Block96
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x3e4764900c71c69c66d0ef9d6da398440a5e9df4ea0dbb9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1208 (reduceState modulus Block95.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1213,[14557]),(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1209 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1209 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1214 modulus last :=
  certifyBlock (by decide) Block95.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block96
namespace OeisA113258.Block97
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x1186193c6bf670c1fb4537de36f157a2bc2b4b6a128d
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1214 (reduceState modulus Block96.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1217,[29209]),(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1215 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1215 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1220 modulus last :=
  certifyBlock (by decide) Block96.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block97
namespace OeisA113258.Block98
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x27516c6da8fd9d2c1660a2a6eafc6506717e3a95
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1220 (reduceState modulus Block97.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1223,[2447]),(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1221 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1221 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1226 modulus last :=
  certifyBlock (by decide) Block97.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block98
namespace OeisA113258.Block99
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x41d06020e8a7945295d1260583100a15dff9b
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1226 (reduceState modulus Block98.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1229,[2459]),(1231,[19697]),(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1227 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1227 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1232 modulus last :=
  certifyBlock (by decide) Block98.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block99
namespace OeisA113258.Block100
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x16cc0ddf0890957f0674ceb52b18611
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1232 (reduceState modulus Block99.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1237,[19793]),(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1233 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1233 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1238 modulus last :=
  certifyBlock (by decide) Block99.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block100
namespace OeisA113258.Block101
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x4b7b94d7e63e48716258bc47cc1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1238 (reduceState modulus Block100.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1239 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1239 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1244 modulus last :=
  certifyBlock (by decide) Block100.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block101
namespace OeisA113258.Block102
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x4b7b94d7e63e48716258bc47cc1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1244 (reduceState modulus Block101.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1249,[12491]),(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1245 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1245 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1250 modulus last :=
  certifyBlock (by decide) Block101.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block102
namespace OeisA113258.Block103
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x18c0837167cdc1f6d2445323
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1250 (reduceState modulus Block102.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1251 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1251 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1256 modulus last :=
  certifyBlock (by decide) Block102.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block103
namespace OeisA113258.Block104
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x18c0837167cdc1f6d2445323
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1256 (reduceState modulus Block103.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1259,[17627]),(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1257 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1257 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1262 modulus last :=
  certifyBlock (by decide) Block103.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block104
namespace OeisA113258.Block105
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x5c06bb0cc3554b491959
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1262 (reduceState modulus Block104.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1263 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1263 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1268 modulus last :=
  certifyBlock (by decide) Block104.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block105
namespace OeisA113258.Block106
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x5c06bb0cc3554b491959
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1268 (reduceState modulus Block105.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1269 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1269 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1274 modulus last :=
  certifyBlock (by decide) Block105.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block106
namespace OeisA113258.Block107
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x5c06bb0cc3554b491959
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1274 (reduceState modulus Block106.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1277,[25541]),(1279,[12791]),(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1275 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1275 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1280 modulus last :=
  certifyBlock (by decide) Block106.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block107
namespace OeisA113258.Block108
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x4b9d812936e63
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1280 (reduceState modulus Block107.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1283,[7699]),(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1281 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1281 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1286 modulus last :=
  certifyBlock (by decide) Block107.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block108
namespace OeisA113258.Block109
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x283a863871
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 6 1286 (reduceState modulus Block108.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1289,[2579]),(1291,[12911]),(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1287 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1287 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1292 modulus last :=
  certifyBlock (by decide) Block108.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block109
namespace OeisA113258.Block110
open PackedCompute BookCheck OeisA113258.Compact
noncomputable def modulus : Nat := 0x1445
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def data : {v : List Nat × State // blockResult modulus 7 1292 (reduceState modulus Block109.last) = v} := by
  refine ⟨?value, ?proof⟩
  case proof => conv => lhs; reduce
noncomputable def last : State := data.val.2
noncomputable def rs : List Nat := data.val.1
noncomputable def part0 : Book := [(1297,[5189])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cells0 : checked 1293 rs part0 = true := rfl
noncomputable def book : Book := part0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCells : checked 1293 rs book = true := cells0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verified : Chain1300.Prefix 1299 modulus last :=
  certifyBlock (by decide) Block109.verified (by decide +kernel) data.property allCells
    (by decide +kernel) (by decide +kernel)
end OeisA113258.Block110
theorem OMA.disproof : ¬ (type_of% @OeisA113258.conjecture) :=
  OeisA113258.Direct.no_perfect_power_of_prefix1300 OeisA113258.Block110.verified
