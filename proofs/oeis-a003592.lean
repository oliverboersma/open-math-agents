import OMAStatements.S_oeis_a003592

-- Credit: @Iraeeee. Conjecture of Zhi-Wei Sun, OEIS A003592 (18 April 2023).
-- The proof combines a kernel-checked finite interval with overlapping dyadic
-- scales. The balancing lemma prescribes binary digits with bounded total error.
namespace Sun3592

def coin (e : ℕ × ℕ) : ℕ := 2^e.1 * 5^e.2 + 1

def Represents (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ x ∈ S, ∃ a b : ℕ, x = 2^a * 5^b + 1) ∧
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ x ∣ y) ∧ ∑ x ∈ S, x = n

def Subsum (xs : List ℕ) (n : ℕ) : Prop :=
  ∃ ys : List ℕ, ys.Sublist xs ∧ ys.sum = n

theorem from_subsum (es : List (ℕ × ℕ)) {n : ℕ} (h : Subsum (es.map coin) n)
    (hd : (es.map coin).Nodup)
    (hp : ∀ x ∈ es.map coin, ∀ y ∈ es.map coin, x ≠ y → ¬x ∣ y) : Represents n := by
  obtain ⟨ys,hs,hn⟩ := h
  refine ⟨ys.toFinset, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp (hs.subset (List.mem_toFinset.mp hx))
    exact ⟨e.1,e.2,rfl⟩
  · intro x hx y hy he
    exact hp x (hs.subset (List.mem_toFinset.mp hx)) y (hs.subset (List.mem_toFinset.mp hy)) he
  · simpa using (List.sum_toFinset id (hd.sublist hs)).trans (by simpa using hn)

def bits : List ℕ → ℕ
  | [] => 1
  | x :: xs => let b := bits xs; b ||| (b <<< x)

theorem subsum_of_bit (xs : List ℕ) (n : ℕ) (h : (bits xs).testBit n = true) : Subsum xs n := by
  induction xs generalizing n with
  | nil =>
    cases n with
    | zero => exact ⟨[], .slnil, rfl⟩
    | succ n =>
      have := Nat.testBit_lt_two_pow (x := 1) (i := n+1) (by
        rw [pow_succ]; have hp : 0 < (2:ℕ)^n := by positivity
        omega)
      simp [bits, this] at h
  | cons x xs ih =>
    simp only [bits, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨hle,h⟩
    · obtain ⟨ys,hs,hn⟩ := ih n h
      exact ⟨ys, hs.cons x, hn⟩
    · obtain ⟨ys,hs,hn⟩ := ih (n-x) h
      exact ⟨x :: ys, hs.cons_cons x, by simp [hn]; omega⟩

def checkSteps (lo hi : ℕ) : List ℕ → Bool
  | [] => true
  | x :: xs => decide (x+lo ≤ hi+1) && checkSteps lo (hi+x) xs

theorem extend_interval (xs seed : List ℕ) (lo hi : ℕ) (ok : checkSteps lo hi xs = true)
    (base : ∀ n, lo ≤ n → n ≤ hi → Subsum seed n) :
    ∀ n, lo ≤ n → n ≤ hi+xs.sum → Subsum (xs.reverse ++ seed) n := by
  induction xs generalizing seed hi with
  | nil => simpa using base
  | cons x xs ih =>
    simp only [checkSteps, Bool.and_eq_true, decide_eq_true_eq] at ok
    have hbase (n : ℕ) (hl : lo ≤ n) (hr : n ≤ hi+x) : Subsum (x::seed) n := by
      by_cases hn : n ≤ hi
      · obtain ⟨ys,hs,he⟩ := base n hl hn
        exact ⟨ys, hs.cons x, he⟩
      · obtain ⟨ys,hs,he⟩ := base (n-x) (by omega) (by omega)
        exact ⟨x::ys, hs.cons_cons x, by simp [he]; omega⟩
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      ih (x::seed) (hi+x) ok.2 hbase

def seed : List (ℕ × ℕ) := [(2, 0), (0, 1), (3, 0), (1, 1), (4, 0), (2, 1), (0, 2), (3, 1), (2, 2), (7, 0), (5, 1), (3, 2), (1, 3), (8, 0), (6, 1)]

def additions : List (ℕ × ℕ) := [(7, 1), (4, 3), (5, 3), (8, 2), (4, 4), (12, 1), (13, 1), (16, 0), (17, 0), (11, 3), (19, 0), (15, 2), (9, 5), (19, 1), (6, 7), (23, 0), (17, 3), (4, 9), (19, 3), (20, 3), (14, 6), (1, 12), (18, 5), (26, 2), (6, 11), (21, 5), (15, 8), (9, 11), (3, 14), (4, 14), (35, 1), (36, 1), (37, 1), (24, 7), (32, 4), (33, 4), (34, 4), (35, 4), (36, 4), (30, 7), (31, 7), (18, 13), (26, 10), (27, 10), (28, 10), (15, 16), (2, 22), (47, 3), (50, 2), (21, 15), (22, 15), (23, 15), (10, 21), (4, 24), (49, 5), (36, 11), (51, 5), (24, 17), (39, 11), (33, 14), (34, 14), (21, 20), (29, 17), (30, 17), (24, 20), (69, 1), (12, 26), (6, 29), (72, 1), (73, 1), (2, 32), (3, 32), (48, 13), (56, 10), (57, 10), (58, 10), (59, 10), (46, 16), (54, 13), (55, 13), (42, 19), (50, 16), (30, 25), (38, 22), (39, 22), (40, 22), (41, 22), (42, 22), (36, 25), (37, 25), (24, 31), (32, 28), (91, 3), (92, 3), (21, 34), (22, 34), (23, 34), (24, 34), (90, 6), (19, 37), (85, 9), (21, 37), (80, 12), (2, 46), (68, 18), (4, 46), (5, 46), (6, 46), (65, 21), (1, 49), (67, 21), (68, 21), (69, 21), (49, 30)]

def tiny : List (List (ℕ × ℕ)) := [
  [],
  [],
  [(0, 0)],
  [(1, 0)],
  [],
  [(2, 0)],
  [(0, 1)],
  [(0, 0), (2, 0)],
  [(1, 0), (2, 0)],
  [(3, 0)],
  [(0, 0), (1, 0), (2, 0)],
  [(1, 1)],
  [],
  [(0, 0), (1, 1)],
  [(2, 0), (3, 0)],
  [(0, 1), (3, 0)],
  [(2, 0), (1, 1)],
  [(4, 0)],
  [(0, 0), (2, 0), (1, 1)],
  [(1, 0), (2, 0), (1, 1)],
  [(3, 0), (1, 1)],
  [(2, 1)],
  [(2, 0), (4, 0)],
  [(0, 1), (4, 0)],
  [(0, 0), (2, 0), (4, 0)],
  [(2, 0), (3, 0), (1, 1)],
  [(0, 2)],
  [(0, 1), (2, 1)],
  [(1, 1), (4, 0)],
  [(1, 0), (0, 2)],
  [(3, 0), (2, 1)],
  [(2, 0), (0, 2)],
  [(1, 1), (2, 1)],
  [(5, 0)],
  [(0, 1), (1, 1), (4, 0)],
  [(3, 0), (0, 2)],
  [(0, 1), (3, 0), (2, 1)],
  [(1, 1), (0, 2)],
  [(4, 0), (2, 1)],
  [(0, 1), (5, 0)],
  [(2, 0), (3, 0), (0, 2)],
  [(3, 1)],
  [(3, 0), (5, 0)],
  [(4, 0), (0, 2)],
  [(0, 1), (4, 0), (2, 1)],
  [(1, 0), (2, 0), (1, 1), (0, 2)],
  [(3, 0), (1, 1), (0, 2)],
  [(2, 1), (0, 2)],
  [(0, 1), (3, 0), (5, 0)],
  [(1, 1), (4, 0), (2, 1)],
  [(4, 0), (5, 0)],
  [(1, 2)],
  [(1, 1), (3, 1)],
  [(0, 1), (2, 1), (0, 2)],
  [(2, 1), (5, 0)],
  [(0, 1), (1, 1), (4, 0), (2, 1)],
  [(3, 0), (2, 1), (0, 2)],
  [(0, 1), (1, 2)],
  [(4, 0), (3, 1)],
  [(0, 2), (5, 0)],
  [(3, 0), (1, 2)],
  [(3, 0), (1, 1), (3, 1)],
  [(2, 1), (3, 1)],
  [(3, 0), (2, 1), (5, 0)],
  [(4, 0), (2, 1), (0, 2)],
  [(6, 0)],
  [(0, 1), (3, 0), (1, 2)],
  [(0, 2), (3, 1)],
  [(3, 0), (0, 2), (5, 0)],
  [(1, 1), (4, 0), (3, 1)],
  [(0, 1), (4, 0), (2, 1), (0, 2)],
  [(4, 0), (2, 1), (5, 0)],
  [(2, 1), (1, 2)],
  [(1, 1), (2, 1), (3, 1)],
  [(5, 0), (3, 1)],
  [(1, 1), (4, 0), (2, 1), (0, 2)],
  [(4, 0), (0, 2), (5, 0)],
  [(0, 2), (1, 2)],
  [(1, 1), (0, 2), (3, 1)],
  [(4, 0), (2, 1), (3, 1)],
  [(2, 1), (0, 2), (5, 0)],
  [(4, 1)],
  [(4, 0), (6, 0)],
  [(1, 1), (2, 1), (1, 2)],
  [(5, 0), (1, 2)],
  [(3, 0), (4, 0), (0, 2), (5, 0)],
  [(2, 1), (6, 0)],
  [(3, 0), (1, 1), (0, 2), (3, 1)],
  [(2, 1), (0, 2), (3, 1)],
  [(3, 0), (2, 1), (0, 2), (5, 0)],
  [(1, 1), (4, 0), (2, 1), (3, 1)],
  [(0, 2), (6, 0)]]

private def valid (xs : List ℕ) (n : ℕ) : Bool :=
  decide xs.Nodup && xs.all (fun x => xs.all fun y => decide (x ≠ y → ¬x ∣ y)) &&
    decide (xs.sum = n)

private theorem certified_tiny (i : Fin 92) (h0 : i.val ≠ 0) (h1 : i.val ≠ 1)
    (h4 : i.val ≠ 4) (h12 : i.val ≠ 12) : Represents i.val := by
  let es := tiny[i.val]!
  have cert : (List.range 92).all (fun j => decide (j = 0 ∨ j = 1 ∨ j = 4 ∨ j = 12) ||
      valid ((tiny[j]!).map coin) j) = true := by decide
  have hc := List.all_eq_true.mp cert i.val (List.mem_range.mpr i.isLt)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
  rcases hc with (hh|hh|hh|hh) | hc
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨hd,hp⟩,hn⟩ := hc
  exact from_subsum es ⟨es.map coin, List.Sublist.refl _, hn⟩ hd hp

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem finite_prefix (n : ℕ) (hn : n ≤ 3125*(25*96+1500)*2^96)
    (h0 : 0 < n) (h1 : n ≠ 1) (h4 : n ≠ 4) (h12 : n ≠ 12) : Represents n := by
  by_cases hs : n < 92
  · exact certified_tiny ⟨n,hs⟩ (Nat.ne_of_gt h0) h1 h4 h12
  let es := additions.reverse ++ seed
  have hseed : (List.range 1374).all (fun j => (bits (seed.map coin)).testBit (92+j)) = true := by decide
  have base (k : ℕ) (h : 92 ≤ k) (hh : k ≤ 1465) : Subsum (seed.map coin) k := by
    have hk := List.all_eq_true.mp hseed (k-92) (List.mem_range.mpr (by omega))
    rw [show 92+(k-92)=k by omega] at hk
    exact subsum_of_bit _ _ hk
  have ok : checkSteps 92 1465 (additions.map coin) = true := by decide
  have bound : 3125*(25*96+1500)*2^96 ≤ 1465 + (additions.map coin).sum := by decide
  have rep := extend_interval _ _ _ _ ok base n (by omega) (hn.trans bound)
  apply from_subsum es
  · simpa [es,List.map_reverse] using rep
  · have hz : (es.map coin).Nodup := by decide
    exact hz
  · have hz : (es.map coin).all (fun x => (es.map coin).all fun y => decide (x ≠ y → ¬x ∣ y)) = true := by decide
    simpa only [List.all_eq_true, decide_eq_true_eq] using hz

/-- The factor 3125 bounds quotients between distinct high summands. -/
theorem band_primitive {T u v : ℕ} (hu : T ≤ u) (hv : v ≤ 3125*T) (hne : u ≠ v) :
    ¬ 3125*u+1 ∣ 3125*v+1 := by
  rintro ⟨q,hq⟩
  have hrem := congrArg (fun z : ℕ => z % 3125) hq
  simp [Nat.add_mod, Nat.mul_mod] at hrem
  have hq1 : q ≠ 1 := by rintro rfl; simp at hq; omega
  have hqbig : 3126 ≤ q := by omega
  have hprod := Nat.mul_le_mul (show 3125*T+1 ≤ 3125*u+1 by omega) hqbig
  omega

private theorem reaches (m a : ℕ) : ∃ b : ℕ, 2^m ≤ 2^a * 5^b := by
  refine ⟨m, ?_⟩
  have ha : 1 ≤ (2:ℕ)^a := Nat.one_le_two_pow
  have hp : (2:ℕ)^m ≤ 5^m := Nat.pow_le_pow_left (by decide) m
  exact hp.trans (by simpa using Nat.mul_le_mul_right (5^m) ha)

noncomputable def exponent5 (m a : ℕ) := Nat.find (reaches m a)
noncomputable def unitCoeff (m a : ℕ) := 2^a * 5^(exponent5 m a)

theorem unit_bounds {m a : ℕ} (ha : a < m) :
    2^m ≤ unitCoeff m a ∧ unitCoeff m a < 5*2^m := by
  have hlo := Nat.find_spec (reaches m a)
  refine ⟨hlo,?_⟩
  unfold unitCoeff
  cases hb : exponent5 m a with
  | zero =>
    simp only [pow_zero, mul_one]
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) ha.le
    have hpos : 0 < (2:ℕ)^m := by positivity
    omega
  | succ b =>
    have small : ¬ 2^m ≤ 2^a * 5^b := Nat.find_min (reaches m a)
      (show b < exponent5 m a by omega)
    rw [pow_succ]
    rw [← Nat.mul_assoc]
    omega

theorem unit_odd (m a : ℕ) : ∃ u : ℤ, (unitCoeff m a : ℤ) = 2^a*(2*u+1) := by
  obtain ⟨u,hu⟩ := (show Odd ((5:ℕ)^(exponent5 m a)) from (show Odd (5:ℕ) from ⟨2,rfl⟩).pow)
  refine ⟨u,?_⟩
  unfold unitCoeff
  rw [hu]
  push_cast
  ring

private theorem factors_injective {a b c d : ℕ} (h : 2^a*5^b = 2^c*5^d) :
    a=c ∧ b=d := by
  have fact (i j : ℕ) : (2^i*5^j).factorization 2 = i := by
    rw [Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
      Nat.factorization_pow, Nat.factorization_pow]
    simp [Nat.Prime.factorization, Nat.prime_two, show Nat.Prime 5 by decide]
  have e := congrArg (fun n : ℕ => n.factorization 2) h
  simp only [fact] at e
  subst c
  have hh : (5:ℕ)^b = 5^d := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^a) h
  exact ⟨rfl, (pow_right_injective₀ (by decide : 0 < (5:ℕ)) (by decide : (5:ℕ) ≠ 1)) hh⟩

noncomputable def high (m : ℕ) (p : ℕ × ℕ) :=
  3125*(unitCoeff m p.1 * 5^p.2)+1

theorem high_injective (m : ℕ) : Function.Injective (high m) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ he
  change 3125*(unitCoeff m a*5^b)+1 = 3125*(unitCoeff m c*5^d)+1 at he
  have h : unitCoeff m a*5^b = unitCoeff m c*5^d := by omega
  simp only [unitCoeff, Nat.mul_assoc, ← pow_add] at h
  obtain ⟨rfl, hh⟩ := factors_injective h
  simp_all

/-- The right shift folds a shifted sum back by one modulus. Bits above M
are harmless: the soundness statement only needs congruence. -/
def circularBits (M : ℕ) : List ℕ → ℕ
  | [] => 1
  | x :: xs =>
    let b := circularBits M xs
    let r := x % M
    (b ||| (b <<< r)) ||| (b >>> (M-r))

theorem circular_sound (M : ℕ) (hM : 0 < M) (xs : List ℕ) (n : ℕ)
    (h : (circularBits M xs).testBit n = true) :
    ∃ ys : List ℕ, ys.Sublist xs ∧ ys.sum ≡ n [MOD M] := by
  induction xs generalizing n with
  | nil =>
    cases n with
    | zero => exact ⟨[], .slnil, rfl⟩
    | succ n =>
      have hh := Nat.testBit_lt_two_pow (x := 1) (i := n+1) (by
        rw [pow_succ]; have hp : 0 < (2:ℕ)^n := by positivity
        omega)
      simp [circularBits,hh] at h
  | cons x xs ih =>
    simp only [circularBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with (h | ⟨hle,h⟩) | h
    · obtain ⟨ys,hs,hy⟩ := ih _ h
      exact ⟨ys,hs.cons x,hy⟩
    · obtain ⟨ys,hs,hy⟩ := ih _ h
      refine ⟨x::ys,hs.cons_cons x,?_⟩
      simpa [Nat.add_sub_of_le hle] using ((Nat.mod_modEq x M).symm.add hy)
    · obtain ⟨ys,hs,hy⟩ := ih _ h
      refine ⟨x::ys,hs.cons_cons x,?_⟩
      have hm := Nat.mod_lt x hM
      have he : x % M + (M - x % M + n) = M+n := by omega
      have hh := (Nat.mod_modEq x M).symm.add hy
      rw [he] at hh
      exact hh.trans (by simp [Nat.ModEq])

def lowTerms : List ℕ := (List.range 15).map fun i => 2^(30+4*i)+1

def lowQuotients : List ℕ := lowTerms.map (· / 5)

set_option maxRecDepth 8192 in
theorem low_residues (r : ℕ) (hr : r < 12500) (hd : 5 ∣ r) :
    ∃ ys : List ℕ, ys.Sublist lowTerms ∧ ys.sum ≡ r [MOD 12500] := by
  have mask : circularBits 2500 lowQuotients % 2^2500 = 2^2500-1 := by
    have hc : circularBits 2500 lowQuotients % (1 <<< 2500) = (1 <<< 2500)-1 := by decide
    simpa [Nat.shiftLeft_eq] using hc
  obtain ⟨k, rfl⟩ := hd
  have hk : k < 2500 := by omega
  have hbit := congrArg (fun n : ℕ => n.testBit k) mask
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, decide_eq_true hk,
    Bool.true_and] at hbit
  obtain ⟨ys,hs,hy⟩ := circular_sound 2500 (by decide) lowQuotients k hbit
  have hmap : lowQuotients.map (5 * ·) = lowTerms := by decide
  refine ⟨ys.map (5*·), hmap ▸ hs.map (5*·), ?_⟩
  have he := Nat.modEq_iff_dvd.mp hy
  have hsum : (ys.map (5*·)).sum = 5*ys.sum := by simpa using List.sum_map_mul_left ys id (r := (5:ℕ))
  rw [Nat.modEq_iff_dvd, hsum]
  simp only [List.map_id_fun, id_eq, Nat.cast_mul, Nat.cast_ofNat]
  obtain ⟨j,hj⟩ := he
  exact ⟨j,by push_cast at hj ⊢; linarith⟩

def fineSum (v : ℕ → ℤ) (j : ℕ → Fin 4) (k : ℕ) : ℤ :=
  ∑ a ∈ Finset.range k, (5 : ℤ)^(j a).val * v a

def baseline (v : ℕ → ℤ) (k : ℕ) : ℤ := ∑ a ∈ Finset.range k, v a

private lemma extend_fine (v : ℕ → ℤ) (j : ℕ → Fin 4) (k : ℕ) (b : Fin 4) :
    fineSum v (Function.update j k b) (k+1) = fineSum v j k + (5 : ℤ)^b.val * v k := by
  rw [fineSum, Finset.sum_range_succ, Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.mem_range.mp hi).ne]

private theorem choose_digit (u q T val err : ℤ)
    (hT : 0 < T) (hv : T ≤ val) (hv' : val < 5*T)
    (hl : -25*T ≤ err) (hh : err ≤ 600*T) :
    ∃ j : Fin 4, (∃ z : ℤ, 4*q - (5^(j.val) - 1)*(2*u+1) = 8*z) ∧
      -25*T ≤ err + 5^(j.val)*val - 25*T ∧ err + 5^(j.val)*val - 25*T ≤ 600*T := by
  by_cases high : err < 0
  · by_cases even : q % 2 = 0
    · refine ⟨2, ⟨q/2 - 6*u - 3, ?_⟩, ?_, ?_⟩ <;> norm_num <;> omega
    · refine ⟨3, ⟨q/2 - 31*u - 15, ?_⟩, ?_, ?_⟩ <;> norm_num <;> omega
  · by_cases even : q % 2 = 0
    · refine ⟨0, ⟨q/2, ?_⟩, ?_, ?_⟩ <;> norm_num <;> omega
    · refine ⟨1, ⟨q/2 - u, ?_⟩, ?_, ?_⟩ <;> norm_num <;> omega

/-- Prescribe a residue modulo four times 2^m while keeping the sum in a band of fixed width. -/
theorem balanced_digits (m : ℕ) (T w : ℤ) (v : ℕ → ℤ) (hT : 0 < T)
    (hv : ∀ a < m, T ≤ v a ∧ v a < 5*T ∧ ∃ u : ℤ, v a = 2^a*(2*u+1))
    (hw : 4 ∣ w-baseline v m) :
    ∃ j : ℕ → Fin 4, 4*(2:ℤ)^m ∣ w - fineSum v j m ∧
      (25*(m:ℤ)-25)*T ≤ fineSum v j m ∧ fineSum v j m ≤ (25*(m:ℤ)+600)*T := by
  have step (k : ℕ) (hk : k ≤ m) :
      ∃ j : ℕ → Fin 4,
        4*(2:ℤ)^k ∣ w-baseline v m - (fineSum v j k - baseline v k) ∧
        -25*T ≤ fineSum v j k - 25*(k:ℤ)*T ∧ fineSum v j k - 25*(k:ℤ)*T ≤ 600*T := by
    induction k with
    | zero => exact ⟨fun _ => 0, by simpa [fineSum, baseline] using hw, by simp [fineSum]; omega,
        by simp [fineSum]; omega⟩
    | succ k ih =>
      obtain ⟨j,⟨q,hq⟩,hl,hh⟩ := ih (by omega)
      obtain ⟨hlo,hhi,u,hu⟩ := hv k (by omega)
      obtain ⟨b,⟨z,hz⟩,hb,hb'⟩ := choose_digit u q T (v k) (fineSum v j k-25*(k:ℤ)*T)
        hT hlo hhi hl hh
      refine ⟨Function.update j k b, ⟨z, ?_⟩, ?_, ?_⟩
      · rw [extend_fine, show baseline v (k+1) = baseline v k + v k by
          simp [baseline,Finset.sum_range_succ], pow_succ]
        calc
          _ = (w - baseline v m - (fineSum v j k - baseline v k)) -
              ((5:ℤ)^b.val-1)*v k := by ring
          _ = (2:ℤ)^k * (4*q - ((5:ℤ)^b.val-1)*(2*u+1)) := by rw [hq,hu]; ring
          _ = _ := by rw [hz]; ring
      · rw [extend_fine]; push_cast; linarith
      · rw [extend_fine]; push_cast; linarith
  obtain ⟨j,hj,hl,hh⟩ := step m le_rfl
  exact ⟨j, by convert hj using 1 <;> ring, by linarith, by linarith⟩

private lemma sublist_sum_le {ys xs : List ℕ} (h : ys.Sublist xs) : ys.sum ≤ xs.sum := by
  induction h with
  | slnil => rfl
  | cons a h ih => simp; omega
  | cons_cons a h ih => simpa using Nat.add_le_add_left ih a

/-- The arithmetic for the continuous central interval, including the low and reserve terms. -/
theorem central_parameters (m : ℕ) (n T : ℤ) (v : ℕ → ℤ) (R : ℕ → ℤ)
    (hT : T = (2:ℤ)^m) (hm : 96 ≤ m)
    (hv : ∀ a < m, T ≤ v a ∧ v a < 5*T ∧ ∃ u : ℤ, v a = 2^a*(2*u+1))
    (hR : ∀ e < 5, 0 ≤ R e ∧ R e ≤ 375*T)
    (hlo : 3125*(25*(m:ℤ)+1500)*T ≤ n) (hhi : n ≤ 3125*(25*(m:ℤ)+2500)*T) :
    ∃ e : ℕ, e < 5 ∧ ∃ ys : List ℕ, ys.Sublist lowTerms ∧ ∃ j : ℕ → Fin 4, ∃ z : ℕ,
      z < 512 ∧ n = (m:ℤ)+9+e+ys.sum + 3125*(R e + fineSum v j m + 511*T + 4*T*z) := by
  have htpos : 0 < T := hT ▸ by positivity
  let H : ℤ := m+9
  let e := ((n-H)%5).toNat
  have he : (e:ℤ) = (n-H)%5 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  have he5 : e < 5 := by omega
  let A := n-H-e-3125*(R e+baseline v m+511*T)
  let r := (A%12500).toNat
  have hr : (r:ℤ) = A%12500 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  have hr0 : r < 12500 := by omega
  have h5 : 5 ∣ r := by dsimp [A] at hr; omega
  obtain ⟨ys,hys,hmod⟩ := low_residues r hr0 h5
  have hyslim := (sublist_sum_le hys).trans (show lowTerms.sum ≤ 2^87 by decide)
  have hsmall : (ys.sum : ℤ) ≤ T := by
    have hpow : (2:ℕ)^87 ≤ 2^m := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hT]; exact_mod_cast hyslim.trans hpow
  have hcount : H + e ≤ T := by
    have hpow : m-1 < 2^(m-1) := Nat.lt_two_pow_self
    have heq : (2:ℕ)^m = 2^(m-1)*2 := by
      conv_lhs => rw [show m = (m-1)+1 by omega,pow_succ]
    have hm' : m+9+e ≤ (2:ℕ)^m := by omega
    dsimp [H]; rw [hT]; exact_mod_cast hm'
  have hsy : (ys.sum : ℤ) % 12500 = (r:ℤ) := by
    have hh : ys.sum % 12500 = r := (show ys.sum % 12500 = r % 12500 from hmod).trans (Nat.mod_eq_of_lt hr0)
    exact_mod_cast hh
  let w := (n-H-e-ys.sum)/3125 - R e - 511*T
  have hw : 4 ∣ w-baseline v m := by dsimp [A] at hr; dsimp [w]; omega
  have hidentity : n = H+e+ys.sum + 3125*(w + R e + 511*T) := by
    dsimp [A] at hr; dsimp [w]; omega
  obtain ⟨j,⟨z,hz⟩,hl,hh⟩ := balanced_digits m T w v htpos hv hw
  rw [← hT] at hz
  obtain ⟨hR0,hRu⟩ := hR e he5
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hz0 : 0 ≤ z := by
    by_contra! hneg
    have hprod := mul_neg_of_pos_of_neg (by linarith : 0 < 4*T) hneg
    nlinarith
  have hz512 : z < 512 := by
    by_contra! hlarge
    have hprod := mul_le_mul_of_nonneg_left hlarge (by linarith : 0 ≤ 4*T)
    have hs0 : (0:ℤ) ≤ ys.sum := by positivity
    nlinarith
  refine ⟨e,he5,ys,hys,j,z.toNat,by omega,?_⟩
  rw [Int.toNat_of_nonneg hz0]
  dsimp [H] at hidentity
  linarith

theorem exponent_above (m a : ℕ) (ha : m ≤ a) : exponent5 m a = 0 := by
  apply Nat.le_zero.mp
  exact Nat.find_min' (reaches m a) (show 2^m ≤ 2^a*5^0 by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) ha)

theorem unit_above (m a : ℕ) (ha : m ≤ a) : unitCoeff m a = 2^a := by
  simp [unitCoeff, exponent_above m a ha]

def Allowed (m : ℕ) (p : ℕ × ℕ) : Prop :=
  2^m ≤ unitCoeff m p.1 * 5^p.2 ∧ unitCoeff m p.1 * 5^p.2 ≤ 3125*2^m

private lemma fine_allowed {m a b : ℕ} (ha : a < m) (hb : b ≤ 4) : Allowed m (a,b) := by
  obtain ⟨hl,hr⟩ := unit_bounds ha
  have hpow : 5^b ≤ (625:ℕ) := Nat.pow_le_pow_right (by decide) hb
  exact ⟨hl.trans (Nat.le_mul_of_pos_right _ (by positivity)),
    (Nat.mul_le_mul (Nat.le_of_lt hr) hpow).trans (by ring_nf; rfl)⟩

def Coded (m n : ℕ) (pool : Finset (ℕ × ℕ)) : Prop :=
  ∃ ys : List ℕ, ys.Sublist lowTerms ∧ ∃ used ⊆ pool,
    (∀ p ∈ used, Allowed m p) ∧ n = ys.sum + ∑ p ∈ used, high m p

private lemma low_to_high {m : ℕ} (hm : 96 ≤ m) (ys : List ℕ) (hs : ys.Sublist lowTerms)
    (used : Finset (ℕ × ℕ)) (hu : ∀ p ∈ used, Allowed m p) :
    Disjoint ys.toFinset (used.image (high m)) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hy
  have all5 : ∀ u ∈ lowTerms, 5 ∣ u := by decide
  have h := all5 _ (hs.subset (List.mem_toFinset.mp hx))
  unfold high at h
  omega

private lemma hsmoothLow {ys : List ℕ} {x : ℕ} (hs : ys.Sublist lowTerms) (hx : x ∈ ys.toFinset) :
    ∃ a b : ℕ, x = 2^a*5^b+1 := by
  obtain ⟨i,_,hi⟩ := List.mem_map.mp (show x ∈ lowTerms from hs.subset (List.mem_toFinset.mp hx))
  exact ⟨30+4*i,0,by simpa using hi.symm⟩

theorem decode {m n : ℕ} {pool} (hm : 96 ≤ m) (h : Coded m n pool) : Represents n := by
  classical
  obtain ⟨ys,hys,used,_,hu,rfl⟩ := h
  have dis := low_to_high hm ys hys used hu
  refine ⟨ys.toFinset ∪ used.image (high m), ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · have hh := hsmoothLow (ys := ys) (x := x) hys hx
      exact hh
    · obtain ⟨⟨a,b⟩,_,rfl⟩ := Finset.mem_image.mp hx
      refine ⟨a,exponent5 m a+b+5,?_⟩
      simp [high,unitCoeff,pow_add]
      ring
  · intro x hx y hy hne hdiv
    have low5 : ∀ x ∈ lowTerms, 5 ∣ x := by decide
    have lowSmall : ∀ x ∈ lowTerms, x < 2^96 := by decide
    have lowPrim : ∀ x ∈ lowTerms, ∀ y ∈ lowTerms, x ≠ y → ¬ x ∣ y := by decide
    have hpow : (2:ℕ)^96 ≤ 2^m := Nat.pow_le_pow_right (by decide) hm
    rcases Finset.mem_union.mp hx with hx|hx <;> rcases Finset.mem_union.mp hy with hy|hy
    · exact lowPrim x (hys.subset (List.mem_toFinset.mp hx)) y (hys.subset (List.mem_toFinset.mp hy)) hne hdiv
    · obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hy
      have hd := (low5 _ (hys.subset (List.mem_toFinset.mp hx))).trans hdiv
      unfold high at hd; omega
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      have hl := (hu p hp).1
      have hy' := hys.subset (List.mem_toFinset.mp hy)
      have hpos : ∀ u ∈ lowTerms, 0 < u := by decide
      have hh := Nat.le_of_dvd (hpos y hy') hdiv
      have hlt := lowSmall y hy'
      unfold high at hh
      omega
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
      apply band_primitive (hu p hp).1 (hu q hq).2 _ hdiv
      intro he
      apply hne
      simpa only [high,he]
  · have hsum : (∑ x ∈ ys.toFinset, x) = ys.sum := by
      simpa using List.sum_toFinset id (l := ys) (by
        have h : lowTerms.Nodup := by decide
        exact h.sublist hys)
    rw [Finset.sum_union dis, hsum, Finset.sum_image (fun a _ b _ he => high_injective m he)]

def graph (start len : ℕ) (f : ℕ → ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range len).image fun i => (start+i,f i)

private lemma mem_graph {p start len f} : p ∈ graph start len f ↔
    ∃ i < len, (start+i,f i) = p := by simp [graph]

private lemma graph_sum (start len : ℕ) (f : ℕ → ℕ) (g : ℕ × ℕ → ℕ) :
    ∑ p ∈ graph start len f, g p = ∑ i ∈ Finset.range len, g (start+i,f i) := by
  apply Finset.sum_image
  intro a _ b _ he
  simpa using congrArg Prod.fst he

def corePool (m : ℕ) := Finset.range (m+9) ×ˢ Finset.range 4

def reserveCoeff (m e : ℕ) := ∑ i ∈ Finset.range e, 25*2^(m+i)

private lemma reserve_bound {m e : ℕ} (he : e < 5) : reserveCoeff m e ≤ 375*2^m := by
  unfold reserveCoeff
  calc
    _ ≤ ∑ i ∈ Finset.range 4, 25*2^(m+i) := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (by intros; omega)
    _ = _ := by simp [Finset.sum_range_succ,pow_add]; ring

private lemma upper_allowed {m i b : ℕ} (hi : i < 9) (hb : b ≤ 1 ∨ (i < 4 ∧ b ≤ 2)) :
    Allowed m (m+i,b) := by
  change 2^m ≤ unitCoeff m (m+i)*5^b ∧ unitCoeff m (m+i)*5^b ≤ 3125*2^m
  rw [unit_above m (m+i) (by omega),pow_add]
  have hl : 1 ≤ (2:ℕ)^i*5^b := by apply Nat.succ_le_of_lt; positivity
  have hu : 2^i*5^b ≤ 3125 := by
    rcases hb with hb|⟨hi',hb⟩
    · have hx : (2:ℕ)^i ≤ 2^8 := Nat.pow_le_pow_right (by decide) (by omega)
      have hy : (5:ℕ)^b ≤ 5^1 := Nat.pow_le_pow_right (by decide) hb
      exact (Nat.mul_le_mul hx hy).trans (by decide)
    · have hx : (2:ℕ)^i ≤ 2^3 := Nat.pow_le_pow_right (by decide) (by omega)
      have hy : (5:ℕ)^b ≤ 5^2 := Nat.pow_le_pow_right (by decide) hb
      exact (Nat.mul_le_mul hx hy).trans (by decide)
  simpa [Nat.mul_assoc,Nat.mul_comm 3125] using
    And.intro (Nat.mul_le_mul_left (2^m) hl) (Nat.mul_le_mul_left (2^m) hu)

private lemma high_sum (m : ℕ) (s : Finset (ℕ × ℕ)) :
    ∑ p ∈ s, high m p = s.card + 3125 * ∑ p ∈ s, unitCoeff m p.1 * 5^p.2 := by
  simp [high, Finset.sum_add_distrib, Finset.mul_sum, Nat.add_comm]

private lemma graph_card (start len : ℕ) (f : ℕ → ℕ) : (graph start len f).card = len := by
  rw [graph, Finset.card_image_of_injOn, Finset.card_range]
  intro i _ j _ hh
  simpa using congrArg Prod.fst hh

def coarseSlot (z i : ℕ) : ℕ := if z.testBit i then 1 else 0

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private lemma coarse_sum (m z : ℕ) (hz : z < 512) :
    ∑ p ∈ graph m 9 (coarseSlot z), unitCoeff m p.1*5^p.2 =
    511*2^m + 4*2^m*z := by
  rw [graph_sum]
  have calc9 : ∀ k : Fin 512, ∑ i ∈ Finset.range 9, 2^i*5^(coarseSlot k.val i) = 511+4*k.val := by decide
  rw [show (∑ i ∈ Finset.range 9, unitCoeff m (m+i) * 5^(coarseSlot z i)) =
      2^m * ∑ i ∈ Finset.range 9, 2^i * 5^(coarseSlot z i) by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi
        rw [unit_above m (m+i) (by omega),pow_add,Nat.mul_assoc]]
  rw [calc9 ⟨z,hz⟩]
  simp <;> ring

private lemma reserve_sum (m e : ℕ) :
    ∑ p ∈ graph m e (fun _ => 2), unitCoeff m p.1*5^p.2 = reserveCoeff m e := by
  rw [graph_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [unit_above m (m+i) (by omega)]
  ring

private theorem assemble_core (m e z : ℕ) (he : e < 5) (hz : z < 512) (j : ℕ → Fin 4) :
    ∃ used ⊆ corePool m, (∀ p ∈ used, Allowed m p) ∧
      ∑ p ∈ used, high m p = m+9+e + 3125 * (reserveCoeff m e +
        (∑ i ∈ Finset.range m, 5^(j i).val*unitCoeff m i) + 511*2^m + 4*2^m*z) := by
  let f := graph 0 m (fun i => (j i).val)
  let c := graph m 9 (coarseSlot z)
  let r := graph m e (fun _ => 2)
  have hslot (i : ℕ) : coarseSlot z i ≤ 1 := by unfold coarseSlot; split <;> decide
  have hfc : Disjoint f c := by
    rw [Finset.disjoint_left]
    intro p hp hq
    obtain ⟨a,ha,ea⟩ := mem_graph.mp hp
    obtain ⟨b,hb,eb⟩ := mem_graph.mp hq
    have h := congrArg Prod.fst (ea.trans eb.symm)
    simp at h; omega
  have hfr : Disjoint f r := by
    rw [Finset.disjoint_left]
    intro p hp hq
    obtain ⟨a,ha,ea⟩ := mem_graph.mp hp
    obtain ⟨b,hb,eb⟩ := mem_graph.mp hq
    have h := congrArg Prod.fst (ea.trans eb.symm)
    simp at h; omega
  have hcr : Disjoint c r := by
    rw [Finset.disjoint_left]
    intro p hp hq
    obtain ⟨a,ha,ea⟩ := mem_graph.mp hp
    obtain ⟨b,hb,eb⟩ := mem_graph.mp hq
    have h := congrArg Prod.snd (ea.trans eb.symm)
    change coarseSlot z a = 2 at h
    have := hslot a; omega
  have hdis : Disjoint (f ∪ c) r := Finset.disjoint_union_left.mpr ⟨hfr,hcr⟩
  refine ⟨(f ∪ c) ∪ r,?_,?_,?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hp|hp
    · rcases Finset.mem_union.mp hp with hp|hp
      · obtain ⟨a,ha,rfl⟩ := mem_graph.mp hp
        simpa [corePool] using (show a < m+9 ∧ (j a).val < 4 from ⟨by omega,(j a).isLt⟩)
      · obtain ⟨i,hi,rfl⟩ := mem_graph.mp hp
        have := hslot i
        simp [corePool]; omega
    · obtain ⟨i,hi,rfl⟩ := mem_graph.mp hp
      simp [corePool]; omega
  · intro p hp
    rcases Finset.mem_union.mp hp with hp|hp
    · rcases Finset.mem_union.mp hp with hp|hp
      · obtain ⟨a,ha,rfl⟩ := mem_graph.mp hp
        simpa using fine_allowed ha (j a).isLt.le
      · obtain ⟨a,ha,rfl⟩ := mem_graph.mp hp
        exact upper_allowed ha (Or.inl (hslot a))
    · obtain ⟨a,ha,rfl⟩ := mem_graph.mp hp
      exact upper_allowed (by omega) (Or.inr ⟨by omega,le_rfl⟩)
  · rw [Finset.sum_union hdis,Finset.sum_union hfc,high_sum,high_sum,high_sum]
    dsimp only [f,c,r]
    rw [graph_card,graph_card,graph_card,coarse_sum m z hz,reserve_sum,graph_sum]
    simp only [zero_add]
    simp_rw [Nat.mul_comm (unitCoeff m _) (5^_)]
    ring

theorem core_covered (m n : ℕ) (hm : 96 ≤ m)
    (hlo : 3125*(25*m+1500)*2^m ≤ n) (hhi : n ≤ 3125*(25*m+2500)*2^m) :
    Coded m n (corePool m) := by
  obtain ⟨e,he,ys,hys,j,z,hz,hn⟩ := central_parameters m n (2^m)
    (fun i => (unitCoeff m i : ℤ)) (fun e => (reserveCoeff m e : ℤ)) rfl hm
    (fun a ha => ⟨by exact_mod_cast (unit_bounds ha).1,by exact_mod_cast (unit_bounds ha).2,unit_odd m a⟩)
    (fun e he => ⟨by positivity,by exact_mod_cast reserve_bound (m := m) he⟩)
    (by exact_mod_cast hlo) (by exact_mod_cast hhi)
  obtain ⟨used,hp,ha,hs⟩ := assemble_core m e z he hz j
  refine ⟨ys,hys,used,hp,ha,?_⟩
  rw [hs]
  have hnat : n = m+9+e+ys.sum + 3125*(reserveCoeff m e+
      (∑ i ∈ Finset.range m, 5^(j i).val*unitCoeff m i)+511*2^m+4*2^m*z) := by
    unfold fineSum at hn
    apply Int.ofNat_inj.mp
    push_cast
    push_cast at hn
    exact hn
  omega

def lowerEnd (m : ℕ) := 3125*(25*m+1500)*2^m
def upperEnd (m : ℕ) := 3125*(650*m+2500)*2^m

theorem scale_exists {n : ℕ} (hn : lowerEnd 96 ≤ n) :
    ∃ m : ℕ, 96 ≤ m ∧ lowerEnd m ≤ n ∧ n ≤ upperEnd m := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨96, le_rfl, le_rfl, by decide⟩
  | succ n hn ih =>
    obtain ⟨m,hm,hl,hr⟩ := ih
    by_cases h : n+1 ≤ upperEnd m
    · exact ⟨m,hm,by omega,h⟩
    have he : n = upperEnd m := by omega
    have hjoin : lowerEnd (m+1) ≤ upperEnd m := by
      unfold lowerEnd upperEnd
      rw [pow_succ]
      have hab : 2*(3125*(25*(m+1)+1500)) ≤ 3125*(650*m+2500) := by omega
      calc
        _ = (2*(3125*(25*(m+1)+1500)))*2^m := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ hab
    have hinc : upperEnd m < upperEnd (m+1) := by
      unfold upperEnd
      rw [pow_succ]
      have hp : 0 < (2:ℕ)^m := by positivity
      have hmul := Nat.mul_lt_mul_of_pos_right
        (show 3125*(650*m+2500) < 2*(3125*(650*(m+1)+2500)) by omega) hp
      calc
        _ < (2*(3125*(650*(m+1)+2500)))*2^m := hmul
        _ = _ := by ring
    exact ⟨m+1,by omega,by omega,by omega⟩

private lemma add_key {m lo hi : ℕ} {pool : Finset (ℕ × ℕ)} (p : ℕ × ℕ)
    (hp : p ∉ pool) (hvalid : Allowed m p) (hwidth : high m p+lo ≤ hi+1)
    (base : ∀ n, lo ≤ n → n ≤ hi → Coded m n pool) :
    ∀ n, lo ≤ n → n ≤ hi+high m p → Coded m n (insert p pool) := by
  intro n hl hr
  by_cases h : n ≤ hi
  · obtain ⟨ys,hs,t,ht,ha,hn⟩ := base n hl h
    exact ⟨ys,hs,t,ht.trans (Finset.subset_insert _ _),ha,hn⟩
  · obtain ⟨ys,hs,t,ht,ha,hn⟩ := base (n-high m p) (by omega) (by omega)
    refine ⟨ys,hs,insert p t,Finset.insert_subset_insert _ ht,?_,?_⟩
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl|hq
      · exact hvalid
      · exact ha q hq
    · rw [Finset.sum_insert (fun h => hp (ht h))]; omega

private lemma add_pool {m lo hi : ℕ} {pool : Finset (ℕ × ℕ)} (extra : Finset (ℕ × ℕ))
    (hdis : Disjoint extra pool) (valid : ∀ p ∈ extra, Allowed m p)
    (width : ∀ p ∈ extra, high m p+lo ≤ hi+1)
    (base : ∀ n, lo ≤ n → n ≤ hi → Coded m n pool) :
    ∀ n, lo ≤ n → n ≤ hi+∑ p ∈ extra, high m p → Coded m n (pool ∪ extra) := by
  induction extra using Finset.induction_on with
  | empty => simpa using base
  | @insert p s hp ih =>
    have hs : s ⊆ insert p s := Finset.subset_insert _ _
    have hh := ih (hdis.mono_left hs) (fun q h => valid q (hs h)) (fun q h => width q (hs h))
    have fresh : p ∉ pool ∪ s := by
      simp only [Finset.mem_union, not_or]
      exact ⟨Finset.disjoint_left.mp hdis (Finset.mem_insert_self _ _),hp⟩
    have hw := width p (Finset.mem_insert_self _ _)
    have hg := add_key p fresh (valid p (Finset.mem_insert_self _ _))
      (show high m p+lo ≤ (hi+∑ q ∈ s,high m q)+1 by omega) hh
    simpa [Finset.union_insert,Finset.sum_insert hp,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hg

private lemma last_exponent {m a : ℕ} (ha : a < m) (ht : 2^m ≤ 2^a*5) :
    exponent5 m a = 1 := by
  have hi : exponent5 m a ≤ 1 := Nat.find_min' (reaches m a) (by simpa using ht : 2^m ≤ 2^a*5^1)
  have ne : exponent5 m a ≠ 0 := by
    intro he
    have h := (unit_bounds ha).1
    have bad : (2:ℕ)^a < 2^m := Nat.pow_lt_pow_right (by decide) ha
    simp [unitCoeff,he] at h; omega
  omega

private lemma last_two (m : ℕ) (hm : 2 ≤ m) :
    4*high m (m-2,4) = 3125*3125*2^m+4 ∧
    2*high m (m-1,4) = 3125*3125*2^m+2 := by
  have h2 : (2:ℕ)^m = 2^(m-2)*4 := by
    conv_lhs => rw [show m = (m-2)+2 by omega,pow_add]
    norm_num
  have h1 : (2:ℕ)^m = 2^(m-1)*2 := by
    conv_lhs => rw [show m = (m-1)+1 by omega,pow_add]
    norm_num
  have e2 := last_exponent (show m-2 < m by omega) (show 2^m ≤ 2^(m-2)*5 by omega)
  have e1 := last_exponent (show m-1 < m by omega) (show 2^m ≤ 2^(m-1)*5 by omega)
  constructor
  · simp only [high,unitCoeff,e2,pow_one,h2]; ring
  · simp only [high,unitCoeff,e1,pow_one,h1]; ring

theorem scale_covered (m n : ℕ) (hm : 96 ≤ m) (hl : lowerEnd m ≤ n) (hu : n ≤ upperEnd m) :
    Represents n := by
  let lo := lowerEnd m
  let hi := 3125*(25*m+2500)*2^m
  let p : ℕ × ℕ := (m-2,4)
  let q : ℕ × ℕ := (m-1,4)
  let rem := graph 0 (m-2) (fun _ => 4)
  have hw : hi = lo+3125000*2^m := by dsimp [lo,hi,lowerEnd]; ring
  have hpx : 4*high m p = 3125*3125*2^m+4 := (last_two m (by omega)).1
  have hqx : 2*high m q = 3125*3125*2^m+2 := (last_two m (by omega)).2
  have hpc : p ∉ corePool m := by simp [p,corePool]
  have hqc : q ∉ insert p (corePool m) := by simp [p,q,corePool]; omega
  have hp := add_key p hpc (fine_allowed (show m-2 < m by omega) le_rfl)
    (show high m p + lo ≤ hi+1 by linarith only [hw,hpx]) (core_covered m · hm)
  have hq := add_key q hqc (fine_allowed (show m-1 < m by omega) le_rfl)
    (show high m q + lo ≤ hi+high m p+1 by linarith only [hw,hpx,hqx]) hp
  have hsep : Disjoint rem (insert q (insert p (corePool m))) := by
    rw [Finset.disjoint_left]
    intro x hx
    obtain ⟨a,ha,rfl⟩ := mem_graph.mp hx
    simp [p,q,corePool]; omega
  have hr (x) (hx : x ∈ rem) : Allowed m x := by
    obtain ⟨a,ha,rfl⟩ := mem_graph.mp hx
    simp only [zero_add]
    exact fine_allowed (by omega) le_rfl
  have width (x) (hx : x ∈ rem) : high m x+lo ≤ hi+high m p+high m q+1 := by
    have hmax := (hr x hx).2
    change 3125*(unitCoeff m x.1*5^x.2)+1+lo ≤ _
    linarith only [hmax,hw,hpx,hqx]
  have rlo (x) (hx : x ∈ rem) : 1953125*2^m ≤ high m x := by
    obtain ⟨a,ha,rfl⟩ := mem_graph.mp hx
    have hmin := (unit_bounds (show a < m by omega)).1
    simp only [high,zero_add]
    norm_num
    omega
  have htotal := Finset.sum_le_sum rlo
  have card : rem.card = m-2 := graph_card .. 
  simp only [Finset.sum_const,card,smul_eq_mul] at htotal
  have hcover : upperEnd m ≤ hi+high m p+high m q+∑ x ∈ rem,high m x := by
    have eq : m = (m-2)+2 := by omega
    have hmul := congrArg (fun k : ℕ => k*(1953125*2^m)) eq
    dsimp [upperEnd,hi]
    nlinarith
  exact decode hm (add_pool rem hsep hr width hq n hl (hu.trans hcover))

end Sun3592

theorem OMA.solution : type_of% @OMA.S_oeis_a003592.main := by
  intro n hn h1 h4 h12
  change Sun3592.Represents n
  by_cases h : n ≤ Sun3592.lowerEnd 96
  · exact Sun3592.finite_prefix n h hn h1 h4 h12
  · obtain ⟨m, hm, hl, hu⟩ := Sun3592.scale_exists (Nat.le_of_lt (Nat.lt_of_not_ge h))
    exact Sun3592.scale_covered m n hm hl hu
