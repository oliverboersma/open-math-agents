import FormalConjectures.OEIS.«212334»

/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Adapted from EliaSupernova's formal proof, licensed under Apache-2.0:
https://github.com/EliaSupernova/oeis-a212334-lean/blob/a963f13619df64d49fc0c39e73eedbd444c59d31/Solution.lean
The upstream proof was produced with AI assistance. This port uses the catalog's
definition directly, omits repeated examples, and places the helpers in their
own namespace. Port for Left to Solve: @rleshner.
-/

namespace OMA.A212334

/-- The `k`-th summand $\binom{n}{k} \binom{n-1}{k} \binom{n+k-1}{k}^2$ of `a n`. -/
def summand (n k : ℕ) : ℕ :=
  n.choose k * (n - 1).choose k * (n + k - 1).choose k ^ 2

/-- The summands of `a n` satisfy a first-order recurrence in `k`. -/
lemma summand_succ (n k : ℕ) (hn : 0 < n) :
    (k + 1) ^ 4 * summand n (k + 1) = (n - k) * (n - 1 - k) * (n + k) ^ 2 * summand n k := by
  have h1 : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) := Nat.choose_succ_right_eq n k
  have h2 : (n - 1).choose (k + 1) * (k + 1) = (n - 1).choose k * (n - 1 - k) :=
    Nat.choose_succ_right_eq (n - 1) k
  have h3 : (n + k) * (n + k - 1).choose k = (n + k).choose (k + 1) * (k + 1) := by
    have h := Nat.add_one_mul_choose_eq (n + k - 1) k
    rwa [Nat.sub_add_cancel (by omega)] at h
  unfold summand
  rw [show n + (k + 1) - 1 = n + k by omega]
  calc (k + 1) ^ 4 * (n.choose (k + 1) * (n - 1).choose (k + 1) * (n + k).choose (k + 1) ^ 2)
      = (n.choose (k + 1) * (k + 1)) * ((n - 1).choose (k + 1) * (k + 1)) *
          ((n + k).choose (k + 1) * (k + 1)) ^ 2 := by ring
    _ = _ := by rw [h1, h2, ← h3]; ring

/-- In `ZMod (p ^ 5)` the fifth power of `p` vanishes. -/
lemma natCast_self_pow_five (p : ℕ) : (p : ZMod (p ^ 5)) ^ 5 = 0 := by
  rw [← Nat.cast_pow]
  exact ZMod.natCast_self _

/-- For a prime `p`, every `0 < k < p` is coprime to `p ^ 5`. -/
lemma coprime_pow_five {p : ℕ} (hp : p.Prime) {k : ℕ} (hk1 : 1 ≤ k) (hkp : k < p) :
    k.Coprime (p ^ 5) :=
  Nat.Coprime.pow_right 5 (Nat.coprime_of_lt_prime (by omega) hkp hp).symm

/-- For a prime `p` and `0 < k < p`, we have
$k^4 \binom{p}{k} \binom{p-1}{k} \binom{p+k-1}{k}^2 \equiv p^4 - p^3 k \pmod{p^5}$. -/
lemma pow_four_mul_summand {p : ℕ} (hp : p.Prime) {k : ℕ} (hk1 : 1 ≤ k) (hkp : k < p) :
    (k : ZMod (p ^ 5)) ^ 4 * (summand p k : ZMod (p ^ 5)) =
      (p : ZMod (p ^ 5)) ^ 4 - (p : ZMod (p ^ 5)) ^ 3 * k := by
  have hP := natCast_self_pow_five p
  induction k, hk1 using Nat.le_induction with
  | base =>
    have h : summand p 1 = p * (p - 1) * p ^ 2 := by simp [summand]
    rw [h]
    push_cast [Nat.cast_sub hp.one_le]
    ring
  | succ k hk1 ih =>
    have ih := ih (by omega)
    have hrec := congrArg (Nat.cast : ℕ → ZMod (p ^ 5)) (summand_succ p k hp.pos)
    rw [Nat.sub_sub] at hrec
    push_cast [Nat.cast_sub (show k ≤ p by omega), Nat.cast_sub (show 1 + k ≤ p by omega)] at hrec
    refine ((ZMod.isUnit_iff_coprime k (p ^ 5)).2 (coprime_pow_five hp hk1
      (by omega))).pow 4 |>.mul_left_cancel ?_
    push_cast
    linear_combination (k : ZMod (p ^ 5)) ^ 4 * hrec +
      ((p : ZMod (p ^ 5)) - k) * (p - (1 + k)) * (p + k) ^ 2 * ih +
      ((p : ZMod (p ^ 5)) ^ 3 - (k + 1) * p ^ 2 - 2 * k ^ 2 * p + 2 * k ^ 2 * (k + 1)) * hP

/-- For a prime `p` and `0 < k < p`, the `k`-th and `(p - k)`-th summands of `a p` add up to
$5 p^4 / k^4$ modulo $p^5$. -/
lemma pow_four_mul_summand_add {p : ℕ} (hp : p.Prime) {k : ℕ} (hk1 : 1 ≤ k) (hkp : k < p) :
    (k : ZMod (p ^ 5)) ^ 4 * ((summand p k : ZMod (p ^ 5)) + summand p (p - k)) =
      5 * (p : ZMod (p ^ 5)) ^ 4 := by
  have hP := natCast_self_pow_five p
  have h1 := pow_four_mul_summand hp hk1 hkp
  have h2 := pow_four_mul_summand hp (show 1 ≤ p - k by omega) (show p - k < p by omega)
  have hu := (ZMod.isUnit_iff_coprime (p - k) (p ^ 5)).2
    (coprime_pow_five hp (show 1 ≤ p - k by omega) (show p - k < p by omega))
  rw [Nat.cast_sub hkp.le] at h2 hu
  refine (hu.pow 4).mul_left_cancel ?_
  linear_combination ((p : ZMod (p ^ 5)) - k) ^ 4 * h1 + (k : ZMod (p ^ 5)) ^ 4 * h2 +
    (-4 * (p : ZMod (p ^ 5)) ^ 3 + 15 * p ^ 2 * k - 20 * p * k ^ 2 + 10 * k ^ 3) * hP

/-- An element of `ZMod (p ^ 5)` that vanishes modulo `p` is killed by `p ^ 4`. -/
lemma pow_four_mul_eq_zero {p : ℕ} (hp : p.Prime) (x : ZMod (p ^ 5))
    (hx : ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p) x = 0) :
    (p : ZMod (p ^ 5)) ^ 4 * x = 0 := by
  have : NeZero (p ^ 5) := ⟨pow_ne_zero 5 hp.ne_zero⟩
  have h : ((x.val : ℕ) : ZMod p) = 0 := by
    rw [← hx, ← map_natCast (ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p)),
      ZMod.natCast_zmod_val]
  obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff _ _).1 h
  rw [← ZMod.natCast_zmod_val x, hm]
  push_cast
  linear_combination (m : ZMod (p ^ 5)) * natCast_self_pow_five p

/-- For a prime `p ≥ 7`, we have $\sum_{k=1}^{p-1} k^{-4} \equiv 0 \pmod{p}$. -/
lemma sum_inv_pow_four {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 4 = 0 := by
  have := Fact.mk hp
  have h1 : ∑ x : ZMod p, x⁻¹ ^ 4 = 0 := by
    rw [← FiniteField.sum_pow_lt_card_sub_one (ZMod p) 4 (by rw [ZMod.card]; omega)]
    exact Equiv.sum_comp (Equiv.inv (ZMod p)) (fun x => x ^ 4)
  have h2 : ∑ k ∈ Finset.range p, ((k : ZMod p)⁻¹) ^ 4 = ∑ x : ZMod p, x⁻¹ ^ 4 :=
    Finset.sum_nbij' (fun k => (k : ZMod p)) (fun x => x.val) (by simp)
      (fun x _ => Finset.mem_range.2 (ZMod.val_lt x))
      (fun k hk => ZMod.val_cast_of_lt (Finset.mem_range.1 hk))
      (fun x _ => ZMod.natCast_zmod_val x) (fun _ _ => rfl)
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hp.pos] at h2
  rw [h1] at h2
  simpa using h2

/-- For a prime `p ≥ 5`, the summands of `a p` with `0 < k < p` add up to zero modulo $p^5$. -/
lemma sum_summand {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∑ k ∈ Finset.Ico 1 p, (summand p k : ZMod (p ^ 5)) = 0 := by
  have := Fact.mk hp
  have hP := natCast_self_pow_five p
  have h2 : IsUnit (2 : ZMod (p ^ 5)) := by
    simpa using (ZMod.isUnit_iff_coprime 2 (p ^ 5)).2
      (Nat.Coprime.pow_right 5 ((Nat.coprime_primes Nat.prime_two hp).2 (by omega)))
  have hrefl : ∑ k ∈ Finset.Ico 1 p, (summand p (p - k) : ZMod (p ^ 5)) =
      ∑ k ∈ Finset.Ico 1 p, (summand p k : ZMod (p ^ 5)) := by
    simpa using Finset.sum_Ico_reflect (fun k => (summand p k : ZMod (p ^ 5))) 1 (Nat.le_succ p)
  have hinv : ∀ k ∈ Finset.Ico 1 p, (k : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹ = 1 := by
    intro k hk
    obtain ⟨hk1, hkp⟩ := Finset.mem_Ico.1 hk
    exact ZMod.coe_mul_inv_eq_one k (coprime_pow_five hp hk1 hkp)
  have hpair : ∀ k ∈ Finset.Ico 1 p, (summand p k : ZMod (p ^ 5)) + summand p (p - k) =
      5 * (p : ZMod (p ^ 5)) ^ 4 * ((k : ZMod (p ^ 5))⁻¹) ^ 4 := by
    intro k hk
    obtain ⟨hk1, hkp⟩ := Finset.mem_Ico.1 hk
    have hinv4 : (k : ZMod (p ^ 5)) ^ 4 * ((k : ZMod (p ^ 5))⁻¹) ^ 4 = 1 := by
      rw [← mul_pow, hinv k hk, one_pow]
    linear_combination ((k : ZMod (p ^ 5))⁻¹) ^ 4 * pow_four_mul_summand_add hp hk1 hkp -
      ((summand p k : ZMod (p ^ 5)) + summand p (p - k)) * hinv4
  have hsum : 2 * ∑ k ∈ Finset.Ico 1 p, (summand p k : ZMod (p ^ 5)) =
      5 * (p : ZMod (p ^ 5)) ^ 4 * ∑ k ∈ Finset.Ico 1 p, ((k : ZMod (p ^ 5))⁻¹) ^ 4 := by
    rw [two_mul]
    nth_rw 2 [← hrefl]
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hpair, Finset.mul_sum]
  have hzero : 5 * (p : ZMod (p ^ 5)) ^ 4 *
      ∑ k ∈ Finset.Ico 1 p, ((k : ZMod (p ^ 5))⁻¹) ^ 4 = 0 := by
    obtain h | hp7 : p = 5 ∨ 7 ≤ p := by
      by_contra hcon
      obtain rfl : p = 6 := by omega
      norm_num at hp
    · have h5 : (5 : ZMod (p ^ 5)) = (p : ZMod (p ^ 5)) := by subst h; simp
      rw [h5]
      linear_combination (∑ k ∈ Finset.Ico 1 p, ((k : ZMod (p ^ 5))⁻¹) ^ 4) * hP
    · rw [mul_assoc, pow_four_mul_eq_zero hp, mul_zero]
      have hφ : ∀ k ∈ Finset.Ico 1 p,
          ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p)
            (((k : ZMod (p ^ 5))⁻¹) ^ 4) = ((k : ZMod p)⁻¹) ^ 4 := by
        intro k hk
        have h := congrArg (ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p))
          (hinv k hk)
        rw [map_mul, map_natCast, map_one] at h
        rw [map_pow, eq_inv_of_mul_eq_one_right h]
      rw [map_sum, Finset.sum_congr rfl hφ, sum_inv_pow_four hp hp7]
  exact h2.mul_left_cancel (by rw [hsum, hzero, mul_zero])

end OMA.A212334

open OMA.A212334 OeisA212334 in
theorem OMA.solution : type_of% @OeisA212334.conjecture_1 := by
  intro p hp hp5
  have h1 : 1 < p ^ 5 := Nat.one_lt_pow (by norm_num) hp.one_lt
  have ha : a p = 1 + ∑ k ∈ Finset.Ico 1 p, summand p k := by
    rw [a, if_neg hp.ne_zero, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hp.pos]
    simp [summand]
  have h := (ZMod.natCast_eq_natCast_iff' (a p) 1 (p ^ 5)).1 (by
    rw [ha]
    push_cast
    rw [sum_summand hp hp5, add_zero])
  rwa [Nat.mod_eq_of_lt h1] at h
