import FormalConjectures.OEIS.«153330»

-- Reduction OeisA153330.conjecture3.R1 of Collatz step differences — conjecture3
-- Credit: @mbilenko03

/-!
# Collatz step differences: a 5x+8y law from a uniform bound on the Collatz ratio

For a terminating `n` with `k` steps, `U` odd steps and `E = k - U` halvings, telescoping the
Collatz map gives `1 = n * 3^U / 2^E * P(n)` with `P(n) = ∏ (1 + 1/(3x))` over the odd iterates
`x ≠ 1`. So `P(n) = 2^E / (3^U * n) ≥ 1` always. If moreover `P(m) < 4/3` for every `m`, then
for `n ≥ 8` the ratio `3^(U'-U) / 2^(E'-E)` (primes for `n+1`) lies strictly between `2/3` and
`4/3`, and every integer pair `(du, de)` with that property has `du + de` equal to `1`, `3`, `6`
or of the form `±(5x+8y)`. Since `a(n) = du + de`, this gives conjecture 3 (the cases `n < 8`
are computed directly).

* `H1` (elementary, a finite check): the arithmetic statement about `(du, de)` above, phrased
  with the four natural-number inequalities that the two trajectories provide.
* `H2` (open core): the uniform bound `3 * 2^E < 4 * 3^U * n`, i.e. `P(n) < 4/3`, for every
  terminating `n ≥ 1`. Numerically the supremum of `P(n)` for `n ≤ 10^8` is about `1.2531`
  (attained at `n = 993`), well below `4/3`.

`main` proves the invariant `3^U * n ≤ 2^E * T^k(n)` by induction, the small cases by
computation, and assembles the rest.
-/

namespace OMA.R_OeisA153330_conjecture3_R1

open OeisA153330

/-- Elementary: if the trajectories of `n ≥ 8` and `n + 1` have `a, c` odd steps and `b, d`
halvings with `1 ≤ 2^b / (3^a n) < 4/3` and `1 ≤ 2^d / (3^c (n+1)) < 4/3`, then the step
difference `(c + d) - (a + b)` is `1`, `3`, `6`, or has absolute value `5x + 8y`. -/
def H1 : Prop :=
  ∀ a b c d n : ℕ, 8 ≤ n → 3 ^ a * n ≤ 2 ^ b → 3 * 2 ^ b < 4 * (3 ^ a * n) →
    3 ^ c * (n + 1) ≤ 2 ^ d → 3 * 2 ^ d < 4 * (3 ^ c * (n + 1)) →
    ((c + d : ℤ) - (a + b) = 1 ∨ (c + d : ℤ) - (a + b) = 3 ∨ (c + d : ℤ) - (a + b) = 6 ∨
      ∃ x y : ℕ, ((c + d : ℤ) - (a + b)).natAbs = 5 * x + 8 * y)

/-- Open core: for every terminating `n ≥ 1` with `k` Collatz steps of which `U` are odd,
`3 * 2^(k - U) < 4 * 3^U * n`, i.e. the Collatz ratio `2^E / (3^U n)` stays below `4/3`. -/
def H2 : Prop :=
  ∀ n k : ℕ, 0 < n → collatzSteps n = some k →
    3 * 2 ^ (k - ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 1)).card) <
      4 * (3 ^ ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 1)).card * n)

lemma iter_eq_one_of_steps {n k : ℕ} (h : collatzSteps n = some k) :
    collatzStep^[k] n = 1 := by
  unfold collatzSteps at h
  split_ifs at h with h0 hex
  · obtain rfl := Option.some.inj h
    exact Nat.sInf_mem hex

lemma card_succ (n k : ℕ) :
    ((Finset.range (k + 1)).filter (fun i => collatzStep^[i] n % 2 = 1)).card =
      ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 1)).card +
        (if collatzStep^[k] n % 2 = 1 then 1 else 0) := by
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma ratio_inv (n : ℕ) : ∀ k : ℕ,
    ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 1)).card ≤ k ∧
    3 ^ ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 1)).card * n ≤
      2 ^ (k - ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 1)).card) *
        collatzStep^[k] n := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨hle, hineq⟩ := ih
    rw [card_succ, Function.iterate_succ_apply']
    generalize ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 1)).card = u at hle hineq ⊢
    generalize collatzStep^[k] n = x at hineq ⊢
    by_cases hx : x % 2 = 1
    · have h0 : ¬ x % 2 = 0 := by omega
      rw [if_pos hx]
      simp only [collatzStep, if_neg h0]
      refine ⟨by omega, ?_⟩
      have hk : k + 1 - (u + 1) = k - u := by omega
      rw [hk, pow_succ]
      have hp : 0 < 2 ^ (k - u) := pow_pos (by norm_num) _
      calc 3 ^ u * 3 * n = 3 * (3 ^ u * n) := by ring
        _ ≤ 3 * (2 ^ (k - u) * x) := Nat.mul_le_mul_left 3 hineq
        _ ≤ 2 ^ (k - u) * (3 * x + 1) := by nlinarith
    · have h0 : x % 2 = 0 := by omega
      rw [if_neg hx, add_zero]
      simp only [collatzStep, h0, if_true]
      refine ⟨by omega, ?_⟩
      have hk : k + 1 - u = (k - u) + 1 := by omega
      rw [hk, pow_succ]
      have hd : 2 * (x / 2) = x := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h0)
      calc 3 ^ u * n ≤ 2 ^ (k - u) * x := hineq
        _ = 2 ^ (k - u) * 2 * (x / 2) := by rw [mul_assoc, hd]

lemma steps_eq {n k : ℕ} (hn : n ≠ 0) (h : IsLeast {j : ℕ | (collatzStep^[j]) n = 1} k) :
    collatzSteps n = some k := by
  have hex : ∃ j, (collatzStep^[j]) n = 1 := ⟨k, h.1⟩
  rw [collatzSteps, if_neg hn, if_pos hex, h.csInf_eq]

lemma a_5 : a 5 = some 3 := by
  have h5 : IsLeast {k : ℕ | (collatzStep^[k]) 5 = 1} 5 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  have h6 : IsLeast {k : ℕ | (collatzStep^[k]) 6 = 1} 8 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  rw [a, if_neg (by omega), steps_eq (by omega) h6, steps_eq (by omega) h5]; rfl

lemma a_6 : a 6 = some 8 := by
  have h6 : IsLeast {k : ℕ | (collatzStep^[k]) 6 = 1} 8 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  have h7 : IsLeast {k : ℕ | (collatzStep^[k]) 7 = 1} 16 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  rw [a, if_neg (by omega), steps_eq (by omega) h7, steps_eq (by omega) h6]; rfl

lemma a_7 : a 7 = some (-13) := by
  have h7 : IsLeast {k : ℕ | (collatzStep^[k]) 7 = 1} 16 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  have h8 : IsLeast {k : ℕ | (collatzStep^[k]) 8 = 1} 3 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  rw [a, if_neg (by omega), steps_eq (by omega) h8, steps_eq (by omega) h7]; rfl

theorem main : H1 → H2 → type_of% @OeisA153330.conjecture3 := by
  intro h1 h2 n v hn ha hv
  by_cases hsmall : n < 8
  · interval_cases n
    · rw [a_1] at ha; cases ha; exact absurd rfl hv.1
    · rw [a_2] at ha; cases ha; exact absurd rfl hv.2.2
    · rw [a_3] at ha; cases ha; exact ⟨1, 0, rfl⟩
    · rw [a_4] at ha; cases ha; exact absurd rfl hv.2.1
    · rw [a_5] at ha; cases ha; exact absurd rfl hv.2.1
    · rw [a_6] at ha; cases ha; exact ⟨0, 1, rfl⟩
    · rw [a_7] at ha; cases ha; exact ⟨1, 1, rfl⟩
  replace hsmall : 8 ≤ n := by omega
  unfold a at ha
  rw [if_neg (by omega)] at ha
  rcases hs2 : collatzSteps (n + 1) with _ | s2 <;> rcases hs1 : collatzSteps n with _ | s1 <;>
    rw [hs2, hs1] at ha <;> simp at ha
  obtain ⟨hle1, hinv1⟩ := ratio_inv n s1
  obtain ⟨hle2, hinv2⟩ := ratio_inv (n + 1) s2
  rw [iter_eq_one_of_steps hs1, mul_one] at hinv1
  rw [iter_eq_one_of_steps hs2, mul_one] at hinv2
  have hb1 := h2 n s1 hn hs1
  have hb2 := h2 (n + 1) s2 (by omega) hs2
  set u1 := ((Finset.range s1).filter (fun i => collatzStep^[i] n % 2 = 1)).card with hu1
  set u2 := ((Finset.range s2).filter (fun i => collatzStep^[i] (n + 1) % 2 = 1)).card with hu2
  have key := h1 u1 (s1 - u1) u2 (s2 - u2) n hsmall hinv1 hb1 hinv2 hb2
  have hval : ((u2 : ℤ) + ((s2 - u2 : ℕ) : ℤ)) - ((u1 : ℤ) + ((s1 - u1 : ℕ) : ℤ)) = v := by
    rw [Nat.cast_sub hle1, Nat.cast_sub hle2, ← ha]; ring
  rw [hval] at key
  rcases key with h | h | h | h
  · exact absurd h hv.1
  · exact absurd h hv.2.1
  · exact absurd h hv.2.2
  · exact h

end OMA.R_OeisA153330_conjecture3_R1
