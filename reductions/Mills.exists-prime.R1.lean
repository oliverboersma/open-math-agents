import FormalConjectures.Wikipedia.Mills

-- Reduction Mills.exists-prime.R1 of Mills' theorem
-- Credit: @ptc-prover-bot
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Mills' theorem from primes in short intervals

Following W. H. Mills, *A prime-representing function*, Bull. AMS 53 (1947), 604:
* `H1` (Hoheisel–Ingham): every interval `(x, x + C x^θ]` contains a prime, for some `θ < 2/3`
  (Ingham 1937 gives `θ = 5/8`). Since `3θ < 2`, for large `q` it gives a prime `p` with
  `q³ ≤ p` and `p + 1 < (q + 1)³`. This is the only non-elementary input. (The same statement is
  `H1` of `Erdos683.erdos_683.variant.erdos_log.R1`.)
* `H2` (Mills' nested intervals): if `q₀, q₁, …` satisfy `qₙ³ ≤ qₙ₊₁` and `qₙ₊₁ + 1 < (qₙ + 1)³`,
  then `qₙ^(3^-(n+1)) ↑` and `(qₙ + 1)^(3^-(n+1)) ↓` squeeze a real `A > 1` with
  `⌊A^(3^(n+1))⌋ = qₙ` for every `n`.

`main` starts from a prime `q₀` above the threshold of `H1`, builds the chain of primes with `H1`,
and applies `H2`.
-/

namespace OMA.R_Mills_exists_prime_R1

open Real Filter

/-- Hoheisel–Ingham: primes in `(x, x + C x^θ]` for some `θ < 2/3` (Ingham 1937: `θ = 5/8`). -/
def H1 : Prop :=
  ∃ θ : ℝ, θ < 2 / 3 ∧ ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + C * (x : ℝ) ^ θ

/-- Mills' nested-interval lemma. -/
def H2 : Prop :=
  ∀ q : ℕ → ℕ, (∀ n, 2 ≤ q n) → (∀ n, q n ^ 3 ≤ q (n + 1)) → (∀ n, q (n + 1) + 1 < (q n + 1) ^ 3) →
    ∃ A : ℝ, 1 < A ∧ ∀ n : ℕ, ⌊A ^ (3 ^ (n + 1))⌋₊ = q n

/-- From `H1`: above some `Q₀`, every `q` has a prime `p` with `q³ ≤ p` and `p + 1 < (q + 1)³`. -/
lemma next_prime (h1 : H1) : ∃ Q₀ : ℕ, 2 ≤ Q₀ ∧ ∀ q : ℕ, Q₀ ≤ q →
    ∃ p : ℕ, p.Prime ∧ q ^ 3 ≤ p ∧ p + 1 < (q + 1) ^ 3 := by
  obtain ⟨θ, hθ, C, hC⟩ := h1
  set θ' := max θ 0 with hθ'
  set C' := max C 0 with hC'
  have he : 0 < 2 - 3 * θ' := by
    have : θ' < 2 / 3 := max_lt hθ (by norm_num)
    linarith
  obtain ⟨Q₀, hQ₀⟩ := exists_nat_ge ((C' + 1) ^ (1 / (2 - 3 * θ')))
  refine ⟨max Q₀ 2, le_max_right _ _, fun q hq => ?_⟩
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hq3 : 2 ≤ q ^ 3 - 1 := by
    have : 8 ≤ q ^ 3 := by nlinarith [Nat.pow_le_pow_left hq2 3]
    omega
  obtain ⟨p, hp, hlt, hle⟩ := hC (q ^ 3 - 1) hq3
  refine ⟨p, hp, by omega, ?_⟩
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hq0 : (0 : ℝ) < q := by linarith
  have hx1 : (1 : ℝ) ≤ ((q ^ 3 - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ q ^ 3 - 1)
  have hxq : ((q ^ 3 - 1 : ℕ) : ℝ) ≤ (q : ℝ) ^ 3 := by
    have : q ^ 3 - 1 ≤ q ^ 3 := Nat.sub_le _ _
    exact_mod_cast this
  -- x^θ ≤ q^(3θ')
  have hpow : ((q ^ 3 - 1 : ℕ) : ℝ) ^ θ ≤ (q : ℝ) ^ (3 * θ') := by
    calc ((q ^ 3 - 1 : ℕ) : ℝ) ^ θ ≤ ((q ^ 3 - 1 : ℕ) : ℝ) ^ θ' :=
          rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _)
      _ ≤ ((q : ℝ) ^ 3) ^ θ' := rpow_le_rpow (by linarith) hxq (le_max_right _ _)
      _ = (q : ℝ) ^ (3 * θ') := by
          rw [← rpow_natCast, ← rpow_mul hq0.le]; norm_num
  -- C' q^(3θ') ≤ q²
  have hQ : (C' + 1) ^ (1 / (2 - 3 * θ')) ≤ (q : ℝ) := by
    have hQq : Q₀ ≤ q := le_trans (le_max_left _ _) hq
    have : (Q₀ : ℝ) ≤ q := by exact_mod_cast hQq
    exact hQ₀.trans this
  have hCq : C' + 1 ≤ (q : ℝ) ^ (2 - 3 * θ') := by
    have h0 : 0 ≤ (C' + 1) ^ (1 / (2 - 3 * θ')) := rpow_nonneg (by positivity) _
    have := rpow_le_rpow h0 hQ he.le
    rwa [← rpow_mul (by positivity), one_div_mul_cancel he.ne', rpow_one] at this
  have hsplit : (q : ℝ) ^ (2 : ℝ) = (q : ℝ) ^ (3 * θ') * (q : ℝ) ^ (2 - 3 * θ') := by
    rw [← rpow_add hq0]; ring_nf
  have hq2' : (q : ℝ) ^ (2 : ℝ) = (q : ℝ) ^ 2 := by norm_cast
  have hpos : 0 ≤ (q : ℝ) ^ (3 * θ') := rpow_nonneg hq0.le _
  have hmain : C' * (q : ℝ) ^ (3 * θ') ≤ (q : ℝ) ^ 2 := by
    rw [← hq2', hsplit]
    nlinarith [mul_le_mul_of_nonneg_left hCq hpos]
  have hCC : C * ((q ^ 3 - 1 : ℕ) : ℝ) ^ θ ≤ C' * (q : ℝ) ^ (3 * θ') := by
    have h0 : 0 ≤ ((q ^ 3 - 1 : ℕ) : ℝ) ^ θ := rpow_nonneg (by linarith) _
    calc C * ((q ^ 3 - 1 : ℕ) : ℝ) ^ θ ≤ C' * ((q ^ 3 - 1 : ℕ) : ℝ) ^ θ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h0
      _ ≤ C' * (q : ℝ) ^ (3 * θ') := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
  have hpR : (p : ℝ) + 1 < ((q : ℝ) + 1) ^ 3 := by
    have hcast : ((q ^ 3 - 1 : ℕ) : ℝ) = (q : ℝ) ^ 3 - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast] at hle hCC
    have hq2R : (0 : ℝ) < 3 * (q : ℝ) := by linarith
    nlinarith [hmain, hCC]
  exact_mod_cast hpR

theorem main : H1 → H2 → type_of% @Mills.exists' := by
  intro h1 h2
  classical
  obtain ⟨Q₀, hQ2, hnext⟩ := next_prime h1
  obtain ⟨q₀, hq₀le, hq₀p⟩ := Nat.exists_infinite_primes Q₀
  -- the chain, as a recursion on primes ≥ Q₀
  let S := {q : ℕ // q.Prime ∧ Q₀ ≤ q}
  have hstep : ∀ s : S, ∃ t : S, s.1 ^ 3 ≤ t.1 ∧ t.1 + 1 < (s.1 + 1) ^ 3 := by
    rintro ⟨s, hs, hsQ⟩
    obtain ⟨p, hp, h1', h2'⟩ := hnext s hsQ
    have : Q₀ ≤ p := le_trans hsQ (le_trans (Nat.le_self_pow (by norm_num) s) h1')
    exact ⟨⟨p, hp, this⟩, h1', h2'⟩
  choose nxt hnxt using hstep
  let c : ℕ → S := fun n => Nat.rec ⟨q₀, hq₀p, hq₀le⟩ (fun _ s => nxt s) n
  have hc : ∀ n, c (n + 1) = nxt (c n) := fun n => rfl
  obtain ⟨A, hA1, hA⟩ := h2 (fun n => (c n).1) (fun n => le_trans hQ2 (c n).2.2)
    (fun n => by rw [hc]; exact (hnxt (c n)).1) (fun n => by rw [hc]; exact (hnxt (c n)).2)
  refine ⟨A, hA1, fun n => ?_⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (n : ℕ) = m + 1 := ⟨n.natPred, (PNat.natPred_add_one n).symm⟩
  rw [hm, hA m]
  exact (c m).2.1.prime

end OMA.R_Mills_exists_prime_R1
