import OMAStatements.S_mo_280192
import Mathlib

namespace OMA.R_mo_280192_R1

open OMA.S_mo_280192

/-- Exact finite certificate: use the least integer multiple of `2^k` at or above `3^k`. -/
def H1 : Prop := ∀ i : Fin 4095,
  let k := i.val + 2
  let m := (3^k - 1) / 2^k + 1
  3^k + m ≤ 2^k * m

/-- Above the cutoff, it suffices to bound multiples indexed by integers prime to three. -/
def H2 : Prop := ∀ k m : ℕ, 4096 < k → ¬ 3 ∣ m → 3^k ≤ 2^k*m → 3^k + m ≤ 2^k*m

lemma extend_from_first {a b : ℕ} (hb : 0 < b) (ha : 0 < a)
    (first : a + ((a-1)/b+1) ≤ b*((a-1)/b+1))
    {m : ℕ} (above : a ≤ b*m) : a + m ≤ b*m := by
  have hq : (a-1)/b < m := (Nat.div_lt_iff_lt_mul hb).2 (by rw [Nat.mul_comm]; omega)
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (show (a-1)/b+1 ≤ m by omega)
  rw [ht, Nat.mul_add]
  have ht' : t ≤ b*t := by simpa using Nat.mul_le_mul_right t hb
  omega

lemma separation (prefixBound : H1) (tailBound : H2) (k : ℕ) (hk : 2 ≤ k) :
    ∀ m : ℕ, 3^k ≤ 2^k*m → 3^k + m ≤ 2^k*m := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m above
    by_cases small : k ≤ 4096
    · have finite := prefixBound ⟨k-2, by omega⟩
      dsimp only at finite
      rw [Nat.sub_add_cancel hk] at finite
      exact extend_from_first (by positivity) (by positivity) finite above
    by_cases multiple : 3 ∣ m
    · obtain ⟨u, rfl⟩ := multiple
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [pow_succ, pow_succ] at above ⊢
      have prev : 3^j ≤ 2^j * (2*u) := by nlinarith only [above]
      have gap := ih j (by omega) (by omega) (2*u) prev
      nlinarith only [gap, Nat.zero_le u]
    · exact tailBound k m (by omega) multiple above

theorem main : H1 → H2 → type_of% @OMA.S_mo_280192.main := by
  intro prefixBound tailBound k hk
  let q := (3^k - 1) / 2^k
  have bpos : 0 < 2^k := by positivity
  have apos : 0 < 3^k := by positivity
  have below : q * 2^k < 3^k := by
    have h := Nat.div_mul_le_self (3^k-1) (2^k)
    dsimp [q]; omega
  have above : 3^k ≤ 2^k*(q+1) := by
    have h := Nat.lt_mul_div_succ (3^k-1) bpos
    dsimp [q]; omega
  have gap := separation prefixBound tailBound k hk (q+1) above
  have hlow : (3:ℚ)^k + ((q:ℚ)+1) ≤ (2:ℚ)^k*((q:ℚ)+1) := by exact_mod_cast gap
  have hupp : (q:ℚ)*(2:ℚ)^k + 1 ≤ (3:ℚ)^k := by exact_mod_cast (Nat.succ_le_of_lt below)
  have bgt : (1:ℚ) < 2^k := one_lt_pow₀ (by norm_num) (by omega)
  refine ⟨(q:ℤ), ?_, ?_⟩
  · unfold lower
    apply (div_lt_iff₀ (by linarith : (0:ℚ) < 2^k-1)).2
    push_cast
    linarith only [hlow]
  · unfold upper
    apply (le_div_iff₀ (by positivity : (0:ℚ) < 2^k)).2
    push_cast
    linarith only [hupp]

end OMA.R_mo_280192_R1
