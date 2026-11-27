import OMAReductions.R_Erdos20_erdos_20_R1

/-!
# A diagonal criterion for the word sunflower bound

A base that works for families of length `N` over `Fin N` at arbitrarily large
values of `N` works for every length and alphabet, with the same base. A Cartesian
power of a counterexample eventually overcomes the cost of padding the last block.
-/

-- Reduction Erdos20.erdos_20.R1.H2.R2 of step Erdos20.erdos_20.R1.H2
-- Credit: @ubuwaits

namespace OMA.R_Erdos20_erdos_20_R1_H2_R2

/-- The diagonal estimate at an unbounded sequence of lengths. -/
def H1 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ D : ℕ, 1 ≤ D ∧ ∀ L : ℕ, ∃ N : ℕ, L ≤ N ∧
    ∀ V : Finset (Fin N → Fin N),
      (∀ w : Fin r → Fin N → Fin N, (∀ i, w i ∈ V) →
        (∀ j, (∀ a b, w a j = w b j) ∨ Function.Injective (fun i => w i j)) →
        ∀ a b, w a = w b) → V.card ≤ D ^ N

/-- Pack a Cartesian power into a diagonal word space, preserving sunflower-freeness. -/
def H2 : Prop :=
  ∀ (r n m t N : ℕ), 0 < N → m ≤ N → t * n ≤ N →
    ∀ W : Finset (Fin n → Fin m),
      (∀ w : Fin r → Fin n → Fin m, (∀ i, w i ∈ W) →
        (∀ j, (∀ a b, w a j = w b j) ∨ Function.Injective (fun i => w i j)) →
        ∀ a b, w a = w b) →
      ∃ V : Finset (Fin N → Fin N), W.card ^ t ≤ V.card ∧
        ∀ v : Fin r → Fin N → Fin N, (∀ i, v i ∈ V) →
          (∀ j, (∀ a b, v a j = v b j) ∨ Function.Injective (fun i => v i j)) →
          ∀ a b, v a = v b

lemma first_two_terms (a t : ℕ) : a ^ t * (a + t) ≤ a * (a + 1) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    calc
      a ^ (t + 1) * (a + (t + 1)) ≤ (a ^ t * (a + t)) * (a + 1) := by
        rw [pow_succ]
        nlinarith [Nat.zero_le (a ^ t * t)]
      _ ≤ (a * (a + 1) ^ t) * (a + 1) := Nat.mul_le_mul_right _ ih
      _ = a * (a + 1) ^ (t + 1) := by rw [pow_succ, Nat.mul_assoc]

theorem main : H1 → H2 → OMA.R_Erdos20_erdos_20_R1.H2 := by
  intro diagonal pack r hr
  obtain ⟨D, hD, scales⟩ := diagonal r hr
  refine ⟨D, hD, ?_⟩
  intro n m W hW
  cases n with
  | zero => simpa using Finset.card_le_one_of_subsingleton W
  | succ n =>
    let k := n + 1
    have hk : 0 < k := Nat.succ_pos _
    let a := D ^ k
    have ha : 0 < a := pow_pos hD _
    obtain ⟨N, hN, bound⟩ := scales (max m ((a * a + 1) * k))
    have hscale := (le_max_right m ((a * a + 1) * k)).trans hN
    let t := N / k
    have ht : a * a + 1 ≤ t := (Nat.le_div_iff_mul_le hk).mpr hscale
    have hNpos : 0 < N := (Nat.mul_pos (Nat.succ_pos _) hk).trans_le hscale
    obtain ⟨V, hcard, hfree⟩ := pack r k m t N hNpos
      ((le_max_left m _).trans hN) (Nat.div_mul_le_self N k) W hW
    have hlen : N ≤ k * (t + 1) := by
      have hrem := Nat.mod_lt N hk
      have hsplit : N % k + k * t = N := Nat.mod_add_div N k
      rw [Nat.mul_succ]
      omega
    have hupper : W.card ^ t ≤ a ^ t * a := calc
      W.card ^ t ≤ V.card := hcard
      _ ≤ D ^ N := bound V hfree
      _ ≤ D ^ (k * (t + 1)) := Nat.pow_le_pow_right hD hlen
      _ = a ^ t * a := by rw [pow_mul, pow_succ]
    change W.card ≤ a
    by_contra! hbad
    have lower := first_two_terms a t
    have hpow := Nat.pow_le_pow_left hbad t
    have hcancel : a ^ t * (a + t) ≤ a ^ t * (a * a) := calc
      a ^ t * (a + t) ≤ a * (a + 1) ^ t := lower
      _ ≤ a * W.card ^ t := Nat.mul_le_mul_left a hpow
      _ ≤ a * (a ^ t * a) := Nat.mul_le_mul_left a hupper
      _ = a ^ t * (a * a) := by ac_rfl
    have := Nat.le_of_mul_le_mul_left hcancel (pow_pos ha t)
    omega

end OMA.R_Erdos20_erdos_20_R1_H2_R2
