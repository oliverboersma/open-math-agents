import Mathlib.Logic.Function.Iterate

/-!
# Connectivity in automata by words of length n-1

Source: https://mathoverflow.net/q/93022 (Mikhail Berlinkov, April 3, 2012).
Lean formalization: @LDJAI with OpenAI Codex.

States and letters of the finite complete deterministic automaton are numbered
without loss of generality. The existence hypothesis and the pairwise condition
using unrestricted positive powers are the ones stated in the question.
-/

namespace OMA.S_mo_93022

/-- The state reached when the input word is read from left to right. -/
def run {n a : ℕ} (δ : Fin a → Fin n → Fin n) (w : List (Fin a)) (p : Fin n) : Fin n :=
  w.foldl (fun s l => δ l s) p

/-- For each distinct pair, one state reaches the other by iterating the given map. -/
def Connecting {n : ℕ} (f : Fin n → Fin n) : Prop :=
  ∀ p q, p ≠ q → ∃ k : ℕ, 0 < k ∧ (f^[k] p = q ∨ f^[k] q = p)

/-- Each state can reach every state by some input word. -/
def Strong {n a : ℕ} (δ : Fin a → Fin n → Fin n) : Prop :=
  ∀ p q, ∃ w, run δ w p = q

theorem main :
    ∀ (n a : ℕ) (_ : 0 < n) (δ : Fin a → Fin n → Fin n),
      Strong δ → (∃ w, Connecting (run δ w)) →
        ∃ v, v.length ≤ n - 1 ∧ Connecting (run δ v) := by
  sorry

end OMA.S_mo_93022
