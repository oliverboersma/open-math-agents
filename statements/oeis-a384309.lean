import Mathlib

/-!
# OEIS A384309

The first coordinate after t steps is the (t+1)-st term. The nine
counters record earlier terms classified by leading digit, with digit
d represented by d-1. The next term is the previous counter of its
leading digit plus one, including the current term in the count.

Sycamore conjectured the exact multiplicity of every positive integer
and the position of the last term of each decimal length. The decimal
index written 23 followed by k-1 nines and a final 3 equals 24*10^k-7.

Source: https://oeis.org/A384309
-/

namespace OMA.S_oeis_a384309

abbrev Digit := Fin 9

def leading (x : ℕ) : Digit := ⟨(x/10^(Nat.log 10 x)-1)%9, Nat.mod_lt _ (by decide)⟩

def state : ℕ → ℕ × (Digit → ℕ)
  | 0 => (1,fun _ => 0)
  | t+1 =>
    let s := state t
    let d := leading s.1
    (s.2 d+1,fun i => s.2 i + if i=d then 1 else 0)

def entry (n : ℕ) := (state (n-1)).1

theorem main :
    (∀ x : ℕ, 0 < x → ∃ M, ∀ m ≥ M,
      ((Finset.range m).filter (fun t => (state t).1=x)).card = if x=1 then 10 else 9) ∧
    (∀ k : ℕ, 0 < k → entry (24*10^k-7)=10^k-1 ∧
      ∀ n > 24*10^k-7, 10^k ≤ entry n) := by
  sorry

end OMA.S_oeis_a384309
