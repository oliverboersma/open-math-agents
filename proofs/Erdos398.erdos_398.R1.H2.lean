import OMAReductions.R_Erdos398_erdos_398_R1
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Ring.Parity

/-! Brocard's equation as a consecutive-factor equation, and a checked prefix. -/

namespace OMA.Erdos398Brocard
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem finite_sqrt_values :
    ∀ j : Fin 128,
      (j.val.factorial + 1).sqrt ^ 2 = j.val.factorial + 1 ↔
        j.val = 4 ∨ j.val = 5 ∨ j.val = 7 := by
  decide +kernel

theorem finite_prefix (n : ℕ) (hn : n < 128) :
    (∃ m : ℕ, n.factorial + 1 = m ^ 2) ↔ n ∈ ({4, 5, 7} : Set ℕ) := by
  have hEq : (∃ m : ℕ, n.factorial + 1 = m ^ 2) ↔
      (n.factorial + 1).sqrt ^ 2 = n.factorial + 1 := by
    simpa only [eq_comm] using Nat.exists_mul_self' (n.factorial + 1)
  rw [hEq]
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using finite_sqrt_values ⟨n, hn⟩

end OMA.Erdos398Brocard

theorem OMA.solution : OMA.R_Erdos398_erdos_398_R1.H2 :=
  OMA.Erdos398Brocard.finite_prefix
