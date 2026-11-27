import FormalConjectures.ErdosProblems.«560»
import Mathlib

/-! Conlon, Fox and Wigderson conjecture that the size Ramsey number of K_{n,n} is of order
n^3 2^n. The upper bound of this order is the theorem of Erdős, Faudree, Rousseau and Schelp
and of Nešetřil and Rödl, with the explicit constant 3/2; it is the catalogue's solved variant
Erdos560.erdos_560.variants.upper_bound. The lower bound of order n^3 2^n is the open part: the
best known lower bound, of Erdős and Rousseau, is of order n^2 2^n. -/

namespace OMA.R_Erdos560_erdos_560_variants_conlon_fox_wigderson_R1

open Filter Asymptotics SimpleGraph

/-- The known upper bound: the size Ramsey number of K_{n,n} is O(n^3 2^n). -/
def H1 : Prop :=
  (fun n : ℕ ↦ ((sizeRamsey (completeBipartiteGraph (Fin n) (Fin n))
    (completeBipartiteGraph (Fin n) (Fin n)) : ℕ) : ℝ)) =O[atTop]
    (fun n : ℕ ↦ (n : ℝ) ^ 3 * 2 ^ n)

/-- The open lower bound of the same order. -/
def H2 : Prop :=
  (fun n : ℕ ↦ (n : ℝ) ^ 3 * 2 ^ n) =O[atTop]
    (fun n : ℕ ↦ ((sizeRamsey (completeBipartiteGraph (Fin n) (Fin n))
      (completeBipartiteGraph (Fin n) (Fin n)) : ℕ) : ℝ))

theorem main : H1 → H2 → type_of% @Erdos560.erdos_560.variants.conlon_fox_wigderson := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_Erdos560_erdos_560_variants_conlon_fox_wigderson_R1
