import FormalConjectures.GreensOpenProblems.«100»

/-!
# Reduction of non-soficity to a cellular-automaton counterexample

The first obligation is supplied mathematically by OpenAI's *A Counterexample to
Kaplansky's Direct-Finiteness Conjecture in Characteristic Two* (2026), whose
Lean artifact is `OAI.OddKaplansky.main_theorem` at openai/math commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. That theorem gives a finite field,
a group, and a linear cellular automaton that is injective but not surjective.
The second obligation is the sofic surjunctivity theorem of Gromov (1999) and
Weiss (2000): a sofic group admits no such automaton over a finite alphabet.

The bridge below uses the cellular-automaton convention in the cited OpenAI
artifact. The two mathematical inputs remain independent obligations, and the
main theorem transports their contradiction to the exact `IsSofic` statement
of Green 100(i).
-/

namespace OMA.R_Green100_green_100_parts_i_R1

open Green100

/-- An explicit witness to failure of surjunctivity over a finite field. The
cellular map is written inline, as in OpenAI's `OAI.OddKaplansky.cellular`. -/
def H1 : Prop :=
  ∃ (K : Type) (fK : Field K) (ftK : Fintype K) (G : Type) (gG : Group G),
    letI := fK
    letI := ftK
    letI := gG
    ∃ b : MonoidAlgebra K G,
      Function.Injective (fun (x : G → K) (g : G) =>
        b.coeff.sum fun u c => c * x (g * u)) ∧
      ¬ Function.Surjective (fun (x : G → K) (g : G) =>
        b.coeff.sum fun u c => c * x (g * u))

/-- Gromov-Weiss surjunctivity, restricted to the linear cellular automata
coming from finite-field group algebras. -/
def H2 : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (G : Type) [Group G], IsSofic G →
    ∀ b : MonoidAlgebra K G,
      Function.Injective (fun (x : G → K) (g : G) =>
        b.coeff.sum fun u c => c * x (g * u)) →
      Function.Surjective (fun (x : G → K) (g : G) =>
        b.coeff.sum fun u c => c * x (g * u))

theorem main : H1 → H2 → type_of% @Green100.green_100.parts.i := by
  intro h1 h2 hall
  obtain ⟨K, fK, ftK, G, gG, b, hinj, hnot_surj⟩ := h1
  letI := fK
  letI := ftK
  letI := gG
  exact hnot_surj (h2 K G (hall G) b hinj)

end OMA.R_Green100_green_100_parts_i_R1
