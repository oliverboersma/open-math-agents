import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Nat.Bits
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Complex.Basic

/-!
# Do identical isometry groups transfer NP-hardness? MathOverflow 47956

The dimension varies. We use the rational threshold decision formulation of
norm evaluation and polynomial-time many-one reductions. Input matrices have
Gaussian rational entries and are encoded densely in row-major order. All
isometries here are bijective complex-linear maps. The source allows arbitrary
vector-space norms on matrices without requiring submultiplicativity.
-/

namespace OMA.S_mo_47956

abbrev Bits := List Bool
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev Family := (n : ℕ) → Mat n → ℝ

def isNorm (N : Family) : Prop :=
  ∀ n, (∀ A, 0 ≤ N n A) ∧ (∀ A, N n A = 0 ↔ A = 0) ∧
    (∀ A B, N n (A + B) ≤ N n A + N n B) ∧
    ∀ (c : ℂ) A, N n (c • A) = ‖c‖ * N n A

def sameIsometries (N M : Family) : Prop :=
  ∀ n (T : Mat n ≃ₗ[ℂ] Mat n),
    (∀ A, N n (T A) = N n A) ↔ (∀ A, M n (T A) = M n A)

def framed (s : Bits) : Bits := List.replicate s.length true ++ [false] ++ s

def ratBits (r : ℚ) : Bits :=
  [decide (r.num < 0)] ++ framed r.num.natAbs.bits ++ framed r.den.bits

structure Query where
  dim : ℕ
  entry : Fin dim → Fin dim → ℚ × ℚ
  threshold : ℚ

def encode (q : Query) : Bits :=
  framed q.dim.bits ++ (List.ofFn (fun i : Fin q.dim =>
    (List.ofFn (fun j : Fin q.dim =>
      ratBits (q.entry i j).1 ++ ratBits (q.entry i j).2)).flatten)).flatten ++
    ratBits q.threshold

def thresholdLanguage (N : Family) : Set Bits :=
  {s | ∃ q : Query, encode q = s ∧ (q.threshold : ℝ) ≤
    N q.dim (fun i j => ((q.entry i j).1 : ℂ) + ((q.entry i j).2 : ℂ) * Complex.I)}

def poly {α β : Type} (ea : α → Bits) (eb : β → Bits) (f : α → β) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime ea eb f)

def inNP (L : Set Bits) : Prop :=
  ∃ (v : Bits × Bits → Bool) (k c : ℕ),
    poly (fun p => framed p.1 ++ p.2) (fun b => [b]) v ∧
    ∀ x, x ∈ L ↔ ∃ w : Bits, w.length ≤ c * (x.length + 1)^k ∧ v (x,w) = true

def hard (H : Set Bits) : Prop :=
  ∀ L : Set Bits, inNP L →
    ∃ r : Bits → Bits, poly id id r ∧ ∀ x, x ∈ L ↔ r x ∈ H

theorem main :
    ∀ N M : Family, isNorm N → isNorm M → sameIsometries N M →
      hard (thresholdLanguage N) → hard (thresholdLanguage M) := by
  sorry

end OMA.S_mo_47956
