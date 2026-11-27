import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Logic.Function.Iterate

/-!
# Truly subcubic counting of triangles with pairwise coprime edge weights

Source: https://mathoverflow.net/q/104415 (Jernej, 10 August 2012).
Credit: @LDJAI.

The author specifies in a comment that the positive integer edge weights may
be assumed polynomially bounded in the vertex count. Zero encodes a missing
edge. We interpret subcubic as a worst-case bound with a fixed positive
exponent saving. We use a deterministic word RAM with logarithmic word size
and a finite program independent of the input size. Word operations have unit
cost. No factoring instruction or other number-theoretic oracle is provided.
-/

namespace OMA.S_mo_104415

/-- An undirected, loopless weighted adjacency matrix with a polynomial weight bound. -/
def ValidInput {n : ℕ} (C : ℕ) (w : Fin n → Fin n → ℕ) : Prop :=
  (∀ i, w i i = 0) ∧ (∀ i j, w i j = w j i) ∧ (∀ i j, w i j ≤ n ^ C)

/-- The increasing vertex order counts each undirected triangle just once. -/
def triangleCount {n : ℕ} (w : Fin n → Fin n → ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n × Fin n)).filter (fun t =>
    let i := t.1
    let j := t.2.1
    let k := t.2.2
    i < j ∧ j < k ∧ 0 < w i j ∧ 0 < w j k ∧ 0 < w k i ∧
    (w i j).Coprime (w j k) ∧ (w j k).Coprime (w k i) ∧
    (w k i).Coprime (w i j))).card

/-- Memory cell 0 contains n. The next n² cells contain the matrix in row-major order. -/
def inputMemory (n : ℕ) (w : Fin n → Fin n → ℕ) : ℕ → ℕ
  | 0 => n
  | addr + 1 =>
    if hi : addr / n < n then
      if hj : addr % n < n then w ⟨addr / n, hi⟩ ⟨addr % n, hj⟩ else 0
    else 0

inductive WordOp where
  | add | sub | mul | div | rem

/-- Instructions address registers by constant indices and data memory indirectly. -/
inductive Instr where
  | const (dst value : ℕ)
  | calc (op : WordOp) (dst left right : ℕ)
  | load (dst addressRegister : ℕ)
  | store (addressRegister src : ℕ)
  | jump (label : ℕ)
  | jumpLT (left right label : ℕ)
  | halt

structure Config where
  pc : ℕ
  reg : ℕ → ℕ
  mem : ℕ → ℕ
  halted : Bool

/-- The arithmetic modulus is a power of two. Inputs to this operation are words. -/
def wordOp (modulus : ℕ) (op : WordOp) (a b : ℕ) : ℕ :=
  match op with
  | .add => (a + b) % modulus
  | .sub => (a + modulus - b) % modulus
  | .mul => (a * b) % modulus
  | .div => a / b
  | .rem => a % b

def writeReg (s : Config) (dst value : ℕ) : Config :=
  {s with pc := s.pc + 1, reg := Function.update s.reg dst value}

/-- Falling off the program is a stuck state. Only an explicit halt counts as success. -/
def step (program : List Instr) (modulus : ℕ) (s : Config) : Config :=
  if s.halted then s else
    match program[s.pc]? with
    | none => s
    | some (.const dst value) => writeReg s dst (value % modulus)
    | some (.calc op dst l r) => writeReg s dst (wordOp modulus op (s.reg l) (s.reg r))
    | some (.load dst addr) => writeReg s dst (s.mem (s.reg addr))
    | some (.store addr src) =>
      {s with pc := s.pc + 1, mem := Function.update s.mem (s.reg addr) (s.reg src)}
    | some (.jump label) => {s with pc := label}
    | some (.jumpLT l r label) =>
      {s with pc := if s.reg l < s.reg r then label else s.pc + 1}
    | some .halt => {s with halted := true}

/-- Each iteration is one RAM instruction. The output is in register 0. -/
def run (program : List Instr) (widthFactor n : ℕ) (w : Fin n → Fin n → ℕ) (time : ℕ) :
    Config :=
  let modulus := 2 ^ (widthFactor * ((n + 2).log2 + 1))
  let start : Config := ⟨0, fun _ => 0, inputMemory n w, false⟩
  (step program modulus)^[time] start

/-- A power bound expresses a positive exponent saving without real powers:
for d ≥ 1, time^d ≤ K (n+2)^(3d-1) means time = O(n^(3 - 1/d)). -/
theorem main : ∀ C : ℕ, ∃ (program : List Instr) (widthFactor K d : ℕ),
    C + 4 ≤ widthFactor ∧ 0 < d ∧
    ∀ (n : ℕ) (w : Fin n → Fin n → ℕ), ValidInput C w →
      ∃ time : ℕ, time ^ d ≤ K * (n + 2) ^ (3 * d - 1) ∧
        (run program widthFactor n w time).halted = true ∧
        (run program widthFactor n w time).reg 0 = triangleCount w := by
  sorry

end OMA.S_mo_104415
