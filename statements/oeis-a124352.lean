import Mathlib.Data.Nat.Basic

/-!
# A124352: directed Hamiltonian paths on the n-antiprism graph
Source: https://oeis.org/A124352
Credit: @LDJAI

Exact edge-set enumeration for directed Hamiltonian paths in the n-antiprism.
The square of a cycle of length 2*n has an edge between any pair of vertices
at cyclic distance one or two. For n >= 3, process the nonwrap edges in order
of their larger vertex, and process the three wrap edges at the end.

A state keeps the degrees and connected-component labels of vertices
0,1,k-2,k-1, and the number of degree-one vertices already forgotten.
For each choice of admissible new edges the algorithm rejects cycles and
degrees exceeding two. A vertex can be forgotten only if it is not isolated
and its component still meets the frontier. At the end all four remaining
vertices must have positive degree, there must be exactly two degree-one
vertices in total, and all components must be joined. Such subgraphs are
precisely spanning paths, since they are connected acyclic graphs of maximum
degree two; each has exactly two orientations. Choices are counted with
multiplicity, even when their states agree.
-/
namespace OMA.S_oeis_a124352

structure State where
  deg : List Nat
  part : List Nat
  ends : Nat
deriving DecidableEq

def canonAux : List Nat → List Nat → List Nat
  | [], _ => []
  | x :: xs, seen =>
    if seen.contains x then seen.idxOf x :: canonAux xs seen
    else seen.length :: canonAux xs (seen ++ [x])

def canonical (xs : List Nat) : List Nat := canonAux xs []

def masks : List (Nat × Nat) → List (List (Nat × Nat))
  | [] => [[]]
  | e :: es => masks es ++ (masks es).map (fun l => e :: l)

def addEdge (s : State) (e : Nat × Nat) : Option State :=
  let i := e.1
  let j := e.2
  let d := s.deg
  let p := s.part
  let a := p.getD i 0
  let b := p.getD j 0
  if d.getD i 0 = 2 ∨ d.getD j 0 = 2 ∨ a = b then none
  else some ⟨(d.set i (d.getD i 0 + 1)).set j (d.getD j 0 + 1),
    p.map (fun x => if x = b then a else x), s.ends⟩

def addEdges (s : State) : List (Nat × Nat) → Option State
  | [] => some ⟨s.deg, canonical s.part, s.ends⟩
  | ed :: es =>
    match addEdge s ed with
    | none => none
    | some t => addEdges t es

def initial : List State :=
  (masks [(0,1),(0,2),(1,2),(1,3),(2,3)]).filterMap
    (fun es => addEdges ⟨[0,0,0,0],[0,1,2,3],0⟩ es)

def forget (s : State) : Option State :=
  let d := s.deg
  let p := s.part
  let e := s.ends + if d.getD 2 0 = 1 then 1 else 0
  if d.getD 2 0 = 0 ∨ p.count (p.getD 2 0) = 1 ∨ e > 2 then none
  else some ⟨[d.getD 0 0,d.getD 1 0,d.getD 3 0,d.getD 4 0],
    canonical [p.getD 0 0,p.getD 1 0,p.getD 3 0,p.getD 4 0], e⟩

def next (s : State) : List State :=
  (masks [(2,4),(3,4)]).filterMap
    (fun es =>
      match addEdges ⟨s.deg ++ [0], s.part ++ [4], s.ends⟩ es with
      | none => none
      | some t => forget t)

def closing (s : State) : Int :=
  2 * Int.ofNat ((masks [(2,0),(3,0),(3,1)]).filter
    (fun es => match addEdges s es with
      | none => false
      | some t => !(t.deg.contains 0) &&
          t.ends + t.deg.count 1 == 2 &&
          t.part.all (fun x => x == 0))).length

def next2 (s : State) : List State := (next s).flatMap next

def sumStates (xs : List State) (f : State → Int) : Int :=
  match xs with
  | [] => 0
  | s :: ss => f s + sumStates ss f

-- Each branch chooses a subset of the two possible nonwrap edges at each new vertex.
def countFrom : Nat → State → Int
  | 0, s => closing s
  | k+1, s => sumStates (next2 s) (countFrom k)

def a (n : Nat) : Int :=
  if n < 3 then 0 else sumStates initial (countFrom (n-2))



def numerator : Nat → Int
  | 3 => 240
  | 4 => -384
  | 5 => -240
  | 6 => 336
  | 7 => 244
  | 8 => -292
  | 9 => -164
  | 10 => 60
  | 11 => 56
  | _ => 0


/--
The source's three equivalent formulas. The middle clause is the generating
function after multiplying by its denominator, stated coefficientwise over
the integers. The sequence is extended by zero below n=3. Since the
denominator has constant coefficient 1, multiplication by it is invertible
on formal power series. The coefficient formula is exactly equivalent to
the displayed quotient, not a numeric approximation.
-/
theorem main :
    (∀ n : Nat, 11 < n →
      a n = 5 * a (n-1) - 6 * a (n-2) - 4 * a (n-3) + 7 * a (n-4) +
        5 * a (n-5) - 5 * a (n-6) - 3 * a (n-7) + a (n-8) + a (n-9)) ∧
    (∀ n : Nat,
      a n - 5*a (n-1) + 6*a (n-2) + 4*a (n-3) - 7*a (n-4) -
        5*a (n-5) + 5*a (n-6) + 3*a (n-7) - a (n-8) - a (n-9) = numerator n) ∧
    (∀ n : Nat, 9 ≤ n →
      a n = 2 * a (n-1) + 3 * a (n-2) - 2 * a (n-3) - 6 * a (n-4) -
        4 * a (n-5) - a (n-6) + 672 * (n : Int) - 1376 - 72 * (n : Int)^2) := by
  sorry

end OMA.S_oeis_a124352
