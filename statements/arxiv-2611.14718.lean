import Mathlib

/-!
# Stochastic dominance in graph parking

Robinson Higuita-Diaz, Lykos López and Alejandro Roldán-Correa, arXiv:2611.14718,
Conjecture 5.2 and equations (2)–(3). Credit: @rleshner.

A natural number below 2^n represents its subset of Fin n in binary.
The static ensemble is uniform on all maximal independent sets. The sequential
process picks a uniform available vertex and removes its closed neighborhood.
-/

namespace OMA.S_arxiv_2611_14718

def closedMask {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) : ℕ :=
  (List.finRange n).foldl (fun s w => if v = w ∨ G.Adj v w then s + 2 ^ w.val else s) 0

def seats (n s : ℕ) : List (Fin n) :=
  (List.finRange n).filter (fun i => s.testBit i.val)

/-- Enumerate the sizes of the maximal independent sets, one entry per set.
At each vertex we may skip it, or occupy it if uncovered. The covered
vertices are precisely the occupied vertices and their neighbors. At the
end a branch is maximal precisely when it covers the whole graph. -/
def jammedSizes {n : ℕ} (N : Fin n → ℕ) : List (Fin n) → ℕ → ℕ → List ℕ
  | [], covered, k => if covered = 2 ^ n - 1 then [k] else []
  | i :: rest, covered, k =>
    jammedSizes N rest covered k ++
      (if covered.testBit i.val then []
       else jammedSizes N rest (covered ||| N i) (k + 1))

def staticCDF {n : ℕ} (N : Fin n → ℕ) (k : ℕ) : ℚ :=
  let counts := jammedSizes N (List.finRange n) 0 0
  (counts.countP (fun j => j ≤ k) : ℚ) / counts.length

/-- Cumulative probability of choosing at most k further vertices from s.
The recursion averages over the possible first choices. -/
def seqCDF {n : ℕ} (N : Fin n → ℕ) : ℕ → ℕ → ℚ
  | 0, s => if s = 0 then 1 else 0
  | k + 1, s =>
    if s = 0 then 1 else
      let xs := seats n s
      (xs.map (fun i => seqCDF N k (s ^^^ (s &&& N i)))).sum / xs.length

theorem main : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ v, G.degree v ≤ 3) → ∀ k : ℕ,
    seqCDF (closedMask G) k (2 ^ n - 1) ≤ staticCDF (closedMask G) k := by
  sorry

end OMA.S_arxiv_2611_14718
