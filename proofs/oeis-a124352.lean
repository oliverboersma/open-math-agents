import OMAStatements.S_oeis_a124352
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

-- Problem: A124352: Number of directed Hamiltonian paths on the n-antiprism graph.
-- Upstream: formal-conjectures statements/oeis-a124352.lean:0 (declaration OMA.S_oeis_a124352.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Proof_oeis_a124352

open OMA.S_oeis_a124352

private def numStates : Nat := 117

private def stateOf (i : Fin numStates) : State :=
  match i.val with
  | 0 => ⟨[0, 0, 0, 0], [0, 1, 2, 3], 0⟩
  | 1 => ⟨[0, 0, 1, 1], [0, 1, 2, 2], 0⟩
  | 2 => ⟨[0, 1, 0, 1], [0, 1, 2, 1], 0⟩
  | 3 => ⟨[0, 1, 1, 2], [0, 1, 1, 1], 0⟩
  | 4 => ⟨[0, 1, 1, 0], [0, 1, 1, 2], 0⟩
  | 5 => ⟨[0, 1, 2, 1], [0, 1, 1, 1], 0⟩
  | 6 => ⟨[0, 2, 1, 1], [0, 1, 1, 1], 0⟩
  | 7 => ⟨[1, 0, 1, 0], [0, 1, 0, 2], 0⟩
  | 8 => ⟨[1, 0, 2, 1], [0, 1, 0, 0], 0⟩
  | 9 => ⟨[1, 1, 1, 1], [0, 1, 0, 1], 0⟩
  | 10 => ⟨[1, 1, 2, 2], [0, 0, 0, 0], 0⟩
  | 11 => ⟨[1, 1, 2, 0], [0, 0, 0, 1], 0⟩
  | 12 => ⟨[1, 2, 2, 1], [0, 0, 0, 0], 0⟩
  | 13 => ⟨[1, 1, 0, 0], [0, 0, 1, 2], 0⟩
  | 14 => ⟨[1, 1, 1, 1], [0, 0, 1, 1], 0⟩
  | 15 => ⟨[1, 2, 0, 1], [0, 0, 1, 0], 0⟩
  | 16 => ⟨[1, 2, 1, 2], [0, 0, 0, 0], 0⟩
  | 17 => ⟨[1, 2, 1, 0], [0, 0, 0, 1], 0⟩
  | 18 => ⟨[2, 1, 1, 0], [0, 0, 0, 1], 0⟩
  | 19 => ⟨[2, 1, 2, 1], [0, 0, 0, 0], 0⟩
  | 20 => ⟨[2, 2, 1, 1], [0, 0, 0, 0], 0⟩
  | 21 => ⟨[0, 0, 1, 1], [0, 1, 2, 3], 2⟩
  | 22 => ⟨[0, 0, 2, 2], [0, 1, 2, 2], 2⟩
  | 23 => ⟨[0, 0, 2, 0], [0, 1, 2, 3], 2⟩
  | 24 => ⟨[0, 0, 2, 1], [0, 1, 2, 2], 1⟩
  | 25 => ⟨[0, 0, 0, 1], [0, 1, 2, 3], 1⟩
  | 26 => ⟨[0, 0, 1, 2], [0, 1, 2, 2], 1⟩
  | 27 => ⟨[0, 0, 1, 0], [0, 1, 2, 3], 1⟩
  | 28 => ⟨[0, 1, 1, 0], [0, 1, 2, 3], 2⟩
  | 29 => ⟨[0, 1, 2, 1], [0, 1, 2, 2], 2⟩
  | 30 => ⟨[0, 1, 1, 1], [0, 1, 2, 1], 1⟩
  | 31 => ⟨[0, 1, 2, 2], [0, 1, 1, 1], 1⟩
  | 32 => ⟨[0, 1, 2, 0], [0, 1, 1, 2], 1⟩
  | 33 => ⟨[0, 1, 0, 0], [0, 1, 2, 3], 1⟩
  | 34 => ⟨[0, 1, 1, 1], [0, 1, 2, 2], 1⟩
  | 35 => ⟨[0, 1, 0, 1], [0, 1, 2, 3], 2⟩
  | 36 => ⟨[0, 1, 1, 2], [0, 1, 2, 2], 2⟩
  | 37 => ⟨[0, 1, 1, 1], [0, 1, 1, 2], 1⟩
  | 38 => ⟨[0, 2, 0, 0], [0, 1, 2, 3], 2⟩
  | 39 => ⟨[0, 2, 1, 1], [0, 1, 2, 2], 2⟩
  | 40 => ⟨[0, 2, 0, 1], [0, 1, 2, 1], 1⟩
  | 41 => ⟨[0, 2, 1, 2], [0, 1, 1, 1], 1⟩
  | 42 => ⟨[0, 2, 1, 0], [0, 1, 1, 2], 1⟩
  | 43 => ⟨[0, 2, 2, 1], [0, 1, 1, 1], 1⟩
  | 44 => ⟨[1, 0, 0, 1], [0, 1, 2, 3], 2⟩
  | 45 => ⟨[1, 0, 1, 2], [0, 1, 2, 2], 2⟩
  | 46 => ⟨[1, 0, 1, 0], [0, 1, 2, 3], 2⟩
  | 47 => ⟨[1, 0, 2, 1], [0, 1, 2, 2], 2⟩
  | 48 => ⟨[1, 0, 1, 1], [0, 1, 2, 2], 1⟩
  | 49 => ⟨[1, 0, 1, 1], [0, 1, 0, 2], 1⟩
  | 50 => ⟨[1, 0, 2, 2], [0, 1, 0, 0], 1⟩
  | 51 => ⟨[1, 0, 2, 0], [0, 1, 0, 2], 1⟩
  | 52 => ⟨[1, 0, 0, 0], [0, 1, 2, 3], 1⟩
  | 53 => ⟨[1, 0, 0, 1], [0, 1, 2, 0], 0⟩
  | 54 => ⟨[1, 0, 1, 2], [0, 1, 0, 0], 0⟩
  | 55 => ⟨[1, 1, 0, 0], [0, 1, 2, 3], 2⟩
  | 56 => ⟨[1, 1, 1, 1], [0, 1, 2, 2], 2⟩
  | 57 => ⟨[1, 1, 0, 1], [0, 1, 2, 1], 1⟩
  | 58 => ⟨[1, 1, 1, 2], [0, 1, 1, 1], 1⟩
  | 59 => ⟨[1, 1, 1, 0], [0, 1, 1, 2], 1⟩
  | 60 => ⟨[1, 1, 2, 1], [0, 1, 1, 1], 1⟩
  | 61 => ⟨[1, 1, 1, 0], [0, 1, 0, 2], 1⟩
  | 62 => ⟨[1, 1, 2, 1], [0, 1, 0, 0], 1⟩
  | 63 => ⟨[1, 1, 0, 1], [0, 0, 1, 2], 1⟩
  | 64 => ⟨[1, 1, 1, 2], [0, 0, 1, 1], 1⟩
  | 65 => ⟨[1, 1, 1, 0], [0, 0, 1, 2], 1⟩
  | 66 => ⟨[1, 1, 2, 1], [0, 0, 1, 1], 1⟩
  | 67 => ⟨[1, 2, 0, 0], [0, 0, 1, 2], 1⟩
  | 68 => ⟨[1, 2, 1, 1], [0, 0, 1, 1], 1⟩
  | 69 => ⟨[1, 1, 1, 1], [0, 0, 1, 2], 2⟩
  | 70 => ⟨[1, 1, 2, 2], [0, 0, 1, 1], 2⟩
  | 71 => ⟨[1, 1, 2, 0], [0, 0, 1, 2], 2⟩
  | 72 => ⟨[1, 2, 1, 0], [0, 0, 1, 2], 2⟩
  | 73 => ⟨[1, 2, 2, 1], [0, 0, 1, 1], 2⟩
  | 74 => ⟨[1, 2, 1, 1], [0, 0, 1, 0], 1⟩
  | 75 => ⟨[1, 2, 2, 2], [0, 0, 0, 0], 1⟩
  | 76 => ⟨[1, 2, 2, 0], [0, 0, 0, 1], 1⟩
  | 77 => ⟨[1, 2, 0, 1], [0, 0, 1, 2], 2⟩
  | 78 => ⟨[1, 2, 1, 2], [0, 0, 1, 1], 2⟩
  | 79 => ⟨[1, 2, 1, 1], [0, 0, 0, 1], 1⟩
  | 80 => ⟨[2, 1, 0, 1], [0, 0, 1, 2], 2⟩
  | 81 => ⟨[2, 1, 1, 2], [0, 0, 1, 1], 2⟩
  | 82 => ⟨[2, 1, 1, 0], [0, 0, 1, 2], 2⟩
  | 83 => ⟨[2, 1, 2, 1], [0, 0, 1, 1], 2⟩
  | 84 => ⟨[2, 1, 1, 1], [0, 0, 1, 1], 1⟩
  | 85 => ⟨[2, 1, 1, 1], [0, 0, 0, 1], 1⟩
  | 86 => ⟨[2, 1, 2, 2], [0, 0, 0, 0], 1⟩
  | 87 => ⟨[2, 1, 2, 0], [0, 0, 0, 1], 1⟩
  | 88 => ⟨[2, 1, 0, 0], [0, 0, 1, 2], 1⟩
  | 89 => ⟨[2, 1, 0, 1], [0, 0, 1, 0], 0⟩
  | 90 => ⟨[2, 1, 1, 2], [0, 0, 0, 0], 0⟩
  | 91 => ⟨[2, 2, 0, 0], [0, 0, 1, 2], 2⟩
  | 92 => ⟨[2, 2, 1, 1], [0, 0, 1, 1], 2⟩
  | 93 => ⟨[2, 2, 0, 1], [0, 0, 1, 0], 1⟩
  | 94 => ⟨[2, 2, 1, 2], [0, 0, 0, 0], 1⟩
  | 95 => ⟨[2, 2, 1, 0], [0, 0, 0, 1], 1⟩
  | 96 => ⟨[2, 2, 2, 1], [0, 0, 0, 0], 1⟩
  | 97 => ⟨[0, 2, 1, 1], [0, 1, 2, 1], 2⟩
  | 98 => ⟨[0, 2, 2, 2], [0, 1, 1, 1], 2⟩
  | 99 => ⟨[0, 2, 2, 0], [0, 1, 1, 2], 2⟩
  | 100 => ⟨[0, 2, 1, 1], [0, 1, 1, 2], 2⟩
  | 101 => ⟨[1, 0, 1, 1], [0, 1, 2, 0], 1⟩
  | 102 => ⟨[1, 1, 1, 1], [0, 1, 2, 1], 2⟩
  | 103 => ⟨[1, 1, 2, 2], [0, 1, 1, 1], 2⟩
  | 104 => ⟨[1, 1, 2, 0], [0, 1, 1, 2], 2⟩
  | 105 => ⟨[1, 1, 1, 1], [0, 1, 1, 2], 2⟩
  | 106 => ⟨[1, 1, 1, 1], [0, 1, 0, 2], 2⟩
  | 107 => ⟨[1, 1, 2, 2], [0, 1, 0, 0], 2⟩
  | 108 => ⟨[1, 1, 2, 0], [0, 1, 0, 2], 2⟩
  | 109 => ⟨[1, 1, 0, 1], [0, 1, 2, 0], 1⟩
  | 110 => ⟨[1, 1, 1, 2], [0, 1, 0, 0], 1⟩
  | 111 => ⟨[2, 1, 1, 1], [0, 0, 1, 0], 1⟩
  | 112 => ⟨[2, 2, 1, 1], [0, 0, 1, 0], 2⟩
  | 113 => ⟨[2, 2, 2, 2], [0, 0, 0, 0], 2⟩
  | 114 => ⟨[2, 2, 2, 0], [0, 0, 0, 1], 2⟩
  | 115 => ⟨[2, 2, 1, 1], [0, 0, 0, 1], 2⟩
  | 116 => ⟨[1, 1, 1, 1], [0, 1, 2, 0], 2⟩
  | _ => ⟨[0, 0, 0, 0], [0, 1, 2, 3], 0⟩

private def adjIdx (i : Fin numStates) : List Nat :=
  match i.val with
  | 0 => [21, 22, 23, 24]
  | 1 => [25, 26, 27, 24, 27, 24, 1]
  | 2 => [28, 29, 30, 31, 32]
  | 3 => [33, 34, 4, 5]
  | 4 => [35, 36, 28, 29, 34, 37, 31, 32, 5]
  | 5 => [33, 34, 2, 3, 4, 5]
  | 6 => [38, 39, 40, 41, 42, 43, 42, 43, 6]
  | 7 => [44, 45, 46, 47, 48, 49, 50, 51, 8]
  | 8 => [52, 48, 53, 54, 7, 8]
  | 9 => [55, 56, 57, 58, 59, 60, 61, 62, 9, 10, 11]
  | 10 => [13, 14]
  | 11 => [63, 64, 65, 66, 14]
  | 12 => [67, 68, 15, 16, 17, 12]
  | 13 => [69, 70, 71, 66]
  | 14 => [63, 64, 65, 66, 65, 66, 14]
  | 15 => [72, 73, 74, 75, 76]
  | 16 => [67, 68, 17, 12]
  | 17 => [77, 78, 72, 73, 68, 79, 75, 76, 12]
  | 18 => [80, 81, 82, 83, 84, 85, 86, 87, 19]
  | 19 => [88, 84, 89, 90, 18, 19]
  | 20 => [91, 92, 93, 94, 95, 96, 95, 96, 20]
  | 21 => [21, 22, 23]
  | 22 => []
  | 23 => []
  | 24 => [25, 26, 27, 24]
  | 25 => [21, 22, 23]
  | 26 => [27, 24]
  | 27 => [21, 22, 23, 24]
  | 28 => [29]
  | 29 => [35, 36, 28, 29]
  | 30 => [28, 29, 30, 31, 32]
  | 31 => [33, 34]
  | 32 => [35, 36, 28, 29, 34]
  | 33 => [29]
  | 34 => [35, 36, 28, 29, 28, 29, 34]
  | 35 => []
  | 36 => [28, 29]
  | 37 => [35, 36, 28, 29, 37, 31, 32]
  | 38 => []
  | 39 => [39]
  | 40 => [97, 98, 99]
  | 41 => [38, 39, 42, 43]
  | 42 => [39, 100, 98, 99, 43]
  | 43 => [38, 39, 40, 41, 42, 43]
  | 44 => []
  | 45 => [46, 47]
  | 46 => [47]
  | 47 => [44, 45, 46, 47]
  | 48 => [44, 45, 46, 47, 46, 47, 48]
  | 49 => [44, 45, 46, 47, 49, 50, 51]
  | 50 => [52, 48]
  | 51 => [44, 45, 46, 47, 48]
  | 52 => [47]
  | 53 => [46, 47, 101, 50, 51]
  | 54 => [52, 48, 7, 8]
  | 55 => []
  | 56 => [56]
  | 57 => [102, 103, 104]
  | 58 => [55, 56, 59, 60]
  | 59 => [56, 105, 103, 104, 60]
  | 60 => [55, 56, 57, 58, 59, 60]
  | 61 => [56, 106, 107, 108, 62]
  | 62 => [55, 56, 109, 110, 61, 62]
  | 63 => [69, 70, 71]
  | 64 => [65, 66]
  | 65 => [69, 70, 71, 66]
  | 66 => [63, 64, 65, 66]
  | 67 => [73]
  | 68 => [77, 78, 72, 73, 72, 73, 68]
  | 69 => [69, 70, 71]
  | 70 => []
  | 71 => []
  | 72 => [73]
  | 73 => [77, 78, 72, 73]
  | 74 => [72, 73, 74, 75, 76]
  | 75 => [67, 68]
  | 76 => [77, 78, 72, 73, 68]
  | 77 => []
  | 78 => [72, 73]
  | 79 => [77, 78, 72, 73, 79, 75, 76]
  | 80 => []
  | 81 => [82, 83]
  | 82 => [83]
  | 83 => [80, 81, 82, 83]
  | 84 => [80, 81, 82, 83, 82, 83, 84]
  | 85 => [80, 81, 82, 83, 85, 86, 87]
  | 86 => [88, 84]
  | 87 => [80, 81, 82, 83, 84]
  | 88 => [83]
  | 89 => [82, 83, 111, 86, 87]
  | 90 => [88, 84, 18, 19]
  | 91 => []
  | 92 => [92]
  | 93 => [112, 113, 114]
  | 94 => [91, 92, 95, 96]
  | 95 => [92, 115, 113, 114, 96]
  | 96 => [91, 92, 93, 94, 95, 96]
  | 97 => [97, 98, 99]
  | 98 => [38, 39]
  | 99 => [39]
  | 100 => [100, 98, 99]
  | 101 => [46, 47, 101, 50, 51]
  | 102 => [102, 103, 104]
  | 103 => [55, 56]
  | 104 => [56]
  | 105 => [105, 103, 104]
  | 106 => [106, 107, 108]
  | 107 => [55, 56]
  | 108 => [56]
  | 109 => [116, 107, 108]
  | 110 => [55, 56, 61, 62]
  | 111 => [82, 83, 111, 86, 87]
  | 112 => [112, 113, 114]
  | 113 => [91, 92]
  | 114 => [92]
  | 115 => [115, 113, 114]
  | 116 => [116, 107, 108]
  | _ => []

private def initIdx : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 12, 18, 19, 20]

private def vLit0 : List Int :=
  [2, 2, 2, 2, 6, 2, 4, 2, 2, 2, 2, 4, 2, 2, 6, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 2, 2, 2, 0, 0, 4, 0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 2, 0, 2, 4, 2, 2, 2, 2, 2, 2, 4, 0, 4, 2, 0, 0, 0, 2, 2, 2, 2, 0, 2, 2, 0, 0, 0, 2, 2, 2, 2, 2, 0, 0, 2, 0, 0, 0, 2, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 2, 0, 0, 2]
private def vLit1 : List Int :=
  [0, 6, 6, 12, 12, 16, 16, 6, 8, 22, 8, 16, 12, 6, 22, 8, 8, 16, 12, 8, 8, 0, 0, 0, 2, 0, 2, 0, 0, 2, 6, 4, 4, 0, 6, 0, 2, 8, 0, 0, 2, 4, 4, 8, 0, 0, 0, 0, 2, 2, 2, 2, 0, 4, 6, 0, 2, 2, 8, 8, 10, 6, 8, 2, 6, 6, 10, 2, 10, 2, 0, 0, 2, 4, 8, 4, 8, 0, 2, 10, 0, 2, 2, 2, 6, 8, 2, 4, 2, 6, 6, 0, 0, 2, 2, 4, 4, 2, 0, 0, 2, 4, 2, 2, 2, 4, 2, 2, 2, 4, 6, 6, 2, 0, 0, 2, 4]
private def vLit2 : List Int :=
  [2, 12, 16, 34, 42, 52, 46, 16, 26, 90, 28, 46, 56, 12, 62, 26, 40, 52, 34, 40, 28, 0, 0, 0, 4, 0, 2, 2, 2, 4, 16, 6, 10, 2, 12, 0, 2, 20, 0, 0, 2, 12, 10, 18, 0, 0, 0, 0, 2, 6, 2, 2, 0, 8, 16, 0, 2, 6, 20, 20, 30, 16, 26, 2, 16, 12, 24, 4, 24, 2, 0, 0, 4, 8, 26, 12, 18, 0, 6, 30, 0, 4, 2, 6, 16, 20, 8, 12, 2, 16, 28, 0, 0, 2, 8, 6, 12, 2, 0, 0, 2, 8, 6, 2, 2, 8, 6, 2, 2, 8, 16, 16, 2, 0, 0, 2, 8]
private def vLit3 : List Int :=
  [4, 26, 38, 108, 108, 158, 116, 38, 68, 284, 74, 116, 202, 26, 152, 68, 136, 158, 108, 136, 74, 0, 0, 0, 8, 0, 6, 4, 4, 8, 38, 14, 20, 4, 26, 0, 6, 44, 0, 0, 2, 28, 20, 42, 0, 0, 0, 0, 2, 10, 2, 2, 0, 12, 44, 0, 2, 10, 52, 44, 78, 38, 68, 2, 36, 26, 54, 8, 54, 2, 0, 0, 8, 18, 68, 28, 42, 0, 12, 78, 0, 8, 6, 12, 36, 52, 18, 28, 6, 44, 92, 0, 0, 2, 18, 14, 28, 2, 0, 0, 2, 12, 10, 2, 2, 12, 10, 2, 2, 12, 44, 44, 2, 0, 0, 2, 12]
private def vLit4 : List Int :=
  [8, 56, 84, 296, 280, 442, 270, 84, 164, 766, 178, 270, 626, 56, 350, 164, 422, 442, 296, 422, 178, 0, 0, 0, 18, 0, 12, 8, 8, 18, 84, 30, 44, 8, 56, 0, 12, 96, 0, 0, 2, 62, 44, 92, 0, 0, 0, 0, 2, 14, 2, 2, 0, 16, 108, 0, 2, 14, 124, 96, 186, 84, 164, 2, 80, 56, 118, 18, 118, 2, 0, 0, 18, 38, 164, 62, 92, 0, 26, 186, 0, 18, 12, 26, 80, 124, 42, 62, 12, 108, 286, 0, 0, 2, 42, 30, 62, 2, 0, 0, 2, 16, 14, 2, 2, 16, 14, 2, 2, 16, 108, 108, 2, 0, 0, 2, 16]
private def vLit5 : List Int :=
  [18, 120, 184, 786, 706, 1166, 606, 184, 374, 1884, 406, 606, 1790, 120, 780, 374, 1204, 1166, 786, 1204, 406, 0, 0, 0, 38, 0, 26, 18, 18, 38, 184, 64, 94, 18, 120, 0, 26, 208, 0, 0, 2, 136, 94, 200, 0, 0, 0, 0, 2, 18, 2, 2, 0, 20, 250, 0, 2, 18, 284, 208, 422, 184, 374, 2, 174, 120, 256, 38, 256, 2, 0, 0, 38, 82, 374, 136, 200, 0, 56, 422, 0, 38, 26, 56, 174, 284, 92, 136, 26, 250, 810, 0, 0, 2, 92, 64, 136, 2, 0, 0, 2, 20, 18, 2, 2, 20, 18, 2, 2, 20, 250, 250, 2, 0, 0, 2, 20]
private def vLit6 : List Int :=
  [38, 258, 398, 2010, 1734, 2980, 1332, 398, 830, 4388, 900, 1332, 4828, 258, 1708, 830, 3250, 2980, 2010, 3250, 900, 0, 0, 0, 82, 0, 56, 38, 38, 82, 398, 138, 202, 38, 258, 0, 56, 448, 0, 0, 2, 294, 202, 432, 0, 0, 0, 0, 2, 22, 2, 2, 0, 24, 560, 0, 2, 22, 632, 448, 934, 398, 830, 2, 376, 258, 552, 82, 552, 2, 0, 0, 82, 176, 830, 294, 432, 0, 120, 934, 0, 82, 56, 120, 376, 632, 200, 294, 56, 560, 2190, 0, 0, 2, 200, 138, 294, 2, 0, 0, 2, 24, 22, 2, 2, 24, 22, 2, 2, 24, 560, 560, 2, 0, 0, 2, 24]
private def vLit7 : List Int :=
  [82, 554, 858, 5010, 4202, 7418, 2896, 858, 1814, 9886, 1966, 2896, 12522, 554, 3706, 1814, 8442, 7418, 5010, 8442, 1966, 0, 0, 0, 176, 0, 120, 82, 82, 176, 858, 296, 434, 82, 554, 0, 120, 964, 0, 0, 2, 634, 434, 930, 0, 0, 0, 0, 2, 26, 2, 2, 0, 28, 1230, 0, 2, 26, 1384, 964, 2038, 858, 1814, 2, 810, 554, 1188, 176, 1188, 2, 0, 0, 176, 378, 1814, 634, 930, 0, 258, 2038, 0, 176, 120, 258, 810, 1384, 432, 634, 120, 1230, 5692, 0, 0, 2, 432, 296, 634, 2, 0, 0, 2, 28, 26, 2, 2, 28, 26, 2, 2, 28, 1230, 1230, 2, 0, 0, 2, 28]
private def vLit8 : List Int :=
  [176, 1190, 1846, 12256, 10044, 18124, 6260, 1846, 3932, 21834, 4260, 6260, 31560, 1190, 8002, 3932, 21304, 18124, 12256, 21304, 4260, 0, 0, 0, 378, 0, 258, 176, 176, 378, 1846, 636, 932, 176, 1190, 0, 258, 2072, 0, 0, 2, 1364, 932, 2000, 0, 0, 0, 0, 2, 30, 2, 2, 0, 32, 2674, 0, 2, 30, 3004, 2072, 4414, 1846, 3932, 2, 1742, 1190, 2554, 378, 2554, 2, 0, 0, 378, 812, 3932, 1364, 2000, 0, 554, 4414, 0, 378, 258, 554, 1742, 3004, 930, 1364, 258, 2674, 14382, 0, 0, 2, 930, 636, 1364, 2, 0, 0, 2, 32, 30, 2, 2, 32, 30, 2, 2, 32, 2674, 2674, 2, 0, 0, 2, 32]
private def vLit9 : List Int :=
  [378, 2556, 3968, 29534, 23766, 43636, 13490, 3968, 8486, 47654, 9192, 13490, 77852, 2556, 17234, 8486, 52616, 43636, 29534, 52616, 9192, 0, 0, 0, 812, 0, 554, 378, 378, 812, 3968, 1366, 2002, 378, 2556, 0, 554, 4452, 0, 0, 2, 2932, 2002, 4298, 0, 0, 0, 0, 2, 34, 2, 2, 0, 36, 5780, 0, 2, 34, 6488, 4452, 9522, 3968, 8486, 2, 3744, 2556, 5488, 812, 5488, 2, 0, 0, 812, 1744, 8486, 2932, 4298, 0, 1190, 9522, 0, 812, 554, 1190, 3744, 6488, 2000, 2932, 554, 5780, 35560, 0, 0, 2, 2000, 1366, 2932, 2, 0, 0, 2, 36, 34, 2, 2, 36, 34, 2, 2, 36, 5780, 5780, 2, 0, 0, 2, 36]
private def vLit10 : List Int :=
  [812, 5490, 8526, 70336, 55756, 103838, 29024, 8526, 18272, 103288, 19790, 29024, 188890, 5490, 37068, 18272, 127788, 103838, 70336, 127788, 19790, 0, 0, 0, 1744, 0, 1190, 812, 812, 1744, 8526, 2934, 4300, 812, 5490, 0, 1190, 9564, 0, 0, 2, 6300, 4300, 9234, 0, 0, 0, 0, 2, 38, 2, 2, 0, 40, 12456, 0, 2, 38, 13976, 9564, 20498, 8526, 18272, 2, 8044, 5490, 11790, 1744, 11790, 2, 0, 0, 1744, 3746, 18272, 6300, 9234, 0, 2556, 20498, 0, 1744, 1190, 2556, 8044, 13976, 4298, 6300, 1190, 12456, 86448, 0, 0, 2, 4298, 2934, 6300, 2, 0, 0, 2, 40, 38, 2, 2, 40, 38, 2, 2, 40, 12456, 12456, 2, 0, 0, 2, 40]

private def stateAt (k : Nat) : State :=
  if h : k < numStates then stateOf ⟨k, h⟩ else ⟨[0, 0, 0, 0], [0, 1, 2, 3], 0⟩

private def sumIdx (v : List Int) : List Nat → Int
  | [] => 0
  | j :: js => v.getD j 0 + sumIdx v js

private def stepVec (v : List Int) : List Int :=
  (List.finRange numStates).map fun i => sumIdx v (adjIdx i)

private def vec : Nat → List Int
  | 0 => vLit0
  | k + 1 => stepVec (vec k)

private lemma sumStates_map_eq_sumIdx (js : List Nat) (v : List Int) (f : State → Int)
    (h : ∀ j ∈ js, f (stateAt j) = v.getD j 0) :
    sumStates (js.map stateAt) f = sumIdx v js := by
  induction js with
  | nil => rfl
  | cons j rest ih =>
    simp only [List.map_cons, sumStates, sumIdx]
    rw [h j (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem j hx))]

private lemma sumStates_linear (xs : List State) (f g : State → Int) :
    sumStates xs (fun s => f s + g s) = sumStates xs f + sumStates xs g := by
  induction xs with
  | nil => rfl
  | cons s ss ih =>
    simp only [sumStates]
    rw [ih]
    omega

private lemma sumStates_smul (xs : List State) (c : Int) (f : State → Int) :
    sumStates xs (fun s => c * f s) = c * sumStates xs f := by
  induction xs with
  | nil => simp [sumStates]
  | cons s ss ih =>
    simp only [sumStates]
    rw [ih]
    exact (Int.mul_add c (f s) (sumStates ss f)).symm

private lemma sumStates_zero (xs : List State) (f : State → Int) (h : ∀ s ∈ xs, f s = 0) :
    sumStates xs f = 0 := by
  induction xs with
  | nil => rfl
  | cons s ss ih =>
    simp only [sumStates]
    rw [h s (List.mem_cons_self ..), ih (fun t ht => h t (List.mem_cons_of_mem s ht))]
    omega

set_option maxHeartbeats 1600000 in
private lemma next2_eq_map :
    ∀ i : Fin numStates, next2 (stateOf i) = (adjIdx i).map stateAt := by
  decide

private lemma adjIdx_lt :
    ∀ i : Fin numStates, ∀ j ∈ adjIdx i, j < numStates := by
  decide

private lemma initIdx_lt : ∀ j ∈ initIdx, j < numStates := by
  decide

set_option maxHeartbeats 800000 in
private lemma initial_eq_map : initial = initIdx.map stateAt := by
  decide

set_option maxHeartbeats 800000 in
private lemma closing_eq_vLit0 :
    ∀ i : Fin numStates, closing (stateOf i) = vLit0.getD i.val 0 := by
  decide

private lemma getD_stepVec (v : List Int) (i : Fin numStates) :
    (stepVec v).getD i.val 0 = sumIdx v (adjIdx i) := by
  unfold stepVec
  have hlen : i.val < ((List.finRange numStates).map fun x => sumIdx v (adjIdx x)).length := by
    simp [i.isLt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp

private lemma countFrom_eq_vec (k : Nat) :
    ∀ i : Fin numStates, countFrom k (stateOf i) = (vec k).getD i.val 0 := by
  induction k with
  | zero =>
    intro i
    exact closing_eq_vLit0 i
  | succ k ih =>
    intro i
    simp only [countFrom, vec, getD_stepVec]
    rw [next2_eq_map i]
    refine sumStates_map_eq_sumIdx (adjIdx i) (vec k) (countFrom k) ?_
    intro j hj
    have hjlt : j < numStates := adjIdx_lt i j hj
    simp only [stateAt, hjlt, dite_true]
    exact ih ⟨j, hjlt⟩

private lemma vec_1 : vec 1 = vLit1 := by change stepVec vLit0 = vLit1; decide
private lemma vec_2 : vec 2 = vLit2 := by change stepVec (vec 1) = vLit2; rw [vec_1]; decide
private lemma vec_3 : vec 3 = vLit3 := by change stepVec (vec 2) = vLit3; rw [vec_2]; decide
private lemma vec_4 : vec 4 = vLit4 := by change stepVec (vec 3) = vLit4; rw [vec_3]; decide
private lemma vec_5 : vec 5 = vLit5 := by change stepVec (vec 4) = vLit5; rw [vec_4]; decide
private lemma vec_6 : vec 6 = vLit6 := by change stepVec (vec 5) = vLit6; rw [vec_5]; decide
private lemma vec_7 : vec 7 = vLit7 := by change stepVec (vec 6) = vLit7; rw [vec_6]; decide
private lemma vec_8 : vec 8 = vLit8 := by change stepVec (vec 7) = vLit8; rw [vec_7]; decide
private lemma vec_9 : vec 9 = vLit9 := by change stepVec (vec 8) = vLit9; rw [vec_8]; decide
private lemma vec_10 : vec 10 = vLit10 := by change stepVec (vec 9) = vLit10; rw [vec_9]; decide

private lemma a_eq_sumIdx (n : Nat) (hn : 3 ≤ n) :
    a n = sumIdx (vec (n - 2)) initIdx := by
  unfold a
  rw [if_neg (by omega), initial_eq_map]
  refine sumStates_map_eq_sumIdx initIdx (vec (n - 2)) (countFrom (n - 2)) ?_
  intro j hj
  have hjlt : j < numStates := initIdx_lt j hj
  simp only [stateAt, hjlt, dite_true]
  exact countFrom_eq_vec (n - 2) ⟨j, hjlt⟩

private lemma a_0 : a 0 = 0 := rfl
private lemma a_1 : a 1 = 0 := rfl
private lemma a_2 : a 2 = 0 := rfl
private lemma a_3 : a 3 = 240 := by rw [a_eq_sumIdx 3 (by omega), show 3 - 2 = 1 by rfl, vec_1]; decide
private lemma a_4 : a 4 = 816 := by rw [a_eq_sumIdx 4 (by omega), show 4 - 2 = 2 by rfl, vec_2]; decide
private lemma a_5 : a 5 = 2400 := by rw [a_eq_sumIdx 5 (by omega), show 5 - 2 = 3 by rfl, vec_3]; decide
private lemma a_6 : a 6 = 6480 := by rw [a_eq_sumIdx 6 (by omega), show 6 - 2 = 4 by rfl, vec_4]; decide
private lemma a_7 : a 7 = 16660 := by rw [a_eq_sumIdx 7 (by omega), show 7 - 2 = 5 by rfl, vec_5]; decide
private lemma a_8 : a 8 = 41440 := by rw [a_eq_sumIdx 8 (by omega), show 8 - 2 = 6 by rfl, vec_6]; decide
private lemma a_9 : a 9 = 100836 := by rw [a_eq_sumIdx 9 (by omega), show 9 - 2 = 7 by rfl, vec_7]; decide
private lemma a_10 : a 10 = 241520 := by rw [a_eq_sumIdx 10 (by omega), show 10 - 2 = 8 by rfl, vec_8]; decide
private lemma a_11 : a 11 = 571692 := by rw [a_eq_sumIdx 11 (by omega), show 11 - 2 = 9 by rfl, vec_9]; decide

private def resid (k : Nat) (s : State) : Int :=
  countFrom (k + 9) s - 5 * countFrom (k + 8) s + 6 * countFrom (k + 7) s +
  4 * countFrom (k + 6) s - 7 * countFrom (k + 5) s - 5 * countFrom (k + 4) s +
  5 * countFrom (k + 3) s + 3 * countFrom (k + 2) s - countFrom (k + 1) s -
  countFrom k s

private lemma resid_succ (k : Nat) (s : State) :
    resid (k + 1) s = sumStates (next2 s) (resid k) := by
  unfold resid
  simp only [countFrom]
  have h1 : ∀ f g : State → Int,
      sumStates (next2 s) (fun t => f t - g t) =
        sumStates (next2 s) f - sumStates (next2 s) g := by
    intro f g
    have : (fun t => f t - g t) = (fun t => f t + (-1) * g t) := by
      funext t; omega
    rw [this, sumStates_linear, sumStates_smul]
    omega
  simp only [h1, sumStates_linear, sumStates_smul]

private lemma resid_one_lit :
    ∀ i : Fin numStates,
      vLit10.getD i.val 0 - 5 * vLit9.getD i.val 0 + 6 * vLit8.getD i.val 0 +
      4 * vLit7.getD i.val 0 - 7 * vLit6.getD i.val 0 - 5 * vLit5.getD i.val 0 +
      5 * vLit4.getD i.val 0 + 3 * vLit3.getD i.val 0 - vLit2.getD i.val 0 -
      vLit1.getD i.val 0 = 0 := by
  decide

private lemma resid_zero_of_pos (k : Nat) (hk : 1 ≤ k) :
    ∀ i : Fin numStates, resid k (stateOf i) = 0 := by
  induction k with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      intro i
      unfold resid
      change countFrom 10 (stateOf i) - 5 * countFrom 9 (stateOf i) +
        6 * countFrom 8 (stateOf i) + 4 * countFrom 7 (stateOf i) -
        7 * countFrom 6 (stateOf i) - 5 * countFrom 5 (stateOf i) +
        5 * countFrom 4 (stateOf i) + 3 * countFrom 3 (stateOf i) -
        countFrom 2 (stateOf i) - countFrom 1 (stateOf i) = 0
      simp only [countFrom_eq_vec, vec_1, vec_2, vec_3, vec_4, vec_5, vec_6, vec_7, vec_8, vec_9, vec_10]
      exact resid_one_lit i
    | succ m =>
      intro i
      rw [resid_succ (m + 1) (stateOf i), next2_eq_map i]
      refine sumStates_zero _ _ ?_
      intro s hs
      rw [List.mem_map] at hs
      obtain ⟨j, hj, rfl⟩ := hs
      have hjlt : j < numStates := adjIdx_lt i j hj
      simp only [stateAt, hjlt, dite_true]
      exact ih (by omega) ⟨j, hjlt⟩

private lemma clause1 :
    ∀ n : Nat, 11 < n →
      a n = 5 * a (n - 1) - 6 * a (n - 2) - 4 * a (n - 3) + 7 * a (n - 4) +
        5 * a (n - 5) - 5 * a (n - 6) - 3 * a (n - 7) + a (n - 8) + a (n - 9) := by
  intro n hn
  have h0 : a n - 5 * a (n - 1) + 6 * a (n - 2) + 4 * a (n - 3) - 7 * a (n - 4) -
      5 * a (n - 5) + 5 * a (n - 6) + 3 * a (n - 7) - a (n - 8) - a (n - 9) = 0 := by
    have hsub : ∀ d : Nat, d ≤ 9 → a (n - d) = sumStates initial (countFrom (n - 11 + (9 - d))) := by
      intro d hd
      unfold a
      rw [if_neg (by omega), show n - d - 2 = n - 11 + (9 - d) by omega]
    have hsub0 : a n = sumStates initial (countFrom (n - 11 + 9)) := by
      simpa using hsub 0 (by omega)
    rw [hsub0, hsub 1 (by omega), hsub 2 (by omega), hsub 3 (by omega),
      hsub 4 (by omega), hsub 5 (by omega), hsub 6 (by omega), hsub 7 (by omega),
      hsub 8 (by omega), hsub 9 (by omega)]
    simp only [show 9 - 1 = 8 by rfl, show 9 - 2 = 7 by rfl, show 9 - 3 = 6 by rfl,
      show 9 - 4 = 5 by rfl, show 9 - 5 = 4 by rfl, show 9 - 6 = 3 by rfl,
      show 9 - 7 = 2 by rfl, show 9 - 8 = 1 by rfl, show 9 - 9 = 0 by rfl, Nat.add_zero]
    have hlin :
        sumStates initial (resid (n - 11)) =
          sumStates initial (countFrom (n - 11 + 9)) -
          5 * sumStates initial (countFrom (n - 11 + 8)) +
          6 * sumStates initial (countFrom (n - 11 + 7)) +
          4 * sumStates initial (countFrom (n - 11 + 6)) -
          7 * sumStates initial (countFrom (n - 11 + 5)) -
          5 * sumStates initial (countFrom (n - 11 + 4)) +
          5 * sumStates initial (countFrom (n - 11 + 3)) +
          3 * sumStates initial (countFrom (n - 11 + 2)) -
          sumStates initial (countFrom (n - 11 + 1)) -
          sumStates initial (countFrom (n - 11)) := by
      unfold resid
      have hsub_s : ∀ f g : State → Int,
          sumStates initial (fun t => f t - g t) =
            sumStates initial f - sumStates initial g := by
        intro f g
        have : (fun t => f t - g t) = (fun t => f t + (-1) * g t) := by funext t; omega
        rw [this, sumStates_linear, sumStates_smul]; omega
      simp only [hsub_s, sumStates_linear, sumStates_smul]
    rw [← hlin, initial_eq_map]
    refine sumStates_zero _ _ ?_
    intro s hs
    rw [List.mem_map] at hs
    obtain ⟨j, hj, rfl⟩ := hs
    have hjlt : j < numStates := initIdx_lt j hj
    simp only [stateAt, hjlt, dite_true]
    exact resid_zero_of_pos (n - 11) (by omega) ⟨j, hjlt⟩
  omega

private lemma clause2 :
    ∀ n : Nat,
      a n - 5 * a (n - 1) + 6 * a (n - 2) + 4 * a (n - 3) - 7 * a (n - 4) -
        5 * a (n - 5) + 5 * a (n - 6) + 3 * a (n - 7) - a (n - 8) - a (n - 9) = numerator n := by
  intro n
  by_cases hlt : n < 12
  · interval_cases n
    · simp [a_0, numerator]
    · simp [a_1, a_0, numerator]
    · simp [a_2, a_1, a_0, numerator]
    · simp [a_3, a_2, a_1, a_0, numerator]
    · simp [a_4, a_3, a_2, a_1, a_0, numerator]
    · simp [a_5, a_4, a_3, a_2, a_1, a_0, numerator]
    · simp [a_6, a_5, a_4, a_3, a_2, a_1, a_0, numerator]
    · simp [a_7, a_6, a_5, a_4, a_3, a_2, a_1, a_0, numerator]
    · simp [a_8, a_7, a_6, a_5, a_4, a_3, a_2, a_1, a_0, numerator]
    · simp [a_9, a_8, a_7, a_6, a_5, a_4, a_3, a_2, a_1, a_0, numerator]
    · simp [a_10, a_9, a_8, a_7, a_6, a_5, a_4, a_3, a_2, a_1, numerator]
    · simp [a_11, a_10, a_9, a_8, a_7, a_6, a_5, a_4, a_3, a_2, numerator]
  · have h1 := clause1 n (by omega)
    have hnum : numerator n = 0 := by
      rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
      all_goals first | omega | rfl
    rw [hnum]
    omega

private def d6 (n : Nat) : Int :=
  a n - (2 * a (n - 1) + 3 * a (n - 2) - 2 * a (n - 3) - 6 * a (n - 4) -
    4 * a (n - 5) - a (n - 6) + 672 * (n : Int) - 1376 - 72 * (n : Int) ^ 2)

private lemma d6_zero (n : Nat) (hn : 9 ≤ n) : d6 n = 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h9 : n = 9
    · subst h9; unfold d6; simp [a_9, a_8, a_7, a_6, a_5, a_4, a_3]
    · by_cases h10 : n = 10
      · subst h10; unfold d6; simp [a_10, a_9, a_8, a_7, a_6, a_5, a_4]
      · by_cases h11 : n = 11
        · subst h11; unfold d6; simp [a_11, a_10, a_9, a_8, a_7, a_6, a_5]
        · have h12 : 11 < n := by omega
          have hr := clause1 n h12
          have hd1 := ih (n - 1) (by omega) (by omega)
          have hd2 := ih (n - 2) (by omega) (by omega)
          have hd3 := ih (n - 3) (by omega) (by omega)
          unfold d6 at hd1 hd2 hd3 ⊢
          have hcast1 : ((n - 1 : Nat) : Int) = (n : Int) - 1 := by omega
          have hcast2 : ((n - 2 : Nat) : Int) = (n : Int) - 2 := by omega
          have hcast3 : ((n - 3 : Nat) : Int) = (n : Int) - 3 := by omega
          have hm1 : n - 1 - 1 = n - 2 := by omega
          have hm2 : n - 1 - 2 = n - 3 := by omega
          have hm3 : n - 1 - 3 = n - 4 := by omega
          have hm4 : n - 1 - 4 = n - 5 := by omega
          have hm5 : n - 1 - 5 = n - 6 := by omega
          have hm6 : n - 1 - 6 = n - 7 := by omega
          have hn1 : n - 2 - 1 = n - 3 := by omega
          have hn2 : n - 2 - 2 = n - 4 := by omega
          have hn3 : n - 2 - 3 = n - 5 := by omega
          have hn4 : n - 2 - 4 = n - 6 := by omega
          have hn5 : n - 2 - 5 = n - 7 := by omega
          have hn6 : n - 2 - 6 = n - 8 := by omega
          have hp1 : n - 3 - 1 = n - 4 := by omega
          have hp2 : n - 3 - 2 = n - 5 := by omega
          have hp3 : n - 3 - 3 = n - 6 := by omega
          have hp4 : n - 3 - 4 = n - 7 := by omega
          have hp5 : n - 3 - 5 = n - 8 := by omega
          have hp6 : n - 3 - 6 = n - 9 := by omega
          rw [hm1, hm2, hm3, hm4, hm5, hm6, hcast1] at hd1
          rw [hn1, hn2, hn3, hn4, hn5, hn6, hcast2] at hd2
          rw [hp1, hp2, hp3, hp4, hp5, hp6, hcast3] at hd3
          linarith

private lemma clause3 :
    ∀ n : Nat, 9 ≤ n →
      a n = 2 * a (n - 1) + 3 * a (n - 2) - 2 * a (n - 3) - 6 * a (n - 4) -
        4 * a (n - 5) - a (n - 6) + 672 * (n : Int) - 1376 - 72 * (n : Int) ^ 2 := by
  intro n hn
  have h := d6_zero n hn
  unfold d6 at h
  omega

end OMA.Proof_oeis_a124352

theorem OMA.solution : type_of% @OMA.S_oeis_a124352.main :=
  ⟨OMA.Proof_oeis_a124352.clause1,
   OMA.Proof_oeis_a124352.clause2,
   OMA.Proof_oeis_a124352.clause3⟩
