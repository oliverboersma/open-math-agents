import FormalConjectures.Wikipedia.UnionClosed
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Fin.Tuple.Embedding

/-! The minimum-five case of the twelve-element union-closed sets theorem. The weights are those of Vučković and Živković, The 12-Element Case of Frankl’s Conjecture (2017), Table I, rows 29 and 33. The integer certificates below were generated afresh. The reduction to twelve coordinates and the direct small-family arguments are adapted from @steveDOTdigital, PR 4706. -/
namespace FranklLocal

lemma layer5_0 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (first : ∀ i, v i ≤ v (i ||| 31))
    (small : ∀ i ∈ ([1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30] : List ℕ), v i=0)
    (fixed : ∀ i ∈ ([0,31] : List ℕ), v i=1) :
    (-14 : ℤ) ≤ (-17) * v 0 + (-13) * v 1 + (-13) * v 2 + (-9) * v 3 + (-13) * v 4 + (-9) * v 5 + (-9) * v 6 + (-5) * v 7 + (-13) * v 8 + (-9) * v 9 + (-9) * v 10 + (-5) * v 11 + (-9) * v 12 + (-5) * v 13 + (-5) * v 14 + (-1) * v 15 + (-13) * v 16 + (-9) * v 17 + (-9) * v 18 + (-5) * v 19 + (-9) * v 20 + (-5) * v 21 + (-5) * v 22 + (-1) * v 23 + (-9) * v 24 + (-5) * v 25 + (-5) * v 26 + (-1) * v 27 + (-5) * v 28 + (-1) * v 29 + (-1) * v 30 + 3 * v 31 := by
  have low (i : ℕ) : -v i ≤ 0 := by rcases bit i with h|h <;> omega
  have high (i : ℕ) : v i ≤ 1 := by rcases bit i with h|h <;> omega
  have row285 : v 0 - v 31 ≤ 0 := sub_nonpos.mpr (first 0)
  have row288 : v 1 ≤ 0 := (small 1 (by decide)).le
  have row290 : v 2 ≤ 0 := (small 2 (by decide)).le
  have row292 : v 3 ≤ 0 := (small 3 (by decide)).le
  have row294 : v 4 ≤ 0 := (small 4 (by decide)).le
  have row296 : v 5 ≤ 0 := (small 5 (by decide)).le
  have row298 : v 6 ≤ 0 := (small 6 (by decide)).le
  have row300 : v 7 ≤ 0 := (small 7 (by decide)).le
  have row302 : v 8 ≤ 0 := (small 8 (by decide)).le
  have row304 : v 9 ≤ 0 := (small 9 (by decide)).le
  have row306 : v 10 ≤ 0 := (small 10 (by decide)).le
  have row308 : v 11 ≤ 0 := (small 11 (by decide)).le
  have row310 : v 12 ≤ 0 := (small 12 (by decide)).le
  have row312 : v 13 ≤ 0 := (small 13 (by decide)).le
  have row314 : v 14 ≤ 0 := (small 14 (by decide)).le
  have row316 : v 15 ≤ 0 := (small 15 (by decide)).le
  have row318 : v 16 ≤ 0 := (small 16 (by decide)).le
  have row320 : v 17 ≤ 0 := (small 17 (by decide)).le
  have row322 : v 18 ≤ 0 := (small 18 (by decide)).le
  have row324 : v 19 ≤ 0 := (small 19 (by decide)).le
  have row326 : v 20 ≤ 0 := (small 20 (by decide)).le
  have row328 : v 21 ≤ 0 := (small 21 (by decide)).le
  have row330 : v 22 ≤ 0 := (small 22 (by decide)).le
  have row332 : v 23 ≤ 0 := (small 23 (by decide)).le
  have row334 : v 24 ≤ 0 := (small 24 (by decide)).le
  have row336 : v 25 ≤ 0 := (small 25 (by decide)).le
  have row338 : v 26 ≤ 0 := (small 26 (by decide)).le
  have row340 : v 27 ≤ 0 := (small 27 (by decide)).le
  have row342 : v 28 ≤ 0 := (small 28 (by decide)).le
  have row344 : v 29 ≤ 0 := (small 29 (by decide)).le
  have row346 : v 30 ≤ 0 := (small 30 (by decide)).le
  by_contra! fail
  have bad : (-17) * v 0 + (-13) * v 1 + (-13) * v 2 + (-9) * v 3 + (-13) * v 4 + (-9) * v 5 + (-9) * v 6 + (-5) * v 7 + (-13) * v 8 + (-9) * v 9 + (-9) * v 10 + (-5) * v 11 + (-9) * v 12 + (-5) * v 13 + (-5) * v 14 + (-1) * v 15 + (-13) * v 16 + (-9) * v 17 + (-9) * v 18 + (-5) * v 19 + (-9) * v 20 + (-5) * v 21 + (-5) * v 22 + (-1) * v 23 + (-9) * v 24 + (-5) * v 25 + (-5) * v 26 + (-1) * v 27 + (-5) * v 28 + (-1) * v 29 + (-1) * v 30 + 3 * v 31 ≤ (-15 : ℤ) := by omega
  have falseBound : (0 : ℤ) ≤ (-1 : ℤ) := by
    linear_combination bad + 17 * row285 + 13 * row288 + 13 * row290 + 9 * row292 + 13 * row294 + 9 * row296 + 9 * row298 + 5 * row300 + 13 * row302 + 9 * row304 + 9 * row306 + 5 * row308 + 9 * row310 + 5 * row312 + 5 * row314 + row316 + 13 * row318 + 9 * row320 + 9 * row322 + 5 * row324 + 9 * row326 + 5 * row328 + 5 * row330 + row332 + 9 * row334 + 5 * row336 + 5 * row338 + row340 + 5 * row342 + row344 + row346 + 14 * (high 31)
  omega

lemma layer5_1 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (first : ∀ i, v i ≤ v (i ||| 31))
    (small : ∀ i ∈ ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30] : List ℕ), v i=0)
    (apart : ∀ i j, (i,j) ∈ ([(15,23),(15,27),(15,29),(15,30),(23,27),(23,29),(23,30),(27,29),(27,30),(29,30)] : List (ℕ × ℕ)) → v i + v j ≤ 1)
    (fixed : ∀ i ∈ ([31] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-15) * v 0 + (-11) * v 1 + (-11) * v 2 + (-7) * v 3 + (-11) * v 4 + (-7) * v 5 + (-7) * v 6 + (-3) * v 7 + (-11) * v 8 + (-7) * v 9 + (-7) * v 10 + (-3) * v 11 + (-7) * v 12 + (-3) * v 13 + (-3) * v 14 + 1 * v 15 + (-11) * v 16 + (-7) * v 17 + (-7) * v 18 + (-3) * v 19 + (-7) * v 20 + (-3) * v 21 + (-3) * v 22 + 1 * v 23 + (-7) * v 24 + (-3) * v 25 + (-3) * v 26 + 1 * v 27 + (-3) * v 28 + 1 * v 29 + 1 * v 30 + 5 * v 31 := by
  have low (i : ℕ) : -v i ≤ 0 := by rcases bit i with h|h <;> omega
  have high (i : ℕ) : v i ≤ 1 := by rcases bit i with h|h <;> omega
  have row296 : v 0 ≤ 0 := (small 0 (by decide)).le
  have row298 : v 1 ≤ 0 := (small 1 (by decide)).le
  have row300 : v 2 ≤ 0 := (small 2 (by decide)).le
  have row302 : v 3 ≤ 0 := (small 3 (by decide)).le
  have row304 : v 4 ≤ 0 := (small 4 (by decide)).le
  have row306 : v 5 ≤ 0 := (small 5 (by decide)).le
  have row308 : v 6 ≤ 0 := (small 6 (by decide)).le
  have row310 : v 7 ≤ 0 := (small 7 (by decide)).le
  have row312 : v 8 ≤ 0 := (small 8 (by decide)).le
  have row314 : v 9 ≤ 0 := (small 9 (by decide)).le
  have row316 : v 10 ≤ 0 := (small 10 (by decide)).le
  have row318 : v 11 ≤ 0 := (small 11 (by decide)).le
  have row320 : v 12 ≤ 0 := (small 12 (by decide)).le
  have row322 : v 13 ≤ 0 := (small 13 (by decide)).le
  have row324 : v 14 ≤ 0 := (small 14 (by decide)).le
  have row328 : v 16 ≤ 0 := (small 16 (by decide)).le
  have row330 : v 17 ≤ 0 := (small 17 (by decide)).le
  have row332 : v 18 ≤ 0 := (small 18 (by decide)).le
  have row334 : v 19 ≤ 0 := (small 19 (by decide)).le
  have row336 : v 20 ≤ 0 := (small 20 (by decide)).le
  have row338 : v 21 ≤ 0 := (small 21 (by decide)).le
  have row340 : v 22 ≤ 0 := (small 22 (by decide)).le
  have row344 : v 24 ≤ 0 := (small 24 (by decide)).le
  have row346 : v 25 ≤ 0 := (small 25 (by decide)).le
  have row348 : v 26 ≤ 0 := (small 26 (by decide)).le
  have row352 : v 28 ≤ 0 := (small 28 (by decide)).le
  have row357 : -(v 31) ≤ -1 := neg_le_neg (fixed 31 (by decide)).ge
  by_contra! fail
  have bad : (-15) * v 0 + (-11) * v 1 + (-11) * v 2 + (-7) * v 3 + (-11) * v 4 + (-7) * v 5 + (-7) * v 6 + (-3) * v 7 + (-11) * v 8 + (-7) * v 9 + (-7) * v 10 + (-3) * v 11 + (-7) * v 12 + (-3) * v 13 + (-3) * v 14 + 1 * v 15 + (-11) * v 16 + (-7) * v 17 + (-7) * v 18 + (-3) * v 19 + (-7) * v 20 + (-3) * v 21 + (-3) * v 22 + 1 * v 23 + (-7) * v 24 + (-3) * v 25 + (-3) * v 26 + 1 * v 27 + (-3) * v 28 + 1 * v 29 + 1 * v 30 + 5 * v 31 ≤ (-1 : ℤ) := by omega
  have falseBound : (0 : ℤ) ≤ (-6 : ℤ) := by
    linear_combination bad + 15 * row296 + 11 * row298 + 11 * row300 + 7 * row302 + 11 * row304 + 7 * row306 + 7 * row308 + 3 * row310 + 11 * row312 + 7 * row314 + 7 * row316 + 3 * row318 + 7 * row320 + 3 * row322 + 3 * row324 + 11 * row328 + 7 * row330 + 7 * row332 + 3 * row334 + 7 * row336 + 3 * row338 + 3 * row340 + 7 * row344 + 3 * row346 + 3 * row348 + 3 * row352 + 5 * row357 + (low 15) + (low 23) + (low 27) + (low 29) + (low 30)
  omega

lemma layer5_2 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (first : ∀ i, v i ≤ v (i ||| 31))
    (small : ∀ i ∈ ([0,1,2,3,4,5,6,8,9,10,12,16,17,18,20,24] : List ℕ), v i=0)
    (apart : ∀ i j, (i,j) ∈ ([(7,11),(7,13),(7,14),(7,19),(7,21),(7,22),(11,13),(11,14),(11,19),(11,25),(11,26),(13,14),(13,21),(13,25),(13,28),(14,22),(14,26),(14,28),(19,21),(19,22),(19,25),(19,26),(21,22),(21,25),(21,28),(22,26),(22,28),(25,26),(25,28),(26,28)] : List (ℕ × ℕ)) → v i + v j ≤ 1)
    (fixed : ∀ i ∈ ([31] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-13) * v 0 + (-9) * v 1 + (-9) * v 2 + (-5) * v 3 + (-9) * v 4 + (-5) * v 5 + (-5) * v 6 + (-1) * v 7 + (-9) * v 8 + (-5) * v 9 + (-5) * v 10 + (-1) * v 11 + (-5) * v 12 + (-1) * v 13 + (-1) * v 14 + 3 * v 15 + (-9) * v 16 + (-5) * v 17 + (-5) * v 18 + (-1) * v 19 + (-5) * v 20 + (-1) * v 21 + (-1) * v 22 + 3 * v 23 + (-5) * v 24 + (-1) * v 25 + (-1) * v 26 + 3 * v 27 + (-1) * v 28 + 3 * v 29 + 3 * v 30 + 7 * v 31 := by
  have low (i : ℕ) : -v i ≤ 0 := by rcases bit i with h|h <;> omega
  have high (i : ℕ) : v i ≤ 1 := by rcases bit i with h|h <;> omega
  have row116 : v 7 + v 21 ≤ 1 := apart 7 21 (by decide)
  have row165 : v 11 + v 13 ≤ 1 := apart 11 13 (by decide)
  have row231 : v 14 + v 28 ≤ 1 := apart 14 28 (by decide)
  have row265 : v 19 + v 22 ≤ 1 := apart 19 22 (by decide)
  have row304 : v 25 + v 26 ≤ 1 := apart 25 26 (by decide)
  have row316 : v 0 ≤ 0 := (small 0 (by decide)).le
  have row318 : v 1 ≤ 0 := (small 1 (by decide)).le
  have row320 : v 2 ≤ 0 := (small 2 (by decide)).le
  have row322 : v 3 ≤ 0 := (small 3 (by decide)).le
  have row324 : v 4 ≤ 0 := (small 4 (by decide)).le
  have row326 : v 5 ≤ 0 := (small 5 (by decide)).le
  have row328 : v 6 ≤ 0 := (small 6 (by decide)).le
  have row331 : v 8 ≤ 0 := (small 8 (by decide)).le
  have row333 : v 9 ≤ 0 := (small 9 (by decide)).le
  have row335 : v 10 ≤ 0 := (small 10 (by decide)).le
  have row338 : v 12 ≤ 0 := (small 12 (by decide)).le
  have row343 : v 16 ≤ 0 := (small 16 (by decide)).le
  have row345 : v 17 ≤ 0 := (small 17 (by decide)).le
  have row347 : v 18 ≤ 0 := (small 18 (by decide)).le
  have row350 : v 20 ≤ 0 := (small 20 (by decide)).le
  have row355 : v 24 ≤ 0 := (small 24 (by decide)).le
  have row362 : -(v 31) ≤ -1 := neg_le_neg (fixed 31 (by decide)).ge
  by_contra! fail
  have bad : (-13) * v 0 + (-9) * v 1 + (-9) * v 2 + (-5) * v 3 + (-9) * v 4 + (-5) * v 5 + (-5) * v 6 + (-1) * v 7 + (-9) * v 8 + (-5) * v 9 + (-5) * v 10 + (-1) * v 11 + (-5) * v 12 + (-1) * v 13 + (-1) * v 14 + 3 * v 15 + (-9) * v 16 + (-5) * v 17 + (-5) * v 18 + (-1) * v 19 + (-5) * v 20 + (-1) * v 21 + (-1) * v 22 + 3 * v 23 + (-5) * v 24 + (-1) * v 25 + (-1) * v 26 + 3 * v 27 + (-1) * v 28 + 3 * v 29 + 3 * v 30 + 7 * v 31 ≤ (-1 : ℤ) := by omega
  have falseBound : (0 : ℤ) ≤ (-3 : ℤ) := by
    linear_combination bad + row116 + row165 + row231 + row265 + row304 + 13 * row316 + 9 * row318 + 9 * row320 + 5 * row322 + 9 * row324 + 5 * row326 + 5 * row328 + 9 * row331 + 5 * row333 + 5 * row335 + 5 * row338 + 9 * row343 + 5 * row345 + 5 * row347 + 5 * row350 + 5 * row355 + 7 * row362 + 3 * (low 15) + 3 * (low 23) + 3 * (low 27) + 3 * (low 29) + 3 * (low 30)
  omega

lemma layer5_3 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (first : ∀ i, v i ≤ v (i ||| 31))
    (small : ∀ i ∈ ([0,1,2,4,8,16] : List ℕ), v i=0)
    (apart : ∀ i j, (i,j) ∈ ([(3,5),(3,6),(3,9),(3,10),(3,17),(3,18),(5,6),(5,9),(5,12),(5,17),(5,20),(6,10),(6,12),(6,18),(6,20),(9,10),(9,12),(9,17),(9,24),(10,12),(10,18),(10,24),(12,20),(12,24),(17,18),(17,20),(17,24),(18,20),(18,24),(20,24)] : List (ℕ × ℕ)) → v i + v j ≤ 1)
    (fixed : ∀ i ∈ ([31] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-11) * v 0 + (-7) * v 1 + (-7) * v 2 + (-3) * v 3 + (-7) * v 4 + (-3) * v 5 + (-3) * v 6 + 1 * v 7 + (-7) * v 8 + (-3) * v 9 + (-3) * v 10 + 1 * v 11 + (-3) * v 12 + 1 * v 13 + 1 * v 14 + 5 * v 15 + (-7) * v 16 + (-3) * v 17 + (-3) * v 18 + 1 * v 19 + (-3) * v 20 + 1 * v 21 + 1 * v 22 + 5 * v 23 + (-3) * v 24 + 1 * v 25 + 1 * v 26 + 5 * v 27 + 1 * v 28 + 5 * v 29 + 5 * v 30 + 9 * v 31 := by
  have low (i : ℕ) : -v i ≤ 0 := by rcases bit i with h|h <;> omega
  have high (i : ℕ) : v i ≤ 1 := by rcases bit i with h|h <;> omega
  have row30 : v 3 + v 5 - v 7 ≤ 1 := join 3 5
  have row31 : v 3 + v 5 ≤ 1 := apart 3 5 (by decide)
  have row33 : v 3 + v 6 ≤ 1 := apart 3 6 (by decide)
  have row35 : v 3 + v 9 - v 11 ≤ 1 := join 3 9
  have row36 : v 3 + v 9 ≤ 1 := apart 3 9 (by decide)
  have row38 : v 3 + v 10 ≤ 1 := apart 3 10 (by decide)
  have row39 : v 3 + v 12 - v 15 ≤ 1 := join 3 12
  have row40 : v 3 + v 13 - v 15 ≤ 1 := join 3 13
  have row43 : v 3 + v 17 - v 19 ≤ 1 := join 3 17
  have row44 : v 3 + v 17 ≤ 1 := apart 3 17 (by decide)
  have row46 : v 3 + v 18 ≤ 1 := apart 3 18 (by decide)
  have row47 : v 3 + v 20 - v 23 ≤ 1 := join 3 20
  have row48 : v 3 + v 21 - v 23 ≤ 1 := join 3 21
  have row50 : v 3 + v 24 - v 27 ≤ 1 := join 3 24
  have row52 : v 3 + v 26 - v 27 ≤ 1 := join 3 26
  have row68 : v 5 + v 6 - v 7 ≤ 1 := join 5 6
  have row69 : v 5 + v 6 ≤ 1 := apart 5 6 (by decide)
  have row71 : v 5 + v 9 - v 13 ≤ 1 := join 5 9
  have row72 : v 5 + v 9 ≤ 1 := apart 5 9 (by decide)
  have row73 : v 5 + v 10 - v 15 ≤ 1 := join 5 10
  have row74 : v 5 + v 11 - v 15 ≤ 1 := join 5 11
  have row76 : v 5 + v 12 ≤ 1 := apart 5 12 (by decide)
  have row79 : v 5 + v 17 - v 21 ≤ 1 := join 5 17
  have row80 : v 5 + v 17 ≤ 1 := apart 5 17 (by decide)
  have row81 : v 5 + v 18 - v 23 ≤ 1 := join 5 18
  have row84 : v 5 + v 20 ≤ 1 := apart 5 20 (by decide)
  have row86 : v 5 + v 24 - v 29 ≤ 1 := join 5 24
  have row93 : v 6 + v 9 - v 15 ≤ 1 := join 6 9
  have row94 : v 6 + v 10 - v 14 ≤ 1 := join 6 10
  have row95 : v 6 + v 10 ≤ 1 := apart 6 10 (by decide)
  have row96 : v 6 + v 11 - v 15 ≤ 1 := join 6 11
  have row98 : v 6 + v 12 ≤ 1 := apart 6 12 (by decide)
  have row101 : v 6 + v 17 - v 23 ≤ 1 := join 6 17
  have row103 : v 6 + v 18 ≤ 1 := apart 6 18 (by decide)
  have row105 : v 6 + v 20 - v 22 ≤ 1 := join 6 20
  have row106 : v 6 + v 20 ≤ 1 := apart 6 20 (by decide)
  have row108 : v 6 + v 24 - v 30 ≤ 1 := join 6 24
  have row143 : v 9 + v 10 - v 11 ≤ 1 := join 9 10
  have row144 : v 9 + v 10 ≤ 1 := apart 9 10 (by decide)
  have row145 : v 9 + v 12 - v 13 ≤ 1 := join 9 12
  have row146 : v 9 + v 12 ≤ 1 := apart 9 12 (by decide)
  have row149 : v 9 + v 17 - v 25 ≤ 1 := join 9 17
  have row150 : v 9 + v 17 ≤ 1 := apart 9 17 (by decide)
  have row151 : v 9 + v 18 - v 27 ≤ 1 := join 9 18
  have row153 : v 9 + v 20 - v 29 ≤ 1 := join 9 20
  have row154 : v 9 + v 21 - v 29 ≤ 1 := join 9 21
  have row158 : v 9 + v 24 ≤ 1 := apart 9 24 (by decide)
  have row159 : v 9 + v 26 - v 27 ≤ 1 := join 9 26
  have row166 : v 10 + v 17 - v 27 ≤ 1 := join 10 17
  have row198 : v 12 + v 18 - v 30 ≤ 1 := join 12 18
  have row201 : v 12 + v 20 ≤ 1 := apart 12 20 (by decide)
  have row268 : v 18 + v 24 ≤ 1 := apart 18 24 (by decide)
  have row281 : v 20 + v 24 - v 28 ≤ 1 := join 20 24
  have row316 : v 0 ≤ 0 := (small 0 (by decide)).le
  have row318 : v 1 ≤ 0 := (small 1 (by decide)).le
  have row320 : v 2 ≤ 0 := (small 2 (by decide)).le
  have row323 : v 4 ≤ 0 := (small 4 (by decide)).le
  have row328 : v 8 ≤ 0 := (small 8 (by decide)).le
  have row337 : v 16 ≤ 0 := (small 16 (by decide)).le
  have row352 : -(v 31) ≤ -1 := neg_le_neg (fixed 31 (by decide)).ge
  by_contra! fail
  have bad : (-11) * v 0 + (-7) * v 1 + (-7) * v 2 + (-3) * v 3 + (-7) * v 4 + (-3) * v 5 + (-3) * v 6 + 1 * v 7 + (-7) * v 8 + (-3) * v 9 + (-3) * v 10 + 1 * v 11 + (-3) * v 12 + 1 * v 13 + 1 * v 14 + 5 * v 15 + (-7) * v 16 + (-3) * v 17 + (-3) * v 18 + 1 * v 19 + (-3) * v 20 + 1 * v 21 + 1 * v 22 + 5 * v 23 + (-3) * v 24 + 1 * v 25 + 1 * v 26 + 5 * v 27 + 1 * v 28 + 5 * v 29 + 5 * v 30 + 9 * v 31 ≤ (-1 : ℤ) := by omega
  rcases bit 3 with h3 | h3
  · rcases bit 5 with h5 | h5
    · rcases bit 6 with h6 | h6
      · rcases bit 9 with h9 | h9
        · have falseBound : (0 : ℤ) ≤ (-1 : ℤ) := by
            linear_combination bad + 3 * row166 + row198 + 2 * row201 + 2 * row268 + row281 + 11 * row316 + 7 * row318 + 7 * row320 + 7 * row323 + 7 * row328 + 7 * row337 + 9 * row352 + 9997 * (low 3) + 9997 * (low 5) + 9997 * (low 6) + (low 7) + 9997 * (low 9) + (low 11) + (low 13) + (low 14) + 5 * (low 15) + (low 19) + (low 21) + (low 22) + 5 * (low 23) + (low 25) + (low 26) + 2 * (low 27) + 5 * (low 29) + 4 * (low 30) + 10000 * h3 + 10000 * h5 + 10000 * h6 + 10000 * h9
          omega
        · have falseBound : (0 : ℤ) ≤ (-7 : ℤ) := by
            linear_combination bad + row143 + 2 * row144 + row145 + 2 * row146 + row149 + 2 * row150 + 3 * row151 + 3 * row153 + 2 * row154 + 3 * row158 + 2 * row159 + 11 * row316 + 7 * row318 + 7 * row320 + 7 * row323 + 7 * row328 + 7 * row337 + 9 * row352 + 9997 * (low 3) + 9997 * (low 5) + 9997 * (low 6) + (low 7) + 9981 * (high 9) + (low 14) + 5 * (low 15) + (low 19) + 3 * (low 21) + (low 22) + 5 * (low 23) + 3 * (low 26) + (low 28) + 5 * (low 30) + 10000 * h3 + 10000 * h5 + 10000 * h6 - 10000 * h9
          omega
      · have falseBound : (0 : ℤ) ≤ (-7 : ℤ) := by
          linear_combination bad + 3 * row93 + row94 + 2 * row95 + 2 * row96 + 9983 * row98 + 3 * row101 + 3 * row103 + row105 + 2 * row106 + 3 * row108 + 11 * row316 + 7 * row318 + 7 * row320 + 7 * row323 + 7 * row328 + 7 * row337 + 9 * row352 + 9997 * (low 3) + 9997 * (low 5) + (low 7) + 3 * (low 11) + 9980 * (low 12) + (low 13) + (low 19) + (low 21) + 2 * (low 23) + (low 25) + (low 26) + 5 * (low 27) + (low 28) + 5 * (low 29) + 2 * (low 30) + 10000 * h3 + 10000 * h5 - 10000 * h6
        omega
    · have falseBound : (0 : ℤ) ≤ (-7 : ℤ) := by
        linear_combination bad + row68 + 2 * row69 + row71 + 2 * row72 + 3 * row73 + 2 * row74 + 3 * row76 + row79 + 2 * row80 + 5 * row81 + 3 * row84 + 5 * row86 + 11 * row316 + 7 * row318 + 7 * row320 + 7 * row323 + 7 * row328 + 7 * row337 + 9 * row352 + 9997 * (low 3) + 9973 * (high 5) + 3 * (low 11) + (low 14) + 2 * (low 18) + (low 19) + (low 22) + 2 * (low 24) + (low 25) + (low 26) + 5 * (low 27) + (low 28) + 5 * (low 30) + 10000 * h3 - 10000 * h5
      omega
  · have falseBound : (0 : ℤ) ≤ (-7 : ℤ) := by
      linear_combination bad + row30 + 2 * row31 + 3 * row33 + row35 + 2 * row36 + 3 * row38 + 3 * row39 + 2 * row40 + row43 + 2 * row44 + 3 * row46 + 3 * row47 + 2 * row48 + 3 * row50 + 2 * row52 + 11 * row316 + 7 * row318 + 7 * row320 + 7 * row323 + 7 * row328 + 7 * row337 + 9 * row352 + 9970 * (high 3) + 3 * (low 13) + (low 14) + 3 * (low 21) + (low 22) + (low 25) + 3 * (low 26) + (low 28) + 5 * (low 29) + 5 * (low 30) - 10000 * h3
    omega

lemma layer5_4 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (first : ∀ i, v i ≤ v (i ||| 31))
    (small : ∀ i ∈ ([0] : List ℕ), v i=0)
    (apart : ∀ i j, (i,j) ∈ ([(1,2),(1,4),(1,8),(1,16),(2,4),(2,8),(2,16),(4,8),(4,16),(8,16)] : List (ℕ × ℕ)) → v i + v j ≤ 1)
    (fixed : ∀ i ∈ ([31] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-9) * v 0 + (-5) * v 1 + (-5) * v 2 + (-1) * v 3 + (-5) * v 4 + (-1) * v 5 + (-1) * v 6 + 3 * v 7 + (-5) * v 8 + (-1) * v 9 + (-1) * v 10 + 3 * v 11 + (-1) * v 12 + 3 * v 13 + 3 * v 14 + 7 * v 15 + (-5) * v 16 + (-1) * v 17 + (-1) * v 18 + 3 * v 19 + (-1) * v 20 + 3 * v 21 + 3 * v 22 + 7 * v 23 + (-1) * v 24 + 3 * v 25 + 3 * v 26 + 7 * v 27 + 3 * v 28 + 7 * v 29 + 7 * v 30 + 11 * v 31 := by
  have low (i : ℕ) : -v i ≤ 0 := by rcases bit i with h|h <;> omega
  have high (i : ℕ) : v i ≤ 1 := by rcases bit i with h|h <;> omega
  have row1 : v 1 + v 2 ≤ 1 := apart 1 2 (by decide)
  have row3 : v 1 + v 4 ≤ 1 := apart 1 4 (by decide)
  have row4 : v 1 + v 6 - v 7 ≤ 1 := join 1 6
  have row6 : v 1 + v 8 ≤ 1 := apart 1 8 (by decide)
  have row7 : v 1 + v 10 - v 11 ≤ 1 := join 1 10
  have row8 : v 1 + v 12 - v 13 ≤ 1 := join 1 12
  have row9 : v 1 + v 14 - v 15 ≤ 1 := join 1 14
  have row11 : v 1 + v 16 ≤ 1 := apart 1 16 (by decide)
  have row12 : v 1 + v 18 - v 19 ≤ 1 := join 1 18
  have row13 : v 1 + v 20 - v 21 ≤ 1 := join 1 20
  have row14 : v 1 + v 22 - v 23 ≤ 1 := join 1 22
  have row15 : v 1 + v 24 - v 25 ≤ 1 := join 1 24
  have row16 : v 1 + v 26 - v 27 ≤ 1 := join 1 26
  have row20 : v 2 + v 4 ≤ 1 := apart 2 4 (by decide)
  have row21 : v 2 + v 5 - v 7 ≤ 1 := join 2 5
  have row23 : v 2 + v 8 ≤ 1 := apart 2 8 (by decide)
  have row24 : v 2 + v 9 - v 11 ≤ 1 := join 2 9
  have row25 : v 2 + v 12 - v 14 ≤ 1 := join 2 12
  have row28 : v 2 + v 16 ≤ 1 := apart 2 16 (by decide)
  have row29 : v 2 + v 17 - v 19 ≤ 1 := join 2 17
  have row30 : v 2 + v 20 - v 22 ≤ 1 := join 2 20
  have row32 : v 2 + v 24 - v 26 ≤ 1 := join 2 24
  have row34 : v 2 + v 28 - v 30 ≤ 1 := join 2 28
  have row36 : v 3 + v 4 - v 7 ≤ 1 := join 3 4
  have row39 : v 3 + v 8 - v 11 ≤ 1 := join 3 8
  have row46 : v 3 + v 17 - v 19 ≤ 1 := join 3 17
  have row47 : v 3 + v 18 - v 19 ≤ 1 := join 3 18
  have row58 : v 4 + v 8 ≤ 1 := apart 4 8 (by decide)
  have row59 : v 4 + v 9 - v 13 ≤ 1 := join 4 9
  have row60 : v 4 + v 10 - v 14 ≤ 1 := join 4 10
  have row63 : v 4 + v 16 ≤ 1 := apart 4 16 (by decide)
  have row64 : v 4 + v 17 - v 21 ≤ 1 := join 4 17
  have row65 : v 4 + v 18 - v 22 ≤ 1 := join 4 18
  have row66 : v 4 + v 19 - v 23 ≤ 1 := join 4 19
  have row67 : v 4 + v 24 - v 28 ≤ 1 := join 4 24
  have row68 : v 4 + v 25 - v 29 ≤ 1 := join 4 25
  have row71 : v 5 + v 6 - v 7 ≤ 1 := join 5 6
  have row73 : v 5 + v 9 - v 13 ≤ 1 := join 5 9
  have row80 : v 5 + v 18 - v 23 ≤ 1 := join 5 18
  have row92 : v 6 + v 10 - v 14 ≤ 1 := join 6 10
  have row97 : v 6 + v 17 - v 23 ≤ 1 := join 6 17
  have row130 : v 8 + v 16 ≤ 1 := apart 8 16 (by decide)
  have row145 : v 9 + v 20 - v 29 ≤ 1 := join 9 20
  have row163 : v 10 + v 24 - v 26 ≤ 1 := join 10 24
  have row184 : v 12 + v 16 - v 28 ≤ 1 := join 12 16
  have row188 : v 12 + v 20 - v 28 ≤ 1 := join 12 20
  have row296 : v 0 ≤ 0 := (small 0 (by decide)).le
  have row327 : -(v 31) ≤ -1 := neg_le_neg (fixed 31 (by decide)).ge
  by_contra! fail
  have bad : (-9) * v 0 + (-5) * v 1 + (-5) * v 2 + (-1) * v 3 + (-5) * v 4 + (-1) * v 5 + (-1) * v 6 + 3 * v 7 + (-5) * v 8 + (-1) * v 9 + (-1) * v 10 + 3 * v 11 + (-1) * v 12 + 3 * v 13 + 3 * v 14 + 7 * v 15 + (-5) * v 16 + (-1) * v 17 + (-1) * v 18 + 3 * v 19 + (-1) * v 20 + 3 * v 21 + 3 * v 22 + 7 * v 23 + (-1) * v 24 + 3 * v 25 + 3 * v 26 + 7 * v 27 + 3 * v 28 + 7 * v 29 + 7 * v 30 + 11 * v 31 ≤ (-1 : ℤ) := by omega
  rcases bit 1 with h1 | h1
  · rcases bit 2 with h2 | h2
    · rcases bit 4 with h4 | h4
      · have falseBound : (0 : ℤ) ≤ (-2 : ℤ) := by
          linear_combination bad + row39 + row80 + row97 + 4 * row130 + row145 + row163 + row184 + 9 * row296 + 11 * row327 + 9995 * (low 1) + 9995 * (low 2) + 9995 * (low 4) + 3 * (low 7) + 2 * (low 11) + 3 * (low 13) + 3 * (low 14) + 7 * (low 15) + 3 * (low 19) + 3 * (low 21) + 3 * (low 22) + 5 * (low 23) + 3 * (low 25) + 2 * (low 26) + 7 * (low 27) + 2 * (low 28) + 6 * (low 29) + 7 * (low 30) + 10000 * h1 + 10000 * h2 + 10000 * h4
        omega
      · have falseBound : (0 : ℤ) ≤ (-5 : ℤ) := by
          linear_combination bad + row36 + 5 * row58 + row59 + row60 + 5 * row63 + 3 * row64 + 3 * row65 + 7 * row66 + row67 + 7 * row68 + row71 + row188 + 9 * row296 + 11 * row327 + 9995 * (low 1) + 9995 * (low 2) + 9971 * (high 4) + (low 7) + 3 * (low 11) + 2 * (low 13) + 2 * (low 14) + 7 * (low 15) + 2 * (low 17) + 2 * (low 18) + 10 * (low 19) + 10 * (low 25) + 3 * (low 26) + 7 * (low 27) + (low 28) + 7 * (low 30) + 10000 * h1 + 10000 * h2 - 10000 * h4
        omega
    · have falseBound : (0 : ℤ) ≤ (-5 : ℤ) := by
        linear_combination bad + 9980 * row20 + row21 + 5 * row23 + row24 + row25 + 5 * row28 + row29 + 3 * row30 + row32 + 7 * row34 + row47 + row92 + 9 * row296 + 11 * row327 + 9995 * (low 1) + 9975 * (low 4) + 2 * (low 7) + 2 * (low 11) + 3 * (low 13) + (low 14) + 7 * (low 15) + (low 19) + 2 * (low 20) + 3 * (low 21) + 7 * (low 23) + 3 * (low 25) + 2 * (low 26) + 7 * (low 27) + 10 * (low 28) + 7 * (low 29) + 10000 * h1 - 10000 * h2
      omega
  · have falseBound : (0 : ℤ) ≤ (-5 : ℤ) := by
      linear_combination bad + 5 * row1 + 5 * row3 + row4 + 5 * row6 + row7 + row8 + 7 * row9 + 5 * row11 + 2 * row12 + 3 * row13 + 7 * row14 + 3 * row15 + 7 * row16 + row46 + row73 + 9 * row296 + 11 * row327 + 9953 * (high 1) + 2 * (low 7) + 2 * (low 11) + (low 13) + 10 * (low 14) + (low 18) + 2 * (low 20) + 10 * (low 22) + 2 * (low 24) + 10 * (low 26) + 3 * (low 28) + 7 * (low 29) + 7 * (low 30) - 10000 * h1
    omega

lemma layer5_5 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (first : ∀ i, v i ≤ v (i ||| 31))
    (fixed : ∀ i ∈ ([31] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-7) * v 0 + (-3) * v 1 + (-3) * v 2 + 1 * v 3 + (-3) * v 4 + 1 * v 5 + 1 * v 6 + 5 * v 7 + (-3) * v 8 + 1 * v 9 + 1 * v 10 + 5 * v 11 + 1 * v 12 + 5 * v 13 + 5 * v 14 + 9 * v 15 + (-3) * v 16 + 1 * v 17 + 1 * v 18 + 5 * v 19 + 1 * v 20 + 5 * v 21 + 5 * v 22 + 9 * v 23 + 1 * v 24 + 5 * v 25 + 5 * v 26 + 9 * v 27 + 5 * v 28 + 9 * v 29 + 9 * v 30 + 13 * v 31 := by
  have low (i : ℕ) : -v i ≤ 0 := by rcases bit i with h|h <;> omega
  have high (i : ℕ) : v i ≤ 1 := by rcases bit i with h|h <;> omega
  have row0 : v 1 + v 2 - v 3 ≤ 1 := join 1 2
  have row1 : v 1 + v 4 - v 5 ≤ 1 := join 1 4
  have row3 : v 1 + v 8 - v 9 ≤ 1 := join 1 8
  have row7 : v 1 + v 16 - v 17 ≤ 1 := join 1 16
  have row15 : v 2 + v 4 - v 6 ≤ 1 := join 2 4
  have row16 : v 2 + v 5 - v 7 ≤ 1 := join 2 5
  have row17 : v 2 + v 8 - v 10 ≤ 1 := join 2 8
  have row20 : v 2 + v 13 - v 15 ≤ 1 := join 2 13
  have row21 : v 2 + v 16 - v 18 ≤ 1 := join 2 16
  have row22 : v 2 + v 17 - v 19 ≤ 1 := join 2 17
  have row23 : v 2 + v 20 - v 22 ≤ 1 := join 2 20
  have row27 : v 2 + v 28 - v 30 ≤ 1 := join 2 28
  have row34 : v 3 + v 10 - v 11 ≤ 1 := join 3 10
  have row43 : v 3 + v 22 - v 23 ≤ 1 := join 3 22
  have row50 : v 4 + v 8 - v 12 ≤ 1 := join 4 8
  have row54 : v 4 + v 16 - v 20 ≤ 1 := join 4 16
  have row120 : v 8 + v 16 - v 24 ≤ 1 := join 8 16
  have row285 : v 0 - v 31 ≤ 0 := sub_nonpos.mpr (first 0)
  have row316 : -(v 31) ≤ -1 := neg_le_neg (fixed 31 (by decide)).ge
  by_contra! fail
  have bad : (-7) * v 0 + (-3) * v 1 + (-3) * v 2 + 1 * v 3 + (-3) * v 4 + 1 * v 5 + 1 * v 6 + 5 * v 7 + (-3) * v 8 + 1 * v 9 + 1 * v 10 + 5 * v 11 + 1 * v 12 + 5 * v 13 + 5 * v 14 + 9 * v 15 + (-3) * v 16 + 1 * v 17 + 1 * v 18 + 5 * v 19 + 1 * v 20 + 5 * v 21 + 5 * v 22 + 9 * v 23 + 1 * v 24 + 5 * v 25 + 5 * v 26 + 9 * v 27 + 5 * v 28 + 9 * v 29 + 9 * v 30 + 13 * v 31 ≤ (-1 : ℤ) := by omega
  rcases bit 1 with h1 | h1
  · have falseBound : (0 : ℤ) ≤ (-1 : ℤ) := by
      linear_combination bad + row15 + row17 + row21 + row50 + row54 + row120 + 7 * row285 + 6 * row316 + 9997 * (low 1) + (low 3) + (low 5) + 5 * (low 7) + (low 9) + 5 * (low 11) + 5 * (low 13) + 5 * (low 14) + 9 * (low 15) + (low 17) + 5 * (low 19) + 5 * (low 21) + 5 * (low 22) + 9 * (low 23) + 5 * (low 25) + 5 * (low 26) + 9 * (low 27) + 5 * (low 28) + 9 * (low 29) + 9 * (low 30) + 10000 * h1
    omega
  · rcases bit 2 with h2 | h2
    · have falseBound : (0 : ℤ) ≤ (-1 : ℤ) := by
        linear_combination bad + row1 + row3 + row7 + row50 + row54 + row120 + 7 * row285 + 6 * row316 + 10000 * (high 1) + 9997 * (low 2) + (low 3) + (low 6) + 5 * (low 7) + (low 10) + 5 * (low 11) + 5 * (low 13) + 5 * (low 14) + 9 * (low 15) + (low 18) + 5 * (low 19) + 5 * (low 21) + 5 * (low 22) + 9 * (low 23) + 5 * (low 25) + 5 * (low 26) + 9 * (low 27) + 5 * (low 28) + 9 * (low 29) + 9 * (low 30) - 10000 * h1 + 10000 * h2
      omega
    · have falseBound : (0 : ℤ) ≤ (-2 : ℤ) := by
        linear_combination bad + 15 * row0 + 3 * row1 + row3 + 3 * row7 + 5 * row16 + 6 * row17 + 9 * row20 + 5 * row22 + 14 * row23 + 9 * row27 + 5 * row34 + 9 * row43 + 7 * row285 + 6 * row316 + 9981 * (high 1) + 9940 * (high 2) + 3 * (low 5) + (low 6) + 4 * (low 8) + (low 12) + 14 * (low 13) + 5 * (low 14) + 3 * (low 17) + (low 18) + 15 * (low 20) + 5 * (low 21) + (low 24) + 5 * (low 25) + 5 * (low 26) + 9 * (low 27) + 14 * (low 28) + 9 * (low 29) - 10000 * h1 - 10000 * h2
      omega

lemma layer5_6 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (first : ∀ i, v i ≤ v (i ||| 31))
    (fixed : ∀ i ∈ ([31] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-5) * v 0 + (-1) * v 1 + (-1) * v 2 + 3 * v 3 + (-1) * v 4 + 3 * v 5 + 3 * v 6 + 7 * v 7 + (-1) * v 8 + 3 * v 9 + 3 * v 10 + 7 * v 11 + 3 * v 12 + 7 * v 13 + 7 * v 14 + 11 * v 15 + (-1) * v 16 + 3 * v 17 + 3 * v 18 + 7 * v 19 + 3 * v 20 + 7 * v 21 + 7 * v 22 + 11 * v 23 + 3 * v 24 + 7 * v 25 + 7 * v 26 + 11 * v 27 + 7 * v 28 + 11 * v 29 + 11 * v 30 + 15 * v 31 := by
  have low (i : ℕ) : -v i ≤ 0 := by rcases bit i with h|h <;> omega
  have high (i : ℕ) : v i ≤ 1 := by rcases bit i with h|h <;> omega
  have row3 : v 1 + v 8 - v 9 ≤ 1 := join 1 8
  have row15 : v 2 + v 4 - v 6 ≤ 1 := join 2 4
  have row21 : v 2 + v 16 - v 18 ≤ 1 := join 2 16
  have row54 : v 4 + v 16 - v 20 ≤ 1 := join 4 16
  have row285 : v 0 - v 31 ≤ 0 := sub_nonpos.mpr (first 0)
  have row316 : -(v 31) ≤ -1 := neg_le_neg (fixed 31 (by decide)).ge
  by_contra! fail
  have bad : (-5) * v 0 + (-1) * v 1 + (-1) * v 2 + 3 * v 3 + (-1) * v 4 + 3 * v 5 + 3 * v 6 + 7 * v 7 + (-1) * v 8 + 3 * v 9 + 3 * v 10 + 7 * v 11 + 3 * v 12 + 7 * v 13 + 7 * v 14 + 11 * v 15 + (-1) * v 16 + 3 * v 17 + 3 * v 18 + 7 * v 19 + 3 * v 20 + 7 * v 21 + 7 * v 22 + 11 * v 23 + 3 * v 24 + 7 * v 25 + 7 * v 26 + 11 * v 27 + 7 * v 28 + 11 * v 29 + 11 * v 30 + 15 * v 31 ≤ (-1 : ℤ) := by omega
  have falseBound : (0 : ℤ) ≤ (-17 : ℤ) := by
    linear_combination 2 * bad + 2 * row3 + row15 + row21 + row54 + 10 * row285 + 20 * row316 + 6 * (low 3) + 6 * (low 5) + 5 * (low 6) + 14 * (low 7) + 4 * (low 9) + 6 * (low 10) + 14 * (low 11) + 6 * (low 12) + 14 * (low 13) + 14 * (low 14) + 22 * (low 15) + 6 * (low 17) + 5 * (low 18) + 14 * (low 19) + 5 * (low 20) + 14 * (low 21) + 14 * (low 22) + 22 * (low 23) + 6 * (low 24) + 14 * (low 25) + 14 * (low 26) + 22 * (low 27) + 14 * (low 28) + 22 * (low 29) + 22 * (low 30)
  omega

lemma layer5_7 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (first : ∀ i, v i ≤ v (i ||| 31))
    (fixed : ∀ i ∈ ([31] : List ℕ), v i=1) :
    (14 : ℤ) ≤ (-3) * v 0 + 1 * v 1 + 1 * v 2 + 5 * v 3 + 1 * v 4 + 5 * v 5 + 5 * v 6 + 9 * v 7 + 1 * v 8 + 5 * v 9 + 5 * v 10 + 9 * v 11 + 5 * v 12 + 9 * v 13 + 9 * v 14 + 13 * v 15 + 1 * v 16 + 5 * v 17 + 5 * v 18 + 9 * v 19 + 5 * v 20 + 9 * v 21 + 9 * v 22 + 13 * v 23 + 5 * v 24 + 9 * v 25 + 9 * v 26 + 13 * v 27 + 9 * v 28 + 13 * v 29 + 13 * v 30 + 17 * v 31 := by
  have low (i : ℕ) : -v i ≤ 0 := by rcases bit i with h|h <;> omega
  have high (i : ℕ) : v i ≤ 1 := by rcases bit i with h|h <;> omega
  have row285 : v 0 - v 31 ≤ 0 := sub_nonpos.mpr (first 0)
  have row316 : -(v 31) ≤ -1 := neg_le_neg (fixed 31 (by decide)).ge
  by_contra! fail
  have bad : (-3) * v 0 + 1 * v 1 + 1 * v 2 + 5 * v 3 + 1 * v 4 + 5 * v 5 + 5 * v 6 + 9 * v 7 + 1 * v 8 + 5 * v 9 + 5 * v 10 + 9 * v 11 + 5 * v 12 + 9 * v 13 + 9 * v 14 + 13 * v 15 + 1 * v 16 + 5 * v 17 + 5 * v 18 + 9 * v 19 + 5 * v 20 + 9 * v 21 + 9 * v 22 + 13 * v 23 + 5 * v 24 + 9 * v 25 + 9 * v 26 + 13 * v 27 + 9 * v 28 + 13 * v 29 + 13 * v 30 + 17 * v 31 ≤ (13 : ℤ) := by omega
  have falseBound : (0 : ℤ) ≤ (-1 : ℤ) := by
    linear_combination bad + 3 * row285 + 14 * row316 + (low 1) + (low 2) + 5 * (low 3) + (low 4) + 5 * (low 5) + 5 * (low 6) + 9 * (low 7) + (low 8) + 5 * (low 9) + 5 * (low 10) + 9 * (low 11) + 5 * (low 12) + 9 * (low 13) + 9 * (low 14) + 13 * (low 15) + (low 16) + 5 * (low 17) + 5 * (low 18) + 9 * (low 19) + 5 * (low 20) + 9 * (low 21) + 9 * (low 22) + 13 * (low 23) + 5 * (low 24) + 9 * (low 25) + 9 * (low 26) + 13 * (low 27) + 9 * (low 28) + 13 * (low 29) + 13 * (low 30)
  omega

lemma layer6_0 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (first : ∀ i, v i ≤ v (i ||| 31))
    (second : ∀ i, v i ≤ v (i ||| 47))
    (small : ∀ i ∈ ([1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,48,49,50,51,52,53,54,56,57,58,60] : List ℕ), v i=0)
    (fixed : ∀ i ∈ ([0,31,47,63] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-12) * v 0 + (-9) * v 1 + (-9) * v 2 + (-6) * v 3 + (-9) * v 4 + (-6) * v 5 + (-6) * v 6 + (-3) * v 7 + (-9) * v 8 + (-6) * v 9 + (-6) * v 10 + (-3) * v 11 + (-6) * v 12 + (-3) * v 13 + (-3) * v 14 + (-9) * v 16 + (-6) * v 17 + (-6) * v 18 + (-3) * v 19 + (-6) * v 20 + (-3) * v 21 + (-3) * v 22 + (-6) * v 24 + (-3) * v 25 + (-3) * v 26 + (-3) * v 28 + 3 * v 31 + (-9) * v 32 + (-6) * v 33 + (-6) * v 34 + (-3) * v 35 + (-6) * v 36 + (-3) * v 37 + (-3) * v 38 + (-6) * v 40 + (-3) * v 41 + (-3) * v 42 + (-3) * v 44 + 3 * v 47 + (-6) * v 48 + (-3) * v 49 + (-3) * v 50 + (-3) * v 52 + 3 * v 55 + (-3) * v 56 + 3 * v 59 + 3 * v 61 + 3 * v 62 + 6 * v 63 := by
  have low (i : ℕ) : -v i ≤ 0 := by rcases bit i with h|h <;> omega
  have high (i : ℕ) : v i ≤ 1 := by rcases bit i with h|h <;> omega
  have row1352 : v 0 - v 47 ≤ 0 := sub_nonpos.mpr (second 0)
  have row1356 : v 1 ≤ 0 := (small 1 (by decide)).le
  have row1359 : v 2 ≤ 0 := (small 2 (by decide)).le
  have row1362 : v 3 ≤ 0 := (small 3 (by decide)).le
  have row1365 : v 4 ≤ 0 := (small 4 (by decide)).le
  have row1368 : v 5 ≤ 0 := (small 5 (by decide)).le
  have row1371 : v 6 ≤ 0 := (small 6 (by decide)).le
  have row1374 : v 7 ≤ 0 := (small 7 (by decide)).le
  have row1377 : v 8 ≤ 0 := (small 8 (by decide)).le
  have row1380 : v 9 ≤ 0 := (small 9 (by decide)).le
  have row1383 : v 10 ≤ 0 := (small 10 (by decide)).le
  have row1386 : v 11 ≤ 0 := (small 11 (by decide)).le
  have row1389 : v 12 ≤ 0 := (small 12 (by decide)).le
  have row1392 : v 13 ≤ 0 := (small 13 (by decide)).le
  have row1395 : v 14 ≤ 0 := (small 14 (by decide)).le
  have row1401 : v 16 ≤ 0 := (small 16 (by decide)).le
  have row1404 : v 17 ≤ 0 := (small 17 (by decide)).le
  have row1407 : v 18 ≤ 0 := (small 18 (by decide)).le
  have row1410 : v 19 ≤ 0 := (small 19 (by decide)).le
  have row1413 : v 20 ≤ 0 := (small 20 (by decide)).le
  have row1416 : v 21 ≤ 0 := (small 21 (by decide)).le
  have row1419 : v 22 ≤ 0 := (small 22 (by decide)).le
  have row1425 : v 24 ≤ 0 := (small 24 (by decide)).le
  have row1428 : v 25 ≤ 0 := (small 25 (by decide)).le
  have row1431 : v 26 ≤ 0 := (small 26 (by decide)).le
  have row1437 : v 28 ≤ 0 := (small 28 (by decide)).le
  have row1445 : -(v 31) ≤ -1 := neg_le_neg (fixed 31 (by decide)).ge
  have row1448 : v 32 ≤ 0 := (small 32 (by decide)).le
  have row1451 : v 33 ≤ 0 := (small 33 (by decide)).le
  have row1454 : v 34 ≤ 0 := (small 34 (by decide)).le
  have row1457 : v 35 ≤ 0 := (small 35 (by decide)).le
  have row1460 : v 36 ≤ 0 := (small 36 (by decide)).le
  have row1463 : v 37 ≤ 0 := (small 37 (by decide)).le
  have row1466 : v 38 ≤ 0 := (small 38 (by decide)).le
  have row1472 : v 40 ≤ 0 := (small 40 (by decide)).le
  have row1475 : v 41 ≤ 0 := (small 41 (by decide)).le
  have row1478 : v 42 ≤ 0 := (small 42 (by decide)).le
  have row1484 : v 44 ≤ 0 := (small 44 (by decide)).le
  have row1491 : v 47 - v 63 ≤ 0 := sub_nonpos.mpr (first 47)
  have row1495 : v 48 ≤ 0 := (small 48 (by decide)).le
  have row1498 : v 49 ≤ 0 := (small 49 (by decide)).le
  have row1501 : v 50 ≤ 0 := (small 50 (by decide)).le
  have row1507 : v 52 ≤ 0 := (small 52 (by decide)).le
  have row1518 : v 56 ≤ 0 := (small 56 (by decide)).le
  by_contra! fail
  have bad : (-12) * v 0 + (-9) * v 1 + (-9) * v 2 + (-6) * v 3 + (-9) * v 4 + (-6) * v 5 + (-6) * v 6 + (-3) * v 7 + (-9) * v 8 + (-6) * v 9 + (-6) * v 10 + (-3) * v 11 + (-6) * v 12 + (-3) * v 13 + (-3) * v 14 + (-9) * v 16 + (-6) * v 17 + (-6) * v 18 + (-3) * v 19 + (-6) * v 20 + (-3) * v 21 + (-3) * v 22 + (-6) * v 24 + (-3) * v 25 + (-3) * v 26 + (-3) * v 28 + 3 * v 31 + (-9) * v 32 + (-6) * v 33 + (-6) * v 34 + (-3) * v 35 + (-6) * v 36 + (-3) * v 37 + (-3) * v 38 + (-6) * v 40 + (-3) * v 41 + (-3) * v 42 + (-3) * v 44 + 3 * v 47 + (-6) * v 48 + (-3) * v 49 + (-3) * v 50 + (-3) * v 52 + 3 * v 55 + (-3) * v 56 + 3 * v 59 + 3 * v 61 + 3 * v 62 + 6 * v 63 ≤ (-1 : ℤ) := by omega
  have falseBound : (0 : ℤ) ≤ (-1 : ℤ) := by
    linear_combination bad + 12 * row1352 + 9 * row1356 + 9 * row1359 + 6 * row1362 + 9 * row1365 + 6 * row1368 + 6 * row1371 + 3 * row1374 + 9 * row1377 + 6 * row1380 + 6 * row1383 + 3 * row1386 + 6 * row1389 + 3 * row1392 + 3 * row1395 + 9 * row1401 + 6 * row1404 + 6 * row1407 + 3 * row1410 + 6 * row1413 + 3 * row1416 + 3 * row1419 + 6 * row1425 + 3 * row1428 + 3 * row1431 + 3 * row1437 + 3 * row1445 + 9 * row1448 + 6 * row1451 + 6 * row1454 + 3 * row1457 + 6 * row1460 + 3 * row1463 + 3 * row1466 + 6 * row1472 + 3 * row1475 + 3 * row1478 + 3 * row1484 + 9 * row1491 + 6 * row1495 + 3 * row1498 + 3 * row1501 + 3 * row1507 + 3 * row1518 + 3 * (low 55) + 3 * (low 59) + 3 * (low 61) + 3 * (low 62) + 3 * (high 63)
  omega

lemma layer6_1 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (first : ∀ i, v i ≤ v (i ||| 31))
    (second : ∀ i, v i ≤ v (i ||| 47))
    (small : ∀ i ∈ ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,16,17,18,19,20,21,22,24,25,26,28,32,33,34,35,36,37,38,40,41,42,44,48,49,50,52,56] : List ℕ), v i=0)
    (fixed : ∀ i ∈ ([63] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-11) * v 0 + (-8) * v 1 + (-8) * v 2 + (-5) * v 3 + (-8) * v 4 + (-5) * v 5 + (-5) * v 6 + (-2) * v 7 + (-8) * v 8 + (-5) * v 9 + (-5) * v 10 + (-2) * v 11 + (-5) * v 12 + (-2) * v 13 + (-2) * v 14 + 1 * v 15 + (-8) * v 16 + (-5) * v 17 + (-5) * v 18 + (-2) * v 19 + (-5) * v 20 + (-2) * v 21 + (-2) * v 22 + 1 * v 23 + (-5) * v 24 + (-2) * v 25 + (-2) * v 26 + 1 * v 27 + (-2) * v 28 + 1 * v 29 + 1 * v 30 + 4 * v 31 + (-8) * v 32 + (-5) * v 33 + (-5) * v 34 + (-2) * v 35 + (-5) * v 36 + (-2) * v 37 + (-2) * v 38 + 1 * v 39 + (-5) * v 40 + (-2) * v 41 + (-2) * v 42 + 1 * v 43 + (-2) * v 44 + 1 * v 45 + 1 * v 46 + 4 * v 47 + (-5) * v 48 + (-2) * v 49 + (-2) * v 50 + 1 * v 51 + (-2) * v 52 + 1 * v 53 + 1 * v 54 + 4 * v 55 + (-2) * v 56 + 1 * v 57 + 1 * v 58 + 4 * v 59 + 1 * v 60 + 4 * v 61 + 4 * v 62 + 7 * v 63 := by
  have low (i : ℕ) : -v i ≤ 0 := by rcases bit i with h|h <;> omega
  have high (i : ℕ) : v i ≤ 1 := by rcases bit i with h|h <;> omega
  have row1353 : v 0 ≤ 0 := (small 0 (by decide)).le
  have row1356 : v 1 ≤ 0 := (small 1 (by decide)).le
  have row1359 : v 2 ≤ 0 := (small 2 (by decide)).le
  have row1362 : v 3 ≤ 0 := (small 3 (by decide)).le
  have row1365 : v 4 ≤ 0 := (small 4 (by decide)).le
  have row1368 : v 5 ≤ 0 := (small 5 (by decide)).le
  have row1371 : v 6 ≤ 0 := (small 6 (by decide)).le
  have row1374 : v 7 ≤ 0 := (small 7 (by decide)).le
  have row1377 : v 8 ≤ 0 := (small 8 (by decide)).le
  have row1380 : v 9 ≤ 0 := (small 9 (by decide)).le
  have row1383 : v 10 ≤ 0 := (small 10 (by decide)).le
  have row1386 : v 11 ≤ 0 := (small 11 (by decide)).le
  have row1389 : v 12 ≤ 0 := (small 12 (by decide)).le
  have row1392 : v 13 ≤ 0 := (small 13 (by decide)).le
  have row1395 : v 14 ≤ 0 := (small 14 (by decide)).le
  have row1400 : v 16 ≤ 0 := (small 16 (by decide)).le
  have row1403 : v 17 ≤ 0 := (small 17 (by decide)).le
  have row1406 : v 18 ≤ 0 := (small 18 (by decide)).le
  have row1409 : v 19 ≤ 0 := (small 19 (by decide)).le
  have row1412 : v 20 ≤ 0 := (small 20 (by decide)).le
  have row1415 : v 21 ≤ 0 := (small 21 (by decide)).le
  have row1418 : v 22 ≤ 0 := (small 22 (by decide)).le
  have row1423 : v 24 ≤ 0 := (small 24 (by decide)).le
  have row1426 : v 25 ≤ 0 := (small 25 (by decide)).le
  have row1429 : v 26 ≤ 0 := (small 26 (by decide)).le
  have row1434 : v 28 ≤ 0 := (small 28 (by decide)).le
  have row1442 : v 32 ≤ 0 := (small 32 (by decide)).le
  have row1445 : v 33 ≤ 0 := (small 33 (by decide)).le
  have row1448 : v 34 ≤ 0 := (small 34 (by decide)).le
  have row1451 : v 35 ≤ 0 := (small 35 (by decide)).le
  have row1454 : v 36 ≤ 0 := (small 36 (by decide)).le
  have row1457 : v 37 ≤ 0 := (small 37 (by decide)).le
  have row1460 : v 38 ≤ 0 := (small 38 (by decide)).le
  have row1465 : v 40 ≤ 0 := (small 40 (by decide)).le
  have row1468 : v 41 ≤ 0 := (small 41 (by decide)).le
  have row1471 : v 42 ≤ 0 := (small 42 (by decide)).le
  have row1476 : v 44 ≤ 0 := (small 44 (by decide)).le
  have row1484 : v 48 ≤ 0 := (small 48 (by decide)).le
  have row1487 : v 49 ≤ 0 := (small 49 (by decide)).le
  have row1490 : v 50 ≤ 0 := (small 50 (by decide)).le
  have row1495 : v 52 ≤ 0 := (small 52 (by decide)).le
  have row1504 : v 56 ≤ 0 := (small 56 (by decide)).le
  have row1517 : -(v 63) ≤ -1 := neg_le_neg (fixed 63 (by decide)).ge
  by_contra! fail
  have bad : (-11) * v 0 + (-8) * v 1 + (-8) * v 2 + (-5) * v 3 + (-8) * v 4 + (-5) * v 5 + (-5) * v 6 + (-2) * v 7 + (-8) * v 8 + (-5) * v 9 + (-5) * v 10 + (-2) * v 11 + (-5) * v 12 + (-2) * v 13 + (-2) * v 14 + 1 * v 15 + (-8) * v 16 + (-5) * v 17 + (-5) * v 18 + (-2) * v 19 + (-5) * v 20 + (-2) * v 21 + (-2) * v 22 + 1 * v 23 + (-5) * v 24 + (-2) * v 25 + (-2) * v 26 + 1 * v 27 + (-2) * v 28 + 1 * v 29 + 1 * v 30 + 4 * v 31 + (-8) * v 32 + (-5) * v 33 + (-5) * v 34 + (-2) * v 35 + (-5) * v 36 + (-2) * v 37 + (-2) * v 38 + 1 * v 39 + (-5) * v 40 + (-2) * v 41 + (-2) * v 42 + 1 * v 43 + (-2) * v 44 + 1 * v 45 + 1 * v 46 + 4 * v 47 + (-5) * v 48 + (-2) * v 49 + (-2) * v 50 + 1 * v 51 + (-2) * v 52 + 1 * v 53 + 1 * v 54 + 4 * v 55 + (-2) * v 56 + 1 * v 57 + 1 * v 58 + 4 * v 59 + 1 * v 60 + 4 * v 61 + 4 * v 62 + 7 * v 63 ≤ (-1 : ℤ) := by omega
  have falseBound : (0 : ℤ) ≤ (-8 : ℤ) := by
    linear_combination bad + 11 * row1353 + 8 * row1356 + 8 * row1359 + 5 * row1362 + 8 * row1365 + 5 * row1368 + 5 * row1371 + 2 * row1374 + 8 * row1377 + 5 * row1380 + 5 * row1383 + 2 * row1386 + 5 * row1389 + 2 * row1392 + 2 * row1395 + 8 * row1400 + 5 * row1403 + 5 * row1406 + 2 * row1409 + 5 * row1412 + 2 * row1415 + 2 * row1418 + 5 * row1423 + 2 * row1426 + 2 * row1429 + 2 * row1434 + 8 * row1442 + 5 * row1445 + 5 * row1448 + 2 * row1451 + 5 * row1454 + 2 * row1457 + 2 * row1460 + 5 * row1465 + 2 * row1468 + 2 * row1471 + 2 * row1476 + 5 * row1484 + 2 * row1487 + 2 * row1490 + 2 * row1495 + 2 * row1504 + 7 * row1517 + (low 15) + (low 23) + (low 27) + (low 29) + (low 30) + 4 * (low 31) + (low 39) + (low 43) + (low 45) + (low 46) + 4 * (low 47) + (low 51) + (low 53) + (low 54) + 4 * (low 55) + (low 57) + (low 58) + 4 * (low 59) + (low 60) + 4 * (low 61) + 4 * (low 62)
  omega

lemma layer6_2 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (first : ∀ i, v i ≤ v (i ||| 31))
    (second : ∀ i, v i ≤ v (i ||| 47))
    (small : ∀ i ∈ ([0,1,2,3,4,5,6,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48] : List ℕ), v i=0)
    (fixed : ∀ i ∈ ([63] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-10) * v 0 + (-7) * v 1 + (-7) * v 2 + (-4) * v 3 + (-7) * v 4 + (-4) * v 5 + (-4) * v 6 + (-1) * v 7 + (-7) * v 8 + (-4) * v 9 + (-4) * v 10 + (-1) * v 11 + (-4) * v 12 + (-1) * v 13 + (-1) * v 14 + 2 * v 15 + (-7) * v 16 + (-4) * v 17 + (-4) * v 18 + (-1) * v 19 + (-4) * v 20 + (-1) * v 21 + (-1) * v 22 + 2 * v 23 + (-4) * v 24 + (-1) * v 25 + (-1) * v 26 + 2 * v 27 + (-1) * v 28 + 2 * v 29 + 2 * v 30 + 5 * v 31 + (-7) * v 32 + (-4) * v 33 + (-4) * v 34 + (-1) * v 35 + (-4) * v 36 + (-1) * v 37 + (-1) * v 38 + 2 * v 39 + (-4) * v 40 + (-1) * v 41 + (-1) * v 42 + 2 * v 43 + (-1) * v 44 + 2 * v 45 + 2 * v 46 + 5 * v 47 + (-4) * v 48 + (-1) * v 49 + (-1) * v 50 + 2 * v 51 + (-1) * v 52 + 2 * v 53 + 2 * v 54 + 5 * v 55 + (-1) * v 56 + 2 * v 57 + 2 * v 58 + 5 * v 59 + 2 * v 60 + 5 * v 61 + 5 * v 62 + 8 * v 63 := by
  have low (i : ℕ) : -v i ≤ 0 := by rcases bit i with h|h <;> omega
  have high (i : ℕ) : v i ≤ 1 := by rcases bit i with h|h <;> omega
  have row747 : v 21 + v 50 - v 55 ≤ 1 := join 21 50
  have row879 : v 25 + v 56 - v 57 ≤ 1 := join 25 56
  have row905 : v 26 + v 52 - v 62 ≤ 1 := join 26 52
  have row952 : v 28 + v 38 - v 62 ≤ 1 := join 28 38
  have row1105 : v 35 + v 49 - v 51 ≤ 1 := join 35 49
  have row1353 : v 0 ≤ 0 := (small 0 (by decide)).le
  have row1356 : v 1 ≤ 0 := (small 1 (by decide)).le
  have row1359 : v 2 ≤ 0 := (small 2 (by decide)).le
  have row1362 : v 3 ≤ 0 := (small 3 (by decide)).le
  have row1365 : v 4 ≤ 0 := (small 4 (by decide)).le
  have row1368 : v 5 ≤ 0 := (small 5 (by decide)).le
  have row1371 : v 6 ≤ 0 := (small 6 (by decide)).le
  have row1372 : v 7 - v 31 ≤ 0 := sub_nonpos.mpr (first 7)
  have row1376 : v 8 ≤ 0 := (small 8 (by decide)).le
  have row1379 : v 9 ≤ 0 := (small 9 (by decide)).le
  have row1382 : v 10 ≤ 0 := (small 10 (by decide)).le
  have row1383 : v 11 - v 31 ≤ 0 := sub_nonpos.mpr (first 11)
  have row1387 : v 12 ≤ 0 := (small 12 (by decide)).le
  have row1388 : v 13 - v 31 ≤ 0 := sub_nonpos.mpr (first 13)
  have row1391 : v 14 - v 47 ≤ 0 := sub_nonpos.mpr (second 14)
  have row1396 : v 16 ≤ 0 := (small 16 (by decide)).le
  have row1399 : v 17 ≤ 0 := (small 17 (by decide)).le
  have row1402 : v 18 ≤ 0 := (small 18 (by decide)).le
  have row1403 : v 19 - v 31 ≤ 0 := sub_nonpos.mpr (first 19)
  have row1407 : v 20 ≤ 0 := (small 20 (by decide)).le
  have row1410 : v 22 - v 31 ≤ 0 := sub_nonpos.mpr (first 22)
  have row1416 : v 24 ≤ 0 := (small 24 (by decide)).le
  have row1432 : v 32 ≤ 0 := (small 32 (by decide)).le
  have row1435 : v 33 ≤ 0 := (small 33 (by decide)).le
  have row1438 : v 34 ≤ 0 := (small 34 (by decide)).le
  have row1443 : v 36 ≤ 0 := (small 36 (by decide)).le
  have row1445 : v 37 - v 47 ≤ 0 := sub_nonpos.mpr (second 37)
  have row1452 : v 40 ≤ 0 := (small 40 (by decide)).le
  have row1454 : v 41 - v 47 ≤ 0 := sub_nonpos.mpr (second 41)
  have row1456 : v 42 - v 47 ≤ 0 := sub_nonpos.mpr (second 42)
  have row1460 : v 44 - v 47 ≤ 0 := sub_nonpos.mpr (second 44)
  have row1468 : v 48 ≤ 0 := (small 48 (by decide)).le
  have row1497 : -(v 63) ≤ -1 := neg_le_neg (fixed 63 (by decide)).ge
  by_contra! fail
  have bad : (-10) * v 0 + (-7) * v 1 + (-7) * v 2 + (-4) * v 3 + (-7) * v 4 + (-4) * v 5 + (-4) * v 6 + (-1) * v 7 + (-7) * v 8 + (-4) * v 9 + (-4) * v 10 + (-1) * v 11 + (-4) * v 12 + (-1) * v 13 + (-1) * v 14 + 2 * v 15 + (-7) * v 16 + (-4) * v 17 + (-4) * v 18 + (-1) * v 19 + (-4) * v 20 + (-1) * v 21 + (-1) * v 22 + 2 * v 23 + (-4) * v 24 + (-1) * v 25 + (-1) * v 26 + 2 * v 27 + (-1) * v 28 + 2 * v 29 + 2 * v 30 + 5 * v 31 + (-7) * v 32 + (-4) * v 33 + (-4) * v 34 + (-1) * v 35 + (-4) * v 36 + (-1) * v 37 + (-1) * v 38 + 2 * v 39 + (-4) * v 40 + (-1) * v 41 + (-1) * v 42 + 2 * v 43 + (-1) * v 44 + 2 * v 45 + 2 * v 46 + 5 * v 47 + (-4) * v 48 + (-1) * v 49 + (-1) * v 50 + 2 * v 51 + (-1) * v 52 + 2 * v 53 + 2 * v 54 + 5 * v 55 + (-1) * v 56 + 2 * v 57 + 2 * v 58 + 5 * v 59 + 2 * v 60 + 5 * v 61 + 5 * v 62 + 8 * v 63 ≤ (-1 : ℤ) := by omega
  have falseBound : (0 : ℤ) ≤ (-4 : ℤ) := by
    linear_combination bad + row747 + row879 + row905 + row952 + row1105 + 10 * row1353 + 7 * row1356 + 7 * row1359 + 4 * row1362 + 7 * row1365 + 4 * row1368 + 4 * row1371 + row1372 + 7 * row1376 + 4 * row1379 + 4 * row1382 + row1383 + 4 * row1387 + row1388 + row1391 + 7 * row1396 + 4 * row1399 + 4 * row1402 + row1403 + 4 * row1407 + row1410 + 4 * row1416 + 7 * row1432 + 4 * row1435 + 4 * row1438 + 4 * row1443 + row1445 + 4 * row1452 + row1454 + row1456 + row1460 + 4 * row1468 + 8 * row1497 + 2 * (low 15) + 2 * (low 23) + 2 * (low 27) + 2 * (low 29) + 2 * (low 30) + 2 * (low 39) + 2 * (low 43) + 2 * (low 45) + 2 * (low 46) + (low 51) + 2 * (low 53) + 2 * (low 54) + 4 * (low 55) + (low 57) + 2 * (low 58) + 5 * (low 59) + 2 * (low 60) + 5 * (low 61) + 3 * (low 62)
  omega

lemma layer6_3 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (first : ∀ i, v i ≤ v (i ||| 31))
    (second : ∀ i, v i ≤ v (i ||| 47))
    (small : ∀ i ∈ ([0,1,2,4,8,16,32] : List ℕ), v i=0)
    (fixed : ∀ i ∈ ([63] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-9) * v 0 + (-6) * v 1 + (-6) * v 2 + (-3) * v 3 + (-6) * v 4 + (-3) * v 5 + (-3) * v 6 + (-6) * v 8 + (-3) * v 9 + (-3) * v 10 + (-3) * v 12 + 3 * v 15 + (-6) * v 16 + (-3) * v 17 + (-3) * v 18 + (-3) * v 20 + 3 * v 23 + (-3) * v 24 + 3 * v 27 + 3 * v 29 + 3 * v 30 + 6 * v 31 + (-6) * v 32 + (-3) * v 33 + (-3) * v 34 + (-3) * v 36 + 3 * v 39 + (-3) * v 40 + 3 * v 43 + 3 * v 45 + 3 * v 46 + 6 * v 47 + (-3) * v 48 + 3 * v 51 + 3 * v 53 + 3 * v 54 + 6 * v 55 + 3 * v 57 + 3 * v 58 + 6 * v 59 + 3 * v 60 + 6 * v 61 + 6 * v 62 + 9 * v 63 := by
  have low (i : ℕ) : -v i ≤ 0 := by rcases bit i with h|h <;> omega
  have high (i : ℕ) : v i ≤ 1 := by rcases bit i with h|h <;> omega
  have row62 : v 3 + v 5 - v 7 ≤ 1 := join 3 5
  have row65 : v 3 + v 9 - v 11 ≤ 1 := join 3 9
  have row67 : v 3 + v 12 - v 15 ≤ 1 := join 3 12
  have row71 : v 3 + v 17 - v 19 ≤ 1 := join 3 17
  have row73 : v 3 + v 20 - v 23 ≤ 1 := join 3 20
  have row83 : v 3 + v 33 - v 35 ≤ 1 := join 3 33
  have row85 : v 3 + v 36 - v 39 ≤ 1 := join 3 36
  have row88 : v 3 + v 40 - v 43 ≤ 1 := join 3 40
  have row94 : v 3 + v 48 - v 51 ≤ 1 := join 3 48
  have row99 : v 3 + v 54 - v 55 ≤ 1 := join 3 54
  have row137 : v 5 + v 10 - v 15 ≤ 1 := join 5 10
  have row142 : v 5 + v 17 - v 21 ≤ 1 := join 5 17
  have row143 : v 5 + v 18 - v 23 ≤ 1 := join 5 18
  have row147 : v 5 + v 24 - v 29 ≤ 1 := join 5 24
  have row155 : v 5 + v 34 - v 39 ≤ 1 := join 5 34
  have row159 : v 5 + v 40 - v 45 ≤ 1 := join 5 40
  have row165 : v 5 + v 48 - v 53 ≤ 1 := join 5 48
  have row178 : v 6 + v 9 - v 15 ≤ 1 := join 6 9
  have row181 : v 6 + v 12 - v 14 ≤ 1 := join 6 12
  have row184 : v 6 + v 17 - v 23 ≤ 1 := join 6 17
  have row185 : v 6 + v 18 - v 22 ≤ 1 := join 6 18
  have row186 : v 6 + v 19 - v 23 ≤ 1 := join 6 19
  have row188 : v 6 + v 21 - v 23 ≤ 1 := join 6 21
  have row196 : v 6 + v 33 - v 39 ≤ 1 := join 6 33
  have row197 : v 6 + v 34 - v 38 ≤ 1 := join 6 34
  have row198 : v 6 + v 35 - v 39 ≤ 1 := join 6 35
  have row201 : v 6 + v 40 - v 46 ≤ 1 := join 6 40
  have row208 : v 6 + v 49 - v 55 ≤ 1 := join 6 49
  have row217 : v 6 + v 60 - v 62 ≤ 1 := join 6 60
  have row221 : v 7 + v 10 - v 15 ≤ 1 := join 7 10
  have row254 : v 7 + v 48 - v 55 ≤ 1 := join 7 48
  have row292 : v 9 + v 10 - v 11 ≤ 1 := join 9 10
  have row299 : v 9 + v 20 - v 29 ≤ 1 := join 9 20
  have row308 : v 9 + v 33 - v 41 ≤ 1 := join 9 33
  have row309 : v 9 + v 34 - v 43 ≤ 1 := join 9 34
  have row311 : v 9 + v 36 - v 45 ≤ 1 := join 9 36
  have row334 : v 10 + v 17 - v 27 ≤ 1 := join 10 17
  have row337 : v 10 + v 20 - v 30 ≤ 1 := join 10 20
  have row346 : v 10 + v 33 - v 43 ≤ 1 := join 10 33
  have row349 : v 10 + v 36 - v 46 ≤ 1 := join 10 36
  have row353 : v 10 + v 40 - v 42 ≤ 1 := join 10 40
  have row357 : v 10 + v 48 - v 58 ≤ 1 := join 10 48
  have row363 : v 10 + v 54 - v 62 ≤ 1 := join 10 54
  have row366 : v 10 + v 57 - v 59 ≤ 1 := join 10 57
  have row374 : v 11 + v 18 - v 27 ≤ 1 := join 11 18
  have row380 : v 11 + v 24 - v 27 ≤ 1 := join 11 24
  have row415 : v 12 + v 17 - v 29 ≤ 1 := join 12 17
  have row416 : v 12 + v 18 - v 30 ≤ 1 := join 12 18
  have row438 : v 12 + v 48 - v 60 ≤ 1 := join 12 48
  have row497 : v 14 + v 20 - v 30 ≤ 1 := join 14 20
  have row511 : v 14 + v 36 - v 46 ≤ 1 := join 14 36
  have row605 : v 17 + v 34 - v 51 ≤ 1 := join 17 34
  have row611 : v 17 + v 40 - v 57 ≤ 1 := join 17 40
  have row612 : v 17 + v 41 - v 57 ≤ 1 := join 17 41
  have row637 : v 18 + v 36 - v 54 ≤ 1 := join 18 36
  have row641 : v 18 + v 40 - v 58 ≤ 1 := join 18 40
  have row643 : v 18 + v 42 - v 58 ≤ 1 := join 18 42
  have row668 : v 19 + v 34 - v 51 ≤ 1 := join 19 34
  have row700 : v 20 + v 34 - v 54 ≤ 1 := join 20 34
  have row767 : v 22 + v 36 - v 54 ≤ 1 := join 22 36
  have row801 : v 23 + v 35 - v 55 ≤ 1 := join 23 35
  have row829 : v 24 + v 33 - v 57 ≤ 1 := join 24 33
  have row830 : v 24 + v 34 - v 58 ≤ 1 := join 24 34
  have row834 : v 24 + v 38 - v 62 ≤ 1 := join 24 38
  have row979 : v 29 + v 36 - v 61 ≤ 1 := join 29 36
  have row1353 : v 0 ≤ 0 := (small 0 (by decide)).le
  have row1356 : v 1 ≤ 0 := (small 1 (by decide)).le
  have row1359 : v 2 ≤ 0 := (small 2 (by decide)).le
  have row1360 : v 3 - v 31 ≤ 0 := sub_nonpos.mpr (first 3)
  have row1361 : v 3 - v 47 ≤ 0 := sub_nonpos.mpr (second 3)
  have row1364 : v 4 ≤ 0 := (small 4 (by decide)).le
  have row1365 : v 5 - v 31 ≤ 0 := sub_nonpos.mpr (first 5)
  have row1366 : v 5 - v 47 ≤ 0 := sub_nonpos.mpr (second 5)
  have row1367 : v 6 - v 31 ≤ 0 := sub_nonpos.mpr (first 6)
  have row1368 : v 6 - v 47 ≤ 0 := sub_nonpos.mpr (second 6)
  have row1373 : v 8 ≤ 0 := (small 8 (by decide)).le
  have row1374 : v 9 - v 31 ≤ 0 := sub_nonpos.mpr (first 9)
  have row1375 : v 9 - v 47 ≤ 0 := sub_nonpos.mpr (second 9)
  have row1376 : v 10 - v 31 ≤ 0 := sub_nonpos.mpr (first 10)
  have row1377 : v 10 - v 47 ≤ 0 := sub_nonpos.mpr (second 10)
  have row1390 : v 16 ≤ 0 := (small 16 (by decide)).le
  have row1393 : v 18 - v 31 ≤ 0 := sub_nonpos.mpr (first 18)
  have row1405 : v 24 - v 31 ≤ 0 := sub_nonpos.mpr (first 24)
  have row1422 : v 32 ≤ 0 := (small 32 (by decide)).le
  have row1424 : v 33 - v 47 ≤ 0 := sub_nonpos.mpr (second 33)
  have row1430 : v 36 - v 47 ≤ 0 := sub_nonpos.mpr (second 36)
  have row1482 : -(v 63) ≤ -1 := neg_le_neg (fixed 63 (by decide)).ge
  by_contra! fail
  have bad : (-9) * v 0 + (-6) * v 1 + (-6) * v 2 + (-3) * v 3 + (-6) * v 4 + (-3) * v 5 + (-3) * v 6 + (-6) * v 8 + (-3) * v 9 + (-3) * v 10 + (-3) * v 12 + 3 * v 15 + (-6) * v 16 + (-3) * v 17 + (-3) * v 18 + (-3) * v 20 + 3 * v 23 + (-3) * v 24 + 3 * v 27 + 3 * v 29 + 3 * v 30 + 6 * v 31 + (-6) * v 32 + (-3) * v 33 + (-3) * v 34 + (-3) * v 36 + 3 * v 39 + (-3) * v 40 + 3 * v 43 + 3 * v 45 + 3 * v 46 + 6 * v 47 + (-3) * v 48 + 3 * v 51 + 3 * v 53 + 3 * v 54 + 6 * v 55 + 3 * v 57 + 3 * v 58 + 6 * v 59 + 3 * v 60 + 6 * v 61 + 6 * v 62 + 9 * v 63 ≤ (-1 : ℤ) := by omega
  rcases bit 3 with h3 | h3
  · rcases bit 5 with h5 | h5
    · rcases bit 6 with h6 | h6
      · rcases bit 9 with h9 | h9
        · rcases bit 10 with h10 | h10
          · have falseBound : (0 : ℤ) ≤ (-1 : ℤ) := by
              linear_combination bad + 3 * row438 + 3 * row611 + 3 * row700 + 9 * row1353 + 6 * row1356 + 6 * row1359 + 6 * row1364 + 6 * row1373 + 6 * row1390 + 3 * row1393 + 3 * row1405 + 6 * row1422 + 3 * row1424 + 3 * row1430 + 9 * row1482 + 9997 * (low 3) + 9997 * (low 5) + 9997 * (low 6) + 9997 * (low 9) + 9997 * (low 10) + 3 * (low 15) + 3 * (low 23) + 3 * (low 27) + 3 * (low 29) + 3 * (low 30) + 3 * (low 39) + 3 * (low 43) + 3 * (low 45) + 3 * (low 46) + 3 * (low 51) + 3 * (low 53) + 6 * (low 55) + 3 * (low 58) + 6 * (low 59) + 6 * (low 61) + 6 * (low 62) + 10000 * h3 + 10000 * h5 + 10000 * h6 + 10000 * h9 + 10000 * h10
            omega
          · have falseBound : (0 : ℤ) ≤ (-7 : ℤ) := by
              linear_combination bad + 3 * row334 + 3 * row337 + 3 * row346 + 3 * row349 + 3 * row353 + 6 * row363 + 6 * row366 + 3 * row438 + 3 * row605 + 3 * row643 + 9 * row1353 + 6 * row1356 + 6 * row1359 + 6 * row1364 + 6 * row1373 + 6 * row1376 + 6 * row1377 + 6 * row1390 + 6 * row1422 + 9 * row1482 + 9997 * (low 3) + 9997 * (low 5) + 9997 * (low 6) + 9997 * (low 9) + 9964 * (high 10) + 3 * (low 15) + 3 * (low 17) + 3 * (low 23) + 3 * (high 24) + 3 * (low 29) + 3 * (low 39) + 3 * (low 45) + 3 * (low 53) + 9 * (low 54) + 6 * (low 55) + 9 * (low 57) + 6 * (low 61) + 10000 * h3 + 10000 * h5 + 10000 * h6 + 10000 * h9 - 10000 * h10
            omega
        · have falseBound : (0 : ℤ) ≤ (-7 : ℤ) := by
            linear_combination bad + 3 * row292 + 3 * row299 + 3 * row308 + 3 * row309 + 3 * row311 + 3 * row380 + 3 * row438 + 3 * row612 + 3 * row641 + 9 * row1353 + 6 * row1356 + 6 * row1359 + 6 * row1364 + 6 * row1373 + 6 * row1374 + 6 * row1375 + 6 * row1390 + 6 * row1422 + 9 * row1482 + 9997 * (low 3) + 9997 * (low 5) + 9997 * (low 6) + 9976 * (high 9) + 3 * (low 15) + 3 * (low 23) + 3 * (low 30) + 3 * (low 39) + 3 * (low 46) + 3 * (low 51) + 3 * (low 53) + 3 * (low 54) + 6 * (low 55) + 6 * (low 59) + 6 * (low 61) + 6 * (low 62) + 10000 * h3 + 10000 * h5 + 10000 * h6 - 10000 * h9
          omega
      · have falseBound : (0 : ℤ) ≤ (-7 : ℤ) := by
          linear_combination bad + 3 * row178 + 3 * row181 + 3 * row184 + 3 * row185 + 3 * row196 + 3 * row197 + 3 * row201 + 6 * row208 + 3 * row217 + 3 * row357 + 3 * row497 + 3 * row767 + 3 * row834 + 9 * row1353 + 6 * row1356 + 6 * row1359 + 6 * row1364 + 6 * row1367 + 6 * row1368 + 6 * row1373 + 6 * row1390 + 6 * row1422 + 9 * row1482 + 9997 * (low 3) + 9997 * (low 5) + 9961 * (high 6) + 3 * (low 27) + 3 * (low 29) + 3 * (low 43) + 3 * (low 45) + 6 * (low 49) + 3 * (low 51) + 3 * (low 53) + 3 * (low 57) + 6 * (low 59) + 6 * (low 60) + 6 * (low 61) + 10000 * h3 + 10000 * h5 - 10000 * h6
        omega
    · have falseBound : (0 : ℤ) ≤ (-5 : ℤ) := by
        linear_combination bad + 3 * row137 + 2 * row142 + row143 + 3 * row155 + 3 * row159 + 3 * row165 + row181 + 2 * row188 + 3 * row299 + row415 + row416 + row511 + row637 + 3 * row829 + row979 + 9 * row1353 + 6 * row1356 + 6 * row1359 + 6 * row1364 + 6 * row1365 + 6 * row1366 + 6 * row1373 + 6 * row1390 + 6 * row1422 + 9 * row1482 + 9997 * (low 3) + 9976 * (high 5) + 3 * (low 27) + 2 * (low 30) + 3 * (low 43) + 2 * (low 46) + 3 * (low 51) + 2 * (low 54) + 6 * (low 55) + 3 * (low 58) + 6 * (low 59) + 3 * (low 60) + 5 * (low 61) + 6 * (low 62) + 10000 * h3 - 10000 * h5
      omega
  · have falseBound : (0 : ℤ) ≤ (-3 : ℤ) := by
      linear_combination bad + 2 * row62 + 3 * row65 + 2 * row67 + 2 * row71 + 3 * row73 + 3 * row83 + row85 + 3 * row88 + 2 * row94 + 4 * row99 + row147 + row186 + 2 * row198 + row221 + row254 + 2 * row349 + 3 * row374 + row415 + row668 + row801 + 2 * row830 + 9 * row1353 + 6 * row1356 + 6 * row1359 + 6 * row1360 + 6 * row1361 + 6 * row1364 + 6 * row1373 + 6 * row1390 + 6 * row1422 + 9 * row1482 + 9966 * (high 3) + (low 29) + 3 * (low 30) + 3 * (low 45) + (low 46) + 3 * (low 53) + 7 * (low 54) + 3 * (low 57) + (low 58) + 6 * (low 59) + 3 * (low 60) + 6 * (low 61) + 6 * (low 62) - 10000 * h3
    omega

lemma layer6_4 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (first : ∀ i, v i ≤ v (i ||| 31))
    (second : ∀ i, v i ≤ v (i ||| 47))
    (small : ∀ i ∈ ([0] : List ℕ), v i=0)
    (fixed : ∀ i ∈ ([63] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-8) * v 0 + (-5) * v 1 + (-5) * v 2 + (-2) * v 3 + (-5) * v 4 + (-2) * v 5 + (-2) * v 6 + 1 * v 7 + (-5) * v 8 + (-2) * v 9 + (-2) * v 10 + 1 * v 11 + (-2) * v 12 + 1 * v 13 + 1 * v 14 + 4 * v 15 + (-5) * v 16 + (-2) * v 17 + (-2) * v 18 + 1 * v 19 + (-2) * v 20 + 1 * v 21 + 1 * v 22 + 4 * v 23 + (-2) * v 24 + 1 * v 25 + 1 * v 26 + 4 * v 27 + 1 * v 28 + 4 * v 29 + 4 * v 30 + 7 * v 31 + (-5) * v 32 + (-2) * v 33 + (-2) * v 34 + 1 * v 35 + (-2) * v 36 + 1 * v 37 + 1 * v 38 + 4 * v 39 + (-2) * v 40 + 1 * v 41 + 1 * v 42 + 4 * v 43 + 1 * v 44 + 4 * v 45 + 4 * v 46 + 7 * v 47 + (-2) * v 48 + 1 * v 49 + 1 * v 50 + 4 * v 51 + 1 * v 52 + 4 * v 53 + 4 * v 54 + 7 * v 55 + 1 * v 56 + 4 * v 57 + 4 * v 58 + 7 * v 59 + 4 * v 60 + 7 * v 61 + 7 * v 62 + 10 * v 63 := by
  have low (i : ℕ) : -v i ≤ 0 := by rcases bit i with h|h <;> omega
  have high (i : ℕ) : v i ≤ 1 := by rcases bit i with h|h <;> omega
  have row0 : v 1 + v 2 - v 3 ≤ 1 := join 1 2
  have row1 : v 1 + v 4 - v 5 ≤ 1 := join 1 4
  have row2 : v 1 + v 6 - v 7 ≤ 1 := join 1 6
  have row3 : v 1 + v 8 - v 9 ≤ 1 := join 1 8
  have row4 : v 1 + v 10 - v 11 ≤ 1 := join 1 10
  have row5 : v 1 + v 12 - v 13 ≤ 1 := join 1 12
  have row6 : v 1 + v 14 - v 15 ≤ 1 := join 1 14
  have row7 : v 1 + v 16 - v 17 ≤ 1 := join 1 16
  have row8 : v 1 + v 18 - v 19 ≤ 1 := join 1 18
  have row9 : v 1 + v 20 - v 21 ≤ 1 := join 1 20
  have row10 : v 1 + v 22 - v 23 ≤ 1 := join 1 22
  have row11 : v 1 + v 24 - v 25 ≤ 1 := join 1 24
  have row12 : v 1 + v 26 - v 27 ≤ 1 := join 1 26
  have row13 : v 1 + v 28 - v 29 ≤ 1 := join 1 28
  have row15 : v 1 + v 32 - v 33 ≤ 1 := join 1 32
  have row16 : v 1 + v 34 - v 35 ≤ 1 := join 1 34
  have row17 : v 1 + v 36 - v 37 ≤ 1 := join 1 36
  have row18 : v 1 + v 38 - v 39 ≤ 1 := join 1 38
  have row19 : v 1 + v 40 - v 41 ≤ 1 := join 1 40
  have row20 : v 1 + v 42 - v 43 ≤ 1 := join 1 42
  have row21 : v 1 + v 44 - v 45 ≤ 1 := join 1 44
  have row23 : v 1 + v 48 - v 49 ≤ 1 := join 1 48
  have row24 : v 1 + v 50 - v 51 ≤ 1 := join 1 50
  have row25 : v 1 + v 52 - v 53 ≤ 1 := join 1 52
  have row26 : v 1 + v 54 - v 55 ≤ 1 := join 1 54
  have row27 : v 1 + v 56 - v 57 ≤ 1 := join 1 56
  have row28 : v 1 + v 58 - v 59 ≤ 1 := join 1 58
  have row29 : v 1 + v 60 - v 61 ≤ 1 := join 1 60
  have row31 : v 2 + v 4 - v 6 ≤ 1 := join 2 4
  have row32 : v 2 + v 5 - v 7 ≤ 1 := join 2 5
  have row33 : v 2 + v 8 - v 10 ≤ 1 := join 2 8
  have row34 : v 2 + v 9 - v 11 ≤ 1 := join 2 9
  have row35 : v 2 + v 12 - v 14 ≤ 1 := join 2 12
  have row36 : v 2 + v 13 - v 15 ≤ 1 := join 2 13
  have row37 : v 2 + v 16 - v 18 ≤ 1 := join 2 16
  have row38 : v 2 + v 17 - v 19 ≤ 1 := join 2 17
  have row39 : v 2 + v 20 - v 22 ≤ 1 := join 2 20
  have row40 : v 2 + v 21 - v 23 ≤ 1 := join 2 21
  have row41 : v 2 + v 24 - v 26 ≤ 1 := join 2 24
  have row42 : v 2 + v 25 - v 27 ≤ 1 := join 2 25
  have row43 : v 2 + v 28 - v 30 ≤ 1 := join 2 28
  have row45 : v 2 + v 32 - v 34 ≤ 1 := join 2 32
  have row46 : v 2 + v 33 - v 35 ≤ 1 := join 2 33
  have row47 : v 2 + v 36 - v 38 ≤ 1 := join 2 36
  have row48 : v 2 + v 37 - v 39 ≤ 1 := join 2 37
  have row49 : v 2 + v 40 - v 42 ≤ 1 := join 2 40
  have row50 : v 2 + v 41 - v 43 ≤ 1 := join 2 41
  have row51 : v 2 + v 44 - v 46 ≤ 1 := join 2 44
  have row53 : v 2 + v 48 - v 50 ≤ 1 := join 2 48
  have row54 : v 2 + v 49 - v 51 ≤ 1 := join 2 49
  have row55 : v 2 + v 52 - v 54 ≤ 1 := join 2 52
  have row56 : v 2 + v 53 - v 55 ≤ 1 := join 2 53
  have row58 : v 2 + v 57 - v 59 ≤ 1 := join 2 57
  have row59 : v 2 + v 60 - v 62 ≤ 1 := join 2 60
  have row61 : v 3 + v 4 - v 7 ≤ 1 := join 3 4
  have row62 : v 3 + v 5 - v 7 ≤ 1 := join 3 5
  have row63 : v 3 + v 6 - v 7 ≤ 1 := join 3 6
  have row64 : v 3 + v 8 - v 11 ≤ 1 := join 3 8
  have row65 : v 3 + v 9 - v 11 ≤ 1 := join 3 9
  have row66 : v 3 + v 10 - v 11 ≤ 1 := join 3 10
  have row67 : v 3 + v 12 - v 15 ≤ 1 := join 3 12
  have row68 : v 3 + v 13 - v 15 ≤ 1 := join 3 13
  have row70 : v 3 + v 16 - v 19 ≤ 1 := join 3 16
  have row71 : v 3 + v 17 - v 19 ≤ 1 := join 3 17
  have row73 : v 3 + v 20 - v 23 ≤ 1 := join 3 20
  have row74 : v 3 + v 21 - v 23 ≤ 1 := join 3 21
  have row76 : v 3 + v 24 - v 27 ≤ 1 := join 3 24
  have row77 : v 3 + v 25 - v 27 ≤ 1 := join 3 25
  have row82 : v 3 + v 32 - v 35 ≤ 1 := join 3 32
  have row83 : v 3 + v 33 - v 35 ≤ 1 := join 3 33
  have row85 : v 3 + v 36 - v 39 ≤ 1 := join 3 36
  have row86 : v 3 + v 37 - v 39 ≤ 1 := join 3 37
  have row88 : v 3 + v 40 - v 43 ≤ 1 := join 3 40
  have row89 : v 3 + v 41 - v 43 ≤ 1 := join 3 41
  have row99 : v 3 + v 54 - v 55 ≤ 1 := join 3 54
  have row101 : v 3 + v 57 - v 59 ≤ 1 := join 3 57
  have row106 : v 4 + v 8 - v 12 ≤ 1 := join 4 8
  have row107 : v 4 + v 9 - v 13 ≤ 1 := join 4 9
  have row108 : v 4 + v 10 - v 14 ≤ 1 := join 4 10
  have row109 : v 4 + v 11 - v 15 ≤ 1 := join 4 11
  have row110 : v 4 + v 16 - v 20 ≤ 1 := join 4 16
  have row111 : v 4 + v 17 - v 21 ≤ 1 := join 4 17
  have row112 : v 4 + v 18 - v 22 ≤ 1 := join 4 18
  have row113 : v 4 + v 19 - v 23 ≤ 1 := join 4 19
  have row114 : v 4 + v 24 - v 28 ≤ 1 := join 4 24
  have row115 : v 4 + v 25 - v 29 ≤ 1 := join 4 25
  have row116 : v 4 + v 26 - v 30 ≤ 1 := join 4 26
  have row118 : v 4 + v 32 - v 36 ≤ 1 := join 4 32
  have row119 : v 4 + v 33 - v 37 ≤ 1 := join 4 33
  have row120 : v 4 + v 34 - v 38 ≤ 1 := join 4 34
  have row121 : v 4 + v 35 - v 39 ≤ 1 := join 4 35
  have row122 : v 4 + v 40 - v 44 ≤ 1 := join 4 40
  have row123 : v 4 + v 41 - v 45 ≤ 1 := join 4 41
  have row124 : v 4 + v 42 - v 46 ≤ 1 := join 4 42
  have row126 : v 4 + v 48 - v 52 ≤ 1 := join 4 48
  have row127 : v 4 + v 49 - v 53 ≤ 1 := join 4 49
  have row128 : v 4 + v 50 - v 54 ≤ 1 := join 4 50
  have row130 : v 4 + v 56 - v 60 ≤ 1 := join 4 56
  have row131 : v 4 + v 57 - v 61 ≤ 1 := join 4 57
  have row132 : v 4 + v 58 - v 62 ≤ 1 := join 4 58
  have row134 : v 5 + v 6 - v 7 ≤ 1 := join 5 6
  have row135 : v 5 + v 8 - v 13 ≤ 1 := join 5 8
  have row136 : v 5 + v 9 - v 13 ≤ 1 := join 5 9
  have row141 : v 5 + v 16 - v 21 ≤ 1 := join 5 16
  have row143 : v 5 + v 18 - v 23 ≤ 1 := join 5 18
  have row145 : v 5 + v 20 - v 21 ≤ 1 := join 5 20
  have row148 : v 5 + v 25 - v 29 ≤ 1 := join 5 25
  have row153 : v 5 + v 32 - v 37 ≤ 1 := join 5 32
  have row155 : v 5 + v 34 - v 39 ≤ 1 := join 5 34
  have row157 : v 5 + v 36 - v 37 ≤ 1 := join 5 36
  have row159 : v 5 + v 40 - v 45 ≤ 1 := join 5 40
  have row166 : v 5 + v 49 - v 53 ≤ 1 := join 5 49
  have row168 : v 5 + v 51 - v 55 ≤ 1 := join 5 51
  have row169 : v 5 + v 52 - v 53 ≤ 1 := join 5 52
  have row170 : v 5 + v 54 - v 55 ≤ 1 := join 5 54
  have row172 : v 5 + v 57 - v 61 ≤ 1 := join 5 57
  have row177 : v 6 + v 8 - v 14 ≤ 1 := join 6 8
  have row178 : v 6 + v 9 - v 15 ≤ 1 := join 6 9
  have row179 : v 6 + v 10 - v 14 ≤ 1 := join 6 10
  have row183 : v 6 + v 16 - v 22 ≤ 1 := join 6 16
  have row184 : v 6 + v 17 - v 23 ≤ 1 := join 6 17
  have row185 : v 6 + v 18 - v 22 ≤ 1 := join 6 18
  have row189 : v 6 + v 24 - v 30 ≤ 1 := join 6 24
  have row191 : v 6 + v 26 - v 30 ≤ 1 := join 6 26
  have row193 : v 6 + v 28 - v 30 ≤ 1 := join 6 28
  have row195 : v 6 + v 32 - v 38 ≤ 1 := join 6 32
  have row196 : v 6 + v 33 - v 39 ≤ 1 := join 6 33
  have row197 : v 6 + v 34 - v 38 ≤ 1 := join 6 34
  have row199 : v 6 + v 36 - v 38 ≤ 1 := join 6 36
  have row200 : v 6 + v 37 - v 39 ≤ 1 := join 6 37
  have row201 : v 6 + v 40 - v 46 ≤ 1 := join 6 40
  have row203 : v 6 + v 42 - v 46 ≤ 1 := join 6 42
  have row207 : v 6 + v 48 - v 54 ≤ 1 := join 6 48
  have row210 : v 6 + v 51 - v 55 ≤ 1 := join 6 51
  have row211 : v 6 + v 52 - v 54 ≤ 1 := join 6 52
  have row220 : v 7 + v 9 - v 15 ≤ 1 := join 7 9
  have row221 : v 7 + v 10 - v 15 ≤ 1 := join 7 10
  have row224 : v 7 + v 13 - v 15 ≤ 1 := join 7 13
  have row226 : v 7 + v 16 - v 23 ≤ 1 := join 7 16
  have row228 : v 7 + v 18 - v 23 ≤ 1 := join 7 18
  have row229 : v 7 + v 19 - v 23 ≤ 1 := join 7 19
  have row231 : v 7 + v 21 - v 23 ≤ 1 := join 7 21
  have row232 : v 7 + v 22 - v 23 ≤ 1 := join 7 22
  have row241 : v 7 + v 33 - v 39 ≤ 1 := join 7 33
  have row242 : v 7 + v 34 - v 39 ≤ 1 := join 7 34
  have row255 : v 7 + v 49 - v 55 ≤ 1 := join 7 49
  have row260 : v 7 + v 54 - v 55 ≤ 1 := join 7 54
  have row268 : v 8 + v 16 - v 24 ≤ 1 := join 8 16
  have row270 : v 8 + v 18 - v 26 ≤ 1 := join 8 18
  have row272 : v 8 + v 20 - v 28 ≤ 1 := join 8 20
  have row273 : v 8 + v 21 - v 29 ≤ 1 := join 8 21
  have row274 : v 8 + v 22 - v 30 ≤ 1 := join 8 22
  have row276 : v 8 + v 32 - v 40 ≤ 1 := join 8 32
  have row277 : v 8 + v 33 - v 41 ≤ 1 := join 8 33
  have row278 : v 8 + v 34 - v 42 ≤ 1 := join 8 34
  have row279 : v 8 + v 35 - v 43 ≤ 1 := join 8 35
  have row280 : v 8 + v 36 - v 44 ≤ 1 := join 8 36
  have row281 : v 8 + v 37 - v 45 ≤ 1 := join 8 37
  have row282 : v 8 + v 38 - v 46 ≤ 1 := join 8 38
  have row284 : v 8 + v 48 - v 56 ≤ 1 := join 8 48
  have row285 : v 8 + v 49 - v 57 ≤ 1 := join 8 49
  have row286 : v 8 + v 50 - v 58 ≤ 1 := join 8 50
  have row287 : v 8 + v 51 - v 59 ≤ 1 := join 8 51
  have row288 : v 8 + v 52 - v 60 ≤ 1 := join 8 52
  have row289 : v 8 + v 53 - v 61 ≤ 1 := join 8 53
  have row290 : v 8 + v 54 - v 62 ≤ 1 := join 8 54
  have row295 : v 9 + v 16 - v 25 ≤ 1 := join 9 16
  have row297 : v 9 + v 18 - v 27 ≤ 1 := join 9 18
  have row299 : v 9 + v 20 - v 29 ≤ 1 := join 9 20
  have row300 : v 9 + v 21 - v 29 ≤ 1 := join 9 21
  have row303 : v 9 + v 24 - v 25 ≤ 1 := join 9 24
  have row307 : v 9 + v 32 - v 41 ≤ 1 := join 9 32
  have row308 : v 9 + v 33 - v 41 ≤ 1 := join 9 33
  have row309 : v 9 + v 34 - v 43 ≤ 1 := join 9 34
  have row311 : v 9 + v 36 - v 45 ≤ 1 := join 9 36
  have row315 : v 9 + v 40 - v 41 ≤ 1 := join 9 40
  have row319 : v 9 + v 48 - v 57 ≤ 1 := join 9 48
  have row320 : v 9 + v 49 - v 57 ≤ 1 := join 9 49
  have row322 : v 9 + v 51 - v 59 ≤ 1 := join 9 51
  have row327 : v 9 + v 56 - v 57 ≤ 1 := join 9 56
  have row329 : v 9 + v 60 - v 61 ≤ 1 := join 9 60
  have row331 : v 10 + v 12 - v 14 ≤ 1 := join 10 12
  have row332 : v 10 + v 13 - v 15 ≤ 1 := join 10 13
  have row333 : v 10 + v 16 - v 26 ≤ 1 := join 10 16
  have row334 : v 10 + v 17 - v 27 ≤ 1 := join 10 17
  have row335 : v 10 + v 18 - v 26 ≤ 1 := join 10 18
  have row336 : v 10 + v 19 - v 27 ≤ 1 := join 10 19
  have row337 : v 10 + v 20 - v 30 ≤ 1 := join 10 20
  have row341 : v 10 + v 24 - v 26 ≤ 1 := join 10 24
  have row343 : v 10 + v 28 - v 30 ≤ 1 := join 10 28
  have row346 : v 10 + v 33 - v 43 ≤ 1 := join 10 33
  have row347 : v 10 + v 34 - v 42 ≤ 1 := join 10 34
  have row348 : v 10 + v 35 - v 43 ≤ 1 := join 10 35
  have row349 : v 10 + v 36 - v 46 ≤ 1 := join 10 36
  have row351 : v 10 + v 38 - v 46 ≤ 1 := join 10 38
  have row353 : v 10 + v 40 - v 42 ≤ 1 := join 10 40
  have row355 : v 10 + v 44 - v 46 ≤ 1 := join 10 44
  have row357 : v 10 + v 48 - v 58 ≤ 1 := join 10 48
  have row359 : v 10 + v 50 - v 58 ≤ 1 := join 10 50
  have row361 : v 10 + v 52 - v 62 ≤ 1 := join 10 52
  have row366 : v 10 + v 57 - v 59 ≤ 1 := join 10 57
  have row369 : v 11 + v 12 - v 15 ≤ 1 := join 11 12
  have row372 : v 11 + v 16 - v 27 ≤ 1 := join 11 16
  have row375 : v 11 + v 19 - v 27 ≤ 1 := join 11 19
  have row386 : v 11 + v 32 - v 43 ≤ 1 := join 11 32
  have row387 : v 11 + v 33 - v 43 ≤ 1 := join 11 33
  have row388 : v 11 + v 34 - v 43 ≤ 1 := join 11 34
  have row394 : v 11 + v 40 - v 43 ≤ 1 := join 11 40
  have row395 : v 11 + v 41 - v 43 ≤ 1 := join 11 41
  have row409 : v 11 + v 57 - v 59 ≤ 1 := join 11 57
  have row414 : v 12 + v 16 - v 28 ≤ 1 := join 12 16
  have row415 : v 12 + v 17 - v 29 ≤ 1 := join 12 17
  have row418 : v 12 + v 20 - v 28 ≤ 1 := join 12 20
  have row419 : v 12 + v 21 - v 29 ≤ 1 := join 12 21
  have row420 : v 12 + v 22 - v 30 ≤ 1 := join 12 22
  have row426 : v 12 + v 32 - v 44 ≤ 1 := join 12 32
  have row427 : v 12 + v 33 - v 45 ≤ 1 := join 12 33
  have row428 : v 12 + v 34 - v 46 ≤ 1 := join 12 34
  have row430 : v 12 + v 36 - v 44 ≤ 1 := join 12 36
  have row431 : v 12 + v 37 - v 45 ≤ 1 := join 12 37
  have row432 : v 12 + v 38 - v 46 ≤ 1 := join 12 38
  have row434 : v 12 + v 40 - v 44 ≤ 1 := join 12 40
  have row438 : v 12 + v 48 - v 60 ≤ 1 := join 12 48
  have row444 : v 12 + v 54 - v 62 ≤ 1 := join 12 54
  have row448 : v 12 + v 58 - v 62 ≤ 1 := join 12 58
  have row451 : v 13 + v 16 - v 29 ≤ 1 := join 13 16
  have row455 : v 13 + v 20 - v 29 ≤ 1 := join 13 20
  have row459 : v 13 + v 24 - v 29 ≤ 1 := join 13 24
  have row465 : v 13 + v 32 - v 45 ≤ 1 := join 13 32
  have row466 : v 13 + v 33 - v 45 ≤ 1 := join 13 33
  have row474 : v 13 + v 41 - v 45 ≤ 1 := join 13 41
  have row488 : v 13 + v 57 - v 61 ≤ 1 := join 13 57
  have row493 : v 14 + v 16 - v 30 ≤ 1 := join 14 16
  have row507 : v 14 + v 32 - v 46 ≤ 1 := join 14 32
  have row580 : v 16 + v 32 - v 48 ≤ 1 := join 16 32
  have row581 : v 16 + v 33 - v 49 ≤ 1 := join 16 33
  have row582 : v 16 + v 34 - v 50 ≤ 1 := join 16 34
  have row583 : v 16 + v 35 - v 51 ≤ 1 := join 16 35
  have row584 : v 16 + v 36 - v 52 ≤ 1 := join 16 36
  have row586 : v 16 + v 38 - v 54 ≤ 1 := join 16 38
  have row587 : v 16 + v 39 - v 55 ≤ 1 := join 16 39
  have row588 : v 16 + v 40 - v 56 ≤ 1 := join 16 40
  have row591 : v 16 + v 43 - v 59 ≤ 1 := join 16 43
  have row592 : v 16 + v 44 - v 60 ≤ 1 := join 16 44
  have row593 : v 16 + v 45 - v 61 ≤ 1 := join 16 45
  have row594 : v 16 + v 46 - v 62 ≤ 1 := join 16 46
  have row596 : v 17 + v 18 - v 19 ≤ 1 := join 17 18
  have row600 : v 17 + v 26 - v 27 ≤ 1 := join 17 26
  have row603 : v 17 + v 32 - v 49 ≤ 1 := join 17 32
  have row604 : v 17 + v 33 - v 49 ≤ 1 := join 17 33
  have row607 : v 17 + v 36 - v 53 ≤ 1 := join 17 36
  have row608 : v 17 + v 37 - v 53 ≤ 1 := join 17 37
  have row611 : v 17 + v 40 - v 57 ≤ 1 := join 17 40
  have row633 : v 18 + v 32 - v 50 ≤ 1 := join 18 32
  have row634 : v 18 + v 33 - v 51 ≤ 1 := join 18 33
  have row636 : v 18 + v 35 - v 51 ≤ 1 := join 18 35
  have row639 : v 18 + v 38 - v 54 ≤ 1 := join 18 38
  have row641 : v 18 + v 40 - v 58 ≤ 1 := join 18 40
  have row649 : v 18 + v 48 - v 50 ≤ 1 := join 18 48
  have row650 : v 18 + v 49 - v 51 ≤ 1 := join 18 49
  have row657 : v 19 + v 20 - v 23 ≤ 1 := join 19 20
  have row660 : v 19 + v 24 - v 27 ≤ 1 := join 19 24
  have row666 : v 19 + v 32 - v 51 ≤ 1 := join 19 32
  have row674 : v 19 + v 40 - v 59 ≤ 1 := join 19 40
  have row682 : v 19 + v 48 - v 51 ≤ 1 := join 19 48
  have row698 : v 20 + v 32 - v 52 ≤ 1 := join 20 32
  have row702 : v 20 + v 36 - v 52 ≤ 1 := join 20 36
  have row706 : v 20 + v 40 - v 60 ≤ 1 := join 20 40
  have row710 : v 20 + v 44 - v 60 ≤ 1 := join 20 44
  have row715 : v 20 + v 49 - v 53 ≤ 1 := join 20 49
  have row729 : v 21 + v 32 - v 53 ≤ 1 := join 21 32
  have row767 : v 22 + v 36 - v 54 ≤ 1 := join 22 36
  have row781 : v 22 + v 50 - v 54 ≤ 1 := join 22 50
  have row828 : v 24 + v 32 - v 56 ≤ 1 := join 24 32
  have row830 : v 24 + v 34 - v 58 ≤ 1 := join 24 34
  have row836 : v 24 + v 40 - v 56 ≤ 1 := join 24 40
  have row838 : v 24 + v 42 - v 58 ≤ 1 := join 24 42
  have row844 : v 24 + v 48 - v 56 ≤ 1 := join 24 48
  have row845 : v 24 + v 49 - v 57 ≤ 1 := join 24 49
  have row846 : v 24 + v 50 - v 58 ≤ 1 := join 24 50
  have row855 : v 25 + v 32 - v 57 ≤ 1 := join 25 32
  have row856 : v 25 + v 33 - v 57 ≤ 1 := join 25 33
  have row863 : v 25 + v 40 - v 57 ≤ 1 := join 25 40
  have row887 : v 26 + v 34 - v 58 ≤ 1 := join 26 34
  have row946 : v 28 + v 32 - v 60 ≤ 1 := join 28 32
  have row1017 : v 30 + v 44 - v 62 ≤ 1 := join 30 44
  have row1081 : v 34 + v 36 - v 38 ≤ 1 := join 34 36
  have row1353 : v 0 ≤ 0 := (small 0 (by decide)).le
  have row1354 : v 1 - v 31 ≤ 0 := sub_nonpos.mpr (first 1)
  have row1355 : v 1 - v 47 ≤ 0 := sub_nonpos.mpr (second 1)
  have row1356 : v 2 - v 31 ≤ 0 := sub_nonpos.mpr (first 2)
  have row1357 : v 2 - v 47 ≤ 0 := sub_nonpos.mpr (second 2)
  have row1358 : v 3 - v 31 ≤ 0 := sub_nonpos.mpr (first 3)
  have row1359 : v 3 - v 47 ≤ 0 := sub_nonpos.mpr (second 3)
  have row1360 : v 4 - v 31 ≤ 0 := sub_nonpos.mpr (first 4)
  have row1361 : v 4 - v 47 ≤ 0 := sub_nonpos.mpr (second 4)
  have row1362 : v 5 - v 31 ≤ 0 := sub_nonpos.mpr (first 5)
  have row1363 : v 5 - v 47 ≤ 0 := sub_nonpos.mpr (second 5)
  have row1365 : v 6 - v 47 ≤ 0 := sub_nonpos.mpr (second 6)
  have row1368 : v 8 - v 31 ≤ 0 := sub_nonpos.mpr (first 8)
  have row1369 : v 8 - v 47 ≤ 0 := sub_nonpos.mpr (second 8)
  have row1370 : v 9 - v 31 ≤ 0 := sub_nonpos.mpr (first 9)
  have row1371 : v 9 - v 47 ≤ 0 := sub_nonpos.mpr (second 9)
  have row1372 : v 10 - v 31 ≤ 0 := sub_nonpos.mpr (first 10)
  have row1373 : v 10 - v 47 ≤ 0 := sub_nonpos.mpr (second 10)
  have row1374 : v 11 - v 31 ≤ 0 := sub_nonpos.mpr (first 11)
  have row1378 : v 13 - v 31 ≤ 0 := sub_nonpos.mpr (first 13)
  have row1381 : v 14 - v 47 ≤ 0 := sub_nonpos.mpr (second 14)
  have row1384 : v 16 - v 31 ≤ 0 := sub_nonpos.mpr (first 16)
  have row1386 : v 17 - v 31 ≤ 0 := sub_nonpos.mpr (first 17)
  have row1392 : v 20 - v 31 ≤ 0 := sub_nonpos.mpr (first 20)
  have row1400 : v 24 - v 31 ≤ 0 := sub_nonpos.mpr (first 24)
  have row1416 : v 32 - v 47 ≤ 0 := sub_nonpos.mpr (second 32)
  have row1420 : v 34 - v 47 ≤ 0 := sub_nonpos.mpr (second 34)
  have row1424 : v 36 - v 47 ≤ 0 := sub_nonpos.mpr (second 36)
  have row1476 : -(v 63) ≤ -1 := neg_le_neg (fixed 63 (by decide)).ge
  by_contra! fail
  have bad : (-8) * v 0 + (-5) * v 1 + (-5) * v 2 + (-2) * v 3 + (-5) * v 4 + (-2) * v 5 + (-2) * v 6 + 1 * v 7 + (-5) * v 8 + (-2) * v 9 + (-2) * v 10 + 1 * v 11 + (-2) * v 12 + 1 * v 13 + 1 * v 14 + 4 * v 15 + (-5) * v 16 + (-2) * v 17 + (-2) * v 18 + 1 * v 19 + (-2) * v 20 + 1 * v 21 + 1 * v 22 + 4 * v 23 + (-2) * v 24 + 1 * v 25 + 1 * v 26 + 4 * v 27 + 1 * v 28 + 4 * v 29 + 4 * v 30 + 7 * v 31 + (-5) * v 32 + (-2) * v 33 + (-2) * v 34 + 1 * v 35 + (-2) * v 36 + 1 * v 37 + 1 * v 38 + 4 * v 39 + (-2) * v 40 + 1 * v 41 + 1 * v 42 + 4 * v 43 + 1 * v 44 + 4 * v 45 + 4 * v 46 + 7 * v 47 + (-2) * v 48 + 1 * v 49 + 1 * v 50 + 4 * v 51 + 1 * v 52 + 4 * v 53 + 4 * v 54 + 7 * v 55 + 1 * v 56 + 4 * v 57 + 4 * v 58 + 7 * v 59 + 4 * v 60 + 7 * v 61 + 7 * v 62 + 10 * v 63 ≤ (-1 : ℤ) := by omega
  rcases bit 1 with h1 | h1
  · rcases bit 2 with h2 | h2
    · rcases bit 4 with h4 | h4
      · rcases bit 8 with h8 | h8
        · rcases bit 16 with h16 | h16
          · have falseBound : (0 : ℤ) ≤ (-1 : ℤ) := by
              linear_combination 2 * bad + 2 * row82 + row85 + 4 * row159 + 2 * row185 + 4 * row357 + 4 * row427 + 2 * row596 + 2 * row1081 + 16 * row1353 + row1359 + 2 * row1365 + 4 * row1370 + 2 * row1386 + 4 * row1392 + 4 * row1400 + 8 * row1416 + 2 * row1420 + row1424 + 20 * row1476 + 19990 * (low 1) + 19990 * (low 2) + 19990 * (low 4) + 2 * (low 7) + 19990 * (low 8) + 2 * (low 11) + 2 * (low 13) + 2 * (low 14) + 8 * (low 15) + 19990 * (low 16) + 2 * (low 21) + 8 * (low 23) + 2 * (low 25) + 2 * (low 26) + 8 * (low 27) + 2 * (low 28) + 8 * (low 29) + 8 * (low 30) + 2 * (low 37) + 7 * (low 39) + 2 * (low 41) + 2 * (low 42) + 8 * (low 43) + 2 * (low 44) + 8 * (low 46) + 2 * (low 49) + 2 * (low 50) + 8 * (low 51) + 2 * (low 52) + 8 * (low 53) + 8 * (low 54) + 14 * (low 55) + 2 * (low 56) + 8 * (low 57) + 4 * (low 58) + 14 * (low 59) + 8 * (low 60) + 14 * (low 61) + 14 * (low 62) + 20000 * h1 + 20000 * h2 + 20000 * h4 + 20000 * h8 + 20000 * h16
            omega
          · have falseBound : (0 : ℤ) ≤ (-11 : ℤ) := by
              linear_combination 3 * bad + 6 * row70 + 3 * row141 + 3 * row183 + 3 * row295 + 3 * row299 + 3 * row333 + 3 * row357 + 3 * row414 + 3 * row415 + 12 * row493 + 6 * row581 + 6 * row582 + 10 * row583 + 3 * row584 + 21 * row587 + row588 + 21 * row591 + 12 * row592 + 21 * row593 + 3 * row607 + 5 * row641 + row650 + 2 * row657 + row682 + row715 + 2 * row844 + row845 + 3 * row846 + 24 * row1353 + 3 * row1363 + 3 * row1365 + 21 * row1384 + 15 * row1416 + 30 * row1476 + 29985 * (low 1) + 29985 * (low 2) + 29985 * (low 4) + 3 * (low 7) + 29985 * (low 8) + 3 * (low 11) + 3 * (low 13) + 15 * (low 14) + 12 * (low 15) + 29860 * (high 16) + 10 * (low 23) + 12 * (low 27) + 6 * (low 29) + 13 * (low 35) + 3 * (low 37) + 3 * (low 38) + 33 * (low 39) + 3 * (low 41) + 3 * (low 42) + 33 * (low 43) + 15 * (low 44) + 33 * (low 45) + 12 * (low 46) + 8 * (low 53) + 12 * (low 54) + 11 * (low 57) + (low 58) + 21 * (low 62) + 30000 * h1 + 30000 * h2 + 30000 * h4 + 30000 * h8 - 30000 * h16
            omega
        · have falseBound : (0 : ℤ) ≤ (-10 : ℤ) := by
            linear_combination 3 * bad + 6 * row64 + 6 * row135 + 3 * row177 + 2 * row183 + row201 + 7 * row268 + 3 * row272 + 7 * row273 + 12 * row274 + 15 * row276 + 3 * row277 + 6 * row278 + 6 * row279 + 3 * row280 + 12 * row281 + 5 * row285 + 21 * row289 + 21 * row290 + 2 * row299 + 4 * row303 + 3 * row341 + 3 * row346 + 3 * row394 + 6 * row438 + 3 * row459 + 3 * row584 + 3 * row588 + 6 * row611 + 6 * row641 + row706 + 3 * row838 + row863 + 24 * row1353 + 21 * row1368 + 21 * row1369 + 30 * row1476 + 29985 * (low 1) + 29985 * (low 2) + 29985 * (low 4) + 3 * (low 7) + 29837 * (high 8) + 12 * (low 15) + 3 * (low 19) + 10 * (low 21) + 13 * (low 22) + 12 * (low 23) + 12 * (low 27) + 9 * (low 35) + 15 * (low 37) + 3 * (low 38) + 12 * (low 39) + 11 * (low 46) + 8 * (low 49) + 3 * (low 50) + 12 * (low 51) + 33 * (low 53) + 33 * (low 54) + 21 * (low 55) + 3 * (low 58) + 21 * (low 59) + 5 * (low 60) + 30000 * h1 + 30000 * h2 + 30000 * h4 - 30000 * h8
          omega
      · rcases bit 8 with h8 | h8
        · have falseBound : (0 : ℤ) ≤ (-10 : ℤ) := by
            linear_combination 3 * bad + 5 * row61 + row82 + 6 * row107 + 6 * row108 + 12 * row109 + 3 * row111 + 6 * row112 + 6 * row114 + 7 * row116 + 6 * row120 + 12 * row121 + 6 * row122 + 10 * row126 + 3 * row127 + 5 * row128 + 21 * row131 + 21 * row132 + 3 * row153 + 3 * row169 + 2 * row193 + 4 * row211 + 2 * row226 + 3 * row426 + 3 * row432 + 3 * row465 + 3 * row493 + 4 * row580 + 6 * row581 + 3 * row607 + 6 * row710 + 3 * row767 + row946 + 24 * row1353 + 21 * row1360 + 21 * row1361 + 30 * row1476 + 29985 * (low 1) + 29985 * (low 2) + 29838 * (high 4) + 29985 * (low 8) + 15 * (low 11) + 3 * (low 19) + 10 * (low 23) + 3 * (low 25) + 10 * (low 26) + 12 * (low 27) + 12 * (low 29) + 14 * (low 35) + 3 * (low 41) + 3 * (low 42) + 12 * (low 43) + 9 * (low 45) + 9 * (low 46) + 8 * (low 50) + 12 * (low 51) + 3 * (low 53) + 21 * (low 55) + 3 * (low 56) + 33 * (low 57) + 33 * (low 58) + 21 * (low 59) + 5 * (low 60) + 30000 * h1 + 30000 * h2 - 30000 * h4 + 30000 * h8
          omega
        · have falseBound : (0 : ℤ) ≤ (-1 : ℤ) := by
            linear_combination bad + row64 + row67 + 9978 * row106 + row107 + row110 + 2 * row111 + row112 + 4 * row113 + 5 * row119 + 2 * row120 + 4 * row121 + 3 * row124 + 4 * row130 + 2 * row145 + 2 * row189 + row270 + 5 * row284 + 6 * row287 + row307 + row331 + row353 + row414 + 2 * row419 + 2 * row420 + row430 + 4 * row431 + row432 + 7 * row448 + 3 * row580 + row674 + row702 + row729 + 8 * row1353 + 7 * row1368 + 7 * row1369 + 10 * row1476 + 9995 * (low 1) + 9995 * (low 2) + (low 7) + 9960 * (high 12) + 3 * (low 15) + 6 * (low 19) + 2 * (low 22) + (low 25) + 4 * (low 27) + 2 * (low 29) + 3 * (low 33) + 5 * (low 35) + 3 * (low 42) + 4 * (low 43) + (low 49) + (low 50) + 10 * (low 51) + 3 * (low 53) + 4 * (low 54) + 7 * (low 55) + 4 * (low 57) + 11 * (low 58) + 7 * (low 61) + 10000 * h1 + 10000 * h2 - 10000 * h4 - 10000 * h8
          omega
    · rcases bit 4 with h4 | h4
      · rcases bit 16 with h16 | h16
        · have falseBound : (0 : ℤ) ≤ (-10 : ℤ) := by
            linear_combination 3 * bad + 3 * row32 + 6 * row34 + 3 * row35 + 12 * row36 + 3 * row38 + 3 * row39 + 3 * row41 + 11 * row42 + 9 * row43 + 3 * row46 + 12 * row48 + 5 * row49 + 10 * row51 + 3 * row53 + 11 * row55 + 21 * row59 + 6 * row64 + 3 * row143 + 4 * row195 + 2 * row203 + 6 * row280 + 3 * row284 + row334 + 3 * row337 + 2 * row346 + 6 * row386 + 3 * row388 + 3 * row426 + 2 * row603 + row634 + row639 + row641 + 3 * row830 + 24 * row1353 + 21 * row1356 + 29876 * row1357 + 30 * row1476 + 29985 * (low 1) + 29985 * (low 4) + 15 * (low 13) + 29985 * (low 16) + 3 * (low 21) + 9 * (low 23) + 14 * (low 25) + 12 * (low 28) + 12 * (low 29) + 15 * (low 37) + 3 * (low 41) + (low 43) + 4 * (low 44) + 12 * (low 45) + 29855 * (high 47) + (low 49) + 11 * (low 51) + 14 * (low 52) + 12 * (low 53) + 21 * (low 55) + 12 * (low 57) + 8 * (low 58) + 21 * (low 59) + 33 * (low 60) + 21 * (low 61) + 30000 * h1 - 30000 * h2 + 30000 * h4 + 30000 * h16
          omega
        · have falseBound : (0 : ℤ) ≤ (-1 : ℤ) := by
            linear_combination bad + 2 * row32 + 4 * row33 + 2 * row34 + 4 * row36 + 4 * row37 + 2 * row38 + 2 * row39 + row41 + 4 * row43 + 4 * row45 + 2 * row46 + 2 * row47 + 4 * row51 + 2 * row53 + 3 * row54 + 7 * row58 + 2 * row66 + 2 * row197 + row228 + row278 + 3 * row333 + 3 * row372 + 2 * row414 + row465 + row588 + row636 + 3 * row639 + row641 + row660 + row781 + 3 * row887 + 8 * row1353 + 7 * row1356 + 6 * row1357 + row1373 + 10 * row1476 + 9995 * (low 1) + 9943 * (high 2) + 9995 * (low 4) + 6 * (low 13) + (low 14) + 9992 * (high 16) + (low 21) + 3 * (low 23) + (low 25) + 3 * (low 28) + 4 * (low 29) + (low 37) + 4 * (low 39) + (low 41) + 4 * (low 43) + 5 * (low 44) + 3 * (low 45) + 4 * (low 49) + (low 52) + 4 * (low 53) + 7 * (low 55) + 11 * (low 57) + 4 * (low 60) + 7 * (low 61) + 7 * (low 62) + 10000 * h1 - 10000 * h2 + 10000 * h4 - 10000 * h16
          omega
      · rcases bit 8 with h8 | h8
        · have falseBound : (0 : ℤ) ≤ (-1 : ℤ) := by
            linear_combination bad + 9965 * row31 + row34 + row35 + row39 + 4 * row43 + row45 + row46 + 4 * row50 + 2 * row51 + 11 * row54 + 7 * row58 + 7 * row59 + row61 + row70 + row107 + row111 + 4 * row114 + 4 * row115 + 3 * row120 + 2 * row122 + row126 + 4 * row127 + row128 + 2 * row157 + 4 * row184 + 3 * row196 + row200 + 3 * row207 + 7 * row210 + 2 * row351 + row418 + 2 * row580 + 2 * row633 + 8 * row1353 + 7 * row1360 + 7 * row1361 + 10 * row1476 + 9995 * (low 1) + 4 * (high 4) + 9949 * (high 6) + 9995 * (low 8) + 4 * (low 15) + 2 * (high 16) + 3 * (low 17) + 2 * (low 24) + 5 * (low 25) + (low 26) + 4 * (low 27) + 2 * (low 33) + 5 * (low 41) + (low 42) + (low 44) + 4 * (low 45) + 16 * (low 49) + (low 56) + 11 * (low 57) + 4 * (low 58) + 11 * (low 60) + 7 * (low 61) + 10000 * h1 - 10000 * h2 - 10000 * h4 + 10000 * h8
          omega
        · have falseBound : (0 : ℤ) ≤ (-1 : ℤ) := by
            linear_combination bad + row32 + 9980 * row33 + 2 * row34 + row36 + 5 * row38 + 4 * row40 + 3 * row45 + 4 * row54 + 5 * row59 + 2 * row66 + row109 + 5 * row110 + 5 * row111 + 2 * row112 + 4 * row121 + 3 * row122 + 4 * row123 + 4 * row124 + 2 * row126 + 8 * row130 + row135 + row179 + row199 + 7 * row272 + 2 * row276 + 2 * row277 + 5 * row278 + 4 * row279 + row288 + 4 * row336 + row341 + 6 * row343 + 4 * row359 + 7 * row366 + 2 * row369 + row767 + row836 + 2 * row1017 + 8 * row1353 + 7 * row1361 + 7 * row1372 + 10 * row1476 + 9995 * (low 1) + 9960 * (high 4) + 3 * (high 8) + 9950 * (high 10) + (low 13) + 8 * (low 17) + (low 25) + 4 * (low 29) + 9 * (low 35) + (low 37) + 3 * (low 41) + 5 * (low 49) + 5 * (low 50) + 4 * (low 53) + 3 * (low 54) + 7 * (low 55) + 8 * (low 56) + 11 * (low 57) + 7 * (low 61) + 10000 * h1 - 10000 * h2 - 10000 * h4 - 10000 * h8
          omega
  · rcases bit 2 with h2 | h2
    · rcases bit 4 with h4 | h4
      · rcases bit 16 with h16 | h16
        · have falseBound : (0 : ℤ) ≤ (-10 : ℤ) := by
            linear_combination 3 * bad + 6 * row2 + 11 * row3 + 6 * row4 + 12 * row6 + 5 * row8 + 6 * row9 + 6 * row11 + 12 * row12 + 6 * row15 + 6 * row16 + 3 * row17 + 6 * row19 + 5 * row21 + 10 * row24 + 12 * row25 + 21 * row26 + 3 * row27 + 21 * row28 + 21 * row29 + 2 * row85 + 4 * row89 + 3 * row136 + 3 * row148 + 3 * row241 + row270 + 3 * row279 + 3 * row300 + row307 + row311 + 6 * row319 + 3 * row320 + 3 * row387 + 6 * row427 + 6 * row603 + 2 * row666 + 24 * row1353 + 21 * row1354 + 21 * row1355 + 30 * row1476 + 29795 * (high 1) + 29985 * (low 2) + 29985 * (low 4) + 15 * (low 14) + 29985 * (low 16) + 3 * (low 22) + 12 * (low 23) + 14 * (low 26) + 3 * (low 28) + 6 * (low 29) + 12 * (low 30) + 3 * (low 38) + 7 * (low 39) + 3 * (low 42) + 2 * (low 43) + 8 * (low 44) + 12 * (low 46) + 13 * (low 50) + 15 * (low 52) + 33 * (low 54) + 6 * (low 56) + 33 * (low 58) + 33 * (low 60) + 21 * (low 62) - 30000 * h1 + 30000 * h2 + 30000 * h4 + 30000 * h16
          omega
        · have falseBound : (0 : ℤ) ≤ (-1 : ℤ) := by
            linear_combination bad + 2 * row2 + 5 * row3 + row4 + 2 * row5 + 4 * row6 + row8 + 2 * row9 + 3 * row10 + row11 + 3 * row12 + row13 + 4 * row16 + 2 * row17 + row19 + 3 * row20 + row23 + 3 * row25 + 7 * row26 + 7 * row28 + 7 * row29 + row83 + row88 + 2 * row141 + row226 + 4 * row295 + 3 * row300 + 5 * row333 + row466 + 4 * row583 + 11 * row586 + 11 * row592 + 7 * row594 + row600 + row608 + row649 + row828 + 4 * row855 + 8 * row1353 + 7 * row1355 + 7 * row1384 + 10 * row1476 + 9938 * (high 1) + 9995 * (low 2) + 9995 * (low 4) + 4 * (low 10) + 5 * (low 14) + 9953 * (high 16) + 4 * (low 22) + 2 * (low 28) + 4 * (low 30) + 2 * (low 34) + 12 * (low 38) + 4 * (low 39) + 4 * (low 42) + 12 * (low 44) + 3 * (low 45) + 11 * (low 46) + 4 * (low 52) + 11 * (low 58) - 10000 * h1 + 10000 * h2 + 10000 * h4 - 10000 * h16
          omega
      · rcases bit 8 with h8 | h8
        · have falseBound : (0 : ℤ) ≤ (-1 : ℤ) := by
            linear_combination bad + 21 * row1 + row4 + 2 * row5 + 4 * row6 + 4 * row8 + row16 + 2 * row23 + 7 * row28 + 7 * row29 + row61 + row70 + 4 * row113 + row114 + row120 + row141 + row157 + 3 * row159 + 3 * row166 + 7 * row168 + row169 + 2 * row196 + row295 + row311 + row333 + row451 + 2 * row603 + 2 * row698 + row828 + 8 * row1353 + 7 * row1355 + 7 * row1362 + 10 * row1476 + 9949 * (high 1) + 9995 * (low 2) + 9977 * (high 4) + 9995 * (low 8) + 5 * (low 14) + 2 * (low 18) + (low 22) + 4 * (low 27) + 3 * (low 29) + 4 * (low 30) + 2 * (low 39) + (low 40) + (low 41) + (low 42) + 4 * (low 43) + (low 44) + 4 * (low 46) + (low 50) + 11 * (low 51) + 4 * (low 54) + 4 * (low 57) + 11 * (low 58) + 11 * (low 60) + 7 * (low 62) - 10000 * h1 + 10000 * h2 - 10000 * h4 + 10000 * h8
          omega
        · have falseBound : (0 : ℤ) ≤ (-1 : ℤ) := by
            linear_combination bad + 22 * row1 + 30 * row3 + 9937 * row5 + 4 * row10 + row11 + 11 * row24 + 2 * row68 + 9955 * row106 + row108 + 2 * row110 + 2 * row111 + 9 * row112 + row114 + row118 + row119 + row126 + 4 * row127 + 6 * row128 + 2 * row134 + 4 * row136 + 3 * row141 + 4 * row153 + 4 * row155 + 7 * row170 + row220 + 4 * row273 + row278 + 4 * row281 + 4 * row286 + 4 * row297 + row308 + 4 * row309 + row319 + 10 * row320 + 7 * row322 + row332 + 4 * row420 + 4 * row428 + 3 * row430 + 2 * row434 + 7 * row444 + 7 * row488 + 4 * row710 + 8 * row1353 + 7 * row1369 + 7 * row1378 + 10 * row1476 + 9995 * (low 2) + (low 11) + 9923 * (high 13) + 11 * (low 18) + (low 19) + (low 26) + 11 * (low 34) + (low 35) + (low 38) + 15 * (low 49) + 22 * (low 50) + 12 * (low 54) + (low 56) - 10000 * h1 + 10000 * h2 - 10000 * h4 - 10000 * h8
          omega
    · rcases bit 4 with h4 | h4
      · rcases bit 8 with h8 | h8
        · have falseBound : (0 : ℤ) ≤ (-5 : ℤ) := by
            linear_combination 5 * bad + 49866 * row0 + 5 * row4 + 5 * row5 + 20 * row6 + 11 * row7 + 21 * row9 + 6 * row11 + 16 * row15 + 19 * row17 + row18 + 10 * row19 + 20 * row21 + 5 * row23 + 20 * row25 + 25 * row35 + 14 * row37 + 5 * row39 + 20 * row51 + 5 * row53 + 55 * row55 + 35 * row59 + 10 * row62 + 4 * row63 + 16 * row65 + 21 * row71 + 16 * row74 + 4 * row76 + 25 * row83 + 14 * row86 + 20 * row89 + 35 * row99 + 35 * row101 + 6 * row195 + 4 * row228 + 5 * row242 + 5 * row347 + 16 * row375 + 20 * row636 + row856 + 40 * row1353 + 35 * row1358 + 35 * row1359 + 50 * row1476 + 49606 * (high 3) + 49975 * (low 4) + 49975 * (low 8) + 6 * (low 9) + 20 * (low 12) + 16 * (low 20) + 5 * (low 26) + 5 * (low 28) + 20 * (low 29) + 20 * (low 30) + 3 * (high 32) + 9 * (low 36) + 15 * (low 41) + 45 * (low 44) + 80 * (low 52) + 5 * (low 56) + 54 * (low 57) + 20 * (low 58) + 55 * (low 60) + 35 * (low 61) - 50000 * h1 - 50000 * h2 + 50000 * h4 + 50000 * h8
          omega
        · have falseBound : (0 : ℤ) ≤ (-2 : ℤ) := by
            linear_combination 2 * bad + 26 * row3 + 19939 * row4 + 2 * row6 + 10 * row8 + 4 * row10 + 2 * row11 + 10 * row15 + 4 * row16 + 2 * row17 + 8 * row18 + 2 * row32 + 19958 * row33 + 4 * row35 + 6 * row37 + 2 * row41 + 2 * row49 + 6 * row51 + 2 * row53 + 14 * row56 + 14 * row59 + 4 * row73 + 2 * row135 + 6 * row178 + 4 * row284 + 6 * row285 + 14 * row287 + 2 * row315 + 2 * row327 + 14 * row329 + 8 * row343 + 6 * row346 + 2 * row348 + 2 * row349 + 8 * row375 + 4 * row581 + 4 * row604 + 16 * row1353 + 3 * row1355 + 6 * row1371 + 5 * row1373 + 19929 * row1374 + 20 * row1476 + 19990 * (low 4) + 2 * (low 6) + 2 * (low 21) + 6 * (low 22) + 10 * (low 28) + 8 * (low 29) + 19915 * (high 31) + 10 * (low 38) + 8 * (low 44) + 8 * (low 45) + 2 * (low 48) + 22 * (low 51) + 2 * (low 52) + 22 * (low 53) + 8 * (low 54) + 8 * (low 58) + 36 * (low 60) - 20000 * h1 - 20000 * h2 + 20000 * h4 - 20000 * h8
          omega
      · rcases bit 8 with h8 | h8
        · have falseBound : (0 : ℤ) ≤ (-1 : ℤ) := by
            linear_combination bad + 4971 * row0 + 4969 * row1 + 13 * row2 + row5 + 5 * row7 + 2 * row8 + 2 * row11 + 3 * row12 + 4 * row13 + row15 + row16 + 2 * row17 + row19 + 9 * row24 + 3 * row25 + 11 * row27 + 7 * row28 + 5023 * row31 + row35 + 2 * row39 + 3 * row45 + row49 + 4 * row50 + row77 + 3 * row111 + 4 * row123 + 2 * row126 + 4 * row130 + 7 * row172 + 2 * row178 + 4 * row191 + row195 + 5 * row210 + 4 * row211 + 2 * row221 + row229 + 2 * row231 + row232 + 4 * row242 + 2 * row255 + 3 * row604 + row608 + 8 * row1353 + 4964 * row1362 + 7 * row1365 + 10 * row1476 + 4972 * (high 3) + 4989 * (high 6) + 9995 * (low 8) + (low 11) + 8 * (low 26) + 5 * (low 28) + 4957 * (high 31) + 8 * (low 41) + (low 44) + 4 * (low 46) + 10 * (low 50) + 6 * (low 52) + 16 * (low 56) + 11 * (low 58) + 7 * (low 62) - 10000 * h1 - 10000 * h2 - 10000 * h4 + 10000 * h8
          omega
        · have falseBound : (0 : ℤ) ≤ (-1 : ℤ) := by
            linear_combination bad + 11 * row0 + 9950 * row1 + 7 * row3 + row11 + 4 * row12 + 12 * row15 + row16 + 2 * row23 + 10 * row27 + 7 * row29 + 12 * row32 + 8 * row33 + 10 * row35 + row37 + 4 * row43 + 2 * row47 + 4 * row48 + row53 + 10 * row55 + 12 * row64 + row71 + 8 * row106 + row111 + 5 * row114 + 5 * row119 + 2 * row122 + 34 * row126 + 9936 * row135 + 4 * row169 + row185 + row211 + 4 * row224 + 7 * row260 + 4 * row268 + 9 * row277 + row278 + row282 + row285 + 11 * row288 + 2 * row335 + row355 + 7 * row361 + 4 * row395 + 7 * row409 + 2 * row455 + 4 * row474 + 2 * row507 + 8 * row1353 + 7 * row1368 + 7 * row1381 + 10 * row1476 + 9942 * (high 2) + 9 * (high 9) + 9925 * (high 13) + 4 * (low 23) + 3 * (low 26) + 2 * (low 29) + 9 * (low 32) + 35 * (low 48) + 4 * (low 51) + 11 * (low 56) + 4 * (low 58) - 10000 * h1 - 10000 * h2 - 10000 * h4 - 10000 * h8
          omega

lemma layer6_5 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (first : ∀ i, v i ≤ v (i ||| 31))
    (second : ∀ i, v i ≤ v (i ||| 47))
    (fixed : ∀ i ∈ ([63] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-7) * v 0 + (-4) * v 1 + (-4) * v 2 + (-1) * v 3 + (-4) * v 4 + (-1) * v 5 + (-1) * v 6 + 2 * v 7 + (-4) * v 8 + (-1) * v 9 + (-1) * v 10 + 2 * v 11 + (-1) * v 12 + 2 * v 13 + 2 * v 14 + 5 * v 15 + (-4) * v 16 + (-1) * v 17 + (-1) * v 18 + 2 * v 19 + (-1) * v 20 + 2 * v 21 + 2 * v 22 + 5 * v 23 + (-1) * v 24 + 2 * v 25 + 2 * v 26 + 5 * v 27 + 2 * v 28 + 5 * v 29 + 5 * v 30 + 8 * v 31 + (-4) * v 32 + (-1) * v 33 + (-1) * v 34 + 2 * v 35 + (-1) * v 36 + 2 * v 37 + 2 * v 38 + 5 * v 39 + (-1) * v 40 + 2 * v 41 + 2 * v 42 + 5 * v 43 + 2 * v 44 + 5 * v 45 + 5 * v 46 + 8 * v 47 + (-1) * v 48 + 2 * v 49 + 2 * v 50 + 5 * v 51 + 2 * v 52 + 5 * v 53 + 5 * v 54 + 8 * v 55 + 2 * v 56 + 5 * v 57 + 5 * v 58 + 8 * v 59 + 5 * v 60 + 8 * v 61 + 8 * v 62 + 11 * v 63 := by
  have low (i : ℕ) : -v i ≤ 0 := by rcases bit i with h|h <;> omega
  have high (i : ℕ) : v i ≤ 1 := by rcases bit i with h|h <;> omega
  have row0 : v 1 + v 2 - v 3 ≤ 1 := join 1 2
  have row1 : v 1 + v 4 - v 5 ≤ 1 := join 1 4
  have row2 : v 1 + v 6 - v 7 ≤ 1 := join 1 6
  have row3 : v 1 + v 8 - v 9 ≤ 1 := join 1 8
  have row4 : v 1 + v 10 - v 11 ≤ 1 := join 1 10
  have row5 : v 1 + v 12 - v 13 ≤ 1 := join 1 12
  have row6 : v 1 + v 14 - v 15 ≤ 1 := join 1 14
  have row7 : v 1 + v 16 - v 17 ≤ 1 := join 1 16
  have row8 : v 1 + v 18 - v 19 ≤ 1 := join 1 18
  have row9 : v 1 + v 20 - v 21 ≤ 1 := join 1 20
  have row11 : v 1 + v 24 - v 25 ≤ 1 := join 1 24
  have row15 : v 1 + v 32 - v 33 ≤ 1 := join 1 32
  have row16 : v 1 + v 34 - v 35 ≤ 1 := join 1 34
  have row17 : v 1 + v 36 - v 37 ≤ 1 := join 1 36
  have row19 : v 1 + v 40 - v 41 ≤ 1 := join 1 40
  have row23 : v 1 + v 48 - v 49 ≤ 1 := join 1 48
  have row27 : v 1 + v 56 - v 57 ≤ 1 := join 1 56
  have row38 : v 2 + v 17 - v 19 ≤ 1 := join 2 17
  have row46 : v 2 + v 33 - v 35 ≤ 1 := join 2 33
  have row47 : v 2 + v 36 - v 38 ≤ 1 := join 2 36
  have row49 : v 2 + v 40 - v 42 ≤ 1 := join 2 40
  have row61 : v 3 + v 4 - v 7 ≤ 1 := join 3 4
  have row62 : v 3 + v 5 - v 7 ≤ 1 := join 3 5
  have row64 : v 3 + v 8 - v 11 ≤ 1 := join 3 8
  have row70 : v 3 + v 16 - v 19 ≤ 1 := join 3 16
  have row71 : v 3 + v 17 - v 19 ≤ 1 := join 3 17
  have row73 : v 3 + v 20 - v 23 ≤ 1 := join 3 20
  have row83 : v 3 + v 33 - v 35 ≤ 1 := join 3 33
  have row111 : v 4 + v 17 - v 21 ≤ 1 := join 4 17
  have row112 : v 4 + v 18 - v 22 ≤ 1 := join 4 18
  have row114 : v 4 + v 24 - v 28 ≤ 1 := join 4 24
  have row120 : v 4 + v 34 - v 38 ≤ 1 := join 4 34
  have row126 : v 4 + v 48 - v 52 ≤ 1 := join 4 48
  have row135 : v 5 + v 8 - v 13 ≤ 1 := join 5 8
  have row136 : v 5 + v 9 - v 13 ≤ 1 := join 5 9
  have row142 : v 5 + v 17 - v 21 ≤ 1 := join 5 17
  have row153 : v 5 + v 32 - v 37 ≤ 1 := join 5 32
  have row154 : v 5 + v 33 - v 37 ≤ 1 := join 5 33
  have row183 : v 6 + v 16 - v 22 ≤ 1 := join 6 16
  have row272 : v 8 + v 20 - v 28 ≤ 1 := join 8 20
  have row276 : v 8 + v 32 - v 40 ≤ 1 := join 8 32
  have row277 : v 8 + v 33 - v 41 ≤ 1 := join 8 33
  have row280 : v 8 + v 36 - v 44 ≤ 1 := join 8 36
  have row295 : v 9 + v 16 - v 25 ≤ 1 := join 9 16
  have row296 : v 9 + v 17 - v 25 ≤ 1 := join 9 17
  have row307 : v 9 + v 32 - v 41 ≤ 1 := join 9 32
  have row310 : v 9 + v 35 - v 43 ≤ 1 := join 9 35
  have row333 : v 10 + v 16 - v 26 ≤ 1 := join 10 16
  have row414 : v 12 + v 16 - v 28 ≤ 1 := join 12 16
  have row588 : v 16 + v 40 - v 56 ≤ 1 := join 16 40
  have row604 : v 17 + v 33 - v 49 ≤ 1 := join 17 33
  have row629 : v 18 + v 24 - v 26 ≤ 1 := join 18 24
  have row698 : v 20 + v 32 - v 52 ≤ 1 := join 20 32
  have row699 : v 20 + v 33 - v 53 ≤ 1 := join 20 33
  have row1087 : v 34 + v 48 - v 50 ≤ 1 := join 34 48
  have row1351 : v 0 - v 31 ≤ 0 := sub_nonpos.mpr (first 0)
  have row1352 : v 0 - v 47 ≤ 0 := sub_nonpos.mpr (second 0)
  have row1353 : v 1 - v 31 ≤ 0 := sub_nonpos.mpr (first 1)
  have row1354 : v 1 - v 47 ≤ 0 := sub_nonpos.mpr (second 1)
  have row1355 : v 2 - v 31 ≤ 0 := sub_nonpos.mpr (first 2)
  have row1360 : v 4 - v 47 ≤ 0 := sub_nonpos.mpr (second 4)
  have row1367 : v 8 - v 31 ≤ 0 := sub_nonpos.mpr (first 8)
  have row1368 : v 8 - v 47 ≤ 0 := sub_nonpos.mpr (second 8)
  have row1376 : v 12 - v 47 ≤ 0 := sub_nonpos.mpr (second 12)
  have row1383 : v 16 - v 31 ≤ 0 := sub_nonpos.mpr (first 16)
  have row1415 : v 32 - v 47 ≤ 0 := sub_nonpos.mpr (second 32)
  have row1417 : v 33 - v 47 ≤ 0 := sub_nonpos.mpr (second 33)
  have row1475 : -(v 63) ≤ -1 := neg_le_neg (fixed 63 (by decide)).ge
  by_contra! fail
  have bad : (-7) * v 0 + (-4) * v 1 + (-4) * v 2 + (-1) * v 3 + (-4) * v 4 + (-1) * v 5 + (-1) * v 6 + 2 * v 7 + (-4) * v 8 + (-1) * v 9 + (-1) * v 10 + 2 * v 11 + (-1) * v 12 + 2 * v 13 + 2 * v 14 + 5 * v 15 + (-4) * v 16 + (-1) * v 17 + (-1) * v 18 + 2 * v 19 + (-1) * v 20 + 2 * v 21 + 2 * v 22 + 5 * v 23 + (-1) * v 24 + 2 * v 25 + 2 * v 26 + 5 * v 27 + 2 * v 28 + 5 * v 29 + 5 * v 30 + 8 * v 31 + (-4) * v 32 + (-1) * v 33 + (-1) * v 34 + 2 * v 35 + (-1) * v 36 + 2 * v 37 + 2 * v 38 + 5 * v 39 + (-1) * v 40 + 2 * v 41 + 2 * v 42 + 5 * v 43 + 2 * v 44 + 5 * v 45 + 5 * v 46 + 8 * v 47 + (-1) * v 48 + 2 * v 49 + 2 * v 50 + 5 * v 51 + 2 * v 52 + 5 * v 53 + 5 * v 54 + 8 * v 55 + 2 * v 56 + 5 * v 57 + 5 * v 58 + 8 * v 59 + 5 * v 60 + 8 * v 61 + 8 * v 62 + 11 * v 63 ≤ (-1 : ℤ) := by omega
  rcases bit 0 with h0 | h0
  · have falseBound : (0 : ℤ) ≤ (-1 : ℤ) := by
      linear_combination 2 * bad + 2 * row2 + row5 + 2 * row9 + 2 * row19 + 2 * row47 + 2 * row61 + 2 * row111 + 2 * row153 + 2 * row295 + 2 * row333 + 2 * row629 + 2 * row1087 + row1354 + 6 * row1355 + 4 * row1360 + 6 * row1367 + 2 * row1368 + row1376 + 4 * row1383 + 6 * row1415 + 2 * row1417 + 22 * row1475 + 19986 * (low 0) + 4 * (low 11) + 3 * (low 13) + 4 * (low 14) + 10 * (low 15) + 4 * (low 19) + 4 * (low 22) + 10 * (low 23) + 2 * (low 25) + 10 * (low 27) + 4 * (low 28) + 10 * (low 29) + 10 * (low 30) + 4 * (low 35) + 2 * (low 37) + 2 * (low 38) + 10 * (low 39) + 2 * (low 41) + 4 * (low 42) + 10 * (low 43) + 4 * (low 44) + 10 * (low 45) + 10 * (low 46) + 4 * (low 49) + 2 * (low 50) + 10 * (low 51) + 4 * (low 52) + 10 * (low 53) + 10 * (low 54) + 16 * (low 55) + 4 * (low 56) + 10 * (low 57) + 10 * (low 58) + 16 * (low 59) + 10 * (low 60) + 16 * (low 61) + 16 * (low 62) + 20000 * h0
    omega
  · rcases bit 1 with h1 | h1
    · have falseBound : (0 : ℤ) ≤ (-8 : ℤ) := by
        linear_combination 3 * bad + 3 * row38 + 3 * row46 + 6 * row49 + 2 * row64 + row70 + 3 * row112 + 3 * row114 + 3 * row120 + 3 * row126 + 2 * row135 + row153 + 3 * row183 + 5 * row276 + 3 * row280 + 3 * row307 + 3 * row333 + 3 * row414 + 2 * row588 + 3 * row698 + 24 * row1351 + 24 * row1352 + 33 * row1475 + 29973 * (high 0) + 29988 * (low 1) + 6 * (low 7) + 4 * (low 11) + 4 * (low 13) + 6 * (low 14) + 15 * (low 15) + 2 * (low 19) + 6 * (low 21) + 15 * (low 23) + 6 * (low 25) + 3 * (low 26) + 15 * (low 27) + 15 * (low 29) + 15 * (low 30) + 3 * (low 35) + 5 * (low 37) + 3 * (low 38) + 15 * (low 39) + 3 * (low 41) + 15 * (low 43) + 3 * (low 44) + 15 * (low 45) + 15 * (low 46) + 6 * (low 49) + 6 * (low 50) + 15 * (low 51) + 15 * (low 53) + 15 * (low 54) + 24 * (low 55) + 4 * (low 56) + 15 * (low 57) + 15 * (low 58) + 24 * (low 59) + 15 * (low 60) + 24 * (low 61) + 24 * (low 62) - 30000 * h0 + 30000 * h1
      omega
    · have falseBound : (0 : ℤ) ≤ (-11 : ℤ) := by
        linear_combination 3 * bad + 12 * row0 + 12 * row1 + 3 * row2 + 5 * row3 + 3 * row4 + 3 * row5 + 15 * row6 + 12 * row7 + 3 * row8 + 3 * row11 + 12 * row15 + 3 * row16 + 3 * row17 + 3 * row19 + 3 * row23 + 15 * row27 + 3 * row62 + 3 * row64 + 3 * row71 + row73 + 5 * row83 + 3 * row136 + 6 * row142 + 3 * row154 + row272 + 3 * row277 + 3 * row296 + 2 * row310 + 3 * row604 + row699 + 24 * row1353 + 24 * row1354 + 33 * row1475 + 30021 * (high 0) + 29854 * (high 1) + 21 * (low 14) + 6 * (low 22) + 14 * (low 23) + 6 * (low 26) + 15 * (low 27) + 5 * (low 28) + 15 * (low 29) + 15 * (low 30) + 6 * (low 38) + 15 * (low 39) + 6 * (low 42) + 13 * (low 43) + 6 * (low 44) + 15 * (low 45) + 15 * (low 46) + 6 * (low 50) + 15 * (low 51) + 6 * (low 52) + 14 * (low 53) + 15 * (low 54) + 24 * (low 55) + 21 * (low 56) + 15 * (low 58) + 24 * (low 59) + 15 * (low 60) + 24 * (low 61) + 24 * (low 62) - 30000 * h0 - 30000 * h1
      omega

lemma layer6_6 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (first : ∀ i, v i ≤ v (i ||| 31))
    (second : ∀ i, v i ≤ v (i ||| 47))
    (fixed : ∀ i ∈ ([63] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-6) * v 0 + (-3) * v 1 + (-3) * v 2 + (-3) * v 4 + 3 * v 7 + (-3) * v 8 + 3 * v 11 + 3 * v 13 + 3 * v 14 + 6 * v 15 + (-3) * v 16 + 3 * v 19 + 3 * v 21 + 3 * v 22 + 6 * v 23 + 3 * v 25 + 3 * v 26 + 6 * v 27 + 3 * v 28 + 6 * v 29 + 6 * v 30 + 9 * v 31 + (-3) * v 32 + 3 * v 35 + 3 * v 37 + 3 * v 38 + 6 * v 39 + 3 * v 41 + 3 * v 42 + 6 * v 43 + 3 * v 44 + 6 * v 45 + 6 * v 46 + 9 * v 47 + 3 * v 49 + 3 * v 50 + 6 * v 51 + 3 * v 52 + 6 * v 53 + 6 * v 54 + 9 * v 55 + 3 * v 56 + 6 * v 57 + 6 * v 58 + 9 * v 59 + 6 * v 60 + 9 * v 61 + 9 * v 62 + 12 * v 63 := by
  have low (i : ℕ) : -v i ≤ 0 := by rcases bit i with h|h <;> omega
  have high (i : ℕ) : v i ≤ 1 := by rcases bit i with h|h <;> omega
  have row41 : v 2 + v 24 - v 26 ≤ 1 := join 2 24
  have row268 : v 8 + v 16 - v 24 ≤ 1 := join 8 16
  have row1351 : v 0 - v 31 ≤ 0 := sub_nonpos.mpr (first 0)
  have row1352 : v 0 - v 47 ≤ 0 := sub_nonpos.mpr (second 0)
  have row1354 : v 1 - v 47 ≤ 0 := sub_nonpos.mpr (second 1)
  have row1355 : v 2 - v 31 ≤ 0 := sub_nonpos.mpr (first 2)
  have row1359 : v 4 - v 31 ≤ 0 := sub_nonpos.mpr (first 4)
  have row1367 : v 8 - v 31 ≤ 0 := sub_nonpos.mpr (first 8)
  have row1383 : v 16 - v 31 ≤ 0 := sub_nonpos.mpr (first 16)
  have row1415 : v 32 - v 47 ≤ 0 := sub_nonpos.mpr (second 32)
  have row1475 : -(v 63) ≤ -1 := neg_le_neg (fixed 63 (by decide)).ge
  by_contra! fail
  have bad : (-6) * v 0 + (-3) * v 1 + (-3) * v 2 + (-3) * v 4 + 3 * v 7 + (-3) * v 8 + 3 * v 11 + 3 * v 13 + 3 * v 14 + 6 * v 15 + (-3) * v 16 + 3 * v 19 + 3 * v 21 + 3 * v 22 + 6 * v 23 + 3 * v 25 + 3 * v 26 + 6 * v 27 + 3 * v 28 + 6 * v 29 + 6 * v 30 + 9 * v 31 + (-3) * v 32 + 3 * v 35 + 3 * v 37 + 3 * v 38 + 6 * v 39 + 3 * v 41 + 3 * v 42 + 6 * v 43 + 3 * v 44 + 6 * v 45 + 6 * v 46 + 9 * v 47 + 3 * v 49 + 3 * v 50 + 6 * v 51 + 3 * v 52 + 6 * v 53 + 6 * v 54 + 9 * v 55 + 3 * v 56 + 6 * v 57 + 6 * v 58 + 9 * v 59 + 6 * v 60 + 9 * v 61 + 9 * v 62 + 12 * v 63 ≤ (-1 : ℤ) := by omega
  have falseBound : (0 : ℤ) ≤ (-9 : ℤ) := by
    linear_combination bad + 2 * row41 + 2 * row268 + 3 * row1351 + 3 * row1352 + 3 * row1354 + row1355 + 3 * row1359 + row1367 + row1383 + 3 * row1415 + 12 * row1475 + 3 * (low 7) + 3 * (low 11) + 3 * (low 13) + 3 * (low 14) + 6 * (low 15) + 3 * (low 19) + 3 * (low 21) + 3 * (low 22) + 6 * (low 23) + 3 * (low 25) + (low 26) + 6 * (low 27) + 3 * (low 28) + 6 * (low 29) + 6 * (low 30) + 3 * (low 35) + 3 * (low 37) + 3 * (low 38) + 6 * (low 39) + 3 * (low 41) + 3 * (low 42) + 6 * (low 43) + 3 * (low 44) + 6 * (low 45) + 6 * (low 46) + 3 * (low 49) + 3 * (low 50) + 6 * (low 51) + 3 * (low 52) + 6 * (low 53) + 6 * (low 54) + 9 * (low 55) + 3 * (low 56) + 6 * (low 57) + 6 * (low 58) + 9 * (low 59) + 6 * (low 60) + 9 * (low 61) + 9 * (low 62)
  omega

open Finset UnionClosed

lemma indexed_sum {α : Type} [Fintype α] [DecidableEq α] (D : Finset α) (I : List ℕ)
    (d : ℕ → α) (s : α → ℤ) (all : (I.map d).toFinset=univ) (nd : (I.map d).Nodup) :
    ∑ u ∈ D, s u = (I.map (fun i => s (d i) * (if d i ∈ D then (1:ℤ) else 0))).sum := by
  have h : (univ.filter (· ∈ D) : Finset α) = D := by ext; simp
  calc
    _ = ∑ u : α, if u∈D then s u else 0 := by rw [← sum_filter,h]
    _ = ((I.map d).map (fun u => if u∈D then s u else 0)).sum := by
      rw [← List.sum_toFinset _ nd, all]
    _ = _ := by simp [List.map_map,Function.comp_def,mul_ite]

lemma indicator_join {α : Type} [DecidableEq α] (D : Finset (Finset α))
    (closed : IsUnionClosed D) (d : ℕ → Finset α) (du : ∀ i j, d (i|||j)=d i∪d j) (i j : ℕ) :
    (if d i∈D then (1:ℤ) else 0) + (if d j∈D then 1 else 0) - (if d (i|||j)∈D then 1 else 0) ≤ 1 := by
  rw [du]
  by_cases a : d i∈D <;> by_cases b : d j∈D
  · simp [a,b,closed _ a _ b]
  all_goals split_ifs <;> omega

lemma indicator_force {α : Type} [DecidableEq α] (D : Finset (Finset α)) (d : ℕ → Finset α)
    (du : ∀ i j, d (i|||j)=d i∪d j) {t : ℕ} (h : ∀ U∈D, U∪d t∈D) (i : ℕ) :
    (if d i∈D then (1:ℤ) else 0) ≤ (if d (i|||t)∈D then 1 else 0) := by
  rw [du]
  by_cases hi : d i∈D
  · simp [hi,h _ hi]
  · simp [hi]; split <;> decide

lemma decode_union (b i j : ℕ) :
    (univ.filter (fun a : Fin b => (i|||j).testBit a.val)) =
    (univ.filter (fun a : Fin b => i.testBit a.val)) ∪
    (univ.filter (fun a : Fin b => j.testBit a.val)) := by ext; simp [Nat.testBit_lor]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
lemma fiber5 (k : ℕ) (hk : k ≤ 7) (D : Finset (Finset (Fin 5)))
    (closed : IsUnionClosed D) (full : univ∈D) (zero : k=0 → ∅∈D)
    (minSize : ∀ U∈D, k+U.card=0 ∨ 5≤k+U.card)
    (avoid : k=1 → ∀ U∈D, U.card≠4)
    (apart : ∀ U∈D, ∀ V∈D, U≠V → k+U.card=5 → k+V.card=5 → k+(U∩V).card≠4) :
    (if k=0 then -14 else if k=7 then 14 else 0 : ℤ) ≤ ∑ U ∈ D, (4*(U.card:ℤ)+2*k-17) := by
  let d (i : ℕ) : Finset (Fin 5) := univ.filter (fun a => i.testBit a.val)
  let v (i : ℕ) : ℤ := if d i∈D then 1 else 0
  have du := decode_union 5
  have ht : d 31 = univ := by decide +kernel
  have hz : d 0 = ∅ := by decide +kernel
  have bit (i) : v i=0 ∨ v i=1 := by dsimp [v]; split <;> simp
  have join := indicator_join D closed d du
  have fixedS (U : Finset (Fin 5)) (_ : U ∈ D) : U∪d 31∈D := by rw [ht,union_eq_right.mpr (subset_univ _)]; exact full
  have fS := indicator_force D d du fixedS
  have stable : ∀ i, d i=univ ∨ (k=0 ∧ d i=∅) → v i=1 := by
    intro i h
    have hD : d i∈D := by
      rcases h with hi|⟨hk,hi⟩
      · exact hi ▸ full
      · exact hi ▸ zero hk
    simp [v,hD]
  have exclude (i : ℕ) (bad : (0<k+(d i).card ∧ k+(d i).card<5) ∨ (k=1 ∧ (d i).card=4)) : v i=0 := by
    have hn : d i∉D := by
      intro h
      have size := minSize _ h
      rcases bad with a|⟨one,e⟩
      · omega
      · exact avoid one _ h e
    simp [v,hn]
  have separate (i j : ℕ) (h : d i≠d j ∧ k+(d i).card=5 ∧ k+(d j).card=5 ∧ k+((d i)∩(d j)).card=4) : v i + v j ≤ 1 := by
    by_cases h1 : d i∈D <;> by_cases h2 : d j∈D
    · exact (apart _ h1 _ h2 h.1 h.2.1 h.2.2.1 h.2.2.2).elim
    all_goals simp [v,h1,h2]
  have all : ((List.range 32).map d).toFinset=univ := by decide +kernel
  have nd : ((List.range 32).map d).Nodup := by decide +kernel
  rw [indexed_sum D _ d _ all nd]
  change _ ≤ ((List.range 32).map (fun i => (4*((d i).card:ℤ)+2*(k:ℤ)-17)*v i)).sum
  interval_cases k
  · have hsm : ∀ i ∈ ([1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30] : List ℕ), (0<0+(d i).card ∧ 0+(d i).card<5) ∨ (0=1 ∧ (d i).card=4) := by decide +kernel
    have hfx : ∀ i ∈ ([0,31] : List ℕ), d i=univ ∨ (0=0 ∧ d i=∅) := by decide +kernel
    have cert := layer5_0 v bit join fS (fun i hi => exclude i (hsm i hi)) (fun i hi => stable i (hfx i hi))
    change (-14 : ℤ) ≤ ((-17 : ℤ)*v 0 + ((-13 : ℤ)*v 1 + ((-13 : ℤ)*v 2 + ((-9 : ℤ)*v 3 + ((-13 : ℤ)*v 4 + ((-9 : ℤ)*v 5 + ((-9 : ℤ)*v 6 + ((-5 : ℤ)*v 7 + ((-13 : ℤ)*v 8 + ((-9 : ℤ)*v 9 + ((-9 : ℤ)*v 10 + ((-5 : ℤ)*v 11 + ((-9 : ℤ)*v 12 + ((-5 : ℤ)*v 13 + ((-5 : ℤ)*v 14 + ((-1 : ℤ)*v 15 + ((-13 : ℤ)*v 16 + ((-9 : ℤ)*v 17 + ((-9 : ℤ)*v 18 + ((-5 : ℤ)*v 19 + ((-9 : ℤ)*v 20 + ((-5 : ℤ)*v 21 + ((-5 : ℤ)*v 22 + ((-1 : ℤ)*v 23 + ((-9 : ℤ)*v 24 + ((-5 : ℤ)*v 25 + ((-5 : ℤ)*v 26 + ((-1 : ℤ)*v 27 + ((-5 : ℤ)*v 28 + ((-1 : ℤ)*v 29 + ((-1 : ℤ)*v 30 + ((3 : ℤ)*v 31 + 0))))))))))))))))))))))))))))))))
    linarith only [cert]
  · have hsm : ∀ i ∈ ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30] : List ℕ), (0<1+(d i).card ∧ 1+(d i).card<5) ∨ (1=1 ∧ (d i).card=4) := by decide +kernel
    have hab : ∀ u ∈ ([(15,23),(15,27),(15,29),(15,30),(23,27),(23,29),(23,30),(27,29),(27,30),(29,30)] : List (ℕ × ℕ)), d u.1 ≠ d u.2 ∧ 1+(d u.1).card=5 ∧ 1+(d u.2).card=5 ∧ 1+((d u.1)∩(d u.2)).card=4 := by decide +kernel
    have hfx : ∀ i ∈ ([31] : List ℕ), d i=univ ∨ (1=0 ∧ d i=∅) := by decide +kernel
    have cert := layer5_1 v bit join fS (fun i hi => exclude i (hsm i hi)) (fun i j hij => separate i j (hab (i,j) hij)) (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-15 : ℤ)*v 0 + ((-11 : ℤ)*v 1 + ((-11 : ℤ)*v 2 + ((-7 : ℤ)*v 3 + ((-11 : ℤ)*v 4 + ((-7 : ℤ)*v 5 + ((-7 : ℤ)*v 6 + ((-3 : ℤ)*v 7 + ((-11 : ℤ)*v 8 + ((-7 : ℤ)*v 9 + ((-7 : ℤ)*v 10 + ((-3 : ℤ)*v 11 + ((-7 : ℤ)*v 12 + ((-3 : ℤ)*v 13 + ((-3 : ℤ)*v 14 + ((1 : ℤ)*v 15 + ((-11 : ℤ)*v 16 + ((-7 : ℤ)*v 17 + ((-7 : ℤ)*v 18 + ((-3 : ℤ)*v 19 + ((-7 : ℤ)*v 20 + ((-3 : ℤ)*v 21 + ((-3 : ℤ)*v 22 + ((1 : ℤ)*v 23 + ((-7 : ℤ)*v 24 + ((-3 : ℤ)*v 25 + ((-3 : ℤ)*v 26 + ((1 : ℤ)*v 27 + ((-3 : ℤ)*v 28 + ((1 : ℤ)*v 29 + ((1 : ℤ)*v 30 + ((5 : ℤ)*v 31 + 0))))))))))))))))))))))))))))))))
    linarith only [cert]
  · have hsm : ∀ i ∈ ([0,1,2,3,4,5,6,8,9,10,12,16,17,18,20,24] : List ℕ), (0<2+(d i).card ∧ 2+(d i).card<5) ∨ (2=1 ∧ (d i).card=4) := by decide +kernel
    have hab : ∀ u ∈ ([(7,11),(7,13),(7,14),(7,19),(7,21),(7,22),(11,13),(11,14),(11,19),(11,25),(11,26),(13,14),(13,21),(13,25),(13,28),(14,22),(14,26),(14,28),(19,21),(19,22),(19,25),(19,26),(21,22),(21,25),(21,28),(22,26),(22,28),(25,26),(25,28),(26,28)] : List (ℕ × ℕ)), d u.1 ≠ d u.2 ∧ 2+(d u.1).card=5 ∧ 2+(d u.2).card=5 ∧ 2+((d u.1)∩(d u.2)).card=4 := by decide +kernel
    have hfx : ∀ i ∈ ([31] : List ℕ), d i=univ ∨ (2=0 ∧ d i=∅) := by decide +kernel
    have cert := layer5_2 v bit join fS (fun i hi => exclude i (hsm i hi)) (fun i j hij => separate i j (hab (i,j) hij)) (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-13 : ℤ)*v 0 + ((-9 : ℤ)*v 1 + ((-9 : ℤ)*v 2 + ((-5 : ℤ)*v 3 + ((-9 : ℤ)*v 4 + ((-5 : ℤ)*v 5 + ((-5 : ℤ)*v 6 + ((-1 : ℤ)*v 7 + ((-9 : ℤ)*v 8 + ((-5 : ℤ)*v 9 + ((-5 : ℤ)*v 10 + ((-1 : ℤ)*v 11 + ((-5 : ℤ)*v 12 + ((-1 : ℤ)*v 13 + ((-1 : ℤ)*v 14 + ((3 : ℤ)*v 15 + ((-9 : ℤ)*v 16 + ((-5 : ℤ)*v 17 + ((-5 : ℤ)*v 18 + ((-1 : ℤ)*v 19 + ((-5 : ℤ)*v 20 + ((-1 : ℤ)*v 21 + ((-1 : ℤ)*v 22 + ((3 : ℤ)*v 23 + ((-5 : ℤ)*v 24 + ((-1 : ℤ)*v 25 + ((-1 : ℤ)*v 26 + ((3 : ℤ)*v 27 + ((-1 : ℤ)*v 28 + ((3 : ℤ)*v 29 + ((3 : ℤ)*v 30 + ((7 : ℤ)*v 31 + 0))))))))))))))))))))))))))))))))
    linarith only [cert]
  · have hsm : ∀ i ∈ ([0,1,2,4,8,16] : List ℕ), (0<3+(d i).card ∧ 3+(d i).card<5) ∨ (3=1 ∧ (d i).card=4) := by decide +kernel
    have hab : ∀ u ∈ ([(3,5),(3,6),(3,9),(3,10),(3,17),(3,18),(5,6),(5,9),(5,12),(5,17),(5,20),(6,10),(6,12),(6,18),(6,20),(9,10),(9,12),(9,17),(9,24),(10,12),(10,18),(10,24),(12,20),(12,24),(17,18),(17,20),(17,24),(18,20),(18,24),(20,24)] : List (ℕ × ℕ)), d u.1 ≠ d u.2 ∧ 3+(d u.1).card=5 ∧ 3+(d u.2).card=5 ∧ 3+((d u.1)∩(d u.2)).card=4 := by decide +kernel
    have hfx : ∀ i ∈ ([31] : List ℕ), d i=univ ∨ (3=0 ∧ d i=∅) := by decide +kernel
    have cert := layer5_3 v bit join fS (fun i hi => exclude i (hsm i hi)) (fun i j hij => separate i j (hab (i,j) hij)) (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-11 : ℤ)*v 0 + ((-7 : ℤ)*v 1 + ((-7 : ℤ)*v 2 + ((-3 : ℤ)*v 3 + ((-7 : ℤ)*v 4 + ((-3 : ℤ)*v 5 + ((-3 : ℤ)*v 6 + ((1 : ℤ)*v 7 + ((-7 : ℤ)*v 8 + ((-3 : ℤ)*v 9 + ((-3 : ℤ)*v 10 + ((1 : ℤ)*v 11 + ((-3 : ℤ)*v 12 + ((1 : ℤ)*v 13 + ((1 : ℤ)*v 14 + ((5 : ℤ)*v 15 + ((-7 : ℤ)*v 16 + ((-3 : ℤ)*v 17 + ((-3 : ℤ)*v 18 + ((1 : ℤ)*v 19 + ((-3 : ℤ)*v 20 + ((1 : ℤ)*v 21 + ((1 : ℤ)*v 22 + ((5 : ℤ)*v 23 + ((-3 : ℤ)*v 24 + ((1 : ℤ)*v 25 + ((1 : ℤ)*v 26 + ((5 : ℤ)*v 27 + ((1 : ℤ)*v 28 + ((5 : ℤ)*v 29 + ((5 : ℤ)*v 30 + ((9 : ℤ)*v 31 + 0))))))))))))))))))))))))))))))))
    linarith only [cert]
  · have hsm : ∀ i ∈ ([0] : List ℕ), (0<4+(d i).card ∧ 4+(d i).card<5) ∨ (4=1 ∧ (d i).card=4) := by decide +kernel
    have hab : ∀ u ∈ ([(1,2),(1,4),(1,8),(1,16),(2,4),(2,8),(2,16),(4,8),(4,16),(8,16)] : List (ℕ × ℕ)), d u.1 ≠ d u.2 ∧ 4+(d u.1).card=5 ∧ 4+(d u.2).card=5 ∧ 4+((d u.1)∩(d u.2)).card=4 := by decide +kernel
    have hfx : ∀ i ∈ ([31] : List ℕ), d i=univ ∨ (4=0 ∧ d i=∅) := by decide +kernel
    have cert := layer5_4 v bit join fS (fun i hi => exclude i (hsm i hi)) (fun i j hij => separate i j (hab (i,j) hij)) (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-9 : ℤ)*v 0 + ((-5 : ℤ)*v 1 + ((-5 : ℤ)*v 2 + ((-1 : ℤ)*v 3 + ((-5 : ℤ)*v 4 + ((-1 : ℤ)*v 5 + ((-1 : ℤ)*v 6 + ((3 : ℤ)*v 7 + ((-5 : ℤ)*v 8 + ((-1 : ℤ)*v 9 + ((-1 : ℤ)*v 10 + ((3 : ℤ)*v 11 + ((-1 : ℤ)*v 12 + ((3 : ℤ)*v 13 + ((3 : ℤ)*v 14 + ((7 : ℤ)*v 15 + ((-5 : ℤ)*v 16 + ((-1 : ℤ)*v 17 + ((-1 : ℤ)*v 18 + ((3 : ℤ)*v 19 + ((-1 : ℤ)*v 20 + ((3 : ℤ)*v 21 + ((3 : ℤ)*v 22 + ((7 : ℤ)*v 23 + ((-1 : ℤ)*v 24 + ((3 : ℤ)*v 25 + ((3 : ℤ)*v 26 + ((7 : ℤ)*v 27 + ((3 : ℤ)*v 28 + ((7 : ℤ)*v 29 + ((7 : ℤ)*v 30 + ((11 : ℤ)*v 31 + 0))))))))))))))))))))))))))))))))
    linarith only [cert]
  · have hfx : ∀ i ∈ ([31] : List ℕ), d i=univ ∨ (5=0 ∧ d i=∅) := by decide +kernel
    have cert := layer5_5 v bit join fS (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-7 : ℤ)*v 0 + ((-3 : ℤ)*v 1 + ((-3 : ℤ)*v 2 + ((1 : ℤ)*v 3 + ((-3 : ℤ)*v 4 + ((1 : ℤ)*v 5 + ((1 : ℤ)*v 6 + ((5 : ℤ)*v 7 + ((-3 : ℤ)*v 8 + ((1 : ℤ)*v 9 + ((1 : ℤ)*v 10 + ((5 : ℤ)*v 11 + ((1 : ℤ)*v 12 + ((5 : ℤ)*v 13 + ((5 : ℤ)*v 14 + ((9 : ℤ)*v 15 + ((-3 : ℤ)*v 16 + ((1 : ℤ)*v 17 + ((1 : ℤ)*v 18 + ((5 : ℤ)*v 19 + ((1 : ℤ)*v 20 + ((5 : ℤ)*v 21 + ((5 : ℤ)*v 22 + ((9 : ℤ)*v 23 + ((1 : ℤ)*v 24 + ((5 : ℤ)*v 25 + ((5 : ℤ)*v 26 + ((9 : ℤ)*v 27 + ((5 : ℤ)*v 28 + ((9 : ℤ)*v 29 + ((9 : ℤ)*v 30 + ((13 : ℤ)*v 31 + 0))))))))))))))))))))))))))))))))
    linarith only [cert]
  · have hfx : ∀ i ∈ ([31] : List ℕ), d i=univ ∨ (6=0 ∧ d i=∅) := by decide +kernel
    have cert := layer5_6 v bit join fS (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-5 : ℤ)*v 0 + ((-1 : ℤ)*v 1 + ((-1 : ℤ)*v 2 + ((3 : ℤ)*v 3 + ((-1 : ℤ)*v 4 + ((3 : ℤ)*v 5 + ((3 : ℤ)*v 6 + ((7 : ℤ)*v 7 + ((-1 : ℤ)*v 8 + ((3 : ℤ)*v 9 + ((3 : ℤ)*v 10 + ((7 : ℤ)*v 11 + ((3 : ℤ)*v 12 + ((7 : ℤ)*v 13 + ((7 : ℤ)*v 14 + ((11 : ℤ)*v 15 + ((-1 : ℤ)*v 16 + ((3 : ℤ)*v 17 + ((3 : ℤ)*v 18 + ((7 : ℤ)*v 19 + ((3 : ℤ)*v 20 + ((7 : ℤ)*v 21 + ((7 : ℤ)*v 22 + ((11 : ℤ)*v 23 + ((3 : ℤ)*v 24 + ((7 : ℤ)*v 25 + ((7 : ℤ)*v 26 + ((11 : ℤ)*v 27 + ((7 : ℤ)*v 28 + ((11 : ℤ)*v 29 + ((11 : ℤ)*v 30 + ((15 : ℤ)*v 31 + 0))))))))))))))))))))))))))))))))
    linarith only [cert]
  · have hfx : ∀ i ∈ ([31] : List ℕ), d i=univ ∨ (7=0 ∧ d i=∅) := by decide +kernel
    have cert := layer5_7 v bit join fS (fun i hi => stable i (hfx i hi))
    change (14 : ℤ) ≤ ((-3 : ℤ)*v 0 + ((1 : ℤ)*v 1 + ((1 : ℤ)*v 2 + ((5 : ℤ)*v 3 + ((1 : ℤ)*v 4 + ((5 : ℤ)*v 5 + ((5 : ℤ)*v 6 + ((9 : ℤ)*v 7 + ((1 : ℤ)*v 8 + ((5 : ℤ)*v 9 + ((5 : ℤ)*v 10 + ((9 : ℤ)*v 11 + ((5 : ℤ)*v 12 + ((9 : ℤ)*v 13 + ((9 : ℤ)*v 14 + ((13 : ℤ)*v 15 + ((1 : ℤ)*v 16 + ((5 : ℤ)*v 17 + ((5 : ℤ)*v 18 + ((9 : ℤ)*v 19 + ((5 : ℤ)*v 20 + ((9 : ℤ)*v 21 + ((9 : ℤ)*v 22 + ((13 : ℤ)*v 23 + ((5 : ℤ)*v 24 + ((9 : ℤ)*v 25 + ((9 : ℤ)*v 26 + ((13 : ℤ)*v 27 + ((9 : ℤ)*v 28 + ((13 : ℤ)*v 29 + ((13 : ℤ)*v 30 + ((17 : ℤ)*v 31 + 0))))))))))))))))))))))))))))))))
    linarith only [cert]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
lemma fiber6 (k : ℕ) (hk : k ≤ 6) (D : Finset (Finset (Fin 6)))
    (closed : IsUnionClosed D) (full : univ∈D) (zero : k=0 → ∅∈D)
    (minSize : ∀ U∈D, k+U.card=0 ∨ 5≤k+U.card)
    (fixS : ∀ U∈D, U∪((univ : Finset (Fin 6)).filter (fun a => (31 : ℕ).testBit a.val))∈D)
    (fixT : ∀ U∈D, U∪((univ : Finset (Fin 6)).filter (fun a => (47 : ℕ).testBit a.val))∈D) :
    (0:ℤ) ≤ ∑ U ∈ D, (3*(U.card:ℤ)+1*k-12) := by
  let d (i : ℕ) : Finset (Fin 6) := univ.filter (fun a => i.testBit a.val)
  let v (i : ℕ) : ℤ := if d i∈D then 1 else 0
  have du := decode_union 6
  have ht : d 63 = univ := by decide +kernel
  have hz : d 0 = ∅ := by decide +kernel
  have bit (i) : v i=0 ∨ v i=1 := by dsimp [v]; split <;> simp
  have join := indicator_join D closed d du
  have fS := indicator_force D d du fixS
  have fT := indicator_force D d du fixT
  have stable : ∀ i, d i=univ ∨ (k=0 ∧ d i=∅) ∨ (k=0 ∧ (d i=d 31 ∨ d i=d 47)) → v i=1 := by
    intro i h
    have hD : d i∈D := by
      rcases h with hi|⟨hk,hi⟩|⟨hk,hi|hi⟩
      · exact hi ▸ full
      · exact hi ▸ zero hk
      · rw [hi]; simpa using fixS ∅ (zero hk)
      · rw [hi]; simpa using fixT ∅ (zero hk)
    simp [v,hD]
  have exclude (i : ℕ) (bad : (0<k+(d i).card ∧ k+(d i).card<5)) : v i=0 := by
    have hn : d i∉D := by
      intro h
      have size := minSize _ h
      omega
    simp [v,hn]
  have all : ((List.range 64).map d).toFinset=univ := by decide +kernel
  have nd : ((List.range 64).map d).Nodup := by decide +kernel
  rw [indexed_sum D _ d _ all nd]
  change _ ≤ ((List.range 64).map (fun i => (3*((d i).card:ℤ)+1*(k:ℤ)-12)*v i)).sum
  interval_cases k
  · have hsm : ∀ i ∈ ([1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,48,49,50,51,52,53,54,56,57,58,60] : List ℕ), (0<0+(d i).card ∧ 0+(d i).card<5) := by decide +kernel
    have hfx : ∀ i ∈ ([0,31,47,63] : List ℕ), d i=univ ∨ (0=0 ∧ d i=∅) ∨ (0=0 ∧ (d i=d 31 ∨ d i=d 47)) := by decide +kernel
    have cert := layer6_0 v bit join fS fT (fun i hi => exclude i (hsm i hi)) (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-12 : ℤ)*v 0 + ((-9 : ℤ)*v 1 + ((-9 : ℤ)*v 2 + ((-6 : ℤ)*v 3 + ((-9 : ℤ)*v 4 + ((-6 : ℤ)*v 5 + ((-6 : ℤ)*v 6 + ((-3 : ℤ)*v 7 + ((-9 : ℤ)*v 8 + ((-6 : ℤ)*v 9 + ((-6 : ℤ)*v 10 + ((-3 : ℤ)*v 11 + ((-6 : ℤ)*v 12 + ((-3 : ℤ)*v 13 + ((-3 : ℤ)*v 14 + ((0 : ℤ)*v 15 + ((-9 : ℤ)*v 16 + ((-6 : ℤ)*v 17 + ((-6 : ℤ)*v 18 + ((-3 : ℤ)*v 19 + ((-6 : ℤ)*v 20 + ((-3 : ℤ)*v 21 + ((-3 : ℤ)*v 22 + ((0 : ℤ)*v 23 + ((-6 : ℤ)*v 24 + ((-3 : ℤ)*v 25 + ((-3 : ℤ)*v 26 + ((0 : ℤ)*v 27 + ((-3 : ℤ)*v 28 + ((0 : ℤ)*v 29 + ((0 : ℤ)*v 30 + ((3 : ℤ)*v 31 + ((-9 : ℤ)*v 32 + ((-6 : ℤ)*v 33 + ((-6 : ℤ)*v 34 + ((-3 : ℤ)*v 35 + ((-6 : ℤ)*v 36 + ((-3 : ℤ)*v 37 + ((-3 : ℤ)*v 38 + ((0 : ℤ)*v 39 + ((-6 : ℤ)*v 40 + ((-3 : ℤ)*v 41 + ((-3 : ℤ)*v 42 + ((0 : ℤ)*v 43 + ((-3 : ℤ)*v 44 + ((0 : ℤ)*v 45 + ((0 : ℤ)*v 46 + ((3 : ℤ)*v 47 + ((-6 : ℤ)*v 48 + ((-3 : ℤ)*v 49 + ((-3 : ℤ)*v 50 + ((0 : ℤ)*v 51 + ((-3 : ℤ)*v 52 + ((0 : ℤ)*v 53 + ((0 : ℤ)*v 54 + ((3 : ℤ)*v 55 + ((-3 : ℤ)*v 56 + ((0 : ℤ)*v 57 + ((0 : ℤ)*v 58 + ((3 : ℤ)*v 59 + ((0 : ℤ)*v 60 + ((3 : ℤ)*v 61 + ((3 : ℤ)*v 62 + ((6 : ℤ)*v 63 + 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    linarith only [cert]
  · have hsm : ∀ i ∈ ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,16,17,18,19,20,21,22,24,25,26,28,32,33,34,35,36,37,38,40,41,42,44,48,49,50,52,56] : List ℕ), (0<1+(d i).card ∧ 1+(d i).card<5) := by decide +kernel
    have hfx : ∀ i ∈ ([63] : List ℕ), d i=univ ∨ (1=0 ∧ d i=∅) ∨ (1=0 ∧ (d i=d 31 ∨ d i=d 47)) := by decide +kernel
    have cert := layer6_1 v bit join fS fT (fun i hi => exclude i (hsm i hi)) (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-11 : ℤ)*v 0 + ((-8 : ℤ)*v 1 + ((-8 : ℤ)*v 2 + ((-5 : ℤ)*v 3 + ((-8 : ℤ)*v 4 + ((-5 : ℤ)*v 5 + ((-5 : ℤ)*v 6 + ((-2 : ℤ)*v 7 + ((-8 : ℤ)*v 8 + ((-5 : ℤ)*v 9 + ((-5 : ℤ)*v 10 + ((-2 : ℤ)*v 11 + ((-5 : ℤ)*v 12 + ((-2 : ℤ)*v 13 + ((-2 : ℤ)*v 14 + ((1 : ℤ)*v 15 + ((-8 : ℤ)*v 16 + ((-5 : ℤ)*v 17 + ((-5 : ℤ)*v 18 + ((-2 : ℤ)*v 19 + ((-5 : ℤ)*v 20 + ((-2 : ℤ)*v 21 + ((-2 : ℤ)*v 22 + ((1 : ℤ)*v 23 + ((-5 : ℤ)*v 24 + ((-2 : ℤ)*v 25 + ((-2 : ℤ)*v 26 + ((1 : ℤ)*v 27 + ((-2 : ℤ)*v 28 + ((1 : ℤ)*v 29 + ((1 : ℤ)*v 30 + ((4 : ℤ)*v 31 + ((-8 : ℤ)*v 32 + ((-5 : ℤ)*v 33 + ((-5 : ℤ)*v 34 + ((-2 : ℤ)*v 35 + ((-5 : ℤ)*v 36 + ((-2 : ℤ)*v 37 + ((-2 : ℤ)*v 38 + ((1 : ℤ)*v 39 + ((-5 : ℤ)*v 40 + ((-2 : ℤ)*v 41 + ((-2 : ℤ)*v 42 + ((1 : ℤ)*v 43 + ((-2 : ℤ)*v 44 + ((1 : ℤ)*v 45 + ((1 : ℤ)*v 46 + ((4 : ℤ)*v 47 + ((-5 : ℤ)*v 48 + ((-2 : ℤ)*v 49 + ((-2 : ℤ)*v 50 + ((1 : ℤ)*v 51 + ((-2 : ℤ)*v 52 + ((1 : ℤ)*v 53 + ((1 : ℤ)*v 54 + ((4 : ℤ)*v 55 + ((-2 : ℤ)*v 56 + ((1 : ℤ)*v 57 + ((1 : ℤ)*v 58 + ((4 : ℤ)*v 59 + ((1 : ℤ)*v 60 + ((4 : ℤ)*v 61 + ((4 : ℤ)*v 62 + ((7 : ℤ)*v 63 + 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    linarith only [cert]
  · have hsm : ∀ i ∈ ([0,1,2,3,4,5,6,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48] : List ℕ), (0<2+(d i).card ∧ 2+(d i).card<5) := by decide +kernel
    have hfx : ∀ i ∈ ([63] : List ℕ), d i=univ ∨ (2=0 ∧ d i=∅) ∨ (2=0 ∧ (d i=d 31 ∨ d i=d 47)) := by decide +kernel
    have cert := layer6_2 v bit join fS fT (fun i hi => exclude i (hsm i hi)) (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-10 : ℤ)*v 0 + ((-7 : ℤ)*v 1 + ((-7 : ℤ)*v 2 + ((-4 : ℤ)*v 3 + ((-7 : ℤ)*v 4 + ((-4 : ℤ)*v 5 + ((-4 : ℤ)*v 6 + ((-1 : ℤ)*v 7 + ((-7 : ℤ)*v 8 + ((-4 : ℤ)*v 9 + ((-4 : ℤ)*v 10 + ((-1 : ℤ)*v 11 + ((-4 : ℤ)*v 12 + ((-1 : ℤ)*v 13 + ((-1 : ℤ)*v 14 + ((2 : ℤ)*v 15 + ((-7 : ℤ)*v 16 + ((-4 : ℤ)*v 17 + ((-4 : ℤ)*v 18 + ((-1 : ℤ)*v 19 + ((-4 : ℤ)*v 20 + ((-1 : ℤ)*v 21 + ((-1 : ℤ)*v 22 + ((2 : ℤ)*v 23 + ((-4 : ℤ)*v 24 + ((-1 : ℤ)*v 25 + ((-1 : ℤ)*v 26 + ((2 : ℤ)*v 27 + ((-1 : ℤ)*v 28 + ((2 : ℤ)*v 29 + ((2 : ℤ)*v 30 + ((5 : ℤ)*v 31 + ((-7 : ℤ)*v 32 + ((-4 : ℤ)*v 33 + ((-4 : ℤ)*v 34 + ((-1 : ℤ)*v 35 + ((-4 : ℤ)*v 36 + ((-1 : ℤ)*v 37 + ((-1 : ℤ)*v 38 + ((2 : ℤ)*v 39 + ((-4 : ℤ)*v 40 + ((-1 : ℤ)*v 41 + ((-1 : ℤ)*v 42 + ((2 : ℤ)*v 43 + ((-1 : ℤ)*v 44 + ((2 : ℤ)*v 45 + ((2 : ℤ)*v 46 + ((5 : ℤ)*v 47 + ((-4 : ℤ)*v 48 + ((-1 : ℤ)*v 49 + ((-1 : ℤ)*v 50 + ((2 : ℤ)*v 51 + ((-1 : ℤ)*v 52 + ((2 : ℤ)*v 53 + ((2 : ℤ)*v 54 + ((5 : ℤ)*v 55 + ((-1 : ℤ)*v 56 + ((2 : ℤ)*v 57 + ((2 : ℤ)*v 58 + ((5 : ℤ)*v 59 + ((2 : ℤ)*v 60 + ((5 : ℤ)*v 61 + ((5 : ℤ)*v 62 + ((8 : ℤ)*v 63 + 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    linarith only [cert]
  · have hsm : ∀ i ∈ ([0,1,2,4,8,16,32] : List ℕ), (0<3+(d i).card ∧ 3+(d i).card<5) := by decide +kernel
    have hfx : ∀ i ∈ ([63] : List ℕ), d i=univ ∨ (3=0 ∧ d i=∅) ∨ (3=0 ∧ (d i=d 31 ∨ d i=d 47)) := by decide +kernel
    have cert := layer6_3 v bit join fS fT (fun i hi => exclude i (hsm i hi)) (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-9 : ℤ)*v 0 + ((-6 : ℤ)*v 1 + ((-6 : ℤ)*v 2 + ((-3 : ℤ)*v 3 + ((-6 : ℤ)*v 4 + ((-3 : ℤ)*v 5 + ((-3 : ℤ)*v 6 + ((0 : ℤ)*v 7 + ((-6 : ℤ)*v 8 + ((-3 : ℤ)*v 9 + ((-3 : ℤ)*v 10 + ((0 : ℤ)*v 11 + ((-3 : ℤ)*v 12 + ((0 : ℤ)*v 13 + ((0 : ℤ)*v 14 + ((3 : ℤ)*v 15 + ((-6 : ℤ)*v 16 + ((-3 : ℤ)*v 17 + ((-3 : ℤ)*v 18 + ((0 : ℤ)*v 19 + ((-3 : ℤ)*v 20 + ((0 : ℤ)*v 21 + ((0 : ℤ)*v 22 + ((3 : ℤ)*v 23 + ((-3 : ℤ)*v 24 + ((0 : ℤ)*v 25 + ((0 : ℤ)*v 26 + ((3 : ℤ)*v 27 + ((0 : ℤ)*v 28 + ((3 : ℤ)*v 29 + ((3 : ℤ)*v 30 + ((6 : ℤ)*v 31 + ((-6 : ℤ)*v 32 + ((-3 : ℤ)*v 33 + ((-3 : ℤ)*v 34 + ((0 : ℤ)*v 35 + ((-3 : ℤ)*v 36 + ((0 : ℤ)*v 37 + ((0 : ℤ)*v 38 + ((3 : ℤ)*v 39 + ((-3 : ℤ)*v 40 + ((0 : ℤ)*v 41 + ((0 : ℤ)*v 42 + ((3 : ℤ)*v 43 + ((0 : ℤ)*v 44 + ((3 : ℤ)*v 45 + ((3 : ℤ)*v 46 + ((6 : ℤ)*v 47 + ((-3 : ℤ)*v 48 + ((0 : ℤ)*v 49 + ((0 : ℤ)*v 50 + ((3 : ℤ)*v 51 + ((0 : ℤ)*v 52 + ((3 : ℤ)*v 53 + ((3 : ℤ)*v 54 + ((6 : ℤ)*v 55 + ((0 : ℤ)*v 56 + ((3 : ℤ)*v 57 + ((3 : ℤ)*v 58 + ((6 : ℤ)*v 59 + ((3 : ℤ)*v 60 + ((6 : ℤ)*v 61 + ((6 : ℤ)*v 62 + ((9 : ℤ)*v 63 + 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    linarith only [cert]
  · have hsm : ∀ i ∈ ([0] : List ℕ), (0<4+(d i).card ∧ 4+(d i).card<5) := by decide +kernel
    have hfx : ∀ i ∈ ([63] : List ℕ), d i=univ ∨ (4=0 ∧ d i=∅) ∨ (4=0 ∧ (d i=d 31 ∨ d i=d 47)) := by decide +kernel
    have cert := layer6_4 v bit join fS fT (fun i hi => exclude i (hsm i hi)) (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-8 : ℤ)*v 0 + ((-5 : ℤ)*v 1 + ((-5 : ℤ)*v 2 + ((-2 : ℤ)*v 3 + ((-5 : ℤ)*v 4 + ((-2 : ℤ)*v 5 + ((-2 : ℤ)*v 6 + ((1 : ℤ)*v 7 + ((-5 : ℤ)*v 8 + ((-2 : ℤ)*v 9 + ((-2 : ℤ)*v 10 + ((1 : ℤ)*v 11 + ((-2 : ℤ)*v 12 + ((1 : ℤ)*v 13 + ((1 : ℤ)*v 14 + ((4 : ℤ)*v 15 + ((-5 : ℤ)*v 16 + ((-2 : ℤ)*v 17 + ((-2 : ℤ)*v 18 + ((1 : ℤ)*v 19 + ((-2 : ℤ)*v 20 + ((1 : ℤ)*v 21 + ((1 : ℤ)*v 22 + ((4 : ℤ)*v 23 + ((-2 : ℤ)*v 24 + ((1 : ℤ)*v 25 + ((1 : ℤ)*v 26 + ((4 : ℤ)*v 27 + ((1 : ℤ)*v 28 + ((4 : ℤ)*v 29 + ((4 : ℤ)*v 30 + ((7 : ℤ)*v 31 + ((-5 : ℤ)*v 32 + ((-2 : ℤ)*v 33 + ((-2 : ℤ)*v 34 + ((1 : ℤ)*v 35 + ((-2 : ℤ)*v 36 + ((1 : ℤ)*v 37 + ((1 : ℤ)*v 38 + ((4 : ℤ)*v 39 + ((-2 : ℤ)*v 40 + ((1 : ℤ)*v 41 + ((1 : ℤ)*v 42 + ((4 : ℤ)*v 43 + ((1 : ℤ)*v 44 + ((4 : ℤ)*v 45 + ((4 : ℤ)*v 46 + ((7 : ℤ)*v 47 + ((-2 : ℤ)*v 48 + ((1 : ℤ)*v 49 + ((1 : ℤ)*v 50 + ((4 : ℤ)*v 51 + ((1 : ℤ)*v 52 + ((4 : ℤ)*v 53 + ((4 : ℤ)*v 54 + ((7 : ℤ)*v 55 + ((1 : ℤ)*v 56 + ((4 : ℤ)*v 57 + ((4 : ℤ)*v 58 + ((7 : ℤ)*v 59 + ((4 : ℤ)*v 60 + ((7 : ℤ)*v 61 + ((7 : ℤ)*v 62 + ((10 : ℤ)*v 63 + 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    linarith only [cert]
  · have hfx : ∀ i ∈ ([63] : List ℕ), d i=univ ∨ (5=0 ∧ d i=∅) ∨ (5=0 ∧ (d i=d 31 ∨ d i=d 47)) := by decide +kernel
    have cert := layer6_5 v bit join fS fT (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-7 : ℤ)*v 0 + ((-4 : ℤ)*v 1 + ((-4 : ℤ)*v 2 + ((-1 : ℤ)*v 3 + ((-4 : ℤ)*v 4 + ((-1 : ℤ)*v 5 + ((-1 : ℤ)*v 6 + ((2 : ℤ)*v 7 + ((-4 : ℤ)*v 8 + ((-1 : ℤ)*v 9 + ((-1 : ℤ)*v 10 + ((2 : ℤ)*v 11 + ((-1 : ℤ)*v 12 + ((2 : ℤ)*v 13 + ((2 : ℤ)*v 14 + ((5 : ℤ)*v 15 + ((-4 : ℤ)*v 16 + ((-1 : ℤ)*v 17 + ((-1 : ℤ)*v 18 + ((2 : ℤ)*v 19 + ((-1 : ℤ)*v 20 + ((2 : ℤ)*v 21 + ((2 : ℤ)*v 22 + ((5 : ℤ)*v 23 + ((-1 : ℤ)*v 24 + ((2 : ℤ)*v 25 + ((2 : ℤ)*v 26 + ((5 : ℤ)*v 27 + ((2 : ℤ)*v 28 + ((5 : ℤ)*v 29 + ((5 : ℤ)*v 30 + ((8 : ℤ)*v 31 + ((-4 : ℤ)*v 32 + ((-1 : ℤ)*v 33 + ((-1 : ℤ)*v 34 + ((2 : ℤ)*v 35 + ((-1 : ℤ)*v 36 + ((2 : ℤ)*v 37 + ((2 : ℤ)*v 38 + ((5 : ℤ)*v 39 + ((-1 : ℤ)*v 40 + ((2 : ℤ)*v 41 + ((2 : ℤ)*v 42 + ((5 : ℤ)*v 43 + ((2 : ℤ)*v 44 + ((5 : ℤ)*v 45 + ((5 : ℤ)*v 46 + ((8 : ℤ)*v 47 + ((-1 : ℤ)*v 48 + ((2 : ℤ)*v 49 + ((2 : ℤ)*v 50 + ((5 : ℤ)*v 51 + ((2 : ℤ)*v 52 + ((5 : ℤ)*v 53 + ((5 : ℤ)*v 54 + ((8 : ℤ)*v 55 + ((2 : ℤ)*v 56 + ((5 : ℤ)*v 57 + ((5 : ℤ)*v 58 + ((8 : ℤ)*v 59 + ((5 : ℤ)*v 60 + ((8 : ℤ)*v 61 + ((8 : ℤ)*v 62 + ((11 : ℤ)*v 63 + 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    linarith only [cert]
  · have hfx : ∀ i ∈ ([63] : List ℕ), d i=univ ∨ (6=0 ∧ d i=∅) ∨ (6=0 ∧ (d i=d 31 ∨ d i=d 47)) := by decide +kernel
    have cert := layer6_6 v bit join fS fT (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-6 : ℤ)*v 0 + ((-3 : ℤ)*v 1 + ((-3 : ℤ)*v 2 + ((0 : ℤ)*v 3 + ((-3 : ℤ)*v 4 + ((0 : ℤ)*v 5 + ((0 : ℤ)*v 6 + ((3 : ℤ)*v 7 + ((-3 : ℤ)*v 8 + ((0 : ℤ)*v 9 + ((0 : ℤ)*v 10 + ((3 : ℤ)*v 11 + ((0 : ℤ)*v 12 + ((3 : ℤ)*v 13 + ((3 : ℤ)*v 14 + ((6 : ℤ)*v 15 + ((-3 : ℤ)*v 16 + ((0 : ℤ)*v 17 + ((0 : ℤ)*v 18 + ((3 : ℤ)*v 19 + ((0 : ℤ)*v 20 + ((3 : ℤ)*v 21 + ((3 : ℤ)*v 22 + ((6 : ℤ)*v 23 + ((0 : ℤ)*v 24 + ((3 : ℤ)*v 25 + ((3 : ℤ)*v 26 + ((6 : ℤ)*v 27 + ((3 : ℤ)*v 28 + ((6 : ℤ)*v 29 + ((6 : ℤ)*v 30 + ((9 : ℤ)*v 31 + ((-3 : ℤ)*v 32 + ((0 : ℤ)*v 33 + ((0 : ℤ)*v 34 + ((3 : ℤ)*v 35 + ((0 : ℤ)*v 36 + ((3 : ℤ)*v 37 + ((3 : ℤ)*v 38 + ((6 : ℤ)*v 39 + ((0 : ℤ)*v 40 + ((3 : ℤ)*v 41 + ((3 : ℤ)*v 42 + ((6 : ℤ)*v 43 + ((3 : ℤ)*v 44 + ((6 : ℤ)*v 45 + ((6 : ℤ)*v 46 + ((9 : ℤ)*v 47 + ((0 : ℤ)*v 48 + ((3 : ℤ)*v 49 + ((3 : ℤ)*v 50 + ((6 : ℤ)*v 51 + ((3 : ℤ)*v 52 + ((6 : ℤ)*v 53 + ((6 : ℤ)*v 54 + ((9 : ℤ)*v 55 + ((3 : ℤ)*v 56 + ((6 : ℤ)*v 57 + ((6 : ℤ)*v 58 + ((9 : ℤ)*v 59 + ((6 : ℤ)*v 60 + ((9 : ℤ)*v 61 + ((9 : ℤ)*v 62 + ((12 : ℤ)*v 63 + 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    linarith only [cert]

end FranklLocal

namespace FranklGlobal
open Finset UnionClosed

lemma weight_sum {V : Type} [DecidableEq V] (X B : Finset V) (a d : ℕ) :
    (∑ i ∈ X, if i ∈ B then a else d) = a*(X∩B).card + d*(X\B).card := by
  have yes : X.filter (· ∈ B) = X∩B := by ext; simp
  have no : X.filter (· ∉ B) = X\B := by ext; simp
  rw [sum_ite,yes,no]
  simp [mul_comm]

lemma reassemble {V : Type} [Fintype V] [DecidableEq V] (F : Finset (Finset V))
    (B : Finset V) (f : Finset V → ℤ) (offset : ℤ)
    (bound : ∀ K ∈ (univ\B).powerset,
       (if K=univ\B then offset else 0) - (if K=∅ then offset else 0) ≤
       ∑ X ∈ F.filter (fun X => X\B=K), f X) : 0 ≤ ∑ X ∈ F, f X := by
  have h := sum_le_sum bound
  have maps (x : Finset V) (_ : x∈F) : x\B ∈ (univ\B).powerset := by
    apply mem_powerset.mpr
    exact sdiff_subset_sdiff (subset_univ _) (Subset.rfl)
  rw [sum_fiberwise_of_maps_to maps, sum_sub_distrib] at h
  simpa using h

lemma weight_witness (F : Finset (Finset (Fin 12))) (B : Finset (Fin 12)) (a d t : ℕ)
    (pa : 0<a) (pd : 0<d) (total : a*B.card+d*(univ\B).card = 2*t)
    (nonneg : (0:ℤ) ≤ ∑ X ∈ F, (((a*(X∩B).card + d*(X\B).card : ℕ) : ℤ) - (t:ℤ))) :
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧ F.card * (∑ i, w i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, w i) := by
  let w (i : Fin 12) := if i∈B then a else d
  have sum (X : Finset (Fin 12)) : (∑ i ∈ X, w i) = a*(X∩B).card+d*(X\B).card := weight_sum X B a d
  have tot : (∑ i, w i) = 2*t := by simpa using (sum univ).trans (by simpa using total)
  refine ⟨w,Finset.sum_pos (fun i _ => by dsimp [w]; split <;> assumption) univ_nonempty,?_⟩
  rw [tot]
  simp only [← sum, sum_sub_distrib, sum_const, nsmul_eq_mul] at nonneg
  have h : F.card*t ≤ ∑ X ∈ F, ∑ i ∈ X, w i := by exact_mod_cast (sub_nonneg.mp nonneg)
  nlinarith

lemma fiber_sum {V : Type} [DecidableEq V] (F : Finset (Finset V)) (B K : Finset V)
    (f : Finset V → ℤ) :
    (∑ X ∈ F.filter (fun X => X\B=K), f (X∩B)) =
    ∑ U ∈ (F.filter (fun X => X\B=K)).image (· ∩ B), f U := by
  symm
  apply sum_image
  intro X hX Y hY eq
  have a := (mem_filter.mp hX).2
  have b := (mem_filter.mp hY).2
  ext i
  by_cases hi : i∈B
  · simpa [hi] using (Finset.ext_iff.mp eq i)
  · simpa [hi] using (Finset.ext_iff.mp (a.trans b.symm) i)

/-- Encode all sets with the same outside part as a family on the distinguished coordinates. -/
lemma slice_data {b : ℕ} (F : Finset (Finset (Fin 12))) (e : Fin b ↪ Fin 12) (K : Finset (Fin 12))
    (closed : IsUnionClosed F) (empty : ∅∈F) (fullSet : univ∈F)
    (minSize : ∀ X∈F, X.Nonempty → 5 ≤ X.card)
    (hK : K ⊆ univ \ (univ.map e)) :
    let B := univ.map e
    let X (U : Finset (Fin b)) := K ∪ U.map e
    let D := univ.filter fun U => X U ∈ F
    IsUnionClosed D ∧ (K=∅ → ∅∈D) ∧ (K=univ\B → univ∈D) ∧
    (∀ U∈D, K.card+U.card=0 ∨ 5≤K.card+U.card) ∧
    (∀ H : Finset (Fin b), H.map e∈F → ∀ U∈D, U∪H∈D) ∧
    (∀ U V : Finset (Fin b), (X U∩X V).card=K.card+(U∩V).card) ∧
    (∀ U : Finset (Fin b), (X U).card=K.card+U.card) ∧
    (∀ U : Finset (Fin b), X U∩B=U.map e) ∧ Function.Injective X ∧
    (∀ s : ℕ → ℤ, (∑ Y ∈ F.filter (fun Y => Y\B=K), s (Y∩B).card) = ∑ U ∈ D, s U.card) := by
  classical
  let B := (univ : Finset (Fin b)).map e
  let X (U : Finset (Fin b)) := K ∪ U.map e
  let D := (univ : Finset (Finset (Fin b))).filter fun U => X U ∈ F
  have mem (U) : U∈D ↔ X U∈F := by simp [D]
  have inner (U : Finset (Fin b)) : U.map e ⊆ B := map_subset_map.mpr (subset_univ _)
  have dis : Disjoint K B := by
    apply disjoint_left.mpr
    intro i hi hb; exact (mem_sdiff.mp (hK hi)).2 hb
  have ins (U) : X U∩B=U.map e := by
    ext i; simp only [X,mem_inter,mem_union]; constructor
    · rintro ⟨h|h,hb⟩
      · exact (disjoint_left.mp dis h hb).elim
      · exact h
    · exact fun h => ⟨Or.inr h,inner U h⟩
  have out (U) : X U\B=K := by
    ext i; simp only [X,mem_sdiff,mem_union]; constructor
    · rintro ⟨h|h,hb⟩
      · exact h
      · exact (hb (inner U h)).elim
    · exact fun h => ⟨Or.inl h,disjoint_left.mp dis h⟩
  have cardX (U) : (X U).card=K.card+U.card := by
    change (K ∪ U.map e).card = _
    rw [card_union_of_disjoint (dis.mono_right (inner U)),card_map]
  have inject : Function.Injective X := by
    intro U V eq
    exact Finset.map_injective e <| (ins U).symm.trans ((congrArg (· ∩ B) eq).trans (ins V))
  change IsUnionClosed D ∧ _
  refine ⟨?_,?_,?_,?_,?_,?_,cardX,ins,inject,?_⟩
  · intro U hu V hv
    apply (mem _).mpr
    have := closed (X U) ((mem U).mp hu) (X V) ((mem V).mp hv)
    simpa [X,map_union,union_assoc,union_left_comm,union_comm] using this
  · intro z; apply (mem _).mpr; simpa [X,z] using empty
  · intro z; apply (mem _).mpr
    have eq : X univ=univ := by ext i; simp [X,z]
    rwa [eq]
  · intro U hu
    by_cases h : (X U).Nonempty
    · exact Or.inr ((cardX U) ▸ minSize _ ((mem _).mp hu) h)
    · have z : X U = ∅ := not_nonempty_iff_eq_empty.mp h
      exact Or.inl (by simpa [z] using (cardX U).symm)
  · intro H hH U hu
    apply (mem _).mpr
    have := closed _ ((mem _).mp hu) _ hH
    simpa [X,map_union,union_assoc] using this
  · intro U V
    have eq : X U∩X V=X (U∩V) := by ext i; simp [X,map_inter]; tauto
    rw [eq,cardX]
  · intro score
    have eq : D.image X = F.filter (fun Y => Y\B=K) := by
      ext Y
      constructor
      · rintro hy
        obtain ⟨U,hu,rfl⟩ := mem_image.mp hy
        exact mem_filter.mpr ⟨(mem _).mp hu,out U⟩
      · intro hy
        obtain ⟨hf,base⟩ := mem_filter.mp hy
        let U := univ.filter (fun i : Fin b => e i∈Y)
        have val : X U=Y := by
          ext a
          simp only [X,mem_union]
          by_cases h : a∈B
          · obtain ⟨i,_,rfl⟩ := mem_map.mp h
            have nk : e i ∉ K := fun hm => disjoint_left.mp dis hm (inner univ (mem_map.mpr ⟨i,mem_univ _,rfl⟩))
            simp [U,nk]
          · have : a∈K ↔ a∈Y := by rw [←base]; simp [h]
            have hn : a∉U.map e := fun hu => h (inner U hu)
            simp [hn,this]
        exact mem_image.mpr ⟨U,(mem _).mpr (val ▸ hf),val⟩
    rw [←eq,sum_image (fun _ _ _ _ eq => inject eq)]
    apply sum_congr rfl
    intro U hu; rw [ins,card_map]
lemma coordinates {V : Type} [DecidableEq V] (B : Finset V) {b : ℕ} (size : B.card=b) :
    ∃ e : Fin b ↪ V, univ.map e=B := by
  classical
  let h : Fin b ≃ B := Fintype.equivOfCardEq (by simpa using size.symm)
  let e := h.toEmbedding.trans (Function.Embedding.subtype (· ∈ B))
  refine ⟨e,?_⟩
  ext v
  constructor
  · intro hv
    obtain ⟨i,_,rfl⟩ := mem_map.mp hv
    exact (h i).2
  · intro hv
    exact mem_map.mpr ⟨h.symm ⟨v,hv⟩,mem_univ _,congrArg Subtype.val (h.apply_symm_apply _)⟩

lemma snoc_range {V : Type} [DecidableEq V] {b : ℕ} (e : Fin b ↪ V) {a : V} (fresh : a∉Set.range e) :
    univ.map (Fin.Embedding.snoc e fresh) = insert a (univ.map e) := by
  ext x
  simp only [mem_map,mem_univ,true_and,mem_insert]
  constructor
  · rintro ⟨i,rfl⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Or.inl (Fin.Embedding.snoc_last)
    · exact Or.inr ⟨j,Fin.Embedding.snoc_castSucc.symm⟩
  · rintro (rfl | ⟨j,rfl⟩)
    · exact ⟨Fin.last _,Fin.Embedding.snoc_last⟩
    · exact ⟨j.castSucc,Fin.Embedding.snoc_castSucc⟩

lemma snoc_prefix {V : Type} [DecidableEq V] {b : ℕ} (e : Fin b ↪ V) {a : V} (fresh : a∉Set.range e)
    (U : Finset (Fin b)) : (U.map Fin.castSuccEmb).map (Fin.Embedding.snoc e fresh) = U.map e := by
  rw [map_map]
  congr 1
  ext j; exact Fin.Embedding.snoc_castSucc (ha:=fresh)

lemma adjacent_coordinates {V : Type} [DecidableEq V] (S T : Finset V) (s : S.card=5) (t : T.card=5)
    (c : (S∩T).card=4) :
    ∃ e : Fin 6 ↪ V, univ.map e=S∪T ∧
      ((univ : Finset (Fin 6)).filter (fun i => (31:ℕ).testBit i.val)).map e=S ∧
      ((univ : Finset (Fin 6)).filter (fun i => (47:ℕ).testBit i.val)).map e=T := by
  classical
  let C := S∩T
  obtain ⟨g,hg⟩ := coordinates C c
  have pick (U : Finset V) (cu : C⊆U) (size : U.card=5) : ∃ v, v∉C ∧ U=insert v C := by
    have count := card_sdiff_of_subset cu
    have z : (U\C).card=1 := by change C.card=4 at c; omega
    obtain ⟨v,eq⟩ := card_eq_one.mp z
    have hv : v∈U\C := eq ▸ mem_singleton_self _
    refine ⟨v,(mem_sdiff.mp hv).2,?_⟩
    ext x
    by_cases a : x∈C
    · simp [a,cu a]
    · have mem := Finset.ext_iff.mp eq x; simpa [a] using mem
  obtain ⟨a,ac,sa⟩ := pick S inter_subset_left s
  obtain ⟨b,bc,tb⟩ := pick T inter_subset_right t
  have anb : a≠b := by
    rintro rfl
    apply ac; exact mem_inter.mpr ⟨sa ▸ mem_insert_self _ _,tb ▸ mem_insert_self _ _⟩
  have ar : a ∉ Set.range g := by
    rintro ⟨i,rfl⟩; exact ac (hg ▸ mem_map.mpr ⟨i,mem_univ _,rfl⟩)
  let ga := Fin.Embedding.snoc g ar
  have gaS : univ.map ga=S := by rw [snoc_range,hg,← sa]
  have br : b ∉ Set.range ga := by
    intro h
    obtain ⟨i,eq⟩ := h
    have hS : b∈S := gaS ▸ mem_map.mpr ⟨i,mem_univ _,eq⟩
    rw [sa,mem_insert] at hS
    exact hS.elim (fun h => anb h.symm) bc
  let e := Fin.Embedding.snoc ga br
  have maskS : (univ : Finset (Fin 6)).filter (fun i => (31:ℕ).testBit i.val) = univ.map Fin.castSuccEmb := by decide +kernel
  have maskT : (univ : Finset (Fin 6)).filter (fun i => (47:ℕ).testBit i.val) =
      insert (Fin.last 5) (((univ : Finset (Fin 4)).map Fin.castSuccEmb).map Fin.castSuccEmb) := by decide +kernel
  refine ⟨e,?_,?_,?_⟩
  · rw [snoc_range,gaS,tb,sa]; ext x; simp <;> tauto
  · rw [maskS,snoc_prefix,gaS]
  · rw [maskT,map_insert,snoc_prefix,snoc_prefix,hg,tb]; rfl


lemma weight_from_fibers {b : ℕ} (F : Finset (Finset (Fin 12))) (e : Fin b ↪ Fin 12)
    (closed : IsUnionClosed F) (empty : ∅∈F) (full : univ∈F)
    (minSize : ∀ X∈F, X.Nonempty → 5 ≤ X.card)
    (a d t : ℕ) (pa : 0<a) (pd : 0<d) (balance : a*b+d*(12-b)=2*t)
    (c : ℤ) (pc : 0≤c)
    (bound : ∀ K ⊆ univ\(univ.map e),
      let D := (univ : Finset (Finset (Fin b))).filter fun U => K∪U.map e∈F
      D.Nonempty → (if K=univ\(univ.map e) then c else 0) - (if K=∅ then c else 0) ≤
        ∑ U ∈ D, ((a:ℤ)*U.card+(d:ℤ)*K.card-(t:ℤ))) :
    ∃ w : Fin 12 → ℕ, 0<∑ i, w i ∧ F.card*(∑ i,w i) ≤ 2*(∑ X∈F,∑ i∈X,w i) := by
  classical
  let B := (univ : Finset (Fin b)).map e
  have bsize : B.card=b := by simp [B]
  have osize : (univ\B).card=12-b := by rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,bsize]
  apply weight_witness F B a d t pa pd (by simpa only [bsize,osize] using balance)
  apply reassemble F B _ c
  intro K hK
  have sub := mem_powerset.mp hK
  let D := (univ : Finset (Finset (Fin b))).filter fun U => K ∪ U.map e ∈ F
  obtain ⟨_,_,top,_,_,_,_,_,_,sums⟩ := slice_data F e K closed empty full minSize sub
  have eq : (∑ X∈F.filter (fun X => X\B=K), (((a*(X∩B).card+d*(X\B).card:ℕ):ℤ)-(t:ℤ))) =
    ∑ U∈D, ((a:ℤ)*U.card+(d:ℤ)*K.card-(t:ℤ)) := by
    calc
      _ = ∑ X∈F.filter (fun X => X\B=K), ((a:ℤ)*(X∩B).card+(d:ℤ)*K.card-(t:ℤ)) := by
        apply sum_congr rfl
        intro X hx
        have z := (mem_filter.mp hx).2
        push_cast; rw [z]
      _ = _ := sums (fun j => (a:ℤ)*j+(d:ℤ)*K.card-(t:ℤ))
  rw [eq]
  by_cases nonempty : D.Nonempty
  · exact bound K sub nonempty
  · have ne : K≠univ\B := fun same => nonempty ⟨univ,top same⟩
    have z := not_nonempty_iff_eq_empty.mp nonempty
    rw [z,sum_empty,if_neg ne]; split <;> omega

lemma nonempty_full {b : ℕ} (D : Finset (Finset (Fin b))) (nonempty : D.Nonempty)
    (stable : ∀ U∈D, U∪univ∈D) : univ∈D := by
  obtain ⟨U,hu⟩ := nonempty
  simpa only [union_eq_right.mpr (subset_univ U)] using stable U hu

lemma five_without_adjacent (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅∈F) (full : univ∈F) (minSize : ∀ X∈F, X.Nonempty → 5≤X.card)
    (S : Finset (Fin 12)) (hS : S∈F) (s : S.card=5)
    (separated : ∀ U∈F, ∀ V∈F, U.card=5 → V.card=5 → (U∩V).card≠4) :
    ∃ w : Fin 12 → ℕ, 0<∑ i,w i ∧ F.card*(∑ i,w i) ≤ 2*(∑ X∈F,∑ i∈X,w i) := by
  classical
  obtain ⟨e,eqS⟩ := coordinates S s
  apply weight_from_fibers F e closed empty full minSize 4 2 17 (by decide) (by decide) (by decide) 14 (by decide)
  intro K sub
  let B := (univ : Finset (Fin 5)).map e
  let X (U : Finset (Fin 5)) := K∪U.map e
  let D := (univ : Finset (Finset (Fin 5))).filter (fun U => X U∈F)
  change D.Nonempty → _
  intro nonempty
  obtain ⟨uc,zero,_,small,fix,inter,size,inside,_,_⟩ := slice_data F e K closed empty full minSize sub
  have mem (U) : U∈D ↔ X U∈F := by simp [D]
  have top : univ∈D := nonempty_full D nonempty (fix univ (eqS ▸ hS))
  have cap : (univ\B).card=7 := by rw [card_sdiff_of_subset (subset_univ _)]; simp [B]
  have hk : K.card≤7 := (card_le_card sub).trans_eq cap
  have lo : K=∅ ↔ K.card=0 := card_eq_zero.symm
  have hi : K=univ\B ↔ K.card=7 := ⟨fun h => h ▸ cap,fun h => eq_of_subset_of_card_le sub (by omega)⟩
  have avoid (one : K.card=1) (U) (hu : U∈D) (four : U.card=4) : False := by
    have sz : (X U).card=5 := by rw [size,one,four]
    have cross : (X U∩S).card=4 := by rw [←eqS,inside,card_map,four]
    exact separated _ ((mem _).mp hu) S hS sz s cross
  have apart (U) (hu : U∈D) (V) (hv : V∈D) (_ : U≠V)
      (u5 : K.card+U.card=5) (v5 : K.card+V.card=5) (bad : K.card+(U∩V).card=4) : False :=
    separated _ ((mem _).mp hu) _ ((mem _).mp hv) ((size U).trans u5) ((size V).trans v5) ((inter U V).trans bad)
  have res := FranklLocal.fiber5 K.card hk D uc top (fun h => zero (lo.mpr h)) small avoid apart
  change (if K=univ\B then (14:ℤ) else 0) - (if K=∅ then 14 else 0) ≤ _
  have offset : (if K=univ\B then (14:ℤ) else 0) - (if K=∅ then 14 else 0) =
      (if K.card=0 then -14 else if K.card=7 then 14 else 0) := by
    simp only [hi,lo]; split_ifs <;> omega
  rw [offset]
  exact res

lemma five_with_adjacent (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅∈F) (full : univ∈F) (minSize : ∀ X∈F, X.Nonempty → 5≤X.card)
    (S T : Finset (Fin 12)) (hS : S∈F) (hT : T∈F) (s : S.card=5) (t : T.card=5) (cross : (S∩T).card=4) :
    ∃ w : Fin 12 → ℕ, 0<∑ i,w i ∧ F.card*(∑ i,w i) ≤ 2*(∑ X∈F,∑ i∈X,w i) := by
  classical
  obtain ⟨e,eqB,eqS,eqT⟩ := adjacent_coordinates S T s t cross
  apply weight_from_fibers F e closed empty full minSize 3 1 12 (by decide) (by decide) (by decide) 0 (by decide)
  intro K sub
  let B := (univ : Finset (Fin 6)).map e
  let D := (univ : Finset (Finset (Fin 6))).filter fun U => K∪U.map e∈F
  change D.Nonempty → _
  intro nonempty
  obtain ⟨uc,zero,_,small,fix,_,_,_,_,_⟩ := slice_data F e K closed empty full minSize sub
  have top : univ∈D := nonempty_full D nonempty (fix univ (eqB ▸ closed S hS T hT))
  have cap : (univ\B).card=6 := by rw [card_sdiff_of_subset (subset_univ _)]; simp [B]
  have res := FranklLocal.fiber6 K.card ((card_le_card sub).trans_eq cap) D uc top (fun h => zero (card_eq_zero.mp h)) small
    (fix _ (eqS ▸ hS)) (fix _ (eqT ▸ hT))
  change (if K=univ\B then (0:ℤ) else 0) - (if K=∅ then 0 else 0) ≤
    ∑ U ∈ D, (3*(U.card:ℤ)+1*(K.card:ℤ)-12)
  simpa only [ite_self,sub_zero,one_mul] using res

end FranklGlobal

namespace OMA.R_UnionClosed_union_closed_variants_univ_card_R2
open Finset UnionClosed
open scoped Classical

-- The 3-element minimum case on the fixed twelve-coordinate universe.
def H1 : Prop := ∀ F : Finset (Finset (Fin 12)), IsUnionClosed F → ∅ ∈ F → univ ∈ F →
    (∃ S ∈ F, S.card = 3) → (∀ S ∈ F, S.Nonempty → 3 ≤ S.card) →
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧
      F.card * (∑ i, w i) ≤ 2 * (∑ S ∈ F, ∑ i ∈ S, w i)

-- The 4-element minimum case on the fixed twelve-coordinate universe.
def H2 : Prop := ∀ F : Finset (Finset (Fin 12)), IsUnionClosed F → ∅ ∈ F → univ ∈ F →
    (∃ S ∈ F, S.card = 4) → (∀ S ∈ F, S.Nonempty → 4 ≤ S.card) →
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧
      F.card * (∑ i, w i) ≤ 2 * (∑ S ∈ F, ∑ i ∈ S, w i)

-- The 5-element minimum case on the fixed twelve-coordinate universe.
lemma minimum_five : ∀ F : Finset (Finset (Fin 12)), IsUnionClosed F → ∅ ∈ F → univ ∈ F →
    (∃ S ∈ F, ∃ T ∈ F, S ≠ T ∧ S.card=5 ∧ T.card=5) → (∀ S ∈ F, S.Nonempty → 5 ≤ S.card) →
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧
      F.card * (∑ i, w i) ≤ 2 * (∑ S ∈ F, ∑ i ∈ S, w i) := by
  intro F closed empty full existsFive minimal
  obtain ⟨S,hS,_,_,_,s,_⟩ := existsFive
  by_cases pair : ∃ A∈F, ∃ B∈F, A.card=5 ∧ B.card=5 ∧ (A∩B).card=4
  · obtain ⟨A,ha,B,hb,a,b,c⟩ := pair
    exact FranklGlobal.five_with_adjacent F closed empty full minimal A B ha hb a b c
  · exact FranklGlobal.five_without_adjacent F closed empty full minimal S hS s
      (fun A ha B hb a b c => pair ⟨A,ha,B,hb,a,b,c⟩)

lemma incidence (F : Finset (Finset (Fin 12))) (w : Fin 12 → ℕ) :
    (∑ S ∈ F, ∑ i ∈ S, w i) = ∑ i, w i*(F.filter (i ∈ ·)).card := by
  calc
    _ = ∑ S ∈ F, ∑ i : Fin 12, if i ∈ S then w i else 0 := by simp
    _ = ∑ i : Fin 12, ∑ S ∈ F, if i ∈ S then w i else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro i _
      rw [←sum_filter]
      simp [Nat.mul_comm]

lemma witness (F : Finset (Finset (Fin 12))) (w : Fin 12 → ℕ) (wp : 0 < ∑ i, w i)
    (hw : F.card * (∑ i, w i) ≤ 2 * (∑ S ∈ F, ∑ i ∈ S, w i)) :
    ∃ i, F.card ≤ 2*(F.filter (i ∈ ·)).card := by
  by_contra! fail
  have h := sum_le_sum (s:=univ) (fun (i : Fin 12) _ =>
    Nat.mul_le_mul_left (w i) (show 2*(F.filter (i ∈ ·)).card + 1 ≤ F.card from fail i))
  simp only [mul_add,mul_one,sum_add_distrib,←sum_mul] at h
  rw [incidence] at hw
  have twice : (∑ i, w i*(2*(F.filter (i ∈ ·)).card)) =
      2*(∑ i, w i*(F.filter (i ∈ ·)).card) := by rw [mul_sum]; apply sum_congr rfl; intros; ring
  rw [twice,mul_comm (∑ i, w i) F.card] at h
  omega

lemma small_member (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (a b : Fin 12) (pair : {a,b} ∈ F) : ∃ i, F.card ≤ 2*(F.filter (i ∈ ·)).card := by
  let A := F.filter (a ∈ ·)
  let B := F.filter (b ∈ ·)
  let none := F \ (A∪B)
  have fromNone {X : Finset (Fin 12)} (hX : X ∈ none) : X ∈ F ∧ a ∉ X ∧ b ∉ X := by
    have h := mem_sdiff.mp hX
    simpa [A,B,h.1] using h
  have inj : none.card ≤ (A∩B).card := by
    apply card_le_card_of_injOn (fun X => X∪{a,b})
    · intro X hX
      obtain ⟨xf,_,_⟩ := fromNone hX
      have u := closed _ xf _ pair
      exact mem_inter.mpr ⟨mem_filter.mpr ⟨u,by simp⟩,mem_filter.mpr ⟨u,by simp⟩⟩
    · intro X hX Y hY eq
      have x := fromNone hX
      have y := fromNone hY
      ext i
      by_cases ia : i=a
      · simp [ia,x.2.1,y.2.1]
      by_cases ib : i=b
      · simp [ib,x.2.2,y.2.2]
      simpa [ia,ib] using Finset.ext_iff.mp eq i
  have sub : A∪B ⊆ F := union_subset (filter_subset _ _) (filter_subset _ _)
  have partition := card_sdiff_add_card_eq_card sub
  have overlap := card_union_add_card_inter A B
  change none.card + (A∪B).card = F.card at partition
  by_cases h : F.card ≤ 2*A.card
  · exact ⟨a,h⟩
  · exact ⟨b,by change F.card ≤ 2*B.card; omega⟩

lemma large_members (F : Finset (Finset (Fin 12))) (empty : ∅ ∈ F) (full : univ ∈ F)
    (hl : ∀ S ∈ F, S.Nonempty → 6 ≤ S.card) : ∃ i, F.card ≤ 2*(F.filter (i ∈ ·)).card := by
  let M := (F.erase ∅).erase univ
  have ef : (univ : Finset (Fin 12)) ≠ ∅ := univ_nonempty.ne_empty
  have nu : univ ∉ M := notMem_erase _ _
  have ne : ∅ ∉ M := fun h => (notMem_erase ∅ F) (mem_of_mem_erase h)
  have hsplit : F = insert ∅ (insert univ M) := by
    dsimp [M]; rw [insert_erase (mem_erase.mpr ⟨ef,full⟩), insert_erase empty]
  have sum : 6*M.card ≤ ∑ S ∈ M, S.card := by
    have h := sum_le_sum (s:=M) (f:=fun _ => 6) (g:=Finset.card) (fun S hS =>
      hl S (mem_of_mem_erase (mem_of_mem_erase hS)) (nonempty_iff_ne_empty.mpr (mem_erase.mp (mem_of_mem_erase hS)).1))
    simpa [Nat.mul_comm] using h
  apply witness F (fun _ => 1) (by simp)
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,card_univ,Fintype.card_fin,mul_one]
  have n0 : (∅ : Finset (Fin 12)) ∉ insert univ M := by simp [ef.symm,ne]
  rw [hsplit,card_insert_of_notMem n0,card_insert_of_notMem nu,sum_insert n0,sum_insert nu]
  simp only [card_empty,card_univ,Fintype.card_fin,zero_add]
  omega

-- With a unique five-set, one proper member of size at least seven
-- balances its one-unit deficit. Without such a member every nonempty
-- set contains the five-set: a six-set missing it would make a union
-- of size between seven and eleven.
lemma unique_five (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅∈F) (full : univ∈F) (low : ∀ X ∈ F, X.Nonempty → 5 ≤ X.card)
    (S : Finset (Fin 12)) (sf : S∈F) (sc : S.card=5)
    (only : ∀ X ∈ F, X.card=5 → X=S) : ∃ i, F.card ≤ 2*(F.filter (i ∈ ·)).card := by
  have se : S ≠ ∅ := by intro h; simp [h] at sc
  have su : S ≠ univ := by intro h; simp [h] at sc
  have ue : (univ : Finset (Fin 12)) ≠ ∅ := univ_nonempty.ne_empty
  by_cases big : ∃ Y ∈ F, Y≠univ ∧ 7≤Y.card
  · obtain ⟨Y,yf,yu,yc⟩ := big
    have ye : Y≠∅ := by intro e; simp [e] at yc
    have ys : Y≠S := by intro e; rw [e,sc] at yc; omega
    let P := (((F.erase ∅).erase univ).erase S).erase Y
    have sm : S ∈ (F.erase ∅).erase univ := mem_erase.mpr ⟨su,mem_erase.mpr ⟨se,sf⟩⟩
    have ym : Y ∈ ((F.erase ∅).erase univ).erase S := mem_erase.mpr ⟨ys,mem_erase.mpr ⟨yu,mem_erase.mpr ⟨ye,yf⟩⟩⟩
    have allp : 6*P.card ≤ ∑ X ∈ P, X.card := by
      have bound (X) (h : X ∈ P) : 6 ≤ X.card := by
        simp only [P,mem_erase] at h
        have l := low X h.2.2.2.2 (nonempty_iff_ne_empty.mpr h.2.2.2.1)
        have ne := h.2.1
        by_contra! no
        exact ne (only X h.2.2.2.2 (by omega))
      have := sum_le_sum (s:=P) (f:=fun _ => 6) (g:=Finset.card) bound
      simpa [Nat.mul_comm] using this
    have pe : ∅∉P := by simp [P]
    have pu : univ∉P := by simp [P]
    have ps : S∉P := by simp [P]
    have py : Y∉P := notMem_erase _ _
    have split : F=insert ∅ (insert univ (insert S (insert Y P))) := by
      dsimp [P]; rw [insert_erase ym,insert_erase sm,insert_erase (mem_erase.mpr ⟨ue,full⟩),insert_erase empty]
    apply witness F (fun _ => 1) (by simp)
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,card_univ,Fintype.card_fin,mul_one]
    rw [split]
    simp [pe,pu,ps,py,se.symm,su.symm,ue.symm,ye.symm,yu.symm,ys.symm,sc]
    omega
  · have all (X) (hX : X∈F) (ne : X.Nonempty) : S⊆X := by
      by_cases whole : X=univ
      · simp [whole]
      by_cases five : X.card=5
      · rw [only X hX five]
      have c := low X hX ne
      have upper : X.card<7 := by by_contra! no; exact big ⟨X,hX,whole,no⟩
      have six : X.card=6 := by omega
      by_contra no
      have sub : X ⊂ X∪S := Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left,fun eq => by
        have h : S ⊆ X∪S := subset_union_right
        rw [←eq] at h
        exact no h⟩
      have high := card_lt_card sub
      have cap := card_union_le X S
      have proper : X∪S≠univ := by intro eq; rw [eq] at cap; simp [six,sc] at cap
      exact big ⟨X∪S,closed _ hX _ sf,proper,by omega⟩
    obtain ⟨i,hi⟩ := nonempty_iff_ne_empty.mpr se
    have subset : F.erase ∅ ⊆ F.filter (i∈·) := by
      intro X hX
      exact mem_filter.mpr ⟨mem_of_mem_erase hX,all X (mem_of_mem_erase hX) (nonempty_iff_ne_empty.mpr (mem_erase.mp hX).1) hi⟩
    have h := card_le_card subset
    have p : 0 < (F.erase ∅).card := card_pos.mpr ⟨S,mem_erase.mpr ⟨se,sf⟩⟩
    have eq := card_erase_add_one empty
    exact ⟨i,by omega⟩

lemma twelve (h₃ : H1) (h₄ : H2) (F : Finset (Finset (Fin 12)))
    (closed : IsUnionClosed F) (empty : ∅∈F) (full : univ∈F) : ∃ i, F.card ≤ 2*(F.filter (i ∈ ·)).card := by
  by_cases small : ∃ S ∈ F, S.Nonempty ∧ S.card ≤ 2
  · obtain ⟨S,hS,ne,le⟩ := small
    by_cases one : S.card=1
    · obtain ⟨a,rfl⟩ := card_eq_one.mp one
      exact small_member F closed a a (by simpa using hS)
    · obtain ⟨a,b,_,rfl⟩ := card_eq_two.mp (show S.card=2 by have := card_pos.mpr ne; omega)
      exact small_member F closed a b hS
  have at3 (S) (hS : S∈F) (ne : S.Nonempty) : 3 ≤ S.card := by
    by_contra! no
    exact small ⟨S,hS,ne,by omega⟩
  have bump (k : ℕ) (bound : ∀ S ∈ F, S.Nonempty → k ≤ S.card)
      (no : ¬ ∃ S ∈ F, S.card=k) (S) (hS : S∈F) (hne : S.Nonempty) : k+1 ≤ S.card := by
    have := bound S hS hne
    have diff : S.card≠k := fun eq => no ⟨S,hS,eq⟩
    omega
  by_cases three : ∃ S ∈ F, S.card = 3
  · obtain ⟨w,p,b⟩ := h₃ F closed empty full three at3
    exact witness F w p b
  have at4 := bump 3 at3 three
  by_cases four : ∃ S ∈ F, S.card = 4
  · obtain ⟨w,p,b⟩ := h₄ F closed empty full four at4
    exact witness F w p b
  have at5 := bump 4 at4 four
  by_cases five : ∃ S ∈ F, S.card = 5
  · obtain ⟨S,sf,sc⟩ := five
    by_cases another : ∃ T ∈ F, T.card=5 ∧ T≠S
    · obtain ⟨T,tf,tc,ts⟩ := another
      obtain ⟨w,p,b⟩ := minimum_five F closed empty full ⟨S,sf,T,tf,ts.symm,sc,tc⟩ at5
      exact witness F w p b
    · exact unique_five F closed empty full at5 S sf sc (fun X hX c => by
        by_contra h
        exact another ⟨X,hX,c,h⟩)
  exact large_members F empty full (bump 5 at5 five)

lemma support_mem {α : Type*} [DecidableEq α] {F : Finset (Finset α)} (h : IsUnionClosed F)
    (e : ∅∈F) (B : Finset (Finset α)) (sub : B ⊆ F) : B.biUnion id ∈ F := by
  induction B using Finset.induction_on with
  | empty => simpa using e
  | @insert X B _ ih =>
    rw [biUnion_insert]
    exact h _ (sub (mem_insert_self ..)) _ (ih (fun _ hB => sub (mem_insert_of_mem hB)))

lemma clones {α : Type*} [Fintype α] [DecidableEq α] (T : Finset α) (n : T.Nonempty)
    (bound : Fintype.card α ≤ 12) : ∃ f : Fin 12 → α, (∀ i, f i ∈ T) ∧ ∀ t ∈ T, ∃ i, f i = t := by
  obtain ⟨z,hz⟩ := n
  let e := Fintype.equivFin ↥T
  have size : Fintype.card ↥T ≤ 12 := by simpa using (T.card_le_univ.trans bound)
  let f (i : Fin 12) : α := if hi : i.val < Fintype.card ↥T then (e.symm ⟨i.val,hi⟩).val else z
  refine ⟨f,?_,?_⟩
  · intro i; dsimp [f]; split_ifs; exact Subtype.property _; exact hz
  · intro t ht
    let j := e ⟨t,ht⟩
    refine ⟨⟨j.val,j.isLt.trans_le size⟩,?_⟩
    change (if hi : j.val < Fintype.card ↥T then (e.symm ⟨j.val,hi⟩).val else z) = t
    rw [dif_pos j.isLt]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨t,ht⟩)

theorem main : H1 → H2 → type_of% @UnionClosed.union_closed.variants.univ_card := by
  intro h₃ h₄ α de A fa neα nontrivial closed bound
  by_cases zero : A=∅
  · subst A; obtain ⟨a⟩ := neα; exact ⟨a,by simp⟩
  have someSet : ∃ S ∈ A, S.Nonempty := by
    by_contra! empty
    apply nontrivial
    apply (Finset.nonempty_iff_ne_empty.mpr zero).subset_singleton_iff.mp
    intro S hS
    exact mem_singleton.mpr (empty S hS)
  let F := insert ∅ A
  have fclosed : IsUnionClosed F := by
    intro X hx Y hy
    rcases mem_insert.mp hx with rfl | x <;> rcases mem_insert.mp hy with rfl | y
    · simp [F]
    · simpa [F] using (mem_insert_of_mem y : Y∈F)
    · simpa [F] using (mem_insert_of_mem x : X∈F)
    · exact mem_insert_of_mem (closed X x Y y)
  let T := F.biUnion id
  have en : ∅ ∈ F := mem_insert_self ..
  have top : T ∈ F := support_mem fclosed en F (by rfl)
  have sub (S : Finset α) (hS : S∈F) : S ⊆ T := fun i hi => mem_biUnion.mpr ⟨S,hS,hi⟩
  obtain ⟨S,sA,t,ht⟩ := someSet
  obtain ⟨f,inside,surj⟩ := clones T ⟨t,sub S (mem_insert_of_mem sA) ht⟩ bound
  let pull (S : Finset α) := univ.filter (fun i : Fin 12 => f i ∈ S)
  let B := F.image pull
  have pmem (S : Finset α) (i : Fin 12) : i∈pull S ↔ f i ∈ S := by simp [pull]
  have inj : Set.InjOn pull (F : Set (Finset α)) := by
    intro X hx Y hy eq
    ext i
    by_cases ti : i ∈ T
    · obtain ⟨u,rfl⟩ := surj i ti
      rw [←pmem X,←pmem Y,eq]
    · have nx : i∉X := fun h => ti (sub X hx h)
      have ny : i∉Y := fun h => ti (sub Y hy h)
      simp [nx,ny]
  have bclosed : IsUnionClosed B := by
    intro U hu V hv
    obtain ⟨X,hX,rfl⟩ := mem_image.mp hu
    obtain ⟨Y,hY,rfl⟩ := mem_image.mp hv
    refine mem_image.mpr ⟨X∪Y,fclosed _ hX _ hY,?_⟩
    ext i; simp [pull]
  have be : ∅∈B := mem_image.mpr ⟨∅,en,by simp [pull]⟩
  have bt : univ∈B := mem_image.mpr ⟨T,top,by ext i; simp [pull,inside]⟩
  obtain ⟨i,hi⟩ := twelve h₃ h₄ B bclosed be bt
  have eqf : B.filter (i ∈ ·) = (F.filter (f i ∈ ·)).image pull := by
    ext U
    constructor
    · intro hU
      obtain ⟨hU,u⟩ := mem_filter.mp hU
      obtain ⟨X,hX,rfl⟩ := mem_image.mp hU
      exact mem_image.mpr ⟨X,mem_filter.mpr ⟨hX,(pmem _ _).mp u⟩,rfl⟩
    · intro hU
      obtain ⟨X,hX,rfl⟩ := mem_image.mp hU
      exact mem_filter.mpr ⟨mem_image_of_mem _ (mem_filter.mp hX).1,(pmem _ _).mpr (mem_filter.mp hX).2⟩
  have eqA : F.filter (f i ∈ ·) = A.filter (f i ∈ ·) := by ext X; simp [F]; aesop
  have bc : B.card=F.card := card_image_of_injOn inj
  have fi : Set.InjOn pull (↑(F.filter (f i ∈ ·)) : Set (Finset α)) :=
    inj.mono (fun _ hs => (mem_filter.mp hs).1)
  have freq : (B.filter (i ∈ ·)).card = (A.filter (f i ∈ ·)).card := by
    rw [eqf,card_image_of_injOn fi,eqA]
  rw [bc,freq] at hi
  have hb : A.card ≤ 2*(A.filter (f i ∈ ·)).card := (card_le_card (subset_insert ∅ A)).trans hi
  refine ⟨f i,?_⟩
  have cast : (A.card:ℚ) ≤ 2*((A.filter (f i ∈ ·)).card:ℚ) := by exact_mod_cast hb
  linarith

end OMA.R_UnionClosed_union_closed_variants_univ_card_R2
