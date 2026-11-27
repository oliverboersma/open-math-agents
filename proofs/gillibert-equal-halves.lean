import OMAStatements.S_gillibert_equal_halves
import Mathlib

/-!
# Disproof of Gillibert's Equal Halves conjecture

Witness `W`: a vertex-transitive graph on 28 vertices, 9-regular, with automorphism group PSL(2,8) of order 504,
number 2659 of the Holt–Royle census of vertex-transitive graphs (file alltrans28_k=09.gz, line 1186; Zenodo
4010122). Its graph6 string is
  [}aKKQacQAGP?rAI?a`GPE@SObh?faTOpDSWSWojCdI@eO{EpH?HqO_ecdAHoq_S
`W` is connected and vertex-transitive (three explicit automorphisms), so the conjecture would give a split.

Idea. An isomorphism `G[A] ≃ G[Aᶜ]` gives an involution `τ` of the vertices that swaps the two sides and preserves
adjacency inside each side. Hence every same-side vertex statistic (degree, triangle count and number of vertices at
distance two, all inside the vertex's own side) is `τ`-invariant, so for every vertex predicate built from these
statistics the two sides have equal counts, and `|A| = 14`. We use 15 such tests (parities and residues mod 4 of
counts) and check by kernel computation that every 2-colouring of the 28 vertices with vertex 0 coloured `true` has
colour classes of different sizes or fails a test. Up to the stabiliser of vertex 0 (order 18, acting on its 9
neighbours) only 46 colourings of the neighbours need to be checked. For each of them, all `2^18` colourings of
the remaining vertices are checked at once: each colouring is one bit position of `2^18`-bit numbers (bit planes)
combined with `Nat.land/lor/xor`. A generic lemma (`IsHom.circuit'`) transfers this bit-plane computation to the
Boolean one, bit by bit.
-/
namespace EH

/-- Boolean operations on a carrier: `Bool` for the meaning, `Nat` bit planes for the computation. -/
structure Ops (W : Type) where
  band : W → W → W
  bor : W → W → W
  bxor : W → W → W
  one : W
  zero : W

def boolOps : Ops Bool := ⟨and, or, xor, true, false⟩
def natOps (N : Nat) : Ops Nat := ⟨Nat.land, Nat.lor, Nat.xor, 2 ^ N - 1, 0⟩

/-- neighbour lists of the witness graph -/
def nbL : List (List Nat) := [[1, 2, 3, 4, 5, 6, 7, 8, 9], [0, 2, 3, 10, 11, 19, 20, 21, 22], [0, 1, 8, 15, 18, 22, 25, 26, 27], [0, 1, 9, 16, 17, 21, 24, 26, 27], [0, 5, 7, 13, 16, 19, 23, 24, 27], [0, 4, 6, 14, 15, 20, 23, 25, 26], [0, 5, 8, 11, 12, 19, 22, 24, 25], [0, 4, 9, 10, 12, 20, 21, 24, 25], [0, 2, 6, 13, 17, 19, 21, 23, 26], [0, 3, 7, 14, 18, 20, 22, 23, 27], [1, 7, 11, 12, 13, 15, 19, 25, 27], [1, 6, 10, 12, 14, 16, 20, 24, 26], [6, 7, 10, 11, 17, 18, 21, 22, 23], [4, 8, 10, 16, 17, 18, 21, 25, 27], [5, 9, 11, 15, 17, 18, 22, 24, 26], [2, 5, 10, 14, 16, 18, 19, 20, 27], [3, 4, 11, 13, 15, 17, 19, 20, 26], [3, 8, 12, 13, 14, 16, 22, 23, 24], [2, 9, 12, 13, 14, 15, 21, 23, 25], [1, 4, 6, 8, 10, 15, 16, 22, 23], [1, 5, 7, 9, 11, 15, 16, 21, 23], [1, 3, 7, 8, 12, 13, 18, 20, 26], [1, 2, 6, 9, 12, 14, 17, 19, 27], [4, 5, 8, 9, 12, 17, 18, 19, 20], [3, 4, 6, 7, 11, 14, 17, 25, 27], [2, 5, 6, 7, 10, 13, 18, 24, 26], [2, 3, 5, 8, 11, 14, 16, 21, 25], [2, 3, 4, 9, 10, 13, 15, 22, 24]]

def nb (v : Nat) : List Nat := nbL.getD v []
/-- triangles at v: pairs u < w of adjacent neighbours -/
def triD : List (List (Nat × Nat)) := [[(1,2),(1,3),(2,8),(3,9),(4,5),(4,7),(5,6),(6,8),(7,9)],[(0,2),(0,3),(2,22),(3,21),(10,11),(10,19),(11,20),(19,22),(20,21)],[(0,1),(0,8),(1,22),(8,26),(15,18),(15,27),(18,25),(22,27),(25,26)],[(0,1),(0,9),(1,21),(9,27),(16,17),(16,26),(17,24),(21,26),(24,27)],[(0,5),(0,7),(5,23),(7,24),(13,16),(13,27),(16,19),(19,23),(24,27)],[(0,4),(0,6),(4,23),(6,25),(14,15),(14,26),(15,20),(20,23),(25,26)],[(0,5),(0,8),(5,25),(8,19),(11,12),(11,24),(12,22),(19,22),(24,25)],[(0,4),(0,9),(4,24),(9,20),(10,12),(10,25),(12,21),(20,21),(24,25)],[(0,2),(0,6),(2,26),(6,19),(13,17),(13,21),(17,23),(19,23),(21,26)],[(0,3),(0,7),(3,27),(7,20),(14,18),(14,22),(18,23),(20,23),(22,27)],[(1,11),(1,19),(7,12),(7,25),(11,12),(13,25),(13,27),(15,19),(15,27)],[(1,10),(1,20),(6,12),(6,24),(10,12),(14,24),(14,26),(16,20),(16,26)],[(6,11),(6,22),(7,10),(7,21),(10,11),(17,22),(17,23),(18,21),(18,23)],[(4,16),(4,27),(8,17),(8,21),(10,25),(10,27),(16,17),(18,21),(18,25)],[(5,15),(5,26),(9,18),(9,22),(11,24),(11,26),(15,18),(17,22),(17,24)],[(2,18),(2,27),(5,14),(5,20),(10,19),(10,27),(14,18),(16,19),(16,20)],[(3,17),(3,26),(4,13),(4,19),(11,20),(11,26),(13,17),(15,19),(15,20)],[(3,16),(3,24),(8,13),(8,23),(12,22),(12,23),(13,16),(14,22),(14,24)],[(2,15),(2,25),(9,14),(9,23),(12,21),(12,23),(13,21),(13,25),(14,15)],[(1,10),(1,22),(4,16),(4,23),(6,8),(6,22),(8,23),(10,15),(15,16)],[(1,11),(1,21),(5,15),(5,23),(7,9),(7,21),(9,23),(11,16),(15,16)],[(1,3),(1,20),(3,26),(7,12),(7,20),(8,13),(8,26),(12,18),(13,18)],[(1,2),(1,19),(2,27),(6,12),(6,19),(9,14),(9,27),(12,17),(14,17)],[(4,5),(4,19),(5,20),(8,17),(8,19),(9,18),(9,20),(12,17),(12,18)],[(3,17),(3,27),(4,7),(4,27),(6,11),(6,25),(7,25),(11,14),(14,17)],[(2,18),(2,26),(5,6),(5,26),(6,24),(7,10),(7,24),(10,13),(13,18)],[(2,8),(2,25),(3,16),(3,21),(5,14),(5,25),(8,21),(11,14),(11,16)],[(2,15),(2,22),(3,9),(3,24),(4,13),(4,24),(9,22),(10,13),(10,15)]]
/-- distance-two vertices w of v with their common neighbours -/
def d2D : List (List (Nat × List Nat)) := [[(10,[1,7]),(11,[1,6]),(12,[6,7]),(13,[4,8]),(14,[5,9]),(15,[2,5]),(16,[3,4]),(17,[3,8]),(18,[2,9]),(19,[1,4,6,8]),(20,[1,5,7,9]),(21,[1,3,7,8]),(22,[1,2,6,9]),(23,[4,5,8,9]),(24,[3,4,6,7]),(25,[2,5,6,7]),(26,[2,3,5,8]),(27,[2,3,4,9])],[(4,[0,19]),(5,[0,20]),(6,[0,11,19,22]),(7,[0,10,20,21]),(8,[0,2,19,21]),(9,[0,3,20,22]),(12,[10,11,21,22]),(13,[10,21]),(14,[11,22]),(15,[2,10,19,20]),(16,[3,11,19,20]),(17,[3,22]),(18,[2,21]),(23,[19,20]),(24,[3,11]),(25,[2,10]),(26,[2,3,11,21]),(27,[2,3,10,22])],[(3,[0,1,26,27]),(4,[0,27]),(5,[0,15,25,26]),(6,[0,8,22,25]),(7,[0,25]),(9,[0,18,22,27]),(10,[1,15,25,27]),(11,[1,26]),(12,[18,22]),(13,[8,18,25,27]),(14,[15,18,22,26]),(16,[15,26]),(17,[8,22]),(19,[1,8,15,22]),(20,[1,15]),(21,[1,8,18,26]),(23,[8,18]),(24,[25,27])],[(2,[0,1,26,27]),(4,[0,16,24,27]),(5,[0,26]),(6,[0,24]),(7,[0,9,21,24]),(8,[0,17,21,26]),(10,[1,27]),(11,[1,16,24,26]),(12,[17,21]),(13,[16,17,21,27]),(14,[9,17,24,26]),(15,[16,27]),(18,[9,21]),(19,[1,16]),(20,[1,9,16,21]),(22,[1,9,17,27]),(23,[9,17]),(25,[24,26])],[(1,[0,19]),(2,[0,27]),(3,[0,16,24,27]),(6,[0,5,19,24]),(8,[0,13,19,23]),(9,[0,7,23,27]),(10,[7,13,19,27]),(11,[16,24]),(12,[7,23]),(14,[5,24]),(15,[5,16,19,27]),(17,[13,16,23,24]),(18,[13,23]),(20,[5,7,16,23]),(21,[7,13]),(22,[19,27]),(25,[5,7,13,24]),(26,[5,16])],[(1,[0,20]),(2,[0,15,25,26]),(3,[0,26]),(7,[0,4,20,25]),(8,[0,6,23,26]),(9,[0,14,20,23]),(10,[15,25]),(11,[6,14,20,26]),(12,[6,23]),(13,[4,25]),(16,[4,15,20,26]),(17,[14,23]),(18,[14,15,23,25]),(19,[4,6,15,23]),(21,[20,26]),(22,[6,14]),(24,[4,6,14,25]),(27,[4,15])],[(1,[0,11,19,22]),(2,[0,8,22,25]),(3,[0,24]),(4,[0,5,19,24]),(7,[0,12,24,25]),(9,[0,22]),(10,[11,12,19,25]),(13,[8,25]),(14,[5,11,22,24]),(15,[5,19]),(16,[11,19]),(17,[8,12,22,24]),(18,[12,25]),(20,[5,11]),(21,[8,12]),(23,[5,8,12,19]),(26,[5,8,11,25]),(27,[22,24])],[(1,[0,10,20,21]),(2,[0,25]),(3,[0,9,21,24]),(5,[0,4,20,25]),(6,[0,12,24,25]),(8,[0,21]),(11,[10,12,20,24]),(13,[4,10,21,25]),(14,[9,24]),(15,[10,20]),(16,[4,20]),(17,[12,24]),(18,[9,12,21,25]),(19,[4,10]),(22,[9,12]),(23,[4,9,12,20]),(26,[21,25]),(27,[4,9,10,24])],[(1,[0,2,19,21]),(3,[0,17,21,26]),(4,[0,13,19,23]),(5,[0,6,23,26]),(7,[0,21]),(9,[0,23]),(10,[13,19]),(11,[6,26]),(12,[6,17,21,23]),(14,[17,26]),(15,[2,19]),(16,[13,17,19,26]),(18,[2,13,21,23]),(20,[21,23]),(22,[2,6,17,19]),(24,[6,17]),(25,[2,6,13,26]),(27,[2,13])],[(1,[0,3,20,22]),(2,[0,18,22,27]),(4,[0,7,23,27]),(5,[0,14,20,23]),(6,[0,22]),(8,[0,23]),(10,[7,27]),(11,[14,20]),(12,[7,18,22,23]),(13,[18,27]),(15,[14,18,20,27]),(16,[3,20]),(17,[3,14,22,23]),(19,[22,23]),(21,[3,7,18,20]),(24,[3,7,14,27]),(25,[7,18]),(26,[3,14])],[(0,[1,7]),(2,[1,15,25,27]),(3,[1,27]),(4,[7,13,19,27]),(5,[15,25]),(6,[11,12,19,25]),(8,[13,19]),(9,[7,27]),(14,[11,15]),(16,[11,13,15,19]),(17,[12,13]),(18,[12,13,15,25]),(20,[1,7,11,15]),(21,[1,7,12,13]),(22,[1,12,19,27]),(23,[12,19]),(24,[7,11,25,27]),(26,[11,25])],[(0,[1,6]),(2,[1,26]),(3,[1,16,24,26]),(4,[16,24]),(5,[6,14,20,26]),(7,[10,12,20,24]),(8,[6,26]),(9,[14,20]),(13,[10,16]),(15,[10,14,16,20]),(17,[12,14,16,24]),(18,[12,14]),(19,[1,6,10,16]),(21,[1,12,20,26]),(22,[1,6,12,14]),(23,[12,20]),(25,[6,10,24,26]),(27,[10,24])],[(0,[6,7]),(1,[10,11,21,22]),(2,[18,22]),(3,[17,21]),(4,[7,23]),(5,[6,23]),(8,[6,17,21,23]),(9,[7,18,22,23]),(13,[10,17,18,21]),(14,[11,17,18,22]),(15,[10,18]),(16,[11,17]),(19,[6,10,22,23]),(20,[7,11,21,23]),(24,[6,7,11,17]),(25,[6,7,10,18]),(26,[11,21]),(27,[10,22])],[(0,[4,8]),(1,[10,21]),(2,[8,18,25,27]),(3,[16,17,21,27]),(5,[4,25]),(6,[8,25]),(7,[4,10,21,25]),(9,[18,27]),(11,[10,16]),(12,[10,17,18,21]),(14,[17,18]),(15,[10,16,18,27]),(19,[4,8,10,16]),(20,[16,21]),(22,[17,27]),(23,[4,8,17,18]),(24,[4,17,25,27]),(26,[8,16,21,25])],[(0,[5,9]),(1,[11,22]),(2,[15,18,22,26]),(3,[9,17,24,26]),(4,[5,24]),(6,[5,11,22,24]),(7,[9,24]),(8,[17,26]),(10,[11,15]),(12,[11,17,18,22]),(13,[17,18]),(16,[11,15,17,26]),(19,[15,22]),(20,[5,9,11,15]),(21,[18,26]),(23,[5,9,17,18]),(25,[5,18,24,26]),(27,[9,15,22,24])],[(0,[2,5]),(1,[2,10,19,20]),(3,[16,27]),(4,[5,16,19,27]),(6,[5,19]),(7,[10,20]),(8,[2,19]),(9,[14,18,20,27]),(11,[10,14,16,20]),(12,[10,18]),(13,[10,16,18,27]),(17,[14,16]),(21,[18,20]),(22,[2,14,19,27]),(23,[5,18,19,20]),(24,[14,27]),(25,[2,5,10,18]),(26,[2,5,14,16])],[(0,[3,4]),(1,[3,11,19,20]),(2,[15,26]),(5,[4,15,20,26]),(6,[11,19]),(7,[4,20]),(8,[13,17,19,26]),(9,[3,20]),(10,[11,13,15,19]),(12,[11,17]),(14,[11,15,17,26]),(18,[13,15]),(21,[3,13,20,26]),(22,[17,19]),(23,[4,17,19,20]),(24,[3,4,11,17]),(25,[13,26]),(27,[3,4,13,15])],[(0,[3,8]),(1,[3,22]),(2,[8,22]),(4,[13,16,23,24]),(5,[14,23]),(6,[8,12,22,24]),(7,[12,24]),(9,[3,14,22,23]),(10,[12,13]),(11,[12,14,16,24]),(15,[14,16]),(18,[12,13,14,23]),(19,[8,16,22,23]),(20,[16,23]),(21,[3,8,12,13]),(25,[13,24]),(26,[3,8,14,16]),(27,[3,13,22,24])],[(0,[2,9]),(1,[2,21]),(3,[9,21]),(4,[13,23]),(5,[14,15,23,25]),(6,[12,25]),(7,[9,12,21,25]),(8,[2,13,21,23]),(10,[12,13,15,25]),(11,[12,14]),(16,[13,15]),(17,[12,13,14,23]),(19,[15,23]),(20,[9,15,21,23]),(22,[2,9,12,14]),(24,[14,25]),(26,[2,14,21,25]),(27,[2,9,13,15])],[(0,[1,4,6,8]),(2,[1,8,15,22]),(3,[1,16]),(5,[4,6,15,23]),(7,[4,10]),(9,[22,23]),(11,[1,6,10,16]),(12,[6,10,22,23]),(13,[4,8,10,16]),(14,[15,22]),(17,[8,16,22,23]),(18,[15,23]),(20,[1,15,16,23]),(21,[1,8]),(24,[4,6]),(25,[6,10]),(26,[8,16]),(27,[4,10,15,22])],[(0,[1,5,7,9]),(2,[1,15]),(3,[1,9,16,21]),(4,[5,7,16,23]),(6,[5,11]),(8,[21,23]),(10,[1,7,11,15]),(12,[7,11,21,23]),(13,[16,21]),(14,[5,9,11,15]),(17,[16,23]),(18,[9,15,21,23]),(19,[1,15,16,23]),(22,[1,9]),(24,[7,11]),(25,[5,7]),(26,[5,11,16,21]),(27,[9,15])],[(0,[1,3,7,8]),(2,[1,8,18,26]),(4,[7,13]),(5,[20,26]),(6,[8,12]),(9,[3,7,18,20]),(10,[1,7,12,13]),(11,[1,12,20,26]),(14,[18,26]),(15,[18,20]),(16,[3,13,20,26]),(17,[3,8,12,13]),(19,[1,8]),(22,[1,12]),(23,[8,12,18,20]),(24,[3,7]),(25,[7,13,18,26]),(27,[3,13])],[(0,[1,2,6,9]),(3,[1,9,17,27]),(4,[19,27]),(5,[6,14]),(7,[9,12]),(8,[2,6,17,19]),(10,[1,12,19,27]),(11,[1,6,12,14]),(13,[17,27]),(15,[2,14,19,27]),(16,[17,19]),(18,[2,9,12,14]),(20,[1,9]),(21,[1,12]),(23,[9,12,17,19]),(24,[6,14,17,27]),(25,[2,6]),(26,[2,14])],[(0,[4,5,8,9]),(1,[19,20]),(2,[8,18]),(3,[9,17]),(6,[5,8,12,19]),(7,[4,9,12,20]),(10,[12,19]),(11,[12,20]),(13,[4,8,17,18]),(14,[5,9,17,18]),(15,[5,18,19,20]),(16,[4,17,19,20]),(21,[8,12,18,20]),(22,[9,12,17,19]),(24,[4,17]),(25,[5,18]),(26,[5,8]),(27,[4,9])],[(0,[3,4,6,7]),(1,[3,11]),(2,[25,27]),(5,[4,6,14,25]),(8,[6,17]),(9,[3,7,14,27]),(10,[7,11,25,27]),(12,[6,7,11,17]),(13,[4,17,25,27]),(15,[14,27]),(16,[3,4,11,17]),(18,[14,25]),(19,[4,6]),(20,[7,11]),(21,[3,7]),(22,[6,14,17,27]),(23,[4,17]),(26,[3,11,14,25])],[(0,[2,5,6,7]),(1,[2,10]),(3,[24,26]),(4,[5,7,13,24]),(8,[2,6,13,26]),(9,[7,18]),(11,[6,10,24,26]),(12,[6,7,10,18]),(14,[5,18,24,26]),(15,[2,5,10,18]),(16,[13,26]),(17,[13,24]),(19,[6,10]),(20,[5,7]),(21,[7,13,18,26]),(22,[2,6]),(23,[5,18]),(27,[2,10,13,24])],[(0,[2,3,5,8]),(1,[2,3,11,21]),(4,[5,16]),(6,[5,8,11,25]),(7,[21,25]),(9,[3,14]),(10,[11,25]),(12,[11,21]),(13,[8,16,21,25]),(15,[2,5,14,16]),(17,[3,8,14,16]),(18,[2,14,21,25]),(19,[8,16]),(20,[5,11,16,21]),(22,[2,14]),(23,[5,8]),(24,[3,11,14,25]),(27,[2,3])],[(0,[2,3,4,9]),(1,[2,3,10,22]),(5,[4,15]),(6,[22,24]),(7,[4,9,10,24]),(8,[2,13]),(11,[10,24]),(12,[10,22]),(14,[9,15,22,24]),(16,[3,4,13,15]),(17,[3,13,22,24]),(18,[2,9,13,15]),(19,[4,10,15,22]),(20,[9,15]),(21,[3,13]),(23,[4,9]),(25,[2,10,13,24]),(26,[2,3])]]
def triL (v : Nat) : List (Nat × Nat) := triD.getD v []
def d2L (v : Nat) : List (Nat × List Nat) := d2D.getD v []

/-- a literal: bit `b` of statistic `s` (0 degree, 1 triangles, 2 distance-two count), possibly negated -/
structure Lit where
  s : Nat
  b : Nat
  pol : Bool

/-- a test: a conjunction of literals per vertex; mode 0 parity of the total count, mode k > 0 equality of the
two sides' counts modulo 2^k -/
structure Test where
  lits : List Lit
  mode : Nat

section
variable {W : Type} (o : Ops W)

def bnot (a : W) : W := o.bxor o.one a

def inc : List W → W → List W
  | [], _ => []
  | b :: bs, x => o.bxor b x :: inc bs (o.band b x)

def cnt (k : Nat) (xs : List W) : List W := xs.foldl (inc o) (List.replicate k o.zero)

def orAll (xs : List W) : W := xs.foldl o.bor o.zero
def xorAll (xs : List W) : W := xs.foldl o.bxor o.zero
def andAll (xs : List W) : W := xs.foldl o.band o.one

def getS (x : List W) (v : Nat) : W := x.getD v o.zero

def same (x : List W) (v u : Nat) : W := bnot o (o.bxor (getS o x v) (getS o x u))

def stats (x : List W) (v : Nat) : List (List W) :=
  [cnt o 4 ((nb v).map (same o x v)),
   cnt o 4 ((triL v).map (fun p => o.band (same o x v p.1) (same o x v p.2))),
   cnt o 4 ((d2L v).map (fun q => o.band (same o x v q.1) (orAll o (q.2.map (same o x v)))))]

def litV (st : List (List W)) (l : Lit) : W :=
  let bit := (st.getD l.s []).getD l.b o.zero
  if l.pol then bit else bnot o bit

def predV (st : List (List W)) (t : Test) : W := andAll o (t.lits.map (litV o st))

def psL (sts : List (List (List W))) (t : Test) : List W :=
  (List.range 28).map (fun v => predV o (sts.getD v []) t)

def sideL (x : List W) (ps : List W) (pos : Bool) : List W :=
  (List.range 28).map (fun v => o.band (if pos then getS o x v else bnot o (getS o x v)) (ps.getD v o.zero))

def testBit' (x : List W) (sts : List (List (List W))) (t : Test) : W :=
  if t.mode = 0 then xorAll o (psL o sts t)
  else orAll o (List.zipWith o.bxor (cnt o t.mode (sideL o x (psL o sts t) true))
    (cnt o t.mode (sideL o x (psL o sts t) false)))

def circuit (tests : List Test) (x : List W) : W :=
  let sts := (List.range 28).map (stats o x)
  let sz := cnt o 5 x
  -- 14 = 0b01110 (little endian 0,1,1,1,0)
  let size14 := andAll o [bnot o (sz.getD 0 o.zero), sz.getD 1 o.zero, sz.getD 2 o.zero, sz.getD 3 o.zero,
    bnot o (sz.getD 4 o.zero)]
  o.bor (bnot o size14) (orAll o (tests.map (testBit' o x sts)))
end

/-- `planes K` : K patterns over 2^K bits; pattern i has bit j equal to bit i of j. -/
def planes : Nat → List Nat
  | 0 => []
  | K+1 => (planes K).map (fun p => Nat.lor p (Nat.shiftLeft p (2 ^ K))) ++ [Nat.shiftLeft (2 ^ (2 ^ K) - 1) (2 ^ K)]

/-- inputs of chunk `r`: vertex 0 in A; the neighbours 1..9 of vertex 0 coloured by the bits of `r`; the other 18
vertices 10..27 sliced over the 2^18 bit positions. -/
def chunkInputs (r : Nat) : List Nat :=
  (2 ^ (2 ^ 18) - 1) :: (List.range 9).map (fun i => if r.testBit i then 2 ^ (2 ^ 18) - 1 else 0) ++ planes 18

def checkChunk (tests : List Test) (r : Nat) : Bool :=
  Nat.beq (circuit (natOps (2 ^ 18)) tests (chunkInputs r)) (2 ^ (2 ^ 18) - 1)

end EH

namespace EH
def tests : List Test := [⟨[⟨0, 2, true⟩], 0⟩,
  ⟨[⟨2, 1, true⟩], 0⟩,
  ⟨[⟨1, 1, true⟩], 0⟩,
  ⟨[⟨1, 2, true⟩], 0⟩,
  ⟨[⟨2, 3, true⟩], 0⟩,
  ⟨[⟨1, 0, false⟩, ⟨1, 1, true⟩, ⟨1, 2, false⟩, ⟨1, 3, false⟩], 0⟩,
  ⟨[⟨2, 0, false⟩, ⟨2, 1, true⟩, ⟨2, 2, true⟩, ⟨2, 3, false⟩], 0⟩,
  ⟨[⟨1, 0, true⟩, ⟨1, 1, false⟩, ⟨1, 2, false⟩, ⟨1, 3, false⟩, ⟨2, 0, false⟩, ⟨2, 1, false⟩, ⟨2, 2, false⟩, ⟨2, 3, true⟩], 0⟩,
  ⟨[⟨1, 0, true⟩, ⟨1, 1, true⟩, ⟨1, 2, false⟩, ⟨1, 3, false⟩, ⟨2, 0, true⟩, ⟨2, 1, true⟩, ⟨2, 2, true⟩, ⟨2, 3, false⟩], 0⟩,
  ⟨[⟨2, 0, true⟩], 2⟩,
  ⟨[⟨2, 1, true⟩], 2⟩,
  ⟨[⟨1, 0, true⟩], 2⟩,
  ⟨[⟨0, 0, false⟩, ⟨0, 1, true⟩, ⟨0, 2, true⟩, ⟨0, 3, false⟩], 2⟩,
  ⟨[⟨0, 0, true⟩, ⟨0, 1, false⟩, ⟨0, 2, true⟩, ⟨0, 3, false⟩, ⟨2, 0, false⟩, ⟨2, 1, true⟩, ⟨2, 2, true⟩, ⟨2, 3, false⟩], 2⟩,
  ⟨[⟨0, 0, true⟩, ⟨0, 1, true⟩, ⟨0, 2, false⟩, ⟨0, 3, false⟩, ⟨1, 0, false⟩, ⟨1, 1, false⟩, ⟨1, 2, false⟩, ⟨1, 3, false⟩], 2⟩]
end EH


namespace EH

/-! ## Transfer: bit `j` of the plane computation is the Boolean computation on bit `j` of the inputs -/

structure IsHom {W W' : Type} (o : Ops W) (o' : Ops W') (f : W → W') : Prop where
  band : ∀ a b, f (o.band a b) = o'.band (f a) (f b)
  bor : ∀ a b, f (o.bor a b) = o'.bor (f a) (f b)
  bxor : ∀ a b, f (o.bxor a b) = o'.bxor (f a) (f b)
  one : f o.one = o'.one
  zero : f o.zero = o'.zero

section
variable {W W' : Type} {o : Ops W} {o' : Ops W'} {f : W → W'}

theorem IsHom.bnot' (h : IsHom o o' f) (a : W) : f (bnot o a) = bnot o' (f a) := by
  simp [bnot, h.bxor, h.one]

theorem IsHom.inc' (h : IsHom o o' f) : ∀ (bs : List W) (x : W), (inc o bs x).map f = inc o' (bs.map f) (f x)
  | [], _ => rfl
  | b :: bs, x => by simp [inc, h.bxor, h.band, h.inc' bs]

theorem foldl_hom (g : W → W → W) (g' : W' → W' → W') (hg : ∀ a b, f (g a b) = g' (f a) (f b)) :
    ∀ (xs : List W) (acc : W), f (xs.foldl g acc) = (xs.map f).foldl g' (f acc)
  | [], _ => rfl
  | x :: xs, acc => by simp [List.foldl, foldl_hom g g' hg xs, hg]

theorem IsHom.cnt' (h : IsHom o o' f) (k : Nat) (xs : List W) :
    (cnt o k xs).map f = cnt o' k (xs.map f) := by
  unfold cnt
  suffices H : ∀ acc : List W, (xs.foldl (inc o) acc).map f = (xs.map f).foldl (inc o') (acc.map f) by
    rw [H]; simp [List.map_replicate, h.zero]
  induction xs with
  | nil => intro acc; rfl
  | cons x xs ih => intro acc; simp only [List.foldl, List.map_cons, ih, h.inc']

theorem IsHom.orAll' (h : IsHom o o' f) (xs : List W) : f (orAll o xs) = orAll o' (xs.map f) := by
  unfold orAll; rw [foldl_hom _ _ h.bor, h.zero]

theorem IsHom.xorAll' (h : IsHom o o' f) (xs : List W) : f (xorAll o xs) = xorAll o' (xs.map f) := by
  unfold xorAll; rw [foldl_hom _ _ h.bxor, h.zero]

theorem IsHom.andAll' (h : IsHom o o' f) (xs : List W) : f (andAll o xs) = andAll o' (xs.map f) := by
  unfold andAll; rw [foldl_hom _ _ h.band, h.one]

theorem IsHom.getS' (h : IsHom o o' f) (x : List W) (v : Nat) : f (getS o x v) = getS o' (x.map f) v := by
  unfold getS; rw [← h.zero, List.getD_map]

theorem IsHom.same' (h : IsHom o o' f) (x : List W) (v u : Nat) :
    f (same o x v u) = same o' (x.map f) v u := by
  simp [same, h.bnot', h.bxor, h.getS']

theorem IsHom.stats' (h : IsHom o o' f) (x : List W) (v : Nat) :
    (stats o x v).map (List.map f) = stats o' (x.map f) v := by
  simp only [stats, List.map_cons, List.map_nil, h.cnt', List.map_map, Function.comp_def, h.band, h.same',
    h.orAll']

theorem IsHom.litV' (h : IsHom o o' f) (st : List (List W)) (l : Lit) :
    f (litV o st l) = litV o' (st.map (List.map f)) l := by
  have e1 : (st.map (List.map f)).getD l.s [] = ((st.getD l.s []).map f) := by
    rw [show ([] : List W') = List.map f [] from rfl, List.getD_map]
  unfold litV
  cases l.pol <;> simp only [e1, ← h.zero, List.getD_map, h.bnot', Bool.false_eq_true, if_false, if_true]

theorem IsHom.predV' (h : IsHom o o' f) (st : List (List W)) (t : Test) :
    f (predV o st t) = predV o' (st.map (List.map f)) t := by
  simp [predV, h.andAll', List.map_map, Function.comp_def, h.litV']

theorem IsHom.psL' (h : IsHom o o' f) (sts : List (List (List W))) (t : Test) :
    (psL o sts t).map f = psL o' (sts.map (List.map (List.map f))) t := by
  have e1 : ∀ v, (sts.map (List.map (List.map f))).getD v [] = (sts.getD v []).map (List.map f) := by
    intro v; rw [show ([] : List (List W')) = List.map (List.map f) [] from rfl, List.getD_map]
  simp only [psL, List.map_map, Function.comp_def, h.predV', e1]

theorem IsHom.sideL' (h : IsHom o o' f) (x ps : List W) (pos : Bool) :
    (sideL o x ps pos).map f = sideL o' (x.map f) (ps.map f) pos := by
  unfold sideL
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left; intro v _
  rw [h.band, ← h.zero, List.getD_map]
  cases pos <;> simp [h.getS', h.bnot']

theorem zipWith_hom {W W' : Type} {f : W → W'} (g : W → W → W) (g' : W' → W' → W')
    (hg : ∀ a b, f (g a b) = g' (f a) (f b)) :
    ∀ (a b : List W), (List.zipWith g a b).map f = List.zipWith g' (a.map f) (b.map f)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by simp [List.zipWith, hg, zipWith_hom g g' hg xs ys]

theorem IsHom.testBit'' (h : IsHom o o' f) (x : List W) (sts : List (List (List W))) (t : Test) :
    f (testBit' o x sts t) = testBit' o' (x.map f) (sts.map (List.map (List.map f))) t := by
  unfold testBit'
  split_ifs with hm
  · rw [h.xorAll', h.psL']
  · rw [h.orAll', zipWith_hom _ _ h.bxor, h.cnt', h.cnt', h.sideL', h.sideL', h.psL']

theorem IsHom.circuit' (h : IsHom o o' f) (tests : List Test) (x : List W) :
    f (circuit o tests x) = circuit o' tests (x.map f) := by
  have hs : (List.map (stats o x) (List.range 28)).map (List.map (List.map f))
      = List.map (stats o' (x.map f)) (List.range 28) := by
    simp [List.map_map, Function.comp_def, h.stats']
  have hz : ∀ i, f ((cnt o 5 x).getD i o.zero) = (cnt o' 5 (x.map f)).getD i o'.zero := by
    intro i; rw [← h.cnt', ← h.zero, List.getD_map]
  simp only [circuit, h.bor, h.bnot', h.andAll', h.orAll', List.map_map, Function.comp_def, h.testBit'', hs,
    List.map_cons, List.map_nil, hz]

end

theorem natHom (N j : Nat) (hj : j < N) : IsHom (natOps N) boolOps (fun a => a.testBit j) where
  band a b := Nat.testBit_and a b j
  bor a b := Nat.testBit_or a b j
  bxor a b := Nat.testBit_xor a b j
  one := by simp [natOps, boolOps, hj]
  zero := by simp [natOps, boolOps]

end EH


namespace EH

/-! ## Meaning of the Boolean circuit -/

def toBits : Nat → Nat → List Bool
  | 0, _ => []
  | k+1, n => decide (n % 2 = 1) :: toBits k (n / 2)

theorem inc_toBits : ∀ (k n : Nat) (x : Bool), inc boolOps (toBits k n) x = toBits k (n + x.toNat)
  | 0, _, _ => rfl
  | k+1, n, x => by
    simp only [toBits, inc]
    rw [inc_toBits k]
    congr 1
    · rcases Nat.mod_two_eq_zero_or_one n with h | h <;> cases x <;> simp [boolOps, h] <;> omega
    · congr 1
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> cases x <;> simp [boolOps, h] <;> omega

theorem replicate_false : ∀ k, List.replicate k false = toBits k 0
  | 0 => rfl
  | k+1 => by simp [List.replicate, toBits, replicate_false k]

theorem cnt_bool (k : Nat) (xs : List Bool) : cnt boolOps k xs = toBits k (xs.count true) := by
  unfold cnt
  have H : ∀ m, xs.foldl (inc boolOps) (toBits k m) = toBits k (m + xs.count true) := by
    induction xs with
    | nil => intro m; simp
    | cons x xs ih =>
      intro m; simp only [List.foldl, inc_toBits, ih, List.count_cons]
      congr 1; cases x <;> simp <;> omega
  have h0 : List.replicate k boolOps.zero = toBits k 0 := replicate_false k
  rw [h0, H]; simp

theorem orAll_bool (xs : List Bool) : orAll boolOps xs = xs.any id := by
  unfold orAll
  have H : ∀ acc, xs.foldl boolOps.bor acc = (acc || xs.any id) := by
    induction xs with
    | nil => intro acc; simp
    | cons x xs ih => intro acc; rw [List.foldl_cons, ih]; cases acc <;> cases x <;> simp [boolOps]
  rw [H]; simp [boolOps]

theorem andAll_bool (xs : List Bool) : andAll boolOps xs = xs.all id := by
  unfold andAll
  have H : ∀ acc, xs.foldl boolOps.band acc = (acc && xs.all id) := by
    induction xs with
    | nil => intro acc; simp
    | cons x xs ih => intro acc; rw [List.foldl_cons, ih]; cases acc <;> cases x <;> simp [boolOps]
  rw [H]; simp [boolOps]

theorem xorAll_bool (xs : List Bool) : xorAll boolOps xs = decide (xs.count true % 2 = 1) := by
  unfold xorAll
  have H : ∀ acc : Bool, xs.foldl boolOps.bxor acc = decide ((acc.toNat + xs.count true) % 2 = 1) := by
    induction xs with
    | nil => intro acc; cases acc <;> simp
    | cons x xs ih =>
      intro acc; simp only [List.foldl, ih, List.count_cons]
      cases acc <;> cases x <;> simp [boolOps] <;> omega
  rw [H]; simp [boolOps]

theorem orAll_zip_self (l : List Bool) : orAll boolOps (List.zipWith boolOps.bxor l l) = false := by
  rw [orAll_bool]; induction l with
  | nil => rfl
  | cons a l ih => simpa [List.zipWith, boolOps] using ih

/-! data facts, checked by the kernel -/
theorem nb_lt : ∀ v < 28, ∀ u ∈ nb v, u < 28 := by decide +kernel
theorem tri_lt : ∀ v < 28, ∀ p ∈ triL v, p.1 < 28 ∧ p.2 < 28 := by decide +kernel
theorem d2_lt : ∀ v < 28, ∀ q ∈ d2L v, q.1 < 28 ∧ ∀ u ∈ q.2, u < 28 := by decide +kernel

section
variable (c : Nat → Bool)

/-- same-side degree, triangle and distance-two counts of vertex `v` under the 2-colouring `c` -/
def degC (v : Nat) : Nat := ((nb v).map (fun u => decide (c v = c u))).count true
def triC (v : Nat) : Nat := ((triL v).map (fun p => decide (c v = c p.1) && decide (c v = c p.2))).count true
def d2C (v : Nat) : Nat :=
  ((d2L v).map (fun q => decide (c v = c q.1) && q.2.any (fun u => decide (c v = c u)))).count true

theorem getS_bool (v : Nat) (hv : v < 28) : getS boolOps ((List.range 28).map c) v = c v := by
  simp [getS, List.getD_eq_getElem?_getD, hv, boolOps]

theorem same_bool (v u : Nat) (hv : v < 28) (hu : u < 28) :
    same boolOps ((List.range 28).map c) v u = decide (c v = c u) := by
  simp only [same, bnot, getS_bool c v hv, getS_bool c u hu]
  cases c v <;> cases c u <;> rfl

theorem stats_bool (v : Nat) (hv : v < 28) :
    stats boolOps ((List.range 28).map c) v = [toBits 4 (degC c v), toBits 4 (triC c v), toBits 4 (d2C c v)] := by
  have h1 : (nb v).map (same boolOps ((List.range 28).map c) v) = (nb v).map (fun u => decide (c v = c u)) := by
    apply List.map_congr_left; intro u hu; exact same_bool c v u hv (nb_lt v hv u hu)
  have h2 : (triL v).map (fun p => boolOps.band (same boolOps ((List.range 28).map c) v p.1)
      (same boolOps ((List.range 28).map c) v p.2)) =
      (triL v).map (fun p => decide (c v = c p.1) && decide (c v = c p.2)) := by
    apply List.map_congr_left; intro p hp
    have := tri_lt v hv p hp
    rw [same_bool c v _ hv this.1, same_bool c v _ hv this.2]; rfl
  have h3 : (d2L v).map (fun q => boolOps.band (same boolOps ((List.range 28).map c) v q.1)
      (orAll boolOps (q.2.map (same boolOps ((List.range 28).map c) v)))) =
      (d2L v).map (fun q => decide (c v = c q.1) && q.2.any (fun u => decide (c v = c u))) := by
    apply List.map_congr_left; intro q hq
    have := d2_lt v hv q hq
    have hm : q.2.map (same boolOps ((List.range 28).map c) v) = q.2.map (fun u => decide (c v = c u)) :=
      List.map_congr_left (fun u hu => same_bool c v u hv (this.2 u hu))
    rw [same_bool c v _ hv this.1, orAll_bool, hm, List.any_map]; rfl
  simp only [stats, cnt_bool, degC, triC, d2C, h1, h2, h3]

/-- the vertex predicate of a test, as a function of the three statistics -/
def F (t : Test) (a b p : Nat) : Bool := predV boolOps [toBits 4 a, toBits 4 b, toBits 4 p] t

def gT (t : Test) (v : Nat) : Bool := F t (degC c v) (triC c v) (d2C c v)

theorem psL_bool (t : Test) :
    psL boolOps ((List.range 28).map (stats boolOps ((List.range 28).map c))) t = (List.range 28).map (gT c t) := by
  unfold psL; apply List.map_congr_left; intro v hv
  have hv' : v < 28 := List.mem_range.mp hv
  simp [List.getD_eq_getElem?_getD, hv', stats_bool c v hv', gT, F]

theorem sideL_bool (ps : List Bool) (hps : ps.length = 28) (pos : Bool) :
    sideL boolOps ((List.range 28).map c) ps pos =
      (List.range 28).map (fun v => (if pos then c v else !c v) && ps.getD v false) := by
  unfold sideL; apply List.map_congr_left; intro v hv
  have hv' : v < 28 := List.mem_range.mp hv
  rw [getS_bool c v hv']
  cases pos <;> simp [bnot, boolOps]

end
end EH


namespace EH

/-! ## The witness graph and the invariance argument -/

theorem nb_symm : ∀ u v : Fin 28, v.val ∈ nb u.val → u.val ∈ nb v.val := by decide +kernel
theorem nb_irrefl : ∀ u : Fin 28, u.val ∉ nb u.val := by decide +kernel

/-- The witness: census graph 2659 (Holt–Royle, `alltrans28_k=09.gz`, line 1186). -/
def W : SimpleGraph (Fin 28) where
  Adj u v := v.val ∈ nb u.val
  symm := ⟨fun u v h => nb_symm u v h⟩
  loopless := ⟨fun u h => nb_irrefl u h⟩

instance : DecidableRel W.Adj := fun u v => inferInstanceAs (Decidable (v.val ∈ nb u.val))

theorem nb_nodup : ∀ v < 28, (nb v).Nodup := by decide +kernel
theorem tri_nodup : ∀ v < 28, (triL v).Nodup := by decide +kernel
theorem d2_nodup : ∀ v < 28, ((d2L v).map Prod.fst).Nodup := by decide +kernel
/-- the triangle list recomputed from the neighbour lists -/
def triLc (v : Nat) : List (Nat × Nat) :=
  (nb v).flatMap (fun u => ((nb v).filter (fun w => decide (u < w) && decide (w ∈ nb u))).map (fun w => (u, w)))
theorem triL_eq : ∀ v < 28, triL v = triLc v := by decide +kernel
theorem tri_mem (v u w : Fin 28) : (u.val, w.val) ∈ triL v.val ↔
    (u < w ∧ W.Adj v u ∧ W.Adj v w ∧ W.Adj u w) := by
  rw [triL_eq v.val v.isLt]
  simp only [triLc, List.mem_flatMap, List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
    Prod.mk.injEq, Fin.lt_def]
  constructor
  · rintro ⟨a, ha, b, ⟨hb, hab, hba⟩, rfl, rfl⟩; exact ⟨hab, ha, hb, hba⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨u.val, h2, w.val, ⟨h3, h1, h4⟩, rfl, rfl⟩
/-- the distance-two list recomputed from the neighbour lists -/
def d2Lc (v : Nat) : List Nat :=
  (List.range 28).filter (fun w => decide (w ≠ v) && !decide (w ∈ nb v) && (nb v).any (fun u => decide (w ∈ nb u)))
theorem d2L_eq : ∀ v < 28, (d2L v).map Prod.fst = d2Lc v := by decide +kernel
theorem d2L_snd : ∀ v < 28, ∀ q ∈ d2L v, q.2 = (nb v).filter (fun u => decide (q.1 ∈ nb u)) := by decide +kernel
theorem d2_mem (v w : Fin 28) : w.val ∈ (d2L v.val).map Prod.fst ↔
    (w ≠ v ∧ ¬ W.Adj v w ∧ ∃ u, W.Adj v u ∧ W.Adj w u) := by
  rw [d2L_eq v.val v.isLt]
  simp only [d2Lc, List.mem_filter, List.mem_range, w.isLt, true_and, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, List.any_eq_true, ne_eq, Fin.ext_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, u, hu1, hu2⟩
    exact ⟨h1, h2, ⟨u, nb_lt v.val v.isLt u hu1⟩, hu1, nb_symm _ _ hu2⟩
  · rintro ⟨h1, h2, u, hu1, hu2⟩
    exact ⟨⟨h1, h2⟩, u.val, hu1, nb_symm _ _ hu2⟩
theorem d2_common : ∀ v < 28, ∀ q ∈ d2L v, ∀ u < 28, (u ∈ q.2 ↔ u ∈ nb v ∧ u ∈ nb q.1) := by
  intro v hv q hq u hu
  rw [d2L_snd v hv q hq, List.mem_filter, decide_eq_true_eq]
  have hq1 : q.1 < 28 := by
    have := (d2L_eq v hv) ▸ List.mem_map_of_mem (f := Prod.fst) hq
    simp [d2Lc] at this; exact this.1
  exact ⟨fun h => ⟨h.1, nb_symm ⟨u, hu⟩ ⟨q.1, hq1⟩ h.2⟩, fun h => ⟨h.1, nb_symm ⟨q.1, hq1⟩ ⟨u, hu⟩ h.2⟩⟩

theorem count_map_card {α β : Type} [Fintype α] [DecidableEq β] (e : α → β) (he : Function.Injective e)
    (l : List β) (hl : l.Nodup) (hcov : ∀ b ∈ l, ∃ a, e a = b) (p : β → Bool) :
    (l.map p).count true = (Finset.univ.filter (fun a => e a ∈ l ∧ p (e a) = true)).card := by
  have h1 : (l.map p).count true = (l.filter p).length := by
    rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
    congr 1; apply List.filter_congr; intro x _; simp
  have h2 : (l.filter p).toFinset = (Finset.univ.filter (fun a => e a ∈ l ∧ p (e a) = true)).map ⟨e, he⟩ := by
    ext b
    simp only [List.mem_toFinset, List.mem_filter, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hb, hp⟩; obtain ⟨a, rfl⟩ := hcov b hb; exact ⟨a, ⟨hb, hp⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hp⟩, rfl⟩; exact ⟨ha, hp⟩
  rw [h1, ← List.toFinset_card_of_nodup (hl.filter _), h2, Finset.card_map]

theorem count_range (p : Nat → Bool) :
    ((List.range 28).map p).count true = (Finset.univ.filter (fun v : Fin 28 => p v.val = true)).card := by
  rw [count_map_card Fin.val Fin.val_injective _ List.nodup_range
    (fun b hb => ⟨⟨b, List.mem_range.mp hb⟩, rfl⟩)]
  congr 1; ext v; simp [v.isLt]

section
variable (c : Nat → Bool)

theorem degC_card (v : Fin 28) :
    degC c v.val = (Finset.univ.filter (fun u => W.Adj v u ∧ c v.val = c u.val)).card := by
  unfold degC
  rw [count_map_card Fin.val Fin.val_injective _ (nb_nodup v.val v.isLt)
    (fun b hb => ⟨⟨b, nb_lt v.val v.isLt b hb⟩, rfl⟩)]
  congr 1; ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]; rfl

theorem triC_card (v : Fin 28) :
    triC c v.val = (Finset.univ.filter (fun p : Fin 28 × Fin 28 =>
      p.1 < p.2 ∧ (W.Adj v p.1 ∧ W.Adj v p.2 ∧ W.Adj p.1 p.2 ∧ c v.val = c p.1.val ∧ c v.val = c p.2.val))).card := by
  unfold triC
  have he : Function.Injective (fun p : Fin 28 × Fin 28 => (p.1.val, p.2.val)) := by
    intro a b h; simp only [Prod.mk.injEq] at h; exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  rw [count_map_card _ he _ (tri_nodup v.val v.isLt)
    (fun b hb => ⟨(⟨b.1, (tri_lt v.val v.isLt b hb).1⟩, ⟨b.2, (tri_lt v.val v.isLt b hb).2⟩), rfl⟩)]
  congr 1; ext ⟨u, w⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [tri_mem v u w]
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem d2C_card (v : Fin 28) :
    d2C c v.val = (Finset.univ.filter (fun w : Fin 28 => (w ≠ v ∧ ¬ W.Adj v w ∧ ∃ u, W.Adj v u ∧ W.Adj w u) ∧
      (c v.val = c w.val ∧ ∃ u : Fin 28, W.Adj v u ∧ W.Adj w u ∧ c v.val = c u.val))).card := by
  unfold d2C
  have hl : (d2L v.val).map (fun q => decide (c v.val = c q.1) && q.2.any (fun u => decide (c v.val = c u))) =
      ((d2L v.val).map Prod.fst).map (fun w => decide (c v.val = c w) &&
        decide (∃ u : Fin 28, u.val ∈ nb v.val ∧ u.val ∈ nb w ∧ c v.val = c u.val)) := by
    rw [List.map_map]
    apply List.map_congr_left; intro q hq
    simp only [Function.comp_apply]
    congr 1
    have hlt := d2_lt v.val v.isLt q hq
    have hc := d2_common v.val v.isLt q hq
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨u, hu, he⟩
      exact ⟨⟨u, hlt.2 u hu⟩, ((hc u (hlt.2 u hu)).mp hu).1, ((hc u (hlt.2 u hu)).mp hu).2, he⟩
    · rintro ⟨u, hu1, hu2, he⟩
      exact ⟨u.val, (hc u.val u.isLt).mpr ⟨hu1, hu2⟩, he⟩
  rw [hl, count_map_card Fin.val Fin.val_injective _ (d2_nodup v.val v.isLt)
    (fun b hb => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
      exact ⟨⟨q.1, (d2_lt v.val v.isLt q hq).1⟩, rfl⟩)]
  congr 1; ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, d2_mem, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, ⟨u, hu1, hu2, hu3⟩⟩; exact ⟨h1, h2, ⟨u, hu1, hu2, hu3⟩⟩
  · rintro ⟨h1, h2, ⟨u, hu1, hu2, hu3⟩⟩; exact ⟨h1, h2, ⟨u, hu1, hu2, hu3⟩⟩

theorem two_mul_card_lt (R : Fin 28 → Fin 28 → Prop) [DecidableRel R] (hsymm : ∀ a b, R a b → R b a)
    (hirr : ∀ a, ¬ R a a) :
    (Finset.univ.filter (fun p : Fin 28 × Fin 28 => R p.1 p.2)).card =
      2 * (Finset.univ.filter (fun p : Fin 28 × Fin 28 => p.1 < p.2 ∧ R p.1 p.2)).card := by
  have h1 : Finset.univ.filter (fun p : Fin 28 × Fin 28 => R p.1 p.2) =
      Finset.univ.filter (fun p : Fin 28 × Fin 28 => p.1 < p.2 ∧ R p.1 p.2) ∪
      Finset.univ.filter (fun p : Fin 28 × Fin 28 => p.2 < p.1 ∧ R p.1 p.2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h
      rcases lt_trichotomy p.1 p.2 with h' | h' | h'
      · exact Or.inl ⟨h', h⟩
      · exact absurd (h' ▸ h) (hirr p.2)
      · exact Or.inr ⟨h', h⟩
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
  have h2 : Disjoint (Finset.univ.filter (fun p : Fin 28 × Fin 28 => p.1 < p.2 ∧ R p.1 p.2))
      (Finset.univ.filter (fun p : Fin 28 × Fin 28 => p.2 < p.1 ∧ R p.1 p.2)) := by
    rw [Finset.disjoint_filter]; intro p _ h h'; exact lt_asymm h.1 h'.1
  have h3 : (Finset.univ.filter (fun p : Fin 28 × Fin 28 => p.2 < p.1 ∧ R p.1 p.2)).card =
      (Finset.univ.filter (fun p : Fin 28 × Fin 28 => p.1 < p.2 ∧ R p.1 p.2)).card := by
    apply Finset.card_equiv (Equiv.prodComm _ _)
    intro p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    exact ⟨fun h => ⟨h.1, hsymm _ _ h.2⟩, fun h => ⟨h.1, hsymm _ _ h.2⟩⟩
  rw [h1, Finset.card_union_of_disjoint h2, h3]; ring

end
end EH


namespace EH

section
variable (c : Nat → Bool) (τ : Equiv.Perm (Fin 28))
  (hτc : ∀ v, c (τ v).val = !c v.val)
  (hτa : ∀ u w, c u.val = c w.val → (W.Adj (τ u) (τ w) ↔ W.Adj u w))
include hτc

theorem same_iff (u w : Fin 28) : c (τ u).val = c (τ w).val ↔ c u.val = c w.val := by
  rw [hτc, hτc]; cases c u.val <;> cases c w.val <;> simp

include hτa

theorem degC_inv (v : Fin 28) : degC c (τ v).val = degC c v.val := by
  rw [degC_card, degC_card]; symm
  apply Finset.card_equiv τ
  intro u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨(hτa v u h2).mpr h1, (same_iff c τ hτc v u).mpr h2⟩
  · rintro ⟨h1, h2⟩
    have h2' := (same_iff c τ hτc v u).mp h2
    exact ⟨(hτa v u h2').mp h1, h2'⟩

/-- ordered same-side triangle pairs at `v` -/
abbrev R3 (v a b : Fin 28) : Prop := W.Adj v a ∧ W.Adj v b ∧ W.Adj a b ∧ c v.val = c a.val ∧ c v.val = c b.val

omit hτc hτa in
theorem triC_eq (v : Fin 28) :
    2 * triC c v.val = (Finset.univ.filter (fun p : Fin 28 × Fin 28 => R3 c v p.1 p.2)).card := by
  rw [triC_card]
  have := two_mul_card_lt (fun a b => R3 c v a b)
    (fun a b h => ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.2, h.2.2.2.1⟩) (fun a h => W.loopless.irrefl a h.2.2.1)
  rw [this]

theorem triC_inv (v : Fin 28) : triC c (τ v).val = triC c v.val := by
  have h1 := triC_eq c (τ v)
  have h2 := triC_eq c v
  have h3 : (Finset.univ.filter (fun p : Fin 28 × Fin 28 => R3 c v p.1 p.2)).card =
      (Finset.univ.filter (fun p : Fin 28 × Fin 28 => R3 c (τ v) p.1 p.2)).card := by
    apply Finset.card_equiv (Equiv.prodCongr τ τ)
    intro p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, R3]
    constructor
    · rintro ⟨a1, a2, a3, e1, e2⟩
      exact ⟨(hτa _ _ e1).mpr a1, (hτa _ _ e2).mpr a2, (hτa _ _ (e1.symm.trans e2)).mpr a3,
        (same_iff c τ hτc _ _).mpr e1, (same_iff c τ hτc _ _).mpr e2⟩
    · rintro ⟨a1, a2, a3, e1, e2⟩
      have e1' := (same_iff c τ hτc _ _).mp e1
      have e2' := (same_iff c τ hτc _ _).mp e2
      exact ⟨(hτa _ _ e1').mp a1, (hτa _ _ e2').mp a2, (hτa _ _ (e1'.symm.trans e2')).mp a3, e1', e2'⟩
  omega

omit hτc hτa in
theorem d2C_card' (v : Fin 28) :
    d2C c v.val = (Finset.univ.filter (fun w : Fin 28 => w ≠ v ∧ ¬ W.Adj v w ∧ c v.val = c w.val ∧
      ∃ u : Fin 28, W.Adj v u ∧ W.Adj w u ∧ c v.val = c u.val)).card := by
  rw [d2C_card]; congr 1; ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨h1, h2, _⟩, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, ⟨u, hu1, hu2, hu3⟩⟩; exact ⟨⟨h1, h2, u, hu1, hu2⟩, h3, u, hu1, hu2, hu3⟩

theorem d2C_inv (v : Fin 28) : d2C c (τ v).val = d2C c v.val := by
  rw [d2C_card', d2C_card']; symm
  apply Finset.card_equiv τ
  intro w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2, h3, ⟨u, hu1, hu2, hu3⟩⟩
    refine ⟨fun h => h1 (τ.injective h), fun h => h2 ((hτa _ _ h3).mp h), (same_iff c τ hτc _ _).mpr h3,
      τ u, (hτa _ _ hu3).mpr hu1, (hτa _ _ (h3.symm.trans hu3)).mpr hu2, (same_iff c τ hτc _ _).mpr hu3⟩
  · rintro ⟨h1, h2, h3, ⟨u, hu1, hu2, hu3⟩⟩
    have h3' := (same_iff c τ hτc _ _).mp h3
    obtain ⟨u', rfl⟩ := τ.surjective u
    have hu3' := (same_iff c τ hτc _ _).mp hu3
    exact ⟨fun h => h1 (h ▸ rfl), fun h => h2 ((hτa _ _ h3').mpr h), h3',
      u', (hτa _ _ hu3').mp hu1, (hτa _ _ (h3'.symm.trans hu3')).mp hu2, hu3'⟩

theorem gT_inv (t : Test) (v : Fin 28) : gT c t (τ v).val = gT c t v.val := by
  unfold gT
  rw [degC_inv c τ hτc hτa, triC_inv c τ hτc hτa, d2C_inv c τ hτc hτa]

omit hτa in
theorem sides_eq (g : Fin 28 → Bool) (hg : ∀ v, g (τ v) = g v) :
    (Finset.univ.filter (fun v : Fin 28 => c v.val = true ∧ g v = true)).card =
      (Finset.univ.filter (fun v : Fin 28 => c v.val = false ∧ g v = true)).card := by
  apply Finset.card_equiv τ
  intro v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hτc, hg]
  cases c v.val <;> simp

omit hτc hτa in
theorem total_split (g : Fin 28 → Bool) :
    (Finset.univ.filter (fun v : Fin 28 => g v = true)).card =
      (Finset.univ.filter (fun v : Fin 28 => c v.val = true ∧ g v = true)).card +
      (Finset.univ.filter (fun v : Fin 28 => c v.val = false ∧ g v = true)).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; cases c v.val <;> simp
  · rw [Finset.disjoint_filter]; intro v _ h h'; rw [h.1] at h'; exact Bool.noConfusion h'.1

theorem test_false (t : Test) :
    testBit' boolOps ((List.range 28).map c) ((List.range 28).map (stats boolOps ((List.range 28).map c))) t
      = false := by
  have hps := psL_bool c t
  have hlen : ((List.range 28).map (gT c t)).length = 28 := by simp
  have hget : ∀ v < 28, ((List.range 28).map (gT c t)).getD v false = gT c t v := by
    intro v hv; simp [List.getD_eq_getElem?_getD, hv]
  have hside := sides_eq c τ hτc (fun v => gT c t v.val) (gT_inv c τ hτc hτa t)
  unfold testBit'
  rw [hps]
  split_ifs with hm
  · rw [xorAll_bool, count_range, total_split c (fun v : Fin 28 => gT c t v.val), ← hside]
    simp only [decide_eq_false_iff_not]; omega
  · rw [sideL_bool c _ hlen, sideL_bool c _ hlen, cnt_bool, cnt_bool]
    have e1 : ((List.range 28).map (fun v => (if true = true then c v else !c v) &&
        ((List.range 28).map (gT c t)).getD v false)).count true =
        (Finset.univ.filter (fun v : Fin 28 => c v.val = true ∧ gT c t v.val = true)).card := by
      rw [count_range]; congr 1; ext v; simp [hget v.val v.isLt]
    have e2 : ((List.range 28).map (fun v => (if false = true then c v else !c v) &&
        ((List.range 28).map (gT c t)).getD v false)).count true =
        (Finset.univ.filter (fun v : Fin 28 => c v.val = false ∧ gT c t v.val = true)).card := by
      rw [count_range]; congr 1; ext v; simp [hget v.val v.isLt]
    rw [e1, e2, hside]; exact orAll_zip_self _

omit hτa in
theorem count14 : ((List.range 28).map c).count true = 14 := by
  rw [count_range]
  have h1 := sides_eq c τ hτc (fun _ => true) (fun _ => rfl)
  simp only [and_true] at h1
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 28)))
    (fun v : Fin 28 => c v.val = true)
  simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at h2
  omega

theorem circuit_false (tests : List Test) : circuit boolOps tests ((List.range 28).map c) = false := by
  unfold circuit
  simp only []
  rw [cnt_bool, count14 c τ hτc]
  have : ∀ t ∈ tests, testBit' boolOps ((List.range 28).map c)
      ((List.range 28).map (stats boolOps ((List.range 28).map c))) t = false :=
    fun t _ => test_false c τ hτc hτa t
  rw [orAll_bool, List.map_congr_left this]
  simp [andAll, toBits, bnot, boolOps]

end
end EH


namespace EH

/-! ## Bit planes enumerate every 2-colouring with vertex 0 coloured `true` -/

theorem planes_length : ∀ K, (planes K).length = K
  | 0 => rfl
  | K+1 => by simp [planes, planes_length K]

theorem testBit_low (K r i : Nat) (hi : i < K) (hr : r < 2 ^ K) : (2 ^ K + r).testBit i = r.testBit i :=
  Nat.testBit_two_pow_add_gt hi r

theorem planes_bit : ∀ K i, i < K → ∀ j, ((planes K).getD i 0).testBit j = (decide (j < 2 ^ K) && j.testBit i)
  | 0, i, hi, _ => absurd hi (Nat.not_lt_zero _)
  | K+1, i, hi, j => by
    have hlen := planes_length K
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have hg : (planes (K+1)).getD i 0 =
          ((planes K).getD i 0) ||| (((planes K).getD i 0) <<< (2 ^ K)) := by
        have hi' : i < (planes K).length := by rw [hlen]; exact hi
        simp only [planes]
        rw [List.getD_append _ _ _ _ (by simpa using hi')]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi', Option.map_some,
          Option.getD_some]
        rfl
      rw [hg, Nat.testBit_or, Nat.testBit_shiftLeft, planes_bit K i hi, planes_bit K i hi]
      by_cases hj : j < 2 ^ K
      · have : ¬ (j ≥ 2 ^ K) := by omega
        simp [hj, this, show j < 2 ^ (K+1) by rw [Nat.pow_succ]; omega]
      · obtain ⟨r, rfl⟩ : ∃ r, j = 2 ^ K + r := ⟨j - 2 ^ K, by omega⟩
        have e1 : 2 ^ K + r - 2 ^ K = r := by omega
        rw [e1]
        by_cases hr : r < 2 ^ K
        · simp [hj, hr, testBit_low K r i hi hr, show 2 ^ K + r < 2 ^ (K+1) by rw [Nat.pow_succ]; omega]
        · simp [hj, hr, show ¬ (2 ^ K + r < 2 ^ (K+1)) by rw [Nat.pow_succ]; omega]
    · have hg : (planes (i+1)).getD i 0 = (2 ^ (2 ^ i) - 1) <<< (2 ^ i) := by
        simp only [planes]
        rw [List.getD_append_right _ _ _ _ (by simp [hlen])]
        simp [hlen]
      rw [hg, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
      by_cases hj : j < 2 ^ i
      · simp [hj, Nat.testBit_lt_two_pow hj, show ¬ (j ≥ 2 ^ i) by omega]
      · obtain ⟨r, rfl⟩ : ∃ r, j = 2 ^ i + r := ⟨j - 2 ^ i, by omega⟩
        have e1 : 2 ^ i + r - 2 ^ i = r := by omega
        rw [e1, Nat.testBit_two_pow_add_eq]
        by_cases hr : r < 2 ^ i
        · simp [hr, Nat.testBit_lt_two_pow hr, show 2 ^ i + r < 2 ^ (i+1) by rw [Nat.pow_succ]; omega]
        · simp [hr, show ¬ (2 ^ i + r < 2 ^ (i+1)) by rw [Nat.pow_succ]; omega]

theorem chunkInputs_length (r : Nat) : (chunkInputs r).length = 28 := by
  simp [chunkInputs, planes_length]

theorem chunk_bit (r : Nat) (v : Nat) (hv : v < 28) (j : Nat) (hj : j < 2 ^ 18) :
    ((chunkInputs r).getD v 0).testBit j =
      (if v = 0 then true else if v ≤ 9 then r.testBit (v - 1) else j.testBit (v - 10)) := by
  have hj' : j < 262144 := by simpa using hj
  unfold chunkInputs
  by_cases h10 : v < 10
  · rw [List.getD_append _ _ _ _ (by simpa using h10)]
    rcases Nat.eq_zero_or_pos v with rfl | hv0
    · simp [hj']
    · obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
      rw [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.getD_some, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel,
        show w + 1 ≤ 9 by omega, if_true]
      split_ifs with hc <;> simp [hc, hj']
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_cons, List.length_map, List.length_range]
    rw [planes_bit 18 (v - 10) (by omega)]
    simp [hj', show v ≠ 0 by omega, show ¬ (v ≤ 9) by omega, show v - (9 + 1) = v - 10 by omega]

/-- little-endian bits to a number -/
def bitsToNat : List Bool → Nat
  | [] => 0
  | b :: bs => Nat.bit b (bitsToNat bs)

theorem bitsToNat_testBit : ∀ (l : List Bool) (i : Nat), (bitsToNat l).testBit i = l.getD i false
  | [], i => by simp [bitsToNat]
  | b :: bs, 0 => by simp [bitsToNat, Nat.testBit_bit_zero]
  | b :: bs, i+1 => by simp [bitsToNat, Nat.testBit_bit_succ, bitsToNat_testBit bs i]

theorem bitsToNat_lt : ∀ (l : List Bool), bitsToNat l < 2 ^ l.length
  | [] => by simp [bitsToNat]
  | b :: bs => by
    have := bitsToNat_lt bs
    simp only [bitsToNat, Nat.bit_val, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

/-- the colours of the neighbours 1..9 of vertex 0, as a 9-bit number -/
def pattern (χ : Nat → Bool) : Nat := bitsToNat ((List.range 9).map (fun i => χ (i + 1)))

/-- every colouring with `χ 0 = true` whose pattern is a listed representative is checked by one chunk -/
theorem all_bool (reps : List Nat) (tests : List Test) (hall : ∀ r ∈ reps, checkChunk tests r = true)
    (χ : Nat → Bool) (h0 : χ 0 = true) (hrep : pattern χ ∈ reps) :
    circuit boolOps tests ((List.range 28).map χ) = true := by
  let lj := (List.range 18).map (fun i => χ (10 + i))
  have hj : bitsToNat lj < 2 ^ 18 := by simpa [lj] using bitsToNat_lt lj
  have hchk := hall _ hrep
  unfold checkChunk at hchk
  have heq := Nat.eq_of_beq_eq_true hchk
  have hbit : (circuit (natOps (2 ^ 18)) tests (chunkInputs (pattern χ))).testBit (bitsToNat lj) = true := by
    rw [heq, Nat.testBit_two_pow_sub_one]; simpa using hj
  rw [(natHom (2 ^ 18) _ hj).circuit'] at hbit
  convert hbit using 2
  apply List.ext_getElem
  · simp [chunkInputs_length]
  · intro v h1 h2
    have hv : v < 28 := by simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    rw [← List.getD_eq_getElem _ 0, chunk_bit _ v hv _ hj, pattern, bitsToNat_testBit, bitsToNat_testBit]
    split_ifs with ha hb
    · subst ha; exact h0
    · simp [List.getD_eq_getElem?_getD, show v - 1 < 9 by omega, show v - 1 + 1 = v by omega]
    · simp [lj, List.getD_eq_getElem?_getD, show v - 10 < 18 by omega, show 10 + (v - 10) = v by omega]

end EH


namespace EH

/-! ## The witness is connected and vertex-transitive -/

def gensD : List (List Nat × List Nat) := [([0,1,3,2,5,4,7,6,9,8,11,10,12,14,13,16,15,18,17,20,19,22,21,23,25,24,27,26],[0,1,3,2,5,4,7,6,9,8,11,10,12,14,13,16,15,18,17,20,19,22,21,23,25,24,27,26]),([0,2,1,8,4,7,9,5,3,6,15,18,14,16,12,10,13,17,11,27,25,26,22,24,23,20,21,19],[0,2,1,8,4,7,9,5,3,6,15,18,14,16,12,10,13,17,11,27,25,26,22,24,23,20,21,19]),([1,0,3,2,10,11,20,19,21,22,4,5,23,13,14,24,25,18,17,7,6,8,9,12,15,16,26,27],[1,0,3,2,10,11,20,19,21,22,4,5,23,13,14,24,25,18,17,7,6,8,9,12,15,16,26,27])]
def wordsD : List (List Nat) := [[],[2],[1,2],[0,1,2],[0,1,0,1,0,1,0,1,2],[1,0,1,0,1,0,1,2],[1,0,1,0,1,2],[0,1,0,1,0,1,2],[1,0,1,2],[0,1,0,1,2],[2,0,1,0,1,0,1,0,1,2],[2,1,0,1,0,1,0,1,2],[2,1,0,1,2,1,0,1,0,1,2],[1,2,1,2,1,0,1,0,1,2],[0,1,2,1,2,1,0,1,0,1,2],[2,0,1,2,1,0,1,0,1,2],[2,1,2,1,0,1,0,1,2],[0,1,2,1,0,1,0,1,0,1,2],[1,2,1,0,1,0,1,0,1,2],[2,0,1,0,1,0,1,2],[2,1,0,1,0,1,2],[2,1,0,1,2],[2,0,1,0,1,2],[1,0,1,2,1,0,1,0,1,2],[0,1,2,1,0,1,0,1,2],[1,2,1,0,1,0,1,2],[1,2,1,0,1,2],[0,1,2,1,0,1,2]]

/-- a permutation table `p` with inverse table `q` that preserves adjacency -/
def goodPerm (p q : List Nat) : Bool :=
  (List.range 28).all (fun i => decide (p.getD i 0 < 28) && decide (q.getD i 0 < 28) &&
    q.getD (p.getD i 0) 0 == i && p.getD (q.getD i 0) 0 == i) &&
  (List.range 28).all (fun a => (List.range 28).all (fun b =>
    decide (b ∈ nb a) == decide (p.getD b 0 ∈ nb (p.getD a 0))))

theorem goodPerm_spec {p q : List Nat} (h : goodPerm p q = true) :
    (∀ i < 28, p.getD i 0 < 28 ∧ q.getD i 0 < 28 ∧ q.getD (p.getD i 0) 0 = i ∧ p.getD (q.getD i 0) 0 = i) ∧
    (∀ a < 28, ∀ b < 28, (b ∈ nb a ↔ p.getD b 0 ∈ nb (p.getD a 0))) := by
  simp only [goodPerm, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq] at h
  refine ⟨fun i hi => ?_, fun a ha b hb => ?_⟩
  · obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h.1 i hi; exact ⟨h1, h2, h3, h4⟩
  · exact decide_eq_decide.mp (h.2 a ha b hb)

/-- the automorphism given by a good table -/
def autOf (p q : List Nat) (h : goodPerm p q = true) : W ≃g W where
  toFun i := ⟨p.getD i.val 0, ((goodPerm_spec h).1 i.val i.isLt).1⟩
  invFun i := ⟨q.getD i.val 0, ((goodPerm_spec h).1 i.val i.isLt).2.1⟩
  left_inv i := Fin.ext ((goodPerm_spec h).1 i.val i.isLt).2.2.1
  right_inv i := Fin.ext ((goodPerm_spec h).1 i.val i.isLt).2.2.2
  map_rel_iff' {a b} := ((goodPerm_spec h).2 a.val a.isLt b.val b.isLt).symm

theorem gens_good : ∀ i < 3, goodPerm (gensD.getD i ([], [])).1 (gensD.getD i ([], [])).2 = true := by
  decide +kernel

/-- generator `i` of the automorphism group (identity if out of range) -/
def autGen (i : Nat) : W ≃g W := if h : i < 3 then autOf _ _ (gens_good i h) else RelIso.refl _

def autWord : List Nat → W ≃g W
  | [] => RelIso.refl _
  | i :: w => (autWord w).trans (autGen i)

def applyGen (i x : Nat) : Nat := if i < 3 then (gensD.getD i ([], [])).1.getD x 0 else x
def applyWord : List Nat → Nat → Nat
  | [], x => x
  | i :: w, x => applyGen i (applyWord w x)

theorem autGen_val (i : Nat) (x : Fin 28) : (autGen i x).val = applyGen i x.val := by
  unfold autGen applyGen; split_ifs <;> rfl

theorem autWord_val : ∀ (w : List Nat) (x : Fin 28), (autWord w x).val = applyWord w x.val
  | [], _ => rfl
  | i :: w, x => by
    simp only [autWord, applyWord, RelIso.trans_apply]
    rw [autGen_val, autWord_val w]

theorem words_ok : ∀ v < 28, applyWord (wordsD.getD v []) 0 = v := by decide +kernel

theorem W_vt : ∀ u v : Fin 28, ∃ φ : W ≃g W, φ u = v := by
  intro u v
  let φu := autWord (wordsD.getD u.val [])
  let φv := autWord (wordsD.getD v.val [])
  refine ⟨φu.symm.trans φv, ?_⟩
  have hu : φu 0 = u := Fin.ext ((autWord_val _ 0).trans (words_ok u.val u.isLt))
  have hv : φv 0 = v := Fin.ext ((autWord_val _ 0).trans (words_ok v.val v.isLt))
  rw [RelIso.trans_apply, ← hu, RelIso.symm_apply_apply, hv]

theorem W_near : ∀ v : Fin 28, v = 0 ∨ W.Adj 0 v ∨ ∃ w, W.Adj 0 w ∧ W.Adj w v := by decide +kernel

theorem W_connected : W.Connected := by
  have h0 : ∀ v : Fin 28, W.Reachable 0 v := by
    intro v
    rcases W_near v with rfl | h | ⟨w, h1, h2⟩
    · exact SimpleGraph.Reachable.refl _
    · exact h.reachable
    · exact h1.reachable.trans h2.reachable
  exact ⟨fun u v => (h0 u).symm.trans (h0 v)⟩

/-! ## From an equal-halves split to a side-swapping permutation -/

section
variable (A : Set (Fin 28)) (φ : W.induce A ≃g W.induce Aᶜ)

open Classical in
noncomputable def swapFun (v : Fin 28) : Fin 28 :=
  if h : v ∈ A then (φ ⟨v, h⟩).val else (φ.symm ⟨v, h⟩).val

theorem swapFun_mem (v : Fin 28) : swapFun A φ v ∈ A ↔ v ∉ A := by
  unfold swapFun
  by_cases h : v ∈ A
  · simp only [h, dite_true, not_true_eq_false, iff_false]; exact (φ ⟨v, h⟩).property
  · simp only [h, dite_false, not_false_eq_true, iff_true]; exact (φ.symm ⟨v, h⟩).property

theorem swapFun_invol : Function.Involutive (swapFun A φ) := by
  intro v
  by_cases h : v ∈ A
  · have h' : swapFun A φ v ∉ A := fun h'' => ((swapFun_mem A φ v).mp h'') h
    have e : swapFun A φ v = (φ ⟨v, h⟩).val := by simp [swapFun, h]
    conv_lhs => rw [swapFun, dif_neg h']
    simp only [e, Subtype.coe_eta, RelIso.symm_apply_apply]
  · have h' : swapFun A φ v ∈ A := (swapFun_mem A φ v).mpr h
    have e : swapFun A φ v = (φ.symm ⟨v, h⟩).val := by simp [swapFun, h]
    conv_lhs => rw [swapFun, dif_pos h']
    simp only [e, Subtype.coe_eta, RelIso.apply_symm_apply]

theorem swapFun_adj (u w : Fin 28) (h : (u ∈ A ↔ w ∈ A)) :
    W.Adj (swapFun A φ u) (swapFun A φ w) ↔ W.Adj u w := by
  by_cases hu : u ∈ A
  · have hw := h.mp hu
    simp only [swapFun, hu, hw, dite_true]
    exact (φ.map_adj_iff (v := ⟨u, hu⟩) (w := ⟨w, hw⟩))
  · have hw : w ∉ A := fun hw => hu (h.mpr hw)
    simp only [swapFun, hu, hw, dite_false]
    exact (φ.symm.map_adj_iff (v := ⟨u, hu⟩) (w := ⟨w, hw⟩))

end

def stabWordsD : List (List Nat) := [[],[0],[1],[1,0],[0,1],[0,1,0],[1,0,1],[1,0,1,0],[0,1,0,1],[0,1,0,1,0],[1,0,1,0,1],[1,0,1,0,1,0],[0,1,0,1,0,1],[0,1,0,1,0,1,0],[1,0,1,0,1,0,1],[1,0,1,0,1,0,1,0],[0,1,0,1,0,1,0,1],[0,1,0,1,0,1,0,1,0]]
def repsD : List Nat := [0,1,3,6,7,9,11,12,13,14,15,27,30,31,35,38,39,43,46,47,51,55,63,97,99,103,107,108,109,110,111,120,121,122,123,126,127,167,175,183,191,237,239,247,255,511]
def covD : List Nat := [0,0,2,0,4,1,0,0,16,0,2,0,0,0,0,0,14,1,1,1,4,1,1,1,15,15,16,0,14,1,0,0,10,5,6,0,5,5,0,0,14,15,7,0,14,14,0,0,11,15,14,0,11,4,14,0,14,15,14,14,14,14,14,0,12,3,3,3,8,1,1,1,13,17,13,2,16,1,16,1,16,17,16,16,9,1,1,1,16,17,16,16,16,16,16,1,6,0,6,0,8,1,6,0,13,13,13,0,0,0,0,0,11,11,1,1,11,1,1,1,0,0,0,0,1,1,0,0,6,2,3,2,9,4,6,16,2,2,2,2,4,4,6,16,10,3,3,3,11,4,9,17,17,17,3,3,17,4,16,17,7,10,6,12,11,4,6,0,7,5,7,13,7,5,6,0,10,10,8,3,11,10,8,0,4,4,7,3,4,4,14,0,6,3,3,3,9,11,6,16,12,2,3,2,16,17,6,16,11,3,3,3,9,11,9,16,17,17,17,3,16,17,16,16,6,10,6,12,8,11,6,6,7,12,7,13,6,0,6,0,11,10,9,3,11,11,8,0,11,17,7,3,11,11,7,0,8,4,7,2,5,4,8,14,12,5,13,2,5,5,7,15,4,4,2,2,4,4,8,14,15,15,15,2,5,5,14,15,8,5,7,13,5,5,8,14,13,5,7,13,5,5,7,14,10,4,14,15,5,4,8,14,15,15,14,15,15,5,14,14,9,12,13,2,8,10,8,1,12,12,13,12,6,5,6,1,9,3,9,3,9,11,8,1,2,2,2,2,9,5,16,1,8,12,6,13,8,10,8,8,13,12,13,13,7,5,6,1,9,10,8,1,9,11,8,1,13,15,13,13,9,5,9,1,7,2,7,2,9,4,6,2,12,2,12,2,5,4,7,2,10,4,3,2,10,4,9,4,2,2,2,2,4,4,2,2,7,10,7,12,8,4,6,4,7,5,7,12,5,5,7,4,10,10,8,10,10,4,8,4,5,4,7,3,5,4,7,4,9,12,6,2,9,10,8,2,12,12,12,2,6,12,6,2,9,3,3,3,9,10,9,2,3,2,3,2,9,5,9,2,7,10,6,12,8,10,6,6,13,12,7,12,7,5,6,6,11,10,9,3,9,10,8,8,11,11,7,3,9,5,7,0]

/-- the pattern of the colouring `n ↦ χ (g n)` for the stabiliser element given by word `w` -/
def permPat (w : List Nat) (P : Nat) : Nat :=
  bitsToNat ((List.range 9).map (fun i => P.testBit (applyWord w (i + 1) - 1)))

theorem stab_ok : ∀ w ∈ stabWordsD, applyWord w 0 = 0 ∧ ∀ i < 9, 1 ≤ applyWord w (i + 1) ∧ applyWord w (i + 1) ≤ 9 := by
  decide +kernel

theorem coverage_data : ∀ P < 512, covD.getD P 0 < 18 ∧ permPat (stabWordsD.getD (covD.getD P 0) []) P ∈ repsD := by
  decide +kernel

theorem coverage (P : Nat) (hP : P < 512) : ∃ w ∈ stabWordsD, permPat w P ∈ repsD := by
  obtain ⟨h1, h2⟩ := coverage_data P hP
  refine ⟨_, ?_, h2⟩
  rw [List.getD_eq_getElem _ _ (by simpa [stabWordsD] using h1)]
  exact List.getElem_mem _

open Classical in
theorem no_split (tests : List Test) (hall : ∀ r ∈ repsD, checkChunk tests r = true)
    (A : Set (Fin 28)) (φ : W.induce A ≃g W.induce Aᶜ) : False := by
  let τ : Equiv.Perm (Fin 28) := (swapFun_invol A φ).toPerm _
  let c : Nat → Bool := fun n => if h : n < 28 then (decide ((⟨n, h⟩ : Fin 28) ∈ A) == decide ((0 : Fin 28) ∈ A))
    else false
  have hcv : ∀ v : Fin 28, c v.val = (decide (v ∈ A) == decide ((0 : Fin 28) ∈ A)) := by
    intro v; simp [c, v.isLt]
  have hτc : ∀ v, c (τ v).val = !c v.val := by
    intro v
    rw [hcv, hcv]
    have := swapFun_mem A φ v
    show (decide (swapFun A φ v ∈ A) == _) = !(decide (v ∈ A) == _)
    by_cases h1 : v ∈ A <;> by_cases h2 : (0 : Fin 28) ∈ A <;> simp_all
  have hτa : ∀ u w, c u.val = c w.val → (W.Adj (τ u) (τ w) ↔ W.Adj u w) := by
    intro u w h
    apply swapFun_adj
    rw [hcv, hcv] at h
    by_cases h1 : u ∈ A <;> by_cases h2 : w ∈ A <;> by_cases h3 : (0 : Fin 28) ∈ A <;> simp_all
  have h0 : c 0 = true := by simp [c]
  -- move the pattern on the neighbours of 0 to a representative
  have hP : pattern c < 512 := by
    have := bitsToNat_lt ((List.range 9).map (fun i => c (i + 1))); simpa [pattern] using this
  obtain ⟨w, hw, hrep⟩ := coverage _ hP
  obtain ⟨hw0, hw9⟩ := stab_ok w hw
  let g := autWord w
  have hg : ∀ v : Fin 28, (g v).val = applyWord w v.val := autWord_val w
  let c' : Nat → Bool := fun n => if h : n < 28 then c (g ⟨n, h⟩).val else false
  have hc' : ∀ v : Fin 28, c' v.val = c (g v).val := by intro v; simp [c', v.isLt]
  let τ' : Equiv.Perm (Fin 28) := (g.toEquiv.trans τ).trans g.symm.toEquiv
  have hτ' : ∀ v, τ' v = g.symm (τ (g v)) := fun v => rfl
  have hτc' : ∀ v, c' (τ' v).val = !c' v.val := by
    intro v; rw [hc', hc', hτ', RelIso.apply_symm_apply, hτc]
  have hτa' : ∀ u w, c' u.val = c' w.val → (W.Adj (τ' u) (τ' w) ↔ W.Adj u w) := by
    intro u w h
    rw [hc', hc'] at h
    rw [hτ', hτ', g.symm.map_adj_iff, hτa _ _ h, g.map_adj_iff]
  have h0' : c' 0 = true := by
    have := hc' 0
    have e : g 0 = 0 := Fin.ext ((hg 0).trans hw0)
    simp only [Fin.val_zero, e] at this
    rw [this]; exact h0
  have hrep' : pattern c' ∈ repsD := by
    have e : pattern c' = permPat w (pattern c) := by
      unfold pattern permPat; congr 1
      apply List.map_congr_left; intro i hi
      have hi' : i < 9 := List.mem_range.mp hi
      obtain ⟨l1, l2⟩ := hw9 i hi'
      rw [bitsToNat_testBit, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.getD_some, show applyWord w (i + 1) - 1 + 1 = applyWord w (i + 1) by omega]
      have := hc' ⟨i + 1, by omega⟩
      rw [hg] at this
      exact this
    rw [e]; exact hrep
  have hT := all_bool repsD tests hall c' h0' hrep'
  have hF := circuit_false c' τ' hτc' hτa' tests
  rw [hT] at hF
  exact Bool.noConfusion hF

end EH

namespace EH

/-! ## The kernel computation: one chunk of 2^18 colourings per representative -/

theorem chunk_0 : checkChunk tests 0 = true := by decide +kernel
theorem chunk_1 : checkChunk tests 1 = true := by decide +kernel
theorem chunk_3 : checkChunk tests 3 = true := by decide +kernel
theorem chunk_6 : checkChunk tests 6 = true := by decide +kernel
theorem chunk_7 : checkChunk tests 7 = true := by decide +kernel
theorem chunk_9 : checkChunk tests 9 = true := by decide +kernel
theorem chunk_11 : checkChunk tests 11 = true := by decide +kernel
theorem chunk_12 : checkChunk tests 12 = true := by decide +kernel
theorem chunk_13 : checkChunk tests 13 = true := by decide +kernel
theorem chunk_14 : checkChunk tests 14 = true := by decide +kernel
theorem chunk_15 : checkChunk tests 15 = true := by decide +kernel
theorem chunk_27 : checkChunk tests 27 = true := by decide +kernel
theorem chunk_30 : checkChunk tests 30 = true := by decide +kernel
theorem chunk_31 : checkChunk tests 31 = true := by decide +kernel
theorem chunk_35 : checkChunk tests 35 = true := by decide +kernel
theorem chunk_38 : checkChunk tests 38 = true := by decide +kernel
theorem chunk_39 : checkChunk tests 39 = true := by decide +kernel
theorem chunk_43 : checkChunk tests 43 = true := by decide +kernel
theorem chunk_46 : checkChunk tests 46 = true := by decide +kernel
theorem chunk_47 : checkChunk tests 47 = true := by decide +kernel
theorem chunk_51 : checkChunk tests 51 = true := by decide +kernel
theorem chunk_55 : checkChunk tests 55 = true := by decide +kernel
theorem chunk_63 : checkChunk tests 63 = true := by decide +kernel
theorem chunk_97 : checkChunk tests 97 = true := by decide +kernel
theorem chunk_99 : checkChunk tests 99 = true := by decide +kernel
theorem chunk_103 : checkChunk tests 103 = true := by decide +kernel
theorem chunk_107 : checkChunk tests 107 = true := by decide +kernel
theorem chunk_108 : checkChunk tests 108 = true := by decide +kernel
theorem chunk_109 : checkChunk tests 109 = true := by decide +kernel
theorem chunk_110 : checkChunk tests 110 = true := by decide +kernel
theorem chunk_111 : checkChunk tests 111 = true := by decide +kernel
theorem chunk_120 : checkChunk tests 120 = true := by decide +kernel
theorem chunk_121 : checkChunk tests 121 = true := by decide +kernel
theorem chunk_122 : checkChunk tests 122 = true := by decide +kernel
theorem chunk_123 : checkChunk tests 123 = true := by decide +kernel
theorem chunk_126 : checkChunk tests 126 = true := by decide +kernel
theorem chunk_127 : checkChunk tests 127 = true := by decide +kernel
theorem chunk_167 : checkChunk tests 167 = true := by decide +kernel
theorem chunk_175 : checkChunk tests 175 = true := by decide +kernel
theorem chunk_183 : checkChunk tests 183 = true := by decide +kernel
theorem chunk_191 : checkChunk tests 191 = true := by decide +kernel
theorem chunk_237 : checkChunk tests 237 = true := by decide +kernel
theorem chunk_239 : checkChunk tests 239 = true := by decide +kernel
theorem chunk_247 : checkChunk tests 247 = true := by decide +kernel
theorem chunk_255 : checkChunk tests 255 = true := by decide +kernel
theorem chunk_511 : checkChunk tests 511 = true := by decide +kernel

theorem allChunks : ∀ r ∈ repsD, checkChunk tests r = true := by
  intro r hr
  simp only [repsD, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [chunk_0, chunk_1, chunk_3, chunk_6, chunk_7, chunk_9, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15, chunk_27, chunk_30, chunk_31, chunk_35, chunk_38, chunk_39, chunk_43, chunk_46, chunk_47, chunk_51, chunk_55, chunk_63, chunk_97, chunk_99, chunk_103, chunk_107, chunk_108, chunk_109, chunk_110, chunk_111, chunk_120, chunk_121, chunk_122, chunk_123, chunk_126, chunk_127, chunk_167, chunk_175, chunk_183, chunk_191, chunk_237, chunk_239, chunk_247, chunk_255, chunk_511]

end EH

theorem OMA.disproof : ¬ (type_of% @OMA.S_gillibert_equal_halves.main) := by
  intro h
  obtain ⟨A, -, -, -, -, ⟨φ⟩⟩ := h EH.W EH.W_connected EH.W_vt ⟨14, rfl⟩
  exact EH.no_split EH.tests EH.allChunks A φ
