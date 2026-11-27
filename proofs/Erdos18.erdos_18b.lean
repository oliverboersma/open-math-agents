import FormalConjectures.ErdosProblems.«18»
import Mathlib

/-!
# Short sums of distinct divisors of a factorial

Howe, Huffman, Kohlmeyer and Kruer previously proved the polylogarithmic bound with exponent 9
in their November 1, 2026 manuscript. Kohlmeyer and Kruer developed the divisor digits,
positive lifting and factorial radix methods in their September work.
The proof below constructs branching levels in binary tries, covers bit positions using
shifted digit sets and transfers between nested least common multiples. It yields
an eventual constant multiple of the fifth power of the natural logarithm.

Earlier polylogarithmic bound and formalization:
https://github.com/Ghuffy1/erdos18-harmonic-shifts/tree/4b2ed2d07693602fa3b87fb5aa72fe16933f98af
-/

/-! Cardinality identity for the branching-level families in the factorial divisor argument. -/

namespace FactorialTrie

inductive Trie : Nat → Type
  | leaf (present : Bool) : Trie 0
  | node {height : Nat} (even odd : Trie height) : Trie (height + 1)

def Trie.leafCount : {height : Nat} → Trie height → Nat
  | _, .leaf present => if present then 1 else 0
  | _, .node even odd => even.leafCount + odd.leafCount

/-- A true entry requests that both branches survive at this depth. A false entry
allows the witness to choose a single branch. -/
def Trie.masks : {height : Nat} → Trie height → Finset (List Bool)
  | _, .leaf present => if present then {[]} else ∅
  | _, .node even odd =>
      ((even.masks ∪ odd.masks).image (false :: ·)) ∪
        ((even.masks ∩ odd.masks).image (true :: ·))

theorem Trie.card_masks {height : Nat} (t : Trie height) : t.masks.card = t.leafCount := by
  induction t with
  | leaf present => cases present <;> simp [masks, leafCount]
  | @node h even odd ihEven ihOdd =>
    have hd : Disjoint ((even.masks ∪ odd.masks).image (false :: ·))
        ((even.masks ∩ odd.masks).image (true :: ·)) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
      cases hb
    rw [masks, leafCount, Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ List.cons_injective,
      Finset.card_image_of_injective _ List.cons_injective,
      Finset.card_union_add_card_inter, ihEven, ihOdd]


end FactorialTrie

namespace FactorialTrie

def Trie.accepts : {h : Nat} → Trie h → Nat → Prop
  | _, .leaf present, _ => present = true
  | _, .node even odd, x => if x % 2 = 0 then even.accepts (x / 2) else odd.accepts (x / 2)

def Trie.child {h : Nat} : Trie (h + 1) → Bool → Trie h
  | .node even odd, b => if b then odd else even

def maskList (f : Nat → Bool) : Nat → List Bool
  | 0 => []
  | h + 1 => f 0 :: maskList (fun j => f (j + 1)) h

theorem Trie.cons_mem_masks {h : Nat} (t : Trie (h+1)) (b : Bool) (m : List Bool) :
    b :: m ∈ t.masks ↔
      if b then m ∈ (t.child false).masks ∧ m ∈ (t.child true).masks
      else m ∈ (t.child false).masks ∨ m ∈ (t.child true).masks := by
  cases t
  cases b <;> simp [masks, child, Finset.mem_image]

theorem Trie.length_of_mem_masks {h : Nat} {t : Trie h} {m : List Bool} (hm : m ∈ t.masks) :
    m.length = h := by
  induction t generalizing m with
  | leaf present =>
    cases present <;> simp_all [masks]
  | node even odd he ho =>
    obtain h | h := Finset.mem_union.mp hm
    · obtain ⟨tail, ht, rfl⟩ := Finset.mem_image.mp h
      rcases Finset.mem_union.mp ht with H | H
      · simp [he H]
      · simp [ho H]
    · obtain ⟨tail, ht, rfl⟩ := Finset.mem_image.mp h
      simp [he (Finset.mem_inter.mp ht).1]

theorem Trie.accepts_join {h : Nat} (t : Trie (h+1)) (b : Bool) (y : Nat) :
    t.accepts (b.toNat + 2*y) ↔ (t.child b).accepts y := by
  cases t
  cases b <;> simp [accepts, child, Nat.add_mul_div_left]

private theorem prescribe_parity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → Bool) (j : ι) (offset r : Nat) :
    ∃ b : ι → Bool, (∀ i, i ≠ j → b i = a i) ∧
      (offset + ∑ i, (b i).toNat) % 2 = r % 2 := by
  classical
  let s := ∑ i ∈ Finset.univ.erase j, (a i).toNat
  let c := decide ((offset+s) % 2 ≠ r % 2)
  let b := fun i => if i = j then c else a i
  refine ⟨b, fun i h => by simp [b,h], ?_⟩
  have hs : ∑ i ∈ Finset.univ.erase j, (b i).toNat = s :=
    Finset.sum_congr rfl fun i hi => by simp [b, Finset.ne_of_mem_erase hi]
  have hs' : ∑ i, (b i).toNat = s+c.toNat := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), hs]
    simp [b]
  rw [hs']
  by_cases hh : (offset+s) % 2 = r % 2
  · simp [c, hh]
  · simp [c, hh]
    omega

private theorem cover_with_offset {ι : Type*} [Fintype ι] (h : Nat)
    (t : ι → Trie h) (m : ι → Nat → Bool)
    (feasible : ∀ i, maskList (m i) h ∈ (t i).masks)
    (cover : ∀ j < h, ∃ i, m i j = true) (offset r : Nat) :
    ∃ x : ι → Nat, (∀ i, x i < 2^h ∧ (t i).accepts (x i)) ∧
      offset + ∑ i, x i ≡ r [MOD 2^h] := by
  classical
  induction h generalizing m r offset with
  | zero =>
    refine ⟨fun _ => 0, fun i => ⟨by simp, ?_⟩, by simp [Nat.ModEq, Nat.mod_one]⟩
    have h := feasible i
    cases e : t i with
    | leaf present =>
      rw [e] at h
      cases present <;> simp_all [Trie.masks, Trie.accepts, maskList]
  | succ h ih =>
    let tail := fun i j => m i (j+1)
    let nextMask := fun i => maskList (tail i) h
    have specs (i : ι) := ((t i).cons_mem_masks (m i 0) (nextMask i)).mp (feasible i)
    have alt (i : ι) : ∃ b : Bool, nextMask i ∈ ((t i).child b).masks := by
      have hi := specs i
      cases e : m i 0 with
      | false =>
        simp only [e, Bool.false_eq_true, ↓reduceIte] at hi
        exact hi.elim (fun H => ⟨false,H⟩) (fun H => ⟨true,H⟩)
      | true =>
        simp only [e, ↓reduceIte] at hi
        exact ⟨false,hi.1⟩
    choose a ha using alt
    obtain ⟨pivot, hpivot⟩ := cover 0 (Nat.succ_pos _)
    obtain ⟨b, hb, hparity⟩ := prescribe_parity a pivot offset r
    have hnext (i : ι) : nextMask i ∈ ((t i).child (b i)).masks := by
      by_cases e : i = pivot
      · subst i
        have hi := specs pivot
        simp only [hpivot, ↓reduceIte] at hi
        cases b pivot
        · exact hi.1
        · exact hi.2
      · rw [hb i e]
        exact ha _
    let low := offset + ∑ i, (b i).toNat
    obtain ⟨y, hy, hmod⟩ := ih (t := fun i => (t i).child (b i)) (m := tail) hnext
      (fun j hj => cover (j+1) (by omega)) (offset := low/2) (r := r/2)
    refine ⟨fun i => (b i).toNat + 2*y i, fun i => ⟨?_, ((t i).accepts_join (b i) _).mpr (hy i).2⟩, ?_⟩
    · have hbound := (hy i).1
      rw [pow_succ]
      have hbit : (b i).toNat ≤ 1 := by cases b i <;> decide
      change (b i).toNat + 2 * y i < _
      omega
    · have hscale := (hmod.mul_left' 2).add_left (r%2)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.add_assoc]
      change low + 2*(∑ i, y i) ≡ r [MOD 2^(h+1)]
      have hpar : low % 2 = r % 2 := hparity
      have hn : low + 2*(∑ i, y i) = r%2 + 2*(low/2 + ∑ i, y i) := by omega
      have hr : r%2 + 2*(r/2) = r := by omega
      rw [hr] at hscale
      rw [hn, pow_succ']
      exact hscale

/-- Once the feasible branching levels cover all bit positions, the sumset
contains every residue modulo the power of two. -/
theorem cover_residues {ι : Type*} [Fintype ι] (h : Nat) (t : ι → Trie h)
    (m : ι → Nat → Bool) (feasible : ∀ i, maskList (m i) h ∈ (t i).masks)
    (cover : ∀ j < h, ∃ i, m i j = true) (r : Nat) :
    ∃ x : ι → Nat, (∀ i, x i < 2^h ∧ (t i).accepts (x i)) ∧
      (∑ i, x i) ≡ r [MOD 2^h] := by
  simpa using cover_with_offset h t m feasible cover 0 r

end FactorialTrie

namespace FactorialTrie.Trie

private def tails (D : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (D.filter fun x ↦ x % 2 = r).image (· / 2)

/-- Read a set of binary words, starting at the least significant bit. -/
def ofFinset : (L : ℕ) → Finset ℕ → Trie L
  | 0, D => .leaf (decide (0 ∈ D))
  | L + 1, D => .node (ofFinset L (tails D 0)) (ofFinset L (tails D 1))

private theorem tails_card (D : Finset ℕ) (r : ℕ) :
    (tails D r).card = (D.filter fun x ↦ x % 2 = r).card := by
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  have hxr := (Finset.mem_filter.mp hx).2
  have hyr := (Finset.mem_filter.mp hy).2
  dsimp at hxy
  omega

private theorem tails_bound {D : Finset ℕ} {L : ℕ}
    (h : ∀ x ∈ D, x < 2 ^ (L + 1)) (r : ℕ) : ∀ y ∈ tails D r, y < 2 ^ L := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  have hx' := h x (Finset.mem_filter.mp hx).1
  rw [pow_succ] at hx'
  omega

theorem leafCount_ofFinset (L : ℕ) (D : Finset ℕ) (h : ∀ x ∈ D, x < 2 ^ L) :
    (ofFinset L D).leafCount = D.card := by
  induction L generalizing D with
  | zero =>
    have hz : ∀ x ∈ D, x = 0 := by simpa using h
    by_cases hzero : 0 ∈ D
    · have heq : D = {0} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hzero, hz⟩
      simp [heq, ofFinset, leafCount]
    · have heq : D = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun x hx ↦ hzero (hz x hx ▸ hx)
      simp [heq, ofFinset, leafCount]
  | succ L ih =>
    have hp (x : ℕ) : x % 2 = 1 ↔ ¬ x % 2 = 0 := by omega
    simpa only [ofFinset, leafCount, ih _ (tails_bound h _), tails_card, hp] using
      (Finset.card_filter_add_card_filter_not (s := D) fun x ↦ x % 2 = 0)

private theorem mem_tails_iff (D : Finset ℕ) (x : ℕ) :
    x / 2 ∈ tails D (x % 2) ↔ x ∈ D := by
  constructor
  · intro hx
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
    obtain ⟨hyD, hmod⟩ := Finset.mem_filter.mp hy
    have hxy : y = x := by omega
    exact hxy ▸ hyD
  · intro hx
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩, rfl⟩

theorem accepts_ofFinset (L : ℕ) (D : Finset ℕ) (x : ℕ) (hx : x < 2 ^ L) :
    (ofFinset L D).accepts x ↔ x ∈ D := by
  induction L generalizing D x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    simp [hx0, ofFinset, accepts]
  | succ L ih =>
    rw [pow_succ] at hx
    have hq : x / 2 < 2 ^ L := by omega
    simp only [ofFinset, accepts]
    split
    next h => simpa only [ih _ _ hq, ← h] using (mem_tails_iff D x)
    next h =>
      have hodd : x % 2 = 1 := by omega
      simpa only [ih _ _ hq, ← hodd] using (mem_tails_iff D x)


end FactorialTrie.Trie

namespace FactorialTrie

/-- The numeric indices of the branching levels of a Boolean mask. -/
def maskPositions : List Bool → Finset Nat
  | [] => ∅
  | b :: m =>
    if b then insert 0 ((maskPositions m).image Nat.succ) else (maskPositions m).image Nat.succ

theorem mem_maskPositions {m : List Bool} {j : Nat} :
    j ∈ maskPositions m ↔ m[j]? = some true := by
  induction m generalizing j with
  | nil => simp [maskPositions]
  | cons b m ih =>
    cases b <;> cases j <;> simp [maskPositions, ih, Finset.mem_image]

theorem card_maskPositions (m : List Bool) : (maskPositions m).card = m.count true := by
  induction m with
  | nil => simp [maskPositions]
  | cons b m ih =>
    cases b <;> simp [maskPositions, Finset.card_image_of_injective _ Nat.succ_injective, ih]

theorem maskPositions_subset_range (m : List Bool) : maskPositions m ⊆ Finset.range m.length := by
  intro j hj
  rw [mem_maskPositions] at hj
  exact Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp hj).1

private theorem maskList_eq (m : List Bool) :
    maskList (fun j => m[j]?.getD false) m.length = m := by
  induction m with
  | nil => rfl
  | cons b m ih =>
    simp [maskList, ih]

theorem cover_residues_of_masks {ι : Type*} [Fintype ι] (k : Nat)
    (t : ι → Trie k) (m : ι → List Bool)
    (feasible : ∀ i, m i ∈ (t i).masks)
    (cover : ∀ j < k, ∃ i, j ∈ maskPositions (m i)) (r : Nat) :
    ∃ x : ι → Nat, (∀ i, x i < 2^k ∧ (t i).accepts (x i)) ∧
      (∑ i, x i) ≡ r [MOD 2^k] := by
  apply cover_residues k t (fun i j => (m i)[j]?.getD false) _ _ r
  · intro i
    have he := maskList_eq (m i)
    rw [Trie.length_of_mem_masks (feasible i)] at he
    rw [he]
    exact feasible i
  · intro j hj
    obtain ⟨i,hi⟩ := cover j hj
    exact ⟨i, by simp [mem_maskPositions.mp hi]⟩

theorem shifted_mem_maskPositions {j : Nat} {m : List Bool} (hj : j ∈ maskPositions m)
    (a z : Nat) :
    a+j ∈ maskPositions (List.replicate a false ++ m ++ List.replicate z false) := by
  have hjlt := Finset.mem_range.mp (maskPositions_subset_range m hj)
  rw [mem_maskPositions] at *
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp)]
  simpa using hj

end FactorialTrie

namespace FactorialTrie.Trie

private def emptyTrie : (h : ℕ) → Trie h
  | 0 => .leaf false
  | h + 1 => .node (emptyTrie h) (emptyTrie h)

private theorem emptyTrie_rejects (h x : ℕ) : ¬ (emptyTrie h).accepts x := by
  induction h generalizing x with
  | zero => simp [emptyTrie, accepts]
  | succ h ih => simpa [emptyTrie, accepts] using ih (x / 2)

private def shiftLow {L : ℕ} (t : Trie L) : (s : ℕ) → Trie (L + s)
  | 0 => t
  | s + 1 => .node (shiftLow t s) (emptyTrie (L + s))

private theorem shiftLow_masks {L : ℕ} (t : Trie L) (s : ℕ) (m : List Bool)
    (hm : m ∈ t.masks) : List.replicate s false ++ m ∈ (shiftLow t s).masks := by
  induction s with
  | zero => simpa [shiftLow] using hm
  | succ s ih =>
    rw [List.replicate_succ, List.cons_append, shiftLow, cons_mem_masks]
    exact Or.inl ih

private theorem shiftLow_accepts {L : ℕ} (t : Trie L) (s x : ℕ) (hx : x < 2^(L+s))
    (ha : (shiftLow t s).accepts x) : ∃ d < 2^L, t.accepts d ∧ x = 2^s*d := by
  induction s generalizing x with
  | zero => exact ⟨x, hx, ha, by simp⟩
  | succ s ih =>
    simp only [shiftLow, accepts] at ha
    split at ha
    next h =>
      rw [Nat.add_succ, pow_succ] at hx
      obtain ⟨d, hd, had, heq⟩ := ih (x/2) (by omega) ha
      refine ⟨d, hd, had, ?_⟩
      rw [pow_succ', Nat.mul_assoc, ← heq]
      omega
    next h => exact (emptyTrie_rejects _ _ ha).elim

private def highLeaf (present : Bool) : (p : ℕ) → Trie p
  | 0 => .leaf present
  | p + 1 => .node (highLeaf present p) (emptyTrie p)

private theorem highLeaf_masks (p : ℕ) : List.replicate p false ∈ (highLeaf true p).masks := by
  induction p with
  | zero => simp [highLeaf, masks]
  | succ p ih =>
    rw [List.replicate_succ, highLeaf, cons_mem_masks]
    exact Or.inl ih

private theorem highLeaf_accepts (p : ℕ) (present : Bool) (x : ℕ) (hx : x < 2^p)
    (ha : (highLeaf present p).accepts x) : x = 0 ∧ present = true := by
  induction p generalizing x with
  | zero => exact ⟨by simpa using hx, ha⟩
  | succ p ih =>
    simp only [highLeaf, accepts] at ha
    split at ha
    next hb =>
      rw [pow_succ] at hx
      obtain ⟨hzero, hp⟩ := ih (x/2) (by omega) ha
      exact ⟨by omega, hp⟩
    next hb => exact (emptyTrie_rejects _ _ ha).elim

private def padHigh (p : ℕ) : {h : ℕ} → Trie h → Trie (p+h)
  | _, .leaf present => highLeaf present p
  | _, .node even odd => .node (padHigh p even) (padHigh p odd)

private theorem padHigh_masks (p : ℕ) {h : ℕ} (t : Trie h) (m : List Bool)
    (hm : m ∈ t.masks) : m ++ List.replicate p false ∈ (padHigh p t).masks := by
  induction t generalizing m with
  | leaf present =>
    cases present
    · simp [masks] at hm
    · simp [masks] at hm
      subst m
      simpa [padHigh] using highLeaf_masks p
  | node even odd he ho =>
    cases m with
    | nil => simp [masks, Finset.mem_image] at hm
    | cons b m =>
      rw [List.cons_append, padHigh, cons_mem_masks]
      rw [cons_mem_masks] at hm
      cases b
      · exact hm.elim (fun H ↦ Or.inl (he m H)) (fun H ↦ Or.inr (ho m H))
      · exact ⟨he m hm.1, ho m hm.2⟩

private theorem padHigh_accepts (p : ℕ) {h : ℕ} (t : Trie h) (x : ℕ) (hx : x < 2^(p+h))
    (ha : (padHigh p t).accepts x) : x < 2^h ∧ t.accepts x := by
  induction t generalizing x with
  | leaf present =>
    obtain ⟨rfl, hp⟩ := highLeaf_accepts p present x hx ha
    exact ⟨by simp, hp⟩
  | @node h even odd he ho =>
    rw [Nat.add_succ, pow_succ] at hx
    simp only [padHigh, accepts] at ha
    rw [pow_succ, accepts]
    split at ha
    next hbit =>
      obtain ⟨hlt, hacc⟩ := he (x/2) (by omega) ha
      exact ⟨by omega, if_pos hbit ▸ hacc⟩
    next hbit =>
      obtain ⟨hlt, hacc⟩ := ho (x/2) (by omega) ha
      exact ⟨by omega, if_neg hbit ▸ hacc⟩

/-- A shifted digit set with zero bits below and above its tree. -/
theorem padded_ofFinset (D : Finset ℕ) (L s k : ℕ) (hs : s + L ≤ k) (m : List Bool)
    (hm : m ∈ (ofFinset L D).masks) :
    ∃ t : Trie k, (List.replicate s false ++ m ++ List.replicate (k-(L+s)) false) ∈ t.masks ∧
      ∀ x < 2^k, t.accepts x → ∃ d ∈ D, x = 2^s*d := by
  generalize hp : k-(L+s) = p
  have heq : k = p+L+s := by omega
  subst k
  let t := ofFinset L D
  refine ⟨shiftLow (padHigh p t) s, ?_, ?_⟩
  · rw [List.append_assoc]
    exact shiftLow_masks _ _ _ (padHigh_masks p t m hm)
  · intro x hx ha
    obtain ⟨d, hd, hacc, hmul⟩ := shiftLow_accepts (padHigh p t) s x hx ha
    obtain ⟨hbound, hdacc⟩ := padHigh_accepts p t d hd hacc
    exact ⟨d, (accepts_ofFinset L D d hbound).mp hdacc, hmul⟩


end FactorialTrie.Trie

namespace FactorialTrie

/-- Feasible masks of independently shifted digit sets give simultaneous small
integer representatives for every residue when their shifts cover every bit. -/
theorem shifted_digit_sum {ι : Type*} [Fintype ι] (k : Nat)
    (L a : ι → Nat) (D : ι → Finset Nat) (m : ι → List Bool)
    (fits : ∀ i, a i + L i ≤ k)
    (feasible : ∀ i, m i ∈ (Trie.ofFinset (L i) (D i)).masks)
    (cover : ∀ j < k, ∃ i p, p ∈ maskPositions (m i) ∧ j = a i+p) (r : Nat) :
    ∃ d : ι → Nat, (∀ i, d i ∈ D i ∧ 2^(a i)*d i < 2^k) ∧
      (∑ i, 2^(a i)*d i) ≡ r [MOD 2^k] := by
  classical
  let padded (i : ι) :=
    List.replicate (a i) false ++ m i ++ List.replicate (k-(L i+a i)) false
  have parents (i : ι) := Trie.padded_ofFinset (D i) (L i) (a i) k (fits i) (m i) (feasible i)
  choose t ht ha using parents
  have hc (j : Nat) (hj : j < k) : ∃ i, j ∈ maskPositions (padded i) := by
    obtain ⟨i,p,hp,rfl⟩ := cover j hj
    exact ⟨i, shifted_mem_maskPositions hp _ _⟩
  obtain ⟨x,hx,hmod⟩ := cover_residues_of_masks k t padded ht hc r
  choose d hd heq using fun i => ha i (x i) (hx i).1 (hx i).2
  refine ⟨d, fun i => ⟨hd i, by simpa only [← heq i] using (hx i).1⟩, ?_⟩
  simpa only [← heq] using hmod

end FactorialTrie

namespace FactorialTrie
open Finset

def divisorDigits (k L : ℕ) : Finset ℕ :=
  (range (2^L)).filter fun d ↦ d = 0 ∨ d ∣ Nat.lcmUpto (128*k)

@[simp] theorem mem_divisorDigits {k L d : ℕ} :
    d ∈ divisorDigits k L ↔ d < 2^L ∧ (d = 0 ∨ d ∣ Nat.lcmUpto (128*k)) := by
  simp [divisorDigits]

private def boundedMasks : ℕ → ℕ → Finset (List Bool)
  | 0, _ => {[]}
  | n+1, 0 => (boundedMasks n 0).image (false :: ·)
  | n+1, s+1 => ((boundedMasks n (s+1)).image (false :: ·)) ∪
      ((boundedMasks n s).image (true :: ·))

private theorem mem_boundedMasks {l : List Bool} (s : ℕ) (hs : l.count true ≤ s) :
    l ∈ boundedMasks l.length s := by
  induction l generalizing s with
  | nil => simp [boundedMasks]
  | cons b l ih =>
    cases b <;> cases s <;> simp_all [boundedMasks]

private theorem card_boundedMasks (n s : ℕ) :
    (boundedMasks n s).card ≤ (n+1)^s := by
  induction n generalizing s with
  | zero => simp [boundedMasks]
  | succ n ih =>
    cases s with
    | zero =>
      simpa only [boundedMasks, pow_zero] using
        (Finset.card_image_le (s := boundedMasks n 0) (f := (false :: ·))).trans (ih 0)
    | succ s =>
      unfold boundedMasks
      calc
        _ ≤ _ := Finset.card_union_le _ _
        _ ≤ (n+1)^(s+1) + (n+1)^s := Nat.add_le_add
          (Finset.card_image_le.trans (ih (s+1))) (Finset.card_image_le.trans (ih s))
        _ = (n+1)^s * (n+2) := by rw [pow_succ]; ring
        _ ≤ (n+2)^(s+1) := by rw [pow_succ]; gcongr; omega

private theorem digit_prime_bound (k : ℕ) : 128*k ≤ 2^(Nat.log 2 k+8) := by
  have h := Nat.lt_pow_succ_log_self (by decide : 1<2) k
  rw [show Nat.log 2 k+8 = (Nat.log 2 k+1)+7 by omega, pow_add]
  norm_num at *; omega

private theorem primes_supply (k : ℕ) (hk : 0<k) :
    k ≤ (Nat.log 2 k + 8) * (Nat.primesLE (128*k)).card := by
  let m := 128*k
  let T := Nat.log 2 k + 8
  have hm : m ≤ 2^T := digit_prime_bound k
  have hp : Nat.lcmUpto m ≤ (2^T)^((Nat.primesLE m).card) := by
    rw [Nat.lcmUpto_eq_prod_pow_log, ← Finset.prod_const]
    apply Finset.prod_le_prod'
    intro p _
    exact (Nat.pow_log_le_self _ (by dsimp [m]; positivity)).trans hm
  have hm' : m+1 ≤ 2^(64*k) := by
    have h := Nat.two_mul_sq_add_one_le_two_pow_two_mul (32*k)
    rw [show 2*(32*k) = 64*k by omega] at h
    dsimp [m]; nlinarith [Nat.mul_le_mul_left k (show 1 ≤ k by omega)]
  have h := (Chebyshev.two_pow_le_mul_lcmUpto m).trans (Nat.mul_le_mul hm' hp)
  rw [← pow_mul, ← pow_add] at h
  have hh := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp h
  dsimp [m,T] at *; omega

/-- Every subset of a fixed set of bounded primes gives a distinct divisor digit. -/
theorem divisorDigits_card_lower {k L : ℕ} (hL : 0 < L) (hLk : L ≤ k) :
    2^((L-1)/(Nat.log 2 k + 8)) ≤ (divisorDigits k L).card := by
  let m := 128*k
  let T := Nat.log 2 k + 8
  let v := (L-1)/T
  have hT : 0 < T := by dsimp [T]; omega
  have hvL : T*v ≤ L-1 := by simpa [v, Nat.mul_comm] using Nat.div_mul_le_self (L-1) T
  have hv : v ≤ (Nat.primesLE m).card := by
    apply Nat.le_of_mul_le_mul_left _ hT
    exact hvL.trans ((by omega : L-1 ≤ k).trans (primes_supply k (by omega)))
  obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq hv
  let f : Finset ℕ → ℕ := fun A ↦ ∏ p ∈ A, p
  have hp {A : Finset ℕ} (h : A ∈ S.powerset) : ∀ p ∈ A, p.Prime :=
    fun _ hp ↦ Nat.prime_of_mem_primesLE (hS (Finset.mem_powerset.mp h hp))
  have hf : Set.InjOn f (↑S.powerset) := by
    intro A hA B hB he
    have h := congrArg Nat.primeFactors he
    simpa only [f, Nat.primeFactors_prod (hp hA), Nat.primeFactors_prod (hp hB)] using h
  have hsub : S.powerset.image f ⊆ divisorDigits k L := by
    intro x hx
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hx
    have hAS := Finset.mem_powerset.mp hA
    have hAP := hAS.trans hS
    have hm : m ≤ 2^T := digit_prime_bound k
    apply mem_divisorDigits.mpr
    constructor
    · calc
        f A ≤ ∏ _p ∈ A, 2^T :=
          Finset.prod_le_prod' fun _ h ↦ (Nat.mem_primesLE.mp (hAP h)).1.trans hm
        _ = 2^(T*A.card) := by rw [Finset.prod_const, ← pow_mul]
        _ ≤ 2^(T*v) := Nat.pow_le_pow_right (by decide)
          (Nat.mul_le_mul_left T ((Finset.card_le_card hAS).trans hSc.le))
        _ < 2^L := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mpr (by omega)
    · right
      exact (Finset.prod_dvd_prod_of_subset A (Nat.primesLE m) id hAP).trans
        (Nat.primorial_dvd_lcmUpto m)
  have h := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injOn hf, Finset.card_powerset, hSc] at h

private theorem two_le_digits {k L : ℕ} (hL : 0<L) : 2 ≤ (divisorDigits k L).card := by
  have h2 : 1 < 2^L := Nat.one_lt_two_pow hL.ne'
  have hsub : ({0,1} : Finset ℕ) ⊆ divisorDigits k L := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [h2,show 0<2^L by positivity]
  simpa using Finset.card_le_card hsub

/-- A divisor-digit trie contains a mask occupying at least a reciprocal quadratic-log fraction
of the available levels. -/
theorem exists_large_digit_mask {k L : ℕ} (hL : 0<L) (hLk : L≤k) :
    ∃ a ∈ (Trie.ofFinset L (divisorDigits k L)).masks,
      0 < a.count true ∧ L ≤ 32 * (1+Nat.log 2 k)^2 * a.count true := by
  let t := Trie.ofFinset L (divisorDigits k L)
  have hc : t.masks.card = (divisorDigits k L).card := by
    rw [Trie.card_masks, Trie.leafCount_ofFinset]; exact fun d hd ↦ (mem_divisorDigits.mp hd).1
  have htwo : 2 ≤ t.masks.card := hc ▸ two_le_digits hL
  have hne := Finset.card_pos.mp (by omega : 0<t.masks.card)
  obtain ⟨a, ha, hmax⟩ := t.masks.exists_max_image (fun a ↦ a.count true) hne
  let s := a.count true
  have hbound : t.masks.card ≤ (L+1)^s := by
    apply le_trans (Finset.card_le_card (t := boundedMasks L s) ?_) (card_boundedMasks L s)
    intro b hb
    rw [← Trie.length_of_mem_masks hb]
    exact mem_boundedMasks s (hmax b hb)
  have hs : 0<s := by
    by_contra! h
    have he : s=0 := by omega
    simp [he] at hbound; omega
  refine ⟨a, ha, hs, ?_⟩
  let w := 1 + Nat.log 2 k
  let T := Nat.log 2 k + 8
  have hw : 1 ≤ w := by dsimp [w]; omega
  have hT : 0<T := by dsimp [T]; omega
  have hlw : L+1 ≤ 2^w := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1<2) k
    dsimp [w]; rw [Nat.add_comm 1 (Nat.log 2 k)]; omega
  have hpow : 2^((L-1)/T) ≤ 2^(w*s) := calc
    _ ≤ (divisorDigits k L).card := divisorDigits_card_lower hL hLk
    _ = t.masks.card := hc.symm
    _ ≤ (L+1)^s := hbound
    _ ≤ (2^w)^s := Nat.pow_le_pow_left hlw _
    _ = 2^(w*s) := (pow_mul _ _ _).symm
  have hvs := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hpow
  have hdiv := Nat.lt_mul_div_succ (L-1) hT
  have h1 : 1 ≤ w*s := Nat.mul_pos (by omega) hs
  have hTle : T ≤ 8*w := by dsimp [T,w]; omega
  calc
    L ≤ T*((L-1)/T+1) := by omega
    _ ≤ (8*w)*(2*(w*s)) := Nat.mul_le_mul hTle (by omega)
    _ ≤ 32*w^2*s := by nlinarith


end FactorialTrie

namespace Erdos18Trie

/-- Admissible starts of bands of length 2^s, including the two reflected bands. -/
def bandStarts (k s : ℕ) : Finset ℕ :=
  ({2 ^ s, 2 * 2 ^ s, k - 2 * 2 ^ s, k - 3 * 2 ^ s} : Finset ℕ).filter
    (fun b ↦ 2 ^ s ≤ b ∧ b + 2 * 2 ^ s ≤ k)

theorem bandStarts_card_le_four (k s : ℕ) : (bandStarts k s).card ≤ 4 := by
  unfold bandStarts
  apply (Finset.card_filter_le _ _).trans
  grw [Finset.card_insert_le, Finset.card_insert_le, Finset.card_insert_le]
  simp

theorem bandStarts_bounds {k s b : ℕ} (hb : b ∈ bandStarts k s) :
    2 ^ s ≤ b ∧ b + 2 * 2 ^ s ≤ k := (Finset.mem_filter.mp hb).2

private theorem exists_left_band {k j : ℕ} (hk : 3 ≤ k) (hj : 0 < j) (hhalf : 2 * j < k) :
    ∃ s ≤ k.log2, ∃ b : ℕ, (b = 2 ^ s ∨ b = 2 * 2 ^ s) ∧
      2 ^ s ≤ b ∧ b + 2 * 2 ^ s ≤ k ∧ b ≤ j ∧ j < b + 2 ^ s := by
  obtain ⟨hl, hu⟩ := (Nat.log2_eq_iff (by omega : j ≠ 0)).mp rfl
  rw [pow_succ] at hu
  have hs : j.log2 ≤ k.log2 := (Nat.le_log2 (by omega : k ≠ 0)).mpr (by omega)
  by_cases h : 3 * 2 ^ j.log2 ≤ k
  · exact ⟨j.log2, hs, 2 ^ j.log2, Or.inl rfl, le_rfl, by omega, hl, by omega⟩
  · cases he : j.log2 with
    | zero => simp [he] at h; omega
    | succ s =>
      rw [he, pow_succ] at hl hu h
      exact ⟨s, by omega, 2 * 2 ^ s, Or.inr rfl, by omega, by omega, by omega, by omega⟩

theorem exists_mem_band {k j : ℕ} (hk : 3 ≤ k) (hj₀ : 0 < j) (hj₁ : j + 1 < k) :
    ∃ s ∈ Finset.range (k.log2 + 1), ∃ b ∈ bandStarts k s, b ≤ j ∧ j < b + 2 ^ s := by
  by_cases h : 2 * j < k
  · obtain ⟨s, hs, b, hb, h1, h2, h3, h4⟩ := exists_left_band hk hj₀ h
    refine ⟨s, Finset.mem_range.mpr (by omega), b, Finset.mem_filter.mpr ⟨?_, h1, h2⟩, h3, h4⟩
    rcases hb with rfl | rfl <;> simp
  · obtain ⟨s, hs, b, hb, h1, h2, h3, h4⟩ :=
      exists_left_band (j := k - 1 - j) hk (by omega) (by omega)
    refine ⟨s, Finset.mem_range.mpr (by omega), k - b - 2 ^ s,
      Finset.mem_filter.mpr ⟨?_, by omega, by omega⟩, by omega, by omega⟩
    rcases hb with rfl | rfl <;> simp only [Finset.mem_insert, Finset.mem_singleton] <;> omega

/-- Pairs (exponent, start) indexing all the selected dyadic bands. -/
def bands (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (k.log2 + 1)).biUnion fun s ↦ (bandStarts k s).image (Prod.mk s)

@[simp] theorem mem_bands {k s b : ℕ} :
    (s, b) ∈ bands k ↔ s < k.log2 + 1 ∧ b ∈ bandStarts k s := by
  simp [bands]

theorem bands_card_le (k : ℕ) : (bands k).card ≤ 4 * (k.log2 + 1) := by
  unfold bands
  rw [Nat.mul_comm]
  apply (Finset.card_biUnion_le_card_mul _ _ 4 ?_).trans_eq
  · simp
  · exact fun s _ ↦ Finset.card_image_le.trans (bandStarts_card_le_four k s)

theorem bands_cover {k j : ℕ} (hk : 3 ≤ k) (hj₀ : 0 < j) (hj₁ : j + 1 < k) :
    ∃ s b, (s, b) ∈ bands k ∧ b ≤ j ∧ j < b + 2 ^ s := by
  obtain ⟨s, hs, b, hb, h⟩ := exists_mem_band hk hj₀ hj₁
  exact ⟨s, b, mem_bands.mpr ⟨Finset.mem_range.mp hs, hb⟩, h⟩


end Erdos18Trie

namespace FactorialTrie

open Finset

/-- Positions attainable with one copy of a branching mask at the indicated shift. -/
def shiftMask (a : ℕ) (I : Finset ℕ) : Finset ℕ := I.image (a + ·)

private theorem useful_shift {b L D : ℕ} {I X : Finset ℕ}
    (hL : 0 < L) (hb : L ≤ b) (hI : I ⊆ range L) (hdense : L ≤ D * I.card)
    (hX : X ⊆ Ico b (b+L)) :
    ∃ a ∈ Ico (b-L) (b+L), X.card ≤ 2*D * (X ∩ shiftMask a I).card := by
  classical
  let A := Ico (b-L) (b+L)
  have hA : A.Nonempty := ⟨b, mem_Ico.mpr (by omega)⟩
  have hcA : A.card = 2*L := by simp [A]; omega
  let rel := fun x a : ℕ ↦ x ∈ shiftMask a I
  have hcov (x : ℕ) (hx : x ∈ X) : I.card ≤ (A.bipartiteAbove rel x).card := by
    obtain ⟨hxb,hxe⟩ := mem_Ico.mp (hX hx)
    apply card_le_card_of_injOn (fun i ↦ x-i)
    · intro i hi
      have hiL := mem_range.mp (hI hi)
      refine (mem_bipartiteAbove _).mpr ⟨mem_Ico.mpr (by dsimp; omega), ?_⟩
      exact mem_image.mpr ⟨i, hi, by dsimp; omega⟩
    · intro i hi j hj heq
      have hiL := mem_range.mp (hI hi)
      have hjL := mem_range.mp (hI hj)
      change x-i = x-j at heq
      omega
  obtain ⟨a,ha,hamax⟩ := A.exists_max_image (fun i ↦ (X.bipartiteBelow rel i).card) hA
  have hcnt := card_nsmul_le_card_nsmul (R := ℕ) rel hcov hamax
  rw [hcA] at hcnt
  have eqI : X.bipartiteBelow rel a = X ∩ shiftMask a I := by ext; simp [rel]
  simp only [smul_eq_mul, eqI] at hcnt
  refine ⟨a, ha, ?_⟩
  have hpos : 0 < I.card := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hdense; omega
  apply Nat.le_of_mul_le_mul_right (c := I.card)
  · calc X.card * I.card ≤ 2*L*(X ∩ shiftMask a I).card := hcnt
         _ ≤ 2*(D*I.card)*(X ∩ shiftMask a I).card := by gcongr
         _ = _ := by ring
  · exact hpos

/-- A batch of D greedy choices at least halves a set of size below 2B. -/
private theorem halve_cover {A X : Finset ℕ} (f : ℕ → Finset ℕ) {D B : ℕ} (hD : 0<D)
    (hX : X.card < 2*B)
    (pick : ∀ T ⊆ X, ∃ a ∈ A, T.card ≤ D*(T ∩ f a).card) :
    ∃ S ⊆ A, S.card ≤ D ∧ ∃ T ⊆ X, T.card < B ∧
      ∀ j ∈ X, j ∈ T ∨ ∃ a ∈ S, j ∈ f a := by
  classical
  have iter (t : ℕ) : ∃ S ⊆ A, S.card ≤ t ∧ ∃ T ⊆ X,
        (T.card < B ∨ D*T.card+t*B ≤ D*X.card) ∧
        ∀ j ∈ X, j ∈ T ∨ ∃ a ∈ S, j ∈ f a := by
    induction t with
    | zero => exact ⟨∅, empty_subset _, by simp, X, Subset.rfl, Or.inr (by simp),
        fun j hj ↦ Or.inl hj⟩
    | succ t ih =>
      obtain ⟨S,hSA,hSt,T,hTX,progress,hcover⟩ := ih
      by_cases hsmall : T.card < B
      · exact ⟨S,hSA,by omega,T,hTX,Or.inl hsmall,hcover⟩
      have hp := progress.resolve_left hsmall
      obtain ⟨a,ha,hgain⟩ := pick T hTX
      refine ⟨insert a S, insert_subset ha hSA, ?_, T \ f a, (sdiff_subset).trans hTX,
        Or.inr ?_, ?_⟩
      · have := card_insert_le a S; omega
      · have he := card_sdiff_add_card_inter T (f a)
        have hweighted := congrArg (D * ·) he
        simp only [Nat.mul_add] at hweighted
        rw [Nat.succ_mul]
        omega
      · intro j hj
        rcases hcover j hj with hin|⟨a₀,ha₀,hj₀⟩
        · by_cases hjf : j ∈ f a
          · exact Or.inr ⟨a, mem_insert_self .., hjf⟩
          · exact Or.inl (mem_sdiff.mpr ⟨hin,hjf⟩)
        · exact Or.inr ⟨a₀, mem_insert_of_mem ha₀, hj₀⟩
  obtain ⟨S,hSA,hSD,T,hTX,hp,hcover⟩ := iter D
  refine ⟨S,hSA,hSD,T,hTX,?_,hcover⟩
  rcases hp with h|h
  · exact h
  · rw [← Nat.mul_add] at h
    have := Nat.le_of_mul_le_mul_left h hD
    omega

private theorem cover_by_halves {A X : Finset ℕ} (f : ℕ → Finset ℕ) {D : ℕ} (hD : 0<D)
    (pick : ∀ T ⊆ X, ∃ a ∈ A, T.card ≤ D*(T ∩ f a).card)
    (s : ℕ) (hX : X.card < 2^s) :
    ∃ S ⊆ A, S.card ≤ s*D ∧ ∀ j ∈ X, ∃ a ∈ S, j ∈ f a := by
  classical
  induction s generalizing X with
  | zero =>
    have hzero : X = ∅ := card_eq_zero.mp (by simpa using hX)
    subst X; exact ⟨∅, empty_subset _, by simp, by simp⟩
  | succ s ih =>
    obtain ⟨S,hSA,hSD,T,hTX,hT,hcov⟩ := halve_cover (B := 2^s) f hD (by simpa [pow_succ, mul_comm] using hX) pick
    obtain ⟨S₁,hS₁A,hS₁D,hcov₁⟩ := ih (X := T) (fun U h ↦ pick U (h.trans hTX)) hT
    refine ⟨S ∪ S₁, union_subset hSA hS₁A, ?_, ?_⟩
    · have := card_union_le S S₁; rw [Nat.succ_mul]; omega
    · intro j hj
      rcases hcov j hj with h|⟨a,ha,hja⟩
      · obtain ⟨a,ha,hja⟩ := hcov₁ j h
        exact ⟨a, mem_union_right _ ha, hja⟩
      · exact ⟨a, mem_union_left _ ha, hja⟩

/-- A band of length L is covered by logarithmically many batches of translations. -/
theorem band_shift_cover {b L D : ℕ} {I : Finset ℕ}
    (hL : 0 < L) (hb : L ≤ b) (hI : I ⊆ range L) (hdense : L ≤ D * I.card) :
    ∃ S ⊆ Ico (b-L) (b+L), S.card ≤ (L.log2+1)*(2*D) ∧
      ∀ j ∈ Ico b (b+L), ∃ a ∈ S, j ∈ shiftMask a I := by
  have hD : 0 < D := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hdense; omega
  apply cover_by_halves (f := fun a ↦ shiftMask a I) (by omega) (fun T hT ↦ useful_shift hL hb hI hdense hT)
  simpa using (Nat.lt_log2_self (n := L))

end FactorialTrie

namespace FactorialTrie

open Finset Erdos18Trie

set_option maxHeartbeats 1000000 in
/-- A family of (length, shift) pairs covering every bit. Every mask fits below bit k. -/
theorem all_shift_cover (k D : ℕ) (hk : 3 ≤ k) (I : ℕ → Finset ℕ)
    (hI : ∀ L, 0 < L → L ≤ k → I L ⊆ range L)
    (hdense : ∀ L, 0 < L → L ≤ k → L ≤ D * (I L).card) :
    ∃ P : Finset (ℕ × ℕ), P.card ≤ 2 + 8*D*(k.log2+1)^2 ∧
      (∀ p ∈ P, 0 < p.1 ∧ p.2+p.1 ≤ k) ∧
      ∀ j < k, ∃ p ∈ P, ∃ i ∈ I p.1, p.2+i=j := by
  classical
  have localCover (p : ℕ × ℕ) (hp : p ∈ bands k) :
      ∃ S ⊆ Ico (p.2-2^p.1) (p.2+2^p.1), S.card ≤ (k.log2+1)*(2*D) ∧
        ∀ j ∈ Ico p.2 (p.2+2^p.1), ∃ a ∈ S, j ∈ shiftMask a (I (2^p.1)) := by
    obtain ⟨_,hband⟩ := mem_bands.mp hp
    obtain ⟨hb,he⟩ := bandStarts_bounds hband
    have hL : 0 < 2^p.1 := by positivity
    have hLk : 2^p.1 ≤ k := by omega
    obtain ⟨S,hSA,hSc,hcov⟩ := band_shift_cover hL hb (hI _ hL hLk) (hdense _ hL hLk)
    refine ⟨S,hSA,hSc.trans ?_,hcov⟩
    gcongr
    rw [Nat.log2_two_pow]
    exact (Nat.le_log2 (by omega : k ≠ 0)).mpr hLk
  choose! S hSA hSc hcov using localCover
  let sets (p : ℕ × ℕ) : Finset (ℕ × ℕ) := (S p).image (Prod.mk (2^p.1))
  let interior := (bands k).biUnion sets
  have hcard : interior.card ≤ 8*D*(k.log2+1)^2 := by
    calc interior.card ≤ (bands k).card * ((k.log2+1)*(2*D)) :=
           card_biUnion_le_card_mul _ _ _ (fun p hp ↦ card_image_le.trans (hSc p hp))
         _ ≤ (4*(k.log2+1)) * ((k.log2+1)*(2*D)) := by gcongr; exact bands_card_le k
         _ = _ := by ring
  let P := insert (1,0) (insert (1,k-1) interior)
  have hzero : 0 ∈ I 1 := by
    have hpos := hdense 1 (by decide) (by omega)
    have hnon : (I 1).Nonempty := card_pos.mp (by
      by_contra! h
      simp [Nat.eq_zero_of_le_zero h] at hpos)
    obtain ⟨x,hx⟩ := hnon
    have hlt := mem_range.mp (hI 1 (by decide) (by omega) hx)
    simpa [show x=0 by omega] using hx
  refine ⟨P, ?_, ?_, ?_⟩
  · have h₁ := card_insert_le (1,0) (insert (1,k-1) interior)
    have h₂ := card_insert_le (1,k-1) interior
    dsimp [P]; omega
  · rintro ⟨L,a⟩ hp
    simp only [P,mem_insert] at hp
    rcases hp with e|e|hp
    · cases e; simp; omega
    · cases e; simp; omega
    · change (L,a) ∈ (bands k).biUnion sets at hp
      obtain ⟨p,hpBand,hm⟩ := mem_biUnion.mp hp
      change (L,a) ∈ (S p).image (Prod.mk (2^p.1)) at hm
      obtain ⟨a₀,ha,he⟩ := mem_image.mp hm
      cases he
      obtain ⟨_,he⟩ := bandStarts_bounds (k := k) (s := p.1) (b := p.2) (mem_bands.mp hpBand).2
      have ht := (mem_Ico.mp (hSA p hpBand ha)).2
      exact ⟨by positivity, by simp only; omega⟩
  · intro j hj
    by_cases hlow : j=0
    · exact ⟨(1,0), mem_insert_self .., 0, hzero, by simp [hlow]⟩
    by_cases hhigh : j=k-1
    · exact ⟨(1,k-1), mem_insert_of_mem (mem_insert_self ..), 0, hzero, by simp [hhigh]⟩
    obtain ⟨s,b,hb,hbj,hje⟩ := bands_cover hk (by omega : 0<j) (by omega : j+1<k)
    obtain ⟨a,ha,hm⟩ := hcov (s,b) hb j (mem_Ico.mpr ⟨hbj,hje⟩)
    obtain ⟨i,hi,he⟩ := mem_image.mp hm
    exact ⟨(2^s,a), mem_insert_of_mem (mem_insert_of_mem
      (mem_biUnion.mpr ⟨(s,b), hb, mem_image.mpr ⟨a,ha,rfl⟩⟩)), i,hi,he⟩

end FactorialTrie

/-! # Small divisor-digit sums representing residues modulo a power of two -/

namespace E18Global

open FactorialTrie

/-- A power of two times a positive divisor of the common base. -/
def Good (base x : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ d ∣ base ∧ x = 2 ^ a * d

/-- Every residue has a multiset representation by a polylogarithmic number of small terms. -/
theorem localMod (k r : ℕ) (hk : 3 ≤ k) :
    ∃ s : Multiset ℕ, s.card ≤ 258 * (Nat.log 2 k + 1)^4 ∧
      (∀ x ∈ s, x < 2^k ∧ (x = 0 ∨ Good (Nat.lcmUpto (128 * k)) x)) ∧
      Nat.ModEq (2^k) r s.sum := by
  classical
  let w := Nat.log 2 k + 1
  let D := 32 * w^2
  have available (L : ℕ) : ∃ m : List Bool, (0 < L ∧ L ≤ k) →
      m ∈ (Trie.ofFinset L (divisorDigits k L)).masks ∧ L ≤ D * m.count true := by
    by_cases hL : 0 < L ∧ L ≤ k
    · obtain ⟨m, hm, _, hlarge⟩ := exists_large_digit_mask hL.1 hL.2
      exact ⟨m, fun _ ↦ ⟨hm, by simpa [D, w, Nat.add_comm 1] using hlarge⟩⟩
    · exact ⟨[], fun h ↦ (hL h).elim⟩
  choose m hm using available
  let I (L : ℕ) := maskPositions (m L)
  have hI (L : ℕ) (hL : 0 < L) (hLk : L ≤ k) : I L ⊆ Finset.range L := by
    simpa only [I, Trie.length_of_mem_masks (hm L ⟨hL, hLk⟩).1] using
      maskPositions_subset_range (m L)
  have hdense (L : ℕ) (hL : 0 < L) (hLk : L ≤ k) : L ≤ D * (I L).card := by
    rw [show (I L).card = (m L).count true from card_maskPositions (m L)]
    exact (hm L ⟨hL, hLk⟩).2
  obtain ⟨P, hcard, hfits, hcover⟩ := all_shift_cover k D hk I hI hdense
  let len (p : P) := p.val.1
  let shift (p : P) := p.val.2
  obtain ⟨d, hd, hmod⟩ := shifted_digit_sum k len shift
    (fun p ↦ divisorDigits k (len p)) (fun p ↦ m (len p))
    (fun p ↦ (hfits p.val p.prop).2)
    (fun p ↦ (hm _ ⟨(hfits p.val p.prop).1, by
      have h := (hfits p.val p.prop).2
      omega⟩).1)
    (fun j hj ↦ by
      obtain ⟨p, hp, i, hi, heq⟩ := hcover j hj
      exact ⟨⟨p, hp⟩, i, hi, heq.symm⟩) r
  let val (p : P) := 2^(shift p) * d p
  let s := (Finset.univ : Finset P).val.map val
  refine ⟨s, ?_, ?_, ?_⟩
  · change s.card ≤ 258 * w^4
    have hs : s.card = P.card := by
      simp only [s, Multiset.card_map]
      change (Finset.univ : Finset P).card = P.card
      exact Finset.card_univ.trans (Fintype.card_coe P)
    have hw : 1 ≤ w^4 := Nat.succ_le_of_lt (pow_pos (Nat.succ_pos _) _)
    have hcalc : 2 + 8*D*w^2 ≤ 258*w^4 := by
      dsimp [D]
      nlinarith only [hw]
    rw [hs]
    apply le_trans _ hcalc
    simpa [w, Nat.log2_eq_log_two] using hcard
  · intro x hx
    change x ∈ (Finset.univ : Finset P).val.map val at hx
    obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hx
    refine ⟨(hd p).2, ?_⟩
    rcases (mem_divisorDigits.mp (hd p).1).2 with hz | hdvd
    · exact Or.inl (by simp [val, hz])
    · by_cases hz : d p = 0
      · exact Or.inl (by simp [val, hz])
      · exact Or.inr ⟨shift p, d p, Nat.pos_of_ne_zero hz, hdvd, rfl⟩
  · change r ≡ (∑ p, val p) [MOD 2^k]
    exact hmod.symm

end E18Global

/-! Eliminate zeroes and merge equal summands without increasing the number of terms. -/

namespace E18Global

open Multiset

theorem distinct_sum {P : ℕ → Prop} (dbl : ∀ x, P x → P (2*x)) (s : Multiset ℕ)
    (hs : ∀ x ∈ s, x = 0 ∨ P x) :
    ∃ F : Finset ℕ, F.card ≤ s.card ∧ F.sum id = s.sum ∧ ∀ x ∈ F, P x := by
  classical
  by_cases hz : 0 ∈ s
  · obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hz
    obtain ⟨F, hF, hsum, hP⟩ := distinct_sum dbl t (fun x hx ↦ hs x (by simp [hx]))
    exact ⟨F, by simpa using hF.trans (Nat.le_succ _), by simpa using hsum, hP⟩
  by_cases hn : s.Nodup
  · exact ⟨⟨s, hn⟩, le_rfl, by simp [Finset.sum_mk], fun x hx ↦
      (hs x hx).resolve_left (fun he ↦ hz (he ▸ hx))⟩
  simp only [Multiset.nodup_iff_ne_cons_cons, not_forall, not_not] at hn
  obtain ⟨x, t, rfl⟩ := hn
  have hx : P x := (hs x (by simp)).resolve_left (fun he ↦ hz (by simp [he]))
  have hnew : ∀ y ∈ (2*x) ::ₘ t, y = 0 ∨ P y := by
    intro y hy
    rcases Multiset.mem_cons.mp hy with rfl | hy
    · exact Or.inr (dbl x hx)
    · exact hs y (by simp [hy])
  obtain ⟨F, hF, hsum, hP⟩ := distinct_sum dbl ((2*x) ::ₘ t) hnew
  exact ⟨F, by simp only [Multiset.card_cons] at *; omega,
    by simp only [Multiset.sum_cons] at *; omega, hP⟩
termination_by s.card
decreasing_by all_goals simp_all


end E18Global

/-! # Binary expansion of a scaled quotient -/

namespace E18Global

theorem binary_lift {q k v : ℕ} (hq : q < 2 ^ (v - k)) :
    ∃ s : Multiset ℕ, s.card ≤ v - k ∧ s.sum = 2 ^ k * q ∧
      ∀ x ∈ s, ∃ a : ℕ, x = 2 ^ a := by
  have hsub : q.bitIndices.toFinset ⊆ Finset.range (v - k) := by
    intro i hi
    apply Finset.mem_range.mpr
    by_contra! hge
    exact (Nat.pow_le_pow_right (by decide) hge |>.trans
      (Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hi))).not_gt hq
  have hlen := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup Nat.bitIndices_nodup, Finset.card_range] at hlen
  refine ⟨↑((2 ^ k * q).bitIndices.map (fun a ↦ 2 ^ a)), ?_, ?_, ?_⟩
  · simpa using hlen
  · exact Nat.sum_map_two_pow_bitIndices _
  · intro x hx
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hx)
    exact ⟨a, rfl⟩

end E18Global

namespace E18Global

/-- Reserve enough leading bits for the largest sum of small representatives.
The remaining high binary digits also fit the logarithmic budget. -/
theorem lift_width (C k₀ : ℕ) :
    ∃ A : ℕ, ∀ v : ℕ, v ≤ A * (Nat.log 2 v + 1)^4 ∨
      ∃ k : ℕ, k₀ ≤ k ∧ k ≤ v ∧
        C * (Nat.log 2 k + 1)^4 * 2^k ≤ 2^(v-1) ∧
        v-k ≤ A * (Nat.log 2 v + 1)^4 := by
  refine ⟨C + 1 + k₀, fun v => ?_⟩
  let w := (Nat.log 2 v + 1)^4
  have hw : 1 ≤ w := Nat.succ_le_of_lt (by dsimp [w]; positivity)
  by_cases hsmall : v ≤ (C + 1 + k₀) * w
  · exact Or.inl hsmall
  right
  let k := v - (C + 1)*w
  have hk₀ : k₀ ≤ k := by
    have h := Nat.mul_le_mul_left k₀ hw
    simp only [Nat.mul_one] at h
    dsimp [k]
    rw [Nat.add_mul] at hsmall
    omega
  have hkv : k ≤ v := Nat.sub_le ..
  have hdiff : v-k = (C+1)*w := by
    dsimp [k]
    rw [Nat.add_mul] at hsmall
    omega
  refine ⟨k, hk₀, hkv, ?_, ?_⟩
  · have hklog := Nat.log_mono_right (b := 2) hkv
    have hcost : C * (Nat.log 2 k + 1)^4 ≤ C*w := by
      dsimp [w]
      gcongr
    calc
      C * (Nat.log 2 k + 1)^4 * 2^k ≤ 2^(C*w) * 2^k :=
        Nat.mul_le_mul_right _ (hcost.trans (C*w).lt_two_pow_self.le)
      _ = 2^(C*w + k) := (pow_add ..).symm
      _ ≤ 2^(v-1) := by
        apply Nat.pow_le_pow_right (by decide)
        rw [Nat.add_mul, Nat.one_mul] at hdiff
        omega
  · rw [hdiff]
    exact Nat.mul_le_mul_right _ (by omega)

end E18Global

namespace E18Global

/-- A common host for the shifted divisor digits at scale `u`. -/
def host (u : ℕ) : ℕ := 2 ^ u * Nat.lcmUpto (128 * u)

theorem host_pos (u : ℕ) : 0 < host u := by
  exact Nat.mul_pos (pow_pos (by decide) _) (Nat.lcmUpto_pos _)

theorem host_dvd_host {u v : ℕ} (h : u ≤ v) : host u ∣ host v := by
  apply mul_dvd_mul
  · exact pow_dvd_pow _ h
  · unfold Nat.lcmUpto
    apply Finset.lcm_dvd
    intro i hi
    refine Finset.dvd_lcm (s := Finset.Icc 1 (128 * v)) (f := id) ?_
    have hi' := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨hi'.1, hi'.2.trans (Nat.mul_le_mul_left 128 h)⟩

theorem host_dvd_host_double (u : ℕ) : host u ∣ host (2 * u) :=
  host_dvd_host (by omega)

theorem two_pow_dvd_factorial_double (u : ℕ) : 2 ^ u ∣ (2 * u).factorial := by
  induction u with
  | zero => simp
  | succ u hu =>
    rw [show 2 * (u + 1) = 2 * u + 1 + 1 by omega, Nat.factorial_succ, Nat.factorial_succ, pow_succ]
    have htwo : 2 ∣ 2 * u + 1 + 1 := ⟨u + 1, by omega⟩
    have h₁ := mul_dvd_mul htwo (dvd_mul_of_dvd_right hu (2 * u + 1))
    simpa only [Nat.mul_comm 2 (2 ^ u)] using h₁

theorem host_dvd_factorial (u : ℕ) : host u ∣ (130 * u).factorial := by
  rw [show 130 * u = 2 * u + 128 * u by omega]
  exact (mul_dvd_mul (two_pow_dvd_factorial_double u)
    (Nat.lcmUpto_dvd_factorial (128 * u))).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem host_le_two_pow (u : ℕ) : host u ≤ 2 ^ (1025 * u) := by
  have hlogtwo : (2 / 3 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hψ := Chebyshev.psi_le_const_mul_self (x := ((128 * u : ℕ) : ℝ)) (by positivity)
  rw [Chebyshev.psi_eq_log_lcmUpto] at hψ
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h4] at hψ
  have hmul : Real.log (Nat.lcmUpto (128 * u)) ≤ (1024 * (u : ℝ)) * Real.log 2 := by
    calc
      _ ≤ (2 * Real.log 2 + 4) * ↑(128 * u) := hψ
      _ ≤ (8 * Real.log 2) * ↑(128 * u) := by gcongr; linarith
      _ = _ := by push_cast; ring
  have hmain : Real.log (host u) ≤ Real.log ((2 : ℕ) ^ (1025 * u)) := by
    unfold host
    push_cast
    rw [Real.log_mul (by positivity)
      (by exact_mod_cast Nat.lcmUpto_ne_zero (128 * u)), Real.log_pow, Real.log_pow]
    push_cast
    nlinarith only [hmul]
  exact_mod_cast (Real.log_le_log_iff (by exact_mod_cast host_pos u) (by positivity)).mp hmain

theorem host_double_le_two_pow (u : ℕ) : host (2 * u) ≤ 2 ^ (2050 * u) := by
  simpa only [← Nat.mul_assoc] using host_le_two_pow (2 * u)

theorem host_log_le (u : ℕ) : Nat.log 2 (host u) ≤ 1025 * u := by
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp
    ((Nat.pow_log_le_self 2 (host_pos u).ne').trans (host_le_two_pow u))

theorem host_double_log_le (u : ℕ) : Nat.log 2 (host (2 * u)) ≤ 2050 * u := by
  simpa only [← Nat.mul_assoc] using host_log_le (2 * u)

theorem prime_le_of_dvd_host {p u : ℕ} (hu : 0 < u) (hp : p.Prime)
    (hd : p ∣ host u) : p ≤ 128 * u := by
  rcases hp.dvd_mul.mp hd with htwo | hlcm
  · have h := Nat.le_of_dvd (by decide : 0 < 2) (hp.dvd_of_dvd_pow htwo)
    omega
  · exact hp.dvd_factorial.mp (hlcm.trans (Nat.lcmUpto_dvd_factorial _))

theorem prime_le_of_dvd_host_double {p u : ℕ} (hu : 0 < u) (hp : p.Prime)
    (hd : p ∣ host (2 * u)) : p ≤ 256 * u := by
  simpa only [← Nat.mul_assoc] using prime_le_of_dvd_host (by omega : 0 < 2 * u) hp hd

theorem prime_le_of_dvd_factorial {p n : ℕ} (hp : p.Prime) (hd : p ∣ n.factorial) : p ≤ n :=
  hp.dvd_factorial.mp hd

end E18Global

/-! # Divisor-sum representations using bounded radix factors -/

namespace E18Global

open Finset

def Short (N R k : ℕ) : Prop :=
  ∀ m < R, ∃ D : Finset ℕ, D ⊆ N.divisors ∧ D.card ≤ k ∧ D.sum id = m

theorem Short.practical {N k : ℕ} (h : Short N (N+1) k) : N.IsPractical := by
  intro m hm
  obtain ⟨D, hD, _, hsum⟩ := h m (by omega)
  exact ⟨D, hD, hsum.symm⟩

theorem Short.practicalH_le {N k : ℕ} (h : Short N (N+1) k) : Erdos18.practicalH N ≤ k := by
  apply Finset.sup_le
  intro m hm
  obtain ⟨D, hD, hsize, hsum⟩ := h m (by have := (mem_Icc.mp hm).2; omega)
  exact (Nat.sInf_le (show D.card ∈ {k | ∃ F : Finset ℕ,
    F ⊆ N.divisors ∧ F.card = k ∧ m ∈ subsetSums F} from
    ⟨D, hD, rfl, D, subset_rfl, hsum.symm⟩)).trans hsize

theorem short_of_practical {N : ℕ} (h : N.IsPractical) :
    Short N (N+1) (Erdos18.practicalH N) := by
  intro m hm
  by_cases h0 : m = 0
  · subst m
    exact ⟨∅, by simp, by simp, by simp⟩
  have hmN : m ≤ N := by omega
  obtain ⟨D, hD, hsum⟩ := h m hmN
  let K := {k | ∃ F : Finset ℕ, F ⊆ N.divisors ∧ F.card = k ∧ m ∈ subsetSums F}
  have hK : K.Nonempty := ⟨D.card, D, hD, rfl, D, subset_rfl, hsum⟩
  obtain ⟨F, hF, hcard, B, hB, hsumB⟩ := Nat.sInf_mem hK
  refine ⟨B, hB.trans hF, (Finset.card_le_card hB).trans ?_, hsumB.symm⟩
  rw [hcard]
  exact Finset.le_sup (s := Icc 1 N) (b := m) (f := fun r ↦
    sInf {k | ∃ F : Finset ℕ, F ⊆ N.divisors ∧ F.card = k ∧ r ∈ subsetSums F})
    (mem_Icc.mpr ⟨by omega, hmN⟩)

theorem Short.of_dvd {N N' R k : ℕ} (hd : N ∣ N') (hN' : 0 < N')
    (h : Short N R k) : Short N' R k := by
  intro m hm
  obtain ⟨D, hD, hsize, hsum⟩ := h m hm
  exact ⟨D, fun d hdmem ↦ Nat.mem_divisors.mpr
    ⟨(Nat.dvd_of_mem_divisors (hD hdmem)).trans hd, hN'.ne'⟩, hsize, hsum⟩

theorem Short.restrict {N R R' k : ℕ} (hR' : R' ≤ R)
    (h : Short N R k) : Short N R' k :=
  fun m hm ↦ h m (hm.trans_le hR')

theorem short_mul {N q k w : ℕ} (hN : 0 < N) (hq : 0 < q)
    (hMain : Short N (N+1) k) (hLow : Short N q w) :
    Short (N*q) (N*q+1) (k+w) := by
  classical
  intro m hm
  let r := m % q
  let s := m / q
  have hR : r < q := Nat.mod_lt _ hq
  have hEq : m = r + q*s := (Nat.mod_add_div m q).symm
  have hSQ : q*s ≤ q*N := by
    rw [mul_comm q N]
    omega
  have hS : s ≤ N := Nat.le_of_mul_le_mul_left hSQ hq
  obtain ⟨D, hD, hDsize, hDsum⟩ := hLow r hR
  obtain ⟨F, hF, hFsize, hFsum⟩ := hMain s (by omega)
  let embed : ℕ ↪ ℕ := ⟨fun d ↦ q*d, fun _ _ hh ↦ Nat.eq_of_mul_eq_mul_left hq hh⟩
  have hDis : Disjoint D (F.map embed) := by
    refine Finset.disjoint_left.mpr ?_
    intro d hd hmem
    obtain ⟨f, hf, rfl⟩ := mem_map.mp hmem
    have hfpos : 0 < f := Nat.pos_of_mem_divisors (hF hf)
    have hle := single_le_sum (f := id) (fun a _ ↦ Nat.zero_le a) hd
    change q*f ≤ D.sum id at hle
    rw [hDsum] at hle
    exact (not_lt_of_ge ((Nat.le_mul_of_pos_right q hfpos).trans hle)) hR
  have hPos : N*q ≠ 0 := (mul_pos hN hq).ne'
  refine ⟨D ∪ F.map embed, ?_, ?_, ?_⟩
  · intro d hd
    rcases mem_union.mp hd with hd | hd
    · exact Nat.mem_divisors.mpr
        ⟨dvd_mul_of_dvd_left (Nat.dvd_of_mem_divisors (hD hd)) _, hPos⟩
    · obtain ⟨f, hf, rfl⟩ := mem_map.mp hd
      refine Nat.mem_divisors.mpr ⟨?_, hPos⟩
      change q*f ∣ N*q
      rw [Nat.mul_comm N q]
      exact Nat.mul_dvd_mul_left q (Nat.dvd_of_mem_divisors (hF hf))
  · rw [card_union_of_disjoint hDis, card_map]
    omega
  · rw [sum_union hDis, sum_map]
    change D.sum id + (∑ d ∈ F, q*d) = m
    rw [← Finset.mul_sum, hDsum]
    change r + q * (F.sum id) = m
    rw [hFsum, ← hEq]

theorem isPractical_two_pow (u : ℕ) : (2^u : ℕ).IsPractical := by
  induction u with
  | zero =>
    norm_num
    intro m hm
    interval_cases m
    · exact zero_mem_subsetSums _
    · exact ⟨{1}, by simp, by simp⟩
  | succ u ih =>
    rw [pow_succ]
    have hR : Short (2^u : ℕ) 2 1 := by
      intro m hm
      interval_cases m
      · exact ⟨∅, by simp, by simp, by simp⟩
      · exact ⟨{1}, by simp [Nat.mem_divisors], by simp, by simp⟩
    exact (short_mul (by positivity) (by decide) (short_of_practical ih) hR).practical

private theorem practical_mul_primes {N A : ℕ} (hN : 0 < N) (hA : 0 < A)
    (hPr : N.IsPractical) (hSmall : ∀ p, p.Prime → p ∣ A → p ≤ N+1) :
    (N*A).IsPractical := by
  induction A using Nat.strong_induction_on with
  | h A ih =>
    by_cases h1 : A = 1
    · simpa [h1] using hPr
    obtain ⟨p, hp, q, hq⟩ := Nat.exists_prime_and_dvd h1
    have hqPos : 0 < q := by
      by_contra! hq0
      have : q = 0 := by omega
      simp [this] at hq
      omega
    have hqLt : q < A := by
      rw [hq]
      simpa using Nat.mul_lt_mul_of_pos_right hp.one_lt hqPos
    have hqPr : (N*q).IsPractical :=
      ih q hqLt hqPos fun r hr hd ↦ hSmall r hr (hd.trans (hq ▸ Nat.dvd_mul_left q p))
    have hpD : p ∣ A := ⟨q, hq⟩
    have hlow : Short (N*q) p (Erdos18.practicalH N) := by
      apply Short.of_dvd (Nat.dvd_mul_right _ _) (by positivity)
      exact (short_of_practical hPr).restrict (hSmall p hp hpD)
    rw [hq, ← mul_assoc, mul_comm N p, mul_assoc, ← mul_comm (N*q) p]
    exact (short_mul (by positivity) hp.pos (short_of_practical hqPr) hlow).practical

theorem practical_of_pow_base {u A : ℕ} (hA : 0 < A)
    (hp : ∀ p, p.Prime → p ∣ A → p ≤ 2^u) : (2^u*A).IsPractical :=
  practical_mul_primes (by positivity) hA (isPractical_two_pow u)
    (fun p hprime hd ↦ (hp p hprime hd).trans (Nat.le_succ _))

private theorem exists_large_factor {A t : ℕ} (hLarge : 2^t ≤ A) (ht : 0 < t)
    (hPr : ∀ p, p.Prime → p ∣ A → p ≤ 2^t) :
    ∃ d, d ∣ A ∧ 2^t ≤ d ∧ d ≤ 2^(2*t) := by
  induction A using Nat.strong_induction_on with
  | h A ih =>
    have htwo : 2 ≤ (2:ℕ)^t := (by decide : 2 ≤ (2:ℕ)^1).trans
      (Nat.pow_le_pow_right (by decide) (by omega))
    obtain ⟨p, hp, q, hq⟩ := Nat.exists_prime_and_dvd
      (show A ≠ 1 by have := htwo.trans hLarge; omega)
    have hqPos : 0 < q := by
      by_contra! hq0
      have : q = 0 := by omega
      simp [this] at hq
      have := htwo.trans hLarge
      omega
    have hqLt : q < A := by
      rw [hq]
      simpa using Nat.mul_lt_mul_of_pos_right hp.one_lt hqPos
    by_cases hqL : 2^t ≤ q
    · obtain ⟨d, hd, hdlo, hdhi⟩ := ih q hqLt hqL
        (fun r hr hrd ↦ hPr r hr (hrd.trans (hq ▸ Nat.dvd_mul_left q p)))
      exact ⟨d, hd.trans (hq ▸ Nat.dvd_mul_left q p), hdlo, hdhi⟩
    · refine ⟨A, dvd_rfl, hLarge, ?_⟩
      calc
        A = p*q := hq
        _ ≤ 2^t * 2^t := Nat.mul_le_mul (hPr p hp ⟨q,hq⟩) (le_of_not_ge hqL)
        _ = _ := by rw [← pow_add, two_mul]

theorem prime_blocks {A t : ℕ} (hA : 0 < A) (ht : 0 < t)
    (hPr : ∀ p, p.Prime → p ∣ A → p ≤ 2^t) :
    ∃ B : List ℕ, B.prod = A ∧ B.length ≤ Nat.log 2 A / t + 1 ∧
      ∀ q ∈ B, 0 < q ∧ q ≤ 2^(2*t) := by
  induction A using Nat.strong_induction_on with
  | h A ih =>
    have htwo : 2 ≤ (2:ℕ)^t := (by decide : 2 ≤ (2:ℕ)^1).trans
      (Nat.pow_le_pow_right (by decide) (by omega))
    by_cases hLess : A < 2^t
    · refine ⟨[A], by simp, by simp, fun q hq ↦ ?_⟩
      simp only [List.mem_singleton] at hq
      subst q
      refine ⟨hA, hLess.le.trans (Nat.pow_le_pow_right (by decide) (by omega))⟩
    · obtain ⟨d, ⟨q,hq⟩, hdLo, hdHi⟩ := exists_large_factor (le_of_not_gt hLess) ht hPr
      have hqPos : 0 < q := by
        by_contra! hq0
        have : q = 0 := by omega
        simp [this] at hq
        omega
      have hd2 := htwo.trans hdLo
      have hqLt : q < A := by
        rw [hq]
        simpa using Nat.mul_lt_mul_of_pos_right (show 1 < d by omega) hqPos
      obtain ⟨B, hProd, hLen, hB⟩ := ih q hqLt hqPos
        (fun p hp hd ↦ hPr p hp (hd.trans (hq ▸ Nat.dvd_mul_left q d)))
      have hLog : t + Nat.log 2 q ≤ Nat.log 2 A := by
        apply Nat.le_log_of_pow_le (by decide)
        rw [pow_add, hq]
        exact Nat.mul_le_mul hdLo (Nat.pow_log_le_self _ hqPos.ne')
      have hDiv : Nat.log 2 q / t + 1 ≤ Nat.log 2 A / t := by
        apply (Nat.le_div_iff_mul_le ht).mpr
        rw [Nat.add_mul, one_mul, add_comm]
        exact (Nat.add_le_add_left (Nat.div_mul_le_self _ _) _).trans hLog
      refine ⟨d::B, by simp [hProd, hq], ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨by omega, hdHi⟩
        · exact hB p hp

theorem radix {M A t w : ℕ} (hM : 0 < M) (hPr : M.IsPractical) (hA : 0 < A)
    (ht : 0 < t) (hPrime : ∀ p, p.Prime → p ∣ A → p ≤ 2^t)
    (hSmall : Short M (2^(2*t)) w) :
    (M*A).IsPractical ∧
      Erdos18.practicalH (M*A) ≤ Erdos18.practicalH M + (Nat.log 2 A / t + 1)*w := by
  obtain ⟨B, rfl, hLen, hB⟩ := prime_blocks hA ht hPrime
  have transfer (C : List ℕ) (hC : ∀ q ∈ C, 0 < q ∧ q ≤ 2^(2*t)) :
    Short (M*C.prod) (M*C.prod+1) (Erdos18.practicalH M + C.length*w) := by
    induction C with
    | nil => simpa using short_of_practical hPr
    | cons q C ih =>
      have hq := hC q (List.mem_cons_self ..)
      have hC' : ∀ r ∈ C, 0 < r ∧ r ≤ 2^(2*t) := fun r hr ↦ hC r (List.mem_cons_of_mem q hr)
      have hCpos : 0 < C.prod := List.prod_pos (fun r hr ↦ (hC' r hr).1)
      have hNpos : 0 < M*C.prod := mul_pos hM hCpos
      have hLow : Short (M*C.prod) q w :=
        (hSmall.restrict hq.2).of_dvd (Nat.dvd_mul_right _ _) hNpos
      have hh := short_mul hNpos hq.1 (ih hC') hLow
      rw [List.prod_cons, List.length_cons, Nat.succ_mul, ← Nat.add_assoc, ← Nat.mul_left_comm,
        Nat.mul_comm q (M*C.prod)]
      exact hh
  have h := transfer B hB
  exact ⟨h.practical, h.practicalH_le.trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right w hLen) _)⟩

end E18Global

/-! # Changing the logarithm base in the bound for factorial divisor sums -/

namespace E18Global

open Filter

theorem real_fifth_of_fifth
    (h : ∃ C : ℕ, ∀ᶠ n : ℕ in atTop,
      Erdos18.practicalH n.factorial ≤ C * (Nat.log 2 n + 1) ^ 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (Erdos18.practicalH n.factorial : ℝ) ≤ C * (Real.log n) ^ (5 : ℕ) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨(C : ℝ) * 3 ^ 5, by positivity, ?_⟩
  have ht : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hC, eventually_ge_atTop (1 : ℕ),
    ht.eventually (eventually_ge_atTop (1 : ℝ))] with n hnBound hn hlog
  have hlog : (1 : ℝ) ≤ Real.log (n : ℝ) := hlog
  have hpow : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  have hlog₂ := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hlog₂
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hbase : (Nat.log 2 n : ℝ) + 1 ≤ 3 * Real.log n := by
    nlinarith only [hlog, hlog₂, mul_le_mul_of_nonneg_left hhalf
      (Nat.cast_nonneg (α := ℝ) (Nat.log 2 n))]
  calc
    (Erdos18.practicalH n.factorial : ℝ) ≤ C * ((Nat.log 2 n : ℝ) + 1) ^ 5 := by
      exact_mod_cast hnBound
    _ ≤ C * (3 * Real.log n) ^ 5 := by gcongr
    _ = (C : ℝ) * 3 ^ 5 * (Real.log n) ^ 5 := by rw [mul_pow, mul_assoc]

theorem strict_six_of_fifth
    (h : ∃ C : ℕ, ∀ᶠ n : ℕ in atTop,
      Erdos18.practicalH n.factorial ≤ C * (Nat.log 2 n + 1) ^ 5) :
    ∀ᶠ n : ℕ in atTop, (Erdos18.practicalH n.factorial : ℝ) < (Real.log n) ^ (6 : ℕ) := by
  obtain ⟨C, hC, hBound⟩ := real_fifth_of_fifth h
  have ht : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hBound, ht.eventually (eventually_gt_atTop C)] with n hn hlog
  have hlog : C < Real.log (n : ℝ) := hlog
  have hpos : 0 < Real.log (n : ℝ) := hC.trans_lt hlog
  calc
    (Erdos18.practicalH n.factorial : ℝ) ≤ C * (Real.log n) ^ (5 : ℕ) := hn
    _ < Real.log n * (Real.log n) ^ (5 : ℕ) := mul_lt_mul_of_pos_right hlog (by positivity)
    _ = (Real.log n) ^ (6 : ℕ) := by ring

end E18Global

/-! The factorial radix transfer from short exact sums in nested hosts. -/

namespace E18Global

open Filter

private theorem exponential_room_aux (t : ℕ) (ht : 16 ≤ t) : 2048 * t ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => decide
  | succ t ht ih =>
    rw [pow_succ]
    omega

private theorem exponential_room (u : ℕ) (hu : 32 ≤ u) : 512 * u ≤ 2 ^ (u / 2) := by
  have ha := exponential_room_aux (u / 2) (by omega)
  omega

private theorem log_factorial_le (n : ℕ) :
    Nat.log 2 n.factorial ≤ n * (Nat.log 2 n + 1) := by
  have h₁ := Nat.factorial_le_pow n
  have h₂ := Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le n
  have h₃ : n.factorial ≤ 2 ^ (n * (Nat.log 2 n + 1)) := by
    calc
      _ ≤ (2^(Nat.log 2 n + 1))^n := h₁.trans h₂
      _ = _ := by rw [← pow_mul, Nat.mul_comm n]
  simpa only [Nat.log_pow Nat.one_lt_two] using Nat.log_mono_right (b := 2) h₃

private theorem choose_host (n j₀ : ℕ) (hn : 2 ^ (j₀ + 8) ≤ n) :
    ∃ j, j₀ ≤ j ∧ 130 * 2 ^ j ≤ n ∧ n ≤ 512 * 2 ^ j ∧ j ≤ Nat.log 2 n := by
  have hlog := Nat.le_log_of_pow_le Nat.one_lt_two hn
  let j := Nat.log 2 n - 8
  have hcut : Nat.log 2 n = j + 8 := by dsimp [j]; omega
  have hpos : n ≠ 0 := by
    have : 0 < (2 : ℕ) ^ (j₀ + 8) := by positivity
    omega
  have h₁ := Nat.pow_log_le_self 2 hpos
  have h₂ := Nat.lt_pow_succ_log_self Nat.one_lt_two n
  rw [hcut, pow_add] at h₁
  rw [hcut, show (j+8).succ = j+9 by omega, pow_add] at h₂
  refine ⟨j, ?_, ?_, ?_, ?_⟩ <;> omega

private theorem sum_doublings (H : ℕ → ℕ) (C j₀ : ℕ)
    (step : ∀ j ≥ j₀, H (j+1) ≤ H j + C * (j+1)^4)
    (j : ℕ) (hj : j₀ ≤ j) : H j ≤ H j₀ + j * (C * (j+1)^4) := by
  induction j, hj using Nat.le_induction with
  | base => omega
  | succ j hj ih =>
    calc
      H (j+1) ≤ H j + C * (j+1)^4 := step j hj
      _ ≤ H j₀ + j * (C * (j+1)^4) + C * (j+1)^4 := Nat.add_le_add_right ih _
      _ = H j₀ + (j+1) * (C * (j+1)^4) := by ring
      _ ≤ H j₀ + (j+1) * (C * ((j+1)+1)^4) := by gcongr; omega

private theorem collapse_bound (B C K j x : ℕ) (hx : 1 ≤ x) (hj : j ≤ x) :
    B + j*(C*x^4) + (1536*x+1)*(K*x^4) ≤ (B+C+1537*K)*x^5 := by
  have hb : B ≤ B*x^5 := by
    calc B = B*1 := by simp
         _ ≤ B*x^5 := Nat.mul_le_mul_left _ (one_le_pow_of_one_le' hx 5)
  have hq : 1536*x+1 ≤ 1537*x := by omega
  calc
    _ ≤ B*x^5 + x*(C*x^4) + (1537*x)*(K*x^4) := by gcongr
    _ = _ := by ring

private theorem host_practical (u : ℕ) (hu : 32 ≤ u) : (host u).IsPractical := by
  apply practical_of_pow_base (Nat.lcmUpto_pos _)
  intro p hp hd
  have hp' : p ≤ 128*u := hp.dvd_factorial.mp (hd.trans (Nat.lcmUpto_dvd_factorial _))
  exact (by omega : p ≤ 512*u).trans ((exponential_room _ hu).trans
    (Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)))

private theorem double_bound {K u : ℕ} (hu : 32 ≤ u) (hP : (host u).IsPractical)
    (hl : Short (host u) (2^u) (K*(Nat.log 2 u+1)^4)) :
    Erdos18.practicalH (host (2*u)) ≤ Erdos18.practicalH (host u) +
      (6151*K)*(Nat.log 2 u+1)^4 := by
  obtain ⟨A, hA⟩ := host_dvd_host_double u
  have hAp : 0 < A := by
    by_contra! h
    have : A = 0 := by omega
    have := host_pos (2*u)
    simp_all
  have ha : A ≤ host (2*u) := by
    rw [hA]
    exact Nat.le_mul_of_pos_left _ (host_pos _)
  have hlog := (Nat.log_mono_right (b := 2) ha).trans (host_double_log_le u)
  have hblocks : Nat.log 2 A / (u/2) + 1 ≤ 6151 := by
    have := Nat.div_le_of_le_mul (show Nat.log 2 A ≤ (u/2)*6150 by omega)
    omega
  have prime : ∀ p, p.Prime → p ∣ A → p ≤ 2 ^ (u/2) := by
    intro p hp hd
    have hd' : p ∣ host (2*u) := hA ▸ dvd_mul_of_dvd_right hd _
    have := prime_le_of_dvd_host_double (by omega : 0 < u) hp hd'
    exact (by omega : p ≤ 512*u).trans (exponential_room u hu)
  have hshort := Short.restrict
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2*(u/2) ≤ u)) hl
  have h := (radix (host_pos _) hP hAp (by omega : 0 < u/2) prime hshort).2
  rw [← hA] at h
  calc
    _ ≤ _ := h
    _ ≤ Erdos18.practicalH (host u) + 6151*(K*(Nat.log 2 u+1)^4) := by gcongr
    _ = _ := by ring

private theorem top_bound {K n u : ℕ} (hu : 32 ≤ u) (hP : (host u).IsPractical)
    (hsmall : 130*u ≤ n) (hlarge : n ≤ 512*u)
    (hl : Short (host u) (2^u) (K*(Nat.log 2 u+1)^4)) :
    Erdos18.practicalH n.factorial ≤ Erdos18.practicalH (host u) +
      (1536*(Nat.log 2 n+1)+1)*(K*(Nat.log 2 u+1)^4) := by
  obtain ⟨A, hA⟩ := (host_dvd_factorial u).trans (Nat.factorial_dvd_factorial hsmall)
  have hAp : 0 < A := by
    by_contra! h
    have : A = 0 := by omega
    have := Nat.factorial_pos n
    simp_all
  have ha : A ≤ n.factorial := by
    rw [hA]
    exact Nat.le_mul_of_pos_left _ (host_pos _)
  have hlog := (Nat.log_mono_right (b := 2) ha).trans (log_factorial_le n)
  have hg : n ≤ (u/2)*1536 := by omega
  have hblocks : Nat.log 2 A / (u/2) ≤ 1536*(Nat.log 2 n+1) := by
    apply Nat.div_le_of_le_mul
    calc
      _ ≤ _ := hlog
      _ ≤ ((u/2)*1536)*(Nat.log 2 n+1) := Nat.mul_le_mul_right _ hg
      _ = _ := by ring
  have prime : ∀ p, p.Prime → p ∣ A → p ≤ 2 ^ (u/2) := by
    intro p hp hd
    have hd' : p ∣ n.factorial := hA ▸ dvd_mul_of_dvd_right hd _
    exact ((prime_le_of_dvd_factorial hp hd').trans hlarge).trans (exponential_room u hu)
  have hshort := Short.restrict
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2*(u/2) ≤ u)) hl
  have h := (radix (host_pos _) hP hAp (by omega : 0 < u/2) prime hshort).2
  rw [← hA] at h
  calc
    _ ≤ _ := h
    _ ≤ _ := by gcongr

theorem fifth_power_of_local (localBound :
    ∃ K u₀ : ℕ, ∀ u ≥ u₀, Short (host u) (2^u) (K*(Nat.log 2 u+1)^4)) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, Erdos18.practicalH n.factorial ≤ C*(Nat.log 2 n+1)^5 := by
  obtain ⟨K,u₀,hl⟩ := localBound
  let j₀ := u₀ + 32
  have hstart : ∀ j ≥ j₀, 32 ≤ 2^j ∧ u₀ ≤ 2^j := by
    intro j hj
    have h := Nat.lt_two_pow_self (n := j)
    dsimp [j₀] at hj
    omega
  let H := fun j : ℕ ↦ Erdos18.practicalH (host (2^j))
  have hstep : ∀ j ≥ j₀, H (j+1) ≤ H j + (6151*K)*(j+1)^4 := by
    intro j hj
    obtain ⟨hu,hu₀⟩ := hstart j hj
    have h := double_bound hu (host_practical _ hu) (hl _ hu₀)
    simpa only [H, pow_succ', Nat.log_pow Nat.one_lt_two] using h
  refine ⟨H j₀+6151*K+1537*K, ?_⟩
  filter_upwards [eventually_ge_atTop (2^(j₀+8))] with n hn
  obtain ⟨j,hj,hsmall,hlarge,hjn⟩ := choose_host n j₀ hn
  obtain ⟨hu,hu₀⟩ := hstart j hj
  have htop := top_bound hu (host_practical _ hu) hsmall hlarge (hl _ hu₀)
  rw [Nat.log_pow Nat.one_lt_two] at htop
  have hhost := sum_doublings H (6151*K) j₀ hstep j hj
  let x := Nat.log 2 n+1
  have hx : j+1 ≤ x := by dsimp [x]; omega
  calc
    _ ≤ H j + (1536*x+1)*(K*(j+1)^4) := htop
    _ ≤ H j₀ + j*((6151*K)*x^4) + (1536*x+1)*(K*x^4) := by
      have h₁ : H j ≤ H j₀ + j*((6151*K)*x^4) := hhost.trans (by gcongr)
      gcongr
    _ ≤ (H j₀+6151*K+1537*K)*x^5 :=
      collapse_bound _ _ _ _ _ (by dsimp [x]; omega) (by omega)

theorem strict_six_of_local (localBound :
    ∃ K u₀ : ℕ, ∀ u ≥ u₀, Short (host u) (2^u) (K*(Nat.log 2 u+1)^4)) :
    ∀ᶠ n : ℕ in atTop, (Erdos18.practicalH n.factorial : ℝ) < (Real.log n) ^ (6 : ℕ) :=
  strict_six_of_fifth (fifth_power_of_local localBound)

theorem erdos_18c_of_local (localBound :
    ∃ K u₀ : ℕ, ∀ u ≥ u₀, Short (host u) (2^u) (K*(Nat.log 2 u+1)^4)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (Erdos18.practicalH n.factorial : ℝ) < Real.log n ^ C := by
  refine ⟨(6 : ℕ), by norm_num, ?_⟩
  simpa only [Real.rpow_natCast] using strict_six_of_local localBound

end E18Global

namespace E18Global

private theorem lcmUpto_dvd_of_le {m n : ℕ} (h : m ≤ n) : Nat.lcmUpto m ∣ Nat.lcmUpto n := by
  unfold Nat.lcmUpto
  apply Finset.lcm_dvd
  intro i hi
  apply Finset.dvd_lcm
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans h⟩

private theorem good_two_pow (b a : ℕ) : Good b (2^a) :=
  ⟨a, 1, by decide, one_dvd _, by simp⟩

private theorem good_double (b x : ℕ) (h : Good b x) : Good b (2*x) := by
  obtain ⟨a, d, hp, hd, rfl⟩ := h
  exact ⟨a+1, d, hp, hd, by rw [pow_succ']; ring⟩

private theorem good_mono {k u x : ℕ} (hk : k ≤ u)
    (h : Good (Nat.lcmUpto (128*k)) x) : Good (Nat.lcmUpto (128*u)) x := by
  obtain ⟨a, d, hp, hd, rfl⟩ := h
  exact ⟨a, d, hp, hd.trans (lcmUpto_dvd_of_le (Nat.mul_le_mul_left 128 hk)), rfl⟩

private theorem good_dvd_host {x u : ℕ} (hx : x < 2^u)
    (h : Good (Nat.lcmUpto (128*u)) x) : x ∣ host u := by
  obtain ⟨a, d, hp, hd, rfl⟩ := h
  have ha := (Nat.le_mul_of_pos_right (2^a) hp).trans hx.le
  exact mul_dvd_mul (pow_dvd_pow _ ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp ha)) hd

private theorem complete_sum {u r w : ℕ} (hr : r < 2^u) (s : Multiset ℕ)
    (hc : s.card ≤ w) (he : s.sum = r)
    (hg : ∀ x ∈ s, x = 0 ∨ Good (Nat.lcmUpto (128*u)) x) :
    ∃ F : Finset ℕ, F ⊆ (host u).divisors ∧ F.card ≤ w ∧ F.sum id = r := by
  obtain ⟨F, hF, hsum, hgood⟩ := distinct_sum (good_double _) s hg
  refine ⟨F, ?_, hF.trans hc, hsum.trans he⟩
  intro x hx
  have hxle := Finset.single_le_sum (f := id) (fun a _ ↦ Nat.zero_le a) hx
  change x ≤ F.sum id at hxle
  exact Nat.mem_divisors.mpr ⟨good_dvd_host (hxle.trans_lt (by rwa [hsum, he])) (hgood x hx),
    (host_pos u).ne'⟩

/-- Exact small integers as short sums of distinct divisors of a nested host. -/
theorem local_exact : ∃ K u₀ : ℕ, ∀ u ≥ u₀, Short (host u) (2^u) (K*(Nat.log 2 u+1)^4) := by
  obtain ⟨A, hw⟩ := lift_width 258 3
  refine ⟨258+A, 0, fun u _ r hr ↦ ?_⟩
  by_cases hz : r = 0
  · exact ⟨∅, by simp, by simp, by simp [hz]⟩
  let v := Nat.log 2 r + 1
  have hrv : r < 2^v := Nat.lt_pow_succ_log_self Nat.one_lt_two _
  have hvu : v ≤ u := Nat.log_lt_of_lt_pow hz hr
  have hvfloor : 2^(v-1) ≤ r := by simpa [v] using Nat.pow_log_le_self 2 hz
  have hvCost : (Nat.log 2 v+1)^4 ≤ (Nat.log 2 u+1)^4 := by
    gcongr
  rcases hw v with hs | ⟨k, h3, hkv, hcap, htail⟩
  · obtain ⟨s, hcard, hsum, hbits⟩ := binary_lift (k := 0) (v := v) (by simpa using hrv)
    apply complete_sum hr s
    · simp only [Nat.sub_zero] at hcard
      rw [Nat.add_mul]
      exact (hcard.trans (hs.trans (Nat.mul_le_mul_left A hvCost))).trans (Nat.le_add_left _ _)
    · simpa using hsum
    · intro x hx
      obtain ⟨a, rfl⟩ := hbits x hx
      exact Or.inr (good_two_pow _ _)
  · obtain ⟨s, hcard, hdigits, hmod⟩ := localMod k r h3
    have hs : s.sum ≤ r := calc
      _ ≤ s.card * 2^k := Multiset.sum_le_card_nsmul s _ (fun x hx ↦ (hdigits x hx).1.le)
      _ ≤ (258 * (Nat.log 2 k + 1)^4) * 2^k := Nat.mul_le_mul_right _ hcard
      _ ≤ r := hcap.trans hvfloor
    obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' hs).mp hmod.symm
    have hsplit : s.sum + 2^k*q = r := by omega
    have hscale : 2^k*q < 2^k*2^(v-k) := by
      rw [← pow_add, Nat.add_sub_of_le hkv]
      omega
    have hqsmall : q < 2^(v-k) := Nat.lt_of_mul_lt_mul_left hscale
    obtain ⟨t, htcard, htsum, hbits⟩ := binary_lift (k := k) (v := v) hqsmall
    apply complete_sum hr (s+t)
    · rw [Multiset.card_add, Nat.add_mul]
      apply Nat.add_le_add
      · apply hcard.trans
        gcongr
        exact hkv.trans hvu
      · exact htcard.trans (htail.trans (Nat.mul_le_mul_left A hvCost))
    · rwa [Multiset.sum_add, htsum]
    · intro x hx
      rcases Multiset.mem_add.mp hx with hx | hx
      · exact (hdigits x hx).2.imp_right (good_mono (hkv.trans hvu))
      · obtain ⟨a, rfl⟩ := hbits x hx
        exact Or.inr (good_two_pow _ _)

theorem factorial_fifth : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in Filter.atTop,
    (Erdos18.practicalH n.factorial : ℝ) ≤ C * (Real.log n)^(5 : ℕ) :=
  real_fifth_of_fifth (fifth_power_of_local local_exact)

theorem factorial_polylog : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop,
    (Erdos18.practicalH n.factorial : ℝ) < Real.log n ^ C :=
  erdos_18c_of_local local_exact


end E18Global


/-! Erdős 18(b) follows from the quantitative factorial divisor bound.
Kohlmeyer and Kruer previously proved part (b) in *Short sums of factorial divisors
and Erdős Problem 18(b)* (September 2026). -/

namespace E18Global

open Filter

theorem factorial_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (Erdos18.practicalH n.factorial : ℝ) < (n : ℝ) ^ ε := by
  obtain ⟨C, _, hbound⟩ := factorial_fifth
  have h := ((isLittleO_log_rpow_rpow_atTop (5 : ℝ) hε).const_mul_left C).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hbound, h.def (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop (1 : ℕ)] with n hn hsmall hnpos
  have hpos : 0 < (n : ℝ) ^ ε := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) _
  have hnorm : |C * (Real.log n) ^ (5 : ℕ)| ≤ 1 / 2 * (n : ℝ) ^ ε := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos hpos,
      Real.rpow_ofNat] using hsmall
  exact hn.trans_lt ((le_abs_self _).trans_lt (hnorm.trans_lt (by linarith)))


end E18Global

theorem OMA.solution : type_of% @Erdos18.erdos_18b :=
  E18Global.factorial_subpolynomial
