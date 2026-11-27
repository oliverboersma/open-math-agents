import FormalConjectures.Wikipedia.SnakeInTheBox
import Mathlib
/-!
# Zémor's upper bound on the longest induced cycle in the hypercube

Formalization of Theorem 1.1 of Gilles Zémor, An upper bound on the size of the
snake-in-the-box, Combinatorica 17 (1997), 287–298, doi:10.1007/BF01200911.

An edge count reduces the result to a lower bound on the sum of the degrees in
the complement of the cycle. Short segments produce degree witnesses. Pairs
with a common witness give further contributions by translating the two
segments. The proof uses fixed blocks of 18 vertices to pack marked segments,
and accounts for the leftover vertices in the additive constant.
-/

namespace CoilBound

open SimpleGraph
open scoped symmDiff BigOperators

abbrev Cube (n : ℕ) := Finset (Fin n)

def flip {n : ℕ} (v : Cube n) (a : Fin n) : Cube n := v ∆ {a}

@[simp] lemma flip_flip {n : ℕ} (v : Cube n) (a : Fin n) :
    flip (flip v a) a = v := by simp [flip, symmDiff_symmDiff_cancel_right]

lemma flip_comm {n : ℕ} (v : Cube n) (a b : Fin n) :
    flip (flip v a) b = flip (flip v b) a := by rw [flip, flip, flip, flip, symmDiff_right_comm]

lemma flip_inj {n : ℕ} {v w : Cube n} {a : Fin n} :
    flip v a = flip w a ↔ v = w := symmDiff_left_inj

lemma label_inj {n : ℕ} {v : Cube n} {a b : Fin n} :
    flip v a = flip v b ↔ a = b := by simp [flip, symmDiff_right_inj]

lemma flip_ne {n : ℕ} (v : Cube n) (a : Fin n) : flip v a ≠ v := by
  simp [flip, symmDiff_eq_left]

lemma adj_iff {n : ℕ} {v w : Cube n} :
    (SnakeInBox.Hypercube n).Adj v w ↔ ∃ a : Fin n, flip v a = w := by
  rw [SnakeInBox.Hypercube, fromRel_adj]
  simp only [symmDiff_comm w v, or_self]
  constructor
  · rintro ⟨_, h⟩
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
    refine ⟨a, ?_⟩
    rw [flip, ← ha, symmDiff_symmDiff_cancel_left]
  · rintro ⟨a, rfl⟩
    refine ⟨(flip_ne v a).symm, ?_⟩
    simp [flip, symmDiff_symmDiff_cancel_left]

lemma adj_flip {n : ℕ} {v w : Cube n} (a : Fin n) :
    (SnakeInBox.Hypercube n).Adj (flip v a) (flip w a) ↔
      (SnakeInBox.Hypercube n).Adj v w := by
  simp only [adj_iff, flip_comm v a, flip_inj]

structure Coil (n L : ℕ) where
  length_min : 3 ≤ L
  vert : Fin L ↪ Cube n
  adj : ∀ i j : Fin L, (SnakeInBox.Hypercube n).Adj (vert i) (vert j) ↔
    (j.val = (i.val + 1) % L ∨ i.val = (j.val + 1) % L)

lemma exists_coil_of_walk {n : ℕ} {u : Cube n}
    (p : (SnakeInBox.Hypercube n).Walk u u) (hc : p.IsCycle) (hi : p.toSubgraph.IsInduced) :
    Nonempty (Coil n p.length) := by
  let v : Fin p.length ↪ Cube n := ⟨fun i => p.getVert i.val, by
    intro a b hab
    apply Fin.ext
    exact hc.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; have := a.isLt; omega) (by simp only [Set.mem_ofPred_eq]; have := b.isLt; omega) hab⟩
  have hmod (i : ℕ) (h : i < p.length) :
      p.getVert (i+1) = p.getVert ((i+1) % p.length) := by
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with heq | hlt
    · change i+1 = p.length at heq
      rw [heq, Nat.mod_self, p.getVert_length, p.getVert_zero]
    · rw [Nat.mod_eq_of_lt hlt]
  refine ⟨⟨hc.three_le_length, v, fun a b => ?_⟩⟩
  change (SnakeInBox.Hypercube n).Adj (p.getVert a) (p.getVert b) ↔ _
  have hl : 0 < p.length := by have := hc.three_le_length; omega
  constructor
  · intro h
    have ha := p.mem_verts_toSubgraph.mpr (p.getVert_mem_support a)
    have hb := p.mem_verts_toSubgraph.mpr (p.getVert_mem_support b)
    obtain ⟨i, he, hit⟩ := (p.toSubgraph_adj_iff).mp (hi ha hb h)
    rw [hmod i hit] at he
    rcases Sym2.eq_iff.mp he with ⟨ha', hb'⟩ | ⟨hb', ha'⟩
    · have h₁ : i = a.val := hc.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega) (by simp only [Set.mem_ofPred_eq]; have := a.isLt; omega) ha'
      have h₂ : (i+1) % p.length = b.val :=
        hc.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; have := Nat.mod_lt (i+1) hl; omega) (by simp only [Set.mem_ofPred_eq]; have := b.isLt; omega) hb'
      exact Or.inl (h₂.symm.trans (by rw [h₁]))
    · have h₁ : i = b.val := hc.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega) (by simp only [Set.mem_ofPred_eq]; have := b.isLt; omega) hb'
      have h₂ : (i+1) % p.length = a.val :=
        hc.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; have := Nat.mod_lt (i+1) hl; omega) (by simp only [Set.mem_ofPred_eq]; have := a.isLt; omega) ha'
      exact Or.inr (h₂.symm.trans (by rw [h₁]))
  · rintro (h | h)
    · rw [h, ← hmod a a.isLt]
      exact p.adj_getVert_succ a.isLt
    · rw [h, ← hmod b b.isLt]
      exact (p.adj_getVert_succ b.isLt).symm

variable {n L : ℕ} (C : Coil n L)

def Coil.index (i : ℤ) : Fin L :=
  ⟨(i % (L : ℤ)).toNat, by
    have hL : (0 : ℤ) < L := by have := C.length_min; omega
    have h₁ := Int.emod_nonneg i (ne_of_gt hL)
    have h₂ := Int.emod_lt_of_pos i hL
    omega⟩

def Coil.atPos (i : ℤ) : Cube n := C.vert (C.index i)

def Coil.inside : Finset (Cube n) := Finset.univ.map C.vert

lemma Coil.mem_inside_iff (v : Cube n) : v ∈ C.inside ↔ ∃ i : Fin L, C.vert i = v := by
  simp [Coil.inside]

@[simp] lemma Coil.atPos_mem (i : ℤ) : C.atPos i ∈ C.inside :=
  (C.mem_inside_iff _).mpr ⟨C.index i, rfl⟩

lemma Coil.index_nat (i : Fin L) : C.index i.val = i := by
  apply Fin.ext
  have h := i.isLt
  simp [Coil.index, Int.emod_eq_of_lt (by omega : 0 ≤ (i.val : ℤ)) (by omega : (i.val : ℤ) < L)]

lemma Coil.index_eq {i j : ℤ} : C.index i = C.index j ↔ i ≡ j [ZMOD (L : ℤ)] := by
  have hL : (0 : ℤ) < L := by have := C.length_min; omega
  have hi := Int.emod_nonneg i (ne_of_gt hL)
  have hj := Int.emod_nonneg j (ne_of_gt hL)
  change _ ↔ i % (L : ℤ) = j % (L : ℤ)
  rw [← Fin.val_inj]
  change (i % (L : ℤ)).toNat = (j % (L : ℤ)).toNat ↔ _
  omega

lemma Coil.atPos_eq {i j : ℤ} : C.atPos i = C.atPos j ↔ i ≡ j [ZMOD (L : ℤ)] := by
  rw [Coil.atPos, Coil.atPos, C.vert.injective.eq_iff, C.index_eq]

lemma Coil.index_succ (i : ℤ) : (C.index (i+1)).val = ((C.index i).val+1) % L := by
  have hL : (0 : ℤ) < L := by have := C.length_min; omega
  have hi : 0 ≤ i % (L : ℤ) := Int.emod_nonneg i (ne_of_gt hL)
  have hconv : (((i % (L : ℤ)).toNat + 1 : ℕ) : ℤ) = i % (L : ℤ) + 1 := by omega
  change ((i+1) % (L : ℤ)).toNat = ((i % (L : ℤ)).toNat+1) % L
  rw [← Int.toNat_natCast (((i % (L : ℤ)).toNat+1) % L), Int.natCast_emod, hconv]
  congr 1
  rw [Int.add_emod i 1, Int.add_emod (i % (L : ℤ)) 1, Int.emod_emod]

lemma Coil.adj_atPos {i j : ℤ} :
    (SnakeInBox.Hypercube n).Adj (C.atPos i) (C.atPos j) ↔
      (j ≡ i+1 [ZMOD (L : ℤ)] ∨ i ≡ j+1 [ZMOD (L : ℤ)]) := by
  rw [Coil.atPos, Coil.atPos, C.adj, ← C.index_succ, ← C.index_succ]
  simp only [Fin.val_inj, C.index_eq]

lemma Coil.adj_succ (i : ℤ) :
    (SnakeInBox.Hypercube n).Adj (C.atPos i) (C.atPos (i+1)) :=
  C.adj_atPos.mpr (Or.inl (Int.ModEq.refl _))

lemma Coil.flip_inside_iff (i : ℤ) (a : Fin n) :
    flip (C.atPos i) a ∈ C.inside ↔
      flip (C.atPos i) a = C.atPos (i-1) ∨ flip (C.atPos i) a = C.atPos (i+1) := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := (C.mem_inside_iff _).mp h
    have he : C.atPos (j.val : ℤ) = flip (C.atPos i) a := by
      simpa [Coil.atPos, C.index_nat] using hj
    have ha : (SnakeInBox.Hypercube n).Adj (C.atPos i) (C.atPos (j.val : ℤ)) :=
      adj_iff.mpr ⟨a, he.symm⟩
    rcases C.adj_atPos.mp ha with hsucc | hprev
    · exact Or.inr (he.symm.trans (C.atPos_eq.mpr hsucc))
    · apply Or.inl
      rw [← he]
      apply C.atPos_eq.mpr
      have h := hprev.symm.sub (Int.ModEq.refl (1 : ℤ))
      convert h using 1 <;> ring
  · rintro (h | h) <;> rw [h] <;> exact C.atPos_mem _

def Coil.outside : Finset (Cube n) := Finset.univ \ C.inside

def Coil.degree (v : Cube n) : ℕ :=
  (Finset.univ.filter fun a : Fin n => flip v a ∈ C.outside).card

def Coil.totalDegree : ℕ := ∑ v ∈ C.outside, C.degree v

@[simp] lemma Coil.mem_outside {v : Cube n} : v ∈ C.outside ↔ v ∉ C.inside := by
  simp [Coil.outside]

lemma Coil.degree_le (v : Cube n) : C.degree v ≤ n := by
  simpa [Coil.degree] using
     (Finset.card_filter_le (s := (Finset.univ : Finset (Fin n)))
          (p := fun a => flip v a ∈ C.outside))

end CoilBound


/- Edge counting on an induced cycle and its complement. -/

namespace CoilBound

open SimpleGraph Finset
open scoped symmDiff BigOperators

variable {n L : ℕ} (C : Coil n L)

lemma no_mod_gap {a b m : ℤ} (ha : a < b) (hb : b-a < m) : ¬ a ≡ b [ZMOD m] := by
  intro he
  have h0 := Int.emod_eq_zero_of_dvd he.dvd
  rw [Int.emod_eq_of_lt (by omega : 0 ≤ b-a) hb] at h0
  omega

lemma Coil.pos_ne {a b : ℤ} (ha : a < b) (hb : b-a < L) : C.atPos a ≠ C.atPos b :=
  fun he => no_mod_gap ha hb (C.atPos_eq.mp he)

lemma Coil.no_chord {a b : ℤ} (ha : a+2 ≤ b) (hb : b-a ≤ (L : ℤ)-2) :
    ¬ (SnakeInBox.Hypercube n).Adj (C.atPos a) (C.atPos b) := by
  intro h
  rcases C.adj_atPos.mp h with he | he
  · exact no_mod_gap (a := a+1) (b := b) (by omega) (by omega) he.symm
  · exact no_mod_gap (a := a) (b := b+1) (by omega) (by omega) he

noncomputable def Coil.step (i : ℤ) : Fin n :=
  Classical.choose (adj_iff.mp (C.adj_succ i))

lemma Coil.flip_step (i : ℤ) : flip (C.atPos i) (C.step i) = C.atPos (i+1) :=
  Classical.choose_spec (adj_iff.mp (C.adj_succ i))

lemma Coil.flip_prev (i : ℤ) : flip (C.atPos i) (C.step (i-1)) = C.atPos (i-1) := by
  have h := congrArg (fun v => flip v (C.step (i-1))) (C.flip_step (i-1))
  simp only [sub_add_cancel, flip_flip] at h
  exact h.symm

lemma Coil.flip_not_mem (i : ℤ) (a : Fin n) :
    flip (C.atPos i) a ∈ C.outside ↔ a ≠ C.step (i-1) ∧ a ≠ C.step i := by
  rw [C.mem_outside, C.flip_inside_iff, ← C.flip_prev i, ← C.flip_step i]
  simp [label_inj]

lemma Coil.distinct_steps (i : ℤ) : C.step i ≠ C.step (i+1) := by
  intro he
  have h := (C.flip_step (i+1)).symm
  rw [← he, ← C.flip_step i, flip_flip] at h
  exact C.pos_ne (a := i) (b := i+1+1) (by omega)
    (by have := C.length_min; omega) h.symm

lemma Coil.distinct_steps_two (hL : 5 ≤ L) (i : ℤ) : C.step i ≠ C.step (i+1+1) := by
  intro he
  have h := (C.flip_step (i+1+1)).symm
  rw [← he, ← C.flip_step (i+1), ← C.flip_step i, flip_comm (flip _ _) (C.step (i+1)) (C.step i),
    flip_flip] at h
  exact C.no_chord (a := i) (b := i+1+1+1) (by omega) (by omega)
    (adj_iff.mpr ⟨C.step (i+1), h.symm⟩)

lemma Coil.no_three_inside {u v w x : Cube n} (hu : u ∈ C.inside)
    (hv : v ∈ C.inside) (hw : w ∈ C.inside) (hx : x ∈ C.inside)
    (ha : (SnakeInBox.Hypercube n).Adj u v) (hb : (SnakeInBox.Hypercube n).Adj u w)
    (hc : (SnakeInBox.Hypercube n).Adj u x) (hvw : v ≠ w) (hvx : v ≠ x) (hwx : w ≠ x) : False := by
  obtain ⟨i, rfl⟩ := (C.mem_inside_iff u).mp hu
  have hi : C.atPos (i.val : ℤ) = C.vert i := by simp [Coil.atPos, C.index_nat]
  rw [← hi] at ha hb hc
  obtain ⟨a, rfl⟩ := adj_iff.mp ha
  obtain ⟨b, rfl⟩ := adj_iff.mp hb
  obtain ⟨c, rfl⟩ := adj_iff.mp hc
  rcases (C.flip_inside_iff _ _).mp hv with hv | hv <;>
    rcases (C.flip_inside_iff _ _).mp hw with hw | hw <;>
    rcases (C.flip_inside_iff _ _).mp hx with hx | hx <;> aesop

lemma Coil.star_degree {u v w x : Cube n}
    (ha : (SnakeInBox.Hypercube n).Adj u v) (hb : (SnakeInBox.Hypercube n).Adj u w)
    (hc : (SnakeInBox.Hypercube n).Adj u x)
    (hvw : v ≠ w) (hvx : v ≠ x) (hwx : w ≠ x) :
    n ≤ C.degree u + C.degree v + C.degree w + C.degree x := by
  let T (z : Cube n) := (univ : Finset (Fin n)).filter fun a => flip z a ∈ C.outside
  have hcover : univ ⊆ T u ∪ T v ∪ T w ∪ T x := by
    intro a _
    by_contra hn
    simp only [mem_union, T, mem_filter, mem_univ, true_and, C.mem_outside, not_or,
      not_not] at hn
    exact C.no_three_inside hn.1.1.1 hn.1.1.2 hn.1.2 hn.2
      ((adj_flip a).mpr ha) ((adj_flip a).mpr hb) ((adj_flip a).mpr hc)
      (fun h => hvw (flip_inj.mp h)) (fun h => hvx (flip_inj.mp h))
      (fun h => hwx (flip_inj.mp h))
  have h0 := card_le_card hcover
  have h1 := card_union_le (T u ∪ T v ∪ T w) (T x)
  have h2 := card_union_le (T u ∪ T v) (T w)
  have h3 := card_union_le (T u) (T v)
  simp only [card_univ, Fintype.card_fin] at h0
  change n ≤ (T u).card + (T v).card + (T w).card + (T x).card
  omega

lemma Coil.star_heavy {u : Cube n} {a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    n ≤ 4 * C.degree u ∨ n ≤ 4 * C.degree (flip u a) ∨
      n ≤ 4 * C.degree (flip u b) ∨ n ≤ 4 * C.degree (flip u c) := by
  have h := C.star_degree (u := u) (adj_iff.mpr ⟨a, rfl⟩) (adj_iff.mpr ⟨b, rfl⟩)
    (adj_iff.mpr ⟨c, rfl⟩) (fun h => hab (label_inj.mp h))
    (fun h => hac (label_inj.mp h)) (fun h => hbc (label_inj.mp h))
  omega

lemma Coil.degree_inside (i : ℤ) : C.degree (C.atPos i) = n - 2 := by
  have hne : C.step (i-1) ≠ C.step i := by
    simpa only [sub_add_cancel] using C.distinct_steps (i-1)
  let t : Finset (Fin n) := {C.step (i-1), C.step i}
  have ht : t.card = 2 := by simp [t, hne]
  have h : univ.filter (fun a : Fin n => flip (C.atPos i) a ∈ C.outside) = univ \ t := by
    ext a
    simp [t, C.flip_not_mem, not_or]
  rw [Coil.degree, h, card_sdiff_of_subset (subset_univ _), ht, card_univ, Fintype.card_fin]

lemma Coil.card_inside : C.inside.card = L := by
  simp [Coil.inside]

lemma Coil.card_outside : C.outside.card = 2 ^ n - L := by
  rw [Coil.outside, card_sdiff_of_subset (subset_univ _), C.card_inside, card_univ,
    Fintype.card_finset, Fintype.card_fin]

def Coil.mixedOut : Finset (Cube n × Fin n) :=
  (C.outside ×ˢ univ).filter fun q => flip q.1 q.2 ∈ C.inside

def Coil.mixedIn : Finset (Cube n × Fin n) :=
  (C.inside ×ˢ univ).filter fun q => flip q.1 q.2 ∈ C.outside

lemma Coil.card_mixed_eq : C.mixedOut.card = C.mixedIn.card := by
  let f (q : Cube n × Fin n) : Cube n × Fin n := (flip q.1 q.2, q.2)
  have hff (q : Cube n × Fin n) : f (f q) = q := by
    rcases q with ⟨v,a⟩
    simp [f]
  refine card_nbij' (s := C.mixedOut) (t := C.mixedIn) f f ?_ ?_ (fun q _ => hff q)
    (fun q _ => hff q)
  · intro q h
    simp only [Finset.mem_coe, Coil.mixedOut, mem_filter, mem_product, mem_univ, and_true] at h
    simpa only [Finset.mem_coe, Coil.mixedIn, mem_filter, mem_product, mem_univ, and_true, f,
      flip_flip] using h.symm
  · intro q h
    simp only [Finset.mem_coe, Coil.mixedIn, mem_filter, mem_product, mem_univ, and_true] at h
    simpa only [Finset.mem_coe, Coil.mixedOut, mem_filter, mem_product, mem_univ, and_true, f,
      flip_flip] using h.symm

lemma card_filter_product {α β : Type*} (s : Finset α) (t : Finset β)
    (P : α → β → Prop) [DecidableRel P] :
    ((s ×ˢ t).filter fun q => P q.1 q.2).card = ∑ a ∈ s, (t.filter (P a)).card := by
  classical
  rw [card_eq_sum_ones]
  simp only [sum_filter, sum_product, card_eq_sum_ones]

lemma Coil.totalDegree_identity :
    L * (n - 2) + C.totalDegree + L * n = 2 ^ n * n := by
  have hIn : C.mixedIn.card = L * (n-2) := by
    rw [Coil.mixedIn, card_filter_product C.inside univ (fun v (a : Fin n) => flip v a ∈ C.outside)]
    change (∑ v ∈ C.inside, C.degree v) = _
    have hdeg (v : Cube n) (hv : v ∈ C.inside) : C.degree v = n - 2 := by
      obtain ⟨i, rfl⟩ := (C.mem_inside_iff v).mp hv
      simpa [Coil.atPos, C.index_nat] using C.degree_inside (i.val : ℤ)
    rw [sum_congr rfl hdeg]
    simp [C.card_inside]
  have hOut : C.mixedOut.card + C.totalDegree = (2^n-L)*n := by
    rw [Coil.mixedOut, card_filter_product C.outside univ (fun v (a : Fin n) => flip v a ∈ C.inside),
      Coil.totalDegree, ← sum_add_distrib]
    calc
      (∑ x ∈ C.outside, ((univ.filter fun a : Fin n => flip x a ∈ C.inside).card + C.degree x))
          = ∑ _x ∈ C.outside, n := by
            apply sum_congr rfl
            intro x hx
            simpa [Coil.degree] using
              (card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
                (p := fun a => flip x a ∈ C.inside))
      _ = _ := by simp [C.card_outside]
  have hL : L ≤ 2^n := by simpa [C.card_inside, Fintype.card_finset] using
    (card_le_univ C.inside : C.inside.card ≤ Fintype.card (Cube n))
  rw [C.card_mixed_eq, hIn] at hOut
  rw [hOut, ← Nat.add_mul, Nat.sub_add_cancel hL]

end CoilBound

/- Local external stars in short segments of a coil. -/

namespace CoilBound

open SimpleGraph Finset
open scoped symmDiff BigOperators

variable {n L : ℕ} (C : Coil n L)

lemma Coil.near_steps_ne (hL : 5 ≤ L) {i j : ℤ} (h1 : i+1 ≤ j) (h2 : j ≤ i+2) :
    C.step i ≠ C.step j := by
  by_cases h : j = i+1
  · rw [h]
    exact C.distinct_steps i
  · have h' : j = i+1+1 := by omega
    rw [h']
    exact C.distinct_steps_two hL i

def Coil.mark (i j : ℤ) : Prop :=
  flip (C.atPos i) (C.step j) ∈ C.outside ∧
    n ≤ 4 * C.degree (flip (C.atPos i) (C.step j))

def Coil.markIn (p q : ℤ) : Prop :=
  ∃ i j : ℤ, p ≤ i ∧ i ≤ q ∧ p ≤ j ∧ j < q ∧ i-6 ≤ j ∧ j ≤ i+5 ∧ C.mark i j

lemma Coil.markIn_mono {p q p' q' : ℤ} (hp : p' ≤ p) (hq : q ≤ q')
    (h : C.markIn p q) : C.markIn p' q' := by
  obtain ⟨i,j,hi,hii,hj,hjj,hl,hr,hm⟩ := h
  exact ⟨i,j,by omega,by omega,by omega,by omega,hl,hr,hm⟩

lemma Coil.mark_from {p q i j : ℤ} (hp : p ≤ i) (hq : i ≤ q)
    (hp' : p ≤ j) (hq' : j < q) (hnear : i-6 ≤ j ∧ j ≤ i+5)
    (ho : flip (C.atPos i) (C.step j) ∈ C.outside)
    (hh : n ≤ 4 * C.degree (flip (C.atPos i) (C.step j))) : C.markIn p q :=
  ⟨i,j,hp,hq,hp',hq',hnear.1,hnear.2,ho,hh⟩

lemma Coil.offs_step (p k : ℤ) :
    C.atPos (p+(k+1)) = flip (C.atPos (p+k)) (C.step (p+k)) := by
  rw [← add_assoc, C.flip_step]

lemma Coil.offs_outside (p i : ℤ) (a : Fin n) :
    flip (C.atPos (p+i)) a ∈ C.outside ↔
      a ≠ C.step (p+(i-1)) ∧ a ≠ C.step (p+i) := by
  rw [C.flip_not_mem]
  have h : p+i-1 = p+(i-1) := by ring
  rw [h]

set_option maxHeartbeats 400000 in
lemma Coil.four_edge_mark (hL : 9 ≤ L) (p : ℤ) (had : C.step p ≠ C.step (p+3)) :
    C.markIn p (p+4) ∨
      (C.step (p-1) = C.step (p+3) ∧ C.step (p+4) = C.step p) ∨
      (C.step (p-1) = C.step (p+2) ∧ C.step (p+4) = C.step (p+1)) := by
  let v (i : ℤ) := C.atPos (p+i)
  let e (i : ℤ) := C.step (p+i)
  let x := e (-1)
  let a := e 0
  let b := e 1
  let c := e 2
  let d := e 3
  let y := e 4
  have hab : a ≠ b := C.near_steps_ne (i := p+0) (j := p+1) (by omega) (by omega) (by omega)
  have hbc : b ≠ c := C.near_steps_ne (i := p+1) (j := p+2) (by omega) (by omega) (by omega)
  have hcd : c ≠ d := C.near_steps_ne (i := p+2) (j := p+3) (by omega) (by omega) (by omega)
  have hac : a ≠ c := C.near_steps_ne (i := p+0) (j := p+2) (by omega) (by omega) (by omega)
  have hbd : b ≠ d := C.near_steps_ne (i := p+1) (j := p+3) (by omega) (by omega) (by omega)
  have had' : a ≠ d := by simpa only [a,d,e,add_zero] using had
  have hxb : x ≠ b := C.near_steps_ne (i := p+(-1)) (j := p+1) (by omega) (by omega) (by omega)
  have hyc : y ≠ c := (C.near_steps_ne (i := p+2) (j := p+4) (by omega) (by omega) (by omega)).symm
  have h1 : v 1 = flip (v 0) a := C.offs_step p 0
  have h2 : v 2 = flip (v 1) b := C.offs_step p 1
  have h3 : v 3 = flip (v 2) c := C.offs_step p 2
  have h4 : v 4 = flip (v 3) d := C.offs_step p 3
  have mark (i j : ℤ) (hi : 0 ≤ i ∧ i ≤ 4) (hj : 0 ≤ j ∧ j < 4)
      (ho : flip (v i) (e j) ∈ C.outside)
      (hh : n ≤ 4 * C.degree (flip (v i) (e j))) : C.markIn p (p+4) :=
    C.mark_from (i := p+i) (j := p+j) (by omega) (by omega) (by omega) (by omega)
      (by omega) ho hh
  by_cases hxd : x = d
  · by_cases hya : y = a
    · right
      left
      simpa only [x,d,y,a,e,add_zero,sub_eq_add_neg] using And.intro hxd hya
    · left
      have hout0 : flip (v 0) b ∈ C.outside := (C.offs_outside p 0 b).mpr ⟨hxb.symm, hab.symm⟩
      have hout1 : flip (v 0) c ∈ C.outside := by
        apply (C.offs_outside p 0 c).mpr
        refine ⟨?_, hac.symm⟩
        change c ≠ x
        rw [hxd]
        exact hcd
      have hout3 : flip (v 3) a ∈ C.outside := (C.offs_outside p 3 a).mpr ⟨hac, had'⟩
      have hout4 : flip (v 4) a ∈ C.outside := (C.offs_outside p 4 a).mpr ⟨had', (Ne.symm hya)⟩
      have hfa : flip (flip (v 3) a) d = flip (v 4) a := by rw [h4, flip_comm]
      have hfb : flip (flip (v 3) a) b = flip (v 0) c := by
        rw [h3,h2,h1]
        calc
          _ = flip (flip (flip (flip (flip (v 0) a) a) b) b) c := by unfold flip; ac_rfl
          _ = _ := by simp
      have hfc : flip (flip (v 3) a) c = flip (v 0) b := by
        rw [h3,h2,h1]
        calc
          _ = flip (flip (flip (flip (flip (v 0) a) a) c) c) b := by unfold flip; ac_rfl
          _ = _ := by simp
      rcases C.star_heavy (u := flip (v 3) a) hbd.symm hcd.symm hbc with h | h | h | h
      · exact mark 3 0 (by norm_num) (by norm_num) hout3 h
      · exact mark 4 0 (by norm_num) (by norm_num) hout4 (hfa ▸ h)
      · exact mark 0 2 (by norm_num) (by norm_num) hout1 (hfb ▸ h)
      · exact mark 0 1 (by norm_num) (by norm_num) hout0 (hfc ▸ h)
  · by_cases hyb : y = b
    · by_cases hxc : x = c
      · right
        right
        simpa only [x,c,y,b,e,sub_eq_add_neg] using And.intro hxc hyb
      · left
        have hout0 : flip (v 0) b ∈ C.outside := (C.offs_outside p 0 b).mpr ⟨hxb.symm, hab.symm⟩
        have hout1 : flip (v 0) c ∈ C.outside := (C.offs_outside p 0 c).mpr ⟨(Ne.symm hxc), hac.symm⟩
        have hout3 : flip (v 3) a ∈ C.outside := (C.offs_outside p 3 a).mpr ⟨hac, had'⟩
        have hout4 : flip (v 4) a ∈ C.outside := by
          apply (C.offs_outside p 4 a).mpr
          refine ⟨had', ?_⟩
          change a ≠ y
          rwa [hyb]
        have hfa : flip (flip (v 3) a) d = flip (v 4) a := by rw [h4, flip_comm]
        have hfb : flip (flip (v 3) a) b = flip (v 0) c := by
          rw [h3,h2,h1]
          calc
            _ = flip (flip (flip (flip (flip (v 0) a) a) b) b) c := by unfold flip; ac_rfl
            _ = _ := by simp
        have hfc : flip (flip (v 3) a) c = flip (v 0) b := by
          rw [h3,h2,h1]
          calc
            _ = flip (flip (flip (flip (flip (v 0) a) a) c) c) b := by unfold flip; ac_rfl
            _ = _ := by simp
        rcases C.star_heavy (u := flip (v 3) a) hbd.symm hcd.symm hbc with h | h | h | h
        · exact mark 3 0 (by norm_num) (by norm_num) hout3 h
        · exact mark 4 0 (by norm_num) (by norm_num) hout4 (hfa ▸ h)
        · exact mark 0 2 (by norm_num) (by norm_num) hout1 (hfb ▸ h)
        · exact mark 0 1 (by norm_num) (by norm_num) hout0 (hfc ▸ h)
    · left
      have hout0 : flip (v 0) d ∈ C.outside := (C.offs_outside p 0 d).mpr ⟨(Ne.symm hxd), had'.symm⟩
      have hout1 : flip (v 1) d ∈ C.outside := (C.offs_outside p 1 d).mpr ⟨had'.symm, hbd.symm⟩
      have houtb : flip (v 4) b ∈ C.outside := (C.offs_outside p 4 b).mpr ⟨hbd, (Ne.symm hyb)⟩
      have houtc : flip (v 4) c ∈ C.outside := (C.offs_outside p 4 c).mpr ⟨hcd, hyc.symm⟩
      have hf0 : flip (flip (v 1) d) a = flip (v 0) d := by
        rw [flip_comm (v 1), h1, flip_flip]
      have hfb : flip (flip (v 1) d) c = flip (v 4) b := by
        rw [h4,h3,h2]
        symm
        calc
          _ = flip (flip (flip (flip (v 1) b) b) d) c := by unfold flip; ac_rfl
          _ = _ := by simp
      have hfc : flip (flip (v 1) d) b = flip (v 4) c := by
        rw [h4,h3,h2]
        symm
        calc
          _ = flip (flip (flip (flip (v 1) c) c) d) b := by unfold flip; ac_rfl
          _ = _ := by simp
      rcases C.star_heavy (u := flip (v 1) d) hac hab hbc.symm with h | h | h | h
      · exact mark 1 3 (by norm_num) (by norm_num) hout1 h
      · exact mark 0 3 (by norm_num) (by norm_num) hout0 (hf0 ▸ h)
      · exact mark 4 1 (by norm_num) (by norm_num) houtb (hfb ▸ h)
      · exact mark 4 2 (by norm_num) (by norm_num) houtc (hfc ▸ h)

set_option maxHeartbeats 600000 in
lemma Coil.six_edge_mark (hL : 9 ≤ L) (p : ℤ) (had : C.step p ≠ C.step (p+3)) :
    C.markIn p (p+6) := by
  let v (i : ℤ) := C.atPos (p+i)
  let e (i : ℤ) := C.step (p+i)
  let x := e (-1)
  let a := e 0
  let b := e 1
  let c := e 2
  let d := e 3
  let y := e 4
  let z := e 5
  have h1 : v 1 = flip (v 0) a := C.offs_step p 0
  have h2 : v 2 = flip (v 1) b := C.offs_step p 1
  have h3 : v 3 = flip (v 2) c := C.offs_step p 2
  have h4 : v 4 = flip (v 3) d := C.offs_step p 3
  have h5 : v 5 = flip (v 4) y := C.offs_step p 4
  have h6 : v 6 = flip (v 5) z := C.offs_step p 5
  have h0 : v 0 = flip (v (-1)) x := by simpa [v,x,e] using C.offs_step p (-1)
  have noEnd (r : Fin n) : v 6 ≠ flip (v (-1)) r := by
    intro he
    apply C.no_chord (a := p-1) (b := p+6) (by omega) (by omega)
    exact adj_iff.mpr ⟨r, by simpa only [v, sub_eq_add_neg] using he.symm⟩
  have noMiddle (r : Fin n) : v 6 ≠ flip (v 1) r := by
    intro he
    apply C.no_chord (a := p+1) (b := p+6) (by omega) (by omega)
    exact adj_iff.mpr ⟨r, he.symm⟩
  rcases C.four_edge_mark hL p had with hm | ⟨hxold, hyold⟩ | ⟨hxold,hyold⟩
  · exact C.markIn_mono le_rfl (by omega) hm
  · have hx : x = d := by simpa only [x,d,e,sub_eq_add_neg] using hxold
    have hy : y = a := by simpa only [y,a,e,add_zero] using hyold
    have hshift : C.step (p+1) ≠ C.step (p+1+3) := by
      have h : b ≠ a := by simpa [a,b,e] using (C.distinct_steps p).symm
      have h' : b ≠ y := by simpa only [hy] using h
      change C.step (p+1) ≠ C.step (p+1+3)
      convert h' using 2 <;> ring
    have hzb : z ≠ b := by
      intro hz
      apply noEnd c
      rw [h6,h5,h4,h3,h2,h1,h0,hx,hy,hz]
      calc
        _ = flip (flip (flip (flip (flip (flip (flip (v (-1)) a) a) b) b) d) d) c := by
          unfold flip
          ac_rfl
        _ = _ := by simp
    rcases C.four_edge_mark hL (p+1) hshift with hm | ⟨_,hh⟩ | ⟨hh,_⟩
    · exact C.markIn_mono (by omega) (by omega) hm
    · exfalso
      apply hzb
      convert hh using 2 <;> ring
    · exfalso
      apply had
      convert hh using 2 <;> ring
  · have hx : x = c := by simpa only [x,c,e,sub_eq_add_neg] using hxold
    have hy : y = b := by simpa only [y,b,e] using hyold
    have hza : z ≠ a := by
      intro hz
      apply noEnd d
      rw [h6,h5,h4,h3,h2,h1,h0,hx,hy,hz]
      calc
        _ = flip (flip (flip (flip (flip (flip (flip (v (-1)) a) a) b) b) c) c) d := by
          unfold flip
          ac_rfl
        _ = _ := by simp
    have hzc : z ≠ c := by
      intro hz
      apply noMiddle d
      rw [h6,h5,h4,h3,h2,hy,hz]
      calc
        _ = flip (flip (flip (flip (flip (v 1) b) b) c) c) d := by unfold flip; ac_rfl
        _ = _ := by simp
    have hzb : z ≠ b := by
      have h : z ≠ y := (C.near_steps_ne (i := p+4) (j := p+5) (by omega) (by omega) (by omega)).symm
      exact hy ▸ h
    have hzd : z ≠ d := (C.near_steps_ne (i := p+3) (j := p+5) (by omega) (by omega) (by omega)).symm
    have hab : a ≠ b := by simpa [a,b,e] using C.distinct_steps p
    have hac : a ≠ c := C.near_steps_ne (i := p+0) (j := p+2) (by omega) (by omega) (by omega)
    have hbc : b ≠ c := C.near_steps_ne (i := p+1) (j := p+2) (by omega) (by omega) (by omega)
    have hbd : b ≠ d := C.near_steps_ne (i := p+1) (j := p+3) (by omega) (by omega) (by omega)
    have hcd : c ≠ d := C.near_steps_ne (i := p+2) (j := p+3) (by omega) (by omega) (by omega)
    have had' : a ≠ d := by simpa only [a,d,e,add_zero] using had
    have hf0 : flip (flip (v 1) z) a = flip (v 0) z := by
      rw [flip_comm (v 1), h1, flip_flip]
    have hf2 : flip (flip (v 1) z) b = flip (v 2) z := by rw [h2, flip_comm]
    have hfc : flip (flip (v 1) z) c = flip (v 6) d := by
      rw [h6,h5,h4,h3,h2,hy]
      symm
      calc
        _ = flip (flip (flip (flip (flip (flip (v 1) b) b) d) d) z) c := by
          unfold flip
          ac_rfl
        _ = _ := by simp
    have hfd : flip (flip (v 1) z) d = flip (v 6) c := by
      rw [h6,h5,h4,h3,h2,hy]
      symm
      calc
        _ = flip (flip (flip (flip (flip (flip (v 1) b) b) c) c) z) d := by
          unfold flip
          ac_rfl
        _ = _ := by simp
    have hout0 : flip (v 0) z ∈ C.outside := by
      apply (C.offs_outside p 0 z).mpr
      change z ≠ x ∧ z ≠ a
      exact ⟨fun h => hzc (h.trans hx),hza⟩
    have hout1 : flip (v 1) z ∈ C.outside := (C.offs_outside p 1 z).mpr ⟨hza,hzb⟩
    have hout2 : flip (v 2) z ∈ C.outside := (C.offs_outside p 2 z).mpr ⟨hzb,hzc⟩
    have mark (i j : ℤ) (hi : 0 ≤ i ∧ i ≤ 6) (hj : 0 ≤ j ∧ j < 6)
        (ho : flip (v i) (e j) ∈ C.outside)
        (hh : n ≤ 4 * C.degree (flip (v i) (e j))) : C.markIn p (p+6) :=
      C.mark_from (i := p+i) (j := p+j) (by omega) (by omega) (by omega) (by omega)
        (by omega) ho hh
    by_cases hw : c = e 6
    · have hout6 : flip (v 6) d ∈ C.outside := (C.offs_outside p 6 d).mpr
        ⟨hzd.symm, fun hh => hcd (hw.trans hh.symm)⟩
      rcases C.star_heavy (u := flip (v 1) z) hab hac hbc with h | h | h | h
      · exact mark 1 5 (by norm_num) (by norm_num) hout1 h
      · exact mark 0 5 (by norm_num) (by norm_num) hout0 (hf0 ▸ h)
      · exact mark 2 5 (by norm_num) (by norm_num) hout2 (hf2 ▸ h)
      · exact mark 6 3 (by norm_num) (by norm_num) hout6 (hfc ▸ h)
    · have hout6 : flip (v 6) c ∈ C.outside := (C.offs_outside p 6 c).mpr ⟨hzc.symm,hw⟩
      rcases C.star_heavy (u := flip (v 1) z) hab had' hbd with h | h | h | h
      · exact mark 1 5 (by norm_num) (by norm_num) hout1 h
      · exact mark 0 5 (by norm_num) (by norm_num) hout0 (hf0 ▸ h)
      · exact mark 2 5 (by norm_num) (by norm_num) hout2 (hf2 ▸ h)
      · exact mark 6 2 (by norm_num) (by norm_num) hout6 (hfd ▸ h)

lemma Coil.seven_edge_mark (hL : 9 ≤ L) (p : ℤ) : C.markIn p (p+7) := by
  by_cases hac : C.step p = C.step (p+3)
  · have hne : C.step (p+1) ≠ C.step (p+4) := by
      intro hb
      have e (k : ℤ) : C.atPos (p+(k+1)) = flip (C.atPos (p+k)) (C.step (p+k)) :=
        C.offs_step p k
      have he : C.atPos (p+5) = flip (C.atPos p) (C.step (p+2)) := by
        have e' (k : ℤ) : C.atPos (p+(k+1)) = flip (C.atPos (p+k)) (C.step (p+k)) := e k
        have e4 := e' 4
        have e3 := e' 3
        have e2 := e' 2
        have e1 := e' 1
        have e0 := e' 0
        norm_num at e4 e3 e2 e1 e0
        rw [e4, e3, e2, e1, e0, ← hac, ← hb]
        calc
          _ = flip (flip (flip (flip (flip (C.atPos p) (C.step p)) (C.step p))
              (C.step (p+1))) (C.step (p+1))) (C.step (p+2)) := by unfold flip; ac_rfl
          _ = _ := by simp
      exact C.no_chord (a := p) (b := p+5) (by omega) (by omega) (adj_iff.mpr ⟨_, he.symm⟩)
    have hm := C.six_edge_mark hL (p+1) (by convert hne using 2 <;> ring)
    exact C.markIn_mono (by omega) (by omega) hm
  · exact C.markIn_mono le_rfl (by omega) (C.six_edge_mark hL p hac)
end CoilBound

/- Vertex-disjoint marked sections and the orientation of their marked edges. -/

namespace CoilBound

open SimpleGraph Finset
open scoped symmDiff BigOperators

variable {n L : ℕ} (C : Coil n L)

structure MarkedPacking (k : ℕ) where
  fits : 18*k ≤ L
  mid : Fin k → ℤ
  lower : ∀ i, (18 : ℤ) * i.val + 5 ≤ mid i
  upper : ∀ i, mid i ≤ (18 : ℤ) * i.val + 12
  label : Fin k → Fin n
  external : ∀ i, flip (C.atPos (mid i)) (label i) ∈ C.outside
  high : ∀ i, n ≤ 4 * C.degree (flip (C.atPos (mid i)) (label i))
  dir : Fin k → ℤ
  dir_eq : ∀ i, dir i = 1 ∨ dir i = -1
  depth : Fin k → ℕ
  depth_bounds : ∀ i, 1 ≤ depth i ∧ depth i ≤ 5
  hit : ∀ i, flip (C.atPos (mid i + dir i * (depth i : ℤ))) (label i) =
    C.atPos (mid i + dir i * ((depth i : ℤ)+1))

lemma Coil.orient_mark {i j : ℤ} (hm : C.mark i j) (h₁ : i-6 ≤ j) (h₂ : j ≤ i+5) :
    ∃ s : ℤ, ∃ d : ℕ, (s = 1 ∨ s = -1) ∧ 1 ≤ d ∧ d ≤ 5 ∧
      flip (C.atPos (i+s*(d : ℤ))) (C.step j) = C.atPos (i+s*((d : ℤ)+1)) := by
  have he := (C.flip_not_mem i (C.step j)).mp hm.1
  have hp : j ≠ i-1 := fun hj => he.1 (congrArg C.step hj)
  have hq : j ≠ i := fun hj => he.2 (congrArg C.step hj)
  by_cases hh : i < j
  · refine ⟨1,(j-i).toNat,Or.inl rfl,by omega,by omega,?_⟩
    simp only [one_mul]
    have harith : i + (↑(j-i).toNat : ℤ) = j := by omega
    rw [harith, show i + ((↑(j-i).toNat : ℤ)+1) = j+1 by omega, C.flip_step]
  · refine ⟨-1,(i-j-1).toNat,Or.inr rfl,by omega,by omega,?_⟩
    simp only [neg_mul, one_mul]
    rw [show i + -(↑(i-j-1).toNat : ℤ) = j+1 by omega,
      show i + -((↑(i-j-1).toNat : ℤ)+1) = j by omega]
    simpa only [add_sub_cancel_right] using C.flip_prev (j+1)

lemma Coil.make_packing (hL : 9 ≤ L) : Nonempty (MarkedPacking C (L/18)) := by
  classical
  have hex (t : Fin (L/18)) :
      ∃ i j : ℤ, (18 : ℤ)*t.val+5 ≤ i ∧ i ≤ (18 : ℤ)*t.val+12 ∧
        i-6 ≤ j ∧ j ≤ i+5 ∧ C.mark i j := by
    obtain ⟨i,j,h1,h2,_,_,h3,h4,hm⟩ := C.seven_edge_mark hL (18*(t.val : ℤ)+5)
    exact ⟨i,j,h1,by omega,h3,h4,hm⟩
  choose i j hi hi' hj hj' hm using hex
  have hor (t : Fin (L/18)) := C.orient_mark (hm t) (hj t) (hj' t)
  choose s d hs hdp hdb hhit using hor
  exact ⟨⟨by omega,i,hi,hi',fun t => C.step (j t),fun t => (hm t).1,
    fun t => (hm t).2,s,hs,d,fun t => ⟨hdp t,hdb t⟩,hhit⟩⟩

variable {C} {k : ℕ} (P : MarkedPacking C k)

def MarkedPacking.N (i : Fin k) : Cube n := flip (C.atPos (P.mid i)) (P.label i)

def MarkedPacking.last (i : Fin k) : ℤ := P.mid i + P.dir i * (P.depth i : ℤ)

def MarkedPacking.seg (i : Fin k) : Finset ℤ := Icc (P.mid i-5) (P.mid i+5)

def MarkedPacking.arc (i : Fin k) : Finset ℤ := Icc (min (P.mid i) (P.last i)) (max (P.mid i) (P.last i))

def MarkedPacking.Far (i j : Fin k) : Prop :=
  (P.mid i + 13 ≤ P.mid j ∧ P.mid j + 13 ≤ P.mid i + (L : ℤ)) ∨
  (P.mid j + 13 ≤ P.mid i ∧ P.mid i + 13 ≤ P.mid j + (L : ℤ))

instance MarkedPacking.decFar (i j : Fin k) : Decidable (P.Far i j) := by unfold MarkedPacking.Far; infer_instance

lemma MarkedPacking.mid_sep {i j : Fin k} (hij : i.val < j.val) :
    P.mid i + 11 ≤ P.mid j ∧ P.mid j + 11 ≤ P.mid i + (L : ℤ) := by
  have hloi := P.lower i
  have hloj := P.lower j
  have hupi := P.upper i
  have hupj := P.upper j
  have hL := P.fits
  have hj := j.isLt
  omega

lemma MarkedPacking.seg_range {i : Fin k} {a : ℤ} (ha : a ∈ P.seg i) :
    0 ≤ a ∧ a < (L : ℤ) := by
  have hi := i.isLt
  have hL := P.fits
  have h0 := P.lower i
  have h1 := P.upper i
  simp only [MarkedPacking.seg, mem_Icc] at ha
  omega

lemma MarkedPacking.mid_mem (i : Fin k) : P.mid i ∈ P.seg i := by
  simp [MarkedPacking.seg]

lemma MarkedPacking.arc_subset (i : Fin k) : P.arc i ⊆ P.seg i := by
  have hb := (P.depth_bounds i).2
  rcases P.dir_eq i with hs | hs <;>
    intro a ha <;> simp only [MarkedPacking.arc, MarkedPacking.last, hs, one_mul, neg_mul, mem_Icc,
      le_min_iff, min_le_iff, le_max_iff, max_le_iff, MarkedPacking.seg] at ha ⊢ <;> omega

lemma MarkedPacking.segment_inj {i j : Fin k} {a b : ℤ}
    (ha : a ∈ P.seg i) (hb : b ∈ P.seg j) (he : C.atPos a = C.atPos b) : i = j ∧ a = b := by
  have hra := P.seg_range ha
  have hrb := P.seg_range hb
  have hab : a = b := by
    rcases lt_trichotomy a b with h | h | h
    · exact False.elim (C.pos_ne h (by omega) he)
    · exact h
    · exact False.elim (C.pos_ne h (by omega) he.symm)
  refine ⟨?_,hab⟩
  rcases lt_trichotomy i.val j.val with h | h | h
  · have hs := (P.mid_sep h).1
    simp only [MarkedPacking.seg, mem_Icc] at ha hb
    omega
  · exact Fin.ext h
  · have hs := (P.mid_sep h).1
    simp only [MarkedPacking.seg, mem_Icc] at ha hb
    omega

lemma MarkedPacking.label_inj_of_N {i j : Fin k} (he : P.N i = P.N j)
    (hf : P.label i = P.label j) : i = j := by
  dsimp only [MarkedPacking.N] at he
  rw [hf, flip_inj] at he
  exact (P.segment_inj (P.mid_mem i) (P.mid_mem j) he).1

lemma MarkedPacking.no_chord_offsets {i j : Fin k} (h : P.Far i j)
    {a b : ℤ} (ha : P.mid i-5 ≤ a ∧ a ≤ P.mid i+5)
    (hb : P.mid j-6 ≤ b ∧ b ≤ P.mid j+6) :
    ¬ (SnakeInBox.Hypercube n).Adj (C.atPos a) (C.atPos b) := by
  rcases h with h | h
  · exact C.no_chord (by omega) (by omega)
  · intro he
    exact C.no_chord (a := b) (b := a) (by omega) (by omega) he.symm

lemma MarkedPacking.cross_labels {i j : Fin k} (hne : i ≠ j) (hN : P.N i = P.N j) :
    P.label j ≠ P.label i ∧
      P.label j ≠ C.step (P.mid i-1) ∧ P.label j ≠ C.step (P.mid i) := by
  refine ⟨fun he => hne (P.label_inj_of_N hN he.symm), ?_⟩
  have hflip : flip (flip (C.atPos (P.mid i)) (P.label j)) (P.label i) =
      C.atPos (P.mid j) := by
    rw [flip_comm, ← MarkedPacking.N, hN, MarkedPacking.N, flip_flip]
  have hn (a : ℤ) (ha : P.mid i - 1 ≤ a ∧ a ≤ P.mid i+1) :
      ¬ (SnakeInBox.Hypercube n).Adj (C.atPos a) (C.atPos (P.mid j)) := by
    rcases lt_or_gt_of_ne (fun h : i.val=j.val => hne (Fin.ext h)) with h | h
    · have hs := P.mid_sep h
      exact C.no_chord (by omega) (by omega)
    · have hs := P.mid_sep h
      intro hh
      exact C.no_chord (a := P.mid j) (b := a) (by omega) (by omega) hh.symm
  refine ⟨fun hl => ?_, fun hl => ?_⟩
  · exact hn (P.mid i-1) (by omega) (adj_iff.mpr ⟨P.label i, by simpa only [hl, C.flip_prev] using hflip⟩)
  · exact hn (P.mid i+1) (by omega) (adj_iff.mpr ⟨P.label i, by simpa only [hl, C.flip_step] using hflip⟩)

end CoilBound

/- Counting same-neighbor pairs whose two short translations remain outside the cycle. -/

namespace CoilBound

open Finset
open scoped BigOperators

variable {n L k : ℕ} {C : Coil n L} (P : MarkedPacking C k)

abbrev MarkPair (k : ℕ) := Fin k × Fin k

noncomputable def MarkedPacking.excluded (i : Fin k) : Finset (Fin n) :=
  {P.label i, C.step (P.mid i-1), C.step (P.mid i)}

lemma MarkedPacking.card_excluded (i : Fin k) : (P.excluded i).card = 3 := by
  have hh := (C.flip_not_mem (P.mid i) (P.label i)).mp (P.external i)
  have hne : C.step (P.mid i-1) ≠ C.step (P.mid i) := by
    simpa only [sub_add_cancel] using C.distinct_steps (P.mid i-1)
  simp [MarkedPacking.excluded, hh.1, hh.2, hne]

noncomputable def MarkedPacking.leftEdges (i : Fin k) : Finset (Fin n) :=
  (Icc (P.mid i-6) (P.mid i+5)).image C.step

noncomputable def MarkedPacking.rightEdges (i : Fin k) : Finset (Fin n) :=
  (Icc (min (P.mid i) (P.last i)-1) (max (P.mid i) (P.last i))).image C.step

lemma MarkedPacking.excluded_left (i : Fin k) : P.excluded i ⊆ P.leftEdges i := by
  have hd := P.depth_bounds i
  rcases P.dir_eq i with hs | hs <;>
    intro a ha <;> simp only [MarkedPacking.excluded, mem_insert, mem_singleton] at ha <;>
    rcases ha with rfl | rfl | rfl
  · have he := P.hit i
    simp only [hs,one_mul] at he
    have hh : P.label i = C.step (P.mid i + (P.depth i : ℤ)) := by
      apply label_inj.mp
      rw [C.flip_step, he]
      congr 1
      ring
    exact mem_image.mpr ⟨_,mem_Icc.mpr (by omega),hh.symm⟩
  · exact mem_image.mpr ⟨_,mem_Icc.mpr (by omega),rfl⟩
  · exact mem_image.mpr ⟨_,mem_Icc.mpr (by omega),rfl⟩
  · have he := P.hit i
    simp only [hs,neg_mul,one_mul] at he
    have hh : P.label i = C.step (P.mid i - (P.depth i : ℤ) - 1) := by
      have hidx : P.mid i - (P.depth i : ℤ) = P.mid i + -(P.depth i : ℤ) := by ring
      rw [hidx]
      apply label_inj.mp
      rw [C.flip_prev, he]
      congr 1
      ring
    exact mem_image.mpr ⟨_,mem_Icc.mpr (by omega),hh.symm⟩
  · exact mem_image.mpr ⟨_,mem_Icc.mpr (by omega),rfl⟩
  · exact mem_image.mpr ⟨_,mem_Icc.mpr (by omega),rfl⟩

lemma MarkedPacking.excluded_right (i : Fin k) : P.excluded i ⊆ P.rightEdges i := by
  have hd := P.depth_bounds i
  rcases P.dir_eq i with hs | hs <;>
    intro a ha <;> simp only [MarkedPacking.excluded, mem_insert, mem_singleton] at ha <;>
    rcases ha with rfl | rfl | rfl
  · have he := P.hit i
    simp only [hs,one_mul] at he
    have hh : P.label i = C.step (P.mid i + (P.depth i : ℤ)) := by
      apply label_inj.mp
      rw [C.flip_step, he]
      congr 1
      ring
    refine mem_image.mpr ⟨_,?_,hh.symm⟩
    simp only [mem_Icc, MarkedPacking.last, hs, one_mul, min_le_iff, le_max_iff]
    omega
  · refine mem_image.mpr ⟨_,?_,rfl⟩
    simp only [mem_Icc, MarkedPacking.last, hs, one_mul, le_max_iff]
    have hm := min_le_left (P.mid i) (P.mid i + (P.depth i : ℤ))
    omega
  · refine mem_image.mpr ⟨_,?_,rfl⟩
    simp only [mem_Icc, MarkedPacking.last, hs, one_mul, le_max_iff]
    have hm := min_le_left (P.mid i) (P.mid i + (P.depth i : ℤ))
    omega
  · have he := P.hit i
    simp only [hs,neg_mul,one_mul] at he
    have hh : P.label i = C.step (P.mid i + -(P.depth i : ℤ) - 1) := by
      apply label_inj.mp
      rw [C.flip_prev, he]
      congr 1
      ring
    refine mem_image.mpr ⟨_,?_,hh.symm⟩
    simp only [mem_Icc, MarkedPacking.last, hs, neg_mul, one_mul, le_max_iff]
    have hm := min_le_right (P.mid i) (P.mid i + -(P.depth i : ℤ))
    omega
  · refine mem_image.mpr ⟨_,?_,rfl⟩
    simp only [mem_Icc, MarkedPacking.last, hs, neg_mul, one_mul, le_max_iff]
    have hm := min_le_left (P.mid i) (P.mid i + -(P.depth i : ℤ))
    omega
  · refine mem_image.mpr ⟨_,?_,rfl⟩
    simp only [mem_Icc, MarkedPacking.last, hs, neg_mul, one_mul, le_max_iff]
    have hm := min_le_left (P.mid i) (P.mid i + -(P.depth i : ℤ))
    omega

noncomputable def MarkedPacking.leftBad (i : Fin k) : Finset (Fin n) := P.leftEdges i \ P.excluded i

noncomputable def MarkedPacking.rightBad (i : Fin k) : Finset (Fin n) := P.rightEdges i \ P.excluded i

lemma MarkedPacking.card_leftBad (i : Fin k) : (P.leftBad i).card ≤ 9 := by
  rw [MarkedPacking.leftBad, card_sdiff_of_subset (P.excluded_left i), P.card_excluded]
  have hh := card_image_le (s := Icc (P.mid i-6) (P.mid i+5)) (f := C.step)
  rw [Int.card_Icc] at hh
  change (P.leftEdges i).card ≤ _ at hh
  omega

lemma MarkedPacking.card_rightBad (i : Fin k) : (P.rightBad i).card ≤ 4 := by
  rw [MarkedPacking.rightBad, card_sdiff_of_subset (P.excluded_right i), P.card_excluded]
  have hh := card_image_le
    (s := Icc (min (P.mid i) (P.last i)-1) (max (P.mid i) (P.last i))) (f := C.step)
  change (P.rightEdges i).card ≤ _ at hh
  rw [Int.card_Icc] at hh
  have hd := (P.depth_bounds i).2
  rcases P.dir_eq i with hs | hs
  · have hle : P.mid i ≤ P.last i := by simp [MarkedPacking.last,hs]
    rw [min_eq_left hle, max_eq_right hle,MarkedPacking.last,hs,one_mul] at hh
    omega
  · have hle : P.last i ≤ P.mid i := by simp [MarkedPacking.last,hs]
    rw [min_eq_right hle, max_eq_left hle,MarkedPacking.last,hs,neg_mul,one_mul] at hh
    omega

lemma MarkedPacking.label_not_excluded {i j : Fin k} (hne : i ≠ j) (hN : P.N i = P.N j) :
    P.label j ∉ P.excluded i := by
  obtain ⟨h1,h2,h3⟩ := P.cross_labels hne hN
  simp [MarkedPacking.excluded,h1,h2,h3]

def MarkedPacking.good (i j : Fin k) : Prop :=
  P.N i = P.N j ∧ i ≠ j ∧ P.Far i j ∧ P.label j ∉ P.leftBad i ∧ P.label i ∉ P.rightBad j

noncomputable instance MarkedPacking.decGood (i j : Fin k) : Decidable (P.good i j) := by unfold MarkedPacking.good; infer_instance

noncomputable def MarkedPacking.goodPairs : Finset (MarkPair k) :=
  (univ ×ˢ univ).filter fun q => P.good q.1 q.2

def MarkedPacking.samePairs : Finset (MarkPair k) :=
  (univ ×ˢ univ).filter fun q => P.N q.1 = P.N q.2

def MarkedPacking.largeVertices : Finset (Cube n) := univ.image P.N

lemma MarkedPacking.left_translate_outside {i j : Fin k} (h : P.good i j) {a : ℤ}
    (ha : a ∈ P.seg i) : flip (C.atPos a) (P.label j) ∈ C.outside := by
  rcases h with ⟨hN,hne,_,hb,_⟩
  by_contra hh
  apply hb
  refine mem_sdiff.mpr ⟨?_,P.label_not_excluded hne hN⟩
  simp only [MarkedPacking.seg,mem_Icc] at ha
  by_cases he : P.label j = C.step (a-1)
  · exact mem_image.mpr ⟨_,mem_Icc.mpr (by omega),he.symm⟩
  · have he' : P.label j = C.step a := by
      by_contra hh'
      exact hh ((C.flip_not_mem a (P.label j)).mpr ⟨he,hh'⟩)
    exact mem_image.mpr ⟨_,mem_Icc.mpr (by omega),he'.symm⟩

lemma MarkedPacking.right_translate_outside {i j : Fin k} (h : P.good i j) {a : ℤ}
    (ha : a ∈ P.arc j) : flip (C.atPos a) (P.label i) ∈ C.outside := by
  rcases h with ⟨hN,hne,_,_,hb⟩
  by_contra hh
  apply hb
  refine mem_sdiff.mpr ⟨?_,P.label_not_excluded hne.symm hN.symm⟩
  simp only [MarkedPacking.arc,mem_Icc] at ha
  by_cases he : P.label i = C.step (a-1)
  · exact mem_image.mpr ⟨_,mem_Icc.mpr (by omega),he.symm⟩
  · have he' : P.label i = C.step a := by
      by_contra hh'
      exact hh ((C.flip_not_mem a (P.label i)).mpr ⟨he,hh'⟩)
    exact mem_image.mpr ⟨_,mem_Icc.mpr (by omega),he'.symm⟩

lemma MarkedPacking.high_count : n * P.largeVertices.card ≤ 4 * C.totalDegree := by
  have hm : P.largeVertices ⊆ C.outside := by
    intro v hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    exact P.external i
  calc
    n * P.largeVertices.card = ∑ _v ∈ P.largeVertices, n := by simp [mul_comm]
    _ ≤ ∑ v ∈ P.largeVertices, 4*C.degree v := by
      apply sum_le_sum
      intro v hv
      obtain ⟨i,_,rfl⟩ := mem_image.mp hv
      exact P.high i
    _ ≤ ∑ v ∈ C.outside, 4*C.degree v := sum_le_sum_of_subset hm
    _ = _ := by rw [Coil.totalDegree, mul_sum]

lemma MarkedPacking.samePairs_cauchy : k*k ≤ P.largeVertices.card * P.samePairs.card := by
  let f (v : Cube n) := ((univ : Finset (Fin k)).filter fun i => P.N i = v).card
  have hf : ∀ i ∈ (univ : Finset (Fin k)), P.N i ∈ P.largeVertices :=
    fun i hi => mem_image.mpr ⟨i,hi,rfl⟩
  have hc : (∑ v ∈ P.largeVertices, f v) = k := by
    rw [show (∑ v ∈ P.largeVertices, f v) = _ from
      sum_card_fiberwise_eq_card_filter univ P.largeVertices P.N]
    simp [hf]
  have hsq : (∑ v ∈ P.largeVertices, f v ^ 2) = P.samePairs.card := by
    rw [MarkedPacking.samePairs, card_filter_product (univ : Finset (Fin k)) univ
      (fun i j => P.N i = P.N j)]
    have hr : (∑ i : Fin k, ({j : Fin k | P.N i = P.N j} : Finset (Fin k)).card) =
        ∑ i : Fin k, f (P.N i) := by simp [f,eq_comm]
    rw [hr, ← sum_fiberwise_of_maps_to hf (fun i => f (P.N i))]
    apply sum_congr rfl
    intro v hv
    rw [pow_two, ← sum_const_nat]
    intro i hi
    rw [(mem_filter.mp hi).2]
  have h := sq_sum_le_card_mul_sum_sq (s := P.largeVertices) (f := f)
  rw [hc,hsq] at h
  simpa only [Nat.cast_id,pow_two] using h

def MarkedPacking.cw (i j : Fin k) : ℤ := (P.mid j-P.mid i) % (L : ℤ)

lemma MarkedPacking.cw_eq_of_lt {i j : Fin k} (h : i.val < j.val) :
    P.cw i j = P.mid j-P.mid i := by
  have hs := P.mid_sep h
  exact Int.emod_eq_of_lt (by omega) (by omega)

lemma MarkedPacking.cw_eq_of_gt {i j : Fin k} (h : j.val < i.val) :
    P.cw i j = (L : ℤ)+ (P.mid j-P.mid i) := by
  have hs := P.mid_sep h
  unfold MarkedPacking.cw
  rw [← Int.add_emod_left (L : ℤ), Int.emod_eq_of_lt (by omega) (by omega)]

lemma MarkedPacking.cw_bounds {i j : Fin k} (h : i ≠ j) :
    11 ≤ P.cw i j ∧ P.cw i j ≤ (L : ℤ)-11 := by
  rcases lt_or_gt_of_ne (fun e : i.val=j.val => h (Fin.ext e)) with hl | hl
  · rw [P.cw_eq_of_lt hl]
    have hs := P.mid_sep hl
    omega
  · rw [P.cw_eq_of_gt hl]
    have hs := P.mid_sep hl
    omega

lemma MarkedPacking.far_iff_cw {i j : Fin k} (h : i ≠ j) :
    P.Far i j ↔ 13 ≤ P.cw i j ∧ P.cw i j ≤ (L : ℤ)-13 := by
  unfold MarkedPacking.Far
  rcases lt_or_gt_of_ne (fun e : i.val=j.val => h (Fin.ext e)) with hl | hl
  · rw [P.cw_eq_of_lt hl]
    have hs := P.mid_sep hl
    omega
  · rw [P.cw_eq_of_gt hl]
    have hs := P.mid_sep hl
    omega

lemma MarkedPacking.cw_mod_sub (i j l : Fin k) :
    P.cw i l - P.cw i j ≡ P.mid l - P.mid j [ZMOD (L : ℤ)] := by
  have h := (Int.mod_modEq (P.mid l-P.mid i) (L : ℤ)).sub
    (Int.mod_modEq (P.mid j-P.mid i) (L : ℤ))
  unfold MarkedPacking.cw
  rw [show P.mid l - P.mid j = (P.mid l - P.mid i) - (P.mid j - P.mid i) by ring]
  exact h

lemma MarkedPacking.separated_cw {i j l : Fin k} (hjl : j ≠ l) :
    ¬ (P.cw i j-1 ≤ P.cw i l ∧ P.cw i l ≤ P.cw i j+1) := by
  intro hh
  have hL : (3 : ℤ) ≤ L := by have := C.length_min; omega
  have hb := P.cw_bounds hjl
  have he : (P.cw i l - P.cw i j) % (L : ℤ) = P.cw j l := P.cw_mod_sub i j l
  by_cases hp : 0 ≤ P.cw i l - P.cw i j
  · rw [Int.emod_eq_of_lt hp (by omega)] at he
    omega
  · rw [← Int.add_emod_left (L : ℤ), Int.emod_eq_of_lt (by omega) (by omega)] at he
    omega

lemma MarkedPacking.close_row (i : Fin k) :
    ((univ : Finset (Fin k)).filter fun j => i ≠ j ∧ ¬ P.Far i j).card ≤ 2 := by
  let F (j : Fin k) : Fin 2 := if P.cw i j ≤ 12 then 0 else 1
  suffices h : ((univ : Finset (Fin k)).filter fun j => i ≠ j ∧ ¬ P.Far i j).card ≤
      (univ : Finset (Fin 2)).card by simpa using h
  apply card_le_card_of_injOn F (fun _ _ => by simp)
  intro j hj l hl he
  simp only [mem_coe,mem_filter,mem_univ,true_and] at hj hl
  have hb := P.cw_bounds hj.1
  have hb' := P.cw_bounds hl.1
  have hf := hj.2
  have hf' := hl.2
  rw [P.far_iff_cw hj.1] at hf
  rw [P.far_iff_cw hl.1] at hf'
  by_contra hn
  apply P.separated_cw (i := i) hn
  dsimp only [F] at he
  split at he <;> split at he <;> first | contradiction | omega

lemma MarkedPacking.bad_rows (t : Fin k → Finset (Fin n)) (c : ℕ)
    (hc : ∀ i, (t i).card ≤ c) :
    ((univ ×ˢ univ : Finset (MarkPair k)).filter fun q =>
      P.N q.1 = P.N q.2 ∧ q.1 ≠ q.2 ∧ P.label q.2 ∈ t q.1).card ≤ k*c := by
  rw [card_filter_product (univ : Finset (Fin k)) univ
    (fun i j => P.N i = P.N j ∧ i ≠ j ∧ P.label j ∈ t i)]
  calc
    _ ≤ ∑ _i : Fin k, c := by
      apply sum_le_sum
      intro i _
      apply le_trans _ (hc i)
      apply card_le_card_of_injOn P.label
      · intro j hj
        exact (mem_filter.mp hj).2.2.2
      · intro j hj l hl he
        exact P.label_inj_of_N ((mem_filter.mp hj).2.1.symm.trans (mem_filter.mp hl).2.1) he
    _ = k*c := by simp

lemma MarkedPacking.bad_columns (t : Fin k → Finset (Fin n)) (c : ℕ)
    (hc : ∀ i, (t i).card ≤ c) :
    ((univ ×ˢ univ : Finset (MarkPair k)).filter fun q =>
      P.N q.1 = P.N q.2 ∧ q.1 ≠ q.2 ∧ P.label q.1 ∈ t q.2).card ≤ k*c := by
  refine le_trans ?_ (P.bad_rows t c hc)
  apply card_le_card_of_injOn Prod.swap
  · intro q hq
    simp only [mem_coe,mem_filter,mem_product,mem_univ,true_and,Prod.fst_swap,Prod.snd_swap] at hq ⊢
    exact ⟨hq.1.symm,hq.2.1.symm,hq.2.2⟩
  · exact Prod.swap_injective.injOn

lemma MarkedPacking.good_count :
    P.samePairs.card ≤ P.goodPairs.card + 16*k := by
  let J : Finset (MarkPair k) := univ.image fun i : Fin k => (i,i)
  let K : Finset (MarkPair k) := (univ ×ˢ univ).filter fun q => q.1 ≠ q.2 ∧ ¬ P.Far q.1 q.2
  let A : Finset (MarkPair k) := (univ ×ˢ univ).filter fun q =>
    P.N q.1 = P.N q.2 ∧ q.1 ≠ q.2 ∧ P.label q.2 ∈ P.leftBad q.1
  let B : Finset (MarkPair k) := (univ ×ˢ univ).filter fun q =>
    P.N q.1 = P.N q.2 ∧ q.1 ≠ q.2 ∧ P.label q.1 ∈ P.rightBad q.2
  have hJ : J.card ≤ k := by
    unfold J
    simpa using (card_image_le (s := (univ : Finset (Fin k))) (f := fun i => (i,i)))
  have hK : K.card ≤ k*2 := by
    unfold K
    rw [card_filter_product (univ : Finset (Fin k)) univ (fun i j => i ≠ j ∧ ¬ P.Far i j)]
    calc
      _ ≤ ∑ _i : Fin k, 2 := sum_le_sum (fun i _ => P.close_row i)
      _ = _ := by simp
  have hA : A.card ≤ k*9 := P.bad_rows P.leftBad 9 P.card_leftBad
  have hB : B.card ≤ k*4 := P.bad_columns P.rightBad 4 P.card_rightBad
  have hcover : P.samePairs ⊆ P.goodPairs ∪ J ∪ K ∪ A ∪ B := by
    rintro ⟨i,j⟩ hm
    have hN : P.N i = P.N j := (mem_filter.mp hm).2
    by_cases he : i = j
    · subst j
      exact mem_union_left B (mem_union_left A (mem_union_left K
        (mem_union_right P.goodPairs (mem_image.mpr ⟨i,mem_univ _,rfl⟩))))
    · by_cases hf : P.Far i j
      · by_cases ha : P.label j ∈ P.leftBad i
        · exact mem_union_left B (mem_union_right _ (mem_filter.mpr ⟨by simp,⟨hN,he,ha⟩⟩))
        · by_cases hb : P.label i ∈ P.rightBad j
          · exact mem_union_right _ (mem_filter.mpr ⟨by simp,⟨hN,he,hb⟩⟩)
          · exact mem_union_left B (mem_union_left A (mem_union_left K (mem_union_left J
              (mem_filter.mpr ⟨by simp,⟨hN,he,hf,ha,hb⟩⟩))))
      · exact mem_union_left B (mem_union_left A (mem_union_right _
          (mem_filter.mpr ⟨by simp,⟨he,hf⟩⟩)))
  have h0 := card_le_card hcover
  have h1 := card_union_le (P.goodPairs ∪ J ∪ K ∪ A) B
  have h2 := card_union_le (P.goodPairs ∪ J ∪ K) A
  have h3 := card_union_le (P.goodPairs ∪ J) K
  have h4 := card_union_le P.goodPairs J
  omega
end CoilBound

/- Two translated paths with the same origin yield a star after they diverge. -/

namespace CoilBound

open Finset SimpleGraph
open scoped BigOperators

variable {n L k : ℕ} {C : Coil n L} (P : MarkedPacking C k)

structure CubeStar (s : Finset (Cube n)) where
  vertex : Fin 4 ↪ Cube n
  in_set : ∀ a, vertex a ∈ s
  adj : ∀ a : Fin 3, (SnakeInBox.Hypercube n).Adj (vertex 0) (vertex a.succ)

lemma make_star {s : Finset (Cube n)} {u v w x : Cube n}
    (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) (hx : x ∈ s)
    (h₁ : (SnakeInBox.Hypercube n).Adj u v) (h₂ : (SnakeInBox.Hypercube n).Adj u w)
    (h₃ : (SnakeInBox.Hypercube n).Adj u x)
    (hvw : v ≠ w) (hvx : v ≠ x) (hwx : w ≠ x) : Nonempty (CubeStar s) := by
  let f : Fin 4 → Cube n := ![u,v,w,x]
  have hinj : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f,h₁.ne,h₂.ne,h₃.ne,
      h₁.ne.symm,h₂.ne.symm,h₃.ne.symm,hvw,hvx,hwx,hvw.symm,hvx.symm,hwx.symm]
  refine ⟨⟨⟨f,hinj⟩,?_,?_⟩⟩
  · intro i
    fin_cases i <;> simp_all [f]
  · intro i
    fin_cases i
    · exact h₁
    · exact h₂
    · exact h₃

def MarkedPacking.pool (i j : Fin k) : Finset (Cube n) :=
  ((P.seg i).image fun a => flip (C.atPos a) (P.label j)) ∪
  ((P.arc j).image fun a => flip (C.atPos a) (P.label i))

lemma MarkedPacking.pool_outside {i j : Fin k} (h : P.good i j) :
    P.pool i j ⊆ C.outside := by
  intro v hv
  rcases mem_union.mp hv with hleft | hright
  · obtain ⟨a,ha,he⟩ := mem_image.mp hleft
    rw [← he]
    exact P.left_translate_outside h ha
  · obtain ⟨b,hb,he⟩ := mem_image.mp hright
    rw [← he]
    exact P.right_translate_outside h hb

lemma MarkedPacking.offset_mem_seg (i : Fin k) {r : ℤ} (h : -5 ≤ r ∧ r ≤ 5) :
    P.mid i + r ∈ P.seg i := by
  simp only [MarkedPacking.seg,mem_Icc]
  omega

lemma MarkedPacking.progress_mem_arc (i : Fin k) {r : ℕ} (hr : r ≤ P.depth i) :
    P.mid i + P.dir i*(r:ℤ) ∈ P.arc i := by
  rcases P.dir_eq i with hs | hs <;>
    simp only [MarkedPacking.arc,MarkedPacking.last,hs,one_mul,neg_mul,mem_Icc,min_le_iff,le_max_iff]
  all_goals omega

lemma Coil.adj_sign (x y s : ℤ) (hs : s = 1 ∨ s = -1) (he : y = x+s) :
    (SnakeInBox.Hypercube n).Adj (C.atPos x) (C.atPos y) := by
  subst y
  rcases hs with rfl | rfl
  · exact C.adj_succ x
  · have h := (C.adj_succ (x + -1)).symm
    simpa using h

set_option maxHeartbeats 800000 in
lemma MarkedPacking.star_of_good {i j : Fin k} (h : P.good i j) :
    Nonempty (CubeStar (P.pool i j)) := by
  let A (r : ℤ) := flip (C.atPos (P.mid i+r)) (P.label j)
  let B (r : ℕ) := flip (C.atPos (P.mid j+P.dir j*(r:ℤ))) (P.label i)
  let d := P.depth j
  have hd : 1 ≤ d ∧ d ≤ 5 := P.depth_bounds j
  have aMem (r : ℤ) (hr : -5 ≤ r ∧ r ≤ 5) : A r ∈ P.pool i j :=
    mem_union_left _ (mem_image.mpr ⟨_,P.offset_mem_seg i hr,rfl⟩)
  have bMem (r : ℕ) (hr : r ≤ d) : B r ∈ P.pool i j :=
    mem_union_right _ (mem_image.mpr ⟨_,P.progress_mem_arc j hr,rfl⟩)
  have aInj {r s : ℤ} (hr : -5 ≤ r ∧ r ≤ 5) (hs : -5 ≤ s ∧ s ≤ 5)
      (he : A r = A s) : r = s := by
    change flip (C.atPos (P.mid i+r)) (P.label j) =
      flip (C.atPos (P.mid i+s)) (P.label j) at he
    have ht := (P.segment_inj (P.offset_mem_seg i hr) (P.offset_mem_seg i hs) (flip_inj.mp he)).2
    omega
  have bInj {r t : ℕ} (hr : r ≤ d) (ht : t ≤ d) (he : B r = B t) : r=t := by
    change flip (C.atPos (P.mid j+P.dir j*(r:ℤ))) (P.label i) =
      flip (C.atPos (P.mid j+P.dir j*(t:ℤ))) (P.label i) at he
    have hup := (P.segment_inj (P.arc_subset j (P.progress_mem_arc j hr))
      (P.arc_subset j (P.progress_mem_arc j ht)) (flip_inj.mp he)).2
    rcases P.dir_eq j with hs | hs <;> simp only [hs,one_mul,neg_mul] at hup <;> omega
  have aAdj (r s : ℤ) (hs : s = 1 ∨ s = -1) :
      (SnakeInBox.Hypercube n).Adj (A r) (A (r+s)) :=
    (adj_flip (P.label j)).mpr (C.adj_sign _ _ _ hs (by ring))
  have bAdj (r : ℕ) : (SnakeInBox.Hypercube n).Adj (B r) (B (r+1)) := by
    apply (adj_flip (P.label i)).mpr
    apply C.adj_sign _ _ _ (P.dir_eq j)
    push_cast
    ring
  have hcenter : B 0 = A 0 := by
    have hN := h.1
    simp only [A,B,Nat.cast_zero,mul_zero,add_zero]
    have e := congrArg (fun v => flip (flip v (P.label j)) (P.label i)) hN
    dsimp only [MarkedPacking.N] at e
    rw [flip_comm (flip (C.atPos (P.mid i)) (P.label i)) (P.label j) (P.label i),
      flip_flip, flip_flip] at e
    exact e.symm
  have hEnds (s : ℤ) (hs : s = 1 ∨ s = -1) : B d ≠ A (s * (d:ℤ)) := by
    intro he
    have hA : P.mid i-5 ≤ P.mid i+s*(d:ℤ) ∧ P.mid i+s*(d:ℤ) ≤ P.mid i+5 := by
      rcases hs with hs | hs <;> simp only [hs,neg_mul,one_mul] <;> omega
    have hB : P.mid j-6 ≤ P.mid j+P.dir j*((d:ℤ)+1) ∧
        P.mid j+P.dir j*((d:ℤ)+1) ≤ P.mid j+6 := by
      rcases P.dir_eq j with hs | hs <;> simp only [hs,neg_mul,one_mul] <;> omega
    apply P.no_chord_offsets h.2.2.1 hA hB
    apply adj_iff.mpr
    refine ⟨P.label i,?_⟩
    have hp := congrArg (fun v => flip (flip v (P.label j)) (P.label i)) he
    simp only [A,B] at hp
    rw [flip_comm (flip (C.atPos (P.mid j + P.dir j * (d : ℤ))) (P.label i))
      (P.label j) (P.label i), flip_flip, flip_flip] at hp
    exact hp.symm.trans (P.hit j)
  have branch (s : ℤ) (hs : s = 1 ∨ s = -1) (hfirst : B 1 = A s) :
      Nonempty (CubeStar (P.pool i j)) := by
    let Q (r : ℕ) := A (s*(r:ℤ))
    have hex : ∃ r : ℕ, r ≤ d ∧ B r ≠ Q r := ⟨d,le_rfl,hEnds s hs⟩
    let r := Nat.find hex
    have hbound : r ≤ d := (Nat.find_spec hex).1
    have hsplit : B r ≠ Q r := (Nat.find_spec hex).2
    have hmin (t : ℕ) (ht : t < r) : B t = Q t := by
      by_contra he
      exact (not_lt_of_ge (Nat.find_min' hex ⟨le_trans ht.le hbound,he⟩)) ht
    have htwo : 2 ≤ r := by
      by_contra! ht
      have hcases : r=0 ∨ r=1 := by omega
      rcases hcases with he | he
      · rw [he] at hsplit
        exact hsplit (by simpa [Q] using hcenter)
      · rw [he] at hsplit
        exact hsplit (by simpa [Q] using hfirst)
    have hsmall (t : ℕ) (ht : t ≤ d) : -5 ≤ s*(t:ℤ) ∧ s*(t:ℤ) ≤ 5 := by
      rcases hs with hs | hs <;> simp only [hs,neg_mul,one_mul] <;> omega
    have hQAdj (t : ℕ) :
        (SnakeInBox.Hypercube n).Adj (Q t) (Q (t+1)) := by
      unfold Q
      rw [show s * (↑(t+1) : ℤ) = s * (t:ℤ) + s by push_cast; ring]
      exact aAdj _ _ hs
    have hr1 : r-1+1=r := by omega
    have hr2 : r-2+1=r-1 := by omega
    have hQ₁ : (SnakeInBox.Hypercube n).Adj (Q (r-1)) (Q (r-2)) := by
      have e := hQAdj (r-2)
      rw [hr2] at e
      exact e.symm
    have hQ₂ : (SnakeInBox.Hypercube n).Adj (Q (r-1)) (Q r) := by
      have e := hQAdj (r-1)
      rwa [hr1] at e
    have hQ₃ : (SnakeInBox.Hypercube n).Adj (Q (r-1)) (B r) := by
      have e := bAdj (r-1)
      rwa [hr1,hmin (r-1) (by omega)] at e
    refine make_star (aMem _ (hsmall _ (by omega))) (aMem _ (hsmall _ (by omega)))
      (aMem _ (hsmall _ hbound)) (bMem _ hbound) hQ₁ hQ₂ hQ₃ ?_ ?_ (Ne.symm hsplit)
    · intro e
      have eq := aInj (hsmall (r-2) (by omega)) (hsmall r hbound) e
      rcases hs with hs | hs <;> simp only [hs,neg_mul,one_mul] at eq <;> omega
    · intro e
      have h := bInj (r := r-2) (t := r) (by omega) hbound
        ((hmin (r-2) (by omega)).trans e)
      omega
  by_cases he : B 1 = A 1
  · exact branch 1 (Or.inl rfl) he
  by_cases hf : B 1 = A (-1)
  · exact branch (-1) (Or.inr rfl) hf
  have hB₁ : (SnakeInBox.Hypercube n).Adj (A 0) (B 1) := by
    rw [← hcenter]
    exact bAdj 0
  exact make_star (aMem 0 (by norm_num)) (aMem 1 (by norm_num))
    (aMem (-1) (by norm_num)) (bMem 1 hd.1) (aAdj 0 1 (Or.inl rfl))
    (aAdj 0 (-1) (Or.inr rfl)) hB₁
    (fun e => by have h := aInj (r := 1) (s := -1) (by norm_num) (by norm_num) e; omega)
    (Ne.symm he) (Ne.symm hf)

end CoilBound

/- The scalar inequalities converting the exterior degree estimate to the coil bound. -/

namespace CoilBound

open Filter SimpleGraph
open scoped BigOperators

lemma degree_from_two_estimates {n k m D : ℝ} (hn : 0 ≤ n) (hk : 0 < k) (hm : 0 < m)
    (hD : 0 ≤ D) (h₁ : n*m ≤ 4*D) (h₂ : (2/3:ℝ)*(k*k-16*k*m) ≤ D*m) :
    k * (Real.sqrt n / Real.sqrt 6 - 6) ≤ D := by
  let a := k/m
  let t := D/k
  have ha : 0 < a := div_pos hk hm
  have ht : 0 ≤ t := div_nonneg hD hk.le
  have ham : a*m = k := div_mul_cancel₀ k hm.ne'
  have htk : t*k = D := div_mul_cancel₀ D hk.ne'
  have h₃ : n ≤ 4*a*t := by
    apply le_of_mul_le_mul_right _ hm
    calc
      n*m ≤ 4*D := h₁
      _ = (4*a*t)*m := by linear_combination -4*t*ham - 4*htk
  have h₄ : a ≤ (3/2:ℝ)*t+16 := by
    apply le_of_mul_le_mul_right _ (mul_pos hk hm)
    nlinarith only [h₂, congrArg (k * ·) ham, congrArg (m * ·) htk]
  have h₅ := mul_le_mul_of_nonneg_left h₄ (show 0 ≤ 4*t by positivity)
  have h₆ : n ≤ 6*(t+6)^2 := by nlinarith only [h₃,h₅,ht]
  have hsix : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have hsq : (Real.sqrt n / Real.sqrt 6)^2 = n/6 := by
    rw [div_pow, Real.sq_sqrt hn, Real.sq_sqrt (by norm_num : (0:ℝ)≤6)]
  have hf : Real.sqrt n / Real.sqrt 6 ≤ t+6 := by
    by_contra! h
    have hz : 0 < (Real.sqrt n / Real.sqrt 6 - (t+6)) *
        (Real.sqrt n / Real.sqrt 6 + (t+6)) := mul_pos (sub_pos.mpr h) (by positivity)
    nlinarith only [h₆,hsq,hz]
  calc
    k * (Real.sqrt n / Real.sqrt 6 - 6) ≤ k*t := by gcongr <;> linarith
    _ = D := by simpa only [mul_comm] using htk

variable {n L : ℕ} (C : Coil n L)

lemma Coil.real_degree_identity (hn : 2 ≤ n) :
    (L : ℝ)*((n : ℝ)-1) + (C.totalDegree : ℝ)/2 = 2^(n-1)*(n : ℝ) := by
  have hp : 2^n = 2^(n-1)*2 := by
    conv_lhs => rw [show n = (n-1)+1 by omega]
    rw [pow_succ]
  have he := C.totalDegree_identity
  rw [hp] at he
  have heR := congrArg (fun a : ℕ => (a : ℝ)) he
  push_cast [Nat.cast_sub hn] at heR
  linarith only [heR]

noncomputable def finalBound (n : ℕ) : ℝ :=
  1 + 2 ^ (n-1) * (6*(n:ℝ)) / (6*n + 1/(6*Real.sqrt 6)*Real.sqrt n - 7)

lemma final_bound_arithmetic {n L D : ℕ} (hn : 2 ≤ n)
    (hidentity : (L : ℝ)*((n : ℝ)-1) + (D : ℝ)/2 = 2^(n-1)*(n : ℝ))
    (hdeficit : 0 ≤ Real.sqrt (n : ℝ)/Real.sqrt 6 - 6 →
      ((L/18 : ℕ) : ℝ)*(Real.sqrt (n : ℝ)/Real.sqrt 6 - 6) ≤ D) : (L : ℝ) ≤ finalBound n := by
  let α := (Real.sqrt (n : ℝ) / Real.sqrt 6 - 6)/36
  let b := (n : ℝ) - 1 + α
  have hsix : 0 < Real.sqrt 6 := by positivity
  have hsix₂ : 1 ≤ Real.sqrt 6 := by
    have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)
    nlinarith
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : Real.sqrt (n : ℝ) ≤ n := by
    have ht := Real.sq_sqrt (by positivity : (0:ℝ) ≤ n)
    have h₂ : (n : ℝ) ≤ (n : ℝ)^2 := by nlinarith only [hN, sq_nonneg ((n:ℝ)-1)]
    by_contra! h
    have hz := mul_pos (sub_pos.mpr h) (show 0 < Real.sqrt (n : ℝ) + (n : ℝ) by positivity)
    nlinarith only [ht, h₂, hz]
  have hab : 16*α ≤ (n : ℝ)-1 := by
    have hdiv : Real.sqrt (n : ℝ) / Real.sqrt 6 ≤ n := by
      calc
        Real.sqrt (n : ℝ) / Real.sqrt 6 ≤ Real.sqrt (n : ℝ) :=
          div_le_self (by positivity) hsix₂
        _ ≤ _ := hsn
    dsimp [α]
    linarith
  have hb : 0 < b := by
    have hd : 0 ≤ Real.sqrt (n : ℝ) / Real.sqrt 6 := by positivity
    dsimp [b,α]
    linarith
  have hlarge : (L : ℝ)*b ≤ 2^(n-1)*(n : ℝ) + b := by
    by_cases hα : 0 ≤ α
    · have hk : (L : ℝ) ≤ (18 : ℝ)*(↑(L/18) : ℝ)+17 := by
        exact_mod_cast (show L ≤ 18*(L/18)+17 by omega)
      have ha := mul_le_mul_of_nonneg_right hk hα
      have hd := hdeficit (by dsimp [α] at hα; linarith)
      have h17 : 17*α ≤ b := by dsimp [b]; linarith
      have hαeq : 36 * α = Real.sqrt (n : ℝ) / Real.sqrt 6 - 6 := by dsimp [α]; ring
      rw [← hαeq] at hd
      dsimp [b] at *
      nlinarith only [hidentity, ha, hd, h17]
    · have he : (L : ℝ)*α ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge hα)
      have hD : (0 : ℝ) ≤ (D : ℝ) := by positivity
      dsimp [b] at *
      nlinarith only [hidentity, he, hD, hb]
  have kout : (L : ℝ) ≤ 1 + 2^(n-1)*(n : ℝ)/b := by
    have hdiv : (L : ℝ)-1 ≤ 2^(n-1)*(n : ℝ)/b := (le_div_iff₀ hb).mpr (by linarith only [hlarge])
    linarith
  unfold finalBound
  have he : 6*n + 1/(6*Real.sqrt 6)*Real.sqrt n - 7 = 6*b := by
    dsimp [b, α]
    field_simp [hsix.ne']
    <;> ring
  rw [he]
  convert kout using 1
  field_simp [hb.ne']

lemma final_of_coils (hn : 2 ≤ n) (h : ∀ {L : ℕ}, Coil n L → (L : ℝ) ≤ finalBound n) :
    (SnakeInBox.LongestCoilInTheBox n : ℝ) ≤ finalBound n := by
  unfold SnakeInBox.LongestCoilInTheBox SnakeInBox.LongestCoilInGraph
  let s := {k | ∃ S : (SnakeInBox.Hypercube n).Subgraph,
    SnakeInBox.IsCoilInGraphOfLength _ S k}
  change ((sSup s : ℕ) : ℝ) ≤ finalBound n
  have hs0 : 0 ≤ finalBound n := by
    have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hd : 0 ≤ (1 / (6*Real.sqrt 6))*Real.sqrt n := by positivity
    have hh : 0 < 6*(n:ℝ) + 1/(6*Real.sqrt 6)*Real.sqrt n - 7 := by linarith
    unfold finalBound
    positivity
  have hbound : ∀ k ∈ s, (k : ℝ) ≤ finalBound n := by
    rintro k ⟨S,hi,u,p,hc,rfl,rfl⟩
    obtain ⟨c⟩ := exists_coil_of_walk p hc hi
    exact h c
  have hB : BddAbove s := ⟨⌊finalBound n⌋₊,fun k hk => (Nat.le_floor_iff hs0).2 (hbound k hk)⟩
  by_cases he : s.Nonempty
  · exact hbound _ (Nat.sSup_mem he hB)
  · have hz : s = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    rw [hz, csSup_empty]
    change ((0 : ℕ) : ℝ) ≤ finalBound n
    simpa only [Nat.cast_zero] using hs0

end CoilBound

/- Bounding the multiplicity of each translated vertex and summing its contribution. -/

namespace CoilBound

open Finset SimpleGraph
open scoped BigOperators

variable {n L k : ℕ} {C : Coil n L} (P : MarkedPacking C k)

abbrev MarkedPacking.Active := {q : MarkPair k // q ∈ P.goodPairs}

abbrev MarkedPacking.Occurrence := P.Active × Fin 4

lemma MarkedPacking.active_good (q : P.Active) : P.good q.1.1 q.1.2 :=
  (mem_filter.mp q.2).2

noncomputable def MarkedPacking.star (q : P.Active) : CubeStar (P.pool q.1.1 q.1.2) :=
  Classical.choice (P.star_of_good (P.active_good q))

noncomputable def MarkedPacking.output (r : P.Occurrence) : Cube n :=
  (P.star r.1).vertex r.2

lemma MarkedPacking.output_outside (r : P.Occurrence) : P.output r ∈ C.outside :=
  P.pool_outside (P.active_good r.1) ((P.star r.1).in_set r.2)

def MarkPair.source (q : MarkPair k) (b : Bool) : Fin k := if b then q.1 else q.2

def MarkPair.other (q : MarkPair k) (b : Bool) : Fin k := if b then q.2 else q.1

lemma MarkedPacking.output_origin (r : P.Occurrence) :
    ∃ b : Bool, ∃ a ∈ P.seg (MarkPair.source r.1.1 b),
      flip (P.output r) (P.label (MarkPair.other r.1.1 b)) = C.atPos a := by
  have hv := (P.star r.1).in_set r.2
  rcases mem_union.mp hv with h | h
  · obtain ⟨a, ha, he⟩ := mem_image.mp h
    refine ⟨true,a,ha,?_⟩
    change flip (P.output r) (P.label r.1.1.2) = C.atPos a
    rw [← show flip (C.atPos a) (P.label r.1.1.2) = P.output r from he, flip_flip]
  · obtain ⟨a, ha, he⟩ := mem_image.mp h
    refine ⟨false,a,P.arc_subset _ ha,?_⟩
    change flip (P.output r) (P.label r.1.1.1) = C.atPos a
    rw [← show flip (C.atPos a) (P.label r.1.1.1) = P.output r from he, flip_flip]

noncomputable def MarkedPacking.side (r : P.Occurrence) : Bool :=
  Classical.choose (P.output_origin r)

noncomputable def MarkedPacking.position (r : P.Occurrence) : ℤ :=
  Classical.choose (Classical.choose_spec (P.output_origin r))

noncomputable def MarkedPacking.occLabel (r : P.Occurrence) : Fin n :=
  P.label (MarkPair.other r.1.1 (P.side r))

lemma MarkedPacking.position_mem (r : P.Occurrence) :
    P.position r ∈ P.seg (MarkPair.source r.1.1 (P.side r)) :=
  (Classical.choose_spec (Classical.choose_spec (P.output_origin r))).1

lemma MarkedPacking.position_flip (r : P.Occurrence) :
    flip (P.output r) (P.occLabel r) = C.atPos (P.position r) :=
  (Classical.choose_spec (Classical.choose_spec (P.output_origin r))).2

def Coil.insideLabels (C : Coil n L) (v : Cube n) : Finset (Fin n) :=
  univ.filter fun a => flip v a ∈ C.inside

lemma Coil.card_insideLabels (C : Coil n L) (v : Cube n) :
    (C.insideLabels v).card = n - C.degree v := by
  have h : (C.insideLabels v).card + C.degree v = n := by
    simpa [Coil.insideLabels,Coil.degree] using
      (card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun a => flip v a ∈ C.inside))
  omega

lemma MarkedPacking.label_mem_inside (r : P.Occurrence) :
    P.occLabel r ∈ C.insideLabels (P.output r) := by
  simp only [Coil.insideLabels,mem_filter,mem_univ,true_and,P.position_flip,C.atPos_mem]

noncomputable def MarkedPacking.fiber (v : Cube n) : Finset P.Occurrence := by
  classical
  exact univ.filter fun r => P.output r = v

lemma MarkedPacking.fiber_count (v : Cube n) :
    (P.fiber v).card ≤ 2 * (n - C.degree v) := by
  classical
  have h : (P.fiber v).card ≤ ((univ : Finset Bool) ×ˢ C.insideLabels v).card := by
    apply card_le_card_of_injOn (fun r => (P.side r,P.occLabel r))
    · intro r hr
      have he : P.output r = v := (mem_filter.mp hr).2
      have hx := P.label_mem_inside r
      rw [he] at hx
      exact mem_product.mpr ⟨mem_univ _,hx⟩
    · rintro ⟨q,r⟩ hx ⟨q',r'⟩ hy he
      have ev : P.output (q,r) = P.output (q',r') :=
        (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm
      obtain ⟨eb,el⟩ := Prod.mk.inj he
      have ht : C.atPos (P.position (q,r)) = C.atPos (P.position (q',r')) := by
        rw [← P.position_flip,← P.position_flip,ev,el]
      have hs := (P.segment_inj (P.position_mem (q,r)) (P.position_mem (q',r')) ht).1
      have hN₁ : P.N (MarkPair.source q.1 (P.side (q,r))) =
          P.N (MarkPair.other q.1 (P.side (q,r))) := by
        cases P.side (q,r) <;> simp [MarkPair.source,MarkPair.other,(P.active_good q).1]
      have hN₂ : P.N (MarkPair.source q'.1 (P.side (q',r'))) =
          P.N (MarkPair.other q'.1 (P.side (q',r'))) := by
        cases P.side (q',r') <;> simp [MarkPair.source,MarkPair.other,(P.active_good q').1]
      have ho : MarkPair.other q.1 (P.side (q,r)) = MarkPair.other q'.1 (P.side (q',r')) :=
        P.label_inj_of_N (hN₁.symm.trans ((congrArg P.N hs).trans hN₂)) el
      have hq : q = q' := by
        apply Subtype.ext
        rw [← eb] at hs ho
        cases hb : P.side (q,r)
        · simp [MarkPair.source,MarkPair.other,hb] at hs ho
          exact Prod.ext ho hs
        · simp [MarkPair.source,MarkPair.other,hb] at hs ho
          exact Prod.ext hs ho
      subst q'
      change (P.star q).vertex r = (P.star q).vertex r' at ev
      exact Prod.ext rfl ((P.star q).vertex.injective ev)
  simpa only [card_product,card_univ,Fintype.card_bool,C.card_insideLabels] using h

noncomputable def Coil.weight (C : Coil n L) (v : Cube n) : ℝ :=
  (C.degree v : ℝ) / (2 * ((n : ℝ) - (C.degree v : ℝ)))

lemma weight_tangent {n d : ℝ} (hn : 0 < n) (hd : d < n) :
    (8 : ℝ)/(9*n)*d - 1/18 ≤ d/(2*(n-d)) := by
  have hnd : 0 < n-d := sub_pos.mpr hd
  have hpos : 0 < 18*n*(n-d) := by positivity
  apply le_of_mul_le_mul_right _ hpos
  field_simp
  nlinarith only [sq_nonneg (4*d-n)]

lemma MarkedPacking.star_weight (hn : 0 < n) (q : P.Active) :
    (2/3 : ℝ) ≤ ∑ r : Fin 4, C.weight (P.output (q,r)) := by
  let s := P.star q
  let v (i : Fin 4) := s.vertex i
  have hd (r : Fin 4) : C.degree (v r) < n := by
    have hm := P.label_mem_inside (q,r)
    have hpos := card_pos.mpr ⟨_,hm⟩
    rw [C.card_insideLabels] at hpos
    change C.degree (P.output (q,r)) < n
    omega
  have hsum : (n : ℝ) ≤ ∑ r : Fin 4, (C.degree (v r) : ℝ) := by
    have he := C.star_degree (s.adj 0) (s.adj 1) (s.adj 2)
      (fun h => by have := s.vertex.injective h; contradiction)
      (fun h => by have := s.vertex.injective h; contradiction)
      (fun h => by have := s.vertex.injective h; contradiction)
    norm_cast
    simpa only [v,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,add_assoc,
      show (0:Fin 2).succ.succ = (1:Fin 3).succ from rfl,
      show (0:Fin 1).succ.succ.succ = (2:Fin 3).succ from rfl] using he
  let c : ℝ := (8:ℝ)/(9*(n:ℝ))
  calc
    (2/3 : ℝ) = c*(n:ℝ) - 4*(1/18) := by dsimp [c]; field_simp; norm_num
    _ ≤ c * (∑ r : Fin 4, (C.degree (v r) : ℝ)) - 4*(1/18) := by
      gcongr
    _ = ∑ r : Fin 4, (c*(C.degree (v r) : ℝ) - 1/18) := by
      rw [sum_sub_distrib,← mul_sum]
      simp
    _ ≤ ∑ r : Fin 4, C.weight (P.output (q,r)) := by
      apply sum_le_sum
      intro r _
      exact weight_tangent (by exact_mod_cast hn) (by have := hd r; exact_mod_cast this)

lemma MarkedPacking.weight_count (hn : 0 < n) :
    (2/3 : ℝ) * (P.goodPairs.card : ℝ) ≤ (C.totalDegree : ℝ) := by
  classical
  have h₁ : (2/3 : ℝ) * (P.goodPairs.card : ℝ) ≤
      ∑ r : P.Occurrence, C.weight (P.output r) := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ _q : P.Active, (2/3 : ℝ) := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun q _ => P.star_weight hn q)
  refine h₁.trans ?_
  have hm : ∀ r ∈ (univ : Finset P.Occurrence), P.output r ∈ C.outside :=
    fun r _ => P.output_outside r
  rw [← sum_fiberwise_of_maps_to hm (fun r => C.weight (P.output r)), Coil.totalDegree, Nat.cast_sum]
  apply sum_le_sum
  intro v hv
  change (∑ r ∈ P.fiber v, C.weight (P.output r)) ≤ _
  have he : (∑ r ∈ P.fiber v, C.weight (P.output r)) =
      (P.fiber v).card * C.weight v := by
    calc
      _ = (∑ _r ∈ P.fiber v, C.weight v) := by
        apply sum_congr rfl
        intro r hr
        rw [(mem_filter.mp hr).2]
      _ = _ := by simp
  rw [he]
  have hd := C.degree_le v
  have hcard : ((P.fiber v).card : ℝ) ≤ 2 * ((n : ℝ) - (C.degree v : ℝ)) := by
    have hcast : ((P.fiber v).card : ℝ) ≤ 2 * (↑(n - C.degree v) : ℝ) := by
      exact_mod_cast P.fiber_count v
    rwa [Nat.cast_sub hd] at hcast
  have hnn : 0 ≤ C.weight v := by
    unfold Coil.weight
    exact div_nonneg (by positivity) (mul_nonneg (by norm_num) (sub_nonneg.mpr (by exact_mod_cast hd)))
  refine (mul_le_mul_of_nonneg_right hcard hnn).trans ?_
  unfold Coil.weight
  by_cases h0 : (2 : ℝ)*((n:ℝ)-(C.degree v:ℝ)) = 0
  · simp [h0]
  · rw [mul_div_cancel₀ _ h0]

lemma Coil.deficit (C : Coil n L) (hn : 0 < n) :
    ((L/18 : ℕ) : ℝ)*(Real.sqrt (n : ℝ)/Real.sqrt 6 - 6) ≤ C.totalDegree := by
  by_cases hL : 18 ≤ L
  · obtain ⟨P⟩ := C.make_packing (by omega : 9 ≤ L)
    have hk : 0 < L/18 := by omega
    have hm : 0 < P.largeVertices.card := by
      let i : Fin (L/18) := ⟨0,hk⟩
      exact card_pos.mpr ⟨P.N i,mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩
    have hhigh : (n : ℝ)*(P.largeVertices.card : ℝ) ≤ 4*(C.totalDegree : ℝ) := by
      exact_mod_cast P.high_count
    have hpair : ((L/18 : ℕ) : ℝ)*((L/18 : ℕ) : ℝ) ≤
        (P.largeVertices.card : ℝ)*(P.samePairs.card : ℝ) := by
      exact_mod_cast P.samePairs_cauchy
    have hgood : (P.samePairs.card : ℝ) ≤ (P.goodPairs.card : ℝ) + 16*((L/18 : ℕ) : ℝ) := by
      exact_mod_cast P.good_count
    have hw := P.weight_count hn
    have hh := mul_le_mul_of_nonneg_left hgood (show 0 ≤ (P.largeVertices.card : ℝ) by positivity)
    have hh' := mul_le_mul_of_nonneg_right hw (show 0 ≤ (P.largeVertices.card : ℝ) by positivity)
    apply degree_from_two_estimates (by positivity) (by exact_mod_cast hk) (by exact_mod_cast hm)
      (by positivity) hhigh
    nlinarith only [hpair,hh,hh']
  · have hdiv : L/18=0 := by omega
    simp [hdiv]

end CoilBound

theorem OMA.solution : type_of% @SnakeInBox.coil_upper_bound := by
  intro n hn
  change (SnakeInBox.LongestCoilInTheBox n : ℝ) ≤ CoilBound.finalBound n
  apply CoilBound.final_of_coils hn
  intro L C
  exact CoilBound.final_bound_arithmetic hn (C.real_degree_identity hn) (fun _ => C.deficit (by omega))
