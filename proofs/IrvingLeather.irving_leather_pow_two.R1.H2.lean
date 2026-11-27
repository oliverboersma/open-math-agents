import OMAReductions.R_IrvingLeather_irving_leather_pow_two_R1
import Mathlib.Tactic

-- Step IrvingLeather.irving_leather_pow_two.R1.H2: hypothesis H2 of reduction IrvingLeather.irving_leather_pow_two.R1
-- Credit: @tatashbar

/-! No profile of size 4 has more than 10 stable matchings (Eilers 1999, by computer search).

The proof here is a kernel-checked branch-and-bound. Relabel the women so that man 0 ranks them in
their natural order, and relabel men 1, 2, 3 so that woman 0 ranks them in their natural order.
Then decide the remaining agents one at a time (man 1, woman 1, man 2, woman 2, man 3, woman 3),
keeping a 24-bit mask of the matchings blocked by a pair of agents decided so far. A branch is
closed once at least 14 of the 24 matchings are blocked. The whole tree has 123912 nodes; it is
split into 27 lemmas, each closed by kernel evaluation. -/

open StableMarriage

namespace M4

/- ## The 24 permutations of `Fin 4`, as rank vectors in lexicographic order -/

def T : Fin 24 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3],
    ![0, 1, 3, 2],
    ![0, 2, 1, 3],
    ![0, 2, 3, 1],
    ![0, 3, 1, 2],
    ![0, 3, 2, 1],
    ![1, 0, 2, 3],
    ![1, 0, 3, 2],
    ![1, 2, 0, 3],
    ![1, 2, 3, 0],
    ![1, 3, 0, 2],
    ![1, 3, 2, 0],
    ![2, 0, 1, 3],
    ![2, 0, 3, 1],
    ![2, 1, 0, 3],
    ![2, 1, 3, 0],
    ![2, 3, 0, 1],
    ![2, 3, 1, 0],
    ![3, 0, 1, 2],
    ![3, 0, 2, 1],
    ![3, 1, 0, 2],
    ![3, 1, 2, 0],
    ![3, 2, 0, 1],
    ![3, 2, 1, 0]]

def Ti : Fin 24 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3],
    ![0, 1, 3, 2],
    ![0, 2, 1, 3],
    ![0, 3, 1, 2],
    ![0, 2, 3, 1],
    ![0, 3, 2, 1],
    ![1, 0, 2, 3],
    ![1, 0, 3, 2],
    ![2, 0, 1, 3],
    ![3, 0, 1, 2],
    ![2, 0, 3, 1],
    ![3, 0, 2, 1],
    ![1, 2, 0, 3],
    ![1, 3, 0, 2],
    ![2, 1, 0, 3],
    ![3, 1, 0, 2],
    ![2, 3, 0, 1],
    ![3, 2, 0, 1],
    ![1, 2, 3, 0],
    ![1, 3, 2, 0],
    ![2, 1, 3, 0],
    ![3, 1, 2, 0],
    ![2, 3, 1, 0],
    ![3, 2, 1, 0]]

theorem Ti_T : ∀ i x, Ti i (T i x) = x := by decide +kernel

theorem T_Ti : ∀ i x, T i (Ti i x) = x := by decide +kernel

def permOf (i : Fin 24) : Equiv.Perm (Fin 4) := ⟨T i, Ti i, Ti_T i, T_Ti i⟩

theorem T_inj : ∀ i j, (∀ x, T i x = T j x) → i = j := by decide +kernel

theorem permOf_injective : Function.Injective permOf := by
  intro i j h
  exact T_inj i j (fun x => congrArg (fun e : Equiv.Perm (Fin 4) => e x) h)

theorem permOf_surjective : Function.Surjective permOf :=
  ((Fintype.bijective_iff_injective_and_card permOf).2
    ⟨permOf_injective, by rw [Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]; rfl⟩).2

theorem permOf_zero : permOf 0 = 1 := by
  apply Equiv.ext
  intro x
  revert x
  decide

/- ## Relabelling men and women does not change the number of stable matchings -/

/-- Rename man `m` to `σ m` and woman `w` to `τ w`. -/
def relabel (p : Profile 4) (σ τ : Equiv.Perm (Fin 4)) : Profile 4 :=
  ⟨fun m => τ.trans (p.manRank (σ m)), fun w => σ.trans (p.womanRank (τ w))⟩

/-- The matching of the original profile that corresponds to `μ`. -/
def conj (σ τ : Equiv.Perm (Fin 4)) : Matching 4 ≃ Matching 4 where
  toFun μ := σ.symm.trans (μ.trans τ)
  invFun ν := σ.trans (ν.trans τ.symm)
  left_inv μ := by ext x; simp
  right_inv ν := by ext x; simp

theorem blocking_relabel (p : Profile 4) (σ τ : Equiv.Perm (Fin 4)) (μ : Matching 4)
    (m w : Fin 4) :
    IsBlockingPair (relabel p σ τ) μ m w ↔ IsBlockingPair p (conj σ τ μ) (σ m) (τ w) := by
  simp [IsBlockingPair, relabel, conj]

theorem stable_relabel (p : Profile 4) (σ τ : Equiv.Perm (Fin 4)) (μ : Matching 4) :
    IsStable (relabel p σ τ) μ ↔ IsStable p (conj σ τ μ) := by
  constructor
  · intro h m w hb
    refine h (σ.symm m) (τ.symm w) ?_
    rw [blocking_relabel]
    simpa using hb
  · intro h m w hb
    exact h (σ m) (τ w) ((blocking_relabel p σ τ μ m w).1 hb)

theorem num_relabel (p : Profile 4) (σ τ : Equiv.Perm (Fin 4)) :
    numStableMatchings (relabel p σ τ) = numStableMatchings p := by
  classical
  unfold numStableMatchings
  exact Fintype.card_congr ((conj σ τ).subtypeEquiv (fun μ => stable_relabel p σ τ μ))

theorem sort3_tab : ∀ i : Fin 24, ∃ s : Fin 24,
    T s 0 = 0 ∧ T i (T s 1) < T i (T s 2) ∧ T i (T s 2) < T i (T s 3) := by decide +kernel

theorem sort3 (ρ : Equiv.Perm (Fin 4)) : ∃ σ : Equiv.Perm (Fin 4),
    σ 0 = 0 ∧ ρ (σ 1) < ρ (σ 2) ∧ ρ (σ 2) < ρ (σ 3) := by
  obtain ⟨i, rfl⟩ := permOf_surjective ρ
  obtain ⟨s, h⟩ := sort3_tab i
  exact ⟨permOf s, h⟩

/- ## Bit masks

A mask is a natural number below `2 ^ 24`; bit `j` stands for the matching `permOf j`. -/

abbrev R := Nat × Nat × Nat × Nat

/-- The number of set bits among the lowest 24. -/
def pc (b : Nat) : Nat :=
  (Nat.add (Nat.mod (Nat.div b 1) 2) (Nat.add (Nat.mod (Nat.div b 2) 2) (Nat.add (Nat.mod (Nat.div b 4) 2) (Nat.add (Nat.mod (Nat.div b 8) 2) (Nat.add (Nat.mod (Nat.div b 16) 2) (Nat.add (Nat.mod (Nat.div b 32) 2) (Nat.add (Nat.mod (Nat.div b 64) 2) (Nat.add (Nat.mod (Nat.div b 128) 2) (Nat.add (Nat.mod (Nat.div b 256) 2) (Nat.add (Nat.mod (Nat.div b 512) 2) (Nat.add (Nat.mod (Nat.div b 1024) 2) (Nat.add (Nat.mod (Nat.div b 2048) 2) (Nat.add (Nat.mod (Nat.div b 4096) 2) (Nat.add (Nat.mod (Nat.div b 8192) 2) (Nat.add (Nat.mod (Nat.div b 16384) 2) (Nat.add (Nat.mod (Nat.div b 32768) 2) (Nat.add (Nat.mod (Nat.div b 65536) 2) (Nat.add (Nat.mod (Nat.div b 131072) 2) (Nat.add (Nat.mod (Nat.div b 262144) 2) (Nat.add (Nat.mod (Nat.div b 524288) 2) (Nat.add (Nat.mod (Nat.div b 1048576) 2) (Nat.add (Nat.mod (Nat.div b 2097152) 2) (Nat.add (Nat.mod (Nat.div b 4194304) 2) (Nat.mod (Nat.div b 8388608) 2))))))))))))))))))))))))

theorem pc_def (b : Nat) : pc b =
    b / 1 % 2 + (b / 2 % 2 + (b / 4 % 2 + (b / 8 % 2 + (b / 16 % 2 + (b / 32 % 2 + (b / 64 % 2 + (b / 128 % 2 + (b / 256 % 2 + (b / 512 % 2 + (b / 1024 % 2 + (b / 2048 % 2 + (b / 4096 % 2 + (b / 8192 % 2 + (b / 16384 % 2 + (b / 32768 % 2 + (b / 65536 % 2 + (b / 131072 % 2 + (b / 262144 % 2 + (b / 524288 % 2 + (b / 1048576 % 2 + (b / 2097152 % 2 + (b / 4194304 % 2 + (b / 8388608 % 2))))))))))))))))))))))) := rfl

/-- Evaluate the mask before continuing. -/
def force (b : Nat) (f : Nat → Bool) : Bool := Nat.casesOn b (f 0) (fun k => f (Nat.succ k))

theorem force_eq (b : Nat) (f : Nat → Bool) : force b f = f b := by
  cases b <;> rfl

def cmp (r : R) (k : Fin 4) : Nat := ![r.1, r.2.1, r.2.2.1, r.2.2.2] k

def dflt : R := (0, 0, 0, 0)

/- ### Tables

For man `m` with rank vector `T a`, the record is `(U 0, U 1, U 2, U 3)` where bit `j` of `U w` says
that he prefers `w` to his partner in matching `j`. For woman `w` with rank vector `T b`, the record
is `(V 0, V 1, V 2, V 3)` where bit `j` of `V m` says that she prefers `m` to her partner in
matching `j`. The pair `(m, w)` blocks matching `j` when bit `j` is set in both. -/

def u0 : R := (16777152, 16773120, 16515072, 0)

def w0x0 : R := (16777152, 15978240, 10652160, 0)
def w0x1 : R := (15978240, 15978303, 10652160, 0)
def w0x2 : R := (10652160, 15978303, 10652223, 0)
def w0x3 : R := (0, 15978303, 10652223, 63)

def W0 : List R :=
  [w0x0, w0x1, w0x2, w0x3]

def W0all : List R :=
  [(16777152, 15978240, 10652160, 0),
   (16777152, 15978240, 0, 5326080),
   (16777152, 10652160, 11451072, 0),
   (16777152, 5326080, 0, 6124992),
   (16777152, 0, 11451072, 798912),
   (16777152, 0, 798912, 6124992),
   (15978240, 15978303, 10652160, 0),
   (15978240, 15978303, 0, 5326080),
   (11451072, 10652160, 11451135, 0),
   (6124992, 5326080, 0, 6125055),
   (11451072, 0, 11451135, 798912),
   (6124992, 0, 798912, 6125055),
   (10652160, 15978303, 10652223, 0),
   (5326080, 15978303, 0, 5326143),
   (10652160, 10652223, 11451135, 0),
   (5326080, 5326143, 0, 6125055),
   (798912, 0, 11451135, 798975),
   (798912, 0, 798975, 6125055),
   (0, 15978303, 10652223, 63),
   (0, 15978303, 63, 5326143),
   (0, 10652223, 11451135, 63),
   (0, 5326143, 63, 6125055),
   (0, 63, 11451135, 798975),
   (0, 63, 798975, 6125055)]

def m1x0 : R := (15978303, 12783420, 199728, 0)
def m1x1 : R := (15978303, 12783420, 0, 12583692)
def m1x2 : R := (15978303, 199728, 3394611, 0)
def m1x3 : R := (15978303, 12583692, 0, 15778575)
def m1x4 : R := (15978303, 0, 3394611, 3194883)
def m1x5 : R := (15978303, 0, 3194883, 15778575)
def m1x6 : R := (12783420, 13582332, 199728, 0)
def m1x7 : R := (12783420, 13582332, 0, 12583692)
def m1x8 : R := (3394611, 199728, 4193523, 0)
def m1x9 : R := (15778575, 12583692, 0, 16577487)
def m1x10 : R := (3394611, 0, 4193523, 3194883)
def m1x11 : R := (15778575, 0, 3194883, 16577487)
def m1x12 : R := (199728, 13582332, 998640, 0)
def m1x13 : R := (12583692, 13582332, 0, 13382604)
def m1x14 : R := (199728, 998640, 4193523, 0)
def m1x15 : R := (12583692, 13382604, 0, 16577487)
def m1x16 : R := (3194883, 0, 4193523, 3993795)
def m1x17 : R := (3194883, 0, 3993795, 16577487)
def m1x18 : R := (0, 13582332, 998640, 798912)
def m1x19 : R := (0, 13582332, 798912, 13382604)
def m1x20 : R := (0, 998640, 4193523, 798912)
def m1x21 : R := (0, 13382604, 798912, 16577487)
def m1x22 : R := (0, 798912, 4193523, 3993795)
def m1x23 : R := (0, 798912, 3993795, 16577487)

def M1 : List R :=
  [m1x0, m1x1, m1x2, m1x3, m1x4, m1x5, m1x6, m1x7, m1x8, m1x9, m1x10, m1x11, m1x12, m1x13, m1x14, m1x15, m1x16, m1x17, m1x18, m1x19, m1x20, m1x21, m1x22, m1x23]

def W1 : List R :=
  [(16773183, 13578300, 4792360, 0),
   (16773183, 13578300, 0, 8785940),
   (16773183, 4792360, 7987243, 0),
   (16773183, 8785940, 0, 11980823),
   (16773183, 0, 7987243, 3194883),
   (16773183, 0, 3194883, 11980823),
   (13578300, 13582332, 4792360, 0),
   (13578300, 13582332, 0, 8785940),
   (7987243, 4792360, 7991275, 0),
   (11980823, 8785940, 0, 11984855),
   (7987243, 0, 7991275, 3194883),
   (11980823, 0, 3194883, 11984855),
   (4792360, 13582332, 4796392, 0),
   (8785940, 13582332, 0, 8789972),
   (4792360, 4796392, 7991275, 0),
   (8785940, 8789972, 0, 11984855),
   (3194883, 0, 7991275, 3198915),
   (3194883, 0, 3198915, 11984855),
   (0, 13582332, 4796392, 4032),
   (0, 13582332, 4032, 8789972),
   (0, 4796392, 7991275, 4032),
   (0, 8789972, 4032, 11984855),
   (0, 4032, 7991275, 3198915),
   (0, 4032, 3198915, 11984855)]

def M2 : List R :=
  [(11451135, 2665195, 41610, 0),
   (11451135, 2665195, 0, 2623585),
   (11451135, 41610, 8827550, 0),
   (11451135, 2623585, 0, 11409525),
   (11451135, 0, 8827550, 8785940),
   (11451135, 0, 8785940, 11409525),
   (2665195, 7991275, 41610, 0),
   (2665195, 7991275, 0, 2623585),
   (8827550, 41610, 14153630, 0),
   (11409525, 2623585, 0, 16735605),
   (8827550, 0, 14153630, 8785940),
   (11409525, 0, 8785940, 16735605),
   (41610, 7991275, 5367690, 0),
   (2623585, 7991275, 0, 7949665),
   (41610, 5367690, 14153630, 0),
   (2623585, 7949665, 0, 16735605),
   (8785940, 0, 14153630, 14112020),
   (8785940, 0, 14112020, 16735605),
   (0, 7991275, 5367690, 5326080),
   (0, 7991275, 5326080, 7949665),
   (0, 5367690, 14153630, 5326080),
   (0, 7949665, 5326080, 16735605),
   (0, 5326080, 14153630, 14112020),
   (0, 5326080, 14112020, 16735605)]

def W2 : List R :=
  [(16519167, 3935475, 1311890, 0),
   (16519167, 3935475, 0, 2623585),
   (16519167, 1311890, 13895582, 0),
   (16519167, 2623585, 0, 15207277),
   (16519167, 0, 13895582, 12583692),
   (16519167, 0, 12583692, 15207277),
   (3935475, 4193523, 1311890, 0),
   (3935475, 4193523, 0, 2623585),
   (13895582, 1311890, 14153630, 0),
   (15207277, 2623585, 0, 15465325),
   (13895582, 0, 14153630, 12583692),
   (15207277, 0, 12583692, 15465325),
   (1311890, 4193523, 1569938, 0),
   (2623585, 4193523, 0, 2881633),
   (1311890, 1569938, 14153630, 0),
   (2623585, 2881633, 0, 15465325),
   (12583692, 0, 14153630, 12841740),
   (12583692, 0, 12841740, 15465325),
   (0, 4193523, 1569938, 258048),
   (0, 4193523, 258048, 2881633),
   (0, 1569938, 14153630, 258048),
   (0, 2881633, 258048, 15465325),
   (0, 258048, 14153630, 12841740),
   (0, 258048, 12841740, 15465325)]

def M3 : List R :=
  [(6125055, 1332695, 20805, 0),
   (6125055, 1332695, 0, 1311890),
   (6125055, 20805, 4813165, 0),
   (6125055, 1311890, 0, 6104250),
   (6125055, 0, 4813165, 4792360),
   (6125055, 0, 4792360, 6104250),
   (1332695, 11984855, 20805, 0),
   (1332695, 11984855, 0, 1311890),
   (4813165, 20805, 15465325, 0),
   (6104250, 1311890, 0, 16756410),
   (4813165, 0, 15465325, 4792360),
   (6104250, 0, 4792360, 16756410),
   (20805, 11984855, 10672965, 0),
   (1311890, 11984855, 0, 11964050),
   (20805, 10672965, 15465325, 0),
   (1311890, 11964050, 0, 16756410),
   (4792360, 0, 15465325, 15444520),
   (4792360, 0, 15444520, 16756410),
   (0, 11984855, 10672965, 10652160),
   (0, 11984855, 10652160, 11964050),
   (0, 10672965, 15465325, 10652160),
   (0, 11964050, 10652160, 16756410),
   (0, 10652160, 15465325, 15444520),
   (0, 10652160, 15444520, 16756410)]

def W3 : List R :=
  [(262143, 62415, 20805, 0),
   (262143, 62415, 0, 41610),
   (262143, 20805, 220533, 0),
   (262143, 41610, 0, 241338),
   (262143, 0, 220533, 199728),
   (262143, 0, 199728, 241338),
   (62415, 16577487, 20805, 0),
   (62415, 16577487, 0, 41610),
   (220533, 20805, 16735605, 0),
   (241338, 41610, 0, 16756410),
   (220533, 0, 16735605, 199728),
   (241338, 0, 199728, 16756410),
   (20805, 16577487, 16535877, 0),
   (41610, 16577487, 0, 16556682),
   (20805, 16535877, 16735605, 0),
   (41610, 16556682, 0, 16756410),
   (199728, 0, 16735605, 16714800),
   (199728, 0, 16714800, 16756410),
   (0, 16577487, 16535877, 16515072),
   (0, 16577487, 16515072, 16556682),
   (0, 16535877, 16735605, 16515072),
   (0, 16556682, 16515072, 16756410),
   (0, 16515072, 16735605, 16714800),
   (0, 16515072, 16714800, 16756410)]

theorem u0_sound : ∀ (w : Fin 4) (j : Fin 24),
    (cmp u0 w).testBit j = true → T 0 w < T 0 (T j 0) := by decide +kernel

theorem M1_sound : ∀ (a : Fin 24) (w : Fin 4) (j : Fin 24),
    (cmp (M1.getD a dflt) w).testBit j = true → T a w < T a (T j 1) := by decide +kernel

theorem M2_sound : ∀ (a : Fin 24) (w : Fin 4) (j : Fin 24),
    (cmp (M2.getD a dflt) w).testBit j = true → T a w < T a (T j 2) := by decide +kernel

theorem M3_sound : ∀ (a : Fin 24) (w : Fin 4) (j : Fin 24),
    (cmp (M3.getD a dflt) w).testBit j = true → T a w < T a (T j 3) := by decide +kernel

theorem W0_sound : ∀ (b : Fin 24) (m : Fin 4) (j : Fin 24),
    (cmp (W0all.getD b dflt) m).testBit j = true → T b m < T b (Ti j 0) := by decide +kernel

theorem W1_sound : ∀ (b : Fin 24) (m : Fin 4) (j : Fin 24),
    (cmp (W1.getD b dflt) m).testBit j = true → T b m < T b (Ti j 1) := by decide +kernel

theorem W2_sound : ∀ (b : Fin 24) (m : Fin 4) (j : Fin 24),
    (cmp (W2.getD b dflt) m).testBit j = true → T b m < T b (Ti j 2) := by decide +kernel

theorem W3_sound : ∀ (b : Fin 24) (m : Fin 4) (j : Fin 24),
    (cmp (W3.getD b dflt) m).testBit j = true → T b m < T b (Ti j 3) := by decide +kernel

theorem M1_mem : ∀ a : Fin 24, M1.getD a dflt ∈ M1 := by decide +kernel

theorem M2_mem : ∀ a : Fin 24, M2.getD a dflt ∈ M2 := by decide +kernel

theorem M3_mem : ∀ a : Fin 24, M3.getD a dflt ∈ M3 := by decide +kernel

theorem W1_mem : ∀ b : Fin 24, W1.getD b dflt ∈ W1 := by decide +kernel

theorem W2_mem : ∀ b : Fin 24, W2.getD b dflt ∈ W2 := by decide +kernel

theorem W3_mem : ∀ b : Fin 24, W3.getD b dflt ∈ W3 := by decide +kernel

theorem W0_mem : ∀ b : Fin 24, T b 1 < T b 2 → T b 2 < T b 3 → W0all.getD b dflt ∈ W0 := by
  decide +kernel

/- ## The search

Agents are decided in the order man 0, woman 0, man 1, woman 1, man 2, woman 2, man 3, woman 3.
The mask `B` collects the matchings blocked by a pair of decided agents. A branch is closed as soon
as at least 14 of the 24 matchings are blocked. -/

def chk6 (u0 u1 u2 u3 : R) (B : Nat) : Bool :=
  W3.all fun v3 => Nat.ble 14 (pc (Nat.lor (Nat.lor (Nat.lor (Nat.lor B (Nat.land u0.2.2.2 v3.1))
    (Nat.land u1.2.2.2 v3.2.1)) (Nat.land u2.2.2.2 v3.2.2.1)) (Nat.land u3.2.2.2 v3.2.2.2)))

def chk5 (u0 u1 u2 v0 v1 v2 : R) (B : Nat) : Bool :=
  M3.all fun u3 => force (Nat.lor (Nat.lor (Nat.lor B (Nat.land u3.1 v0.2.2.2))
    (Nat.land u3.2.1 v1.2.2.2)) (Nat.land u3.2.2.1 v2.2.2.2))
    fun B5 => Nat.ble 14 (pc B5) || chk6 u0 u1 u2 u3 B5

def chk4 (u0 u1 u2 v0 v1 : R) (B : Nat) : Bool :=
  W2.all fun v2 => force (Nat.lor (Nat.lor (Nat.lor B (Nat.land u0.2.2.1 v2.1))
    (Nat.land u1.2.2.1 v2.2.1)) (Nat.land u2.2.2.1 v2.2.2.1))
    fun B4 => Nat.ble 14 (pc B4) || chk5 u0 u1 u2 v0 v1 v2 B4

def chk3 (u0 u1 v0 v1 : R) (B : Nat) : Bool :=
  M2.all fun u2 => force (Nat.lor (Nat.lor B (Nat.land u2.1 v0.2.2.1)) (Nat.land u2.2.1 v1.2.2.1))
    fun B3 => Nat.ble 14 (pc B3) || chk4 u0 u1 u2 v0 v1 B3

def chk2 (u0 u1 v0 : R) (B : Nat) : Bool :=
  W1.all fun v1 => force (Nat.lor (Nat.lor B (Nat.land u0.2.1 v1.1)) (Nat.land u1.2.1 v1.2.1))
    fun B2 => Nat.ble 14 (pc B2) || chk3 u0 u1 v0 v1 B2

def chk1b (u0 u1 v0 : R) (B : Nat) : Bool :=
  force (Nat.lor B (Nat.land u1.1 v0.2.1)) fun B1 => Nat.ble 14 (pc B1) || chk2 u0 u1 v0 B1

def chk1 (u0 v0 : R) (B : Nat) : Bool := M1.all fun u1 => chk1b u0 u1 v0 B

def chk0a (v0 : R) : Bool := chk1 u0 v0 (Nat.land u0.1 v0.1)

def chk0 : Bool := W0.all chk0a

/- ## Soundness -/

/-- Every matching whose bit is set in `B` is unstable. -/
def MS (p : Profile 4) (B : Nat) : Prop :=
  ∀ j : Fin 24, B.testBit j = true → ¬ IsStable p (permOf j)

theorem MS_or {p : Profile 4} {B C : Nat} (hB : MS p B) (hC : MS p C) : MS p (Nat.lor B C) := by
  intro j hj
  have hj' : (B ||| C).testBit j = true := hj
  rw [Nat.testBit_lor, Bool.or_eq_true] at hj'
  rcases hj' with h | h
  · exact hB j h
  · exact hC j h

theorem MS_and {p : Profile 4} {a b : Fin 24} {ru rv : R} (m w : Fin 4)
    (ha : permOf a = p.manRank m) (hb : permOf b = p.womanRank w)
    (hu : ∀ (w : Fin 4) (j : Fin 24), (cmp ru w).testBit j = true → T a w < T a (T j m))
    (hv : ∀ (m : Fin 4) (j : Fin 24), (cmp rv m).testBit j = true → T b m < T b (Ti j w)) :
    MS p (Nat.land (cmp ru w) (cmp rv m)) := by
  intro j hj hs
  have hj' : (cmp ru w &&& cmp rv m).testBit j = true := hj
  rw [Nat.testBit_land, Bool.and_eq_true] at hj'
  have h1 := hu w j hj'.1
  have h2 := hv m j hj'.2
  refine hs m w ⟨?_, ?_, ?_⟩
  · intro e
    have e' : T j m = w := e
    rw [e'] at h1
    exact lt_irrefl _ h1
  · rw [← ha]
    exact h1
  · rw [← hb]
    exact h2

theorem pc_eq (B : Nat) :
    pc B = (Finset.univ.filter fun j : Fin 24 => B.testBit j = true).card := by
  rw [Finset.card_filter]
  have h : ∀ j : Fin 24, (if B.testBit j = true then 1 else 0) = B / 2 ^ (j : ℕ) % 2 := by
    intro j
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (B / 2 ^ (j : ℕ)) with h | h <;> simp [h]
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => B / 2 ^ i % 2) 24, pc_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

theorem prune {p : Profile 4} {B : Nat} (hB : MS p B) (h : Nat.ble 14 (pc B) = true) :
    numStableMatchings p ≤ 10 := by
  classical
  have h14 : 14 ≤ pc B := Nat.le_of_ble_eq_true h
  have h1 : Fintype.card {μ : Matching 4 // IsStable p μ} ≤
      Fintype.card {j : Fin 24 // IsStable p (permOf j)} :=
    Fintype.card_le_of_surjective
      (fun j : {j : Fin 24 // IsStable p (permOf j)} =>
        (⟨permOf j.1, j.2⟩ : {μ : Matching 4 // IsStable p μ}))
      (by
        rintro ⟨μ, hμ⟩
        obtain ⟨j, rfl⟩ := permOf_surjective μ
        exact ⟨⟨j, hμ⟩, rfl⟩)
  have h2 : Fintype.card {j : Fin 24 // IsStable p (permOf j)} ≤
      Fintype.card {j : Fin 24 // ¬ (B.testBit j = true)} :=
    Fintype.card_subtype_mono (fun j : Fin 24 => IsStable p (permOf j))
      (fun j : Fin 24 => ¬ (B.testBit j = true)) (fun j hj hb => hB j hb hj)
  have h3 : Fintype.card {j : Fin 24 // ¬ (B.testBit j = true)} = 24 - pc B := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, pc_eq, Fintype.card_subtype]
  have h4 : numStableMatchings p = Fintype.card {μ : Matching 4 // IsStable p μ} := by
    unfold numStableMatchings
    congr
  omega

theorem t0_0 : chk0a w0x0 = true := by decide +kernel

theorem t0_1 : chk0a w0x1 = true := by decide +kernel

theorem t0_2 : chk0a w0x2 = true := by decide +kernel

theorem t3_0 : chk1b u0 m1x0 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_1 : chk1b u0 m1x1 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_2 : chk1b u0 m1x2 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_3 : chk1b u0 m1x3 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_4 : chk1b u0 m1x4 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_5 : chk1b u0 m1x5 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_6 : chk1b u0 m1x6 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_7 : chk1b u0 m1x7 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_8 : chk1b u0 m1x8 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_9 : chk1b u0 m1x9 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_10 : chk1b u0 m1x10 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_11 : chk1b u0 m1x11 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_12 : chk1b u0 m1x12 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_13 : chk1b u0 m1x13 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_14 : chk1b u0 m1x14 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_15 : chk1b u0 m1x15 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_16 : chk1b u0 m1x16 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_17 : chk1b u0 m1x17 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_18 : chk1b u0 m1x18 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_19 : chk1b u0 m1x19 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_20 : chk1b u0 m1x20 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_21 : chk1b u0 m1x21 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_22 : chk1b u0 m1x22 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t3_23 : chk1b u0 m1x23 w0x3 (Nat.land u0.1 w0x3.1) = true := by decide +kernel

theorem t0_3 : chk0a w0x3 = true := by
  unfold chk0a chk1
  refine List.all_eq_true.mpr ?_
  intro u1 hu1
  simp only [M1, List.mem_cons, List.mem_nil_iff, or_false] at hu1
  rcases hu1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact t3_0
  · exact t3_1
  · exact t3_2
  · exact t3_3
  · exact t3_4
  · exact t3_5
  · exact t3_6
  · exact t3_7
  · exact t3_8
  · exact t3_9
  · exact t3_10
  · exact t3_11
  · exact t3_12
  · exact t3_13
  · exact t3_14
  · exact t3_15
  · exact t3_16
  · exact t3_17
  · exact t3_18
  · exact t3_19
  · exact t3_20
  · exact t3_21
  · exact t3_22
  · exact t3_23

theorem chk0_true : chk0 = true := by
  unfold chk0
  refine List.all_eq_true.mpr ?_
  intro v hv
  simp only [W0, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact t0_0
  · exact t0_1
  · exact t0_2
  · exact t0_3

/-- The bound for a profile in normal form: man 0 ranks the women in their natural order and
woman 0 ranks men 1, 2, 3 in their natural order. -/
theorem walk (h : chk0 = true) (p : Profile 4) (hm0 : p.manRank 0 = 1)
    (hw12 : p.womanRank 0 1 < p.womanRank 0 2) (hw23 : p.womanRank 0 2 < p.womanRank 0 3) :
    numStableMatchings p ≤ 10 := by
  choose a ha using fun m => permOf_surjective (p.manRank m)
  choose b hb using fun w => permOf_surjective (p.womanRank w)
  have ha0 : a 0 = 0 := permOf_injective (by rw [ha 0, hm0, permOf_zero])
  have hu0 : ∀ (w : Fin 4) (j : Fin 24),
      (cmp u0 w).testBit j = true → T (a 0) w < T (a 0) (T j 0) := by
    rw [ha0]
    exact u0_sound
  have hu1 := M1_sound (a 1)
  have hu2 := M2_sound (a 2)
  have hu3 := M3_sound (a 3)
  have hv0 := W0_sound (b 0)
  have hv1 := W1_sound (b 1)
  have hv2 := W2_sound (b 2)
  have hv3 := W3_sound (b 3)
  have hb12 : T (b 0) 1 < T (b 0) 2 := by
    have e := hw12
    rw [← hb 0] at e
    exact e
  have hb23 : T (b 0) 2 < T (b 0) 3 := by
    have e := hw23
    rw [← hb 0] at e
    exact e
  have mv0 := W0_mem (b 0) hb12 hb23
  have mu1 := M1_mem (a 1)
  have mu2 := M2_mem (a 2)
  have mu3 := M3_mem (a 3)
  have mv1 := W1_mem (b 1)
  have mv2 := W2_mem (b 2)
  have mv3 := W3_mem (b 3)
  generalize W0all.getD (b 0) dflt = v0 at hv0 mv0
  generalize M1.getD (a 1) dflt = u1 at hu1 mu1
  generalize M2.getD (a 2) dflt = u2 at hu2 mu2
  generalize M3.getD (a 3) dflt = u3 at hu3 mu3
  generalize W1.getD (b 1) dflt = v1 at hv1 mv1
  generalize W2.getD (b 2) dflt = v2 at hv2 mv2
  generalize W3.getD (b 3) dflt = v3 at hv3 mv3
  -- the sixteen pairs
  have p00 : MS p (Nat.land u0.1 v0.1) := MS_and 0 0 (ha 0) (hb 0) hu0 hv0
  have p10 : MS p (Nat.land u1.1 v0.2.1) := MS_and 1 0 (ha 1) (hb 0) hu1 hv0
  have p20 : MS p (Nat.land u2.1 v0.2.2.1) := MS_and 2 0 (ha 2) (hb 0) hu2 hv0
  have p30 : MS p (Nat.land u3.1 v0.2.2.2) := MS_and 3 0 (ha 3) (hb 0) hu3 hv0
  have p01 : MS p (Nat.land u0.2.1 v1.1) := MS_and 0 1 (ha 0) (hb 1) hu0 hv1
  have p11 : MS p (Nat.land u1.2.1 v1.2.1) := MS_and 1 1 (ha 1) (hb 1) hu1 hv1
  have p21 : MS p (Nat.land u2.2.1 v1.2.2.1) := MS_and 2 1 (ha 2) (hb 1) hu2 hv1
  have p31 : MS p (Nat.land u3.2.1 v1.2.2.2) := MS_and 3 1 (ha 3) (hb 1) hu3 hv1
  have p02 : MS p (Nat.land u0.2.2.1 v2.1) := MS_and 0 2 (ha 0) (hb 2) hu0 hv2
  have p12 : MS p (Nat.land u1.2.2.1 v2.2.1) := MS_and 1 2 (ha 1) (hb 2) hu1 hv2
  have p22 : MS p (Nat.land u2.2.2.1 v2.2.2.1) := MS_and 2 2 (ha 2) (hb 2) hu2 hv2
  have p32 : MS p (Nat.land u3.2.2.1 v2.2.2.2) := MS_and 3 2 (ha 3) (hb 2) hu3 hv2
  have p03 : MS p (Nat.land u0.2.2.2 v3.1) := MS_and 0 3 (ha 0) (hb 3) hu0 hv3
  have p13 : MS p (Nat.land u1.2.2.2 v3.2.1) := MS_and 1 3 (ha 1) (hb 3) hu1 hv3
  have p23 : MS p (Nat.land u2.2.2.2 v3.2.2.1) := MS_and 2 3 (ha 2) (hb 3) hu2 hv3
  have p33 : MS p (Nat.land u3.2.2.2 v3.2.2.2) := MS_and 3 3 (ha 3) (hb 3) hu3 hv3
  have B1 := MS_or p00 p10
  have B2 := MS_or (MS_or B1 p01) p11
  have B3 := MS_or (MS_or B2 p20) p21
  have B4 := MS_or (MS_or (MS_or B3 p02) p12) p22
  have B5 := MS_or (MS_or (MS_or B4 p30) p31) p32
  have B6 := MS_or (MS_or (MS_or (MS_or B5 p03) p13) p23) p33
  -- walk down the branch of `p`
  unfold chk0 at h
  have k0 := List.all_eq_true.mp h v0 mv0
  unfold chk0a chk1 at k0
  have k1 := List.all_eq_true.mp k0 u1 mu1
  unfold chk1b at k1
  rw [force_eq, Bool.or_eq_true] at k1
  rcases k1 with k1 | k1
  · exact prune B1 k1
  unfold chk2 at k1
  have k2 := List.all_eq_true.mp k1 v1 mv1
  rw [force_eq, Bool.or_eq_true] at k2
  rcases k2 with k2 | k2
  · exact prune B2 k2
  unfold chk3 at k2
  have k3 := List.all_eq_true.mp k2 u2 mu2
  rw [force_eq, Bool.or_eq_true] at k3
  rcases k3 with k3 | k3
  · exact prune B3 k3
  unfold chk4 at k3
  have k4 := List.all_eq_true.mp k3 v2 mv2
  rw [force_eq, Bool.or_eq_true] at k4
  rcases k4 with k4 | k4
  · exact prune B4 k4
  unfold chk5 at k4
  have k5 := List.all_eq_true.mp k4 u3 mu3
  rw [force_eq, Bool.or_eq_true] at k5
  rcases k5 with k5 | k5
  · exact prune B5 k5
  unfold chk6 at k5
  exact prune B6 (List.all_eq_true.mp k5 v3 mv3)

theorem main (p : Profile 4) : numStableMatchings p ≤ 10 := by
  obtain ⟨σ, hσ0, hσ1, hσ2⟩ := sort3 ((relabel p 1 (p.manRank 0).symm).womanRank 0)
  rw [← num_relabel p 1 (p.manRank 0).symm,
    ← num_relabel (relabel p 1 (p.manRank 0).symm) σ 1]
  refine walk chk0_true _ ?_ ?_ ?_
  · apply Equiv.ext
    intro x
    simp [relabel, hσ0]
  · simpa [relabel] using hσ1
  · simpa [relabel] using hσ2

end M4

theorem OMA.solution : OMA.R_IrvingLeather_irving_leather_pow_two_R1.H2 :=
  M4.main
