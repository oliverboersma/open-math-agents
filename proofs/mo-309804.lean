import OMAStatements.S_mo_309804
import Mathlib
/-!
# The Lyapunov trace bound

A fixed point of the correspondence minimizing the Gramian trace pairing
over density matrices gives a state supported on a single eigenspace.
A finite Cayley factorization gives the positive Lyapunov solver, and
regularization by a positive trace-one state yields the required supremum.
The matrix tangent inequality gives the reverse bound and characterizes
attainment: the symmetric part of A must be strictly negative definite.
-/
/-
Brouwer and Kakutani fixed-point theorems, adapted from harfe/fixed-point-theorems-lean4,
commit 0684d5803ab318f7c02b0878928bc0cd0d655d9d.

Copyright (c) 2026 harfe

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-/

section

open Classical


/-
The Cubical Sperner's Lemma.
We mostly follow Kuhn 1960 "Some Combinatorial Lemmas in Topology"
-/

structure SpernerCube where
  n : ℕ
  p : ℕ
  RL : (Fin n → Fin (p+1)) → ℕ
  rl_proper : ∀ (I: Fin n → Fin (p+1) ), RL I ≤ n ∧
      ∀ (k : Fin n), (I k = 0 → RL I ≠ k.1) ∧ (I k = p → RL I ≤ k.1)

namespace SpernerCube

def G (SC : SpernerCube) := Fin SC.n → Fin (SC.p+1)

instance Gfin (SC : SpernerCube): Fintype SC.G := by {
  exact Pi.instFintype
}

end SpernerCube

variable (SC : SpernerCube)
variable {n1 : ℕ}
variable {hn1 : n1 + 1 = SC.n}


def simplex (m:ℕ ) (I : Fin (m+1)→ SC.G) := Function.Injective I
    ∧ ∀ i < m, ∀ j : Fin SC.n, (I (Fin.ofNat _ i) j).1 ≤ (I (Fin.ofNat _ (i+1)) j).1
    ∧ (I (Fin.last m) j).1 ≤ (I 0 j).1 + 1

def complete_simplex (m:ℕ ) (I : Fin (m+1) → SC.G ) := simplex SC m I
    ∧ Set.range (fun (i:Fin (m+1))↦ SC.RL (I i)) = {j : ℕ | j ≤ m}

def is_face I J :=
    simplex SC n1 I ∧ simplex SC SC.n J ∧ Set.range I ⊆ Set.range J

def is_boundary_face I := ∃! J, @is_face SC n1 I J

def complete_boundary_face I := is_boundary_face SC I ∧ complete_simplex SC n1 I

def case_A (I : Fin (n1 +1) → SC.G) := ∃ j, ∀ k, I k j = 0

def case_B (I : Fin (n1 +1) → SC.G) := ∃ j, ∀ k, I k j = Fin.last SC.p

def case_C (I : Fin (n1 +1) → SC.G) :=
    ∃ j, ∃ (q : Fin (SC.p + 1)), (q ≠ 0 ∧ q ≠ Fin.last SC.p ) ∧ ∀ k, I k j = q

def case_D (I : Fin (n1 +1) → SC.G) := ∀ j, ∀ q, ∃ k,I k j ≠ q


lemma one_of_ABCD (I : Fin (n1 +1) → SC.G) :
    case_A SC I ∨ case_B SC I ∨ case_C SC I ∨ case_D SC I := by {
  by_cases h1 : case_D SC I
  exact Or.inr (Or.inr (Or.inr h1))
  unfold case_D at h1
  push Not at h1
  obtain ⟨j , ⟨ q, h2 ⟩⟩ := h1
  by_cases q0 : q = 0
  {
    apply Or.inl
    use j
    rwa [← q0]
  }
  by_cases qp : q = Fin.last SC.p
  {
    apply Or.inr (Or.inl _)
    use j
    intro k
    rwa [h2 k]
  }
  suffices h3 : case_C SC I by {
    simp only [h3, true_or, or_true]
  }
  use j, q
}


section simplex_properties


lemma monotone_1_of_simplex {m:ℕ } (I : Fin (m+1)→ SC.G) (hs : simplex SC m I) (i1 i2 : Fin (m+1))
    (h1 : i1 ≤ i2) : ∀ j, I i1 j ≤ I i2 j := by {
  intro j
  let f := fun i ↦ I i j
  have h2 := @Fin.monotone_iff_le_succ m _ _ f
  suffices h3 : Monotone f by exact (h3 h1)
  rw [h2]
  clear i1 i2 h1
  intro i1
  have h3 := (hs.2 i1.1 i1.2 j).1
  simp only [Fin.val_fin_le] at h3
  convert h3 <;> ext <;> simp [Fin.ofNat_eq_cast, Nat.mod_eq_of_lt]
}

lemma monotone_2_of_simplex {m:ℕ } (I : Fin (m+1)→ SC.G) (hs : simplex SC m I) (i1 i2 : Fin (m+1)) :
    i1 ≤ i2 ↔ ∀ j, I i1 j ≤ I i2 j := by {
  apply Iff.intro
  {
    intro h1 j
    apply monotone_1_of_simplex _ I hs i1 i2 h1
  }
  {
    intro h1
    by_contra h2
    have h3 : i1 ≠ i2 := ne_of_not_le h2
    apply h3
    apply hs.1
    apply funext
    intro j
    apply le_antisymm (h1 j)
    apply monotone_1_of_simplex _ _ hs i2 i1 (le_of_not_ge h2)
  }
}

lemma last_of_simplex {m: ℕ} I (hs : simplex SC m I) j :
    (I (Fin.last m) j).1 ≤ (I 0 j).1 + 1 := by {
  cases m
  simp only [Fin.last_zero, Fin.isValue, le_add_iff_nonneg_right, zero_le]
  rename_i m
  have h3 : 0 < m + 1 := by omega
  exact (hs.2 0 h3 j).2
}

lemma le_add_one_of_simplex {m: ℕ} I (hs : simplex SC m I) (i1 i2 : Fin (m+1)) j :
    (I i1 j).1 ≤ (I i2 j).1 + 1 := by {
  have h1 := last_of_simplex SC I hs j
  apply le_trans _ (le_trans h1 _)
  apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i1)
  apply Nat.add_le_add_right
  apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i2)
}

end simplex_properties


lemma p_ne_zero_of_cube {hn1 : n1 + 1 = SC.n}: Fin.last SC.p ≠ 0 := by {
  simp only [ne_eq, Fin.last_eq_zero_iff]
  intro h1
  let v : Fin SC.n → Fin (SC.p + 1) := fun _ ↦ 0
  have h3 : NeZero SC.n := by {
    rw [←hn1]
    exact instNeZeroNatHAdd_1
  }
  have h4 : v 0 = 0 := by {rfl}
  have h2 := (SC.rl_proper v).2 0
  simp only [Fin.val_zero, ne_eq, h1, Fin.val_eq_zero_iff, nonpos_iff_eq_zero] at h2
  exact h2.1 h4 (h2.2 h4)
}


section simplex_child


def insert_index (j : Fin (SC.n+1)) (a: Fin (n1 +1 )) : Fin (SC.n+1) :=
{ val := if a.val < j.val then a.val else a.val+1,
  isLt := by {
    by_cases hlt : a.val < j.val
    {
      simp only [hlt, ↓reduceIte]
      exact Nat.lt_trans hlt j.2
    }
    {
      simp only [hlt, ↓reduceIte, add_lt_add_iff_right]
      rw [← hn1]
      exact a.2
    }
} }

def delete_vertex (j: Fin (SC.n+1)) (I : Fin (SC.n+1)→ SC.G) : Fin (n1 + 1) → SC.G :=
  fun a ↦ I (@insert_index SC n1 hn1 j a)

lemma insert_index_ne j a : @insert_index SC n1 hn1 j a ≠ j := by {
  apply Fin.ne_of_val_ne
  unfold insert_index
  by_cases hlt : a.val < j.val
  {
    simp only [hlt, ↓reduceIte]
    omega
  }
  {
    simp only [hlt, ↓reduceIte, ne_eq]
    omega
  }
}

lemma almost_surjective_of_insert_index (j : Fin (SC.n+1)) (a : Fin (SC.n+1)) (h : a ≠ j)
    : ∃ k : Fin (n1 + 1) , a = @insert_index SC n1 hn1 j k := by {
  unfold insert_index
  by_cases hlt : a.1 < j.1
  {
    use (Fin.ofNat _ a.1)
    have h2 : a.1 = (Fin.ofNat (n1 + 1) a.1) := by {
      rw [Fin.ofNat_eq_cast, Fin.val_cast_of_lt]
      rw [hn1]
      apply lt_of_lt_of_le hlt
      exact Fin.is_le j
    }
    simp only [← h2, hlt]
    rfl
  }
  {
    have h2 : j.1 < a.1 := by {
      have := Fin.val_ne_of_ne (id (Ne.symm h))
      omega
    }
    let a1 := a.1 - 1
    have h3 : a1 + 1 = a.1 := by {
      show a.1 - 1 + 1 = a.1
      omega
    }
    let a1f := Fin.ofNat (n1 + 1) a1
    use a1f
    ext
    have h4 : a1 < n1 +1 := by {
      have h5 := a.2
      show a.1 - 1 < n1 + 1
      omega
    }
    have h6 : a1f.1 = a1 := by {
      unfold a1f
      simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      exact h4
    }
    have h5 : ¬ (a1f < j.1) := by {
      simp only [not_lt, h6]
      show j.1 ≤ a.1 - 1
      omega
    }
    simp only [h5, ↓reduceIte]
    rw [← h3, h6]
  }
}

lemma insert_index_strict_mono j : StrictMono (@insert_index SC n1 hn1 j) := by {
  intro a b h1
  have h2 : a.1 < b.1 := by {exact h1}
  have h21 : a.1 < b.1 + 1 := by omega
  unfold insert_index
  by_cases h3 : a.1 < j.1
  {
    by_cases h4 : b.1 < j.1
    repeat {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, Fin.val_fin_lt, gt_iff_lt]
      assumption
    }
  }
  {
    by_cases h4 : b.1 < j.1
    {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, gt_iff_lt]
      omega
    }
    {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, gt_iff_lt]
      omega
    }
  }
}

lemma insert_index_inj j : Function.Injective (@insert_index SC n1 hn1 j) := by {
  apply StrictMono.injective
  apply insert_index_strict_mono
}


lemma delete_vertex_inj J {hs : simplex SC SC.n J} i1 i2
    (h1 : @delete_vertex SC n1 hn1 i1 J = @delete_vertex SC n1 hn1 i2 J ) : i1 = i2 := by {
  by_contra h2
  obtain ⟨k, h3 ⟩ := @almost_surjective_of_insert_index SC n1 hn1 i2 i1 h2
  apply @insert_index_ne SC n1 hn1 i1 k
  apply hs.1
  nth_rewrite 2 [h3]
  exact (congrFun h1) k
}

lemma delete_vertex_simplex J {hs : simplex SC SC.n J} i :
    simplex SC n1 (@delete_vertex SC n1 hn1 i J) := by {
  apply And.intro
  {
    intro k1 k2 h2
    apply insert_index_inj SC i
    apply hs.1 h2
  }
  {
    intro i2 hi2 j
    unfold delete_vertex
    apply And.intro
    {
      apply monotone_1_of_simplex SC J hs
      rw [StrictMono.le_iff_le]
      {
        simp only [Fin.ofNat_eq_cast]
        apply Fin.natCast_mono hi2
        exact Nat.le_add_right i2 1
      }
      apply insert_index_strict_mono
    }
    apply le_add_one_of_simplex SC J hs
  }
}

lemma delete_vertex_is_face J {hs : simplex SC SC.n J} i :
    is_face SC (@delete_vertex SC n1 hn1 i J) J := by {
  apply And.intro
  {
    apply delete_vertex_simplex
    exact hs
  }
  {
    apply And.intro hs
    intro c hc
    obtain ⟨ i2, hi2 ⟩ := hc
    use @insert_index SC n1 hn1 i i2
    exact hi2
  }
}

lemma is_id_of_strict_mono (m: ℕ ) (f : Fin m → Fin m) (hsm : StrictMono f)
    : ∀ k, f k = k := by {
  suffices h1 : ∀ (a : ℕ), ∀ k, k.1 < a → f k = k by {
    intro k
    exact h1 m k k.2
  }
  intro a
  induction' a with a ha
  {
    intro k h1
    omega
  }
  {
    have h1 : Function.Injective f := by {exact StrictMono.injective hsm}
    have h2 : Function.Surjective f := Finite.surjective_of_injective h1
    intro k hk
    have h3 j : j < k → f j = j := by {
      intro hj
      apply ha
      omega
    }
    by_cases h4 : f k < k
    apply h1 (h3 (f k) h4)
    simp only [not_lt] at h4
    apply le_antisymm _ h4
    obtain ⟨l, h9⟩ := h2 k
    suffices h8 : k ≤ l by {rwa [← hsm.le_iff_le, h9] at h8}
    by_contra! h6
    have h7 := h3 l h6
    rw [h9] at h7
    rw [h7] at h6
    exact (lt_self_iff_false l).mp h6
  }
}

lemma is_insert_index_of_strict_mono f (hsm : StrictMono f)
    : ∃ j, f = @insert_index SC n1 hn1 j := by {
  have h31 : Function.Injective f := by {exact hsm.injective}
  have hns : ∃ j, ∀ i, f i ≠ j := by {
    by_contra! h1
    have h2 : Function.Surjective f := by {exact h1 }
    have h5 : Function.Bijective f :=  And.intro h31 h2
    have h4 := Nat.card_eq_of_bijective f h5
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.add_right_cancel_iff] at h4
    rw [h4] at hn1
    simp only [Nat.add_eq_left, one_ne_zero] at hn1
  }
  obtain ⟨ j, hj⟩ := hns
  use j
  have h1 : ∀ k1, ∃ k2, f k1 = @insert_index SC n1 hn1 j k2 := by {
    intro k1
    apply almost_surjective_of_insert_index
    exact hj k1
  }
  obtain ⟨g, hg⟩ := axiomOfChoice h1
  have h2 : StrictMono g := by {
    intro k1 k2
    contrapose!
    intro h4
    rw [←hsm.le_iff_le, hg k1, hg k2]
    have h5 := @insert_index_strict_mono SC n1 hn1 j
    rw [h5.le_iff_le]
    exact h4
  }
  have h3 := is_id_of_strict_mono _ g h2
  ext1 k
  rw [hg k, h3 k]
}

lemma child_simplex_char (I : Fin (n1 +1) → SC.G) J {hs : simplex SC SC.n J}
    : is_face SC I J ↔ ∃ i, I = @delete_vertex SC n1 hn1 i J := by {
  apply Iff.intro
  {
    intro h1
    have h2 : ∃ (f : Fin (n1+1) → Fin (SC.n+1)), ∀ k, I k = J (f k) := by {
      have h2 := h1.2.2
      have h3 : ∀ k, ∃ j, I k = J j := by {
        intro k
        have h4 : I k ∈ Set.range I := by {
          exact Set.mem_range_self k
        }
        have h3 := h2 h4
        obtain ⟨j, hj⟩ := h2 h4
        use j
        exact hj.symm
      }
      apply axiom_of_choice h3
    }
    obtain ⟨f, hf ⟩ := h2
    have h31 : Function.Injective f := by {
      intro k1 k2 h2
      apply h1.1.1
      rw [hf k1, hf k2, h2]
    }
    have h3 : StrictMono f := by {
      apply Monotone.strictMono_of_injective _ h31
      intro k1 k2 h2
      rw [monotone_2_of_simplex SC J hs]
      rw [← hf k1, ← hf k2]
      rwa [←monotone_2_of_simplex SC I h1.1]
    }
    obtain ⟨j, hj⟩ := is_insert_index_of_strict_mono SC f h3
    use j
    ext k
    unfold delete_vertex
    rw [hf k, hj]
  }
  {
    intro h1
    obtain ⟨ i, hi⟩ := h1
    rw [hi]
    apply @delete_vertex_is_face SC _ _ J hs
  }
}

end simplex_child


section cases_ABCD

lemma insert_vertex I (v : SC.G) j :
    ∃ J, I = @delete_vertex SC n1 hn1 j J ∧ J j = v := by {
  have h1 : ∀ j2, ∃ w, (j2 = j → w = v)
      ∧ ∀ i, @insert_index SC n1 hn1 j i = j2 → I i = w := by {
    intro j2
    by_cases h1 : j2 = j
    {
      use v
      simp only [implies_true, true_and]
      intro i
      have h3 : @insert_index SC n1 hn1 j i ≠ j := by {apply insert_index_ne}
      simp only [h1, h3, IsEmpty.forall_iff]
    }
    {
      have h3 : ∃ i, j2 = @insert_index SC n1 hn1 j i := by {
        apply almost_surjective_of_insert_index
        exact h1
      }
      obtain ⟨ i, hi⟩ := h3
      use (I i)
      simp only [h1, IsEmpty.forall_iff, true_and]
      intro i2 h2
      congr!
      apply insert_index_inj SC j
      rw [h2, hi]
    }
  }
  obtain ⟨J, h2⟩ := axiomOfChoice h1
  use J
  apply And.intro
  {
    ext i
    exact (h2 (@insert_index SC n1 hn1 j i)).2 i rfl
  }
  exact (h2 j).1 rfl
}

lemma surround_index (j : Fin (SC.n + 1)) (i : Fin (n1 + 1)) (hij : i.1 + 1 = j.1 )
    (hj1 : j ≠ Fin.last SC.n): ((@insert_index SC n1 hn1 j i).1 + 1 = j.1
    ∧ j.1 + 1 = @insert_index SC n1 hn1 j (i+1)) := by {
  unfold insert_index
  have h2 : i.1 < j.1 := by omega
  have h3 : (i+1).1 = i.1 + 1 := by {
    refine Fin.val_add_one_of_lt ?_
    simp only [Nat.succ_eq_add_one]
    show i.1 < n1
    have h6 := Fin.val_lt_last hj1
    omega
  }
  apply And.intro
  {
    simp only [h2, ↓reduceIte]
    exact hij
  }
  simp only [h3, hij, lt_self_iff_false, ↓reduceIte]
}

lemma parent_injective I (hs : simplex SC n1 I) J j
    (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ∉ Set.range I)
    : Function.Injective J := by {
  have h5 j3 : j3 ≠ j → ∃ i3, j3 = @insert_index SC n1 hn1 j i3
    := by {apply almost_surjective_of_insert_index}
  intro j1 j2 h4
  have h7 j3 : J j3 = J j → j3 = j := by {
      intro h7
      by_contra h51
      apply h2
      obtain ⟨i3, hi3⟩ := h5 j3 h51
      use i3
      rw [←h7,h1,hi3]
      rfl
  }
  by_cases h8 : j1 = j
  {
    rw [h8, h7 j2]
    rw [←h8,h4]
  }
  by_cases h9 : j2 = j
  {
    rw [h9, h7 j1]
    rw [←h9,h4]
  }
  obtain ⟨i1, hi1⟩ := h5 j1 h8
  obtain ⟨i2, hi2⟩ := h5 j2 h9
  suffices h11 : i1 = i2 by {rw [hi1,hi2,h11] }
  apply hs.1
  rw [h1]
  unfold delete_vertex
  rw [← hi1,← hi2, h4]
}

lemma parent_simplex_case_BC I (hs : simplex SC n1 I) J
    (h1 : I = @delete_vertex SC n1 hn1 0 J) (h2 : J 0 ≠ I 0)
    (h3 : ∀ k, J 0 k ≤ I 0 k ∧ (I (Fin.last n1) k).1 ≤ (J 0 k).1 + 1) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use 0
    exact h4
  }
  have h4 : J 0 ∉ Set.range I := by {
    intro h5
    obtain ⟨i1, hi1⟩ := h5
    apply h2
    apply funext
    intro k
    apply le_antisymm (h3 k).1
    rw [←hi1]
    apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i1)
  }
  apply And.intro ( parent_injective SC I hs J 0 h1 h4)
  have h5 j2 : j2 < n1 + 1 →  J (Fin.ofNat _ (j2+1)) = I (Fin.ofNat _ j2) := by {
    rw [h1]
    unfold delete_vertex insert_index
    congr! with h7
    simp only [Fin.ofNat_eq_cast, Fin.val_zero, not_lt_zero, ↓reduceIte]
    rw [Fin.val_cast_of_lt, Fin.val_cast_of_lt h7]
    omega
  }
  intro j1 hj1 k1
  apply And.intro
  {
    rw [←hn1] at hj1
    rw [h5 j1 hj1]
    cases j1
    {
      simp only [Fin.ofNat_eq_cast, Fin.val_fin_le]
      exact (h3 k1).1
    }
    rename_i j2
    rw [h5 j2]
    apply monotone_1_of_simplex SC I hs
    simp only [Fin.ofNat_eq_cast]
    apply Fin.natCast_mono
    exact Nat.le_of_lt_succ hj1
    exact Nat.le_add_right j2 1
    exact Nat.lt_of_succ_lt hj1
  }
  {
    have h6 := h5 n1 (lt_add_one n1)
    have e1 : (Fin.ofNat (SC.n + 1) (n1 + 1) : Fin (SC.n + 1)) = Fin.last SC.n := by
      rw [← hn1]; simp [Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    have e2 : (Fin.ofNat (n1 + 1) n1 : Fin (n1 + 1)) = Fin.last n1 := by
      simp [Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    rw [e1, e2] at h6
    rw [congrFun h6 k1]
    exact (h3 k1).2
  }
}

lemma parent_simplex_case_AC I (hs : simplex SC n1 I) J j (hj : j = Fin.last SC.n)
    (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ≠ I (Fin.last n1))
    (h3 : ∀ k, I (Fin.last n1) k ≤ J j k ∧ (J j k).1 ≤ (I 0 k).1 + 1) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use j
    exact h4
  }
  have h4 : J j ∉ Set.range I := by {
    intro h5
    obtain ⟨i1, hi1⟩ := h5
    apply h2
    apply funext
    intro k
    apply le_antisymm _ (h3 k).1
    rw [←hi1]
    apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i1)
  }
  have h5 j2 : j2 < SC.n → J (Fin.ofNat _ j2) = I (Fin.ofNat _ j2) := by {
    intro h6
    rw [h1,hj]
    unfold delete_vertex insert_index
    congr!
    have h7 : (Fin.ofNat (n1+1) j2).1 < (Fin.last SC.n).1 := by {
      simp only [Fin.ofNat_eq_cast, Fin.val_last]
      rw [Fin.val_cast_of_lt]
      exact h6
      rwa [←hn1] at h6
    }
    simp only [h7,↓reduceIte]
    simp only [Fin.ofNat_eq_cast]
    rw [Fin.val_cast_of_lt, Fin.val_cast_of_lt]
    rwa [←hn1] at h6
    exact Nat.lt_add_right 1 h6
  }
  apply And.intro ( parent_injective SC I hs J j h1 h4)
  intro j1 hj1 k1
  apply And.intro
  {
    rw [h5 _ hj1]
    by_cases h12 : j1 + 1 < SC.n
    {
      rw [h5 _ h12]
      apply monotone_1_of_simplex SC I hs
      simp only [Fin.ofNat_eq_cast]
      apply Fin.natCast_mono
      apply Nat.le_of_lt_add_one
      rwa [hn1]
      exact Nat.le_add_right j1 1
    }
    have h16 : j1+1 = SC.n := by omega
    have h13 : Fin.ofNat _ j1 = Fin.last n1 := by {
      suffices h15 : j1 = n1 by {
        simp only [h15, Fin.ofNat_eq_cast, Fin.natCast_eq_last]
      }
      omega
    }
    have h14 : Fin.ofNat _ (j1+1) = j := by {
      rw [hj]
      simp only [h16, Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    }
    rw [h13,h14]
    exact (h3 k1).1
  }
  {
    have h7 : J 0 = I 0 := by {
      have h6 := h5 0 (Nat.zero_lt_of_lt hj1)
      simp only [Fin.ofNat_eq_cast] at h6
      exact h6
    }
    rw [h7,←hj]
    exact (h3 k1).2
  }
}

lemma parent_simplex_case_D I (hs : simplex SC n1 I) J j i
    (hij : i.1 + 1 = j.1 ) (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ∉ Set.range I)
    (h3 : ∀ k, I i k ≤ J j k ∧ J j k ≤ I (i+1) k) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use j
    exact h4
  }
  have h5 j3 : j3 ≠ j → ∃ i3, j3 = @insert_index SC n1 hn1 j i3 := by {
    apply almost_surjective_of_insert_index
  }
  have h6 j3 : j3 ≠ j → ∃ i3, I i3 = J j3 := by {
    intro h7
    obtain ⟨i3, hi3⟩ := h5 j3 h7
    use i3
    rw [h1, hi3]
    rfl
  }
  apply And.intro (parent_injective SC I hs J j h1 h2)
  intro i2 h4 k2
  have h5 := h3 k2
  apply And.intro
  {
    simp only [Fin.ofNat_eq_cast, Fin.val_fin_le]
    rw [h1] at h5
    unfold delete_vertex at h5
    have h6 : (@insert_index SC n1 hn1 j i).1 + 1 = j := by {
      unfold insert_index
      have h7 : i.1 < j.1 := by omega
      simp only [h7, ↓reduceIte]
      exact hij
    }
    by_cases h8 : i2 = j.1
    {
      convert h5.2
      simp only [h8, Fin.cast_val_eq_self]
      have h11 : j ≠ Fin.last SC.n := by {
        suffices h12 : j.1 ≠ SC.n by exact Ne.symm (Fin.ne_of_val_ne (Ne.symm h12))
        rw [←h8]
        exact Nat.ne_of_lt h4
      }
      have h9 := @surround_index SC n1 hn1 j i hij h11
      rw [h8, h9.2]
      exact Fin.cast_val_eq_self (insert_index SC j (i + 1))
    }
    by_cases h9 : i2 + 1 = j.1
    {
      rw [←h9] at h6
      simp only [Nat.add_right_cancel_iff] at h6
      convert h5.1
      rw [←h6]
      simp only [Fin.cast_val_eq_self]
      rw [h9]
      simp only [Fin.cast_val_eq_self]
    }
    have h11 : ∃ i3, (Fin.ofNat _ i2) = @insert_index SC n1 hn1 j i3 := by {
      apply almost_surjective_of_insert_index
      intro h12
      apply h8
      rw [← h12]
      simp only [Fin.ofNat_eq_cast]
      rw [Fin.val_cast_of_lt]
      apply lt_trans h4 (lt_add_one SC.n)
    }
    have h12 : ∃ i3, (Fin.ofNat _ (i2+1)) = @insert_index SC n1 hn1 j i3 := by {
      apply almost_surjective_of_insert_index
      intro h12
      apply h9
      rw [← h12]
      simp only [Fin.ofNat_eq_cast]
      rw [Fin.val_cast_of_lt]
      omega
    }
    simp only [Fin.ofNat_eq_cast] at h11 h12
    obtain ⟨i3, hi3⟩ := h11
    obtain ⟨i4, hi4⟩ := h12
    rw [hi3, hi4]
    suffices h21 : I i3 k2 ≤ I i4 k2 by {rwa [h1] at h21}
    apply monotone_1_of_simplex SC I hs
    have h21 : StrictMono (@insert_index SC n1 hn1 j) := by {
      apply insert_index_strict_mono
    }
    rw [←h21.le_iff_le]
    rw [←hi3, ← hi4]
    refine (Fin.natCast_le_natCast ?_ h4).mpr ?_
    exact Nat.le_of_succ_le h4
    exact Nat.le_succ i2
  }
  {
    have h11 : (J (Fin.last SC.n) k2).1 ≤ (I (Fin.last n1) k2).1 := by {
      simp only [Fin.val_fin_le]
      by_cases h12 : Fin.last SC.n = j
      {
        rw [h12]
        apply le_trans h5.2
        apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last _)
      }
      obtain ⟨ i3, hi3⟩ := h6 _ h12
      rw [←hi3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last _)
    }
    have h13 := last_of_simplex SC I hs k2
    apply le_trans h11 (le_trans h13 _)
    simp only [add_le_add_iff_right, Fin.val_fin_le]
    by_cases h14 : 0 = j
    {
      rw [h14]
      apply le_trans _ h5.1
      apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le _)
    }
    {
      obtain ⟨i3, hi3⟩ := h6 _ h14
      rw [← hi3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le _)
    }
  }
}


noncomputable def coord_change_count (v1 v2 : SC.G) := Finset.card {i | v1 i ≠ v2 i}

lemma ccc_add {m} I (hs : simplex SC m I) (i1 i2 i3) (h1 : i1 ≤ i2 ∧ i2 ≤ i3) :
    coord_change_count SC (I i1) (I i3) =
    coord_change_count SC (I i1) (I i2) + coord_change_count SC (I i2) (I i3) := by {
  unfold coord_change_count
  rw [←Finset.card_union_of_disjoint]
  congr
  apply Finset.ext_iff.mpr
  intro k2
  simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  rw [←Decidable.not_and_iff_not_or_not]
  apply Iff.intro
  {
    intro h3 h4
    apply h3
    rw [h4.1, h4.2]
  }
  {
    intro h2 h3
    apply h2
    have h4 := monotone_1_of_simplex SC I hs i1 i2 h1.1 k2
    have h5 := monotone_1_of_simplex SC I hs i2 i3 h1.2 k2
    rw [h3] at h4 ⊢
    suffices h1 : I i3 k2 = I i2 k2 by exact ⟨h1, Eq.symm h1⟩
    exact Fin.le_antisymm h4 h5
  }
  {
    apply Finset.disjoint_filter.mpr
    intro k1 hk1 h2 h3
    apply h3
    have h4 : ∀ k, I i1 k ≤ I i2 k :=  monotone_1_of_simplex SC I hs i1 i2 h1.1
    have h5 : I i1 k1 < I i2 k1 := lt_of_le_of_ne (h4 k1) h2
    have h6 : (I i3 k1).1 ≤ (I i1 k1).1 + 1 := by {
      apply le_add_one_of_simplex _ _ hs
    }
    apply le_antisymm ( monotone_1_of_simplex SC I hs i2 i3 h1.2 k1)
    apply le_trans h6 h5
  }
}

lemma ccc_pos {m} I (hs : simplex SC m I) i1 i2 (h1 : i1 ≠ i2)
    : 0 < coord_change_count SC (I i1) (I i2) := by {
  unfold coord_change_count
  by_contra! h2
  apply h1
  apply hs.1
  simp only [ne_eq, nonpos_iff_eq_zero, Finset.card_eq_zero] at h2
  apply funext
  intro k
  rw [Finset.filter_eq_empty_iff] at h2
  simp only [Finset.mem_univ, Decidable.not_not, forall_const] at h2
  apply h2
}

noncomputable def ccc_fun {m} (I : Fin (m+1)→ SC.G) (i : Fin (m+1)) : Fin (SC.n + 1 )
    := ⟨ coord_change_count SC (I 0) (I i), by {
      refine Nat.lt_succ_of_le ?_
      exact card_finset_fin_le {i_1 | I 0 i_1 ≠ I i i_1}
    } ⟩

lemma ccc_fun_strict_mono {m} I (hs : simplex SC m I) :
    StrictMono (ccc_fun SC I) := by {
  intro i1 i2 h1
  unfold ccc_fun
  simp only [Fin.mk_lt_mk]
  have h3 : 0 ≤ i1 ∧ i1 ≤ i2 := ⟨ (Fin.zero_le i1), (Fin.le_of_lt h1) ⟩
  rw [ccc_add SC I hs 0 i1 i2 h3]
  simp only [lt_add_iff_pos_right, gt_iff_lt]
  apply ccc_pos SC I hs _ _ $ Fin.ne_of_lt h1
}

lemma ccc_fun_is_insert_index I (hs : simplex SC n1 I) :
    ∃ j, ccc_fun SC I = @insert_index SC n1 hn1 j := by {
  apply is_insert_index_of_strict_mono
  apply ccc_fun_strict_mono SC I hs
}



lemma ccc_fun_case_D_iff {m} I (hs : simplex SC m I) :
    case_D SC I ↔ ccc_fun SC I (Fin.last m) = Fin.last SC.n := by {
  have h1 : (ccc_fun SC I (Fin.last m) = Fin.last SC.n) ↔ ∀ k, I 0 k ≠ I (Fin.last m) k  := by {
    unfold ccc_fun coord_change_count
    rw [Fin.ext_iff]
    have h3 : SC.n = Fintype.card (Fin SC.n) := by {exact Eq.symm (Fintype.card_fin SC.n)}
    simp only [ne_eq, Fin.val_last]
    nth_rewrite 7 [h3]
    rw [Finset.card_eq_iff_eq_univ, Finset.eq_univ_iff_forall]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  }
  apply Iff.trans _ h1.symm
  unfold case_D
  apply Iff.intro
  {
    intro h2 k1
    obtain ⟨i2, hi2⟩ := h2 k1 (I 0 k1)
    intro h3
    apply hi2
    apply le_antisymm
    {
      rw [h3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i2)
    }
    exact monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i2) k1
  }
  {
    contrapose!
    intro h2
    obtain ⟨k2, ⟨q, hq⟩ ⟩ := h2
    use k2
    rw [hq, hq]
  }
}

lemma last_eq_first_add_one J (hs : simplex SC SC.n J)
    : ∀ k, (J (Fin.last SC.n) k).1 = (J 0 k).1 + 1 := by {
  have h3 : ∀ j3, ccc_fun SC J j3 = j3 := by {
    apply is_id_of_strict_mono
    apply ccc_fun_strict_mono SC J hs
  }
  have h2 := (ccc_fun_case_D_iff SC J hs).mpr (h3 _)
  unfold case_D at h2
  intro k
  apply le_antisymm  (last_of_simplex SC J hs k)
  apply Nat.add_one_le_of_lt
  obtain ⟨j1, hj1⟩ := h2 k (J 0 k)
  have h4 := monotone_1_of_simplex SC J hs _ _ (Fin.le_last j1) k
  apply lt_of_lt_of_le _ h4
  apply lt_of_le_of_ne (monotone_1_of_simplex SC J hs _ _ (Fin.zero_le j1) k) hj1.symm
}

lemma delete_vertex_ccc_fun_match J (hs : simplex SC SC.n J) j1 j2
    ( h1 : ccc_fun SC (@delete_vertex SC n1 hn1 j1 J) = @insert_index SC n1 hn1 j2)
    : (j1 = 0 → j2 = Fin.last SC.n) ∧ (j1 ≠ 0 → j1 = j2) := by {
  let I := @delete_vertex SC n1 hn1 j1 J
  have hsI : simplex SC n1 I := by {
    suffices h2 : is_face SC I J by { exact h2.1}
    rw [@child_simplex_char SC n1 hn1 I J hs]
    use j1
  }
  have scnpos : 0 < SC.n := by omega
  by_cases h4 : j1 = 0
  {
    simp only [h4, forall_const, ne_eq, not_true_eq_false, IsEmpty.forall_iff, and_true]
    have h5 : I 0 = J 1 := by {
      unfold I delete_vertex insert_index
      congr!
      rw [h4]
      simp only [Fin.val_zero, lt_self_iff_false, ↓reduceIte, zero_add]
      simp only [Fin.val_one']
      refine Eq.symm (Nat.mod_eq_of_lt ?_)
      exact Nat.lt_add_of_pos_left scnpos
    }
    symm
    by_contra h6
    obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 _ _ h6
    have h8 : (ccc_fun SC I i1).1 = SC.n := by {
      unfold I
      rw [h1, ← hi1]
      simp only [Fin.val_last]
    }
    unfold ccc_fun at h8
    simp only [h5] at h8
    unfold I delete_vertex at h8
    let c2 := coord_change_count SC (J 0) (J 1)
    have c2pos : 0 < c2 := by {
      apply ccc_pos _ _ hs
      simp only [ne_eq, Fin.zero_eq_one_iff, Nat.add_eq_right]
      omega
    }
    let j3 := @insert_index SC n1 hn1 j1 i1
    have h9 : (ccc_fun SC J j3).1 = c2 + SC.n:= by {
      simp only [← h8]
      apply ccc_add SC J hs
      simp only [Fin.zero_le, true_and]
      suffices h9 : j3 ≠ j1 by {
        rw [h4] at h9
        exact Fin.one_le_of_ne_zero h9
      }
      apply insert_index_ne
    }
    have h10 : c2 + SC.n ≤ SC.n := by {
      rw [←h9]
      exact Fin.is_le (ccc_fun SC J j3)
    }
    simp only [add_le_iff_nonpos_left, nonpos_iff_eq_zero] at h10
    omega
  }
  simp only [h4, IsEmpty.forall_iff, ne_eq, not_false_eq_true, forall_const, true_and]
  have h2 : I 0 = J 0 := by {
    unfold I delete_vertex
    congr!
    unfold insert_index
    simpa only [Fin.val_zero, Fin.val_pos_iff, zero_add, Fin.mk_eq_zero,
        ite_eq_left_iff, not_lt,Fin.le_zero_iff, one_ne_zero, imp_false]
  }
  have h3 : ∀ j3, ccc_fun SC J j3 = j3 := by {
    apply is_id_of_strict_mono
    apply ccc_fun_strict_mono SC J hs
  }
  symm
  by_contra h5
  obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 _ _ h5
  have h6 : ccc_fun SC I i1 = ccc_fun SC J j2 := by {
    unfold ccc_fun
    simp [h2]
    congr
    rw [hi1]
    rfl
  }
  rw [h1, h3 j2] at h6
  contrapose h6
  apply insert_index_ne
}

lemma case_D_iff_not_end_1 I (hs : simplex SC n1 I) j
    (h1 : ccc_fun SC I = @insert_index SC n1 hn1 j) :
    case_D SC I ↔ j ≠ 0 ∧ j ≠ Fin.last SC.n := by {
  rw [ccc_fun_case_D_iff SC I hs, h1]
  have h2 : j ≠ 0 := by {
    intro h3
    apply @insert_index_ne SC n1 hn1 j 0
    rw [←h1, h3]
    unfold ccc_fun coord_change_count
    simp only [ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty, Fin.zero_eta]
  }
  simp only [ne_eq, h2, not_false_eq_true, true_and]
  apply Iff.intro
  {
    intro h3 h4
    apply @insert_index_ne SC n1 hn1 j (Fin.last n1)
    rw [h3,h4]
  }
  {
    intro h3
    have h32 : Fin.last SC.n ≠ j := fun a ↦ h3 (Eq.symm a)
    obtain ⟨i2, hi2⟩  := @almost_surjective_of_insert_index SC n1 hn1 j (Fin.last SC.n) h32
    apply le_antisymm
    exact Fin.le_last (insert_index SC j (Fin.last n1))
    rw [hi2]
    have h4 := @insert_index_strict_mono SC n1 hn1 j
    rw [h4.le_iff_le]
    exact Fin.le_last i2
  }
}

lemma case_D_iff_not_end_2 J (hs : simplex SC SC.n J) j :
    case_D SC (@delete_vertex SC n1 hn1 j J) ↔ j ≠ 0 ∧ j ≠ Fin.last SC.n := by {
  let I := @delete_vertex SC n1 hn1 j J
  have hsI : simplex SC n1 I := by {
    suffices h2 : is_face SC I J by exact h2.1
    rw [@child_simplex_char SC n1 hn1 I J hs]
    use j
  }
  obtain ⟨j2, hj2⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hsI
  have h1 := @delete_vertex_ccc_fun_match SC n1 hn1 J hs j j2 hj2
  by_cases h2 : j = 0
  {
    rw [ccc_fun_case_D_iff SC I hsI]
    simp only [h2, ne_eq, not_true_eq_false, Fin.zero_eq_last_iff, false_and, iff_false]
    rw [←h1.1 h2, hj2]
    apply insert_index_ne
  }
  rw [@case_D_iff_not_end_1 SC n1 hn1 I hsI]
  rw [hj2, ← h1.2 h2]
}

lemma same_delete_index_eq_iff J1 J2 j
    (h1 : @delete_vertex SC n1 hn1 j J1 = @delete_vertex SC n1 hn1 j J2)
    : J1 = J2 ↔ J1 j = J2 j := by {
  apply Iff.intro (fun a ↦ congrFun a j)
  intro h2
  ext j2
  by_cases h3 : j2 = j
  rw [h3,h2]
  obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 j j2 h3
  rw [hi1]
  exact congrFun h1 i1
}


lemma case_D_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h1 : case_D SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 2 := by {
  obtain ⟨ j1, hj1 ⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hs
  have h2 : j1 ≠ 0 ∧ j1 ≠ Fin.last SC.n := by {
    rw [←case_D_iff_not_end_1 SC I hs j1 hj1]
    exact h1
  }
  have h3 : ∃ (i1: Fin (n1 + 1)), i1.1 + 1 = j1.1 := by {
    obtain ⟨a, ha⟩ := Fin.exists_succ_eq_of_ne_zero h2.1
    rw [← ha]
    simp only [Fin.val_succ, Nat.add_right_cancel_iff]
    use ⟨ a.1, by {rw [hn1]; exact a.2}⟩
  }
  obtain ⟨ i1, hi1⟩ := h3
  have h32 : i1 ≤ i1 + 1 := by {
    refine Fin.le_of_lt ?_
    refine Fin.lt_add_one_iff.mpr ?_
    show i1.1 < n1
    have h3 := Fin.val_lt_last h2.2
    omega
  }
  have h11 := @surround_index SC n1 hn1 j1 i1 hi1 h2.2
  have h12 : @insert_index SC n1 hn1 j1 i1 ≤ j1 ∧ j1 ≤ @insert_index SC n1 hn1 j1 (i1+1) := by {
    rw [Fin.le_def, Fin.le_def, ←h11.2]
    apply And.intro
    rw [←h11.1]
    apply Nat.le_add_right
    apply Nat.le_add_right
  }
  have h3 : coord_change_count SC (I i1) (I (i1+1)) = 2 := by {
    have h3 : (@insert_index SC n1 hn1 j1 i1).1 + 2
        = (@insert_index SC n1 hn1 j1 (i1 +1)).1 := by {
      rw [← h11.2, ←h11.1]
    }
    have h4 : (ccc_fun SC I (i1+1)).1 = (ccc_fun SC I i1).1
        + coord_change_count SC (I i1) (I (i1 + 1)) := by {
      apply ccc_add SC I hs
      simp only [Fin.zero_le, true_and, h32]
    }
    rw [← hj1, h4 ] at h3
    simp only [Nat.add_left_cancel_iff] at h3
    exact h3.symm
  }
  have h4 : ∃ k1, ∃ k2, k1 ≠ k2 ∧ {k | I i1 k ≠ I (i1 +1) k} = {k1, k2} := by {
    unfold coord_change_count at h3
    rw [Finset.card_eq_two] at h3
    convert h3
    simp only [ne_eq]
    rw [←Finset.coe_eq_pair]
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
  }
  obtain ⟨k1, ⟨k2, h4⟩ ⟩ := h4
  have hk1 : I i1 k1 ≠ I (i1+1) k1 := by {
    have h5 := Set.mem_insert k1 {k2}
    rwa [←h4.2] at h5
  }
  have hk2 : I i1 k2 ≠ I (i1+1) k2 := by {
    have h5 : k2 ∈ ({k1, k2} : Set _) := Set.mem_insert_of_mem k1 rfl
    rwa [←h4.2] at h5
  }
  have h5 k3 : I i1 k3 ≠ I (i1+1) k3 → ∃ J3,
      I = @delete_vertex SC n1 hn1 j1 J3 ∧ is_face SC I J3 ∧ J3 j1 k3 ≠ I i1 k3 := by {
    intro h21
    let ins : SC.G := fun k ↦ if k = k3 then I (i1 + 1) k else I i1 k
    obtain ⟨J3, hJ3⟩ := @insert_vertex SC n1 hn1 I ins j1
    have h6 : ∀ k, I i1 k ≤ ins k ∧ ins k ≤ I (i1+1) k := by {
      intro k
      unfold ins
      have h13 : I i1 k3 ≤ I (i1+1) k3 := monotone_1_of_simplex SC I hs _ _ h32 k3
      by_cases h12 : k = k3
      simp only [h12, ↓reduceIte, le_refl, and_true, ge_iff_le]
      exact monotone_1_of_simplex SC I hs _ _ h32 k3
      simp only [h12, ↓reduceIte, le_refl, true_and, ge_iff_le]
      exact monotone_1_of_simplex SC I hs _ _ h32 k
    }
    have h22 : J3 j1 k3 ≠ I i1 k3 := by {
      rw [hJ3.2]
      unfold ins
      simp only [↓reduceIte, ne_eq]
      exact h21.symm
    }
    have h23 : ∃ k4, k3 ≠ k4 ∧ I i1 k4 ≠ I (i1+1) k4 := by {
      by_cases h24 : k3 = k1
      use k2
      rw [h24]
      apply And.intro h4.1 hk2
      use k1
    }
    have h7 : ins ∉ Set.range I := by {
      intro h9
      obtain ⟨i2,hi2⟩ := h9
      rw [forall_and, ← hi2] at h6
      rw [← monotone_2_of_simplex _ _ hs,← monotone_2_of_simplex _ _ hs] at h6
      have h13 : i2 = i1 ∨ i2 = i1 + 1 := by {
        refine (WCovBy.le_and_le_iff ?_).mp h6
        apply And.intro h32
        intro i3 h33
        simp only [not_lt]
        exact Fin.add_one_le_of_lt h33
      }
      cases' h13 with h13 h13
      apply h22
      rw [hJ3.2, ←hi2, h13]
      obtain ⟨k4, hk4⟩ := h23
      apply hk4.2
      rw [←h13, hi2]
      unfold ins
      simp only [right_eq_ite_iff]
      intro h33
      exact False.elim $ hk4.1 h33.symm
    }
    use J3
    apply And.intro hJ3.1 (And.intro _ h22)
    apply @parent_simplex_case_D SC n1 hn1 I hs J3 _ _ hi1 hJ3.1
    rwa [hJ3.2]
    rwa [hJ3.2]
  }
  obtain ⟨J1, hJ1⟩ := h5 k1 hk1
  obtain ⟨J2, hJ2⟩ := h5 k2 hk2
  have h6 J3 : I = @delete_vertex SC n1 hn1 j1 J3 → is_face SC I J3
    → ∀ k, I i1 k ≤ J3 j1 k ∧ J3 j1 k ≤ I (i1+1) k := by {
    intro h14 h13 k3
    rw [h14]
    apply And.intro
    apply monotone_1_of_simplex SC J3 h13.2.1 _ _ h12.1
    apply monotone_1_of_simplex SC J3 h13.2.1 _ _ h12.2
  }
  have h7 J3 k3 : I = @delete_vertex SC n1 hn1 j1 J3 ∧ is_face SC I J3 ∧ J3 j1 k3 ≠ I i1 k3
      → J3 j1 k3 = I (i1+1) k3 ∧ ∀ k4, k3 ≠ k4 → J3 j1 k4 = I i1 k4 := by {
    intro h9
    have h6 := h6 J3 h9.1 h9.2.1
    have h31 := h3
    rw [h9.1] at h31
    have h21 := ccc_add SC J3 h9.2.1.2.1 _ _ _ h12
    unfold delete_vertex at h31
    rw [h31] at h21
    have h22 c1 c2 : 2 = c1 + c2 → 0 < c2 → c1 ≤ 1 := by omega
    have h23 : coord_change_count SC (I i1) (J3 j1) ≤ 1 := by {
      rw [h9.1]
      apply h22 _ _ h21
      apply ccc_pos SC
      exact h9.2.1.2.1
      symm
      apply insert_index_ne
    }
    apply And.intro
    {
      apply le_antisymm (h6 k3).2
      rw [Fin.le_def]
      have h24 := le_add_one_of_simplex SC I hs (i1+1) i1 k3
      apply le_trans h24
      apply Fin.val_add_one_le_of_lt (lt_of_le_of_ne (h6 k3).1 h9.2.2.symm)
    }
    intro k4 hk4
    contrapose! h23
    refine Finset.one_lt_card_iff.mpr ?_
    use k3, k4
    simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    exact And.intro h9.2.2.symm ( And.intro h23.symm hk4)
  }
  refine Finset.card_eq_two.mpr ?_
  use J1, J2
  apply And.intro
  {
    have h71 := (h7 J1 k1 hJ1).2 k2 h4.1
    intro h9
    apply hJ2.2.2
    rw [←h9, h71]
  }
  apply subset_antisymm
  {
    intro J3
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    intro hJ3
    have h14 := (@child_simplex_char SC n1 hn1 I J3 hJ3.2.1).mp hJ3
    obtain ⟨j2, hj2⟩ := h14
    rw [hj2] at hj1
    have h13 := @delete_vertex_ccc_fun_match SC n1 hn1 J3 hJ3.2.1 j2 j1 hj1
    have h15 := @case_D_iff_not_end_2 SC n1 hn1 J3 hJ3.2.1 j2
    rw [←hj2] at h15
    have h16 : j2 = j1 := h13.2 (h15.mp h1).1
    rw [h16] at hj2
    rw [same_delete_index_eq_iff SC J3 J1 j1, same_delete_index_eq_iff SC J3 J2 j1]
    have h71 := h7 J1 k1 hJ1
    have h72 := h7 J2 k2 hJ2
    have h18 : ∃ k5, J3 j1 k5 ≠ I i1 k5 := by {
      suffices h19 : J3 j1 ≠ I i1 by exact Function.ne_iff.mp h19
      intro h19
      apply @insert_index_ne SC n1 hn1 j1 i1
      apply hJ3.2.1.1
      rw [h19, hj2]
      rfl
    }
    obtain ⟨k5, hk5⟩ := h18
    have h73 := h7 J3 k5 ⟨hj2, ⟨ hJ3, hk5⟩ ⟩
    clear h15 h13
    have h19 : k5 = k1 ∨ k5 = k2 := by {
      have h21 : I i1 k5 ≠ I (i1+1) k5 := by {
        rw [←h73.1]
        exact hk5.symm
      }
      exact h4.2.subset h21
    }
    have h20 (J4 : _ → SC.G) : (J4 j1 k5 = I (i1+1) k5 ∧ ∀ k4, k5 ≠ k4 → J4 j1 k4 = I i1 k4)
        → J3 j1 = J4 j1:= by {
      intro h21
      apply funext
      intro k6
      by_cases h22 : k5 = k6
      rw [←h22,h21.1,h73.1]
      rw [h21.2 k6 h22, h73.2 k6 h22]
    }
    cases h19
    left
    rename_i h21
    apply h20
    rwa [h21]
    right
    rename_i h21
    apply h20
    rwa [h21]
    rw [←hJ2.1, ←hj2]
    any_goals exact hn1
    rw [←hJ1.1, ←hj2]
  }
  {
    refine Finset.insert_subset ?_ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hJ1.2.1
    simp only [Finset.singleton_subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hJ2.2.1
  }
}


lemma unique_const_ABC {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) k1 q1
    (h1 : ∀ i, I i k1 = q1): ∀ k2, k1 ≠ k2 → I 0 k2 ≠ I (Fin.last n1) k2 := by {
  intro k2 h3 h2
  let s : Finset (Fin SC.n) := {i | I 0 i ≠ I (Fin.last n1) i}
  have h4 : n1 ≤ s.card := by {
    obtain ⟨j, hj⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hs
    show n1 ≤ (ccc_fun SC I (Fin.last n1)).1
    rw [hj]
    unfold insert_index
    simp only [Fin.val_last]
    by_cases h11 : n1 < j.1
    simp only [h11, ↓reduceIte, le_refl]
    simp only [h11, ↓reduceIte, le_add_iff_nonneg_right, zero_le]
  }
  have h6 : 2 ≤ sᶜ.card := by {
    show 1 < sᶜ.card
    rw [Finset.one_lt_card]
    use k2
    unfold s
    simp only [ne_eq, Finset.compl_filter, Decidable.not_not, Finset.mem_filter,
        Finset.mem_univ,h2, and_self, true_and]
    use k1
    apply And.intro _ h3.symm
    rw [h1,h1]
  }
  have h7 := add_le_add h4 h6
  simp only [Finset.card_add_card_compl, Fintype.card_fin] at h7
  rw [←hn1,add_le_add_iff_left] at h7
  simp only [Nat.not_ofNat_le_one] at h7
}


lemma case_AC_ex_unique I (hs : simplex SC n1 I) k1 q
    (hABC : ∀ i, I i k1 = q) (hAC : q ≠ Fin.last SC.p)
    : ∃! J, I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J := by {
  have h1 k2 : I 0 k2 ≠ Fin.last SC.p := by {
    intro h11
    have h12 : k1 ≠ k2 := by {
      intro h13
      apply hAC
      rw [←hABC 0,h13,h11]
    }
    apply @unique_const_ABC SC n1 hn1 I hs k1 q hABC k2 h12
    apply le_antisymm
    apply monotone_1_of_simplex SC I hs
    exact Fin.zero_le (Fin.last n1)
    rw [h11]
    exact Fin.le_last (I (Fin.last n1) k2)
  }
  let ins2 : SC.G := fun k ↦ (I 0 k) + 1
  have h2 k : (ins2 k).1 = (I 0 k).1 + 1 := by {
    apply Fin.val_add_one_of_lt
    rw [Fin.lt_last_iff_ne_last]
    exact h1 k
  }
  obtain ⟨J1, hJ1⟩ := @insert_vertex SC n1 hn1 I ins2 (Fin.last SC.n)
  have h3 : J1 (Fin.last SC.n) ≠ I (Fin.last n1) := by {
    intro h12
    have h11 : I 0 k1 = I 0 k1 + 1 := by {
      show I 0 k1 = ins2 k1
      rw [←hJ1.2, h12,hABC,hABC]
    }
    simp only [left_eq_add, Fin.one_eq_zero_iff, Nat.add_eq_right] at h11
    apply @p_ne_zero_of_cube SC n1 hn1
    simp only [Fin.last_eq_zero_iff, h11]
  }
  have h4 : is_face SC I J1 := by {
    apply parent_simplex_case_AC SC I hs J1 (Fin.last SC.n) rfl hJ1.1 h3
    intro k2
    rw [hJ1.2]
    apply And.intro
    {
      rw [Fin.le_def, h2 k2]
      apply le_add_one_of_simplex SC I hs
    }
    rw [h2 k2]
  }
  use J1
  simp only
  apply And.intro (And.intro hJ1.1 h4)
  intro J2 hJ2
  rw [@same_delete_index_eq_iff SC n1 hn1 _ _ _ (hJ2.1.symm.trans hJ1.1)]
  rw [hJ1.2]
  apply funext
  intro k1
  ext
  have h5 := last_eq_first_add_one SC J2 hJ2.2.2.1 k1
  rw [h5, h2 k1]
  suffices h6 : I 0 = J2 0 by {rw [h6]}
  rw [hJ2.1]
  unfold delete_vertex insert_index
  congr!
  simp only [Fin.val_zero, Fin.val_last, zero_add, ite_eq_left_iff,
    not_lt, nonpos_iff_eq_zero,one_ne_zero, imp_false]
  rw [←hn1]
  omega
}

lemma case_B_not_last I (h1 : case_B SC I) J
    (h2 : I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J) : False := by {
  have h3 := last_eq_first_add_one SC J h2.2.2.1
  obtain ⟨k1, hk1⟩ := h1
  have h4 : I 0 = J 0 := by {
    rw [h2.1]
    unfold delete_vertex insert_index
    congr!
    simp only [Fin.val_zero, Fin.val_last, zero_add, ite_eq_left_iff,
        not_lt, nonpos_iff_eq_zero,one_ne_zero, imp_false]
    rw [←hn1]
    omega
  }
  have h5 := (J (Fin.last SC.n) k1).is_le
  rw [h3 k1,←h4,hk1 0] at h5
  contrapose! h5
  exact lt_add_one SC.p
}


lemma case_BC_ex_unique I (hs : simplex SC n1 I) k1 q
    (hABC : ∀ i, I i k1 = q) (hBC : q ≠ 0)
    : ∃! J, I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J := by {
  have h1 k2 : I (Fin.last n1) k2 ≠ 0 := by {
    intro h11
    have h12 : k1 ≠ k2 := by {
      intro h13
      apply hBC
      rw [←hABC (Fin.last n1),h13,h11]
    }
    apply @unique_const_ABC SC n1 hn1 I hs k1 q hABC k2 h12
    apply le_antisymm
    apply monotone_1_of_simplex SC I hs
    exact Fin.zero_le (Fin.last n1)
    rw [h11]
    exact Fin.zero_le (I 0 k2)
  }
  let ins2 : SC.G := fun k ↦ (I (Fin.last n1) k) - 1
  have h22 k := Fin.val_sub_one_of_ne_zero (h1 k)
  have h21 k : (ins2 k).1 + 1 = (I (Fin.last n1) k).1  := by {
    rw [h22]
    apply Nat.sub_one_add_one ( Fin.val_ne_zero_iff.mpr (h1 k))
  }
  obtain ⟨J1, hJ1⟩ := @insert_vertex SC n1 hn1 I ins2 0
  have h3 : J1 0 ≠ I 0 := by {
    intro h12
    have h11 : (ins2 k1).1 + 1 = ins2 k1 := by {
      rw [h21 k1, hABC, ←hJ1.2,h12,hABC]
    }
    simp only [Nat.add_eq_left, one_ne_zero] at h11
  }
  have h4 : is_face SC I J1 := by {
    apply parent_simplex_case_BC SC I hs J1 hJ1.1 h3
    intro k2
    rw [hJ1.2]
    apply And.intro
    rw [Fin.le_def, ←add_le_add_iff_right 1, h21 k2]
    exact le_add_one_of_simplex SC I hs (Fin.last n1) 0 k2
    rw [h21 k2]
  }
  use J1
  simp only
  apply And.intro (And.intro hJ1.1 h4)
  intro J2 hJ2
  rw [@same_delete_index_eq_iff SC n1 hn1 _ _ _ (hJ2.1.symm.trans hJ1.1), hJ1.2]
  apply funext
  intro k1
  ext
  have h5 := last_eq_first_add_one SC J2 hJ2.2.2.1 k1
  have h6 : I (Fin.last n1) = J2 (Fin.last SC.n) := by {
    rw [hJ2.1]
    unfold delete_vertex insert_index
    simp only [Fin.val_last, Fin.val_zero, not_lt_zero, ↓reduceIte]
    congr!
  }
  rw [←h6, ←h21 k1] at h5
  omega
}

lemma zero_ne_last {hn1 : n1 + 1 = SC.n} : 0 ≠ Fin.last SC.n := by {
  simp only [ne_eq, Fin.zero_eq_last_iff]
  rw [←hn1]
  omega
}

lemma case_A_not_zero I (h1 : case_A SC I) J
    (h2 : I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J) : False := by {
  have h3 := last_eq_first_add_one SC J h2.2.2.1
  obtain ⟨k1, hk1⟩ := h1
  have h4 : I (Fin.last n1) = J (Fin.last SC.n) := by {
    rw [h2.1]
    unfold delete_vertex insert_index
    simp only [Fin.val_last, Fin.val_zero, not_lt_zero, ↓reduceIte]
    congr!
  }
  apply Nat.zero_ne_add_one (J 0 k1).1
  rw [←h3 k1,← h4,hk1]
  rfl
}



lemma case_ABC_count_disj {hn1 : n1 + 1 = SC.n} I k1 q
    (hABC : ∀ i, I i k1 = q) : Finset.card { J | is_face SC I J}
    = Finset.card {J | I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J}
    + Finset.card {J | I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J} := by {
  have hnd : ¬ case_D SC I := by {
    contrapose! hABC
    exact hABC k1 q
  }
  rw [←Finset.card_union_of_disjoint]
  congr
  ext J
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  apply Iff.intro
  {
    intro h1
    simp only [h1, and_true]
    rw [child_simplex_char] at h1
    obtain ⟨j1, hj1⟩ := h1
    have h2 := @case_D_iff_not_end_2 SC n1 hn1 J h1.2.1 j1
    rw [hj1,h2] at hnd
    have h3 := Decidable.or_iff_not_not_and_not.mpr hnd
    cases' h3 with h3 h3
    rw [hj1,h3]
    exact Or.inl rfl
    rw [hj1,h3]
    exact Or.inr rfl
    · exact hn1
    · exact h1.2.1
  }
  {
    intro h1
    rw [←or_and_right] at h1
    exact h1.2
  }
  apply Finset.disjoint_filter.mpr
  intro J h1 h2 h3
  apply @zero_ne_last SC n1 hn1
  apply @delete_vertex_inj SC n1 hn1 J h2.2.2.1
  rw [←h2.1,←h3.1]
}


lemma case_C_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h1 : case_C SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 2 := by {
  obtain ⟨k1,q, h1⟩  := h1
  have h2 := @case_AC_ex_unique SC n1 hn1 I hs k1 q h1.2 h1.1.2
  have h3 := @case_BC_ex_unique SC n1 hn1 I hs k1 q h1.2 h1.1.1
  rw [Fintype.existsUnique_iff_card_one] at h2 h3
  rw [case_ABC_count_disj SC I k1 q h1.2,h2,h3]
  exact hn1
}

lemma case_B_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h2 : case_B SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 1 := by {
  obtain ⟨k1, h1⟩  := id h2
  have h4 : Fin.last SC.p ≠ 0 := @p_ne_zero_of_cube SC n1 hn1
  have h3 := @case_BC_ex_unique SC n1 hn1 I hs k1 _ h1 h4
  rw [Fintype.existsUnique_iff_card_one] at h3
  rw [case_ABC_count_disj SC I k1 (Fin.last SC.p) h1, h3]
  simp only [Nat.add_eq_left]
  apply Finset.card_filter_eq_zero_iff.mpr
  intro J h5
  apply case_B_not_last SC I h2
  exact hn1
}

lemma case_A_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h2 : case_A SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 1 := by {
  obtain ⟨k1, h1⟩  := id h2
  have h4 : Fin.last SC.p ≠ 0 := @p_ne_zero_of_cube SC n1 hn1
  have h3 := @case_AC_ex_unique SC n1 hn1 I hs k1 _ h1 h4.symm
  rw [Fintype.existsUnique_iff_card_one] at h3
  rw [case_ABC_count_disj SC I k1 0 h1, h3]
  simp only [Nat.add_eq_right]
  apply Finset.card_filter_eq_zero_iff.mpr
  intro J h5
  apply case_A_not_zero SC I h2
  exact hn1
}

end cases_ABCD

-- used in other file
lemma boundary_is_A_or_B {hn1 : n1 + 1 = SC.n} I (hbf : @is_boundary_face SC n1 I)
    : case_A SC I ∨ case_B SC I := by {
  have hs : simplex SC n1 I := by {
    obtain ⟨J,hJ⟩ := hbf
    exact hJ.1.1
  }
  unfold is_boundary_face at hbf
  rw [Fintype.existsUnique_iff_card_one] at hbf
  have h1 := one_of_ABCD SC I
  rw [←or_assoc] at h1
  cases' h1 with h1 h1
  assumption
  cases' h1 with h1 h1
  rw [@case_C_parent_count SC n1 hn1 I hs h1] at hbf
  simp only [OfNat.ofNat_ne_one] at hbf
  rw [@case_D_parent_count SC n1 hn1 I hs h1] at hbf
  simp only [OfNat.ofNat_ne_one] at hbf
}

-- used in other file
lemma case_B_boundary {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I)
    (h1 : case_B SC I) : is_boundary_face SC I :=
  (Fintype.existsUnique_iff_card_one _).mpr (@case_B_parent_count SC n1 hn1 I hs h1)


-- used in other file
lemma parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) :
    Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} ∈ {c | c = 1 ∨ c = 2} := by {
  simp only [Set.mem_ofPred_eq]
  have h1 := one_of_ABCD SC I
  rw [←or_assoc] at h1
  cases' h1 with h1 h1
  left
  cases' h1 with h2 h2
  exact @case_A_parent_count SC n1 hn1 I hs h2
  exact @case_B_parent_count SC n1 hn1 I hs h2
  right
  cases' h1 with h2 h2
  exact @case_C_parent_count SC n1 hn1 I hs h2
  exact @case_D_parent_count SC n1 hn1 I hs h2
}

end

section

open Classical



section completeness

lemma complete_simplex_iff {SC} m I(hs : simplex SC m I) :
    complete_simplex SC m I ↔ ∀ c, c ≤ m → ∃ i, SC.RL (I i) = c := by {
  apply Iff.intro
  {
    intro h1 c hc
    rwa [← Set.mem_range, h1.2, Set.mem_ofPred_eq]
  }
  {
    intro c1
    apply And.intro hs
    refine Set.toFinset_inj.mp ?_
    refine (Finset.eq_iff_card_ge_of_superset ?_).mp ?_
    {
      simp only [Set.toFinset_range, Set.toFinset_subset, Finset.coe_image, Finset.coe_univ,
        Set.image_univ]
      intro c hc
      simp only [Set.mem_range, c1 c hc]
    }
    let f1 := fun (j : ℕ ) ↦ SC.RL (I (Fin.ofNat _ j))
    apply Finset.card_le_card_of_surjOn f1
    intro j h1
    simp only [Set.toFinset_range, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_range] at h1
    obtain ⟨ i, hi⟩ := h1
    use i
    simp only [Set.coe_toFinset, Set.mem_ofPred_eq]
    apply And.intro (Fin.is_le i)
    unfold f1
    rw [← hi]
    simp only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self]
  }
}


lemma rl_inj_of_complete {SC} m I (hcs : complete_simplex SC m I):
    ∀ i1 i2, SC.RL (I i1) = SC.RL (I i2) → i1 = i2 := by {
  let f1 : Fin (m+1) → Fin (m+1) := fun j ↦ Fin.ofNat _ (SC.RL (I j))
  suffices h1 : Function.Injective f1 by {
    intro i1 i2 h2
    apply h1
    unfold f1
    rw [h2]
  }
  have h2 := hcs.2
  apply Function.Surjective.injective_of_finite
  rfl
  rw [complete_simplex_iff _ _ hcs.1] at hcs
  intro c
  obtain ⟨a, ha⟩ := hcs c (Fin.is_le c)
  use a
  unfold f1
  rw [ha]
  exact Fin.cast_val_eq_self c
}


lemma char_complete_face {SC n1 hn1} I J (hs : simplex SC SC.n J) :
    complete_simplex SC n1 I ∧ is_face SC I J
    ↔ ∃ i, I = @delete_vertex SC n1 hn1 i J
    ∧ ∀ (c:ℕ ), c ≤ n1 → ∃ i2, i2 ≠ i ∧ SC.RL (J i2) = c := by {
  apply Iff.intro
  {
    rw [child_simplex_char]
    intro h1
    obtain ⟨i, hi1 ⟩ := h1.2
    use i
    apply And.intro hi1
    intro c hc
    have h2 := (complete_simplex_iff n1 I h1.1.1).mp h1.1 c hc
    obtain ⟨j, hj⟩ := h2
    rw [← hj, hi1]
    unfold delete_vertex
    use @insert_index SC n1 hn1 i j
    apply And.intro _ rfl
    apply insert_index_ne
    exact hn1
    exact hs
  }
  {
    intro h1
    obtain ⟨i, hi1 ⟩ := h1
    have hface : is_face SC I J := by {
      rw [child_simplex_char]
      use i
      exact hi1.1
      exact hs
    }
    apply And.intro _ hface
    rw [complete_simplex_iff n1 I hface.1]
    intro c hc
    obtain ⟨i2, hi2⟩ := hi1.2 c hc
    have h3 := @almost_surjective_of_insert_index SC n1 hn1 i i2 hi2.1
    obtain ⟨j, hj⟩ := h3
    use j
    rw [hi1.1, ← hi2.2, hj]
    rfl
  }
}


lemma complete_child_uniq {SC n1} {hn1 : n1 + 1 = SC.n} J (hcs : complete_simplex SC SC.n J) :
    ∃! (I : Fin (n1+1) → SC.G), complete_simplex SC n1 I ∧ is_face SC I J := by {
  have h4 : ∃ i, SC.RL (J i) = SC.n := by {
    rw [← Set.mem_range, hcs.2]
    simp only [Set.mem_ofPred_eq, le_refl]
  }
  obtain ⟨ i, hi⟩ := h4
  let I := @delete_vertex SC n1 hn1 i J
  have hs2 : simplex SC n1 I := by {
    apply delete_vertex_simplex
    exact hcs.1
  }
  use I
  have h1 : complete_simplex SC n1 I ∧ is_face SC I J := by
  {
    rw [@char_complete_face SC n1 hn1 _ _ hcs.1]
    use i
    apply And.intro rfl
    rw [complete_simplex_iff] at hcs
    {
      intro c hc
      have h3 : c ≤ SC.n := by omega
      obtain ⟨i2, hi2 ⟩ := hcs c h3
      use i2
      apply And.intro _ hi2
      intro h4
      rw [h4, hi, ← hn1] at hi2
      rw [← hi2] at hc
      revert hc
      simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, imp_self]
    }
    {
      exact hcs.1
    }
  }
  simp only
  apply And.intro h1
  intro I2 h2
  rw [@char_complete_face SC n1 hn1 _ _ hcs.1] at h2
  obtain ⟨ i2, hi2 ⟩ := h2
  have h2 : SC.RL (J i2) = SC.n := by {
    let c2 := SC.RL (J i2)
    suffices h3 : ¬ (c2 ≤ n1) by {
      apply le_antisymm (SC.rl_proper (J i2)).1
      omega
    }
    intro h2
    obtain ⟨i3, hi3⟩ := hi2.2 c2 h2
    apply hi3.1
    apply rl_inj_of_complete SC.n J hcs
    exact hi3.2
  }
  suffices h3 : i2 = i by {
    rw [hi2.1, h3]
  }
  apply rl_inj_of_complete SC.n J hcs
  rw [h2]
  exact (Eq.symm hi)
}


lemma incomplete_childs {SC n1} {hn1 : n1 + 1 = SC.n} J (hs : simplex SC SC.n J)
    (hnc : ¬ complete_simplex SC SC.n J):
    Even (Finset.card { I : Fin (n1 + 1) → SC.G | complete_simplex SC n1 I ∧ is_face SC I J}) := by {
  let S : Finset _:= { I : Fin (n1 + 1) → SC.G | complete_simplex SC n1 I ∧ is_face SC I J}
  let c := S.card
  suffices h1 : c > 0 → c = 2 by {
    suffices h2 : Even c by {exact h2}
    by_cases h3 : c > 0
    rw [h1 h3]
    exact even_two
    use 0
    omega
  }
  intro cpos
  have h1 : Finset.Nonempty S := by {
    apply Finset.card_ne_zero.mp
    omega
  }
  obtain ⟨I1, h1 ⟩ := h1
  have hI1S := h1
  unfold S at h1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1
  obtain ⟨i1, hi1 ⟩ := (@char_complete_face SC n1 hn1 I1 J hs).mp h1
  apply Finset.card_eq_two.mpr
  have h2 : SC.RL (J i1) ≤ n1 := by {
    by_contra h3
    apply hnc
    rw [complete_simplex_iff _ _ hs]
    intro c hc
    by_cases h4 : c ≤ n1
    {
      obtain ⟨i2, hi2 ⟩ := hi1.2 c h4
      use i2
      exact hi2.2
    }
    {
      use i1
      have h6 : c = SC.n := le_antisymm hc (le_of_eq_of_le hn1.symm (not_le.mp h4))
      rw [h6]
      apply le_antisymm (SC.rl_proper (J i1)).1
      exact le_of_eq_of_le hn1.symm (not_le.mp h3)
    }
  }
  obtain ⟨i2, hi2⟩ := hi1.2 (SC.RL (J i1)) h2
  let I2 := @delete_vertex SC n1 hn1 i2 J
  have hI2S : I2 ∈ S := by {
    unfold S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [@char_complete_face SC n1 hn1 I2 J hs]
    use i2
    apply And.intro rfl
    intro c hc
    obtain ⟨i3, hi3⟩ := hi1.2 c hc
    by_cases h4 : i3 = i2
    {
      use i1
      rw [← hi3.2,h4, hi2.2]
      exact And.intro hi2.1.symm rfl
    }
    {
      use i3
      exact And.imp_left (fun a ↦ h4) hi3
    }
  }
  use I1, I2
  apply And.intro
  {
    intro h3
    apply hi2.1
    apply @delete_vertex_inj SC n1 hn1 J hs
    rw [← hi1.1, h3]
  }
  ext I3
  simp only [Finset.mem_insert, Finset.mem_singleton]
  apply Iff.intro
  {
    intro h3
    unfold S at h3
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h3
    have h31 := h3
    rw [@char_complete_face SC n1 hn1 I3 J hs] at h3
    obtain ⟨ i3, hi3 ⟩ := h3
    by_contra h4
    simp only [not_or] at h4
    rw [hi1.1] at h4
    have h7 : ∀ i4, ¬ (I3 = @delete_vertex SC n1 hn1 i4 J) → i4 ≠ i3 := by {
      intro i4 h8 h9
      apply h8
      rw [hi3.1, h9]
    }
    have h5 := @almost_surjective_of_insert_index SC n1 hn1 i3
    obtain ⟨ k1, hk1 ⟩ := h5 i1 (h7 i1 h4.1)
    obtain ⟨ k2, hk2 ⟩ := h5 i2 (h7 i2 h4.2)
    apply hi2.1
    suffices h7 : k1 = k2 by {
      rw [hk1, hk2, h7]
    }
    apply rl_inj_of_complete n1 I3 h31.1
    rw [hi3.1]
    unfold delete_vertex
    rw [← hk1, ← hk2]
    exact hi2.2.symm
  }
  {
    intro h5
    cases h5
    rename_i h9
    rwa [h9]
    rename_i h9
    rwa [h9]
  }
}


lemma complete_boundary_face_last {SC n1} {hn1 : n1 + 1 = SC.n} (I : Fin (n1 + 1) → SC.G)
    (hcbf : complete_boundary_face SC I) :
    ∀ i, ∀ j, j.1 + 1 = SC.n →  (I i j).1 = SC.p := by {
  intro i j hj
  revert i
  have h3 := @boundary_is_A_or_B SC n1 hn1 I hcbf.1
  have h1 : j.1 = n1 := by omega
  have h4 : ∀ n2, n2 ≤ n1 → ∃ i, SC.RL (I i) = n2 := by {
    intro n2 hn2
    rw [← Set.mem_range, hcbf.2.2]
    simp only [Set.mem_ofPred_eq, hn2]
  }
  have h6 (j2 : Fin SC.n) : j2.1 ≤ n1 := by omega
  cases h3
  {
    rename_i h1
    obtain ⟨ j2, hj2⟩ := h1
    exfalso
    obtain ⟨i, hi⟩ := h4 j2.1 (h6 j2)
    have h5 := ((SC.rl_proper (I i)).2 j2).1 (hj2 i)
    exact h5 hi
  }
  {
    rename_i h1
    obtain ⟨ j2, hj2⟩ := h1
    have hj3 i : (I i j2).1 = SC.p := by {
      rw [hj2 i]
      exact Fin.val_last SC.p
    }
    suffices h3 : j = j2 by {
      intro i
      rw [h3, hj3 i]
    }
    have h3 := SC.rl_proper
    obtain ⟨i, hi⟩ := h4 n1 (Nat.le_refl n1)
    have h5 := ((SC.rl_proper (I i)).2 j2).2 (hj3 i)
    rw [hi] at h5
    ext
    rw [h1]
    exact Nat.le_antisymm h5 (h6 j2)
  }
}

end completeness



section handshake

variable {A B : Type*}
variable [Fintype A] [Fintype B]

lemma handshake_3 (r : A → B → Prop) (c : A → Prop)
    (h1 : ∀ a, c a ↔ Odd (Finset.card {b | r a b}))
    : Odd (Finset.card {a | c a}) ↔ Odd (∑ a, Finset.card {b | r a b}) := by {
  rw [Finset.odd_sum_iff_odd_card_odd]
  rw [iff_eq_eq]
  congr
  ext a
  exact h1 a
}

lemma handshake_2 (r : A → B → Prop)
    (c : A → Prop) (d : B → Prop)
    (h1 : ∀ a, c a ↔ Odd (Finset.card {b | r a b}))
    (h2 : ∀ b, d b ↔ Odd (Finset.card {a | r a b})) :
    Odd (Finset.card {a | c a}) → Odd (Finset.card {b | d b}) := by {
  intro h3
  have h5 : ∑ a, Finset.card {b | r a b} = ∑ b, Finset.card {a | r a b} := by {
    apply Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
  }
  let r2 b a := r a b
  rw [handshake_3 r2 d h2, ←h5]
  rwa [←handshake_3 r c h1]
}

lemma handshake_1 (r : A → B → Prop)
    (c1 c2 c3: A → Prop) (d1 d2: B → Prop)
    (h1 : ∀ b, d1 b → ∃! a, c2 a ∧ r a b)
    (h2 : ∀ b, d2 b → ¬ d1 b → Even (Finset.card { a | c2 a ∧ r a b}))
    (h3 : ∀ a, c3 a → Finset.card { b | r a b} ∈ {c | c = 1 ∨ c = 2})
    (h5 : ∀ a, c1 a ↔ (∃! b, r a b) ∧ c2 a)
    (h6 : ∀ a, c2 a → c3 a) (h7 : ∀ b, ∀ a, r a b → d2 b)
    : Odd (Finset.card {a : A | c1 a}) → Odd (Finset.card {b : B | d1 b}) := by {
  let r2 a b := c2 a ∧ r a b
  apply handshake_2 r2
  {
    intro a
    rw [h5]
    by_cases p1 : c2 a
    unfold r2
    simp only [p1, and_true, true_and]
    rw [Fintype.existsUnique_iff_card_one]
    apply Iff.intro
    {
      intro p2
      use 0
      rwa [mul_zero, zero_add]
    }
    {
      intro p2
      have p3 := h3 a (h6 a p1)
      simp only [Set.mem_ofPred_eq] at p3
      cases p3
      rename_i p4
      exact p4
      rename_i p4
      rw [p4] at p2
      exfalso
      revert p2
      simp only [imp_false, Nat.not_odd_iff_even, even_two]
    }
    {
      unfold r2
      simp only [p1, and_false, false_and, Finset.filter_false, Finset.card_empty, Nat.not_odd_zero]
    }
  }
  {
    intro b
    by_cases p1 : d1 b
    {
      simp only [p1, true_iff]
      use 0
      rw [mul_zero, zero_add]
      rw [← Fintype.existsUnique_iff_card_one]
      exact h1 b p1
    }
    {
      simp only [p1, false_iff]
      intro p2
      have p5 : Finset.Nonempty {a | r2 a b} := by {
        have p3 : Odd (Finset.card { a | r2 a b}) := by {
          convert p2
        }
        apply Finset.card_ne_zero.mp
        intro p4
        revert p3
        rw [p4]
        simp only [Nat.not_odd_zero, imp_self]
      }
      have p3 : d2 b := by {
        obtain ⟨a, p6⟩ := p5
        apply h7 b a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at p6
        exact p6.2
      }
      revert p2
      have p4 := h2 b p3 p1
      simp only [imp_false, Nat.not_odd_iff_even]
      convert p4
    }
  }
}

end handshake



lemma odd_of_boundary_faces SC {n1} {hn1 : n1 + 1 = SC.n}:
    Odd (Finset.card { I : Fin (n1 + 1) → SC.G | complete_boundary_face SC I})
    → Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  apply handshake_1 (is_face SC)
  apply @complete_child_uniq SC n1 hn1
  apply @incomplete_childs SC n1 hn1
  apply @parent_count SC n1 hn1
  {
    intro I
    rfl
  }
  exact fun _ h1 ↦ h1.1
  exact fun _ _ h1 ↦ h1.2.1
}


section induction_step

variable (SC : SpernerCube)
variable {n1 : ℕ}


def child_map (v : Fin n1 → Fin (SC.p+1) ) : SC.G := fun i ↦
  match n1 with
  | 0 => Fin.last SC.p
  | Nat.succ _ => if i.1 + 1 = SC.n then Fin.last SC.p else v (Fin.ofNat _ i.1)

lemma child_map_last (v : Fin n1 → Fin (SC.p +1 ))
    : ∀ j, j.1 + 1 = SC.n → child_map SC v j = SC.p := by {
  intro j hj
  unfold child_map
  cases n1
  rfl
  simp only [hj, ↓reduceIte, Fin.val_last]
}

lemma child_map_applied [NeZero SC.n] {hn1 : n1 + 1 = SC.n} (v : Fin n1 → Fin (SC.p + 1))
    : ∀ (i : Fin n1), child_map SC v (Fin.ofNat _ i.1) = v i := by {
  intro i
  dsimp only [child_map]
  cases n1
  exact Fin.elim0 i
  rename_i n2
  simp only [Nat.succ_eq_add_one]
  have h5 : i.1 + 1 < SC.n := by omega
  have h2 : i.1 < SC.n := by omega
  have h3 := Fin.val_cast_of_lt h2
  rw [Fin.ofNat_eq_cast, h3]
  have h6 : i.1 + 1 ≠ SC.n := by omega
  simp only [h6, ↓reduceIte, Fin.ofNat_eq_cast, Fin.cast_val_eq_self]
}

lemma child_map_inj {hn1 : n1 + 1 = SC.n }: Function.Injective (@child_map SC n1) := by {
  intro v1 v2 h1
  ext i
  have h0 : NeZero SC.n := by {
    rw [← hn1]
    exact instNeZeroNatHAdd_1
  }
  rw [← child_map_applied SC v1]
  rw [← child_map_applied SC v2]
  rwa [h1]
  exact hn1
}

lemma child_map_surj_on {hn1 : n1 + 1 = SC.n} w
    (h1 : ∀ j, j.1 + 1 = SC.n → w j = SC.p)
    : ∃ v, @child_map SC n1 v = w := by {
  have h0 : NeZero SC.n := by {
    rw [← hn1]
    exact instNeZeroNatHAdd_1
  }
  let v2 : Fin n1 → Fin (SC.p +1) := fun i ↦ w (Fin.ofNat _ i.1)
  use v2
  apply funext
  intro i
  unfold child_map
  cases n1
  {
    simp only
    have h2 := h1 0
    simp only [Fin.val_zero, zero_add] at h2 hn1
    have h3 : i = 0 := by {
      have h4 := i.2
      simp only [← hn1] at h4
      ext
      simp only [Fin.val_zero]
      exact Nat.lt_one_iff.mp h4
    }
    rw [h3]
    exact Fin.eq_of_val_eq (id (Eq.symm (h2 hn1)))
  }
  {
    rename_i n2
    have h2 := h1 i
    by_cases h3 : i.1 +1 = SC.n
    {
      simp only [h3, ↓reduceIte]
      exact Eq.symm (Fin.eq_of_val_eq (h1 i h3))
    }
    simp only [h3, ↓reduceIte, Nat.succ_eq_add_one]
    unfold v2
    congr
    simp only [Fin.ofNat_eq_cast]
    rw [Fin.val_cast_of_lt]
    exact Fin.cast_val_eq_self i
    have h4 := i.2
    simp only [← hn1] at h3 h4
    omega
  }
}

def child_cube {hn1 : n1 + 1 = SC.n}: SpernerCube where
  n := n1
  p := SC.p
  RL := fun v ↦ SC.RL (child_map SC v)
  rl_proper := by {
    intro v
    have h0 : NeZero SC.n := by {
      rw [← hn1]
      exact instNeZeroNatHAdd_1
    }
    have h1 := child_map_last SC v
    have h2 := SC.rl_proper (child_map SC v)
    apply And.intro
    {
      have h3 := (h2.2 (Fin.ofNat _ n1)).2
      have h4 : n1 < SC.n := by omega
      simp only [Fin.ofNat_eq_cast] at h3
      rw [Fin.val_cast_of_lt h4] at h3
      apply h3
      apply child_map_last
      rw [Fin.val_cast_of_lt h4]
      exact hn1
    }
    intro i
    have h3 := h2.2 (Fin.ofNat _ i.1)
    rw [child_map_applied] at h3
    have h4 : (Fin.ofNat SC.n i.1).1 = i.1 := by {
      apply Fin.val_cast_of_lt
      omega
    }
    rwa [h4] at h3
    exact hn1
  }


end induction_step


lemma induction_start (SC : SpernerCube) (h0 : 0 = SC.n)
    : Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  use 0
  simp only [mul_zero, zero_add]
  rw [←Fintype.existsUnique_iff_card_one]
  let b : SC.G := fun _ ↦ 0
  let a : Fin (SC.n + 1) → SC.G := fun _ ↦ b
  use a
  simp only
  have h1 (x : Fin (SC.n+1)) : x = 0 := by {
    ext
    simp only [Fin.val_zero]
    rw [← Nat.lt_one_iff]
    apply Fin.val_lt_of_le x
    rw [←h0]
  }
  have hf (j : Fin SC.n) : False := by {
    apply Fin.elim0
    rwa [h0]
  }
  apply And.intro
  apply And.intro
  apply And.intro
  {
    intro x1 x2 _
    rw [h1 x1, h1 x2]
  }
  {
    intro i hi j
    exact False.elim ( hf j )
  }
  {
    ext i
    simp only [← h0]
    simp only [Set.mem_range, nonpos_iff_eq_zero, Set.ofPred_eq_eq_singleton, Set.mem_singleton_iff]
    have h3 : ∀ c, SC.RL (a c) = 0 := by {
      intro c
      have h2 := (SC.rl_proper (a c)).1
      simp only [← h0] at h2
      omega
    }
    apply Iff.intro
    {
      intro h2
      cases h2
      rename_i c hc
      rw [h3 c] at hc
      exact (Eq.symm hc)
    }
    {
      intro hi0
      use 0
      rw [hi0]
      exact h3 0
    }
  }
  {
    intro a2 h2
    ext i
    apply funext
    intro j
    exact False.elim ( hf j )
  }
}

theorem strong_cubical_sperner (k: ℕ ) : ∀ (SC : SpernerCube), k = SC.n →
    Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  induction' k with k hind
  {
    intro SC hk
    exact induction_start SC hk
  }
  {
    intro SC1 hk1
    apply @odd_of_boundary_faces SC1 k hk1
    let SC2 := @child_cube SC1 k hk1
    have hnz : NeZero SC1.n := by {
      rw [← hk1]
      exact instNeZeroNatHAdd_1
    }
    have h2 : Odd (Finset.card { I : Fin (k+1) → SC2.G | complete_simplex SC2 SC2.n I}) :=
      hind SC2 rfl
    apply Eq.mpr _ h2
    apply congrArg
    let f1 : SC2.G → SC1.G := child_map SC1
    let f2 : (Fin (k+1)→ SC2.G) → (Fin (k+1)→ SC1.G) := fun a ↦ fun b ↦ f1 (a b)
    have hf1inj : Function.Injective f1 := by {
      apply child_map_inj SC1
      rw [← hk1]
      rfl
    }
    symm
    have hcomp I : complete_boundary_face SC1 (f2 I) ↔ complete_simplex SC2 SC2.n I := by {
      unfold complete_boundary_face complete_simplex
      have h_last j k: j.1 + 1 = SC1.n → f2 I k j = SC1.p := by {
        apply child_map_last
      }
      have h_bf : simplex SC1 k (f2 I) ↔ is_boundary_face SC1 (f2 I) ∧ simplex SC1 k (f2 I):= by {
        simp only [iff_and_self]
        intro hs
        apply @case_B_boundary SC1 k hk1
        exact hs
        use (Fin.ofNat _ k)
        intro i
        ext
        apply h_last
        simp [← hk1]
      }
      rw [← and_assoc, ←h_bf]
      have h3 : SC2.n = k := rfl
      apply and_congr
      apply and_congr
      {
        apply Iff.intro
        {
          intro h4 i1 i2 h5
          exact h4 (congrArg f1 h5)
        }
        {
          intro h4 i1 i2 h5
          apply h4
          apply hf1inj h5
        }
      }
      {
        simp only [h3]
        apply forall₂_congr
        intro i hi1
        apply Iff.intro
        {
          intro h4 j
          have h6 k : (f2 I k (Fin.ofNat _ j.1)) = (I k j) := by {
            unfold f2
            apply child_map_applied
            rw [← hk1]
            rfl
          }
          have h7 := h4 (Fin.ofNat _ j.1)
          rw [h6, h6, h6, h6] at h7
          exact h7
        }
        {
          intro h4 j
          by_cases h5 : j.1 + 1 = SC1.n
          {
            rw [h_last, h_last, h_last, h_last]
            simp only [le_refl, le_add_iff_nonneg_right, zero_le,
              and_self]
            repeat' exact h5
          }
          {
            have h7 : j.1 < SC2.n := by {
              rw [h3]
              have h6 := j.2
              simp only [← hk1] at h5 h6
              omega
            }
            have hn02 : NeZero SC2.n := by {
              exact NeZero.of_gt hi1
            }
            let j2 : Fin SC2.n := (Fin.ofNat _ j.1)
            have h8 : j = (Fin.ofNat _ j2.1) := by {
              unfold j2
              simp only [Fin.ofNat_eq_cast,]
              rw [Fin.val_cast_of_lt]
              exact Eq.symm (Fin.cast_val_eq_self j)
              exact h7
            }
            have h6 k : (f2 I k j) = (I k j2) := by {
              unfold f2
              rw [h8]
              apply child_map_applied
              exact hk1
            }
            rw [h6, h6, h6, h6]
            exact h4 j2
          }
        }
      }
      exact Eq.congr_right rfl
    }
    apply Finset.card_nbij f2
    {
      intro I hI
      have hI' : complete_simplex SC2 SC2.n I :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hI)).2
      exact Finset.mem_coe.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcomp I).mpr hI'⟩)
    }
    {
      intro I1 h41 I2 h42 h5
      ext i
      apply hf1inj
      exact congrFun h5 i
    }
    {
      simp only [Finset.coe_filter, Finset.mem_univ, true_and]
      intro J
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      intro h3
      have h4 : ∃ I, f2 I = J := by {
        suffices h6 : ∀ i, ∃ ii, f1 ii = J i by {
          obtain ⟨I, h5⟩  := axiomOfChoice h6
          use I
          ext i
          exact h5 i
        }
        intro i
        have h5 := @child_map_surj_on SC1 k hk1
        apply h5
        exact @complete_boundary_face_last SC1 k hk1 J h3 i
      }
      obtain ⟨I, h4⟩ := h4
      use I
      simp only [h4, and_true]
      exact Set.mem_ofPred.mpr ((hcomp I).mp (h4 ▸ h3))
    }
  }

}

theorem weaker_cubical_sperner SC : ∃ I, complete_simplex SC SC.n I := by {
  have h1 := strong_cubical_sperner SC.n SC rfl
  obtain ⟨k1, hk1⟩ := h1
  have h2 : 0 < 2 * k1 + 1 := by omega
  rw [←hk1, Finset.card_pos] at h2
  obtain ⟨I, hI1⟩ := h2
  use I
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI1
  exact hI1
}

end

section

open Classical

/-
shows the fixed-point theorem for the unit cube
by applying the cubical sperner's lemma
-/


variable {n : ℕ}

def unit_cube := { v : Fin n → ℝ | 0 ≤ v ∧ v ≤ 1 }

noncomputable def rl_point {f : @unit_cube n → @unit_cube n} (x : @unit_cube n) : ℕ :=
  match (Finset.min { i | (f x).1 i < x.1 i ∨ x.1 i = 1}) with
    | some k => k.1
    | none => n

lemma reduced_label_props_1 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n)
    : @rl_point n f x ≤ n ∧ ∀ k,
    (@rl_point n f x = k.1 → (f x).1 k < x.1 k ∨ x.1 k = 1)
    ∧ ((f x).1 k < x.1 k ∨ x.1 k = 1 → @rl_point n f x ≤ k.1) := by {
  let s : Finset (Fin n) := {i | (f x).1 i < x.1 i ∨ x.1 i = 1}
  let minval := Finset.min s
  let rlp := match minval with
    | some k => k.1
    | none => n
  by_cases he : s = ∅
  {
    have h1 : @rl_point n f x = n := by {
      show rlp = n
      unfold rlp minval
      rw [he]
      simp only [Finset.min_empty]
    }
    rw [h1]
    simp only [le_refl, true_and]
    intro k
    have h2 : n ≠ k.1 := by omega
    simp only [h2, IsEmpty.forall_iff, true_and]
    intro h3
    have h4 : k ∈ s := by {
      unfold s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h3
    }
    rw [he] at h4
    simp only [Finset.notMem_empty] at h4
  }
  have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty hne
  have h1 : @rl_point n f x = m.1 := by {
    show rlp = m.1
    unfold rlp minval
    rw [hm]
  }
  rw [h1]
  simp only [Fin.is_le', Fin.val_fin_le, true_and]
  intro k1
  apply And.intro
  {
    intro h2
    suffices h3 : k1 ∈ s by {
      unfold s at h3
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h3
      exact h3
    }
    apply Finset.mem_of_min
    rw [hm]
    simp only [WithTop.coe_eq_coe]
    ext
    exact h2
  }
  {
    intro h2
    have h3 : k1 ∈ s := by {
      unfold s
      simp only [Finset.mem_filter, Finset.mem_univ, h2, and_self]
    }
    exact Finset.min_le_of_eq h3 hm
  }
}

lemma reduced_label_props_2 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n)
    : @rl_point n f x ≤ n ∧
    ∀ k, (x.1 k = 0 → @rl_point n f x ≠ k.1) ∧ (x.1 k = 1 → @rl_point n f x ≤ k.1):= by {
  have h1 := reduced_label_props_1 f x
  apply And.intro h1.1
  intro k
  apply And.intro
  {
    intro h2 h3
    have h4 := (h1.2 k).1 h3
    rw [h2] at h4
    simp only [zero_ne_one, or_false] at h4
    contrapose! h4
    exact (f x).2.1 k
  }
  {
    intro h2
    apply (h1.2 k).2
    exact Or.inr h2
  }
}

lemma reduced_label_props_3 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n) (k : Fin n)
    : (@rl_point n f x = k → (f x).1 k ≤ x.1 k) ∧ (@rl_point n f x > k → (f x).1 k ≥ x.1 k) := by {
  have h1 := (reduced_label_props_1 f x).2 k
  apply And.intro
  {
    intro h2
    cases h1.1 h2
    (expose_names; exact le_of_lt h)
    rename_i h3
    rw [h3]
    exact (f x).2.2 k
  }
  {
    contrapose!
    intro h2
    apply h1.2
    exact Or.inl h2
  }
}

noncomputable def discrete_map (p : ℕ ) (v : Fin n → Fin (p+1)) : @unit_cube n :=
  ⟨ fun i ↦ ((v i).1 : ℝ ) / p , by {
    unfold unit_cube
    simp only [Set.mem_ofPred_eq]
    rw [Pi.le_def, Pi.le_def, ←forall_and]
    intro i
    simp only [Pi.zero_apply, Pi.one_apply]
    apply And.intro
    exact div_nonneg (Nat.cast_nonneg' ↑(v i)) (Nat.cast_nonneg' p)
    apply div_le_one_of_le₀ ?_ (Nat.cast_nonneg' p)
    simp only [Nat.cast_le]
    exact Fin.is_le (v i)
  }⟩

noncomputable def sperner_cube_of_function (f : @unit_cube n → @unit_cube n)
  (p : ℕ ) {ppos : 0 < p} : SpernerCube where
  n := n
  p := p
  RL := fun v ↦ @rl_point _ f (discrete_map p v)
  rl_proper := by {
    intro v
    let x := discrete_map p v
    have h1 := reduced_label_props_2 f x
    apply And.intro h1.1
    intro k
    apply And.intro
    {
      intro h2
      apply (h1.2 k).1
      unfold x discrete_map
      simp only [div_eq_zero_iff, Nat.cast_eq_zero, Fin.val_eq_zero_iff]
      exact Or.inl h2
    }
    {
      intro h2
      apply (h1.2 k).2
      unfold x discrete_map
      simp only [h2]
      refine (div_eq_one_iff_eq ?_).mpr rfl
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    }
  }

lemma dist_discrete_map p (ppos: 0 < p) (v1 v2 : Fin n → Fin (p+1))
    (h1 : ∀ k, (v1 k).1 ≤ (v2 k).1 + 1 ∧ (v2 k).1 ≤ (v1 k).1 + 1) :
    dist (discrete_map p v1) (discrete_map p v2) ≤ 1 / p := by {
  let x1 := (discrete_map p v1).1
  let x2 := (discrete_map p v2).1
  show dist x1 x2 ≤ 1 / p
  refine (dist_pi_le_iff ?_).mpr ?_
  simp only [one_div, inv_nonneg, Nat.cast_nonneg]
  intro k
  have hx1 : x1 k = (v1 k).1 / p := by {rfl}
  have hx2 : x2 k = (v2 k).1 / p := by {rfl}
  rw [hx1, hx2]
  rw [Real.dist_eq, abs_sub_le_iff]
  have h1k := (h1 k).1
  have h2k := (h1 k).2
  apply And.intro
  repeat {
    rw [sub_le_iff_le_add', ← add_div]
    have ppos2 : 0 < (p : ℝ) := Nat.cast_pos'.mpr ppos
    rwa [div_le_div_iff_of_pos_right ppos2, ←Nat.cast_add_one, Nat.cast_le]
  }
}

lemma nearby_points (f : @unit_cube n → @unit_cube n) (p0:ℕ):
    ∃ x0 : @unit_cube n, ∀ k, (f x0).1 k ≥ x0.1 k ∧
    ∃ xk : @unit_cube n, dist x0 xk ≤ 1 / ↑(p0 +1) ∧ (f xk).1 k ≤ xk.1 k := by {
  let p := p0 + 1
  have ppos : 0 < p := by omega
  let SC := @sperner_cube_of_function n f p ppos
  obtain ⟨I, h3⟩ := weaker_cubical_sperner SC
  have h4 j : j ≤ n → ∃ i, SC.RL (I i) = j := by {
    intro h4
    exact h3.2.symm.subset h4
  }
  obtain ⟨i0, hi0⟩ := h4 n (Nat.le_refl n)
  let x0 := discrete_map SC.p (I i0)
  use x0
  intro k
  apply And.intro
  {
    apply (reduced_label_props_3 f x0 k).2
    have h6 : @rl_point _ f x0 = n := by exact hi0
    rw [h6]
    simp only [gt_iff_lt, Fin.is_lt]
  }
  obtain ⟨ik, hik⟩ := h4 k.1 k.is_le'
  let xk := discrete_map SC.p (I ik)
  use xk
  apply And.intro _ $ (reduced_label_props_3 f xk k).1 hik
  unfold x0 xk
  apply dist_discrete_map p ppos
  have h5 := le_add_one_of_simplex SC I h3.1
  intro k
  exact ⟨h5 i0 ik k, h5 ik i0 k⟩
}


theorem fixed_point_unit_cube (f : C(@unit_cube n, @unit_cube n)) : ∃ x, f x = x := by {
  obtain ⟨x0s, hx0⟩ := axiomOfChoice (nearby_points f)
  have hc1 : ∃ xx : @unit_cube n, ∃ (φ:ℕ → ℕ ), StrictMono φ ∧
      Filter.Tendsto (x0s ∘ φ ) Filter.atTop (nhds xx) := by {
    have hc1 : IsCompact (@unit_cube n) := isCompact_Icc
    let x0 : ℕ → Fin n → ℝ := fun i ↦ (x0s i).1
    have h2 : ∀ i, x0 i ∈ unit_cube := fun i ↦ (x0s i).2
    obtain ⟨a, ⟨ha, ⟨φ,h3⟩ ⟩ ⟩ := hc1.isSeqCompact h2
    use ⟨a, ha⟩
    use φ
    exact And.intro h3.1 $ tendsto_subtype_rng.mpr h3.2
  }
  obtain ⟨xxx, ⟨φ, h2⟩ ⟩ := hc1
  let y0 := x0s ∘ φ
  let g : Fin n → @unit_cube n → ℝ := fun k x ↦ x.1 k
  have hc2 k : Continuous (g k) := by {
    exact (continuous_apply k).comp continuous_subtype_val
  }
  have h3 k : xxx.1 k ≤ (f xxx).1 k := by {
    show g k xxx ≤ g k (f xxx)
    have h6 :=  (hc2 k).seqContinuous h2.2
    have h7 := (hc2 k).seqContinuous $ f.2.seqContinuous h2.2
    apply le_of_tendsto_of_tendsto' h6 h7
    exact fun i ↦ (hx0 (φ i) k).1
  }
  have h4 k : (f xxx).1 k ≤ xxx.1 k := by {
    show g k (f xxx) ≤ g k xxx
    have h5 n:= (hx0 (φ n) k).2
    obtain ⟨yk, h6⟩ := axiomOfChoice h5
    have h4 : Filter.Tendsto yk Filter.atTop (nhds xxx) := by {
      apply tendsto_of_tendsto_of_dist h2.2
      have h7 := @tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h7 _
      {
        intro i
        apply le_trans (h6 i).1
        simp only [Nat.cast_add, Nat.cast_one, one_div]
        apply inv_anti₀ (Nat.cast_add_one_pos i)
        simp only [add_le_add_iff_right, Nat.cast_le, h2.1.le_apply]
      }
      exact fun _ ↦ dist_nonneg
    }
    have h7 := (hc2 k).seqContinuous h4
    have h8 := (hc2 k).seqContinuous $ f.2.seqContinuous h4
    apply le_of_tendsto_of_tendsto' h8 h7
    exact fun i ↦ (h6 i).2
  }
  use xxx
  ext k
  apply le_antisymm (h4 k) (h3 k)
}

/-- The cubical fixed-point theorem stated with mathlib's `Function.IsFixedPt` vocabulary. -/
theorem fixed_point_unit_cube_isFixedPt (f : C(@unit_cube n, @unit_cube n)) :
    ∃ x, Function.IsFixedPt f x := by
  simpa [Function.IsFixedPt] using fixed_point_unit_cube f

end

section

/-
some helper lemmas involving homeomorphisms.
-/


lemma homeo_unit_ball {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s: Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s)
    (hni : (interior s).Nonempty):
    Nonempty (s ≃ₜ Metric.closedBall (0: V) 1) := by {
  have h1 := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hcvx hni
  have h2 : Bornology.IsBounded s := IsCompact.isBounded hcmpct
  cases (h1 h2)
  rename_i e he
  have h4 := closure_eq_iff_isClosed.mpr (IsCompact.isClosed hcmpct)
  have e2 := Homeomorph.image e s
  rw [h4] at he
  rw [he.2.1] at e2
  exact Nonempty.intro e2
}


theorem homeo_of_finrank_eq {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (hreq : Module.finrank ℝ V = Module.finrank ℝ W) :
    Nonempty (Metric.closedBall (0: V) 1 ≃ₜ Metric.closedBall (0: W) 1) := by {
  have L := ContinuousLinearEquiv.ofFinrankEq hreq
  let pL := L ⁻¹' (Metric.closedBall (0:W) 1)
  have hpL : pL = L.toHomeomorph ⁻¹' (Metric.closedBall (0:W) 1) := rfl
  have h4 : Convex ℝ pL := Convex.linear_preimage (convex_closedBall 0 1) L.toLinearMap
  have h5 : IsCompact pL := by {
    rw [hpL,Homeomorph.isCompact_preimage]
    exact isCompact_closedBall 0 1
  }
  have h6 : (interior pL).Nonempty := by {
    rw [hpL, ← Homeomorph.preimage_interior]
    refine (Function.Surjective.nonempty_preimage ?_).mpr ?_
    exact Homeomorph.surjective L.toHomeomorph
    use 0
    rw [interior_closedBall]
    {simp only [Metric.mem_ball, dist_self, zero_lt_one]}
    {exact Ne.symm (zero_ne_one' ℝ)}
  }
  have e1 : pL ≃ₜ Metric.closedBall (0:W) 1 := by {
    rw [hpL]
    exact L.toHomeomorph.sets hpL
  }
  have h7 := homeo_unit_ball _ h4 h5 h6
  cases h7
  rename_i e2
  apply Nonempty.intro
  exact e2.symm.trans e1
}


lemma unit_cube_homeo_unit_ball {n}
    : Nonempty (Set.Icc (0 : Fin n → ℝ) 1 ≃ₜ Metric.closedBall (0 : Fin n → ℝ) 1 ) := by
  apply homeo_unit_ball _ (convex_Icc 0 1) isCompact_Icc
  have h1 : Set.Icc (0 : Fin n → ℝ) 1 = Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1) := by
    ext x; simp [Set.mem_Icc, Pi.le_def]
  rw [h1, interior_pi_set Set.finite_univ]
  exact Set.univ_pi_nonempty_iff.mpr fun _ => by
    rw [interior_Icc]; exact ⟨1/2, by norm_num, by norm_num⟩

lemma homeo_unit_cube_of_convex_compact {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s: Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : s.Nonempty)
    : ∃ k, Nonempty (s ≃ₜ Set.Icc (0 : Fin k → ℝ) 1) := by {
  have := hne.coe_sort
  let W := affineSpan ℝ s
  obtain ⟨ps, hps⟩ := hne
  let pss : W := ⟨ps, mem_affineSpan ℝ hps⟩
  let g2 := AffineIsometryEquiv.constVSub ℝ pss
  let g1 : W → V := fun x ↦ x.1
  let s2 := g1 ⁻¹' s
  let s3 := g2.symm ⁻¹' s2
  have h32 : Convex ℝ s3 := by {
    exact hcvx.affine_preimage
      ((affineSpan ℝ s).subtype.comp
      (AffineIsometryEquiv.constVSub ℝ pss).symm.toAffineMap)
  }
  have h34 : (interior s3).Nonempty := by {
    refine (Convex.interior_nonempty_iff_affineSpan_eq_top h32).mpr ?_
    unfold s3
    rw [←AffineIsometryEquiv.coe_toAffineEquiv]
    rw [← AffineSubspace.comap_span]
    rw [affineSpan_coe_preimage_eq_top]
    rfl
  }
  let g3 := g1.comp g2.symm
  have h4 : Topology.IsEmbedding g3 := by {
    apply Topology.IsEmbedding.subtypeVal.comp g2.symm.toHomeomorph.isEmbedding
  }
  have h5 : Set.MapsTo g3 s3 s := by {
    intro w h1
    unfold s3 s2 at h1
    rwa [Set.mem_preimage, Set.mem_preimage] at h1
  }
  have h6 : Function.Surjective (Set.MapsTo.restrict g3 s3 s h5) := by {
    refine (Set.MapsTo.restrict_surjective_iff h5).mpr ?_
    refine Set.SurjOn.comp_right ?_ ?_
    exact AffineIsometryEquiv.surjective g2.symm
    intro v h1
    refine (Set.mem_image g1 (g1 ⁻¹' s) v).mpr ?_
    have h11 : v ∈ affineSpan ℝ s := mem_affineSpan ℝ h1
    use ⟨v, h11⟩
    simp only [Set.mem_preimage]
    apply And.intro h1 rfl
  }
  let e1 := (h4.restrict h5).toHomeomorphOfSurjective h6
  have h31 : IsCompact s3 := by {
    have h51 : _ → IsCompact Set.univ := (Homeomorph.isCompact_image e1).mp
    simp only [Set.image_univ, EquivLike.range_eq_univ] at h51
    apply isCompact_iff_isCompact_univ.mpr
    apply h51 $ isCompact_iff_isCompact_univ.mp hcmpct
  }
  obtain ⟨e2⟩ := homeo_unit_ball s3 h32 h31 h34
  let k := Module.finrank ℝ W.direction
  obtain ⟨e3⟩ := @unit_cube_homeo_unit_ball k
  have h2 : k = Module.finrank ℝ (Fin k → ℝ) := (Module.finrank_fin_fun ℝ).symm
  obtain ⟨e4⟩ := homeo_of_finrank_eq h2
  let e5 := (e1.symm.trans e2).trans (e4.trans e3.symm)
  use k
  exact Nonempty.intro e5
}

end

section

/- Brouwer fixed-point theorem:
Every continuous function mapping a nonempty compact convex set to itself has a fixed point
(the set should be a subset of a finite dimensional vector space).

https://en.wikipedia.org/wiki/Brouwer_fixed-point_theorem
-/


theorem brouwer_fixed_point {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    : ∀ (s : Set V), Convex ℝ s → IsCompact s → Set.Nonempty s →
    ∀ (f : C(s, s)), ∃ x, f x = x := by {
  intro s hcvx hcmpct hne f
  obtain ⟨k, ⟨e⟩ ⟩ := homeo_unit_cube_of_convex_compact s hcvx hcmpct hne
  let g := (toContinuousMap e).comp (f.comp (toContinuousMap e.symm))
  obtain ⟨y, hy⟩ := @fixed_point_unit_cube k g
  use (toContinuousMap e.symm) y
  have h1 : e.symm (e (f (e.symm y))) = e.symm y := congrArg e.symm hy
  rwa [e.symm_apply_apply] at h1
}

/-- Brouwer's fixed-point theorem stated with mathlib's `Function.IsFixedPt` vocabulary. -/
theorem brouwer_fixed_point_isFixedPt {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : Set.Nonempty s)
    (f : C(s, s)) :
    ∃ x, Function.IsFixedPt f x := by
  simpa [Function.IsFixedPt] using brouwer_fixed_point s hcvx hcmpct hne f

/-- The fixed-point set of a continuous self-map on a Brouwer domain is nonempty. -/
theorem brouwer_fixedPoints_nonempty {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : Set.Nonempty s)
    (f : C(s, s)) :
    (Function.fixedPoints f).Nonempty := by
  exact brouwer_fixed_point_isFixedPt s hcvx hcmpct hne f

end

section

/-
Kakutani Fixed-Point theorem:
Let s be a nonempty, compact, convex of a finite-dimensional space.
Let f be a set-valued map on s with closed graph,
and each f(x) be nonempty, compact, convex, and a subset of s.
Then there is a point x with x ∈ f(x).

Main result is `kakutani_fixed_point` below.
Proof relies on the Brouwer fixed-point theorem.

https://en.wikipedia.org/wiki/Kakutani_fixed-point_theorem
-/

open Classical
open Filter

/- defining the closed graph property of a set-valued map -/
def closedGraph {X Y} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Set Y) : Prop :=
    IsClosed { z : X × Y | z.2 ∈ f z.1}

/- defining that x is a convex combinations of points y_i with weights a_i -/
def convex_comb {V : Type*} {k: ℕ} [AddCommGroup V] [Module ℝ V]
  (x : V) (a : Fin k → ℝ) (y: Fin k → V) : Prop :=
  (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1 ∧ x = ∑ i, a i • y i


lemma mem_of_convex_comb {V : Type*} {k: ℕ} [AddCommGroup V] [Module ℝ V]
  (x : V) {a : Fin k → ℝ} {y: Fin k → V} (h0 : convex_comb x a y)
  s (h1 : Convex ℝ s) (h2 : ∀ i, y i ∈ s): x ∈ s := by {
  unfold convex_comb at h0
  rw [h0.2.2]
  apply Convex.sum_mem h1 (fun i _ ↦ h0.1 i) h0.2.1 fun i a ↦ h2 i
}


lemma sub_ICC_of_convex_comb {V : Type*} {k: ℕ} [AddCommGroup V] [Module ℝ V]
    (x : V) {a : Fin k → ℝ} {y: Fin k → V} (h0 : convex_comb x a y)
    : a ∈ Set.Icc 0 1 := by {
  simp only [Set.mem_Icc]
  apply And.intro h0.1
  have h2 := h0.1
  have h1 := h0.2.1
  intro i
  simp only [Pi.one_apply]
  rw [←h1]
  apply Finset.single_le_sum (fun i a ↦ h2 i)
  simp only [Finset.mem_univ]
}


/- useful to get a fixed size of vectors -/
lemma caratheodory_1 {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) k (h1 : k = Module.finrank ℝ V) {x} (h2 : x ∈ convexHull ℝ s)
    : ∃ (z : Fin (k+1)→ V), ∃ a, Set.range z ⊆ s ∧ convex_comb x a z := by {
  obtain ⟨I ,hI,z1,α, h3⟩  := eq_pos_convex_span_of_mem_convexHull h2
  have h4 : hI.card ≤ k + 1 := by {
    apply le_trans $ AffineIndependent.card_le_finrank_succ h3.2.1
    rw [h1,add_le_add_iff_right]
    exact Submodule.finrank_le (vectorSpan ℝ (Set.range z1))
  }
  let g1 := hI.equivFin
  let g2 : Fin (hI.card) → Fin (k+1) := fun i ↦ Fin.ofNat _ i.1
  let g3 := g2 ∘ g1
  have hg3 : Function.Injective g3 := by {
    unfold g3
    refine (Equiv.injective_comp g1 g2).mpr ?_
    intro i1 i2 h5
    unfold g2 at h5
    simp only [Fin.ofNat_eq_cast] at h5
    rw [←Fin.val_eq_val] at h5 ⊢
    rwa [Fin.val_cast_of_lt, Fin.val_cast_of_lt] at h5 <;> omega
  }
  have hsne : s.Nonempty := convexHull_nonempty_iff.mp (Set.nonempty_of_mem h2)
  obtain ⟨sdef, hsdef⟩ := hsne
  let β := Function.extend g3 α (fun _ ↦ 0)
  let z2 := Function.extend g3 z1 (fun _ ↦ sdef)
  have h5 : Set.range z2 ⊆ s := by {
    intro y hy
    obtain ⟨i1, hi1⟩ := hy
    rw [← hi1]
    unfold z2
    by_cases h5 : ∃ i2, g3 i2 = i1
    {
      apply h3.1
      obtain ⟨i2, hi2⟩ := h5
      use i2
      rw [←hi2,Function.Injective.extend_apply hg3]
    }
    rwa [Function.extend_apply' _ _ _ h5]
  }
  use z2, β
  have h6 : ∑ i, β i = 1 := by {
    rw [←h3.2.2.2.1]
    symm
    apply Fintype.sum_of_injective g3 hg3
    exact fun i a ↦ Function.extend_apply' α (fun x ↦ 0) i a
    exact fun i ↦ Eq.symm (Function.Injective.extend_apply hg3 α (fun x ↦ 0) i)
  }
  have h7 : x = ∑ i, β i • z2 i := by {
    rw [←h3.2.2.2.2]
    apply Fintype.sum_of_injective g3 hg3
    intro i h7
    simp only [smul_eq_zero]
    exact Or.inl $ Function.extend_apply' α (fun x ↦ 0) i h7
    intro i
    unfold β z2
    rw [Function.Injective.extend_apply hg3,Function.Injective.extend_apply hg3]
  }
  have h9 i : 0 ≤ β i := by {
    unfold β
    have h12 : 0 ≤ α := fun i ↦ le_of_lt (h3.2.2.1 i)
    apply Function.extend_nonneg h12
    rfl
  }
  apply And.intro h5
  apply And.intro h9 (And.intro h6 h7)
}

lemma set_valued_map_approx_fixed_point {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcmpct : IsCompact s) (hcvx : Convex ℝ s) (hne : s.Nonempty) (f : s → Set V)
    (h1 : ∀ x, f x ⊆ s ∧ Convex ℝ (f x) ∧ (f x).Nonempty)
    k (hk : k = Module.finrank ℝ V) (eps : ℝ ) (heps : 0 < eps)
    : ∃ a : s, ∃ (y : Fin (k+1)→ s), ∃ z, ∃ α, convex_comb a.1 α z
    ∧ ∀ i, dist a (y i) < eps ∧ (z i ) ∈ f (y i)  := by {
  let eb (x : s) := Metric.ball x eps
  let G : s → Set V := fun x ↦ convexHull ℝ {z | ∃ y, dist x y < eps ∧ z ∈ f y}
  have hG1 : ∀ x, Convex ℝ (G x) := by {
    intro x
    exact convex_convexHull ℝ {z | ∃ y, dist x y < eps ∧ z ∈ f y}
  }
  have : CompactSpace ↑s := isCompact_iff_compactSpace.mp hcmpct
  have h2 := exists_continuous_forall_mem_convex_of_local_const hG1
  have h3 : ∃ g : C(s, V), ∀ x, g x ∈ G x := by {
    apply h2
    intro x
    obtain ⟨z, hz⟩ := (h1 x).2.2
    use z
    apply Metric.eventually_nhds_iff.mpr
    use eps
    apply And.intro heps
    intro y h3
    apply subset_convexHull
    use x
  }
  obtain ⟨g, hg⟩ := h3
  have h6 : ∀ x, g x ∈ s := by {
      intro x
      suffices h6 : G x ⊆ s  by {exact h6 (hg x)}
      unfold G
      apply convexHull_min _ hcvx
      intro z h5
      obtain ⟨y, hy⟩ := h5
      apply (h1 y).1 hy.2
    }
  have h5 : ∃ x, g x = x := by {
    let g2 : s → s := fun x ↦ ⟨g x, h6 x⟩
    have h7 : Continuous g2 := Continuous.subtype_mk g.continuous h6
    let g3 : C(s,s) := ⟨g2, h7⟩
    have brouwer_fpt := brouwer_fixed_point s hcvx hcmpct hne g3
    obtain ⟨x, hx⟩ := brouwer_fpt
    use x
    nth_rewrite 2 [←hx]
    rfl
  }
  obtain ⟨a, ha⟩ := h5
  have h5 : a.1 ∈ G a := by {
    rw [←ha]
    exact hg a
  }
  obtain ⟨z, ⟨α, h7⟩ ⟩ := caratheodory_1 _ k hk h5
  use a
  have h8 i : ∃ y, dist a y < eps ∧ (z i) ∈ f y := by {
    apply h7.1
    use i
  }
  obtain ⟨y, hy⟩ := axiomOfChoice h8
  use y, z, α
  tauto
}



theorem kakutani_fixed_point {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : Set.Nonempty s)
    (f : s → Set V) (hcg : closedGraph f)
    (h1 : ∀ x, f x ⊆ s ∧ Convex ℝ (f x) ∧ (f x).Nonempty)
    : ∃ x : s, x.1 ∈ f x := by {
  let k := Module.finrank ℝ V
  have h2 := set_valued_map_approx_fixed_point s hcmpct hcvx hne f h1 k rfl
  have h31 (i : ℕ) : 0 < (1:ℝ )/(i+1) := Nat.one_div_pos_of_nat
  have h3 (i : ℕ) := h2 ((1:ℝ )/(i + 1)) (h31 i)
  have h5 i := Prod.exists'.mpr (Prod.exists'.mpr (Prod.exists'.mpr (h3 i)))
  obtain ⟨B,h6⟩ := axiomOfChoice h5
  clear h2 h3 h5
  let Btype := ((↑s × (Fin (k + 1) → ↑s)) × (Fin (k + 1) → V)) × (Fin (k + 1) → ℝ)
  let sB : Set Btype := (Set.univ ×ˢ {x | ∀ i, x i ∈ s}) ×ˢ (Set.Icc 0 1)
  have hBc : IsCompact sB := by {
    have : CompactSpace ↑s := isCompact_iff_compactSpace.mp hcmpct
    apply IsCompact.prod
    apply IsCompact.prod
    {
      apply isCompact_univ_iff.mpr
      apply instCompactSpaceProd
    }
    exact isCompact_pi_infinite fun i ↦ hcmpct
    exact isCompact_Icc
  }
  have h4 i : B i ∈ sB := by {
    unfold sB
    apply And.intro
    apply And.intro trivial
    intro i2
    apply (h1 ((B i).1.1.2 i2)).1
    exact ((h6 i).2 i2).2
    exact sub_ICC_of_convex_comb _ (h6 i).1
  }
  obtain ⟨B0, hB0, φ, h3⟩ := hBc.isSeqCompact h4
  let A := B ∘ φ
  have hA2 : Tendsto A atTop (nhds B0) := h3.2
  let x i := (A i).1.1.1
  let y j i := (A i).1.1.2 j
  let z j i := (A i).1.2 j
  let α j i := (A i).2 j
  let xxx := B0.1.1.1
  have ha2 j : Tendsto (α j) atTop (nhds (B0.2 j)) := by {
    exact (continuous_apply j).seqContinuous (Tendsto.snd_nhds hA2)
  }
  have hz2 j : Tendsto (z j) atTop (nhds (B0.1.2 j)) := by {
    exact (continuous_apply j).seqContinuous (Tendsto.fst_nhds hA2).snd_nhds
  }
  have hx2 : Tendsto x atTop (nhds xxx) :=  (Tendsto.fst_nhds hA2).fst_nhds.fst_nhds
  have hy2 j: Tendsto (y j) atTop (nhds xxx) := by {
    have h8 i : dist (x i) (y j i) < 1 / (↑(φ i) + 1) := ((h6 (φ i)).2 j).1
    have h7 := @tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _
    apply tendsto_of_tendsto_of_dist hx2
    apply squeeze_zero (fun _ ↦ dist_nonneg) _ h7
    intro i
    apply le_trans (le_of_lt (h8 i))
    simp only [one_div]
    apply inv_anti₀ (Nat.cast_add_one_pos i)
    simp only [add_le_add_iff_right, Nat.cast_le]
    exact h3.1.le_apply
  }
  have h8 j : B0.1.2 j ∈ f (xxx) := by {
    let yzj i := (y j i, z j i)
    have h10 i: yzj i ∈ {x | x.2 ∈ f x.1} := ((h6 (φ i)).2 j).2
    have h11 : Tendsto yzj atTop (nhds (xxx, B0.1.2 j))
        := Tendsto.prodMk_nhds (hy2 j) (hz2 j)
    exact hcg.isSeqClosed h10 h11
  }
  have h9 : convex_comb xxx.1 B0.2 B0.1.2 := by {
    apply And.intro
    {
      intro j
      apply ge_of_tendsto' (ha2 j)
      exact fun i ↦ (h6 (φ i)).1.1 j
    }
    apply And.intro
    {
      have h12 := tendsto_finsetSum Finset.univ (fun i _ ↦ ha2 i)
      have h11 i : ∑ c, α c i = 1 := (h6 (φ i)).1.2.1
      simp only [h11, tendsto_const_nhds_iff] at h12
      exact h12.symm
    }
    have h11 i : x i = ∑ j, α j i • z j i := (h6 (φ i)).1.2.2
    have h12 j := Tendsto.smul (ha2 j) (hz2 j)
    have h13 := tendsto_finsetSum Finset.univ (fun i _ ↦ h12 i)
    simp only [← h11] at h13
    have h14 : Tendsto (fun i ↦ (x i).1) atTop (nhds xxx.1) := by {
      apply continuous_subtype_val.seqContinuous hx2
    }
    apply tendsto_nhds_unique h14 h13
  }
  use xxx
  apply mem_of_convex_comb xxx.1 h9 _ (h1 xxx).2.1 h8
}

end
/- A finite Cayley factorization for the real triangular Lyapunov equation. -/

namespace MO309804
open Matrix Polynomial
open scoped MatrixOrder

abbrev M (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

private def sand {n} (T P : M n) := T * P * star T

private lemma sand_sand {n} (S T P : M n) : sand S (sand T P) = sand (S*T) P := by
  simp [sand,star_mul,mul_assoc]

private lemma sand_psd {n} {X : M n} (h : X.PosSemidef) (T : M n) : (sand T X).PosSemidef :=
  h.mul_mul_conjTranspose_same T

private lemma plus_unit {n} {A : M n} (ht : A.IsUpperTriangular) (hd : ∀ i, A i i < 0)
    {a : ℝ} (ha : a < 0) : IsUnit (A + a • 1) := by
  rw [Matrix.isUnit_iff_isUnit_det,Matrix.det_of_isUpperTriangular, isUnit_iff_ne_zero]
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    simpa using (show A i i + a ≠ 0 by have := hd i; linarith)
  · intro i j hij
    have hne : i ≠ j := by intro h; subst j; exact lt_irrefl _ hij
    simp [ht hij, Matrix.one_apply_ne hne]

private lemma sandwich_shift {n} (A P X : M n) (a : ℝ)
    (he : A*P+P*star A= -X) :
    sand (A+a•1) P = sand (A-a•1) P + (-2*a) • X := by
  have hX : X = -(A*P+P*star A) := by rw [he,neg_neg]
  rw [hX]
  simp only [sand,star_add,star_sub,star_smul,star_trivial,star_one,add_mul,sub_mul,mul_add,mul_sub,
    smul_mul_assoc,mul_smul_comm,mul_one,one_mul,smul_sub,smul_add,smul_neg]
  module

private lemma shift_eq {n} (A P X : M n) (a : ℝ) (he : A*P+P*star A= -X) :
    A * sand (A-a•1) P + sand (A-a•1) P * star A = -sand (A-a•1) X := by
  let T := A-a•1
  have hc : A*T=T*A := by simp [T,mul_sub,sub_mul]
  have hs : star T*star A=star A*star T := by simpa using congrArg star hc
  change A * sand T P + sand T P * star A = -sand T X
  calc
    _ = (A*T)*P*star T + T*P*(star T*star A) := by simp [sand,mul_assoc]
    _ = T*(A*P+P*star A)*star T := by rw [hc,hs]; simp [mul_add,add_mul,mul_assoc]
    _ = _ := by simp [he,sand]

private noncomputable def poly {n} (A : M n) (s : Finset (Fin n)) : ℝ[X] := ∏ i ∈ s, (X - C (A i i))

private lemma finite_psd {n} {A : M n} (ht : A.IsUpperTriangular) (hd : ∀ i, A i i < 0)
    (s : Finset (Fin n)) (P X : M n) (hX : X.PosSemidef) (he : A*P+P*star A= -X)
    (hz : sand (aeval A (poly A s)) P = 0) : P.PosSemidef := by
  classical
  induction s using Finset.induction_on generalizing P X with
  | empty =>
    simp [poly,sand] at hz
    simpa [hz] using (Matrix.PosSemidef.zero : (0 : M n).PosSemidef)
  | @insert i s hi ih =>
    let a := A i i
    let T := A-a•1
    have hh : (sand T P).PosSemidef := by
      apply ih (sand T P) (sand T X) (sand_psd hX T) (shift_eq A P X a he)
      rw [sand_sand]
      have hpoly : poly A (insert i s) = poly A s * (Polynomial.X - C a) := by
        simp [poly,hi,mul_comm,a]
      simpa only [hpoly,map_mul,map_sub,aeval_X,aeval_C,Algebra.algebraMap_eq_smul_one,T] using hz
    apply (Matrix.IsUnit.posSemidef_star_right_conjugate_iff (x:=P) (plus_unit ht hd (hd i))).mp
    change (sand (A+a•1) P).PosSemidef
    rw [sandwich_shift A P X a he]
    exact hh.add (hX.smul (show 0 ≤ -2*a by dsimp [a]; have := hd i; linarith))

theorem lyap_psd {n} {A P X : M n} (ht : A.IsUpperTriangular) (hd : ∀ i, A i i < 0)
    (hX : X.PosSemidef) (he : A*P+P*A.transpose= -X) : P.PosSemidef := by
  apply finite_psd ht hd Finset.univ P X hX
  · simpa [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using he
  · have hpoly : poly A Finset.univ = A.charpoly := (A.charpoly_of_isUpperTriangular ht).symm
    simp [hpoly,A.aeval_self_charpoly,sand]

theorem lyap_pd {n} (hn : 0<n) {A P X : M n} (ht : A.IsUpperTriangular) (hd : ∀ i, A i i < 0)
    (hX : X.PosDef) (he : A*P+P*A.transpose= -X) : P.PosDef := by
  let i : Fin n := ⟨0,hn⟩
  let a := A i i
  let T := A-a•1
  have hstar : A*P+P*star A= -X := by
    simpa [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using he
  have hT : (sand T P).PosSemidef := sand_psd (lyap_psd ht hd hX.posSemidef he) _
  apply (Matrix.IsUnit.posDef_star_right_conjugate_iff (x:=P) (plus_unit ht hd (hd i))).mp
  change (sand (A+a•1) P).PosDef
  rw [sandwich_shift A P X a hstar]
  exact Matrix.PosDef.posSemidef_add hT (hX.smul (show 0 < -2*a by dsimp [a]; have := hd i; linarith))

private def op {n} (A : M n) : M n →ₗ[ℝ] M n where
  toFun P := -(A*P+P*A.transpose)
  map_add' P Q := by simp only [mul_add,add_mul]; abel
  map_smul' c P := by simp [smul_add]

theorem exists_solver {n} (hn : 0<n) (A : M n) (ht : A.IsUpperTriangular) (hd : ∀ i, A i i < 0) :
    ∃ L : M n →L[ℝ] M n, (∀ X, A*(L X)+(L X)*A.transpose= -X) ∧
      (∀ X : M n, X.PosSemidef → (L X).PosSemidef) ∧ (∀ X : M n, X.PosDef → (L X).PosDef) := by
  have hker : Function.Injective (op A) := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro P h
    change -(A*P+P*A.transpose)=0 at h
    have he : A*P+P*A.transpose= -(0 : M n) := by simpa only [neg_neg] using congrArg Neg.neg h
    have hp := lyap_psd ht hd Matrix.PosSemidef.zero he
    have hm : (-P).PosSemidef := by
      apply lyap_psd (X:=0) ht hd Matrix.PosSemidef.zero
      calc
        _ = -(A*P+P*A.transpose) := by simp only [mul_neg,neg_mul]; abel
        _ = _ := by rw [he]; simp
    exact le_antisymm (neg_nonneg.mp hm.nonneg) hp.nonneg
  let e := LinearEquiv.ofInjectiveEndo (op A) hker
  let L := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have he (X : M n) : A*(L X)+(L X)*A.transpose= -X := by
    have h := e.apply_symm_apply X
    change -(A*(L X)+(L X)*A.transpose)=X at h
    simpa only [neg_neg] using congrArg Neg.neg h
  exact ⟨L,he,fun X h => lyap_psd ht hd h (he X),fun X h => lyap_pd hn ht hd h (he X)⟩

end MO309804
namespace MO309804Domain

open Matrix Set
open scoped Matrix.Norms.Elementwise

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def density (n : ℕ) : Set (Mat n) :=
  {X | X.PosSemidef ∧ X.trace = 1} ∩ Metric.closedBall 0 1

private lemma closed_psd (n : ℕ) : IsClosed {X : Mat n | X.PosSemidef} := by
  have h : {X : Mat n | X.PosSemidef} =
      {X | X.conjTranspose = X} ∩
        ⋂ v : Fin n → ℝ, {X : Mat n | 0 ≤ star v ⬝ᵥ (X *ᵥ v)} := by
    ext X
    simp [Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian]
  rw [h]
  apply IsClosed.inter
  · apply isClosed_eq _ continuous_id
    apply continuous_matrix
    intro i j
    simp [Matrix.conjTranspose_apply]
    fun_prop
  · apply isClosed_iInter
    intro v
    apply isClosed_le continuous_const
    simp only [dotProduct, Matrix.mulVec]
    fun_prop

private lemma compact_density (n : ℕ) : IsCompact (density n) := by
  exact (isCompact_closedBall (0 : Mat n) 1).of_isClosed_subset
    (((closed_psd n).inter (isClosed_eq (by unfold Matrix.trace; fun_prop) continuous_const)).inter
      Metric.isClosed_closedBall) inter_subset_right

private lemma convex_density (n : ℕ) : Convex ℝ (density n) := by
  apply Convex.inter _ (convex_closedBall _ _)
  intro X hX Y hY a b ha hb hab
  exact ⟨(hX.1.smul ha).add (hY.1.smul hb), by
    simp [Matrix.trace_add, Matrix.trace_smul, hX.2, hY.2, hab]⟩

private lemma pure_mem {n : ℕ} (v : Fin n → ℝ) (hv : v ⬝ᵥ v = 1) :
    Matrix.vecMulVec v v ∈ density n := by
  refine ⟨⟨by simpa using Matrix.posSemidef_vecMulVec_self_star v,
    by rwa [Matrix.trace_vecMulVec]⟩, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, Matrix.norm_le_iff (by norm_num : (0:ℝ) ≤ 1)]
  have hi (i : Fin n) : |v i| ≤ 1 := by
    have h := Finset.single_le_sum (f := fun j => v j * v j)
      (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)
    change _ ≤ v ⬝ᵥ v at h
    rw [hv] at h
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  intro i j
  simpa [Matrix.vecMulVec_apply, Real.norm_eq_abs, abs_mul] using
    mul_le_mul (hi i) (hi j) (abs_nonneg _) (by norm_num)

theorem minimizing {n : ℕ} (hn : 0 < n) (L : Mat n →L[ℝ] Mat n) :
    ∃ X : Mat n, X.PosSemidef ∧ X.trace = 1 ∧
      ∀ v : Fin n → ℝ, v ⬝ᵥ v = 1 →
        (L X * X).trace ≤ (L X * Matrix.vecMulVec v v).trace := by
  classical
  let D := density n
  let cost (X Y : Mat n) := (L X * Y).trace
  have hc : Continuous (fun z : Mat n × Mat n => cost z.1 z.2) := by
    simp only [cost, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    fun_prop
  let B (x : D) := {Y : Mat n | Y ∈ D ∧ ∀ Z ∈ D, cost x Y ≤ cost x Z}
  have hnD : D.Nonempty := by
    let i : Fin n := ⟨0, hn⟩
    exact ⟨_, pure_mem (Pi.single i 1) (by simp)⟩
  have hg : closedGraph B := by
    have h : {p : D × Mat n | p.2 ∈ B p.1} =
        {p | p.2 ∈ D} ∩ ⋂ z ∈ D, {p : D × Mat n | cost p.1 p.2 ≤ cost p.1 z} := by
      ext p
      simp [B]
    unfold closedGraph
    rw [h]
    exact ((compact_density n).isClosed.preimage continuous_snd).inter
      (isClosed_biInter fun z _ => isClosed_le
        (hc.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
        (hc.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_const)))
  have hb (x : D) : B x ⊆ D ∧ Convex ℝ (B x) ∧ (B x).Nonempty := by
    refine ⟨fun _ hy => hy.1, ?_, ?_⟩
    · intro Y hY Z hZ a b ha hb hab
      refine ⟨convex_density n hY.1 hZ.1 ha hb hab, ?_⟩
      intro T hT
      have hy := mul_le_mul_of_nonneg_left (hY.2 T hT) ha
      have hz := mul_le_mul_of_nonneg_left (hZ.2 T hT) hb
      simp only [cost, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
        smul_eq_mul] at *
      calc
        _ ≤ a * (L x * T).trace + b * (L x * T).trace := add_le_add hy hz
        _ = _ := by rw [← add_mul, hab, one_mul]
    · obtain ⟨y, hy, h⟩ := (compact_density n).exists_isMinOn hnD
          (hc.comp (continuous_const.prodMk continuous_id)).continuousOn
      exact ⟨y, hy, fun z hz => h hz⟩
  obtain ⟨x,hx⟩ := kakutani_fixed_point D (convex_density n) (compact_density n) hnD B hg hb
  exact ⟨x, x.property.1.1, x.property.1.2, fun v hv => hx.2 _ (pure_mem v hv)⟩

end MO309804Domain
namespace MO309804Slack

open Matrix
open scoped MatrixOrder

theorem rayleigh_slack {n : ℕ} (P X : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosSemidef) (hX : X.PosSemidef) (htr : X.trace = 1)
    (hmin : ∀ v : Fin n → ℝ, v ⬝ᵥ v = 1 →
      (P * X).trace ≤ (P * Matrix.vecMulVec v v).trace) :
    ∃ t : ℝ, 0 ≤ t ∧ (P - t • 1).PosSemidef ∧ P * X = t • X := by
  classical
  let t := (P * X).trace
  have hunit (v : Fin n → ℝ) (hv : v ⬝ᵥ v = 1) : t ≤ v ⬝ᵥ (P *ᵥ v) := by
    simpa only [t, mul_vecMulVec, trace_vecMulVec, dotProduct_comm (P *ᵥ v)] using hmin v hv
  have hQ : (P - t • 1).PosSemidef := by
    apply posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨hP.1.sub (isHermitian_one.smul (by simp [IsSelfAdjoint])), ?_⟩
    intro w
    by_cases hw : w = 0
    · simp [hw]
    have hz : 0 < w ⬝ᵥ w := lt_of_le_of_ne
      (Finset.sum_nonneg fun i _ => mul_self_nonneg (w i))
      (Ne.symm (mt dotProduct_self_eq_zero.mp hw))
    let a := Real.sqrt (w ⬝ᵥ w)
    have ha : 0 < a := Real.sqrt_pos.mpr hz
    have haa : a ^ 2 = w ⬝ᵥ w := Real.sq_sqrt hz.le
    have hone : (a⁻¹ • w) ⬝ᵥ (a⁻¹ • w) = 1 := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← haa]
      field_simp
    have hb := hunit _ hone
    rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hb
    field_simp [ha.ne'] at hb
    simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
    rw [haa] at hb
    exact sub_nonneg.mpr hb
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  rw [star_eq_conjTranspose] at hB
  have ht : 0 ≤ t := by
    dsimp [t]
    rw [hB, ← Matrix.mul_assoc, trace_mul_cycle]
    exact (hP.mul_mul_conjTranspose_same B).trace_nonneg
  refine ⟨t, ht, hQ, ?_⟩
  let Q := P - t • 1
  have hzero : (Q * X).trace = 0 := by
    simp [Q, sub_mul, htr, t]
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hQ.nonneg
  change Q = _ at hC
  rw [star_eq_conjTranspose] at hC
  have hCB : C * Bᴴ = 0 := by
    apply trace_conjTranspose_mul_self_eq_zero_iff.mp
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    rw [hB, ← Matrix.mul_assoc, trace_mul_cycle, hC] at hzero
    simpa only [Matrix.mul_assoc] using hzero
  have hprod : Q * X = 0 := by
    rw [hC, hB, Matrix.mul_assoc, ← Matrix.mul_assoc C, hCB, zero_mul, mul_zero]
  simpa [Q, sub_mul, Matrix.smul_mul, sub_eq_zero] using hprod

end MO309804Slack
namespace MO309804
open Matrix
theorem positive_at_fixed {n : ℕ} {A P X : M n} {t : ℝ}
    (hp : P.PosSemidef) (hx : X.PosSemidef) (htr : X.trace = 1)
    (he : A*P+P*A.transpose = -X) (ht : 0 ≤ t)
    (hs : (P-t•1).PosSemidef) (hf : P*X=t•X) : P.PosDef := by
  have ht' : 0 < t := by
    apply lt_of_le_of_ne ht
    intro h
    subst t
    simp only [zero_smul] at hf
    have hf' : X*P=0 := by
      have h1 : star X = X := hx.isHermitian.eq
      have h2 : star P = P := hp.isHermitian.eq
      simpa only [star_mul, h1, h2, star_zero] using congrArg star hf
    have hz : (X*X).trace=0 := by
      have hh := congrArg (fun Z : M n => (Z*X).trace) he
      have hcycle : ((P*A.transpose)*X).trace=0 := by
        rw [Matrix.trace_mul_comm, ←mul_assoc, hf', zero_mul, Matrix.trace_zero]
      simpa only [add_mul, Matrix.trace_add, mul_assoc A P X, hf, mul_zero, Matrix.trace_zero,
        hcycle, add_zero, neg_mul, Matrix.trace_neg, eq_neg_iff_add_eq_zero, zero_add] using hh
    have hx0 : X=0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (by rw [hx.isHermitian.eq]; exact hz)
    simp [hx0] at htr
  simpa only [sub_add_cancel] using Matrix.PosDef.posSemidef_add hs ((Matrix.PosDef.one : (1 : M n).PosDef).smul ht')
end MO309804
namespace MO309804
open Matrix
variable {n : ℕ} {A X P : Matrix (Fin n) (Fin n) ℝ}

theorem inverse_trace (hp : P.PosDef) (he : A * P + P * A.transpose = -X) :
    (X * P⁻¹).trace = -2 * A.trace := by
  have hu := P.isUnit_iff_isUnit_det.mp hp.isUnit
  have h := congrArg (fun M => (M * P⁻¹).trace) he
  change ((A * P + P * A.transpose) * P⁻¹).trace = ((-X) * P⁻¹).trace at h
  rw [add_mul, trace_add, P.mul_nonsing_inv_cancel_right A hu,
    trace_mul_cycle P A.transpose P⁻¹, P.nonsing_inv_mul hu, one_mul,
    trace_transpose, neg_mul, trace_neg] at h
  linarith

theorem supported_objective {c : ℝ} (hp : P.PosDef) (hc : 1 + c ≠ 0)
    (hx : X.trace = 1) (hs : X * P = c • X) :
    (X * (1 + P)⁻¹).trace = 1 / (1 + c) := by
  have hpos : ((1 : Matrix (Fin n) (Fin n) ℝ) + P).PosDef :=
    Matrix.PosDef.one.add_posSemidef hp.posSemidef
  have h1 : X * (1 + P) = (1 + c) • X := by
    rw [mul_add, mul_one, hs, add_smul, one_smul]
  have h2 := congrArg (fun M => (M * (1 + P)⁻¹).trace) h1
  change (X * (1 + P) * (1 + P)⁻¹).trace = (((1 + c) • X) * (1 + P)⁻¹).trace at h2
  rw [Matrix.mul_nonsing_inv_cancel_right _ _ ((1 + P).isUnit_iff_isUnit_det.mp hpos.isUnit),
    hx, smul_mul_assoc, trace_smul, smul_eq_mul] at h2
  exact (eq_div_iff hc).mpr (by linarith)
theorem endpoint {c : ℝ} (hp : P.PosDef) (hx : X.PosSemidef)
    (htr : X.trace = 1) (hA : A.trace < 0)
    (he : A * P + P * A.transpose = -X) (hs : P * X = c • X) :
    (X * (1 + P)⁻¹).trace = 2 * A.trace / (2 * A.trace - 1) := by
  have hxt : X.transpose = X := by simpa using hx.isHermitian.eq
  have hpt : P.transpose = P := by simpa using hp.isHermitian.eq
  have hr : X * P = c • X := by
    simpa [Matrix.transpose_mul, Matrix.transpose_smul, hxt, hpt] using
      congrArg Matrix.transpose hs
  have h := congrArg (fun M => (M * P⁻¹).trace) hr
  change (X * P * P⁻¹).trace = ((c • X) * P⁻¹).trace at h
  rw [P.mul_nonsing_inv_cancel_right X (P.isUnit_iff_isUnit_det.mp hp.isUnit),
    htr, smul_mul_assoc, trace_smul, smul_eq_mul, inverse_trace hp he] at h
  have hc : 0 < c := by nlinarith [show 0 < -(2 * A.trace) by linarith]
  rw [supported_objective hp (by positivity : 1 + c ≠ 0) htr hr]
  apply (div_eq_div_iff (by positivity) (by linarith)).mpr
  nlinarith
open Filter Topology
theorem regularize {X₁ P₁ : Matrix (Fin n) (Fin n) ℝ} {S : Set ℝ}
    (hx : X.PosSemidef) (hp : P.PosDef) (hx₁ : X₁.PosDef) (hp₁ : P₁.PosDef)
    (htr : X.trace = 1) (htr₁ : X₁.trace = 1)
    (he : A * P + P * A.transpose = -X) (he₁ : A * P₁ + P₁ * A.transpose = -X₁)
    (hb : BddAbove S)
    (hS : ∀ U V : Matrix (Fin n) (Fin n) ℝ, U.PosDef → U.trace = 1 → V.PosDef →
      A * V + V * A.transpose = -U → (U * (1 + V)⁻¹).trace ∈ S) :
    (X * (1 + P)⁻¹).trace ≤ sSup S := by
  let u (t : ℝ) := (1-t) • X + t • X₁
  let v (t : ℝ) := (1-t) • P + t • P₁
  have hu : Continuous u := by dsimp [u]; fun_prop
  have hv : Continuous v := by dsimp [v]; fun_prop
  have hinv : ContinuousAt (fun Q : Matrix (Fin n) (Fin n) ℝ => Q⁻¹) (1 + P) := by
    apply continuousAt_matrix_inv
    have hq := Matrix.PosDef.one.add_posSemidef hp.posSemidef
    change ContinuousAt (fun r : ℝ => Ring.inverse r) _
    simpa only [Ring.inverse_eq_inv] using
      (continuousAt_inv₀ ((1 + P).isUnit_iff_isUnit_det.mp hq.isUnit).ne_zero)
  have hv0 : ContinuousAt (fun t => 1 + v t) (0 : ℝ) := continuousAt_const.add hv.continuousAt
  have hi : ContinuousAt (fun t => (1 + v t)⁻¹) (0 : ℝ) :=
    (show ContinuousAt (fun Q : Matrix (Fin n) (Fin n) ℝ => Q⁻¹) (1 + v 0) by simpa [v] using hinv).comp (f := fun t : ℝ => 1 + v t) hv0
  have hf : ContinuousAt (fun t => (u t * (1 + v t)⁻¹).trace) (0 : ℝ) :=
    (continuous_id.matrix_trace.continuousAt).comp (hu.continuousAt.mul hi)
  apply le_of_tendsto (show Tendsto (fun t => (u t * (1 + v t)⁻¹).trace) (𝓝[>] 0)
      (𝓝 (X * (1 + P)⁻¹).trace) by simpa [ContinuousWithinAt, u, v] using hf.continuousWithinAt (s := Set.Ioi 0))
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht₁
  have ht0 : 0 < t := ht
  have ht1 : 0 < 1 - t := sub_pos.mpr ht₁
  apply le_csSup hb
  apply hS
  · exact Matrix.PosDef.posSemidef_add (hx.smul ht1.le) (hx₁.smul ht0)
  · simp [u, Matrix.trace_add, Matrix.trace_smul, htr, htr₁]
  · exact (hp.smul ht1).add (hp₁.smul ht0)
  · dsimp [v, u]
    rw [mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc]
    rw [add_add_add_comm, ← smul_add, ← smul_add, he, he₁, smul_neg, smul_neg, neg_add]
open scoped MatrixOrder
theorem objective_le_trace (hx : X.PosSemidef) (hp : P.PosDef) :
    (X * (1 + P)⁻¹).trace ≤ X.trace := by
  have hq := Matrix.PosDef.one.add_posSemidef hp.posSemidef
  let Q := 1 + P
  have hu := Q.isUnit_iff_isUnit_det.mp hq.isUnit
  have hqpoly : Q * Q - Q = P + P ^ 2 := by dsimp [Q]; noncomm_ring
  have hpoly : (Q * Q - Q).PosSemidef := hqpoly ▸ hp.posSemidef.add (hp.posSemidef.pow 2)
  have hinv := hpoly.mul_mul_conjTranspose_same Q⁻¹
  have hh : Q⁻¹.conjTranspose = Q⁻¹ := hq.inv.isHermitian.eq
  rw [hh, mul_sub, Q.nonsing_inv_mul_cancel_left Q hu, Q.nonsing_inv_mul hu,
    sub_mul, Q.mul_nonsing_inv hu, one_mul] at hinv
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx.nonneg
  have h0 := (hinv.mul_mul_conjTranspose_same B).trace_nonneg
  rw [Matrix.trace_mul_cycle, ← Matrix.star_eq_conjTranspose, ← hB,
    mul_sub, mul_one, trace_sub] at h0
  linarith
end MO309804
namespace MO309804Sharp
open Matrix
open scoped MatrixOrder

variable {n : ℕ} {A X P : Matrix (Fin n) (Fin n) ℝ}
private abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

private theorem gap_factor (hp : P.PosDef) (c : ℝ) :
    ∃ K : Mat n, K.PosDef ∧
      (1 - c • P) * K * (1 - c • P).conjTranspose =
      c ^ 2 • (1 : Mat n) + P⁻¹ - (1 + c) ^ 2 • (1 + P)⁻¹ := by
  let Q := 1 + P
  let K := (P + P^2)⁻¹
  have hq : Q.PosDef := Matrix.PosDef.one.add_posSemidef hp.posSemidef
  have hk : K.PosDef := (hp.add_posSemidef (hp.posSemidef.pow 2)).inv
  refine ⟨K, hk, ?_⟩
  have hu := P.isUnit_iff_isUnit_det.mp hp.isUnit
  have hv := Q.isUnit_iff_isUnit_det.mp hq.isUnit
  have h1 : K = P⁻¹ * Q⁻¹ := by rw [← Matrix.mul_inv_rev]; dsimp [K, Q]; simp [add_mul, pow_two]
  have h2 : K = Q⁻¹ * P⁻¹ := by rw [← Matrix.mul_inv_rev]; dsimp [K, Q]; simp [mul_add, pow_two]
  have hpk : P * K = Q⁻¹ := by rw [h1, P.mul_nonsing_inv_cancel_left _ hu]
  have hkp : K * P = Q⁻¹ := by rw [h2, P.nonsing_inv_mul_cancel_right _ hu]
  have hkq : K * Q = P⁻¹ := by rw [h1, Q.nonsing_inv_mul_cancel_right _ hv]
  have hQP : Q⁻¹ * P = 1 - Q⁻¹ := by
    have h := Q.nonsing_inv_mul hv
    change Q⁻¹ * (1 + P) = 1 at h
    rw [mul_add, mul_one] at h
    exact eq_sub_of_add_eq' h
  have he : K = P⁻¹ - Q⁻¹ := by
    change K * (1 + P) = P⁻¹ at hkq
    rw [mul_add, mul_one, hkp] at hkq
    exact eq_sub_of_add_eq hkq
  have hr : (1 - c • P).conjTranspose = 1 - c • P := by
    have ht : P.transpose = P := by simpa using hp.isHermitian.eq
    simp [ht]
  change (1 - c • P) * K * (1 - c • P).conjTranspose =
    c ^ 2 • (1 : Mat n) + P⁻¹ - (1+c)^2 • Q⁻¹
  rw [hr, sub_mul, one_mul, smul_mul_assoc, hpk, mul_sub, mul_one, mul_smul_comm,
    sub_mul, hkp, smul_mul_assoc, hQP, he]
  module

private theorem weighted_gap (hx : X.PosDef) {K R : Mat n} (hk : K.PosDef) :
    0 ≤ (X * (R * K * R.conjTranspose)).trace ∧
    ((X * (R * K * R.conjTranspose)).trace = 0 → R = 0) := by
  obtain ⟨B, hBu, hB⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hx.isStrictlyPositive
  rw [star_eq_conjTranspose] at hB
  have htrace : (X * (R * K * R.conjTranspose)).trace =
      ((B * R) * K * (B * R).conjTranspose).trace := by
    rw [hB, Matrix.mul_assoc, Matrix.trace_mul_comm B.conjTranspose, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [htrace]
  refine ⟨(hk.posSemidef.mul_mul_conjTranspose_same _).trace_nonneg, ?_⟩
  intro hz
  obtain ⟨C, hCu, hC⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hk.isStrictlyPositive
  rw [star_eq_conjTranspose] at hC
  have h0 : C * (B * R).conjTranspose = 0 := by
    apply trace_conjTranspose_mul_self_eq_zero_iff.mp
    rw [hC] at hz
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc] using hz
  have hbr : (B * R).conjTranspose = 0 := by
    exact hCu.isRegular.left (by simpa using h0 : C * (B * R).conjTranspose = C * 0)
  have hbr' : B * R = 0 := by simpa using congrArg Matrix.conjTranspose hbr
  exact hBu.isRegular.left (by simpa using hbr' : B * R = B * 0)

theorem sharp_and_rigid (hx : X.PosDef) (hp : P.PosDef) (htr : X.trace = 1)
    (he : A * P + P * A.transpose = -X) (hA : A.trace < 0) :
    (X * (1 + P)⁻¹).trace ≤ 2 * A.trace / (2 * A.trace - 1) ∧
    ((X * (1 + P)⁻¹).trace = 2 * A.trace / (2 * A.trace - 1) →
      (-2 * A.trace) • P = 1) := by
  let c := -2 * A.trace
  let z := (X * (1 + P)⁻¹).trace
  have hc : 0 < c := by dsimp [c]; linarith
  have hden : 0 < 1 + c := by linarith
  have hid : 2 * A.trace / (2 * A.trace - 1) = c / (1 + c) := by
    apply (div_eq_div_iff (by linarith) hden.ne').mpr
    dsimp [c]; ring
  rw [hid]
  obtain ⟨K, hk, heq⟩ := gap_factor hp c
  obtain ⟨hn, hz⟩ := weighted_gap (R := 1 - c • P) hx hk
  have hgap : (X * ((1 - c • P) * K * (1 - c • P).conjTranspose)).trace =
      (1 + c) * (c - (1 + c) * z) := by
    rw [heq, mul_sub, mul_add, mul_smul_comm, mul_smul_comm, mul_one, trace_sub,
      trace_add, trace_smul, trace_smul, htr, MO309804.inverse_trace hp he]
    change c ^ 2 * 1 + c - (1 + c)^2 * z = _
    ring
  rw [hgap] at hn hz
  refine ⟨(le_div_iff₀ hden).mpr ?_, ?_⟩
  · change z * (1+c) ≤ c
    nlinarith [nonneg_of_mul_nonneg_right hn hden]
  · intro eq
    have hh : z * (1 + c) = c := (eq_div_iff hden.ne').mp eq
    exact (sub_eq_zero.mp (hz (by rw [mul_comm z] at hh; rw [hh]; ring))).symm
theorem strict_necessary (hx : X.PosDef) (hp : P.PosDef) (htr : X.trace = 1)
    (he : A * P + P * A.transpose = -X) (hA : A.trace < 0)
    (hval : (X * (1 + P)⁻¹).trace = 2 * A.trace / (2 * A.trace - 1)) :
    (-(A + A.transpose)).PosDef := by
  let c := -2 * A.trace
  have hc : 0 < c := by dsimp [c]; linarith
  have hr : c • P = 1 := (sharp_and_rigid hx hp htr he hA).2 hval
  have h := congrArg (fun M => c • M) he
  change c • (A * P + P * A.transpose) = c • (-X) at h
  rw [smul_add, ← Matrix.mul_smul, ← Matrix.smul_mul, hr, mul_one, one_mul, smul_neg] at h
  rw [h, neg_neg]
  exact hx.smul hc
end MO309804Sharp
namespace MO309804
open Matrix

theorem attains_of_symmetric_part {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (ha : A.trace < 0) (h : (-(A + A.transpose)).PosDef) :
    2 * A.trace / (2 * A.trace - 1) ∈ OMA.S_mo_309804.values A := by
  let c := (-2 * A.trace)⁻¹
  have hc : 0 < c := inv_pos.mpr (by linarith)
  let X := c • (-(A + A.transpose))
  let P := c • (1 : Matrix (Fin n) (Fin n) ℝ)
  have hx : X.PosDef := h.smul hc
  have hp : P.PosDef := Matrix.PosDef.one.smul hc
  have htr : X.trace = 1 := by
    simp only [X, trace_smul, trace_neg, trace_add, trace_transpose, smul_eq_mul, c]
    rw [show -(A.trace + A.trace) = -2 * A.trace by ring]
    exact inv_mul_cancel₀ (by nlinarith : -2 * A.trace ≠ 0)
  have he : A * P + P * A.transpose = -X := by simp [P, X, smul_add]
  have hs : P * X = c • X := by simp [P]
  exact ⟨X,P,hx,htr,hp,he,(endpoint hp hx.posSemidef htr ha he hs).symm⟩

theorem attainment_iff {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (ha : A.trace < 0) :
    (2 * A.trace / (2 * A.trace - 1) ∈ OMA.S_mo_309804.values A) ↔
    (-(A + A.transpose)).PosDef := by
  refine ⟨?_, attains_of_symmetric_part ha⟩
  rintro ⟨X,P,hx,htr,hp,he,heq⟩
  have hs := (MO309804Sharp.sharp_and_rigid hx hp htr he ha).2 heq.symm
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => (-2 * A.trace) • M) he
  change (-2 * A.trace) • (A * P + P * A.transpose) = (-2 * A.trace) • (-X) at h
  rw [smul_add, ← Matrix.mul_smul, ← smul_mul_assoc, hs, mul_one, one_mul, smul_neg] at h
  have hh : -(A + A.transpose) = (-2 * A.trace) • X := by rw [h, neg_neg]
  rw [hh]
  exact hx.smul (by linarith : 0 < -2 * A.trace)

end MO309804
theorem MO309804.optimum {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (ht : A.IsUpperTriangular) (hd : ∀ i, A i i < 0) :
    sSup (OMA.S_mo_309804.values A) = 2 * A.trace / (2 * A.trace - 1) ∧
    ((2 * A.trace / (2 * A.trace - 1) ∈ OMA.S_mo_309804.values A) ↔
      (-(A + A.transpose)).PosDef) := by
  classical
  obtain ⟨L, he, hps, hpd⟩ := MO309804.exists_solver hn A ht hd
  obtain ⟨X, hx, htr, hmin⟩ := MO309804Domain.minimizing hn L
  have hp := hps X hx
  obtain ⟨t, ht0, hlo, hs⟩ := MO309804Slack.rayleigh_slack (L X) X hp hx htr hmin
  have hp' := MO309804.positive_at_fixed hp hx htr (he X) ht0 hlo hs
  have htrace : A.trace < 0 := by
    let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Finset.sum_neg (fun i _ => hd i) Finset.univ_nonempty
  let Y : Matrix (Fin n) (Fin n) ℝ := (n : ℝ)⁻¹ • 1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hy : Y.PosDef := Matrix.PosDef.one.smul (inv_pos.mpr hnR)
  have hytr : Y.trace = 1 := by simp [Y, Matrix.trace_smul, Matrix.trace_one, hnR.ne']
  have hb : BddAbove (OMA.S_mo_309804.values A) := by
    refine ⟨1, ?_⟩
    rintro y ⟨U,V,hU,hUtr,hV,_,rfl⟩
    simpa [hUtr] using MO309804.objective_le_trace hU.posSemidef hV
  refine ⟨le_antisymm ?_ ?_, MO309804.attainment_iff htrace⟩
  · apply csSup_le (show (OMA.S_mo_309804.values A).Nonempty from
      ⟨_, Y, L Y, hy, hytr, hpd Y hy, he Y, rfl⟩)
    rintro _ ⟨U, V, hU, hut, hV, huv, rfl⟩
    exact (MO309804Sharp.sharp_and_rigid hU hV hut huv htrace).1
  · rw [← MO309804.endpoint hp' hx htr htrace (he X) hs]
    apply MO309804.regularize hx hp' hy (hpd Y hy) htr hytr (he X) (he Y) hb
    exact fun U V hU hUtr hV heq => ⟨U, V, hU, hUtr, hV, heq, rfl⟩

theorem OMA.solution : type_of% @OMA.S_mo_309804.main := by
  intro n hn A ht hd
  exact (MO309804.optimum hn A ht hd).1.ge
