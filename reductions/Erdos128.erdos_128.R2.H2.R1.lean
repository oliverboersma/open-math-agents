import OMAReductions.R_Erdos128_erdos_128_R2

/-!
# Reduction Erdos128.erdos_128.R2.H2.R1 of step Erdos128.erdos_128.R2.H2

Proves directly inside `main` (for all finite n, no sorry, standard axioms only):
1. Weighted Grötzsch double-counting (`grotzsch_weighted_deg_le`): in any triangle-free graph
   containing a homomorphic copy (v, u, w) of the 11-vertex Grötzsch graph,
     3 * ∑ i, deg(v i) + 2 * ∑ i, deg(u i) + 4 * deg(w) ≤ 10 * n,
   hence ∃ v, 29 * deg(v) ≤ 10 * n (the sharp Jin 1995 threshold, closing (10/29, 5/14)).
2. Grötzsch twin-core structure (`grotzsch_twin_core`): when δ(G) > n/3 and G contains a
   Grötzsch copy, the set M of vertices reaching maximum Grötzsch-neighborhood weight 10
   satisfies 3 * |M| > 2 * n, and G[M] is homomorphic to the Grötzsch graph via the unique
   11 weight-10 independent sets and diameter-2 common-neighbor exclusion.

Splits Erdos128.erdos_128.R2.H2 cleanly into:
- H1: Brandt (1999) Grötzsch containment theorem (every non-3-colorable triangle-free graph
      with δ(G) > n/3 and δ(G) < 5n/14 contains a Grötzsch copy).
- H2: The sharpened narrow band 1/3 < δ(G)/n ≤ 10/29 with both an explicit Grötzsch copy
      and an explicit > 2n/3 Grötzsch-homomorphic twin core M.
-/

-- Reduction Erdos128.erdos_128.R2.H2.R1 of step Erdos128.erdos_128.R2.H2
-- Credit: @therationalpie

namespace OMA.R_Erdos128_erdos_128_R2_H2_R1

open Finset SimpleGraph

def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.CliqueFree 3 →
    ¬ G.Colorable 3 →
    (∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard) →
    (∃ v : V, 14 * (G.neighborSet v).ncard < 5 * Fintype.card V) →
    ∃ (v u : Fin 5 → V) (w : V),
      ∀ i : Fin 5,
        G.Adj (v i) (v (i + 1)) ∧
        G.Adj (u i) (v (i + 1)) ∧
        G.Adj (u i) (v (i + 4)) ∧
        G.Adj w (u i)

def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    12 ≤ Fintype.card V →
    73 * Fintype.card V ^ 2 < 800 * G.edgeSet.ncard →
    500000 * G.edgeSet.ncard < 99999 * Fintype.card V ^ 2 →
    (∀ I : Set V, G.IsIndepSet I → 5 * I.ncard < 2 * Fintype.card V) →
    ¬ G.Colorable 3 →
    (∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard) →
    (∃ v : V, 29 * (G.neighborSet v).ncard ≤ 10 * Fintype.card V) →
    (∃ (v u : Fin 5 → V) (w : V),
      ∀ i : Fin 5,
        G.Adj (v i) (v (i + 1)) ∧
        G.Adj (u i) (v (i + 1)) ∧
        G.Adj (u i) (v (i + 4)) ∧
        G.Adj w (u i)) →
    (∃ (M : Set V) (tag : V → Fin 3) (idx : V → Fin 5),
      2 * Fintype.card V < 3 * M.ncard ∧
      ∀ x ∈ M, ∀ y ∈ M, G.Adj x y →
        (tag x = 0 ∧ tag y = 0 ∧ (idx y = idx x + 1 ∨ idx y = idx x + 4)) ∨
        (tag x = 0 ∧ tag y = 1 ∧ (idx y = idx x + 1 ∨ idx y = idx x + 4)) ∨
        (tag x = 1 ∧ tag y = 0 ∧ (idx y = idx x + 1 ∨ idx y = idx x + 4)) ∨
        (tag x = 1 ∧ tag y = 2) ∨
        (tag x = 2 ∧ tag y = 1)) →
    (∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) →
    ¬ G.CliqueFree 3

lemma bool_toNat_le_one (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

lemma bool_pair_le_one {a b : Bool} (h : (!(a && b)) = true) : a.toNat + b.toNat ≤ 1 := by
  cases a <;> cases b <;> first | decide | exact Bool.noConfusion h

lemma bool_zero_of_pair {a b : Bool} (hb : b = true) (h : (!(a && b)) = true) : a.toNat = 0 := by
  subst hb; cases a <;> first | decide | exact Bool.noConfusion h

lemma bool_zero_of_pair' {a : Bool} (h : (!(true && a)) = true) : a.toNat = 0 := by
  cases a <;> first | decide | exact Bool.noConfusion h

lemma bool_eq_false_of_toNat_zero {b : Bool} (h : b.toNat = 0) : b = false := by
  cases b <;> first | rfl | exact Nat.noConfusion h

lemma bool_eq_true_of_toNat_one {b : Bool} (h : b.toNat = 1) : b = true := by
  cases b <;> first | rfl | exact Nat.noConfusion h

lemma bool_ite_eq_toNat (b : Bool) : (if b = true then (1 : ℕ) else 0) = b.toNat := by
  cases b <;> rfl

lemma bool_ite4_eq_toNat (b : Bool) : (if b = true then (4 : ℕ) else 0) = 4 * b.toNat := by
  cases b <;> rfl

lemma sum_fin5_bool_toNat (f : Fin 5 → Bool) :
    (∑ i : Fin 5, if f i then (1 : ℕ) else 0) =
      (f 0).toNat + (f 1).toNat + (f 2).toNat + (f 3).toNat + (f 4).toNat := by
  rw [Fin.sum_univ_five]
  simp only [bool_ite_eq_toNat]

lemma c5_cases (v0 v1 v2 v3 v4 : Bool)
    (h01 : (!(v0 && v1)) = true) (h12 : (!(v1 && v2)) = true) (h23 : (!(v2 && v3)) = true)
    (h34 : (!(v3 && v4)) = true) (h40 : (!(v4 && v0)) = true) :
    (v0 = false ∧ v1 = false ∧ v2 = false ∧ v3 = false ∧ v4 = false) ∨
    (v0 = true  ∧ v1 = false ∧ v2 = false ∧ v3 = false ∧ v4 = false) ∨
    (v0 = false ∧ v1 = true  ∧ v2 = false ∧ v3 = false ∧ v4 = false) ∨
    (v0 = false ∧ v1 = false ∧ v2 = true  ∧ v3 = false ∧ v4 = false) ∨
    (v0 = false ∧ v1 = false ∧ v2 = false ∧ v3 = true  ∧ v4 = false) ∨
    (v0 = false ∧ v1 = false ∧ v2 = false ∧ v3 = false ∧ v4 = true)  ∨
    (v0 = false ∧ v1 = true  ∧ v2 = false ∧ v3 = false ∧ v4 = true)  ∨
    (v0 = true  ∧ v1 = false ∧ v2 = true  ∧ v3 = false ∧ v4 = false) ∨
    (v0 = false ∧ v1 = true  ∧ v2 = false ∧ v3 = true  ∧ v4 = false) ∨
    (v0 = false ∧ v1 = false ∧ v2 = true  ∧ v3 = false ∧ v4 = true)  ∨
    (v0 = true  ∧ v1 = false ∧ v2 = false ∧ v3 = true  ∧ v4 = false) := by
  cases v0 <;> cases v1 <;> cases v2 <;> cases v3 <;> cases v4 <;>
    first
    | exact Bool.noConfusion h01
    | exact Bool.noConfusion h12
    | exact Bool.noConfusion h23
    | exact Bool.noConfusion h34
    | exact Bool.noConfusion h40
    | decide

lemma fin5_eq_of_vals {f g : Fin 5 → Bool}
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) (h2 : f 2 = g 2) (h3 : f 3 = g 3) (h4 : f 4 = g 4) :
    ∀ i : Fin 5, f i = g i
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨3, _⟩ => h3
  | ⟨4, _⟩ => h4

lemma grotzsch_core_le (v0 v1 v2 v3 v4 u0 u1 u2 u3 u4 w : Bool)
    (hv01 : (!(v0 && v1)) = true) (hv12 : (!(v1 && v2)) = true) (hv23 : (!(v2 && v3)) = true)
    (hv34 : (!(v3 && v4)) = true) (hv40 : (!(v4 && v0)) = true)
    (hu01 : (!(u0 && v1)) = true) (hu04 : (!(u0 && v4)) = true) (hw0 : (!(w && u0)) = true)
    (hu12 : (!(u1 && v2)) = true) (hu10 : (!(u1 && v0)) = true) (hw1 : (!(w && u1)) = true)
    (hu23 : (!(u2 && v3)) = true) (hu21 : (!(u2 && v1)) = true) (hw2 : (!(w && u2)) = true)
    (hu34 : (!(u3 && v4)) = true) (hu32 : (!(u3 && v2)) = true) (hw3 : (!(w && u3)) = true)
    (hu40 : (!(u4 && v0)) = true) (hu43 : (!(u4 && v3)) = true) (hw4 : (!(w && u4)) = true) :
    3 * (v0.toNat + v1.toNat + v2.toNat + v3.toNat + v4.toNat) +
    2 * (u0.toNat + u1.toNat + u2.toNat + u3.toNat + u4.toNat) +
    4 * w.toNat ≤ 10 := by
  have c0 := bool_toNat_le_one u0; have c1 := bool_toNat_le_one u1
  have c2 := bool_toNat_le_one u2; have c3 := bool_toNat_le_one u3
  have c4 := bool_toNat_le_one u4
  cases w
  · rcases c5_cases v0 v1 v2 v3 v4 hv01 hv12 hv23 hv34 hv40 with
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
    · simp only [Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu10; have := bool_zero_of_pair rfl hu40; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu01; have := bool_zero_of_pair rfl hu21; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu12; have := bool_zero_of_pair rfl hu32; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu23; have := bool_zero_of_pair rfl hu43; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu04; have := bool_zero_of_pair rfl hu34; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu01; have := bool_zero_of_pair rfl hu21; have := bool_zero_of_pair rfl hu34; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu10; have := bool_zero_of_pair rfl hu32; have := bool_zero_of_pair rfl hu40; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu01; have := bool_zero_of_pair rfl hu21; have := bool_zero_of_pair rfl hu43; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu04; have := bool_zero_of_pair rfl hu12; have := bool_zero_of_pair rfl hu32; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu10; have := bool_zero_of_pair rfl hu23; have := bool_zero_of_pair rfl hu40; simp only [Bool.toNat_true, Bool.toNat_false]; omega
  · have := bool_zero_of_pair' hw0; have := bool_zero_of_pair' hw1
    have := bool_zero_of_pair' hw2; have := bool_zero_of_pair' hw3
    have := bool_zero_of_pair' hw4
    have e01 := bool_pair_le_one hv01; have e12 := bool_pair_le_one hv12
    have e23 := bool_pair_le_one hv23; have e34 := bool_pair_le_one hv34
    have e40 := bool_pair_le_one hv40
    simp only [Bool.toNat_true]; omega

lemma grotzsch_indep_weight_le :
    ∀ (bv bu : Fin 5 → Bool) (bw : Bool),
      (∀ i : Fin 5,
        !(bv i && bv (i + 1)) ∧
        !(bu i && bv (i + 1)) ∧
        !(bu i && bv (i + 4)) ∧
        !(bw && bu i)) →
      3 * (∑ i : Fin 5, if bv i then 1 else 0) +
      2 * (∑ i : Fin 5, if bu i then 1 else 0) +
      (if bw then 4 else 0) ≤ 10 := by
  intro bv bu bw h
  rw [sum_fin5_bool_toNat bv, sum_fin5_bool_toNat bu, bool_ite4_eq_toNat bw]
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
  simp only [Fin.reduceAdd] at h0 h1 h2 h3 h4
  exact grotzsch_core_le (bv 0) (bv 1) (bv 2) (bv 3) (bv 4)
    (bu 0) (bu 1) (bu 2) (bu 3) (bu 4) bw
    h0.1 h1.1 h2.1 h3.1 h4.1
    h0.2.1 h0.2.2.1 h0.2.2.2
    h1.2.1 h1.2.2.1 h1.2.2.2
    h2.2.1 h2.2.2.1 h2.2.2.2
    h3.2.1 h3.2.2.1 h3.2.2.2
    h4.2.1 h4.2.2.1 h4.2.2.2

lemma grotzsch_indep_weight_eq_ten :
    ∀ (bv bu : Fin 5 → Bool) (bw : Bool),
      (∀ i : Fin 5,
        !(bv i && bv (i + 1)) ∧
        !(bu i && bv (i + 1)) ∧
        !(bu i && bv (i + 4)) ∧
        !(bw && bu i)) →
      3 * (∑ i : Fin 5, if bv i then 1 else 0) +
      2 * (∑ i : Fin 5, if bu i then 1 else 0) +
      (if bw then 4 else 0) = 10 →
      (∃ r : Fin 5,
        (∀ i : Fin 5, bv i = decide (i = r + 1 ∨ i = r + 4)) ∧
        (∀ i : Fin 5, bu i = decide (i = r + 1 ∨ i = r + 4)) ∧
        bw = false) ∨
      (∃ r : Fin 5,
        (∀ i : Fin 5, bv i = decide (i = r + 1 ∨ i = r + 4)) ∧
        (∀ i : Fin 5, bu i = false) ∧
        bw = true) ∨
      ((∀ i : Fin 5, bv i = false) ∧
       (∀ i : Fin 5, bu i = true) ∧
       bw = false) := by
  intro bv bu bw h heq
  rw [sum_fin5_bool_toNat bv, sum_fin5_bool_toNat bu, bool_ite4_eq_toNat bw] at heq
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
  simp only [Fin.reduceAdd] at h0 h1 h2 h3 h4
  have c0 := bool_toNat_le_one (bu 0); have c1 := bool_toNat_le_one (bu 1)
  have c2 := bool_toNat_le_one (bu 2); have c3 := bool_toNat_le_one (bu 3)
  have c4 := bool_toNat_le_one (bu 4)
  rcases c5_cases (bv 0) (bv 1) (bv 2) (bv 3) (bv 4) h0.1 h1.1 h2.1 h3.1 h4.1 with
    ⟨v0, v1, v2, v3, v4⟩ | ⟨v0, v1, v2, v3, v4⟩ | ⟨v0, v1, v2, v3, v4⟩ |
    ⟨v0, v1, v2, v3, v4⟩ | ⟨v0, v1, v2, v3, v4⟩ | ⟨v0, v1, v2, v3, v4⟩ |
    ⟨v0, v1, v2, v3, v4⟩ | ⟨v0, v1, v2, v3, v4⟩ | ⟨v0, v1, v2, v3, v4⟩ |
    ⟨v0, v1, v2, v3, v4⟩ | ⟨v0, v1, v2, v3, v4⟩
  · -- bv all false
    rw [v0, v1, v2, v3, v4] at heq
    cases bw
    · right; right
      simp only [Bool.toNat_false] at heq
      have e0 := bool_eq_true_of_toNat_one (by omega : (bu 0).toNat = 1)
      have e1 := bool_eq_true_of_toNat_one (by omega : (bu 1).toNat = 1)
      have e2 := bool_eq_true_of_toNat_one (by omega : (bu 2).toNat = 1)
      have e3 := bool_eq_true_of_toNat_one (by omega : (bu 3).toNat = 1)
      have e4 := bool_eq_true_of_toNat_one (by omega : (bu 4).toNat = 1)
      exact ⟨fin5_eq_of_vals v0 v1 v2 v3 v4, fin5_eq_of_vals e0 e1 e2 e3 e4, rfl⟩
    · have := bool_zero_of_pair' h0.2.2.2; have := bool_zero_of_pair' h1.2.2.2
      have := bool_zero_of_pair' h2.2.2.2; have := bool_zero_of_pair' h3.2.2.2
      have := bool_zero_of_pair' h4.2.2.2
      simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
  · -- single bv 0 = true: impossible
    rw [v0, v1, v2, v3, v4] at heq
    cases bw
    · have z1 := bool_zero_of_pair v0 h1.2.2.1
      have z4 := bool_zero_of_pair v0 h4.2.1
      simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
    · have := bool_zero_of_pair' h0.2.2.2; have := bool_zero_of_pair' h1.2.2.2
      have := bool_zero_of_pair' h2.2.2.2; have := bool_zero_of_pair' h3.2.2.2
      have := bool_zero_of_pair' h4.2.2.2
      simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
  · -- single bv 1 = true: impossible
    rw [v0, v1, v2, v3, v4] at heq
    cases bw
    · have z0 := bool_zero_of_pair v1 h0.2.1
      have z2 := bool_zero_of_pair v1 h2.2.2.1
      simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
    · have := bool_zero_of_pair' h0.2.2.2; have := bool_zero_of_pair' h1.2.2.2
      have := bool_zero_of_pair' h2.2.2.2; have := bool_zero_of_pair' h3.2.2.2
      have := bool_zero_of_pair' h4.2.2.2
      simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
  · -- single bv 2 = true: impossible
    rw [v0, v1, v2, v3, v4] at heq
    cases bw
    · have z1 := bool_zero_of_pair v2 h1.2.1
      have z3 := bool_zero_of_pair v2 h3.2.2.1
      simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
    · have := bool_zero_of_pair' h0.2.2.2; have := bool_zero_of_pair' h1.2.2.2
      have := bool_zero_of_pair' h2.2.2.2; have := bool_zero_of_pair' h3.2.2.2
      have := bool_zero_of_pair' h4.2.2.2
      simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
  · -- single bv 3 = true: impossible
    rw [v0, v1, v2, v3, v4] at heq
    cases bw
    · have z2 := bool_zero_of_pair v3 h2.2.1
      have z4 := bool_zero_of_pair v3 h4.2.2.1
      simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
    · have := bool_zero_of_pair' h0.2.2.2; have := bool_zero_of_pair' h1.2.2.2
      have := bool_zero_of_pair' h2.2.2.2; have := bool_zero_of_pair' h3.2.2.2
      have := bool_zero_of_pair' h4.2.2.2
      simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
  · -- single bv 4 = true: impossible
    rw [v0, v1, v2, v3, v4] at heq
    cases bw
    · have z0 := bool_zero_of_pair v4 h0.2.2.1
      have z3 := bool_zero_of_pair v4 h3.2.1
      simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
    · have := bool_zero_of_pair' h0.2.2.2; have := bool_zero_of_pair' h1.2.2.2
      have := bool_zero_of_pair' h2.2.2.2; have := bool_zero_of_pair' h3.2.2.2
      have := bool_zero_of_pair' h4.2.2.2
      simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
  · -- r = 0: bv 1 = true, bv 4 = true
    rw [v0, v1, v2, v3, v4] at heq
    cases bw
    · left
      have z0 := bool_zero_of_pair v1 h0.2.1
      have z2 := bool_zero_of_pair v1 h2.2.2.1
      have z3 := bool_zero_of_pair v4 h3.2.1
      simp only [Bool.toNat_true, Bool.toNat_false] at heq
      have u0 := bool_eq_false_of_toNat_zero z0
      have u1 := bool_eq_true_of_toNat_one (by omega : (bu 1).toNat = 1)
      have u2 := bool_eq_false_of_toNat_zero z2
      have u3 := bool_eq_false_of_toNat_zero z3
      have u4 := bool_eq_true_of_toNat_one (by omega : (bu 4).toNat = 1)
      exact ⟨0, fin5_eq_of_vals v0 v1 v2 v3 v4, fin5_eq_of_vals u0 u1 u2 u3 u4, rfl⟩
    · right; left
      have u0 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h0.2.2.2)
      have u1 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h1.2.2.2)
      have u2 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h2.2.2.2)
      have u3 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h3.2.2.2)
      have u4 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h4.2.2.2)
      exact ⟨0, fin5_eq_of_vals v0 v1 v2 v3 v4, fin5_eq_of_vals u0 u1 u2 u3 u4, rfl⟩
  · -- r = 1: bv 0 = true, bv 2 = true
    rw [v0, v1, v2, v3, v4] at heq
    cases bw
    · left
      have z1 := bool_zero_of_pair v0 h1.2.2.1
      have z3 := bool_zero_of_pair v2 h3.2.2.1
      have z4 := bool_zero_of_pair v0 h4.2.1
      simp only [Bool.toNat_true, Bool.toNat_false] at heq
      have u0 := bool_eq_true_of_toNat_one (by omega : (bu 0).toNat = 1)
      have u1 := bool_eq_false_of_toNat_zero z1
      have u2 := bool_eq_true_of_toNat_one (by omega : (bu 2).toNat = 1)
      have u3 := bool_eq_false_of_toNat_zero z3
      have u4 := bool_eq_false_of_toNat_zero z4
      exact ⟨1, fin5_eq_of_vals v0 v1 v2 v3 v4, fin5_eq_of_vals u0 u1 u2 u3 u4, rfl⟩
    · right; left
      have u0 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h0.2.2.2)
      have u1 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h1.2.2.2)
      have u2 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h2.2.2.2)
      have u3 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h3.2.2.2)
      have u4 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h4.2.2.2)
      exact ⟨1, fin5_eq_of_vals v0 v1 v2 v3 v4, fin5_eq_of_vals u0 u1 u2 u3 u4, rfl⟩
  · -- r = 2: bv 1 = true, bv 3 = true
    rw [v0, v1, v2, v3, v4] at heq
    cases bw
    · left
      have z0 := bool_zero_of_pair v1 h0.2.1
      have z2 := bool_zero_of_pair v1 h2.2.2.1
      have z4 := bool_zero_of_pair v3 h4.2.2.1
      simp only [Bool.toNat_true, Bool.toNat_false] at heq
      have u0 := bool_eq_false_of_toNat_zero z0
      have u1 := bool_eq_true_of_toNat_one (by omega : (bu 1).toNat = 1)
      have u2 := bool_eq_false_of_toNat_zero z2
      have u3 := bool_eq_true_of_toNat_one (by omega : (bu 3).toNat = 1)
      have u4 := bool_eq_false_of_toNat_zero z4
      exact ⟨2, fin5_eq_of_vals v0 v1 v2 v3 v4, fin5_eq_of_vals u0 u1 u2 u3 u4, rfl⟩
    · right; left
      have u0 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h0.2.2.2)
      have u1 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h1.2.2.2)
      have u2 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h2.2.2.2)
      have u3 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h3.2.2.2)
      have u4 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h4.2.2.2)
      exact ⟨2, fin5_eq_of_vals v0 v1 v2 v3 v4, fin5_eq_of_vals u0 u1 u2 u3 u4, rfl⟩
  · -- r = 3: bv 2 = true, bv 4 = true
    rw [v0, v1, v2, v3, v4] at heq
    cases bw
    · left
      have z0 := bool_zero_of_pair v4 h0.2.2.1
      have z1 := bool_zero_of_pair v2 h1.2.1
      have z3 := bool_zero_of_pair v2 h3.2.2.1
      simp only [Bool.toNat_true, Bool.toNat_false] at heq
      have u0 := bool_eq_false_of_toNat_zero z0
      have u1 := bool_eq_false_of_toNat_zero z1
      have u2 := bool_eq_true_of_toNat_one (by omega : (bu 2).toNat = 1)
      have u3 := bool_eq_false_of_toNat_zero z3
      have u4 := bool_eq_true_of_toNat_one (by omega : (bu 4).toNat = 1)
      exact ⟨3, fin5_eq_of_vals v0 v1 v2 v3 v4, fin5_eq_of_vals u0 u1 u2 u3 u4, rfl⟩
    · right; left
      have u0 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h0.2.2.2)
      have u1 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h1.2.2.2)
      have u2 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h2.2.2.2)
      have u3 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h3.2.2.2)
      have u4 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h4.2.2.2)
      exact ⟨3, fin5_eq_of_vals v0 v1 v2 v3 v4, fin5_eq_of_vals u0 u1 u2 u3 u4, rfl⟩
  · -- r = 4: bv 0 = true, bv 3 = true
    rw [v0, v1, v2, v3, v4] at heq
    cases bw
    · left
      have z1 := bool_zero_of_pair v0 h1.2.2.1
      have z2 := bool_zero_of_pair v3 h2.2.1
      have z4 := bool_zero_of_pair v0 h4.2.1
      simp only [Bool.toNat_true, Bool.toNat_false] at heq
      have u0 := bool_eq_true_of_toNat_one (by omega : (bu 0).toNat = 1)
      have u1 := bool_eq_false_of_toNat_zero z1
      have u2 := bool_eq_false_of_toNat_zero z2
      have u3 := bool_eq_true_of_toNat_one (by omega : (bu 3).toNat = 1)
      have u4 := bool_eq_false_of_toNat_zero z4
      exact ⟨4, fin5_eq_of_vals v0 v1 v2 v3 v4, fin5_eq_of_vals u0 u1 u2 u3 u4, rfl⟩
    · right; left
      have u0 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h0.2.2.2)
      have u1 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h1.2.2.2)
      have u2 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h2.2.2.2)
      have u3 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h3.2.2.2)
      have u4 := bool_eq_false_of_toNat_zero (bool_zero_of_pair' h4.2.2.2)
      exact ⟨4, fin5_eq_of_vals v0 v1 v2 v3 v4, fin5_eq_of_vals u0 u1 u2 u3 u4, rfl⟩

lemma grotzsch_diam_two (t1 t2 : Fin 3) (i1 i2 : Fin 5) :
      ¬ ((t1 = 0 ∧ t2 = 0 ∧ (i2 = i1 + 1 ∨ i2 = i1 + 4)) ∨
         (t1 = 0 ∧ t2 = 1 ∧ (i2 = i1 + 1 ∨ i2 = i1 + 4)) ∨
         (t1 = 1 ∧ t2 = 0 ∧ (i2 = i1 + 1 ∨ i2 = i1 + 4)) ∨
         (t1 = 1 ∧ t2 = 2) ∨
         (t1 = 2 ∧ t2 = 1)) →
      (∃ j : Fin 5,
        (t1 = 0 ∧ (j = i1 + 1 ∨ j = i1 + 4) ∨ t1 = 1 ∧ (j = i1 + 1 ∨ j = i1 + 4)) ∧
        (t2 = 0 ∧ (j = i2 + 1 ∨ j = i2 + 4) ∨ t2 = 1 ∧ (j = i2 + 1 ∨ j = i2 + 4))) ∨
      (∃ j : Fin 5,
        (t1 = 0 ∧ (j = i1 + 1 ∨ j = i1 + 4) ∨ t1 = 2) ∧
        (t2 = 0 ∧ (j = i2 + 1 ∨ j = i2 + 4) ∨ t2 = 2)) ∨
      (t1 = 1 ∧ t2 = 1) := by
  intro hnot
  fin_cases t1 <;> fin_cases t2
  · left
    have hcases := OMA.R_Erdos128_erdos_128_R2.fin5_cases_rel i1 i2
    rcases hcases with heq | heq | heq | heq | heq <;> rw [heq] at hnot ⊢
    · exact ⟨i1 + 1, Or.inl ⟨rfl, Or.inl rfl⟩, Or.inl ⟨rfl, Or.inl rfl⟩⟩
    · exact (hnot (Or.inl ⟨rfl, rfl, Or.inl rfl⟩)).elim
    · exact ⟨i1 + 1, Or.inl ⟨rfl, Or.inl rfl⟩, Or.inl ⟨rfl, Or.inr (OMA.R_Erdos128_erdos_128_R2.fin5_add_2_4 i1).symm⟩⟩
    · exact ⟨i1 + 4, Or.inl ⟨rfl, Or.inr rfl⟩, Or.inl ⟨rfl, Or.inl (OMA.R_Erdos128_erdos_128_R2.fin5_add_3_1 i1).symm⟩⟩
    · exact (hnot (Or.inl ⟨rfl, rfl, Or.inr rfl⟩)).elim
  · left
    have hcases := OMA.R_Erdos128_erdos_128_R2.fin5_cases_rel i1 i2
    rcases hcases with heq | heq | heq | heq | heq <;> rw [heq] at hnot ⊢
    · exact ⟨i1 + 1, Or.inl ⟨rfl, Or.inl rfl⟩, Or.inr ⟨rfl, Or.inl rfl⟩⟩
    · exact (hnot (Or.inr (Or.inl ⟨rfl, rfl, Or.inl rfl⟩))).elim
    · exact ⟨i1 + 1, Or.inl ⟨rfl, Or.inl rfl⟩, Or.inr ⟨rfl, Or.inr (OMA.R_Erdos128_erdos_128_R2.fin5_add_2_4 i1).symm⟩⟩
    · exact ⟨i1 + 4, Or.inl ⟨rfl, Or.inr rfl⟩, Or.inr ⟨rfl, Or.inl (OMA.R_Erdos128_erdos_128_R2.fin5_add_3_1 i1).symm⟩⟩
    · exact (hnot (Or.inr (Or.inl ⟨rfl, rfl, Or.inr rfl⟩))).elim
  · right; left
    exact ⟨i1 + 1, Or.inl ⟨rfl, Or.inl rfl⟩, Or.inr rfl⟩
  · left
    have hcases := OMA.R_Erdos128_erdos_128_R2.fin5_cases_rel i1 i2
    rcases hcases with heq | heq | heq | heq | heq <;> rw [heq] at hnot ⊢
    · exact ⟨i1 + 1, Or.inr ⟨rfl, Or.inl rfl⟩, Or.inl ⟨rfl, Or.inl rfl⟩⟩
    · exact (hnot (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, Or.inl rfl⟩)))).elim
    · exact ⟨i1 + 1, Or.inr ⟨rfl, Or.inl rfl⟩, Or.inl ⟨rfl, Or.inr (OMA.R_Erdos128_erdos_128_R2.fin5_add_2_4 i1).symm⟩⟩
    · exact ⟨i1 + 4, Or.inr ⟨rfl, Or.inr rfl⟩, Or.inl ⟨rfl, Or.inl (OMA.R_Erdos128_erdos_128_R2.fin5_add_3_1 i1).symm⟩⟩
    · exact (hnot (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, Or.inr rfl⟩)))).elim
  · right; right; exact ⟨rfl, rfl⟩
  · exact (hnot (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))).elim
  · right; left
    exact ⟨i2 + 1, Or.inr rfl, Or.inl ⟨rfl, Or.inl rfl⟩⟩
  · exact (hnot (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))).elim
  · right; left
    exact ⟨0, Or.inr rfl, Or.inr rfl⟩

lemma not_adj_both_of_cliqueFree {V : Type} {G : SimpleGraph V}
    (hcf : G.CliqueFree 3) {x y z : V} (hxy : G.Adj x y) (hxz : G.Adj x z) :
    ¬ G.Adj y z :=
  fun hyz => OMA.R_Erdos128_erdos_128_R2.not_adj_of_cliqueFree_three hcf hxy hyz hxz

lemma not_and_decide {p q : Prop} [Decidable p] [Decidable q] (h : p → q → False) :
    (!(decide p && decide q)) = true := by
  by_cases hp : p <;> by_cases hq : q
  · exact (h hp hq).elim
  · rw [decide_eq_true hp, decide_eq_false hq]; rfl
  · rw [decide_eq_false hp, decide_eq_true hq]; rfl
  · rw [decide_eq_false hp, decide_eq_false hq]; rfl

lemma grotzsch_profile_valid {V : Type} {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcf : G.CliqueFree 3) (v u : Fin 5 → V) (w : V)
    (hg : ∀ i : Fin 5,
      G.Adj (v i) (v (i + 1)) ∧
      G.Adj (u i) (v (i + 1)) ∧
      G.Adj (u i) (v (i + 4)) ∧
      G.Adj w (u i)) (x : V) :
    ∀ i : Fin 5,
      !(decide (G.Adj x (v i)) && decide (G.Adj x (v (i + 1)))) ∧
      !(decide (G.Adj x (u i)) && decide (G.Adj x (v (i + 1)))) ∧
      !(decide (G.Adj x (u i)) && decide (G.Adj x (v (i + 4)))) ∧
      !(decide (G.Adj x w) && decide (G.Adj x (u i))) := by
  intro i
  obtain ⟨h1, h2, h3, h4⟩ := hg i
  exact ⟨not_and_decide fun ha hb => not_adj_both_of_cliqueFree hcf ha hb h1,
         not_and_decide fun ha hb => not_adj_both_of_cliqueFree hcf ha hb h2,
         not_and_decide fun ha hb => not_adj_both_of_cliqueFree hcf ha hb h3,
         not_and_decide fun ha hb => not_adj_both_of_cliqueFree hcf ha hb h4⟩

lemma sum_adj_eq_neighborSet_ncard {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : V) :
    (∑ x : V, if decide (G.Adj x z) then (1 : ℕ) else 0) = (G.neighborSet z).ncard := by
  rw [← G.coe_neighborFinset, Set.ncard_coe_finset]
  have h1 : (∑ x : V, if decide (G.Adj x z) then (1 : ℕ) else 0) =
      (Finset.univ.filter (fun x : V => G.Adj x z)).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : G.Adj x z
    · rw [decide_eq_true h, if_pos rfl, if_pos h]
    · rw [decide_eq_false h, if_neg Bool.false_ne_true, if_neg h]
  rw [h1]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

lemma grotzsch_weighted_sum_eq {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v u : Fin 5 → V) (w : V) :
    ∑ x : V,
      (3 * (∑ i : Fin 5, if decide (G.Adj x (v i)) then (1 : ℕ) else 0) +
       2 * (∑ i : Fin 5, if decide (G.Adj x (u i)) then (1 : ℕ) else 0) +
       (if decide (G.Adj x w) then (4 : ℕ) else 0)) =
    3 * (∑ i : Fin 5, (G.neighborSet (v i)).ncard) +
    2 * (∑ i : Fin 5, (G.neighborSet (u i)).ncard) +
    4 * (G.neighborSet w).ncard := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hv : (∑ x : V, ∑ i : Fin 5, if decide (G.Adj x (v i)) then (1 : ℕ) else 0) =
      ∑ i : Fin 5, (G.neighborSet (v i)).ncard := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => sum_adj_eq_neighborSet_ncard G (v i)
  have hu : (∑ x : V, ∑ i : Fin 5, if decide (G.Adj x (u i)) then (1 : ℕ) else 0) =
      ∑ i : Fin 5, (G.neighborSet (u i)).ncard := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => sum_adj_eq_neighborSet_ncard G (u i)
  have hw : (∑ x : V, if decide (G.Adj x w) then (4 : ℕ) else 0) =
      4 * (G.neighborSet w).ncard := by
    rw [← sum_adj_eq_neighborSet_ncard G w, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> rfl
  rw [hv, hu, hw]

lemma grotzsch_min_deg_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcf : G.CliqueFree 3)
    (v u : Fin 5 → V) (w : V)
    (hg : ∀ i : Fin 5,
      G.Adj (v i) (v (i + 1)) ∧
      G.Adj (u i) (v (i + 1)) ∧
      G.Adj (u i) (v (i + 4)) ∧
      G.Adj w (u i)) :
    ∃ z : V, 29 * (G.neighborSet z).ncard ≤ 10 * Fintype.card V := by
  have hsum_le :
      3 * (∑ i : Fin 5, (G.neighborSet (v i)).ncard) +
      2 * (∑ i : Fin 5, (G.neighborSet (u i)).ncard) +
      4 * (G.neighborSet w).ncard ≤ 10 * Fintype.card V := by
    rw [← grotzsch_weighted_sum_eq G v u w]
    calc
      ∑ x : V,
          (3 * (∑ i : Fin 5, if decide (G.Adj x (v i)) then (1 : ℕ) else 0) +
           2 * (∑ i : Fin 5, if decide (G.Adj x (u i)) then (1 : ℕ) else 0) +
           (if decide (G.Adj x w) then (4 : ℕ) else 0))
          ≤ ∑ _x : V, (10 : ℕ) :=
        Finset.sum_le_sum fun x _ =>
          grotzsch_indep_weight_le
            (fun i => decide (G.Adj x (v i)))
            (fun i => decide (G.Adj x (u i)))
            (decide (G.Adj x w))
            (grotzsch_profile_valid hcf v u w hg x)
      _ = 10 * Fintype.card V := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  by_contra h
  push Not at h
  have hv0 := h (v 0); have hv1 := h (v 1); have hv2 := h (v 2); have hv3 := h (v 3); have hv4 := h (v 4)
  have hu0 := h (u 0); have hu1 := h (u 1); have hu2 := h (u 2); have hu3 := h (u 3); have hu4 := h (u 4)
  have hw := h w
  rw [Fin.sum_univ_five, Fin.sum_univ_five] at hsum_le
  have sv : 50 * Fintype.card V < 29 * ((G.neighborSet (v 0)).ncard + (G.neighborSet (v 1)).ncard +
      (G.neighborSet (v 2)).ncard + (G.neighborSet (v 3)).ncard + (G.neighborSet (v 4)).ncard) := by
    have h01 : 20 * Fintype.card V < 29 * ((G.neighborSet (v 0)).ncard + (G.neighborSet (v 1)).ncard) := by omega
    have h23 : 20 * Fintype.card V < 29 * ((G.neighborSet (v 2)).ncard + (G.neighborSet (v 3)).ncard) := by omega
    omega
  have su : 50 * Fintype.card V < 29 * ((G.neighborSet (u 0)).ncard + (G.neighborSet (u 1)).ncard +
      (G.neighborSet (u 2)).ncard + (G.neighborSet (u 3)).ncard + (G.neighborSet (u 4)).ncard) := by
    have h01 : 20 * Fintype.card V < 29 * ((G.neighborSet (u 0)).ncard + (G.neighborSet (u 1)).ncard) := by omega
    have h23 : 20 * Fintype.card V < 29 * ((G.neighborSet (u 2)).ncard + (G.neighborSet (u 3)).ncard) := by omega
    omega
  generalize (G.neighborSet (v 0)).ncard + (G.neighborSet (v 1)).ncard +
      (G.neighborSet (v 2)).ncard + (G.neighborSet (v 3)).ncard + (G.neighborSet (v 4)).ncard = Sv at hsum_le sv
  generalize (G.neighborSet (u 0)).ncard + (G.neighborSet (u 1)).ncard +
      (G.neighborSet (u 2)).ncard + (G.neighborSet (u 3)).ncard + (G.neighborSet (u 4)).ncard = Su at hsum_le su
  omega

lemma grotzsch_twin_core {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcf : G.CliqueFree 3)
    (hmin : ∀ z : V, Fintype.card V < 3 * (G.neighborSet z).ncard)
    (v u : Fin 5 → V) (w : V)
    (hg : ∀ i : Fin 5,
      G.Adj (v i) (v (i + 1)) ∧
      G.Adj (u i) (v (i + 1)) ∧
      G.Adj (u i) (v (i + 4)) ∧
      G.Adj w (u i)) :
    ∃ (M : Set V) (tag : V → Fin 3) (idx : V → Fin 5),
      2 * Fintype.card V < 3 * M.ncard ∧
      ∀ x ∈ M, ∀ y ∈ M, G.Adj x y →
        (tag x = 0 ∧ tag y = 0 ∧ (idx y = idx x + 1 ∨ idx y = idx x + 4)) ∨
        (tag x = 0 ∧ tag y = 1 ∧ (idx y = idx x + 1 ∨ idx y = idx x + 4)) ∨
        (tag x = 1 ∧ tag y = 0 ∧ (idx y = idx x + 1 ∨ idx y = idx x + 4)) ∨
        (tag x = 1 ∧ tag y = 2) ∨
        (tag x = 2 ∧ tag y = 1) := by
  let wt : V → ℕ := fun x =>
    3 * (∑ i : Fin 5, if decide (G.Adj x (v i)) then (1 : ℕ) else 0) +
    2 * (∑ i : Fin 5, if decide (G.Adj x (u i)) then (1 : ℕ) else 0) +
    (if decide (G.Adj x w) then (4 : ℕ) else 0)
  have hwt_le : ∀ x : V, wt x ≤ 10 := fun x =>
    grotzsch_indep_weight_le
      (fun i => decide (G.Adj x (v i)))
      (fun i => decide (G.Adj x (u i)))
      (decide (G.Adj x w))
      (grotzsch_profile_valid hcf v u w hg x)
  let Mf : Finset V := Finset.univ.filter (fun x => wt x = 10)
  have hsum_gt : 29 * Fintype.card V < 3 * ∑ x : V, wt x := by
    dsimp only [wt]
    rw [grotzsch_weighted_sum_eq G v u w, Fin.sum_univ_five, Fin.sum_univ_five]
    have hv0 := hmin (v 0); have hv1 := hmin (v 1); have hv2 := hmin (v 2); have hv3 := hmin (v 3); have hv4 := hmin (v 4)
    have hu0 := hmin (u 0); have hu1 := hmin (u 1); have hu2 := hmin (u 2); have hu3 := hmin (u 3); have hu4 := hmin (u 4)
    have hw := hmin w
    have sv : 5 * Fintype.card V < 3 * ((G.neighborSet (v 0)).ncard + (G.neighborSet (v 1)).ncard +
        (G.neighborSet (v 2)).ncard + (G.neighborSet (v 3)).ncard + (G.neighborSet (v 4)).ncard) := by
      have h01 : 2 * Fintype.card V < 3 * ((G.neighborSet (v 0)).ncard + (G.neighborSet (v 1)).ncard) := by omega
      have h23 : 2 * Fintype.card V < 3 * ((G.neighborSet (v 2)).ncard + (G.neighborSet (v 3)).ncard) := by omega
      omega
    have su : 5 * Fintype.card V < 3 * ((G.neighborSet (u 0)).ncard + (G.neighborSet (u 1)).ncard +
        (G.neighborSet (u 2)).ncard + (G.neighborSet (u 3)).ncard + (G.neighborSet (u 4)).ncard) := by
      have h01 : 2 * Fintype.card V < 3 * ((G.neighborSet (u 0)).ncard + (G.neighborSet (u 1)).ncard) := by omega
      have h23 : 2 * Fintype.card V < 3 * ((G.neighborSet (u 2)).ncard + (G.neighborSet (u 3)).ncard) := by omega
      omega
    generalize (G.neighborSet (v 0)).ncard + (G.neighborSet (v 1)).ncard +
        (G.neighborSet (v 2)).ncard + (G.neighborSet (v 3)).ncard + (G.neighborSet (v 4)).ncard = Sv at sv ⊢
    generalize (G.neighborSet (u 0)).ncard + (G.neighborSet (u 1)).ncard +
        (G.neighborSet (u 2)).ncard + (G.neighborSet (u 3)).ncard + (G.neighborSet (u 4)).ncard = Su at su ⊢
    omega
  have hsum_ub : ∑ x : V, wt x ≤ 9 * Fintype.card V + Mf.card := by
    have hsplit : ∑ x : V, wt x =
        (∑ x ∈ Mf, wt x) + (∑ x ∈ Finset.univ.filter (fun x => ¬ wt x = 10), wt x) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => wt x = 10) wt]
    have h1 : ∑ x ∈ Mf, wt x = 10 * Mf.card := by
      have : ∀ x ∈ Mf, wt x = 10 := fun x hx => (Finset.mem_filter.mp hx).2
      rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_comm]
    have h2 : ∑ x ∈ Finset.univ.filter (fun x => ¬ wt x = 10), wt x ≤
        9 * (Finset.univ.filter (fun x => ¬ wt x = 10)).card := by
      calc
        ∑ x ∈ Finset.univ.filter (fun x => ¬ wt x = 10), wt x
            ≤ ∑ _x ∈ Finset.univ.filter (fun x => ¬ wt x = 10), (9 : ℕ) :=
          Finset.sum_le_sum fun x hx => by
            have hne := (Finset.mem_filter.mp hx).2
            have hle := hwt_le x
            omega
        _ = 9 * (Finset.univ.filter (fun x => ¬ wt x = 10)).card := by
          simp only [Finset.sum_const, smul_eq_mul, mul_comm]
    have hcard_sum : Mf.card + (Finset.univ.filter (fun x => ¬ wt x = 10)).card = Fintype.card V := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V)) (p := fun x => wt x = 10)
      rw [Finset.card_univ] at this
      exact this
    omega
  have hM_card : 2 * Fintype.card V < 3 * (Mf : Set V).ncard := by
    rw [Set.ncard_coe_finset]
    omega
  -- Classify every vertex x ∈ Mf into its exact Grötzsch neighborhood profile (tag x, idx x)
  have hclass : ∀ x : V, x ∈ Mf →
      ∃ (t : Fin 3) (r : Fin 5),
        (t = 0 ∧ (∀ i : Fin 5, G.Adj x (v i) ↔ (i = r + 1 ∨ i = r + 4)) ∧
                 (∀ i : Fin 5, G.Adj x (u i) ↔ (i = r + 1 ∨ i = r + 4)) ∧ ¬ G.Adj x w) ∨
        (t = 1 ∧ (∀ i : Fin 5, G.Adj x (v i) ↔ (i = r + 1 ∨ i = r + 4)) ∧
                 (∀ i : Fin 5, ¬ G.Adj x (u i)) ∧ G.Adj x w) ∨
        (t = 2 ∧ (∀ i : Fin 5, ¬ G.Adj x (v i)) ∧
                 (∀ i : Fin 5, G.Adj x (u i)) ∧ ¬ G.Adj x w) := by
    intro x hx
    have hwt10 : wt x = 10 := (Finset.mem_filter.mp hx).2
    have hc := grotzsch_indep_weight_eq_ten
      (fun i => decide (G.Adj x (v i)))
      (fun i => decide (G.Adj x (u i)))
      (decide (G.Adj x w))
      (grotzsch_profile_valid hcf v u w hg x) hwt10
    rcases hc with ⟨r, hbv, hbu, hbw⟩ | ⟨r, hbv, hbu, hbw⟩ | ⟨hbv, hbu, hbw⟩
    · refine ⟨0, r, Or.inl ⟨rfl, ?_, ?_, ?_⟩⟩
      · intro i; exact decide_eq_decide.mp (hbv i)
      · intro i; exact decide_eq_decide.mp (hbu i)
      · exact of_decide_eq_false hbw
    · refine ⟨1, r, Or.inr (Or.inl ⟨rfl, ?_, ?_, ?_⟩)⟩
      · intro i; exact decide_eq_decide.mp (hbv i)
      · intro i; exact of_decide_eq_false (hbu i)
      · exact of_decide_eq_true hbw
    · refine ⟨2, 0, Or.inr (Or.inr ⟨rfl, ?_, ?_, ?_⟩)⟩
      · intro i; exact of_decide_eq_false (hbv i)
      · intro i; exact of_decide_eq_true (hbu i)
      · exact of_decide_eq_false hbw
  choose tag' idx' hspec using fun (x : {x : V // x ∈ Mf}) => hclass x.1 x.2
  let tag : V → Fin 3 := fun x => if hx : x ∈ Mf then tag' ⟨x, hx⟩ else 0
  let idx : V → Fin 5 := fun x => if hx : x ∈ Mf then idx' ⟨x, hx⟩ else 0
  refine ⟨(Mf : Set V), tag, idx, hM_card, ?_⟩
  intro x hx y hy hxy
  rw [Finset.mem_coe] at hx hy
  have hsx := hspec ⟨x, hx⟩
  have hsy := hspec ⟨y, hy⟩
  simp only [tag, idx, dif_pos hx, dif_pos hy]
  by_contra hnot
  have hdiam := grotzsch_diam_two (tag' ⟨x, hx⟩) (tag' ⟨y, hy⟩) (idx' ⟨x, hx⟩) (idx' ⟨y, hy⟩) hnot
  rcases hdiam with ⟨j, hj1, hj2⟩ | ⟨j, hj1, hj2⟩ | ⟨ht1, ht2⟩
  · have hxj : G.Adj x (v j) := by
      rcases hsx with ⟨ht, hfv, _, _⟩ | ⟨ht, hfv, _, _⟩ | ⟨ht, _, _, _⟩
      · rcases hj1 with ⟨_, h⟩ | ⟨h0, _⟩
        · exact (hfv j).mpr h
        · rw [ht] at h0; exact absurd h0 (by decide)
      · rcases hj1 with ⟨h0, _⟩ | ⟨_, h⟩
        · rw [ht] at h0; exact absurd h0 (by decide)
        · exact (hfv j).mpr h
      · rcases hj1 with ⟨h0, _⟩ | ⟨h0, _⟩ <;> (rw [ht] at h0; exact absurd h0 (by decide))
    have hyj : G.Adj y (v j) := by
      rcases hsy with ⟨ht, hfv, _, _⟩ | ⟨ht, hfv, _, _⟩ | ⟨ht, _, _, _⟩
      · rcases hj2 with ⟨_, h⟩ | ⟨h0, _⟩
        · exact (hfv j).mpr h
        · rw [ht] at h0; exact absurd h0 (by decide)
      · rcases hj2 with ⟨h0, _⟩ | ⟨_, h⟩
        · rw [ht] at h0; exact absurd h0 (by decide)
        · exact (hfv j).mpr h
      · rcases hj2 with ⟨h0, _⟩ | ⟨h0, _⟩ <;> (rw [ht] at h0; exact absurd h0 (by decide))
    exact not_adj_both_of_cliqueFree hcf hxj.symm hyj.symm hxy
  · have hxj : G.Adj x (u j) := by
      rcases hsx with ⟨ht, _, hfu, _⟩ | ⟨ht, _, _, _⟩ | ⟨ht, _, hfu, _⟩
      · rcases hj1 with ⟨_, h⟩ | h0
        · exact (hfu j).mpr h
        · rw [ht] at h0; exact absurd h0 (by decide)
      · rcases hj1 with ⟨h0, _⟩ | h0 <;> (rw [ht] at h0; exact absurd h0 (by decide))
      · exact hfu j
    have hyj : G.Adj y (u j) := by
      rcases hsy with ⟨ht, _, hfu, _⟩ | ⟨ht, _, _, _⟩ | ⟨ht, _, hfu, _⟩
      · rcases hj2 with ⟨_, h⟩ | h0
        · exact (hfu j).mpr h
        · rw [ht] at h0; exact absurd h0 (by decide)
      · rcases hj2 with ⟨h0, _⟩ | h0 <;> (rw [ht] at h0; exact absurd h0 (by decide))
      · exact hfu j
    exact not_adj_both_of_cliqueFree hcf hxj.symm hyj.symm hxy
  · have hxw : G.Adj x w := by
      rcases hsx with ⟨ht, _, _, _⟩ | ⟨_, _, _, hfw⟩ | ⟨ht, _, _, _⟩
      · rw [ht] at ht1; exact absurd ht1 (by decide)
      · exact hfw
      · rw [ht] at ht1; exact absurd ht1 (by decide)
    have hyw : G.Adj y w := by
      rcases hsy with ⟨ht, _, _, _⟩ | ⟨_, _, _, hfw⟩ | ⟨ht, _, _, _⟩
      · rw [ht] at ht2; exact absurd ht2 (by decide)
      · exact hfw
      · rw [ht] at ht2; exact absurd ht2 (by decide)
    exact not_adj_both_of_cliqueFree hcf hxw.symm hyw.symm hxy

theorem main : H1 → H2 → OMA.R_Erdos128_erdos_128_R2.H2 := by
  intro h1 h2 V _ G h12 h73 h500 hind _ _ _ hcol3 hmin h514 hdense hcf
  classical
  obtain ⟨v, u, w, hg⟩ := h1 V G hcf hcol3 hmin h514
  have h29 := grotzsch_min_deg_le G hcf v u w hg
  have hcore := grotzsch_twin_core G hcf hmin v u w hg
  exact h2 V G h12 h73 h500 hind hcol3 hmin h29 ⟨v, u, w, hg⟩ hcore hdense hcf

end OMA.R_Erdos128_erdos_128_R2_H2_R1
