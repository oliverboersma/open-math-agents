import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H3_R1
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum

/-! Normalize the exterior heavy supports and the one-secant labels. -/
-- Credit: @avivorly
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H3_R1_H2_R1

open Finset

def H1 : Prop :=
  let R := Fin 6 ⊕ (Fin 37 ⊕ Fin 68)
  let P := Fin 19 ⊕ Fin 92
  let S (M : R → P → Bool) (p : P) := univ.filter fun a : Fin 6 => M (.inl a) p = true
  let B (M : R → P → Bool) (p : P) :=
    (univ.filter fun b : Fin 37 => M (.inr (.inl b)) p = true).card
  ∀ (i : Fin 4) (M : R → P → Bool),
    (∀ l, (univ.filter fun p => M l p = true).card = 11) →
    (∀ p, (univ.filter fun l => M l p = true).card = 11) →
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) →
    (∀ p q, p ≠ q → ∃! l, M l p = true ∧ M l q = true) →
    (∀ a : Fin 6, (univ.filter fun p : Fin 19 => M (.inl a) (.inl p) = true).card = 5) →
    (∀ c : Fin 68, (univ.filter fun p : Fin 19 => M (.inr (.inr c)) (.inl p) = true).card = 1) →
    (∀ p : Fin 19, B M (.inl p) + 2*(S M (.inl p)).card = 9) →
    (∀ p : Fin 92, B M (.inr p) + 2*(S M (.inr p)).card = 4) →
    let D (p : Fin 19) := univ.filter fun a : Fin 6 =>
      ((([[7, 25, 42, 33, 18, 12, 20, 36, 48, 1, 1, 2, 2, 4, 8, 8, 16, 32, 0], [7, 25, 42, 33, 18, 20, 36, 48, 1, 1, 2, 2, 4, 4, 8, 8, 8, 16, 32], [7, 25, 42, 33, 18, 12, 36, 48, 1, 1, 2, 2, 4, 4, 8, 8, 16, 16, 32], [7, 25, 42, 52, 33, 18, 12, 1, 1, 2, 2, 4, 4, 8, 8, 16, 16, 32, 32]] : List (List Nat))[i.val]!)[p.val]!).testBit a.val
    let d : List (Fin 6) := if i = 1 then [2,3] else if i = 2 then [2,4] else []
    let E (q : Fin 92) := (((if d.isEmpty then [] else [d]) ++ (List.finRange 6).flatMap
      (fun a => List.replicate (if d.contains a then 5 else 6) [a]))[q.val]!).toFinset
    let g (c : Fin 68) := ((List.finRange 19).flatMap fun p => List.replicate ((D p).card + 2) p)[c.val]!
    (∀ p, S M (.inl p) = D p) →
    ∃ (ε : Equiv.Perm (Fin 92)) (ρ : Equiv.Perm (Fin 68)),
      (∀ q, S M (.inr (ε q)) = E q) ∧
      (∀ c p, M (.inr (.inr (ρ c))) (.inl p) = decide (g c = p))

def H2 : Prop :=
  let R := Fin 6 ⊕ (Fin 37 ⊕ Fin 68)
  let P := Fin 19 ⊕ Fin 92
  let S (M : R → P → Bool) (p : P) := univ.filter fun a : Fin 6 => M (.inl a) p = true
  let B (M : R → P → Bool) (p : P) :=
    (univ.filter fun b : Fin 37 => M (.inr (.inl b)) p = true).card
  ¬ ∃ i : Fin 4, ∃ M : R → P → Bool,
    (∀ l, (univ.filter fun p => M l p = true).card = 11) ∧
    (∀ p, (univ.filter fun l => M l p = true).card = 11) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∃! l, M l p = true ∧ M l q = true) ∧
    (∀ a : Fin 6, (univ.filter fun p : Fin 19 => M (.inl a) (.inl p) = true).card = 5) ∧
    (∀ b : Fin 37, (univ.filter fun p : Fin 19 => M (.inr (.inl b)) (.inl p) = true).card = 3) ∧
    (∀ c : Fin 68, (univ.filter fun p : Fin 19 => M (.inr (.inr c)) (.inl p) = true).card = 1) ∧
    (∀ p : Fin 19, B M (.inl p) + 2*(S M (.inl p)).card = 9) ∧
    (∀ p : Fin 92, B M (.inr p) + 2*(S M (.inr p)).card = 4) ∧
    let D (p : Fin 19) := univ.filter fun a : Fin 6 =>
      ((([[7, 25, 42, 33, 18, 12, 20, 36, 48, 1, 1, 2, 2, 4, 8, 8, 16, 32, 0], [7, 25, 42, 33, 18, 20, 36, 48, 1, 1, 2, 2, 4, 4, 8, 8, 8, 16, 32], [7, 25, 42, 33, 18, 12, 36, 48, 1, 1, 2, 2, 4, 4, 8, 8, 16, 16, 32], [7, 25, 42, 52, 33, 18, 12, 1, 1, 2, 2, 4, 4, 8, 8, 16, 16, 32, 32]] : List (List Nat))[i.val]!)[p.val]!).testBit a.val
    let d : List (Fin 6) := if i = 1 then [2,3] else if i = 2 then [2,4] else []
    let E (q : Fin 92) := (((if d.isEmpty then [] else [d]) ++ (List.finRange 6).flatMap
      (fun a => List.replicate (if d.contains a then 5 else 6) [a]))[q.val]!).toFinset
    let g (c : Fin 68) := ((List.finRange 19).flatMap fun p => List.replicate ((D p).card + 2) p)[c.val]!
    (∀ p, S M (.inl p) = D p) ∧ (∀ q, S M (.inr q) = E q) ∧
    ∀ c p, M (.inr (.inr c)) (.inl p) = decide (g c = p)

lemma card_filter_relabel {X Y : Type} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (P : Y → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x => P (e x)).card = (Finset.univ.filter P).card := by
  have mapped := Finset.filter_map (s := Finset.univ) (p := P) (f := e.toEmbedding)
  rw [Finset.map_univ_equiv] at mapped
  rw [mapped, Finset.card_map]
  rfl


lemma unique_relabel {X Y : Type} (e : X ≃ Y) (P : Y → Prop)
    (h : ∃! y, P y) : ∃! x, P (e x) := by
  obtain ⟨y,yes,only⟩ := h
  refine ⟨e.symm y,?_ ,?_⟩
  · simpa only [Equiv.apply_symm_apply] using yes
  · intro x hx
    apply e.injective
    simpa only [Equiv.apply_symm_apply] using only (e x) hx


set_option maxHeartbeats 2200000 in
lemma mask_layout_eq : ∀ i : Fin 4, ∀ p : Fin 19,
    (univ.filter fun a : Fin 6 => ((([[7, 25, 42, 33, 18, 12, 20, 36, 48, 1, 1, 2, 2, 4, 8, 8, 16, 32, 0], [7, 25, 42, 33, 18, 20, 36, 48, 1, 1, 2, 2, 4, 4, 8, 8, 8, 16, 32], [7, 25, 42, 33, 18, 12, 36, 48, 1, 1, 2, 2, 4, 4, 8, 8, 16, 16, 32], [7, 25, 42, 52, 33, 18, 12, 1, 1, 2, 2, 4, 4, 8, 8, 16, 16, 32, 32]] : List (List Nat))[i.val]!)[p.val]!).testBit a.val) =
      ((([[[0, 1, 2], [0, 3, 4], [1, 3, 5], [0, 5], [1, 4], [2, 3], [2, 4], [2, 5], [4, 5], [0], [0], [1], [1], [2], [3], [3], [4], [5], []], [[0, 1, 2], [0, 3, 4], [1, 3, 5], [0, 5], [1, 4], [2, 4], [2, 5], [4, 5], [0], [0], [1], [1], [2], [2], [3], [3], [3], [4], [5]], [[0, 1, 2], [0, 3, 4], [1, 3, 5], [0, 5], [1, 4], [2, 3], [2, 5], [4, 5], [0], [0], [1], [1], [2], [2], [3], [3], [4], [4], [5]], [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5], [0, 5], [1, 4], [2, 3], [0], [0], [1], [1], [2], [2], [3], [3], [4], [4], [5], [5]]] : List (List (List (Fin 6))))[i.val]!)[p.val]!).toFinset := by
  decide +kernel

theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H3_R1.H2 := by
  intro normalize impossible
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H3_R1.H2
  dsimp only
  rintro ⟨i,M,rows,cols,rowPairs,colPairs,five,three,one,inside,outside,supports⟩
  classical
  have insideForm (p : Fin 19) :
      (univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true) =
        univ.filter fun a : Fin 6 => ((([[7, 25, 42, 33, 18, 12, 20, 36, 48, 1, 1, 2, 2, 4, 8, 8, 16, 32, 0], [7, 25, 42, 33, 18, 20, 36, 48, 1, 1, 2, 2, 4, 4, 8, 8, 8, 16, 32], [7, 25, 42, 33, 18, 12, 36, 48, 1, 1, 2, 2, 4, 4, 8, 8, 16, 16, 32], [7, 25, 42, 52, 33, 18, 12, 1, 1, 2, 2, 4, 4, 8, 8, 16, 16, 32, 32]] : List (List Nat))[i.val]!)[p.val]!).testBit a.val :=
    (supports p).trans (mask_layout_eq i p).symm
  obtain ⟨ε,ρ,outerForm,shortForm⟩ := normalize i M rows cols rowPairs colPairs five one inside outside insideForm
  let r := Equiv.sumCongr (Equiv.refl (Fin 6))
    (Equiv.sumCongr (Equiv.refl (Fin 37)) ρ)
  let c := Equiv.sumCongr (Equiv.refl (Fin 19)) ε
  let N (l : Fin 6 ⊕ (Fin 37 ⊕ Fin 68)) (p : Fin 19 ⊕ Fin 92) := M (r l) (c p)
  apply impossible
  refine ⟨i,N,?_,?_,?_,?_,five,three,fun a => one (ρ a),inside,fun p => outside (ε p),?_⟩
  · intro l
    exact (card_filter_relabel c (fun p => M (r l) p = true)).trans (rows (r l))
  · intro p
    exact (card_filter_relabel r (fun l => M l (c p) = true)).trans (cols (c p))
  · intro l m ne
    exact unique_relabel c _ (rowPairs (r l) (r m) (fun eq => ne (r.injective eq)))
  · intro p q ne
    exact unique_relabel r _ (colPairs (c p) (c q) (fun eq => ne (c.injective eq)))
  · dsimp only
    exact ⟨insideForm,outerForm,shortForm⟩

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H3_R1_H2_R1
