import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H3_R1_H3_R1
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum

/-! Fix the heavy exterior columns and one-secant labels. -/
-- Credit: @avivorly
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H3_R1_H3_R1_H2_R1

open Finset

def H1 : Prop :=
  let R := Fin 6 ⊕ (Fin 37 ⊕ Fin 68)
  let P := Fin 19 ⊕ Fin 92
  let A (M : R → P → Bool) (p : P) :=
    (univ.filter fun a : Fin 6 => M (.inl a) p = true).card
  let B (M : R → P → Bool) (p : P) :=
    (univ.filter fun b : Fin 37 => M (.inr (.inl b)) p = true).card
  ∀ M : R → P → Bool,
    (∀ l, (univ.filter fun p => M l p = true).card = 11) →
    (∀ p, (univ.filter fun l => M l p = true).card = 11) →
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) →
    (∀ p q, p ≠ q → ∃! l, M l p = true ∧ M l q = true) →
    (∀ a, (univ.filter fun p : Fin 19 => M (.inl a) (.inl p) = true).card = 5) →
    (∀ c, (univ.filter fun p : Fin 19 => M (.inr (.inr c)) (.inl p) = true).card = 1) →
    (∀ p, B M (.inl p) + 2*A M (.inl p) = 9) →
    (∀ p, B M (.inr p) + 2*A M (.inr p) = 4) →
    let D (p : Fin 19) := (([[0, 1, 2, 3], [0, 4, 5], [1, 4], [1, 5], [2, 4], [2, 5], [3, 4], [3, 5], [0], [0], [0], [1], [1], [2], [2], [3], [3], [4], [5]] : List (List (Fin 6)))[p.val]!).toFinset
    let E (q : Fin 92) :=
      let double := False
      let blocks := (List.finRange 6).flatMap fun a => List.replicate (if double ∧ 4 ≤ a.val then 5 else 6) [a]
      (((if double then [[4,5]] else []) ++ blocks)[q.val]!).toFinset
    let g (c : Fin 68) := ((List.finRange 19).flatMap fun p => List.replicate ((D p).card + 2) p)[c.val]!
    (∀ p, (univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true) = D p) →
    ∃ (ε : Equiv.Perm (Fin 92)) (ρ : Equiv.Perm (Fin 68)),
      (∀ q, (univ.filter fun a : Fin 6 => M (.inl a) (.inr (ε q)) = true) = E q) ∧
      (∀ c p, M (.inr (.inr (ρ c))) (.inl p) = decide (g c = p))

def H2 : Prop :=
  let R := Fin 6 ⊕ (Fin 37 ⊕ Fin 68)
  let P := Fin 19 ⊕ Fin 92
  let A (M : R → P → Bool) (p : P) :=
    (univ.filter fun a : Fin 6 => M (.inl a) p = true).card
  let B (M : R → P → Bool) (p : P) :=
    (univ.filter fun b : Fin 37 => M (.inr (.inl b)) p = true).card
  ¬ ∃ M : R → P → Bool,
    (∀ l, (univ.filter fun p => M l p = true).card = 11) ∧
    (∀ p, (univ.filter fun l => M l p = true).card = 11) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∃! l, M l p = true ∧ M l q = true) ∧
    (∀ a : Fin 6, (univ.filter fun p : Fin 19 => M (.inl a) (.inl p) = true).card = 5) ∧
    (∀ b : Fin 37, (univ.filter fun p : Fin 19 => M (.inr (.inl b)) (.inl p) = true).card = 3) ∧
    (∀ c : Fin 68, (univ.filter fun p : Fin 19 => M (.inr (.inr c)) (.inl p) = true).card = 1) ∧
    (∀ p : Fin 19, B M (.inl p) + 2*A M (.inl p) = 9) ∧
    (∀ p : Fin 92, B M (.inr p) + 2*A M (.inr p) = 4) ∧
    let D (p : Fin 19) := (([[0, 1, 2, 3], [0, 4, 5], [1, 4], [1, 5], [2, 4], [2, 5], [3, 4], [3, 5], [0], [0], [0], [1], [1], [2], [2], [3], [3], [4], [5]] : List (List (Fin 6)))[p.val]!).toFinset
    let E (q : Fin 92) :=
      let double := False
      let blocks := (List.finRange 6).flatMap fun a => List.replicate (if double ∧ 4 ≤ a.val then 5 else 6) [a]
      (((if double then [[4,5]] else []) ++ blocks)[q.val]!).toFinset
    let g (c : Fin 68) := ((List.finRange 19).flatMap fun p => List.replicate ((D p).card + 2) p)[c.val]!
    (∀ p : Fin 19, (univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true) = D p) ∧
    (∀ q : Fin 92, (univ.filter fun a : Fin 6 => M (.inl a) (.inr q) = true) = E q) ∧
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


theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H3_R1_H3_R1.H2 := by
  intro normalize impossible
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H3_R1_H3_R1.H2
  dsimp only
  rintro ⟨M,rows,cols,rowPairs,colPairs,five,three,one,inside,outside,supports⟩
  classical
  obtain ⟨ε,ρ,outerForm,shortForm⟩ := normalize M rows cols rowPairs colPairs five one inside outside supports
  let r := Equiv.sumCongr (Equiv.refl (Fin 6))
    (Equiv.sumCongr (Equiv.refl (Fin 37)) ρ)
  let c := Equiv.sumCongr (Equiv.refl (Fin 19)) ε
  let N (l : Fin 6 ⊕ (Fin 37 ⊕ Fin 68)) (p : Fin 19 ⊕ Fin 92) := M (r l) (c p)
  apply impossible
  refine ⟨N,?_,?_,?_,?_,five,three,fun a => one (ρ a),inside,fun p => outside (ε p),?_⟩
  · intro l
    exact (card_filter_relabel c (fun p => M (r l) p = true)).trans (rows (r l))
  · intro p
    exact (card_filter_relabel r (fun l => M l (c p) = true)).trans (cols (c p))
  · intro l m ne
    exact unique_relabel c _ (rowPairs (r l) (r m) (fun eq => ne (r.injective eq)))
  · intro p q ne
    exact unique_relabel r _ (colPairs (c p) (c q) (fun eq => ne (c.injective eq)))
  · dsimp only
    exact ⟨supports,outerForm,shortForm⟩

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H3_R1_H3_R1_H2_R1
