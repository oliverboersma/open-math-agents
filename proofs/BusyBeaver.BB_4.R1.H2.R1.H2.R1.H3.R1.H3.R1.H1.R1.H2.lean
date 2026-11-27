import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1
import Mathlib

/-! A reader state is a tuple of states of the original readers. A configuration
is marked exactly when every component marks its projection. -/
-- Credit: @marcusbuffett
open Turing Turing.BusyBeaver

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1.H2 := by
  classical
  intro I fi F M family compatible
  choose n m x y L R S hl hr initial closed using family
  let E := Fintype.equivFin (∀ i,Fin (n i))
  let D := Fintype.equivFin (∀ i,Fin (m i))
  let left (a : Fin 2) (l : Fin (Fintype.card (∀ i,Fin (n i)))) := E (fun i => L i a (E.symm l i))
  let right (a : Fin 2) (r : Fin (Fintype.card (∀ i,Fin (m i)))) := D (fun i => R i a (D.symm r i))
  let mark (q : Fin 4) (a : Fin 2) (l : Fin (Fintype.card (∀ i,Fin (n i))))
      (r : Fin (Fintype.card (∀ i,Fin (m i)))) := decide (∀ i,S i q a (E.symm l i) (D.symm r i)=true)
  refine ⟨_,_,E x,D y,left,right,mark,?_,?_,?_,?_⟩
  · simp only [left,Equiv.symm_apply_apply,hl]
  · simp only [right,Equiv.symm_apply_apply,hr]
  · simp only [mark,Equiv.symm_apply_apply,initial,implies_true,decide_true]
  · intro q a s t l r marked
    have component : ∀ i, S i q a (L i s (E.symm l i)) (R i t (D.symm r i))=true := by
      simpa only [mark,left,right,Equiv.symm_apply_apply,decide_eq_true_eq] using marked
    have each i := closed i q a s t (E.symm l i) (D.symm r i) (component i)
    obtain ⟨p,⟨w,d⟩,move,moves⟩ := compatible q a (fun i => by
      obtain ⟨p,w,d,h,_⟩ := each i
      exact ⟨p,.write w d,h⟩)
    refine ⟨p,w,d,move,?_⟩
    have next (i : I) : (match d with
        | .left => S i p s (E.symm l i) (R i w (R i t (D.symm r i)))
        | .right => S i p t (L i w (L i s (E.symm l i))) (D.symm r i))=true := by
      obtain ⟨p',w',d',h,hnext⟩ := each i
      have e := Option.some.inj ((moves i).symm.trans h)
      cases e
      cases d <;> exact hnext
    cases d <;> simp only [mark,left,right,Equiv.symm_apply_apply,decide_eq_true_eq] <;> exact next

