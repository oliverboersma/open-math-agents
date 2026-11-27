import OMAReductions.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1
import Mathlib

-- Step LatinSquare.oddOrderLeq9LatinSquareTransversal.R1.H2: hypothesis H2 of reduction LatinSquare.oddOrderLeq9LatinSquareTransversal.R1
-- Credit: @ivillar

/-!
Reduced Latin squares of orders 1, 3, 5 have a transversal: exhaustive kernel-checked search
over the cells in row-major order with Latin pruning.
-/
namespace F2Latin
open LatinSquare

def E3_2 (x00 x01 x02 x10 x11 x12 x20 x21 x22 a0 a1 : Fin 3) : Prop :=
  ∃ a2 : Fin 3, a2 ≠ a0 ∧ a2 ≠ a1 ∧ ![x20,x21,x22] a2 ≠ ![x00,x01,x02] a0 ∧ ![x20,x21,x22] a2 ≠ ![x10,x11,x12] a1

instance (x00 x01 x02 x10 x11 x12 x20 x21 x22 a0 a1 : Fin 3) : Decidable (E3_2 x00 x01 x02 x10 x11 x12 x20 x21 x22 a0 a1) := by
  delta E3_2; infer_instance

def E3_1 (x00 x01 x02 x10 x11 x12 x20 x21 x22 a0 : Fin 3) : Prop :=
  ∃ a1 : Fin 3, a1 ≠ a0 ∧ ![x10,x11,x12] a1 ≠ ![x00,x01,x02] a0 ∧ E3_2 x00 x01 x02 x10 x11 x12 x20 x21 x22 a0 a1

instance (x00 x01 x02 x10 x11 x12 x20 x21 x22 a0 : Fin 3) : Decidable (E3_1 x00 x01 x02 x10 x11 x12 x20 x21 x22 a0) := by
  delta E3_1; infer_instance

def E3_0 (x00 x01 x02 x10 x11 x12 x20 x21 x22 : Fin 3) : Prop :=
  ∃ a0 : Fin 3, E3_1 x00 x01 x02 x10 x11 x12 x20 x21 x22 a0

instance (x00 x01 x02 x10 x11 x12 x20 x21 x22 : Fin 3) : Decidable (E3_0 x00 x01 x02 x10 x11 x12 x20 x21 x22) := by
  delta E3_0; infer_instance

def C3_8 (x00 x01 x02 x10 x11 x12 x20 x21 : Fin 3) : Prop :=
  ∀ x22 : Fin 3, (x22 ≠ x20 ∧ x22 ≠ x21 ∧ x22 ≠ x02 ∧ x22 ≠ x12) → E3_0 x00 x01 x02 x10 x11 x12 x20 x21 x22

instance (x00 x01 x02 x10 x11 x12 x20 x21 : Fin 3) : Decidable (C3_8 x00 x01 x02 x10 x11 x12 x20 x21) := by
  delta C3_8; infer_instance

def C3_7 (x00 x01 x02 x10 x11 x12 x20 : Fin 3) : Prop :=
  ∀ x21 : Fin 3, (x21 ≠ x20 ∧ x21 ≠ x01 ∧ x21 ≠ x11) → C3_8 x00 x01 x02 x10 x11 x12 x20 x21

instance (x00 x01 x02 x10 x11 x12 x20 : Fin 3) : Decidable (C3_7 x00 x01 x02 x10 x11 x12 x20) := by
  delta C3_7; infer_instance

def C3_6 (x00 x01 x02 x10 x11 x12 : Fin 3) : Prop :=
  ∀ x20 : Fin 3, (x20 = 2) → C3_7 x00 x01 x02 x10 x11 x12 x20

instance (x00 x01 x02 x10 x11 x12 : Fin 3) : Decidable (C3_6 x00 x01 x02 x10 x11 x12) := by
  delta C3_6; infer_instance

def C3_5 (x00 x01 x02 x10 x11 : Fin 3) : Prop :=
  ∀ x12 : Fin 3, (x12 ≠ x10 ∧ x12 ≠ x11 ∧ x12 ≠ x02) → C3_6 x00 x01 x02 x10 x11 x12

instance (x00 x01 x02 x10 x11 : Fin 3) : Decidable (C3_5 x00 x01 x02 x10 x11) := by
  delta C3_5; infer_instance

def C3_4 (x00 x01 x02 x10 : Fin 3) : Prop :=
  ∀ x11 : Fin 3, (x11 ≠ x10 ∧ x11 ≠ x01) → C3_5 x00 x01 x02 x10 x11

instance (x00 x01 x02 x10 : Fin 3) : Decidable (C3_4 x00 x01 x02 x10) := by
  delta C3_4; infer_instance

def C3_3 (x00 x01 x02 : Fin 3) : Prop :=
  ∀ x10 : Fin 3, (x10 = 1) → C3_4 x00 x01 x02 x10

instance (x00 x01 x02 : Fin 3) : Decidable (C3_3 x00 x01 x02) := by
  delta C3_3; infer_instance

def C3_2 (x00 x01 : Fin 3) : Prop :=
  ∀ x02 : Fin 3, (x02 = 2) → C3_3 x00 x01 x02

instance (x00 x01 : Fin 3) : Decidable (C3_2 x00 x01) := by
  delta C3_2; infer_instance

def C3_1 (x00 : Fin 3) : Prop :=
  ∀ x01 : Fin 3, (x01 = 1) → C3_2 x00 x01

instance (x00 : Fin 3) : Decidable (C3_1 x00) := by
  delta C3_1; infer_instance

def C3_0 : Prop :=
  ∀ x00 : Fin 3, (x00 = 0) → C3_1 x00

instance : Decidable C3_0 := by
  delta C3_0; infer_instance

theorem key3 : C3_0 := by
  decide +kernel

theorem inj3 {α : Type} (f : Fin 3 → α) (h10 : f 1 ≠ f 0) (h20 : f 2 ≠ f 0) (h21 : f 2 ≠ f 1) :
    Function.Injective f := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h h10 | exact absurd h.symm h10 | exact absurd h h20 | exact absurd h.symm h20 | exact absurd h h21 | exact absurd h.symm h21

theorem case3 (L : LatinSquare 3) (hr : ∀ i, L.mat 0 i = i) (hc : ∀ i, L.mat i 0 = i) :
    ∃ σ, IsTransversal L σ := by
  have e : ∀ (i b : Fin 3), (![L.mat i 0, L.mat i 1, L.mat i 2] : Fin 3 → Fin 3) b = L.mat i b := by
    intro i b; fin_cases b <;> rfl
  obtain ⟨a0, a1, h10, g10, a2, h20, h21, g20, g21⟩ := key3
      (L.mat 0 0) (hr 0)
      (L.mat 0 1) (hr 1)
      (L.mat 0 2) (hr 2)
      (L.mat 1 0) (hc 1)
      (L.mat 1 1) ⟨(fun h => absurd (L.row_injective 1 h) (by decide)), (fun h => absurd (L.col_injective 1 (a₁ := 1) (a₂ := 0) h) (by decide))⟩
      (L.mat 1 2) ⟨(fun h => absurd (L.row_injective 1 h) (by decide)), (fun h => absurd (L.row_injective 1 h) (by decide)), (fun h => absurd (L.col_injective 2 (a₁ := 1) (a₂ := 0) h) (by decide))⟩
      (L.mat 2 0) (hc 2)
      (L.mat 2 1) ⟨(fun h => absurd (L.row_injective 2 h) (by decide)), (fun h => absurd (L.col_injective 1 (a₁ := 2) (a₂ := 0) h) (by decide)), (fun h => absurd (L.col_injective 1 (a₁ := 2) (a₂ := 1) h) (by decide))⟩
      (L.mat 2 2) ⟨(fun h => absurd (L.row_injective 2 h) (by decide)), (fun h => absurd (L.row_injective 2 h) (by decide)), (fun h => absurd (L.col_injective 2 (a₁ := 2) (a₂ := 0) h) (by decide)), (fun h => absurd (L.col_injective 2 (a₁ := 2) (a₂ := 1) h) (by decide))⟩
  simp only [e] at g10 g20 g21
  exact ⟨![a0, a1, a2], inj3 _ h10 h20 h21,
    inj3 _ g10 g20 g21⟩

def E5_4 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44 a0 a1 a2 a3 : Fin 5) : Prop :=
  ∃ a4 : Fin 5, a4 ≠ a0 ∧ a4 ≠ a1 ∧ a4 ≠ a2 ∧ a4 ≠ a3 ∧ ![x40,x41,x42,x43,x44] a4 ≠ ![x00,x01,x02,x03,x04] a0 ∧ ![x40,x41,x42,x43,x44] a4 ≠ ![x10,x11,x12,x13,x14] a1 ∧ ![x40,x41,x42,x43,x44] a4 ≠ ![x20,x21,x22,x23,x24] a2 ∧ ![x40,x41,x42,x43,x44] a4 ≠ ![x30,x31,x32,x33,x34] a3

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44 a0 a1 a2 a3 : Fin 5) : Decidable (E5_4 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44 a0 a1 a2 a3) := by
  delta E5_4; infer_instance

def E5_3 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44 a0 a1 a2 : Fin 5) : Prop :=
  ∃ a3 : Fin 5, a3 ≠ a0 ∧ a3 ≠ a1 ∧ a3 ≠ a2 ∧ ![x30,x31,x32,x33,x34] a3 ≠ ![x00,x01,x02,x03,x04] a0 ∧ ![x30,x31,x32,x33,x34] a3 ≠ ![x10,x11,x12,x13,x14] a1 ∧ ![x30,x31,x32,x33,x34] a3 ≠ ![x20,x21,x22,x23,x24] a2 ∧ E5_4 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44 a0 a1 a2 a3

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44 a0 a1 a2 : Fin 5) : Decidable (E5_3 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44 a0 a1 a2) := by
  delta E5_3; infer_instance

def E5_2 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44 a0 a1 : Fin 5) : Prop :=
  ∃ a2 : Fin 5, a2 ≠ a0 ∧ a2 ≠ a1 ∧ ![x20,x21,x22,x23,x24] a2 ≠ ![x00,x01,x02,x03,x04] a0 ∧ ![x20,x21,x22,x23,x24] a2 ≠ ![x10,x11,x12,x13,x14] a1 ∧ E5_3 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44 a0 a1 a2

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44 a0 a1 : Fin 5) : Decidable (E5_2 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44 a0 a1) := by
  delta E5_2; infer_instance

def E5_1 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44 a0 : Fin 5) : Prop :=
  ∃ a1 : Fin 5, a1 ≠ a0 ∧ ![x10,x11,x12,x13,x14] a1 ≠ ![x00,x01,x02,x03,x04] a0 ∧ E5_2 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44 a0 a1

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44 a0 : Fin 5) : Decidable (E5_1 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44 a0) := by
  delta E5_1; infer_instance

def E5_0 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44 : Fin 5) : Prop :=
  ∃ a0 : Fin 5, E5_1 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44 a0

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44 : Fin 5) : Decidable (E5_0 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44) := by
  delta E5_0; infer_instance

def C5_24 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 : Fin 5) : Prop :=
  ∀ x44 : Fin 5, (x44 ≠ x40 ∧ x44 ≠ x41 ∧ x44 ≠ x42 ∧ x44 ≠ x43 ∧ x44 ≠ x04 ∧ x44 ≠ x14 ∧ x44 ≠ x24 ∧ x44 ≠ x34) → E5_0 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 x44

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43 : Fin 5) : Decidable (C5_24 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43) := by
  delta C5_24; infer_instance

def C5_23 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 : Fin 5) : Prop :=
  ∀ x43 : Fin 5, (x43 ≠ x40 ∧ x43 ≠ x41 ∧ x43 ≠ x42 ∧ x43 ≠ x03 ∧ x43 ≠ x13 ∧ x43 ≠ x23 ∧ x43 ≠ x33) → C5_24 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 x43

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42 : Fin 5) : Decidable (C5_23 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42) := by
  delta C5_23; infer_instance

def C5_22 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 : Fin 5) : Prop :=
  ∀ x42 : Fin 5, (x42 ≠ x40 ∧ x42 ≠ x41 ∧ x42 ≠ x02 ∧ x42 ≠ x12 ∧ x42 ≠ x22 ∧ x42 ≠ x32) → C5_23 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 x42

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41 : Fin 5) : Decidable (C5_22 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41) := by
  delta C5_22; infer_instance

def C5_21 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 : Fin 5) : Prop :=
  ∀ x41 : Fin 5, (x41 ≠ x40 ∧ x41 ≠ x01 ∧ x41 ≠ x11 ∧ x41 ≠ x21 ∧ x41 ≠ x31) → C5_22 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 x41

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40 : Fin 5) : Decidable (C5_21 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40) := by
  delta C5_21; infer_instance

def C5_20 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 : Fin 5) : Prop :=
  ∀ x40 : Fin 5, (x40 = 4) → C5_21 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 x40

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34 : Fin 5) : Decidable (C5_20 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34) := by
  delta C5_20; infer_instance

def C5_19 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 : Fin 5) : Prop :=
  ∀ x34 : Fin 5, (x34 ≠ x30 ∧ x34 ≠ x31 ∧ x34 ≠ x32 ∧ x34 ≠ x33 ∧ x34 ≠ x04 ∧ x34 ≠ x14 ∧ x34 ≠ x24) → C5_20 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 x34

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33 : Fin 5) : Decidable (C5_19 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33) := by
  delta C5_19; infer_instance

def C5_18 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 : Fin 5) : Prop :=
  ∀ x33 : Fin 5, (x33 ≠ x30 ∧ x33 ≠ x31 ∧ x33 ≠ x32 ∧ x33 ≠ x03 ∧ x33 ≠ x13 ∧ x33 ≠ x23) → C5_19 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 x33

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32 : Fin 5) : Decidable (C5_18 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32) := by
  delta C5_18; infer_instance

def C5_17 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 : Fin 5) : Prop :=
  ∀ x32 : Fin 5, (x32 ≠ x30 ∧ x32 ≠ x31 ∧ x32 ≠ x02 ∧ x32 ≠ x12 ∧ x32 ≠ x22) → C5_18 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 x32

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31 : Fin 5) : Decidable (C5_17 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31) := by
  delta C5_17; infer_instance

def C5_16 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 : Fin 5) : Prop :=
  ∀ x31 : Fin 5, (x31 ≠ x30 ∧ x31 ≠ x01 ∧ x31 ≠ x11 ∧ x31 ≠ x21) → C5_17 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 x31

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30 : Fin 5) : Decidable (C5_16 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30) := by
  delta C5_16; infer_instance

def C5_15 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 : Fin 5) : Prop :=
  ∀ x30 : Fin 5, (x30 = 3) → C5_16 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 x30

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24 : Fin 5) : Decidable (C5_15 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24) := by
  delta C5_15; infer_instance

def C5_14 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 : Fin 5) : Prop :=
  ∀ x24 : Fin 5, (x24 ≠ x20 ∧ x24 ≠ x21 ∧ x24 ≠ x22 ∧ x24 ≠ x23 ∧ x24 ≠ x04 ∧ x24 ≠ x14) → C5_15 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 x24

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23 : Fin 5) : Decidable (C5_14 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23) := by
  delta C5_14; infer_instance

def C5_13 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 : Fin 5) : Prop :=
  ∀ x23 : Fin 5, (x23 ≠ x20 ∧ x23 ≠ x21 ∧ x23 ≠ x22 ∧ x23 ≠ x03 ∧ x23 ≠ x13) → C5_14 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 x23

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22 : Fin 5) : Decidable (C5_13 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22) := by
  delta C5_13; infer_instance

def C5_12 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 : Fin 5) : Prop :=
  ∀ x22 : Fin 5, (x22 ≠ x20 ∧ x22 ≠ x21 ∧ x22 ≠ x02 ∧ x22 ≠ x12) → C5_13 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 x22

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21 : Fin 5) : Decidable (C5_12 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21) := by
  delta C5_12; infer_instance

def C5_11 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 : Fin 5) : Prop :=
  ∀ x21 : Fin 5, (x21 ≠ x20 ∧ x21 ≠ x01 ∧ x21 ≠ x11) → C5_12 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 x21

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20 : Fin 5) : Decidable (C5_11 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20) := by
  delta C5_11; infer_instance

def C5_10 (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 : Fin 5) : Prop :=
  ∀ x20 : Fin 5, (x20 = 2) → C5_11 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 x20

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 x14 : Fin 5) : Decidable (C5_10 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14) := by
  delta C5_10; infer_instance

def C5_9 (x00 x01 x02 x03 x04 x10 x11 x12 x13 : Fin 5) : Prop :=
  ∀ x14 : Fin 5, (x14 ≠ x10 ∧ x14 ≠ x11 ∧ x14 ≠ x12 ∧ x14 ≠ x13 ∧ x14 ≠ x04) → C5_10 x00 x01 x02 x03 x04 x10 x11 x12 x13 x14

instance (x00 x01 x02 x03 x04 x10 x11 x12 x13 : Fin 5) : Decidable (C5_9 x00 x01 x02 x03 x04 x10 x11 x12 x13) := by
  delta C5_9; infer_instance

def C5_8 (x00 x01 x02 x03 x04 x10 x11 x12 : Fin 5) : Prop :=
  ∀ x13 : Fin 5, (x13 ≠ x10 ∧ x13 ≠ x11 ∧ x13 ≠ x12 ∧ x13 ≠ x03) → C5_9 x00 x01 x02 x03 x04 x10 x11 x12 x13

instance (x00 x01 x02 x03 x04 x10 x11 x12 : Fin 5) : Decidable (C5_8 x00 x01 x02 x03 x04 x10 x11 x12) := by
  delta C5_8; infer_instance

def C5_7 (x00 x01 x02 x03 x04 x10 x11 : Fin 5) : Prop :=
  ∀ x12 : Fin 5, (x12 ≠ x10 ∧ x12 ≠ x11 ∧ x12 ≠ x02) → C5_8 x00 x01 x02 x03 x04 x10 x11 x12

instance (x00 x01 x02 x03 x04 x10 x11 : Fin 5) : Decidable (C5_7 x00 x01 x02 x03 x04 x10 x11) := by
  delta C5_7; infer_instance

def C5_6 (x00 x01 x02 x03 x04 x10 : Fin 5) : Prop :=
  ∀ x11 : Fin 5, (x11 ≠ x10 ∧ x11 ≠ x01) → C5_7 x00 x01 x02 x03 x04 x10 x11

instance (x00 x01 x02 x03 x04 x10 : Fin 5) : Decidable (C5_6 x00 x01 x02 x03 x04 x10) := by
  delta C5_6; infer_instance

def C5_5 (x00 x01 x02 x03 x04 : Fin 5) : Prop :=
  ∀ x10 : Fin 5, (x10 = 1) → C5_6 x00 x01 x02 x03 x04 x10

instance (x00 x01 x02 x03 x04 : Fin 5) : Decidable (C5_5 x00 x01 x02 x03 x04) := by
  delta C5_5; infer_instance

def C5_4 (x00 x01 x02 x03 : Fin 5) : Prop :=
  ∀ x04 : Fin 5, (x04 = 4) → C5_5 x00 x01 x02 x03 x04

instance (x00 x01 x02 x03 : Fin 5) : Decidable (C5_4 x00 x01 x02 x03) := by
  delta C5_4; infer_instance

def C5_3 (x00 x01 x02 : Fin 5) : Prop :=
  ∀ x03 : Fin 5, (x03 = 3) → C5_4 x00 x01 x02 x03

instance (x00 x01 x02 : Fin 5) : Decidable (C5_3 x00 x01 x02) := by
  delta C5_3; infer_instance

def C5_2 (x00 x01 : Fin 5) : Prop :=
  ∀ x02 : Fin 5, (x02 = 2) → C5_3 x00 x01 x02

instance (x00 x01 : Fin 5) : Decidable (C5_2 x00 x01) := by
  delta C5_2; infer_instance

def C5_1 (x00 : Fin 5) : Prop :=
  ∀ x01 : Fin 5, (x01 = 1) → C5_2 x00 x01

instance (x00 : Fin 5) : Decidable (C5_1 x00) := by
  delta C5_1; infer_instance

def C5_0 : Prop :=
  ∀ x00 : Fin 5, (x00 = 0) → C5_1 x00

instance : Decidable C5_0 := by
  delta C5_0; infer_instance

theorem key5 : C5_0 := by
  decide +kernel

theorem inj5 {α : Type} (f : Fin 5 → α) (h10 : f 1 ≠ f 0) (h20 : f 2 ≠ f 0) (h21 : f 2 ≠ f 1) (h30 : f 3 ≠ f 0) (h31 : f 3 ≠ f 1) (h32 : f 3 ≠ f 2) (h40 : f 4 ≠ f 0) (h41 : f 4 ≠ f 1) (h42 : f 4 ≠ f 2) (h43 : f 4 ≠ f 3) :
    Function.Injective f := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h h10 | exact absurd h.symm h10 | exact absurd h h20 | exact absurd h.symm h20 | exact absurd h h21 | exact absurd h.symm h21 | exact absurd h h30 | exact absurd h.symm h30 | exact absurd h h31 | exact absurd h.symm h31 | exact absurd h h32 | exact absurd h.symm h32 | exact absurd h h40 | exact absurd h.symm h40 | exact absurd h h41 | exact absurd h.symm h41 | exact absurd h h42 | exact absurd h.symm h42 | exact absurd h h43 | exact absurd h.symm h43

theorem case5 (L : LatinSquare 5) (hr : ∀ i, L.mat 0 i = i) (hc : ∀ i, L.mat i 0 = i) :
    ∃ σ, IsTransversal L σ := by
  have e : ∀ (i b : Fin 5), (![L.mat i 0, L.mat i 1, L.mat i 2, L.mat i 3, L.mat i 4] : Fin 5 → Fin 5) b = L.mat i b := by
    intro i b; fin_cases b <;> rfl
  obtain ⟨a0, a1, h10, g10, a2, h20, h21, g20, g21, a3, h30, h31, h32, g30, g31, g32, a4, h40, h41, h42, h43, g40, g41, g42, g43⟩ := key5
      (L.mat 0 0) (hr 0)
      (L.mat 0 1) (hr 1)
      (L.mat 0 2) (hr 2)
      (L.mat 0 3) (hr 3)
      (L.mat 0 4) (hr 4)
      (L.mat 1 0) (hc 1)
      (L.mat 1 1) ⟨(fun h => absurd (L.row_injective 1 h) (by decide)), (fun h => absurd (L.col_injective 1 (a₁ := 1) (a₂ := 0) h) (by decide))⟩
      (L.mat 1 2) ⟨(fun h => absurd (L.row_injective 1 h) (by decide)), (fun h => absurd (L.row_injective 1 h) (by decide)), (fun h => absurd (L.col_injective 2 (a₁ := 1) (a₂ := 0) h) (by decide))⟩
      (L.mat 1 3) ⟨(fun h => absurd (L.row_injective 1 h) (by decide)), (fun h => absurd (L.row_injective 1 h) (by decide)), (fun h => absurd (L.row_injective 1 h) (by decide)), (fun h => absurd (L.col_injective 3 (a₁ := 1) (a₂ := 0) h) (by decide))⟩
      (L.mat 1 4) ⟨(fun h => absurd (L.row_injective 1 h) (by decide)), (fun h => absurd (L.row_injective 1 h) (by decide)), (fun h => absurd (L.row_injective 1 h) (by decide)), (fun h => absurd (L.row_injective 1 h) (by decide)), (fun h => absurd (L.col_injective 4 (a₁ := 1) (a₂ := 0) h) (by decide))⟩
      (L.mat 2 0) (hc 2)
      (L.mat 2 1) ⟨(fun h => absurd (L.row_injective 2 h) (by decide)), (fun h => absurd (L.col_injective 1 (a₁ := 2) (a₂ := 0) h) (by decide)), (fun h => absurd (L.col_injective 1 (a₁ := 2) (a₂ := 1) h) (by decide))⟩
      (L.mat 2 2) ⟨(fun h => absurd (L.row_injective 2 h) (by decide)), (fun h => absurd (L.row_injective 2 h) (by decide)), (fun h => absurd (L.col_injective 2 (a₁ := 2) (a₂ := 0) h) (by decide)), (fun h => absurd (L.col_injective 2 (a₁ := 2) (a₂ := 1) h) (by decide))⟩
      (L.mat 2 3) ⟨(fun h => absurd (L.row_injective 2 h) (by decide)), (fun h => absurd (L.row_injective 2 h) (by decide)), (fun h => absurd (L.row_injective 2 h) (by decide)), (fun h => absurd (L.col_injective 3 (a₁ := 2) (a₂ := 0) h) (by decide)), (fun h => absurd (L.col_injective 3 (a₁ := 2) (a₂ := 1) h) (by decide))⟩
      (L.mat 2 4) ⟨(fun h => absurd (L.row_injective 2 h) (by decide)), (fun h => absurd (L.row_injective 2 h) (by decide)), (fun h => absurd (L.row_injective 2 h) (by decide)), (fun h => absurd (L.row_injective 2 h) (by decide)), (fun h => absurd (L.col_injective 4 (a₁ := 2) (a₂ := 0) h) (by decide)), (fun h => absurd (L.col_injective 4 (a₁ := 2) (a₂ := 1) h) (by decide))⟩
      (L.mat 3 0) (hc 3)
      (L.mat 3 1) ⟨(fun h => absurd (L.row_injective 3 h) (by decide)), (fun h => absurd (L.col_injective 1 (a₁ := 3) (a₂ := 0) h) (by decide)), (fun h => absurd (L.col_injective 1 (a₁ := 3) (a₂ := 1) h) (by decide)), (fun h => absurd (L.col_injective 1 (a₁ := 3) (a₂ := 2) h) (by decide))⟩
      (L.mat 3 2) ⟨(fun h => absurd (L.row_injective 3 h) (by decide)), (fun h => absurd (L.row_injective 3 h) (by decide)), (fun h => absurd (L.col_injective 2 (a₁ := 3) (a₂ := 0) h) (by decide)), (fun h => absurd (L.col_injective 2 (a₁ := 3) (a₂ := 1) h) (by decide)), (fun h => absurd (L.col_injective 2 (a₁ := 3) (a₂ := 2) h) (by decide))⟩
      (L.mat 3 3) ⟨(fun h => absurd (L.row_injective 3 h) (by decide)), (fun h => absurd (L.row_injective 3 h) (by decide)), (fun h => absurd (L.row_injective 3 h) (by decide)), (fun h => absurd (L.col_injective 3 (a₁ := 3) (a₂ := 0) h) (by decide)), (fun h => absurd (L.col_injective 3 (a₁ := 3) (a₂ := 1) h) (by decide)), (fun h => absurd (L.col_injective 3 (a₁ := 3) (a₂ := 2) h) (by decide))⟩
      (L.mat 3 4) ⟨(fun h => absurd (L.row_injective 3 h) (by decide)), (fun h => absurd (L.row_injective 3 h) (by decide)), (fun h => absurd (L.row_injective 3 h) (by decide)), (fun h => absurd (L.row_injective 3 h) (by decide)), (fun h => absurd (L.col_injective 4 (a₁ := 3) (a₂ := 0) h) (by decide)), (fun h => absurd (L.col_injective 4 (a₁ := 3) (a₂ := 1) h) (by decide)), (fun h => absurd (L.col_injective 4 (a₁ := 3) (a₂ := 2) h) (by decide))⟩
      (L.mat 4 0) (hc 4)
      (L.mat 4 1) ⟨(fun h => absurd (L.row_injective 4 h) (by decide)), (fun h => absurd (L.col_injective 1 (a₁ := 4) (a₂ := 0) h) (by decide)), (fun h => absurd (L.col_injective 1 (a₁ := 4) (a₂ := 1) h) (by decide)), (fun h => absurd (L.col_injective 1 (a₁ := 4) (a₂ := 2) h) (by decide)), (fun h => absurd (L.col_injective 1 (a₁ := 4) (a₂ := 3) h) (by decide))⟩
      (L.mat 4 2) ⟨(fun h => absurd (L.row_injective 4 h) (by decide)), (fun h => absurd (L.row_injective 4 h) (by decide)), (fun h => absurd (L.col_injective 2 (a₁ := 4) (a₂ := 0) h) (by decide)), (fun h => absurd (L.col_injective 2 (a₁ := 4) (a₂ := 1) h) (by decide)), (fun h => absurd (L.col_injective 2 (a₁ := 4) (a₂ := 2) h) (by decide)), (fun h => absurd (L.col_injective 2 (a₁ := 4) (a₂ := 3) h) (by decide))⟩
      (L.mat 4 3) ⟨(fun h => absurd (L.row_injective 4 h) (by decide)), (fun h => absurd (L.row_injective 4 h) (by decide)), (fun h => absurd (L.row_injective 4 h) (by decide)), (fun h => absurd (L.col_injective 3 (a₁ := 4) (a₂ := 0) h) (by decide)), (fun h => absurd (L.col_injective 3 (a₁ := 4) (a₂ := 1) h) (by decide)), (fun h => absurd (L.col_injective 3 (a₁ := 4) (a₂ := 2) h) (by decide)), (fun h => absurd (L.col_injective 3 (a₁ := 4) (a₂ := 3) h) (by decide))⟩
      (L.mat 4 4) ⟨(fun h => absurd (L.row_injective 4 h) (by decide)), (fun h => absurd (L.row_injective 4 h) (by decide)), (fun h => absurd (L.row_injective 4 h) (by decide)), (fun h => absurd (L.row_injective 4 h) (by decide)), (fun h => absurd (L.col_injective 4 (a₁ := 4) (a₂ := 0) h) (by decide)), (fun h => absurd (L.col_injective 4 (a₁ := 4) (a₂ := 1) h) (by decide)), (fun h => absurd (L.col_injective 4 (a₁ := 4) (a₂ := 2) h) (by decide)), (fun h => absurd (L.col_injective 4 (a₁ := 4) (a₂ := 3) h) (by decide))⟩
  simp only [e] at g10 g20 g21 g30 g31 g32 g40 g41 g42 g43
  exact ⟨![a0, a1, a2, a3, a4], inj5 _ h10 h20 h21 h30 h31 h32 h40 h41 h42 h43,
    inj5 _ g10 g20 g21 g30 g31 g32 g40 g41 g42 g43⟩

theorem small : ∀ (n : ℕ) [NeZero n], n ∈ ({1,3,5} : Finset ℕ) → ∀ L : LatinSquare n,
    (∀ i, L.mat 0 i = i) → (∀ i, L.mat i 0 = i) → ∃ σ, IsTransversal L σ := by
  intro n _ hn L hr hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl
  · exact ⟨id, Function.injective_id, fun a b _ => Subsingleton.elim a b⟩
  · exact case3 L hr hc
  · exact case5 L hr hc

end F2Latin

theorem OMA.solution : OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1.H2 :=
  F2Latin.small
