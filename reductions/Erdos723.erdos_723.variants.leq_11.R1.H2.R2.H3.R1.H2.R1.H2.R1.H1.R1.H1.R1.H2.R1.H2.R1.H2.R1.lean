import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H2_R1

-- Credit: @avivorly
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H2_R1_H2_R1

open Finset
open scoped Classical

def H1 : Prop :=
  let P := Fin 111
  let R := Fin 8 ⊕ Fin 72
  let A (M : R → P → Bool) (p : P) := univ.filter fun l : Fin 8 => M (.inl l) p = true
  let B (M : R → P → Bool) (p : P) := univ.filter fun l : Fin 72 => M (.inr l) p = true
  let valid (M : R → P → Bool) (S : Finset P) :=
    S.card = 16 ∧ (∀ l, (univ.filter fun p => M l p).card = 11) ∧
    (∀ a : Fin 8, (S.filter fun p => M (.inl a) p).card = 4) ∧
    (∀ b : Fin 72, (S.filter fun p => M (.inr b) p).card = 2) ∧
    (∀ p ∈ S, (A M p).card = 2 ∧ (B M p).card = 9) ∧
    (∀ p ∉ S, 2 * (A M p).card + (B M p).card = 8) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true → M m p = true → M m q = true → l = m) ∧
    (∀ p ∉ S, (A M p).card ≤ 3) ∧ (univ.filter fun p => p ∉ S ∧ (A M p).card = 3).card = 1
  let E : List (Fin 8 × Fin 8) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]
  let C := (E.zipIdx.filter fun x => !(0x35a5807 : Nat).testBit x.2).map Prod.fst
  let word (M : R → P → Bool) (S : Finset P) (e : Equiv.Perm (Fin 8)) :=
    let G (a b : Fin 8) := decide (b ≠ a ∧ ∃ p ∉ S, M (.inl (e a)) p = true ∧ M (.inl (e b)) p = true)
    (E.zipIdx.map fun ((a,b),i) => if G a b then 2^i else 0).foldr Nat.lor 0
  let norm (M : R → P → Bool) (S : Finset P) :=
    word M S (Equiv.refl _) = 0x35a5807 ∧
    (∀ p ∉ S, (A M p).card = 3 → A M p = {2,4,7}) ∧
    ∃ (c : Fin 16 ≃ ↥S) (r : Fin 72 → Fin 16 × Fin 16) (q : P),
    (∀ i, A M (c i).val = {C[i.val]!.1, C[i.val]!.2}) ∧
    (∀ b i, M (.inr b) (c i).val = true ↔ i = (r b).1 ∨ i = (r b).2) ∧
    q ∉ S ∧ A M q = {3,5} ∧ (B M q).image r = {(0,10),(2,4),(3,13),(6,15)}
  ¬ ∃ M S, valid M S ∧ norm M S

def H2 : Prop :=
  let P := Fin 111
  let R := Fin 8 ⊕ Fin 72
  let A (M : R → P → Bool) (p : P) := univ.filter fun l : Fin 8 => M (.inl l) p = true
  let B (M : R → P → Bool) (p : P) := univ.filter fun l : Fin 72 => M (.inr l) p = true
  let valid (M : R → P → Bool) (S : Finset P) :=
    S.card = 16 ∧ (∀ l, (univ.filter fun p => M l p).card = 11) ∧
    (∀ a : Fin 8, (S.filter fun p => M (.inl a) p).card = 4) ∧
    (∀ b : Fin 72, (S.filter fun p => M (.inr b) p).card = 2) ∧
    (∀ p ∈ S, (A M p).card = 2 ∧ (B M p).card = 9) ∧
    (∀ p ∉ S, 2 * (A M p).card + (B M p).card = 8) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true → M m p = true → M m q = true → l = m) ∧
    (∀ p ∉ S, (A M p).card ≤ 3) ∧ (univ.filter fun p => p ∉ S ∧ (A M p).card = 3).card = 1
  let E : List (Fin 8 × Fin 8) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]
  let C := (E.zipIdx.filter fun x => !(0x35a5807 : Nat).testBit x.2).map Prod.fst
  let word (M : R → P → Bool) (S : Finset P) (e : Equiv.Perm (Fin 8)) :=
    let G (a b : Fin 8) := decide (b ≠ a ∧ ∃ p ∉ S, M (.inl (e a)) p = true ∧ M (.inl (e b)) p = true)
    (E.zipIdx.map fun ((a,b),i) => if G a b then 2^i else 0).foldr Nat.lor 0
  let norm (M : R → P → Bool) (S : Finset P) :=
    word M S (Equiv.refl _) = 0x35a5807 ∧
    (∀ p ∉ S, (A M p).card = 3 → A M p = {2,4,7}) ∧
    ∃ (c : Fin 16 ≃ ↥S) (r : Fin 72 → Fin 16 × Fin 16) (q : P),
    (∀ i, A M (c i).val = {C[i.val]!.1, C[i.val]!.2}) ∧
    (∀ b i, M (.inr b) (c i).val = true ↔ i = (r b).1 ∨ i = (r b).2) ∧
    q ∉ S ∧ A M q = {3,5} ∧ (B M q).image r = {(0,10),(2,6),(3,13),(4,15)}
  ¬ ∃ M S, valid M S ∧ norm M S

def H3 : Prop :=
  let P := Fin 111
  let R := Fin 8 ⊕ Fin 72
  let A (M : R → P → Bool) (p : P) := univ.filter fun l : Fin 8 => M (.inl l) p = true
  let B (M : R → P → Bool) (p : P) := univ.filter fun l : Fin 72 => M (.inr l) p = true
  let valid (M : R → P → Bool) (S : Finset P) :=
    S.card = 16 ∧ (∀ l, (univ.filter fun p => M l p).card = 11) ∧
    (∀ a : Fin 8, (S.filter fun p => M (.inl a) p).card = 4) ∧
    (∀ b : Fin 72, (S.filter fun p => M (.inr b) p).card = 2) ∧
    (∀ p ∈ S, (A M p).card = 2 ∧ (B M p).card = 9) ∧
    (∀ p ∉ S, 2 * (A M p).card + (B M p).card = 8) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true → M m p = true → M m q = true → l = m) ∧
    (∀ p ∉ S, (A M p).card ≤ 3) ∧ (univ.filter fun p => p ∉ S ∧ (A M p).card = 3).card = 1
  let E : List (Fin 8 × Fin 8) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]
  let C := (E.zipIdx.filter fun x => !(0x35a5807 : Nat).testBit x.2).map Prod.fst
  let word (M : R → P → Bool) (S : Finset P) (e : Equiv.Perm (Fin 8)) :=
    let G (a b : Fin 8) := decide (b ≠ a ∧ ∃ p ∉ S, M (.inl (e a)) p = true ∧ M (.inl (e b)) p = true)
    (E.zipIdx.map fun ((a,b),i) => if G a b then 2^i else 0).foldr Nat.lor 0
  let norm (M : R → P → Bool) (S : Finset P) :=
    word M S (Equiv.refl _) = 0x35a5807 ∧
    (∀ p ∉ S, (A M p).card = 3 → A M p = {2,4,7}) ∧
    ∃ (c : Fin 16 ≃ ↥S) (r : Fin 72 → Fin 16 × Fin 16) (q : P),
    (∀ i, A M (c i).val = {C[i.val]!.1, C[i.val]!.2}) ∧
    (∀ b i, M (.inr b) (c i).val = true ↔ i = (r b).1 ∨ i = (r b).2) ∧
    q ∉ S ∧ A M q = {3,5} ∧ (B M q).image r = {(0,15),(2,4),(3,13),(6,10)}
  ¬ ∃ M S, valid M S ∧ norm M S

def H4 : Prop :=
  let P := Fin 111
  let R := Fin 8 ⊕ Fin 72
  let A (M : R → P → Bool) (p : P) := univ.filter fun l : Fin 8 => M (.inl l) p = true
  let B (M : R → P → Bool) (p : P) := univ.filter fun l : Fin 72 => M (.inr l) p = true
  let valid (M : R → P → Bool) (S : Finset P) :=
    S.card = 16 ∧ (∀ l, (univ.filter fun p => M l p).card = 11) ∧
    (∀ a : Fin 8, (S.filter fun p => M (.inl a) p).card = 4) ∧
    (∀ b : Fin 72, (S.filter fun p => M (.inr b) p).card = 2) ∧
    (∀ p ∈ S, (A M p).card = 2 ∧ (B M p).card = 9) ∧
    (∀ p ∉ S, 2 * (A M p).card + (B M p).card = 8) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true → M m p = true → M m q = true → l = m) ∧
    (∀ p ∉ S, (A M p).card ≤ 3) ∧ (univ.filter fun p => p ∉ S ∧ (A M p).card = 3).card = 1
  let E : List (Fin 8 × Fin 8) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]
  let C := (E.zipIdx.filter fun x => !(0x35a5807 : Nat).testBit x.2).map Prod.fst
  let word (M : R → P → Bool) (S : Finset P) (e : Equiv.Perm (Fin 8)) :=
    let G (a b : Fin 8) := decide (b ≠ a ∧ ∃ p ∉ S, M (.inl (e a)) p = true ∧ M (.inl (e b)) p = true)
    (E.zipIdx.map fun ((a,b),i) => if G a b then 2^i else 0).foldr Nat.lor 0
  let norm (M : R → P → Bool) (S : Finset P) :=
    word M S (Equiv.refl _) = 0x35a5807 ∧
    (∀ p ∉ S, (A M p).card = 3 → A M p = {2,4,7}) ∧
    ∃ (c : Fin 16 ≃ ↥S) (r : Fin 72 → Fin 16 × Fin 16) (q : P),
    (∀ i, A M (c i).val = {C[i.val]!.1, C[i.val]!.2}) ∧
    (∀ b i, M (.inr b) (c i).val = true ↔ i = (r b).1 ∨ i = (r b).2) ∧
    q ∉ S ∧ A M q = {3,5} ∧ (B M q).image r = {(0,15),(2,6),(3,10),(4,13)}
  ¬ ∃ M S, valid M S ∧ norm M S

set_option maxRecDepth 12000 in
theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H2_R1.H2 := by
  intro first second third fourth
  rintro ⟨M,S,valid,graph,triple,points,label,q,heavy,light,out,support,choice⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at choice
  rcases choice with choice | choice | choice | choice
  · exact first ⟨M,S,valid,graph,triple,points,label,q,heavy,light,out,support,choice⟩
  · exact second ⟨M,S,valid,graph,triple,points,label,q,heavy,light,out,support,choice⟩
  · exact third ⟨M,S,valid,graph,triple,points,label,q,heavy,light,out,support,choice⟩
  · exact fourth ⟨M,S,valid,graph,triple,points,label,q,heavy,light,out,support,choice⟩

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H2_R1_H2_R1
