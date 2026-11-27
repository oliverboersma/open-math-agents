import OMAReductions.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1

/-! The nine-difference obstruction uses the argument in the Erdős 757 lower-bound reduction by @Dugongue. For the five progression edges we enumerate their possible midpoints. Each leaf gives an explicit linear combination forcing a repeated point or a parallelogram. -/

open scoped Pointwise Classical
open Finset

private def middle757 (x y z : ℝ) : Prop :=
  x+y+z = 3*x ∨ x+y+z = 3*y ∨ x+y+z = 3*z

private lemma edgeMiddle757 {x y z : ℝ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : ∃ a b c : ℝ, a < b ∧ b < c ∧ a+c=2*b ∧ ({x,y,z} : Finset ℝ)={a,b,c}) :
    middle757 x y z := by
  obtain ⟨a,b,c,hab,hbc,hmid,he⟩ := h
  have hsum := congrArg (fun s : Finset ℝ => ∑ t ∈ s, t) he
  simp [hxy,hxz,hyz,hab.ne,hbc.ne,(hab.trans hbc).ne] at hsum
  have hb : b ∈ ({x,y,z} : Finset ℝ) := by rw [he]; simp
  simp only [mem_insert,mem_singleton] at hb
  rcases hb with hb|hb|hb
  · exact Or.inl (by linarith)
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

private lemma forbiddenFour757 {A : Finset ℝ}
    (hcond : ∀ B : Set ℝ, B ⊆ (A : Set ℝ) → B.ncard = 4 → 11 ≤ (B-B).ncard)
    (f : Fin 7 ↪ ℝ) (hf : ∀ i, f i ∈ A) (i j u v : Fin 7) (hn : [i,j,u,v].Nodup) :
    f i + f j ≠ f u + f v := by
  intro h
  let a := f i
  let b := f j
  let c := f u
  let d := f v
  change a+b=c+d at h
  have hBA : ({a,b,c,d} : Set ℝ) ⊆ A := by
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl|rfl|rfl|rfl <;> exact hf _
  have hB4 : ({a,b,c,d} : Set ℝ).ncard = 4 := by
    have he : ({a,b,c,d} : Set ℝ) = ↑([a,b,c,d].toFinset) := by ext t; simp
    rw [he, Set.ncard_coe_finset, List.toFinset_card_of_nodup]
    · rfl
    · exact hn.map f.injective
  have hsub : ({a,b,c,d} : Set ℝ) - {a,b,c,d} ⊆
      {x | x ∈ [0,a-c,c-a,a-d,d-a,a-b,b-a,c-d,d-c]} := by
    rintro x ⟨t,ht,w,hw,rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht hw
    simp only [Set.mem_setOf_eq,List.mem_cons,List.mem_singleton]
    rcases ht with e|e|e|e <;> rcases hw with g|g|g|g <;> rw [e,g] <;>
      repeat (first | (left; linarith) | right)
    all_goals linarith
  have listBound (l : List ℝ) : ({t | t ∈ l} : Set ℝ).ncard ≤ l.length := by
    induction l with
    | nil => simp
    | cons a l ih =>
      have he : {t | t ∈ a :: l} = insert a {t | t ∈ l} := by ext t; simp
      rw [he]
      exact (Set.ncard_insert_le _ _).trans (by simp; omega)
  have h9 : (({a,b,c,d} : Set ℝ)-{a,b,c,d}).ncard ≤ 9 :=
    (Set.ncard_le_ncard hsub (List.finite_toSet _)).trans (listBound _)
  have h11 := hcond _ hBA hB4
  omega


private lemma fiveCase00 (f : Fin 7 ↪ ℝ) (bad : ∀ i j u v : Fin 7, [i,j,u,v].Nodup → f i + f j ≠ f u + f v)
    (h0 : f 0+f 1+f 2=3*f 0) (h1 : f 0+f 3+f 4=3*f 0) (h2 : middle757 (f 0) (f 5) (f 6)) (h3 : middle757 (f 1) (f 3) (f 5)) (h4 : middle757 (f 2) (f 4) (f 6)) : False := by
  apply bad 1 2 3 4 (by decide)
  linear_combination (1) * h0 + (-1) * h1

private lemma fiveCase01 (f : Fin 7 ↪ ℝ) (bad : ∀ i j u v : Fin 7, [i,j,u,v].Nodup → f i + f j ≠ f u + f v)
    (h0 : f 0+f 1+f 2=3*f 0) (h1 : f 0+f 3+f 4=3*f 3) (h2 : middle757 (f 0) (f 5) (f 6)) (h3 : middle757 (f 1) (f 3) (f 5)) (h4 : middle757 (f 2) (f 4) (f 6)) : False := by
  rcases h2 with h2|h2|h2
  · apply bad 1 2 5 6 (by decide)
    linear_combination (1) * h0 + (-1) * h2
  · rcases h3 with h3|h3|h3
    · rcases h4 with h4|h4|h4
      · apply (show f 0 ≠ f 1 from f.injective.ne (by decide))
        linear_combination (-1/3) * h0 + (1/6) * h1 + (1/6) * h2 + (1/3) * h3 + (-1/6) * h4
      · apply (show f 1 ≠ f 4 from f.injective.ne (by decide))
        linear_combination (-1/3) * h0 + (-1/3) * h1 + (-1/3) * h2 + (-2/3) * h3 + (1/3) * h4
      · apply (show f 1 ≠ f 6 from f.injective.ne (by decide))
        linear_combination (-1/3) * h0 + (-1/3) * h1 + (-1/3) * h2 + (-2/3) * h3 + (1/3) * h4
    · apply bad 0 4 1 5 (by decide)
      linear_combination (1) * h1 + (-1) * h3
    · apply bad 0 6 1 3 (by decide)
      linear_combination (1) * h2 + (-1) * h3
  · rcases h3 with h3|h3|h3
    · rcases h4 with h4|h4|h4
      · apply bad 0 2 1 3 (by decide)
        linear_combination (-1/3) * h0 + (2/3) * h1 + (-1/3) * h2 + (1/3) * h3 + (-2/3) * h4
      · apply (show f 0 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (-2/9) * h0 + (4/9) * h1 + (1/9) * h2 + (-1/9) * h3 + (2/9) * h4
      · apply (show f 1 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (-1/3) * h3 + (-1/3) * h4
    · apply bad 0 4 1 5 (by decide)
      linear_combination (1) * h1 + (-1) * h3
    · rcases h4 with h4|h4|h4
      · apply (show f 0 ≠ f 5 from f.injective.ne (by decide))
        linear_combination (-4/9) * h0 + (2/9) * h1 + (-1/9) * h2 + (4/9) * h3 + (-2/9) * h4
      · apply bad 0 3 4 6 (by decide)
        linear_combination (-1/3) * h0 + (-1/3) * h1 + (2/3) * h2 + (1/3) * h3 + (1/3) * h4
      · apply (show f 1 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (2/3) * h0 + (2/3) * h1 + (2/3) * h2 + (1/3) * h3 + (-2/3) * h4

private lemma fiveCase02 (f : Fin 7 ↪ ℝ) (bad : ∀ i j u v : Fin 7, [i,j,u,v].Nodup → f i + f j ≠ f u + f v)
    (h0 : f 0+f 1+f 2=3*f 0) (h1 : f 0+f 3+f 4=3*f 4) (h2 : middle757 (f 0) (f 5) (f 6)) (h3 : middle757 (f 1) (f 3) (f 5)) (h4 : middle757 (f 2) (f 4) (f 6)) : False := by
  rcases h2 with h2|h2|h2
  · apply bad 1 2 5 6 (by decide)
    linear_combination (1) * h0 + (-1) * h2
  · rcases h3 with h3|h3|h3
    · rcases h4 with h4|h4|h4
      · apply bad 0 1 2 4 (by decide)
        linear_combination (-1/3) * h0 + (2/3) * h1 + (-1/3) * h2 + (-2/3) * h3 + (1/3) * h4
      · apply (show f 1 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (-1/3) * h0 + (-1/3) * h1 + (-1/3) * h2 + (-2/3) * h3 + (1/3) * h4
      · apply (show f 0 ≠ f 5 from f.injective.ne (by decide))
        linear_combination (-2/9) * h0 + (1/9) * h1 + (4/9) * h2 + (-1/9) * h3 + (2/9) * h4
    · rcases h4 with h4|h4|h4
      · apply (show f 0 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (-4/9) * h0 + (-1/9) * h1 + (2/9) * h2 + (4/9) * h3 + (-2/9) * h4
      · apply (show f 1 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (2/3) * h3 + (-1/3) * h4
      · apply bad 0 4 3 5 (by decide)
        linear_combination (-1/3) * h0 + (-1/3) * h1 + (2/3) * h2 + (1/3) * h3 + (1/3) * h4
    · apply bad 0 6 1 3 (by decide)
      linear_combination (1) * h2 + (-1) * h3
  · rcases h3 with h3|h3|h3
    · apply bad 0 1 4 6 (by decide)
      linear_combination (1/2) * h1 + (1/2) * h2 + (-1/2) * h3
    · rcases h4 with h4|h4|h4
      · apply (show f 2 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (-1/3) * h0 + (-1/3) * h1 + (-1/3) * h2 + (1/3) * h3 + (-2/3) * h4
      · apply (show f 0 ≠ f 1 from f.injective.ne (by decide))
        linear_combination (-2/3) * h0 + (-2/3) * h1 + (1/3) * h2 + (-1/3) * h3 + (2/3) * h4
      · apply (show f 0 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (-2/3) * h0 + (1/3) * h1 + (-2/3) * h2 + (2/3) * h3 + (2/3) * h4
    · rcases h4 with h4|h4|h4
      · apply (show f 2 ≠ f 5 from f.injective.ne (by decide))
        linear_combination (-1/3) * h0 + (-1/3) * h1 + (-1/3) * h2 + (1/3) * h3 + (-2/3) * h4
      · apply (show f 0 ≠ f 5 from f.injective.ne (by decide))
        linear_combination (-2/3) * h0 + (-2/3) * h1 + (1/3) * h2 + (2/3) * h3 + (2/3) * h4
      · apply (show f 0 ≠ f 1 from f.injective.ne (by decide))
        linear_combination (-2/3) * h0 + (1/3) * h1 + (-2/3) * h2 + (-1/3) * h3 + (2/3) * h4

private lemma fiveCase10 (f : Fin 7 ↪ ℝ) (bad : ∀ i j u v : Fin 7, [i,j,u,v].Nodup → f i + f j ≠ f u + f v)
    (h0 : f 0+f 1+f 2=3*f 1) (h1 : f 0+f 3+f 4=3*f 0) (h2 : middle757 (f 0) (f 5) (f 6)) (h3 : middle757 (f 1) (f 3) (f 5)) (h4 : middle757 (f 2) (f 4) (f 6)) : False := by
  rcases h2 with h2|h2|h2
  · apply bad 3 4 5 6 (by decide)
    linear_combination (1) * h1 + (-1) * h2
  · rcases h3 with h3|h3|h3
    · apply bad 0 2 3 5 (by decide)
      linear_combination (1) * h0 + (-1) * h3
    · rcases h4 with h4|h4|h4
      · apply (show f 2 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (2/3) * h3 + (-1/3) * h4
      · apply (show f 0 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (1/6) * h0 + (-1/3) * h1 + (1/6) * h2 + (1/3) * h3 + (-1/6) * h4
      · apply (show f 3 ≠ f 6 from f.injective.ne (by decide))
        linear_combination (-1/3) * h0 + (-1/3) * h1 + (-1/3) * h2 + (-2/3) * h3 + (1/3) * h4
    · apply bad 0 6 1 3 (by decide)
      linear_combination (1) * h2 + (-1) * h3
  · rcases h3 with h3|h3|h3
    · apply bad 0 2 3 5 (by decide)
      linear_combination (1) * h0 + (-1) * h3
    · rcases h4 with h4|h4|h4
      · apply (show f 0 ≠ f 1 from f.injective.ne (by decide))
        linear_combination (4/9) * h0 + (-2/9) * h1 + (1/9) * h2 + (-1/9) * h3 + (2/9) * h4
      · apply bad 0 1 2 6 (by decide)
        linear_combination (-2/3) * h0 + (-2/3) * h1 + (1/3) * h2 + (-1/3) * h3 + (-1/3) * h4
      · apply (show f 1 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (-1/3) * h0 + (-1/3) * h1 + (-1/3) * h2 + (1/3) * h3 + (1/3) * h4
    · rcases h4 with h4|h4|h4
      · apply bad 0 1 2 6 (by decide)
        linear_combination (-1/3) * h0 + (-1/3) * h1 + (2/3) * h2 + (1/3) * h3 + (1/3) * h4
      · apply (show f 0 ≠ f 5 from f.injective.ne (by decide))
        linear_combination (2/9) * h0 + (-4/9) * h1 + (-1/9) * h2 + (4/9) * h3 + (-2/9) * h4
      · apply (show f 1 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (-2/3) * h0 + (-2/3) * h1 + (-2/3) * h2 + (-1/3) * h3 + (2/3) * h4

private lemma fiveCase11 (f : Fin 7 ↪ ℝ) (bad : ∀ i j u v : Fin 7, [i,j,u,v].Nodup → f i + f j ≠ f u + f v)
    (h0 : f 0+f 1+f 2=3*f 1) (h1 : f 0+f 3+f 4=3*f 3) (h2 : middle757 (f 0) (f 5) (f 6)) (h3 : middle757 (f 1) (f 3) (f 5)) (h4 : middle757 (f 2) (f 4) (f 6)) : False := by
  rcases h2 with h2|h2|h2
  · rcases h3 with h3|h3|h3
    · apply bad 0 2 3 5 (by decide)
      linear_combination (1) * h0 + (-1) * h3
    · apply bad 0 4 1 5 (by decide)
      linear_combination (1) * h1 + (-1) * h3
    · rcases h4 with h4|h4|h4
      · apply (show f 2 ≠ f 5 from f.injective.ne (by decide))
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (2/3) * h3 + (-1/3) * h4
      · apply (show f 4 ≠ f 5 from f.injective.ne (by decide))
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (2/3) * h3 + (-1/3) * h4
      · apply (show f 0 ≠ f 5 from f.injective.ne (by decide))
        linear_combination (1/6) * h0 + (1/6) * h1 + (-1/3) * h2 + (1/3) * h3 + (-1/6) * h4
  · rcases h3 with h3|h3|h3
    · apply bad 0 2 3 5 (by decide)
      linear_combination (1) * h0 + (-1) * h3
    · apply bad 0 4 1 5 (by decide)
      linear_combination (1) * h1 + (-1) * h3
    · apply bad 0 6 1 3 (by decide)
      linear_combination (1) * h2 + (-1) * h3
  · rcases h3 with h3|h3|h3
    · apply bad 0 2 3 5 (by decide)
      linear_combination (1) * h0 + (-1) * h3
    · apply bad 0 4 1 5 (by decide)
      linear_combination (1) * h1 + (-1) * h3
    · rcases h4 with h4|h4|h4
      · apply bad 0 3 1 6 (by decide)
        linear_combination (2/3) * h0 + (-1/3) * h1 + (2/3) * h2 + (1/3) * h3 + (1/3) * h4
      · apply bad 0 1 3 6 (by decide)
        linear_combination (-1/3) * h0 + (2/3) * h1 + (2/3) * h2 + (1/3) * h3 + (1/3) * h4
      · apply (show f 0 ≠ f 5 from f.injective.ne (by decide))
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (2/3) * h3 + (-1/3) * h4

private lemma fiveCase12 (f : Fin 7 ↪ ℝ) (bad : ∀ i j u v : Fin 7, [i,j,u,v].Nodup → f i + f j ≠ f u + f v)
    (h0 : f 0+f 1+f 2=3*f 1) (h1 : f 0+f 3+f 4=3*f 4) (h2 : middle757 (f 0) (f 5) (f 6)) (h3 : middle757 (f 1) (f 3) (f 5)) (h4 : middle757 (f 2) (f 4) (f 6)) : False := by
  rcases h2 with h2|h2|h2
  · rcases h3 with h3|h3|h3
    · apply bad 0 2 3 5 (by decide)
      linear_combination (1) * h0 + (-1) * h3
    · rcases h4 with h4|h4|h4
      · apply bad 0 1 2 4 (by decide)
        linear_combination (-1/3) * h0 + (2/3) * h1 + (-1/3) * h2 + (1/3) * h3 + (1/3) * h4
      · apply (show f 1 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (-1/3) * h0 + (-1/3) * h1 + (-1/3) * h2 + (1/3) * h3 + (1/3) * h4
      · apply (show f 0 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (2/9) * h0 + (-1/9) * h1 + (-4/9) * h2 + (4/9) * h3 + (-2/9) * h4
    · rcases h4 with h4|h4|h4
      · apply (show f 0 ≠ f 1 from f.injective.ne (by decide))
        linear_combination (4/9) * h0 + (1/9) * h1 + (-2/9) * h2 + (-1/9) * h3 + (2/9) * h4
      · apply (show f 1 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (-2/3) * h0 + (-2/3) * h1 + (-2/3) * h2 + (-1/3) * h3 + (2/3) * h4
      · apply bad 0 1 2 4 (by decide)
        linear_combination (-2/3) * h0 + (1/3) * h1 + (-2/3) * h2 + (-1/3) * h3 + (-1/3) * h4
  · rcases h3 with h3|h3|h3
    · apply bad 0 2 3 5 (by decide)
      linear_combination (1) * h0 + (-1) * h3
    · rcases h4 with h4|h4|h4
      · apply bad 0 5 1 4 (by decide)
        linear_combination (2/3) * h0 + (2/3) * h1 + (-1/3) * h2 + (1/3) * h3 + (1/3) * h4
      · apply (show f 0 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (2/3) * h3 + (-1/3) * h4
      · apply bad 0 1 4 5 (by decide)
        linear_combination (-1/3) * h0 + (2/3) * h1 + (2/3) * h2 + (1/3) * h3 + (1/3) * h4
    · apply bad 0 6 1 3 (by decide)
      linear_combination (1) * h2 + (-1) * h3
  · rcases h3 with h3|h3|h3
    · apply bad 0 1 4 6 (by decide)
      linear_combination (1/2) * h1 + (1/2) * h2 + (-1/2) * h3
    · rcases h4 with h4|h4|h4
      · apply bad 0 3 1 2 (by decide)
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (-1/3) * h3 + (2/3) * h4
      · apply (show f 0 ≠ f 1 from f.injective.ne (by decide))
        linear_combination (2/3) * h0 + (2/3) * h1 + (-1/3) * h2 + (1/3) * h3 + (-2/3) * h4
      · apply (show f 1 ≠ f 4 from f.injective.ne (by decide))
        linear_combination (-1/3) * h0 + (2/3) * h1 + (-1/3) * h2 + (1/3) * h3 + (1/3) * h4
    · rcases h4 with h4|h4|h4
      · apply bad 0 5 1 2 (by decide)
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (-1/3) * h3 + (2/3) * h4
      · apply (show f 1 ≠ f 6 from f.injective.ne (by decide))
        linear_combination (-1/3) * h0 + (-1/3) * h1 + (2/3) * h2 + (1/3) * h3 + (1/3) * h4
      · apply (show f 0 ≠ f 1 from f.injective.ne (by decide))
        linear_combination (2/3) * h0 + (-1/3) * h1 + (2/3) * h2 + (1/3) * h3 + (-2/3) * h4

private lemma fiveCase20 (f : Fin 7 ↪ ℝ) (bad : ∀ i j u v : Fin 7, [i,j,u,v].Nodup → f i + f j ≠ f u + f v)
    (h0 : f 0+f 1+f 2=3*f 2) (h1 : f 0+f 3+f 4=3*f 0) (h2 : middle757 (f 0) (f 5) (f 6)) (h3 : middle757 (f 1) (f 3) (f 5)) (h4 : middle757 (f 2) (f 4) (f 6)) : False := by
  rcases h2 with h2|h2|h2
  · apply bad 3 4 5 6 (by decide)
    linear_combination (1) * h1 + (-1) * h2
  · rcases h3 with h3|h3|h3
    · rcases h4 with h4|h4|h4
      · apply (show f 1 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (-1/3) * h0 + (-1/3) * h1 + (-1/3) * h2 + (-2/3) * h3 + (1/3) * h4
      · apply (show f 0 ≠ f 1 from f.injective.ne (by decide))
        linear_combination (-1/9) * h0 + (-4/9) * h1 + (2/9) * h2 + (4/9) * h3 + (-2/9) * h4
      · apply bad 0 2 1 5 (by decide)
        linear_combination (-1/3) * h0 + (-1/3) * h1 + (2/3) * h2 + (1/3) * h3 + (1/3) * h4
    · rcases h4 with h4|h4|h4
      · apply (show f 1 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (2/3) * h3 + (-1/3) * h4
      · apply bad 0 2 1 5 (by decide)
        linear_combination (-2/3) * h0 + (-2/3) * h1 + (1/3) * h2 + (-1/3) * h3 + (-1/3) * h4
      · apply (show f 0 ≠ f 5 from f.injective.ne (by decide))
        linear_combination (1/9) * h0 + (-2/9) * h1 + (4/9) * h2 + (-1/9) * h3 + (2/9) * h4
    · apply bad 0 6 1 3 (by decide)
      linear_combination (1) * h2 + (-1) * h3
  · rcases h3 with h3|h3|h3
    · rcases h4 with h4|h4|h4
      · apply (show f 0 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (-2/3) * h0 + (-2/3) * h1 + (1/3) * h2 + (-1/3) * h3 + (2/3) * h4
      · apply (show f 1 ≠ f 4 from f.injective.ne (by decide))
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (-1/3) * h3 + (2/3) * h4
      · apply (show f 0 ≠ f 1 from f.injective.ne (by decide))
        linear_combination (1/3) * h0 + (-2/3) * h1 + (-2/3) * h2 + (2/3) * h3 + (2/3) * h4
    · apply bad 0 3 2 6 (by decide)
      linear_combination (1/2) * h0 + (1/2) * h2 + (-1/2) * h3
    · rcases h4 with h4|h4|h4
      · apply (show f 0 ≠ f 5 from f.injective.ne (by decide))
        linear_combination (-2/3) * h0 + (-2/3) * h1 + (1/3) * h2 + (2/3) * h3 + (2/3) * h4
      · apply (show f 4 ≠ f 5 from f.injective.ne (by decide))
        linear_combination (-1/3) * h0 + (-1/3) * h1 + (-1/3) * h2 + (1/3) * h3 + (-2/3) * h4
      · apply (show f 0 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (1/3) * h0 + (-2/3) * h1 + (-2/3) * h2 + (-1/3) * h3 + (2/3) * h4

private lemma fiveCase21 (f : Fin 7 ↪ ℝ) (bad : ∀ i j u v : Fin 7, [i,j,u,v].Nodup → f i + f j ≠ f u + f v)
    (h0 : f 0+f 1+f 2=3*f 2) (h1 : f 0+f 3+f 4=3*f 3) (h2 : middle757 (f 0) (f 5) (f 6)) (h3 : middle757 (f 1) (f 3) (f 5)) (h4 : middle757 (f 2) (f 4) (f 6)) : False := by
  rcases h2 with h2|h2|h2
  · rcases h3 with h3|h3|h3
    · rcases h4 with h4|h4|h4
      · apply (show f 1 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (-1/3) * h3 + (-1/3) * h4
      · apply bad 0 2 1 3 (by decide)
        linear_combination (-1/3) * h0 + (2/3) * h1 + (-1/3) * h2 + (1/3) * h3 + (1/3) * h4
      · apply (show f 0 ≠ f 1 from f.injective.ne (by decide))
        linear_combination (-1/9) * h0 + (2/9) * h1 + (-4/9) * h2 + (4/9) * h3 + (-2/9) * h4
    · apply bad 0 4 1 5 (by decide)
      linear_combination (1) * h1 + (-1) * h3
    · rcases h4 with h4|h4|h4
      · apply (show f 1 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (2/3) * h0 + (2/3) * h1 + (2/3) * h2 + (1/3) * h3 + (-2/3) * h4
      · apply (show f 0 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (1/9) * h0 + (4/9) * h1 + (-2/9) * h2 + (-1/9) * h3 + (2/9) * h4
      · apply bad 0 2 1 3 (by decide)
        linear_combination (-2/3) * h0 + (1/3) * h1 + (-2/3) * h2 + (-1/3) * h3 + (-1/3) * h4
  · rcases h3 with h3|h3|h3
    · rcases h4 with h4|h4|h4
      · apply (show f 0 ≠ f 1 from f.injective.ne (by decide))
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (2/3) * h3 + (-1/3) * h4
      · apply bad 0 4 1 2 (by decide)
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (2/3) * h3 + (-1/3) * h4
      · apply bad 0 6 1 2 (by decide)
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (2/3) * h3 + (-1/3) * h4
    · apply bad 0 4 1 5 (by decide)
      linear_combination (1) * h1 + (-1) * h3
    · apply bad 0 6 1 3 (by decide)
      linear_combination (1) * h2 + (-1) * h3
  · rcases h3 with h3|h3|h3
    · rcases h4 with h4|h4|h4
      · apply (show f 0 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (2/3) * h0 + (2/3) * h1 + (-1/3) * h2 + (1/3) * h3 + (-2/3) * h4
      · apply bad 0 1 3 4 (by decide)
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (-1/3) * h3 + (2/3) * h4
      · apply (show f 1 ≠ f 4 from f.injective.ne (by decide))
        linear_combination (-1/3) * h0 + (-1/3) * h1 + (2/3) * h2 + (-2/3) * h3 + (-2/3) * h4
    · apply bad 0 4 1 5 (by decide)
      linear_combination (1) * h1 + (-1) * h3
    · rcases h4 with h4|h4|h4
      · apply (show f 3 ≠ f 6 from f.injective.ne (by decide))
        linear_combination (-1/3) * h0 + (-1/3) * h1 + (2/3) * h2 + (1/3) * h3 + (1/3) * h4
      · apply bad 0 1 4 5 (by decide)
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (2/3) * h3 + (2/3) * h4
      · apply (show f 0 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (-1/3) * h0 + (2/3) * h1 + (2/3) * h2 + (1/3) * h3 + (-2/3) * h4

private lemma fiveCase22 (f : Fin 7 ↪ ℝ) (bad : ∀ i j u v : Fin 7, [i,j,u,v].Nodup → f i + f j ≠ f u + f v)
    (h0 : f 0+f 1+f 2=3*f 2) (h1 : f 0+f 3+f 4=3*f 4) (h2 : middle757 (f 0) (f 5) (f 6)) (h3 : middle757 (f 1) (f 3) (f 5)) (h4 : middle757 (f 2) (f 4) (f 6)) : False := by
  rcases h2 with h2|h2|h2
  · rcases h3 with h3|h3|h3
    · rcases h4 with h4|h4|h4
      · apply (show f 0 ≠ f 5 from f.injective.ne (by decide))
        linear_combination (-2/3) * h0 + (1/3) * h1 + (-2/3) * h2 + (-1/3) * h3 + (2/3) * h4
      · apply (show f 0 ≠ f 1 from f.injective.ne (by decide))
        linear_combination (1/3) * h0 + (-2/3) * h1 + (-2/3) * h2 + (2/3) * h3 + (2/3) * h4
      · apply (show f 1 ≠ f 6 from f.injective.ne (by decide))
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (-1/3) * h3 + (2/3) * h4
    · rcases h4 with h4|h4|h4
      · apply (show f 0 ≠ f 3 from f.injective.ne (by decide))
        linear_combination (-2/3) * h0 + (1/3) * h1 + (-2/3) * h2 + (2/3) * h3 + (2/3) * h4
      · apply (show f 0 ≠ f 5 from f.injective.ne (by decide))
        linear_combination (1/3) * h0 + (-2/3) * h1 + (-2/3) * h2 + (-1/3) * h3 + (2/3) * h4
      · apply (show f 3 ≠ f 6 from f.injective.ne (by decide))
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (-1/3) * h3 + (2/3) * h4
    · apply bad 0 5 2 4 (by decide)
      linear_combination (1/2) * h0 + (1/2) * h1 + (-1/2) * h3
  · rcases h3 with h3|h3|h3
    · rcases h4 with h4|h4|h4
      · apply (show f 0 ≠ f 5 from f.injective.ne (by decide))
        linear_combination (2/3) * h0 + (-1/3) * h1 + (2/3) * h2 + (1/3) * h3 + (-2/3) * h4
      · apply (show f 1 ≠ f 6 from f.injective.ne (by decide))
        linear_combination (-1/3) * h0 + (2/3) * h1 + (-1/3) * h2 + (-2/3) * h3 + (-2/3) * h4
      · apply bad 0 3 1 6 (by decide)
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (2/3) * h3 + (2/3) * h4
    · rcases h4 with h4|h4|h4
      · apply (show f 3 ≠ f 6 from f.injective.ne (by decide))
        linear_combination (2/3) * h0 + (-1/3) * h1 + (-1/3) * h2 + (-2/3) * h3 + (-2/3) * h4
      · apply (show f 0 ≠ f 5 from f.injective.ne (by decide))
        linear_combination (-1/3) * h0 + (2/3) * h1 + (2/3) * h2 + (1/3) * h3 + (-2/3) * h4
      · apply bad 0 1 3 6 (by decide)
        linear_combination (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (2/3) * h3 + (2/3) * h4
    · apply bad 0 6 1 3 (by decide)
      linear_combination (1) * h2 + (-1) * h3
  · rcases h3 with h3|h3|h3
    · apply bad 0 1 4 6 (by decide)
      linear_combination (1/2) * h1 + (1/2) * h2 + (-1/2) * h3
    · apply bad 0 3 2 6 (by decide)
      linear_combination (1/2) * h0 + (1/2) * h2 + (-1/2) * h3
    · apply bad 0 5 2 4 (by decide)
      linear_combination (1/2) * h0 + (1/2) * h1 + (-1/2) * h3

theorem OMA.solution : OMA.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1.H2 := by
  classical
  intro A hcond
  dsimp only
  rintro ⟨f,h0,h1,h2,h3,h4⟩
  obtain ⟨sub0,ap0⟩ := Finset.mem_filter.mp h0
  have incl0 := Finset.mem_powerset.mp sub0
  have m0 : middle757 (f 0) (f 1) (f 2) := edgeMiddle757 (f.injective.ne (by decide)) (f.injective.ne (by decide)) (f.injective.ne (by decide)) ap0
  obtain ⟨sub1,ap1⟩ := Finset.mem_filter.mp h1
  have incl1 := Finset.mem_powerset.mp sub1
  have m1 : middle757 (f 0) (f 3) (f 4) := edgeMiddle757 (f.injective.ne (by decide)) (f.injective.ne (by decide)) (f.injective.ne (by decide)) ap1
  obtain ⟨sub2,ap2⟩ := Finset.mem_filter.mp h2
  have incl2 := Finset.mem_powerset.mp sub2
  have m2 : middle757 (f 0) (f 5) (f 6) := edgeMiddle757 (f.injective.ne (by decide)) (f.injective.ne (by decide)) (f.injective.ne (by decide)) ap2
  obtain ⟨sub3,ap3⟩ := Finset.mem_filter.mp h3
  have incl3 := Finset.mem_powerset.mp sub3
  have m3 : middle757 (f 1) (f 3) (f 5) := edgeMiddle757 (f.injective.ne (by decide)) (f.injective.ne (by decide)) (f.injective.ne (by decide)) ap3
  obtain ⟨sub4,ap4⟩ := Finset.mem_filter.mp h4
  have incl4 := Finset.mem_powerset.mp sub4
  have m4 : middle757 (f 2) (f 4) (f 6) := edgeMiddle757 (f.injective.ne (by decide)) (f.injective.ne (by decide)) (f.injective.ne (by decide)) ap4
  have hf (i : Fin 7) : f i ∈ A := by
    fin_cases i
    · exact incl0 (show f 0 ∈ _ by simp)
    · exact incl0 (show f 1 ∈ _ by simp)
    · exact incl0 (show f 2 ∈ _ by simp)
    · exact incl1 (show f 3 ∈ _ by simp)
    · exact incl1 (show f 4 ∈ _ by simp)
    · exact incl2 (show f 5 ∈ _ by simp)
    · exact incl2 (show f 6 ∈ _ by simp)
  have bad := forbiddenFour757 hcond f hf
  rcases m0 with g0|g0|g0 <;> rcases m1 with g1|g1|g1
  · exact fiveCase00 f bad g0 g1 m2 m3 m4
  · exact fiveCase01 f bad g0 g1 m2 m3 m4
  · exact fiveCase02 f bad g0 g1 m2 m3 m4
  · exact fiveCase10 f bad g0 g1 m2 m3 m4
  · exact fiveCase11 f bad g0 g1 m2 m3 m4
  · exact fiveCase12 f bad g0 g1 m2 m3 m4
  · exact fiveCase20 f bad g0 g1 m2 m3 m4
  · exact fiveCase21 f bad g0 g1 m2 m3 m4
  · exact fiveCase22 f bad g0 g1 m2 m3 m4
