import FormalConjectures.ErdosProblems.«835»

/-! Fix a central block A and retain the half of the middle layer meeting A in at
least k/2 points. Complementation identifies opposite equatorial blocks. For an
exact trace I on A, the color counts in the retained slice differ by at most one,
with the exceptional color and the sign prescribed by A and the codimension.
H1 is the resulting constrained coloring obstruction on that half. H2 is a
finite incidence identity independent of graphs. The odd k cases disappear
from H1 entirely. -/

-- Credit: @Pixelstorm44
-- The star bijection is adapted from the project proof of
-- Erdos835.chromaticNumber_johnson_2k_k_lower_bound.

open Finset SimpleGraph

namespace OMA.R_Erdos835_johnson_chromaticNumber_R2

/-- No coloring of the closed half with its antipodal equator and prescribed
color populations on every exact trace. F i contains the retained blocks of color i. -/
def H1 : Prop :=
  ∀ k : ℕ, 3 ≤ k → Even k → ∀ A : Finset (Fin (2*k)), A.card = k →
    ¬ ∃ (F : Fin (k+1) → Finset (Finset (Fin (2*k)))) (a : Fin (k+1)),
      A ∈ F a ∧
      (∀ i B, B ∈ F i → B.card = k ∧ k ≤ 2*(A ∩ B).card) ∧
      (∀ B : Finset (Fin (2*k)), B.card = k → k ≤ 2*(A ∩ B).card → ∃! i, B ∈ F i) ∧
      (∀ i B C, B ∈ F i → C ∈ F i → (B ∩ C).card + 1 ≠ k) ∧
      (∀ i B, B ∈ F i → 2*(A ∩ B).card = k → Bᶜ ∈ F i) ∧
      (∀ I : Finset (Fin (2*k)), I ⊆ A → k ≤ 2*I.card → ∀ i j : Fin (k+1),
        (((F i).filter (fun B => A ∩ B = I)).card : ℤ) -
          ((F j).filter (fun B => A ∩ B = I)).card =
        (-1 : ℤ) ^ (k-I.card) * ((if a = i then 1 else 0) - (if a = j then 1 else 0)))

/-- Two uniform block families covering each codimension-one set exactly once
have a prescribed signed difference on every exact trace of a fixed block. -/
def H2 : Prop :=
  ∀ (n k : ℕ) (F G : Finset (Finset (Fin n))),
    (∀ B ∈ F, B.card = k) → (∀ B ∈ G, B.card = k) →
    (∀ T : Finset (Fin n), T.card = k-1 →
      (F.filter (fun B => T ⊆ B)).card = 1 ∧ (G.filter (fun B => T ⊆ B)).card = 1) →
    ∀ A I : Finset (Fin n), A.card = k → I ⊆ A →
      ((F.filter (fun B => A ∩ B = I)).card : ℤ) - (G.filter (fun B => A ∩ B = I)).card =
      (-1 : ℤ) ^ (k-I.card) * ((if A ∈ F then 1 else 0) - (if A ∈ G then 1 else 0))

theorem extend_colors {n m q : ℕ} (hq : q = n-m+1) (hm : 0 < m) (hmn : m ≤ n)
    (c : (SimpleGraph.johnson n m).Coloring (Fin q))
    (T : Finset (Fin n)) (hT : T.card = m-1) (a : Fin q) :
    ∃! A : {S : Finset (Fin n) // S.card = m}, T ⊆ A.1 ∧ c A = a := by
  classical
  let R : Finset (Fin n) := univ \ T
  let ext (x : R) : {S : Finset (Fin n) // S.card = m} := ⟨insert x.1 T,by
    rw [card_insert_of_notMem (mem_sdiff.mp x.2).2,hT]
    omega⟩
  have adj (A B : {S : Finset (Fin n) // S.card = m}) (hA : T ⊆ A.1) (hB : T ⊆ B.1) (hne : A ≠ B) :
      (SimpleGraph.johnson n m).Adj A B := by
    apply johnson_adj_iff_ge.mpr
    have hcard := card_le_card (subset_inter hA hB)
    exact ⟨hne,by omega⟩
  have hIj : Function.Injective (fun x : R => c (ext x)) := by
    intro x y he
    by_contra hn
    have hne : ext x ≠ ext y := by
      intro e
      have hmem : x.1 ∈ (ext y).1 := e ▸ mem_insert_self _ _
      have hxy := (mem_insert.mp hmem).resolve_right (mem_sdiff.mp x.2).2
      exact hn (Subtype.ext hxy)
    exact (c.valid (adj _ _ (subset_insert _ _) (subset_insert _ _) hne)) he
  have hR : Fintype.card R = Fintype.card (Fin q) := by
    simp [R,hT]
    omega
  have hSurj := ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hIj,hR⟩).2
  obtain ⟨x,hx⟩ := hSurj a
  refine ⟨ext x,⟨subset_insert _ _,hx⟩,?_⟩
  rintro B ⟨hB,hBa⟩
  by_contra hne
  exact (c.valid (adj _ _ hB (subset_insert _ _) hne)) (hBa.trans hx.symm)

lemma star_count {k : ℕ} (hk : 0 < k) (c : (johnson (2*k) k).Coloring (Fin (k+1)))
    (F : Fin (k+1) → Finset (Finset (Fin (2*k))))
    (hf : ∀ i B, B ∈ F i ↔ ∃ h : B.card = k, c ⟨B,h⟩ = i)
    (a : Fin (k+1)) (T : Finset (Fin (2*k))) (hT : T.card = k-1) :
    ((F a).filter (fun B => T ⊆ B)).card = 1 := by
  classical
  obtain ⟨B, ⟨hTB,hB⟩, huniq⟩ := extend_colors (by omega) hk (by omega) c T hT a
  apply card_eq_one.mpr
  refine ⟨B.val, ?_⟩
  ext S
  simp only [mem_filter, hf, mem_singleton]
  constructor
  · rintro ⟨⟨hS,ha⟩,hTS⟩
    exact congrArg Subtype.val (huniq ⟨S,hS⟩ ⟨hTS,ha⟩)
  · rintro rfl
    exact ⟨⟨B.property,hB⟩,hTB⟩

lemma empty_trace {k : ℕ} (c : (johnson (2*k) k).Coloring (Fin (k+1)))
    (F : Fin (k+1) → Finset (Finset (Fin (2*k))))
    (hf : ∀ i B, B ∈ F i ↔ ∃ h : B.card = k, c ⟨B,h⟩ = i)
    (i : Fin (k+1)) (A : {S : Finset (Fin (2*k)) // S.card = k}) :
    (((F i).filter (fun B => A.val ∩ B = ∅)).card : ℤ) =
    (if c ⟨A.valᶜ, by rw [card_compl, Fintype.card_fin,A.property]; omega⟩ = i then 1 else 0) := by
  classical
  let C : {S : Finset (Fin (2*k)) // S.card = k} := ⟨A.valᶜ, by rw [card_compl,Fintype.card_fin,A.property]; omega⟩
  change _ = (if c C = i then 1 else 0)
  have heq : (F i).filter (fun B => A.val ∩ B = ∅) =
      (if c C = i then {C.val} else ∅) := by
    ext B
    have onlyCompl (hB : B.card = k) (hd : A.val ∩ B = ∅) : B = C.val := by
      apply eq_of_subset_of_card_le _ (by rw [hB,C.property])
      exact fun x hx => mem_compl.mpr (fun hxA => disjoint_left.mp
        (disjoint_iff_inter_eq_empty.mpr hd) hxA hx)
    have hAC : A.val ∩ C.val = ∅ := by simp [C]
    simp only [mem_filter,hf]
    split_ifs with hi
    · simp only [mem_singleton]
      constructor
      · rintro ⟨⟨hB,_⟩,hd⟩; exact onlyCompl hB hd
      · rintro rfl; exact ⟨⟨C.property,hi⟩,hAC⟩
    · simp only [notMem_empty,iff_false]
      rintro ⟨⟨hB,hc⟩,hd⟩
      obtain rfl := onlyCompl hB hd
      exact hi hc
  rw [heq]; split_ifs <;> simp

theorem main : H1 → H2 → type_of% @Erdos835.johnson_chromaticNumber := by
  classical
  intro half trace k hk
  by_contra! bad
  obtain ⟨c⟩ := chromaticNumber_le_iff_colorable.mp
    (show (johnson (2*k) k).chromaticNumber ≤ ((k+1 : ℕ) : ℕ∞) from
      Order.le_of_lt_add_one (by simpa only [Nat.cast_add_one,add_assoc,one_add_one_eq_two] using bad))
  let V := {S : Finset (Fin (2*k)) // S.card = k}
  let F (i : Fin (k+1)) : Finset (Finset (Fin (2*k))) :=
    ((univ : Finset V).filter (fun v => c v = i)).image Subtype.val
  have hf (i : Fin (k+1)) (B : Finset (Fin (2*k))) :
      B ∈ F i ↔ ∃ h : B.card = k, c ⟨B,h⟩ = i := by
    simp only [F,V, mem_image, mem_filter, mem_univ, true_and, Subtype.exists]
    constructor
    · rintro ⟨_, h, hc, rfl⟩; exact ⟨h,hc⟩
    · rintro ⟨h,hc⟩; exact ⟨B,h,hc,rfl⟩
  have htr (X : V) (I : Finset (Fin (2*k))) (hI : I ⊆ X.val) (i j : Fin (k+1)) :
      (((F i).filter (fun B => X.val ∩ B = I)).card : ℤ) -
        ((F j).filter (fun B => X.val ∩ B = I)).card =
      (-1 : ℤ) ^ (k-I.card) * ((if c X = i then 1 else 0) - (if c X = j then 1 else 0)) := by
    have u := trace (2*k) k (F i) (F j) (fun B hB => ((hf i B).1 hB).choose)
      (fun B hB => ((hf j B).1 hB).choose) (fun T hT =>
        ⟨star_count (by omega) c F hf i T hT,star_count (by omega) c F hf j T hT⟩)
      X.val I X.property hI
    have hm (a : Fin (k+1)) : X.val ∈ F a ↔ c X = a := by
      rw [hf]; exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨X.property,h⟩⟩
    simpa only [hm] using u
  let comp (X : V) : V := ⟨X.valᶜ,by rw [card_compl,Fintype.card_fin,X.property]; omega⟩
  have opp (X : V) (i j : Fin (k+1)) :
      ((if c (comp X) = i then (1:ℤ) else 0) - (if c (comp X) = j then 1 else 0)) =
      (-1 : ℤ) ^ k * ((if c X = i then 1 else 0) - (if c X = j then 1 else 0)) := by
    simpa only [empty_trace c F hf,card_empty,Nat.sub_zero,comp] using
      htr X ∅ (empty_subset _) i j
  obtain ⟨S,_,hS⟩ := exists_subset_card_eq (s := (univ : Finset (Fin (2*k)))) (n:=k) (by simp; omega)
  let A : V := ⟨S,hS⟩
  rcases Nat.even_or_odd k with he | ho
  · have antipodal (X : V) : c (comp X) = c X := by
      by_contra h
      have u := opp X (c (comp X)) (c X)
      simp [h,Ne.symm h,he.neg_one_pow] at u
    let G (i : Fin (k+1)) := (F i).filter (fun B => k ≤ 2*(A.val ∩ B).card)
    apply half k hk he A.val A.property
    refine ⟨G,c A,mem_filter.mpr ⟨(hf _ _).2 ⟨A.property,rfl⟩,by simp [A,hS]; omega⟩,
      ?_,?_,?_,?_,?_⟩
    · intro i B hB
      exact ⟨((hf i B).1 (mem_filter.mp hB).1).choose,(mem_filter.mp hB).2⟩
    · intro B hc hcap
      refine ⟨c ⟨B,hc⟩,mem_filter.mpr ⟨(hf _ _).2 ⟨hc,rfl⟩,hcap⟩,?_⟩
      intro i hi
      exact ((hf i B).1 (mem_filter.mp hi).1).choose_spec.symm
    · intro i B C hB hC hadj
      obtain ⟨hb,hbi⟩ := (hf _ _).1 (mem_filter.mp hB).1
      obtain ⟨hc,hci⟩ := (hf _ _).1 (mem_filter.mp hC).1
      exact c.valid (show (johnson (2*k) k).Adj ⟨B,hb⟩ ⟨C,hc⟩ from hadj) (hbi.trans hci.symm)
    · intro i B hB heq
      obtain ⟨hb,hbi⟩ := (hf _ _).1 (mem_filter.mp hB).1
      let X : V := ⟨B,hb⟩
      refine mem_filter.mpr ⟨(hf _ _).2 ⟨(comp X).property,(antipodal X).trans hbi⟩,?_⟩
      have ht : A.val ∩ Bᶜ = A.val \ (A.val ∩ B) := by ext x; simp
      rw [ht,card_sdiff_of_subset inter_subset_left,A.property]; omega
    · intro I hI hcap i j
      have eqf (a : Fin (k+1)) : (G a).filter (fun B => A.val ∩ B = I) =
          (F a).filter (fun B => A.val ∩ B = I) := by
        ext B
        simp only [G,mem_filter]
        exact ⟨fun h => ⟨h.1.1,h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ hcap⟩,h.2⟩⟩
      rw [eqf,eqf]; exact htr A I hI i j
  · obtain ⟨b,hb⟩ : ∃ b : Fin (k+1), b ∉ ({c A,c (comp A)} : Finset _) := by
      by_contra! hall
      have heq : ({c A,c (comp A)} : Finset _) = univ := eq_univ_iff_forall.mpr hall
      have hle : ({c A,c (comp A)} : Finset _).card ≤ 2 := card_le_two
      rw [heq,card_univ,Fintype.card_fin] at hle; omega
    have hA : c A ≠ b := fun h => hb (h ▸ mem_insert_self _ _)
    have hC : c (comp A) ≠ b := fun h => hb (h ▸ mem_insert_of_mem (mem_singleton_self _))
    have u := opp A (c A) b
    rw [ho.neg_one_pow] at u
    split_ifs at u <;> omega

end OMA.R_Erdos835_johnson_chromaticNumber_R2
