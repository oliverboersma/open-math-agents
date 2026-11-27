import FormalConjectures.GreensOpenProblems.«70»

open scoped Finset

namespace Green70

/-! ### Part 1: 2D orientation, collinearity, and planar convex independence -/

private def orient (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

private lemma orient_self_left (a b : ℝ × ℝ) : orient a a b = 0 := by
  unfold orient; ring

private lemma orient_self_right (a b : ℝ × ℝ) : orient a b b = 0 := by
  unfold orient; ring

private lemma orient_self_mid (a b : ℝ × ℝ) : orient a b a = 0 := by
  unfold orient; ring

private lemma orient_swap_bc (a b c : ℝ × ℝ) : orient a c b = -orient a b c := by
  unfold orient; ring

private lemma orient_cyclic (a b c : ℝ × ℝ) : orient a b c = orient b c a := by
  unfold orient; ring

private lemma orient_add_smul (u v x y : ℝ × ℝ) (a b : ℝ) (hab : a + b = 1) :
    orient u v (a • x + b • y) = a * orient u v x + b * orient u v y := by
  have hb : b = 1 - a := by linarith
  subst hb
  unfold orient
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
  ring

private lemma convex_orient_le (u v : ℝ × ℝ) (c : ℝ) :
    Convex ℝ {x : ℝ × ℝ | orient u v x ≤ c} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  rw [orient_add_smul u v x y a b hab]
  have h1 : a * orient u v x ≤ a * c := mul_le_mul_of_nonneg_left hx ha
  have h2 : b * orient u v y ≤ b * c := mul_le_mul_of_nonneg_left hy hb
  linarith [show a * c + b * c = c by linear_combination c * hab]

private lemma convex_orient_ge (u v : ℝ × ℝ) (c : ℝ) :
    Convex ℝ {x : ℝ × ℝ | c ≤ orient u v x} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  rw [orient_add_smul u v x y a b hab]
  have h1 : a * c ≤ a * orient u v x := mul_le_mul_of_nonneg_left hx ha
  have h2 : b * c ≤ b * orient u v y := mul_le_mul_of_nonneg_left hy hb
  linarith [show a * c + b * c = c by linear_combination c * hab]

private lemma convex_orient_lt (u v : ℝ × ℝ) (c : ℝ) :
    Convex ℝ {x : ℝ × ℝ | orient u v x < c} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  rw [orient_add_smul u v x y a b hab]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb' : b = 1 := by linarith
    subst hb'; linarith
  · have h1 : a * orient u v x < a * c := mul_lt_mul_of_pos_left hx ha'
    have h2 : b * orient u v y ≤ b * c := mul_le_mul_of_nonneg_left hy.le hb
    linarith [show a * c + b * c = c by linear_combination c * hab]

private lemma convex_orient_gt (u v : ℝ × ℝ) (c : ℝ) :
    Convex ℝ {x : ℝ × ℝ | c < orient u v x} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  rw [orient_add_smul u v x y a b hab]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb' : b = 1 := by linarith
    subst hb'; linarith
  · have h1 : a * c < a * orient u v x := mul_lt_mul_of_pos_left hx ha'
    have h2 : b * c ≤ b * orient u v y := mul_le_mul_of_nonneg_left hy.le hb
    linarith [show a * c + b * c = c by linear_combination c * hab]

private lemma orient_le_of_mem_convexHull {S : Set (ℝ × ℝ)} {u v x : ℝ × ℝ} {c : ℝ}
    (hx : x ∈ convexHull ℝ S) (hS : ∀ y ∈ S, orient u v y ≤ c) : orient u v x ≤ c :=
  convexHull_min hS (convex_orient_le u v c) hx

private lemma orient_ge_of_mem_convexHull {S : Set (ℝ × ℝ)} {u v x : ℝ × ℝ} {c : ℝ}
    (hx : x ∈ convexHull ℝ S) (hS : ∀ y ∈ S, c ≤ orient u v y) : c ≤ orient u v x :=
  convexHull_min hS (convex_orient_ge u v c) hx

private lemma orient_lt_of_mem_convexHull {S : Set (ℝ × ℝ)} {u v x : ℝ × ℝ} {c : ℝ}
    (hx : x ∈ convexHull ℝ S) (hS : ∀ y ∈ S, orient u v y < c) : orient u v x < c :=
  convexHull_min hS (convex_orient_lt u v c) hx

private lemma orient_gt_of_mem_convexHull {S : Set (ℝ × ℝ)} {u v x : ℝ × ℝ} {c : ℝ}
    (hx : x ∈ convexHull ℝ S) (hS : ∀ y ∈ S, c < orient u v y) : c < orient u v x :=
  convexHull_min hS (convex_orient_gt u v c) hx

private lemma collinear_of_orient_eq_zero {S : Set (ℝ × ℝ)} {a b : ℝ × ℝ} (hab : a ≠ b)
    (h : ∀ x ∈ S, orient a b x = 0) : Collinear ℝ S := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨a, b - a, fun x hx => ?_⟩
  have ho := h x hx
  unfold orient at ho
  by_cases h1 : b.1 - a.1 ≠ 0
  · refine ⟨(x.1 - a.1) / (b.1 - a.1), ?_⟩
    ext
    · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
      rw [div_mul_cancel₀ _ h1]; ring
    · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
      field_simp
      linear_combination ho
  · push_neg at h1
    have h2 : b.2 - a.2 ≠ 0 := by
      intro h2
      apply hab
      ext <;> linarith
    refine ⟨(x.2 - a.2) / (b.2 - a.2), ?_⟩
    ext
    · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
      have hx1 : (b.2 - a.2) * (x.1 - a.1) = 0 := by
        rw [h1] at ho; linarith
      have hx2 : x.1 - a.1 = 0 := (mul_eq_zero.mp hx1).resolve_left h2
      rw [h1]; linarith
    · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
      rw [div_mul_cancel₀ _ h2]; ring

private lemma orient_eq_zero_of_collinear {a b c : ℝ × ℝ}
    (h : Collinear ℝ ({a, b, c} : Set (ℝ × ℝ))) : orient a b c = 0 := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h
  obtain ⟨p₀, v, hv⟩ := h
  obtain ⟨ra, hra⟩ := hv a (by simp)
  obtain ⟨rb, hrb⟩ := hv b (by simp)
  obtain ⟨rc, hrc⟩ := hv c (by simp)
  rw [hra, hrb, hrc]
  unfold orient
  simp only [vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

private lemma convexIndependent_range_of_cyclic_orient {m : ℕ} (hm : 3 ≤ m) (p : Fin m → ℝ × ℝ)
    (ho : ∀ i j k : Fin m, i < j → j < k → 0 < orient (p i) (p j) (p k)) :
    ConvexIndependent ℝ ((↑) : ↥(Set.range p) → ℝ × ℝ) := by
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff]
  rintro _ ⟨t, rfl⟩ ht0'
  have ht : p t ∈ convexHull ℝ (p '' ({t}ᶜ : Set (Fin m))) := by
    refine convexHull_mono ?_ ht0'
    rintro x ⟨⟨j, rfl⟩, hxj⟩
    exact ⟨j, fun h => hxj (by rw [Set.mem_singleton_iff, show j = t from h]), rfl⟩
  by_cases ht0 : t.1 = 0
  · let u := p ⟨1, by omega⟩
    let v := p ⟨m - 1, by omega⟩
    have hpt : 0 < orient u v (p t) := by
      dsimp only [u, v]
      rw [orient_cyclic, orient_cyclic]
      exact ho t ⟨1, by omega⟩ ⟨m - 1, by omega⟩ (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
    have hle : orient u v (p t) ≤ 0 := by
      refine orient_le_of_mem_convexHull ht ?_
      rintro _ ⟨j, hj, rfl⟩
      have hjne : j.1 ≠ 0 := fun h => hj (Fin.ext (by omega))
      by_cases hj1 : j.1 = 1
      · have : j = ⟨1, by omega⟩ := Fin.ext hj1; rw [this]; dsimp only [u]; rw [orient_self_mid]
      · by_cases hjm : j.1 = m - 1
        · have : j = ⟨m - 1, by omega⟩ := Fin.ext hjm; rw [this]; dsimp only [v]; rw [orient_self_right]
        · have hpos := ho ⟨1, by omega⟩ j ⟨m - 1, by omega⟩
            (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
          dsimp only [u, v]; rw [orient_swap_bc] at hpos; linarith
    linarith
  · by_cases htm : t.1 = m - 1
    · let u := p ⟨0, by omega⟩
      let v := p ⟨m - 2, by omega⟩
      have hpt : 0 < orient u v (p t) := by
        dsimp only [u, v]
        exact ho ⟨0, by omega⟩ ⟨m - 2, by omega⟩ t (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
      have hle : orient u v (p t) ≤ 0 := by
        refine orient_le_of_mem_convexHull ht ?_
        rintro _ ⟨j, hj, rfl⟩
        have hjne : j.1 ≠ m - 1 := fun h => hj (Fin.ext (by omega))
        by_cases hj0 : j.1 = 0
        · have : j = ⟨0, by omega⟩ := Fin.ext hj0; rw [this]; dsimp only [u]; rw [orient_self_mid]
        · by_cases hjm2 : j.1 = m - 2
          · have : j = ⟨m - 2, by omega⟩ := Fin.ext hjm2; rw [this]; dsimp only [v]; rw [orient_self_right]
          · have hpos := ho ⟨0, by omega⟩ j ⟨m - 2, by omega⟩
              (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
            dsimp only [u, v]; rw [orient_swap_bc] at hpos; linarith
      linarith
    · let u := p ⟨t.1 + 1, by omega⟩
      let v := p ⟨t.1 - 1, by omega⟩
      have hpt : 0 < orient u v (p t) := by
        dsimp only [u, v]
        rw [orient_cyclic]
        exact ho ⟨t.1 - 1, by omega⟩ t ⟨t.1 + 1, by omega⟩
          (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
      have hle : orient u v (p t) ≤ 0 := by
        refine orient_le_of_mem_convexHull ht ?_
        rintro _ ⟨j, hj, rfl⟩
        have hjne : j.1 ≠ t.1 := fun h => hj (Fin.ext h)
        by_cases hjm : j.1 = t.1 - 1
        · have : j = ⟨t.1 - 1, by omega⟩ := Fin.ext hjm; rw [this]; dsimp only [v]; rw [orient_self_right]
        · by_cases hjp : j.1 = t.1 + 1
          · have : j = ⟨t.1 + 1, by omega⟩ := Fin.ext hjp; rw [this]; dsimp only [u]; rw [orient_self_mid]
          · rcases lt_or_gt_of_ne hjne with hlt | hgt
            · have hpos := ho j ⟨t.1 - 1, by omega⟩ ⟨t.1 + 1, by omega⟩
                (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
              dsimp only [u, v]; rw [orient_cyclic, orient_cyclic, orient_swap_bc] at hpos; linarith
            · have hpos := ho ⟨t.1 - 1, by omega⟩ ⟨t.1 + 1, by omega⟩ j
                (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
              dsimp only [u, v]; rw [orient_cyclic, orient_swap_bc] at hpos; linarith
      linarith

/- ### Part 2: Erdős–Szekeres Cups-and-Caps + Perturbation to General Position -/

private lemma orient_trans_right (p q r s : ℝ × ℝ) :
    (r.1 - q.1) * orient p q s = (s.1 - q.1) * orient p q r + (q.1 - p.1) * orient q r s := by
  unfold orient; ring

private lemma orient_trans_left (p q r s : ℝ × ℝ) :
    (r.1 - q.1) * orient p r s = (r.1 - p.1) * orient q r s + (s.1 - r.1) * orient p q r := by
  unfold orient; ring

private def IsCup (L : List (ℝ × ℝ)) : Prop :=
  L.Pairwise (fun a b => a.1 < b.1) ∧
    ∀ i j k (hi : i < L.length) (hj : j < L.length) (hk : k < L.length),
      i < j → j < k → 0 < orient L[i] L[j] L[k]

private def IsCap (L : List (ℝ × ℝ)) : Prop :=
  L.Pairwise (fun a b => a.1 < b.1) ∧
    ∀ i j k (hi : i < L.length) (hj : j < L.length) (hk : k < L.length),
      i < j → j < k → orient L[i] L[j] L[k] < 0

private lemma isCup_append_singleton {L : List (ℝ × ℝ)} {q : ℝ × ℝ}
    (hL : IsCup L) (hlen : 2 ≤ L.length)
    (hx : L[L.length - 1].1 < q.1)
    (ho : 0 < orient L[L.length - 2] L[L.length - 1] q) :
    IsCup (L ++ [q]) := by
  have hpw := List.pairwise_iff_getElem.mp hL.1
  constructor
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.length_append, List.length_singleton] at hi hj
    by_cases hj' : j < L.length
    · have hi' : i < L.length := by omega
      simp only [List.getElem_append_left hi', List.getElem_append_left hj']
      exact hpw i j hi' hj' hij
    · have hjeq : j = L.length := by omega
      have hi' : i < L.length := by omega
      subst hjeq
      simp only [List.getElem_append_left hi', List.getElem_append_right le_rfl, Nat.sub_self,
        List.getElem_singleton]
      by_cases hil : i = L.length - 1
      · subst hil; exact hx
      · exact lt_trans (hpw i (L.length - 1) hi' (by omega) (by omega)) hx
  · intro i j k hi hj hk hij hjk
    rw [List.length_append, List.length_singleton] at hi hj hk
    by_cases hk' : k < L.length
    · have hi' : i < L.length := by omega
      have hj' : j < L.length := by omega
      simp only [List.getElem_append_left hi', List.getElem_append_left hj',
        List.getElem_append_left hk']
      exact hL.2 i j k hi' hj' hk' hij hjk
    · have hkeq : k = L.length := by omega
      have hi' : i < L.length := by omega
      have hj' : j < L.length := by omega
      subst hkeq
      simp only [List.getElem_append_left hi', List.getElem_append_left hj',
        List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton]
      by_cases hjl : j = L.length - 1
      · subst hjl
        by_cases hil : i = L.length - 2
        · subst hil; exact ho
        · have h1 := hL.2 i (L.length - 2) (L.length - 1) hi' (by omega) (by omega) (by omega) (by omega)
          have hx1 := hpw i (L.length - 2) hi' (by omega) (by omega)
          have hx2 := hpw (L.length - 2) (L.length - 1) (by omega) (by omega) (by omega)
          have hid := orient_trans_left L[i] L[L.length - 2] L[L.length - 1] q
          nlinarith
      · have h1 := hL.2 i j (L.length - 1) hi' hj' (by omega) hij (by omega)
        have h2 : 0 < orient L[j] L[L.length - 1] q := by
          by_cases hj2 : j = L.length - 2
          · subst hj2; exact ho
          · have h2a := hL.2 j (L.length - 2) (L.length - 1) hj' (by omega) (by omega) (by omega) (by omega)
            have hx1 := hpw j (L.length - 2) hj' (by omega) (by omega)
            have hx2 := hpw (L.length - 2) (L.length - 1) (by omega) (by omega) (by omega)
            have hid := orient_trans_left L[j] L[L.length - 2] L[L.length - 1] q
            nlinarith
        have hx1 := hpw i j hi' hj' hij
        have hx2 := hpw j (L.length - 1) hj' (by omega) (by omega)
        have hid := orient_trans_right L[i] L[j] L[L.length - 1] q
        nlinarith

private lemma isCap_cons {r : ℝ × ℝ} {L : List (ℝ × ℝ)}
    (hL : IsCap L) (hlen : 2 ≤ L.length)
    (hx : r.1 < L[0].1)
    (ho : orient r L[0] L[1] < 0) :
    IsCap (r :: L) := by
  have hpw := List.pairwise_iff_getElem.mp hL.1
  constructor
  · rw [List.pairwise_cons]
    refine ⟨fun x hx' => ?_, hL.1⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx'
    by_cases hj0 : j = 0
    · subst hj0; exact hx
    · exact lt_trans hx (hpw 0 j (by omega) hj (by omega))
  · intro i j k hi hj hk hij hjk
    cases i with
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        cases k with
        | zero => omega
        | succ k' =>
          simp only [List.getElem_cons_succ]
          exact hL.2 i' j' k' (by simpa using hi) (by simpa using hj) (by simpa using hk)
            (by omega) (by omega)
    | zero =>
      cases j with
      | zero => omega
      | succ j' =>
        cases k with
        | zero => omega
        | succ k' =>
          simp only [List.getElem_cons_zero, List.getElem_cons_succ]
          have hj' : j' < L.length := by simpa using hj
          have hk' : k' < L.length := by simpa using hk
          by_cases hj0 : j' = 0
          · subst hj0
            by_cases hk1 : k' = 1
            · subst hk1; exact ho
            · have h1 := hL.2 0 1 k' (by omega) (by omega) hk' (by omega) (by omega)
              have hx1 := hpw 0 1 (by omega) (by omega) (by omega)
              have hx2 := hpw 1 k' (by omega) hk' (by omega)
              have hid := orient_trans_right r L[0] L[1] L[k']
              nlinarith
          · have h1 : orient r L[0] L[j'] < 0 := by
              by_cases hj1 : j' = 1
              · subst hj1; exact ho
              · have h1a := hL.2 0 1 j' (by omega) (by omega) hj' (by omega) (by omega)
                have hx1 := hpw 0 1 (by omega) (by omega) (by omega)
                have hx2 := hpw 1 j' (by omega) hj' (by omega)
                have hid := orient_trans_right r L[0] L[1] L[j']
                nlinarith
            have h2 := hL.2 0 j' k' (by omega) hj' hk' (by omega) (by omega)
            have hx1 := hpw 0 j' (by omega) hj' (by omega)
            have hx2 := hpw j' k' hj' hk' (by omega)
            have hid := orient_trans_left r L[0] L[j'] L[k']
            nlinarith

private def esNum (a b : ℕ) : ℕ := (a + b - 4).choose (a - 2) + 1

private lemma cups_caps (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∀ P : Finset (ℝ × ℝ), esNum a b ≤ #P →
      (∀ p ∈ P, ∀ q ∈ P, p ≠ q → p.1 ≠ q.1) →
      (∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P, p ≠ q → q ≠ r → p ≠ r → orient p q r ≠ 0) →
      (∃ L : List (ℝ × ℝ), L.length = a ∧ (∀ x ∈ L, x ∈ P) ∧ IsCup L) ∨
      (∃ L : List (ℝ × ℝ), L.length = b ∧ (∀ x ∈ L, x ∈ P) ∧ IsCap L) := by
  induction hn : a + b using Nat.strong_induction_on generalizing a b with
  | h s ih =>
    intro P hP hdx hnc
    by_cases ha2 : a = 2
    · left
      have hcard : 2 ≤ #P := by
        have : 1 ≤ (a + b - 4).choose (a - 2) := by
          rw [ha2]; simp
        unfold esNum at hP; omega
      obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < #P)
      rcases lt_or_gt_of_ne (hdx p hp q hq hpq) with hlt | hgt
      · refine ⟨[p, q], by simp [ha2], by simp [hp, hq], ?_, ?_⟩
        · simp [hlt]
        · intro i j k hi hj hk hij hjk; simp at hk; omega
      · refine ⟨[q, p], by simp [ha2], by simp [hp, hq], ?_, ?_⟩
        · simp [hgt]
        · intro i j k hi hj hk hij hjk; simp at hk; omega
    · by_cases hb2 : b = 2
      · right
        have hcard : 2 ≤ #P := by
          have : 1 ≤ (a + b - 4).choose (a - 2) := by
            rw [hb2]
            have : a + 2 - 4 = a - 2 := by omega
            rw [this, Nat.choose_self]
          unfold esNum at hP; omega
        obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < #P)
        rcases lt_or_gt_of_ne (hdx p hp q hq hpq) with hlt | hgt
        · refine ⟨[p, q], by simp [hb2], by simp [hp, hq], ?_, ?_⟩
          · simp [hlt]
          · intro i j k hi hj hk hij hjk; simp at hk; omega
        · refine ⟨[q, p], by simp [hb2], by simp [hp, hq], ?_, ?_⟩
          · simp [hgt]
          · intro i j k hi hj hk hij hjk; simp at hk; omega
      · have ha3 : 3 ≤ a := by omega
        have hb3 : 3 ≤ b := by omega
        classical
        let E : Finset (ℝ × ℝ) := P.filter fun p =>
          ∃ L : List (ℝ × ℝ), L.length = a - 1 ∧ (∀ x ∈ L, x ∈ P) ∧ IsCup L ∧
            ∃ (h : L.length - 1 < L.length), L[L.length - 1] = p
        by_cases hPE : esNum (a - 1) b ≤ #(P \ E)
        · have hsub := ih (a - 1 + b) (by omega) (a - 1) b (by omega) hb rfl (P \ E) hPE
            (fun p hp q hq => hdx p (Finset.mem_sdiff.mp hp).1 q (Finset.mem_sdiff.mp hq).1)
            (fun p hp q hq r hr => hnc p (Finset.mem_sdiff.mp hp).1 q (Finset.mem_sdiff.mp hq).1
              r (Finset.mem_sdiff.mp hr).1)
          rcases hsub with ⟨L, hlen, hmem, hcup⟩ | ⟨L, hlen, hmem, hcap⟩
          · exfalso
            have hne : L.length - 1 < L.length := by omega
            have hlast_mem : L[L.length - 1] ∈ P \ E := hmem _ (List.getElem_mem hne)
            have hlast_E : L[L.length - 1] ∈ E := by
              rw [Finset.mem_filter]
              exact ⟨(Finset.mem_sdiff.mp hlast_mem).1, L, hlen,
                fun x hx => (Finset.mem_sdiff.mp (hmem x hx)).1, hcup, hne, rfl⟩
            exact (Finset.mem_sdiff.mp hlast_mem).2 hlast_E
          · exact Or.inr ⟨L, hlen, fun x hx => (Finset.mem_sdiff.mp (hmem x hx)).1, hcap⟩
        · have hE_card : esNum a (b - 1) ≤ #E := by
            have hsum : #(P \ E) + #E = #P := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ P)
            have hchoose : (a + b - 4).choose (a - 2) =
                (a - 1 + b - 4).choose (a - 1 - 2) + (a + (b - 1) - 4).choose (a - 2) := by
              have h1 : a + b - 4 = (a + b - 5) + 1 := by omega
              have h2 : a - 2 = (a - 3) + 1 := by omega
              have h3 : a - 1 + b - 4 = a + b - 5 := by omega
              have h4 : a - 1 - 2 = a - 3 := by omega
              have h5 : a + (b - 1) - 4 = a + b - 5 := by omega
              rw [h1, h2, h3, h4, h5, Nat.choose_succ_succ]
            unfold esNum at hP hPE ⊢
            omega
          have hsub := ih (a + (b - 1)) (by omega) a (b - 1) ha (by omega) rfl E hE_card
            (fun p hp q hq => hdx p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1)
            (fun p hp q hq r hr => hnc p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
              r (Finset.mem_filter.mp hr).1)
          rcases hsub with ⟨L, hlen, hmem, hcup⟩ | ⟨C, hClen, hCmem, hcap⟩
          · exact Or.inl ⟨L, hlen, fun x hx => (Finset.mem_filter.mp (hmem x hx)).1, hcup⟩
          · have hC2 : 2 ≤ C.length := by omega
            have hpE : C[0] ∈ E := hCmem _ (List.getElem_mem (by omega))
            obtain ⟨hpP, U, hUlen, hUmem, hUcup, hUlast_lt, hUlast⟩ := Finset.mem_filter.mp hpE
            have hU2 : 2 ≤ U.length := by omega
            have hpwU := List.pairwise_iff_getElem.mp hUcup.1
            have hpwC := List.pairwise_iff_getElem.mp hcap.1
            let r := U[U.length - 2]
            let p := C[0]
            let q := C[1]
            have hrP : r ∈ P := hUmem _ (List.getElem_mem (by omega))
            have hqP : q ∈ P := (Finset.mem_filter.mp (hCmem _ (List.getElem_mem (by omega)))).1
            have hrp_x : r.1 < p.1 := by
              dsimp only [r, p]
              rw [← hUlast]; exact hpwU (U.length - 2) (U.length - 1) (by omega) hUlast_lt (by omega)
            have hpq_x : p.1 < q.1 := hpwC 0 1 (by omega) (by omega) (by omega)
            have hrp : r ≠ p := fun h => ne_of_lt hrp_x (congrArg Prod.fst h)
            have hpq : p ≠ q := fun h => ne_of_lt hpq_x (congrArg Prod.fst h)
            have hrq : r ≠ q := fun h => ne_of_lt (lt_trans hrp_x hpq_x) (congrArg Prod.fst h)
            have hne0 := hnc r hrP p hpP q hqP hrp hpq hrq
            rcases lt_or_gt_of_ne hne0 with hneg | hpos
            · right
              refine ⟨r :: C, by simp [hClen]; omega, ?_, isCap_cons hcap hC2 hrp_x hneg⟩
              intro x hx
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · exact hrP
              · exact (Finset.mem_filter.mp (hCmem x hx)).1
            · left
              refine ⟨U ++ [q], by simp [hUlen]; omega, ?_, ?_⟩
              · intro x hx
                simp only [List.mem_append, List.mem_singleton] at hx
                rcases hx with hx | rfl
                · exact hUmem x hx
                · exact hqP
              · refine isCup_append_singleton hUcup hU2 ?_ ?_
                · rwa [hUlast]
                · rwa [hUlast]

private lemma exists_point_in_box_avoiding (p₀ : ℝ × ℝ) {ε : ℝ} (hε : 0 < ε)
    (S : Finset (ℝ × ℝ)) :
    ∃ q : ℝ × ℝ, |q.1 - p₀.1| < ε ∧ |q.2 - p₀.2| < ε ∧
      (∀ a ∈ S, q.1 ≠ a.1) ∧
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → orient a b q ≠ 0) := by
  classical
  have hIx : (Set.Ioo (p₀.1 - ε) (p₀.1 + ε)).Infinite := Set.Ioo_infinite (by linarith)
  obtain ⟨x, hxI, hxS⟩ := hIx.exists_notMem_finset (S.image Prod.fst)
  have hx_ne : ∀ a ∈ S, x ≠ a.1 := fun a ha h =>
    hxS (Finset.mem_image.mpr ⟨a, ha, h.symm⟩)
  let badY : Finset ℝ := (S ×ˢ S).image fun ab =>
    ab.1.2 + (ab.2.2 - ab.1.2) * (x - ab.1.1) / (ab.2.1 - ab.1.1)
  have hIy : (Set.Ioo (p₀.2 - ε) (p₀.2 + ε)).Infinite := Set.Ioo_infinite (by linarith)
  obtain ⟨y, hyI, hyS⟩ := hIy.exists_notMem_finset badY
  refine ⟨(x, y), abs_sub_lt_iff.mpr ⟨by linarith [hxI.2], by linarith [hxI.1]⟩,
    abs_sub_lt_iff.mpr ⟨by linarith [hyI.2], by linarith [hyI.1]⟩, hx_ne, ?_⟩
  intro a ha b hb hab ho
  unfold orient at ho
  by_cases h1 : b.1 - a.1 = 0
  · have h2 : b.2 - a.2 ≠ 0 := fun h2 => hab (Prod.ext (by linarith) (by linarith))
    have hxa : x - a.1 ≠ 0 := sub_ne_zero.mpr (hx_ne a ha)
    rw [h1] at ho
    have : (b.2 - a.2) * (x - a.1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h2 h
    · exact hxa h
  · have hy_eq : y = a.2 + (b.2 - a.2) * (x - a.1) / (b.1 - a.1) := by
      field_simp
      linear_combination ho
    exact hyS (Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, hy_eq.symm⟩)

private lemma orient_perturb_bound {a b c a' b' c' : ℝ × ℝ} {M ε : ℝ}
    (hM : 0 ≤ M) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ha : |a.1| ≤ M ∧ |a.2| ≤ M) (hb : |b.1| ≤ M ∧ |b.2| ≤ M) (hc : |c.1| ≤ M ∧ |c.2| ≤ M)
    (ha' : |a'.1 - a.1| ≤ ε ∧ |a'.2 - a.2| ≤ ε)
    (hb' : |b'.1 - b.1| ≤ ε ∧ |b'.2 - b.2| ≤ ε)
    (hc' : |c'.1 - c.1| ≤ ε ∧ |c'.2 - c.2| ≤ ε) :
    |orient a' b' c' - orient a b c| ≤ (16 * M + 16) * ε := by
  set u1 := b.1 - a.1; set u2 := b.2 - a.2
  set v1 := c.1 - a.1; set v2 := c.2 - a.2
  set du1 := (b'.1 - a'.1) - u1; set du2 := (b'.2 - a'.2) - u2
  set dv1 := (c'.1 - a'.1) - v1; set dv2 := (c'.2 - a'.2) - v2
  have hu1 : |u1| ≤ 2 * M := by
    calc |b.1 - a.1| ≤ |b.1| + |a.1| := abs_sub _ _
      _ ≤ 2 * M := by linarith [ha.1, hb.1]
  have hu2 : |u2| ≤ 2 * M := by
    calc |b.2 - a.2| ≤ |b.2| + |a.2| := abs_sub _ _
      _ ≤ 2 * M := by linarith [ha.2, hb.2]
  have hv1 : |v1| ≤ 2 * M := by
    calc |c.1 - a.1| ≤ |c.1| + |a.1| := abs_sub _ _
      _ ≤ 2 * M := by linarith [ha.1, hc.1]
  have hv2 : |v2| ≤ 2 * M := by
    calc |c.2 - a.2| ≤ |c.2| + |a.2| := abs_sub _ _
      _ ≤ 2 * M := by linarith [ha.2, hc.2]
  have hdu1 : |du1| ≤ 2 * ε := by
    have : du1 = (b'.1 - b.1) - (a'.1 - a.1) := by dsimp [du1, u1]; ring
    rw [this]; calc |(b'.1 - b.1) - (a'.1 - a.1)| ≤ |b'.1 - b.1| + |a'.1 - a.1| := abs_sub _ _
      _ ≤ 2 * ε := by linarith [ha'.1, hb'.1]
  have hdu2 : |du2| ≤ 2 * ε := by
    have : du2 = (b'.2 - b.2) - (a'.2 - a.2) := by dsimp [du2, u2]; ring
    rw [this]; calc |(b'.2 - b.2) - (a'.2 - a.2)| ≤ |b'.2 - b.2| + |a'.2 - a.2| := abs_sub _ _
      _ ≤ 2 * ε := by linarith [ha'.2, hb'.2]
  have hdv1 : |dv1| ≤ 2 * ε := by
    have : dv1 = (c'.1 - c.1) - (a'.1 - a.1) := by dsimp [dv1, v1]; ring
    rw [this]; calc |(c'.1 - c.1) - (a'.1 - a.1)| ≤ |c'.1 - c.1| + |a'.1 - a.1| := abs_sub _ _
      _ ≤ 2 * ε := by linarith [ha'.1, hc'.1]
  have hdv2 : |dv2| ≤ 2 * ε := by
    have : dv2 = (c'.2 - c.2) - (a'.2 - a.2) := by dsimp [dv2, v2]; ring
    rw [this]; calc |(c'.2 - c.2) - (a'.2 - a.2)| ≤ |c'.2 - c.2| + |a'.2 - a.2| := abs_sub _ _
      _ ≤ 2 * ε := by linarith [ha'.2, hc'.2]
  have hid : orient a' b' c' - orient a b c =
      (u1 * dv2 + du1 * v2 + du1 * dv2) - (u2 * dv1 + du2 * v1 + du2 * dv1) := by
    change ((b'.1 - a'.1) * (c'.2 - a'.2) - (b'.2 - a'.2) * (c'.1 - a'.1)) -
      ((b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)) = _
    have h1 : b'.1 - a'.1 = u1 + du1 := by dsimp [u1, du1]; ring
    have h2 : b'.2 - a'.2 = u2 + du2 := by dsimp [u2, du2]; ring
    have h3 : c'.1 - a'.1 = v1 + dv1 := by dsimp [v1, dv1]; ring
    have h4 : c'.2 - a'.2 = v2 + dv2 := by dsimp [v2, dv2]; ring
    rw [h1, h2, h3, h4]; ring
  rw [hid]
  have hm1 : |u1 * dv2| ≤ 4 * M * ε := by
    calc |u1 * dv2| = |u1| * |dv2| := abs_mul _ _
      _ ≤ (2 * M) * (2 * ε) := mul_le_mul hu1 hdv2 (abs_nonneg _) (by linarith)
      _ = 4 * M * ε := by ring
  have hm2 : |du1 * v2| ≤ 4 * M * ε := by
    calc |du1 * v2| = |du1| * |v2| := abs_mul _ _
      _ ≤ (2 * ε) * (2 * M) := mul_le_mul hdu1 hv2 (abs_nonneg _) (by linarith)
      _ = 4 * M * ε := by ring
  have hm3 : |du1 * dv2| ≤ 4 * ε := by
    calc |du1 * dv2| = |du1| * |dv2| := abs_mul _ _
      _ ≤ (2 * ε) * (2 * ε) := mul_le_mul hdu1 hdv2 (abs_nonneg _) (by linarith)
      _ ≤ (2 * 1) * (2 * ε) := by nlinarith
      _ = 4 * ε := by ring
  have hm4 : |u2 * dv1| ≤ 4 * M * ε := by
    calc |u2 * dv1| = |u2| * |dv1| := abs_mul _ _
      _ ≤ (2 * M) * (2 * ε) := mul_le_mul hu2 hdv1 (abs_nonneg _) (by linarith)
      _ = 4 * M * ε := by ring
  have hm5 : |du2 * v1| ≤ 4 * M * ε := by
    calc |du2 * v1| = |du2| * |v1| := abs_mul _ _
      _ ≤ (2 * ε) * (2 * M) := mul_le_mul hdu2 hv1 (abs_nonneg _) (by linarith)
      _ = 4 * M * ε := by ring
  have hm6 : |du2 * dv1| ≤ 4 * ε := by
    calc |du2 * dv1| = |du2| * |dv1| := abs_mul _ _
      _ ≤ (2 * ε) * (2 * ε) := mul_le_mul hdu2 hdv1 (abs_nonneg _) (by linarith)
      _ ≤ (2 * 1) * (2 * ε) := by nlinarith
      _ = 4 * ε := by ring
  have hA : |u1 * dv2 + du1 * v2 + du1 * dv2| ≤ (8 * M + 4) * ε := by
    calc |u1 * dv2 + du1 * v2 + du1 * dv2|
        ≤ |u1 * dv2 + du1 * v2| + |du1 * dv2| := abs_add_le _ _
      _ ≤ (|u1 * dv2| + |du1 * v2|) + |du1 * dv2| := by linarith [abs_add_le (u1 * dv2) (du1 * v2)]
      _ ≤ (8 * M + 4) * ε := by linarith
  have hB : |u2 * dv1 + du2 * v1 + du2 * dv1| ≤ (8 * M + 4) * ε := by
    calc |u2 * dv1 + du2 * v1 + du2 * dv1|
        ≤ |u2 * dv1 + du2 * v1| + |du2 * dv1| := abs_add_le _ _
      _ ≤ (|u2 * dv1| + |du2 * v1|) + |du2 * dv1| := by linarith [abs_add_le (u2 * dv1) (du2 * v1)]
      _ ≤ (8 * M + 4) * ε := by linarith
  calc |(u1 * dv2 + du1 * v2 + du1 * dv2) - (u2 * dv1 + du2 * v1 + du2 * dv1)|
      ≤ |u1 * dv2 + du1 * v2 + du1 * dv2| + |u2 * dv1 + du2 * v1 + du2 * dv1| := abs_sub _ _
    _ ≤ (16 * M + 16) * ε := by linarith

private lemma exists_general_position_perturbation (P : Finset (ℝ × ℝ)) :
    ∃ f : (ℝ × ℝ) → (ℝ × ℝ),
      (∀ p ∈ P, ∀ q ∈ P, p ≠ q → (f p).1 ≠ (f q).1) ∧
      (∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P, p ≠ q → q ≠ r → p ≠ r → orient (f p) (f q) (f r) ≠ 0) ∧
      (∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P, 0 < orient p q r → 0 < orient (f p) (f q) (f r)) ∧
      (∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P, orient p q r < 0 → orient (f p) (f q) (f r) < 0) := by
  classical
  let M : ℝ := (P.image (fun p => max |p.1| |p.2|)).fold max 0 id
  have hM0 : 0 ≤ M := by
    have : ∀ (s : Finset ℝ), 0 ≤ s.fold max 0 id := by
      intro s; induction s using Finset.induction_on with
      | empty => simp
      | insert a s _ ih => simp only [Finset.fold_insert_idem, id_eq]; exact le_max_of_le_right ih
    exact this _
  have hM_bound : ∀ p ∈ P, |p.1| ≤ M ∧ |p.2| ≤ M := by
    intro p hp
    have hmem : max |p.1| |p.2| ∈ P.image (fun p => max |p.1| |p.2|) :=
      Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have hle : ∀ (s : Finset ℝ) (x : ℝ), x ∈ s → x ≤ s.fold max 0 id := by
      intro s x hx
      induction s using Finset.induction_on with
      | empty => simp at hx
      | insert a s _ ih =>
        simp only [Finset.mem_insert] at hx
        simp only [Finset.fold_insert_idem, id_eq]
        rcases hx with rfl | hx
        · exact le_max_left _ _
        · exact le_max_of_le_right (ih hx)
    have h := hle _ _ hmem
    exact ⟨le_trans (le_max_left _ _) h, le_trans (le_max_right _ _) h⟩
  let nonZeroOrients : Finset ℝ :=
    ((P ×ˢ P ×ˢ P).image (fun t => |orient t.1 t.2.1 t.2.2|)).filter (0 < ·)
  let δ : ℝ := if h : nonZeroOrients.Nonempty then nonZeroOrients.min' h else 1
  have hδ0 : 0 < δ := by
    dsimp [δ]
    split_ifs with h
    · exact (Finset.mem_filter.mp (Finset.min'_mem nonZeroOrients h)).2
    · norm_num
  have hδ_le : ∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P, orient p q r ≠ 0 → δ ≤ |orient p q r| := by
    intro p hp q hq r hr hne
    have hmem : |orient p q r| ∈ nonZeroOrients := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_image.mpr ⟨(p, q, r),
        Finset.mem_product.mpr ⟨hp, Finset.mem_product.mpr ⟨hq, hr⟩⟩, rfl⟩, abs_pos.mpr hne⟩
    have hne' : nonZeroOrients.Nonempty := ⟨_, hmem⟩
    dsimp [δ]
    rw [dif_pos hne']
    exact Finset.min'_le nonZeroOrients _ hmem
  let ε : ℝ := min 1 (δ / (32 * M + 32))
  have hε0 : 0 < ε := lt_min one_pos (div_pos hδ0 (by linarith))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε_bound : (16 * M + 16) * ε < δ := by
    have h1 : ε ≤ δ / (32 * M + 32) := min_le_right _ _
    have h2 : (16 * M + 16) * ε ≤ (16 * M + 16) * (δ / (32 * M + 32)) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 : (16 * M + 16) * (δ / (32 * M + 32)) = δ / 2 := by
      have hne : (32 * M + 32 : ℝ) ≠ 0 := by linarith
      field_simp; ring
    linarith
  -- Construct f by induction on any subset Q ⊆ P
  have hbuild : ∀ Q : Finset (ℝ × ℝ),
      ∃ f : (ℝ × ℝ) → (ℝ × ℝ),
        (∀ p ∈ Q, |((f p).1 - p.1)| < ε ∧ |((f p).2 - p.2)| < ε) ∧
        (∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → (f p).1 ≠ (f q).1) ∧
        (∀ p ∈ Q, ∀ q ∈ Q, ∀ r ∈ Q, p ≠ q → q ≠ r → p ≠ r → orient (f p) (f q) (f r) ≠ 0) := by
    intro Q
    induction Q using Finset.induction_on with
    | empty => exact ⟨id, by simp, by simp, by simp⟩
    | insert a Q ha ih =>
      obtain ⟨f, hf_close, hf_x, hf_nc⟩ := ih
      obtain ⟨q, hq1, hq2, hqx, hqnc⟩ := exists_point_in_box_avoiding a hε0 (Q.image f)
      let f' : (ℝ × ℝ) → (ℝ × ℝ) := fun x => if x = a then q else f x
      refine ⟨f', ?_, ?_, ?_⟩
      · intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hpQ
        · simp [f', hq1, hq2]
        · have hpa : p ≠ a := fun h => ha (h ▸ hpQ)
          simp only [f', if_neg hpa]
          exact hf_close p hpQ
      · intro p hp r hr hpr
        rcases Finset.mem_insert.mp hp with rfl | hpQ <;>
        rcases Finset.mem_insert.mp hr with rfl | hrQ
        · exact absurd rfl hpr
        · have hra : r ≠ p := fun h => ha (h ▸ hrQ)
          dsimp only [f']; rw [if_pos rfl, if_neg hra]
          exact hqx (f r) (Finset.mem_image.mpr ⟨r, hrQ, rfl⟩)
        · have hpa : p ≠ r := fun h => ha (h ▸ hpQ)
          dsimp only [f']; rw [if_neg hpa, if_pos rfl]
          exact (hqx (f p) (Finset.mem_image.mpr ⟨p, hpQ, rfl⟩)).symm
        · have hpa : p ≠ a := fun h => ha (h ▸ hpQ)
          have hra : r ≠ a := fun h => ha (h ▸ hrQ)
          simp only [f', if_neg hpa, if_neg hra]
          exact hf_x p hpQ r hrQ hpr
      · intro p hp r hr s hs hpr hrs hps
        have hcase : ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → orient (f u) (f v) q ≠ 0 := by
          intro u hu v hv huv
          have hne : f u ≠ f v := fun h => hf_x u hu v hv huv (congrArg Prod.fst h)
          exact hqnc (f u) (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
            (f v) (Finset.mem_image.mpr ⟨v, hv, rfl⟩) hne
        rcases Finset.mem_insert.mp hp with rfl | hpQ <;>
        rcases Finset.mem_insert.mp hr with rfl | hrQ <;>
        rcases Finset.mem_insert.mp hs with rfl | hsQ
        · exact absurd rfl hpr
        · exact absurd rfl hpr
        · exact absurd rfl hps
        · have hra : r ≠ p := fun h => ha (h ▸ hrQ)
          have hsa : s ≠ p := fun h => ha (h ▸ hsQ)
          dsimp only [f']; rw [if_pos rfl, if_neg hra, if_neg hsa]
          rw [orient_cyclic]; exact hcase r hrQ s hsQ hrs
        · exact absurd rfl hrs
        · have hpa : p ≠ r := fun h => ha (h ▸ hpQ)
          have hsa : s ≠ r := fun h => ha (h ▸ hsQ)
          dsimp only [f']; rw [if_neg hpa, if_pos rfl, if_neg hsa]
          rw [orient_cyclic, orient_cyclic]; exact hcase s hsQ p hpQ hps.symm
        · have hpa : p ≠ s := fun h => ha (h ▸ hpQ)
          have hra : r ≠ s := fun h => ha (h ▸ hrQ)
          dsimp only [f']; rw [if_neg hpa, if_neg hra, if_pos rfl]
          exact hcase p hpQ r hrQ hpr
        · have hpa : p ≠ a := fun h => ha (h ▸ hpQ)
          have hra : r ≠ a := fun h => ha (h ▸ hrQ)
          have hsa : s ≠ a := fun h => ha (h ▸ hsQ)
          simp only [f', if_neg hpa, if_neg hra, if_neg hsa]
          exact hf_nc p hpQ r hrQ s hsQ hpr hrs hps
  obtain ⟨f, hf_close, hf_x, hf_nc⟩ := hbuild P
  refine ⟨f, hf_x, hf_nc, ?_, ?_⟩
  · intro p hp q hq r hr ho
    have hbd := orient_perturb_bound hM0 hε0.le hε1 (hM_bound p hp) (hM_bound q hq) (hM_bound r hr)
      ⟨(hf_close p hp).1.le, (hf_close p hp).2.le⟩
      ⟨(hf_close q hq).1.le, (hf_close q hq).2.le⟩
      ⟨(hf_close r hr).1.le, (hf_close r hr).2.le⟩
    have hδp : δ ≤ orient p q r := by
      have := hδ_le p hp q hq r hr (ne_of_gt ho)
      rwa [abs_of_pos ho] at this
    linarith [(abs_sub_le_iff.mp hbd).2]
  · intro p hp q hq r hr ho
    have hbd := orient_perturb_bound hM0 hε0.le hε1 (hM_bound p hp) (hM_bound q hq) (hM_bound r hr)
      ⟨(hf_close p hp).1.le, (hf_close p hp).2.le⟩
      ⟨(hf_close q hq).1.le, (hf_close q hq).2.le⟩
      ⟨(hf_close r hr).1.le, (hf_close r hr).2.le⟩
    have hδp : δ ≤ -orient p q r := by
      have := hδ_le p hp q hq r hr (ne_of_lt ho)
      rwa [abs_of_neg ho] at this
    linarith [(abs_sub_le_iff.mp hbd).1]

/-- Non-strict convex position: a finite set `X` admits a cyclic ordering with `orient ≥ 0`. -/
private def InConvexPos (X : Finset (ℝ × ℝ)) : Prop :=
  ∃ p : Fin #X ≃ X, ∀ i j k : Fin #X, i < j → j < k → 0 ≤ orient (p i) (p j) (p k)

private lemma exists_inConvexPos (k : ℕ) (hk : 2 ≤ k) (P : Finset (ℝ × ℝ)) (hP : esNum k k ≤ #P) :
    ∃ X ⊆ P, #X = k ∧ InConvexPos X := by
  classical
  obtain ⟨f, hf_x, hf_nc, hf_pos, hf_neg⟩ := exists_general_position_perturbation P
  have hfinj : Set.InjOn f (P : Set (ℝ × ℝ)) := fun p hp q hq h => by
    by_contra hpq
    exact hf_x p hp q hq hpq (congrArg Prod.fst h)
  let P' := P.image f
  have hP'_card : esNum k k ≤ #P' := by
    rwa [Finset.card_image_of_injOn hfinj]
  have hP'_x : ∀ p ∈ P', ∀ q ∈ P', p ≠ q → p.1 ≠ q.1 := by
    intro p hp q hq hpq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    exact hf_x a ha b hb (fun h => hpq (congrArg f h))
  have hP'_nc : ∀ p ∈ P', ∀ q ∈ P', ∀ r ∈ P', p ≠ q → q ≠ r → p ≠ r → orient p q r ≠ 0 := by
    intro p hp q hq r hr hpq hqr hpr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hr
    exact hf_nc a ha b hb c hc (fun h => hpq (congrArg f h)) (fun h => hqr (congrArg f h))
      (fun h => hpr (congrArg f h))
  -- Helper: from a list L of length k in P' with pairwise distinct x-coords and orient > 0 (or < 0),
  -- pull back to X ⊆ P with InConvexPos X.
  have hpull : ∀ (L : List (ℝ × ℝ)), L.length = k → (∀ x ∈ L, x ∈ P') →
      L.Pairwise (fun a b => a.1 < b.1) →
      (∀ i j m (hi : i < L.length) (hj : j < L.length) (hm : m < L.length),
        i < j → j < m → 0 < orient L[i] L[j] L[m]) →
      ∃ X ⊆ P, #X = k ∧ InConvexPos X := by
    intro L hlen hmem hpw ho
    have hpre : ∀ i : Fin k, ∃ a ∈ P, f a = L[i.1]'(by omega) := fun i =>
      Finset.mem_image.mp (hmem _ (List.getElem_mem (by omega)))
    choose g hgP hgf using hpre
    have hginj : Function.Injective g := by
      intro i j hij
      by_contra hne
      have hpw' := List.pairwise_iff_getElem.mp hpw
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · have := hpw' i.1 j.1 (by omega) (by omega) hlt
        rw [← hgf i, ← hgf j, hij] at this; exact lt_irrefl _ this
      · have := hpw' j.1 i.1 (by omega) (by omega) hgt
        rw [← hgf i, ← hgf j, hij] at this; exact lt_irrefl _ this
    let X : Finset (ℝ × ℝ) := Finset.univ.image g
    have hXP : X ⊆ P := by
      intro x hx; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx; exact hgP i
    have hXcard : #X = k := by
      rw [Finset.card_image_of_injective _ hginj, Finset.card_fin]
    refine ⟨X, hXP, hXcard, ?_⟩
    let e : Fin #X ≃ X :=
      (finCongr hXcard).trans
        (Equiv.ofBijective (fun i : Fin k => (⟨g i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩ : X))
          ⟨fun i j h => hginj (congrArg Subtype.val h),
           fun ⟨x, hx⟩ => let ⟨i, _, hi⟩ := Finset.mem_image.mp hx; ⟨i, Subtype.ext hi⟩⟩)
    refine ⟨e, fun i j m hij hjm => ?_⟩
    by_contra hneg
    push Not at hneg
    have h1 := hf_neg _ (hgP ((finCongr hXcard) i)) _ (hgP ((finCongr hXcard) j)) _ (hgP ((finCongr hXcard) m)) hneg
    have h2 := ho i.1 j.1 m.1 (by omega) (by omega) (by omega) hij hjm
    rw [hgf, hgf, hgf] at h1
    simp only [finCongr_apply, Fin.val_cast] at h1
    linarith
  rcases cups_caps k k hk hk P' hP'_card hP'_x hP'_nc with ⟨L, hlen, hmem, hcup⟩ | ⟨L, hlen, hmem, hcap⟩
  · exact hpull L hlen hmem hcup.1 hcup.2
  · -- Reverse the cap to get orient > 0!
    have hrev_len : L.reverse.length = k := by simp [hlen]
    have hrev_mem : ∀ x ∈ L.reverse, x ∈ P' := fun x hx => hmem x (List.mem_reverse.mp hx)
    have hrev_pw : L.reverse.Pairwise (fun a b => b.1 < a.1) :=
      List.pairwise_reverse.mpr hcap.1
    have hpre : ∀ i : Fin k, ∃ a ∈ P, f a = L.reverse[i.1]'(by omega) := fun i =>
      Finset.mem_image.mp (hrev_mem _ (List.getElem_mem (by omega)))
    choose g hgP hgf using hpre
    have hginj : Function.Injective g := by
      intro i j hij
      by_contra hne
      have hpw' := List.pairwise_iff_getElem.mp hrev_pw
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · have := hpw' i.1 j.1 (by omega) (by omega) hlt
        rw [← hgf i, ← hgf j, hij] at this; exact lt_irrefl _ this
      · have := hpw' j.1 i.1 (by omega) (by omega) hgt
        rw [← hgf i, ← hgf j, hij] at this; exact lt_irrefl _ this
    let X : Finset (ℝ × ℝ) := Finset.univ.image g
    have hXP : X ⊆ P := by
      intro x hx; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx; exact hgP i
    have hXcard : #X = k := by
      rw [Finset.card_image_of_injective _ hginj, Finset.card_fin]
    refine ⟨X, hXP, hXcard, ?_⟩
    let e : Fin #X ≃ X :=
      (finCongr hXcard).trans
        (Equiv.ofBijective (fun i : Fin k => (⟨g i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩ : X))
          ⟨fun i j h => hginj (congrArg Subtype.val h),
           fun ⟨x, hx⟩ => let ⟨i, _, hi⟩ := Finset.mem_image.mp hx; ⟨i, Subtype.ext hi⟩⟩)
    refine ⟨e, fun i j m hij hjm => ?_⟩
    by_contra hneg
    push Not at hneg
    have h1 := hf_neg _ (hgP ((finCongr hXcard) i)) _ (hgP ((finCongr hXcard) j)) _ (hgP ((finCongr hXcard) m)) hneg
    rw [hgf, hgf, hgf] at h1
    simp only [finCongr_apply, Fin.val_cast, List.getElem_reverse] at h1
    have h2 := hcap.2 (L.length - 1 - m.1) (L.length - 1 - j.1) (L.length - 1 - i.1)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have hrev_orient : orient L[L.length - 1 - i.1] L[L.length - 1 - j.1] L[L.length - 1 - m.1] =
        -orient L[L.length - 1 - m.1] L[L.length - 1 - j.1] L[L.length - 1 - i.1] := by
      unfold orient; ring
    linarith

/- ### Part 3: Convex hull boundary, cyclic angle ordering, and layer size bound -/

private def IsBoundaryPt (Q : Finset (ℝ × ℝ)) (q : ℝ × ℝ) : Prop :=
  q ∈ Q ∧ ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ x ∈ Q, a * x.1 + b * x.2 ≤ a * q.1 + b * q.2

private noncomputable def hullBoundary (Q : Finset (ℝ × ℝ)) : Finset (ℝ × ℝ) :=
  by classical exact Q.filter fun q =>
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ x ∈ Q, a * x.1 + b * x.2 ≤ a * q.1 + b * q.2

private lemma mem_hullBoundary {Q : Finset (ℝ × ℝ)} {q : ℝ × ℝ} :
    q ∈ hullBoundary Q ↔ IsBoundaryPt Q q := by
  classical
  simp [hullBoundary, IsBoundaryPt]

private lemma hullBoundary_subset (Q : Finset (ℝ × ℝ)) : hullBoundary Q ⊆ Q := by
  classical
  exact Finset.filter_subset _ Q

private lemma hullBoundary_nonempty {Q : Finset (ℝ × ℝ)} (hQ : Q.Nonempty) :
    (hullBoundary Q).Nonempty := by
  obtain ⟨q, hqQ, hmax⟩ := Q.exists_max_image Prod.fst hQ
  refine ⟨q, mem_hullBoundary.mpr ⟨hqQ, 1, 0, Or.inl one_ne_zero, fun x hx => ?_⟩⟩
  simpa using hmax x hx

private abbrev IsStrictInterior (Q : Finset (ℝ × ℝ)) (z : ℝ × ℝ) : Prop :=
  ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → ∃ x ∈ Q, a * z.1 + b * z.2 < a * x.1 + b * x.2

private lemma isStrictInterior_of_not_mem_hullBoundary {Q : Finset (ℝ × ℝ)} {z : ℝ × ℝ}
    (hzQ : z ∈ Q) (hzB : z ∉ hullBoundary Q) :
    ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → ∃ x ∈ Q, a * z.1 + b * z.2 < a * x.1 + b * x.2 := by
  intro a b hab
  by_contra h
  push Not at h
  exact hzB (mem_hullBoundary.mpr ⟨hzQ, a, b, hab, h⟩)

private lemma isStrictInterior_centroid {Q : Finset (ℝ × ℝ)} {u v w : ℝ × ℝ}
    (hu : u ∈ Q) (hv : v ∈ Q) (hw : w ∈ Q) (ho : orient u v w ≠ 0) :
    let z : ℝ × ℝ := ((u.1 + v.1 + w.1) / 3, (u.2 + v.2 + w.2) / 3)
    ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → ∃ x ∈ Q, a * z.1 + b * z.2 < a * x.1 + b * x.2 := by
  intro z a b hab
  by_contra h
  push Not at h
  have h1 := h u hu
  have h2 := h v hv
  have h3 := h w hw
  have hsum : (a * u.1 + b * u.2) + (a * v.1 + b * v.2) + (a * w.1 + b * w.2) =
      3 * (a * z.1 + b * z.2) := by
    dsimp [z]; ring
  have heq1 : a * u.1 + b * u.2 = a * z.1 + b * z.2 := by linarith
  have heq2 : a * v.1 + b * v.2 = a * z.1 + b * z.2 := by linarith
  have heq3 : a * w.1 + b * w.2 = a * z.1 + b * z.2 := by linarith
  have hd1 : a * (v.1 - u.1) + b * (v.2 - u.2) = 0 := by linarith
  have hd2 : a * (w.1 - u.1) + b * (w.2 - u.2) = 0 := by linarith
  apply ho
  unfold orient
  rcases hab with ha | hb
  · have : a * ((v.1 - u.1) * (w.2 - u.2) - (v.2 - u.2) * (w.1 - u.1)) = 0 := by
      linear_combination (w.2 - u.2) * hd1 - (v.2 - u.2) * hd2
    exact (mul_eq_zero.mp this).resolve_left ha
  · have : b * ((v.1 - u.1) * (w.2 - u.2) - (v.2 - u.2) * (w.1 - u.1)) = 0 := by
      linear_combination (v.1 - u.1) * hd2 - (w.1 - u.1) * hd1
    exact (mul_eq_zero.mp this).resolve_left hb

private def toC (p : ℝ × ℝ) : ℂ := ⟨p.1, p.2⟩

private lemma toC_ne_zero_iff (p q : ℝ × ℝ) : toC (p - q) ≠ 0 ↔ p ≠ q := by
  constructor
  · intro h heq; apply h; subst heq; apply Complex.ext <;> simp [toC]
  · intro h heq; apply h
    have h1 := congrArg Complex.re heq
    have h2 := congrArg Complex.im heq
    simp [toC] at h1 h2
    exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)

private lemma orient_eq_norm_mul_sin_sub (z a b : ℝ × ℝ) (ha : a ≠ z) (hb : b ≠ z) :
    orient z a b =
      ‖toC (a - z)‖ * ‖toC (b - z)‖ *
        Real.sin (Complex.arg (toC (b - z)) - Complex.arg (toC (a - z))) := by
  have ha0 : toC (a - z) ≠ 0 := (toC_ne_zero_iff a z).mpr ha
  have hb0 : toC (b - z) ≠ 0 := (toC_ne_zero_iff b z).mpr hb
  have hre : ∀ u : ℝ × ℝ, u ≠ z → u.1 - z.1 = ‖toC (u - z)‖ * Real.cos (Complex.arg (toC (u - z))) := by
    intro u hu
    have hu0 : toC (u - z) ≠ 0 := (toC_ne_zero_iff u z).mpr hu
    rw [Complex.cos_arg hu0, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hu0)]
    rfl
  have him : ∀ u : ℝ × ℝ, u ≠ z → u.2 - z.2 = ‖toC (u - z)‖ * Real.sin (Complex.arg (toC (u - z))) := by
    intro u hu
    have hu0 : toC (u - z) ≠ 0 := (toC_ne_zero_iff u z).mpr hu
    rw [Complex.sin_arg, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hu0)]
    rfl
  have hac := hre a ha
  have has := him a ha
  have hbc := hre b hb
  have hbs := him b hb
  unfold orient
  rw [hac, has, hbc, hbs, Real.sin_sub]
  ring

private lemma orient_sum_four (z a b c : ℝ × ℝ) :
    orient a b c = orient z a b + orient z b c + orient z c a := by
  unfold orient; ring

private lemma cramer_2d (z a b c : ℝ × ℝ) :
    orient z a c • (b - z) = orient z b c • (a - z) + orient z a b • (c - z) := by
  ext <;> (unfold orient; simp; ring)

/-- Any interior point `z` strictly separates rays to distinct boundary points of `Q`, and sorting
    `hullBoundary Q` by `Complex.arg (q - z)` yields a valid `InConvexPos` cyclic ordering. -/
private lemma arg_injOn_hullBoundary {Q : Finset (ℝ × ℝ)} {z : ℝ × ℝ}
    (hz : ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → ∃ x ∈ Q, a * z.1 + b * z.2 < a * x.1 + b * x.2) :
    (∀ q ∈ hullBoundary Q, q ≠ z) ∧
    Set.InjOn (fun q => Complex.arg (toC (q - z))) (hullBoundary Q : Set (ℝ × ℝ)) := by
  have hne : ∀ q ∈ hullBoundary Q, q ≠ z := by
    intro q hq hqz
    obtain ⟨_, a, b, hab, hmax⟩ := mem_hullBoundary.mp hq
    obtain ⟨x, hxQ, hlt⟩ := hz a b hab
    subst hqz
    linarith [hmax x hxQ]
  refine ⟨hne, fun q₁ hq₁ q₂ hq₂ harg => ?_⟩
  by_contra h12
  have hne1 : q₁ ≠ z := hne q₁ hq₁
  have hne2 : q₂ ≠ z := hne q₂ hq₂
  have h01 : toC (q₁ - z) ≠ 0 := (toC_ne_zero_iff q₁ z).mpr hne1
  have h02 : toC (q₂ - z) ≠ 0 := (toC_ne_zero_iff q₂ z).mpr hne2
  have hr1 : 0 < ‖toC (q₁ - z)‖ := norm_pos_iff.mpr h01
  have hr2 : 0 < ‖toC (q₂ - z)‖ := norm_pos_iff.mpr h02
  have hprop : ∀ (p₁ p₂ : ℝ × ℝ), p₁ ∈ hullBoundary Q → p₂ ∈ hullBoundary Q →
      p₁ ≠ z → p₂ ≠ z → Complex.arg (toC (p₁ - z)) = Complex.arg (toC (p₂ - z)) →
      ‖toC (p₁ - z)‖ < ‖toC (p₂ - z)‖ → False := by
    intro p₁ p₂ hp₁ hp₂ hp1z hp2z ha hlt
    have hp10 : toC (p₁ - z) ≠ 0 := (toC_ne_zero_iff p₁ z).mpr hp1z
    have hp20 : toC (p₂ - z) ≠ 0 := (toC_ne_zero_iff p₂ z).mpr hp2z
    set t := ‖toC (p₁ - z)‖ / ‖toC (p₂ - z)‖
    have ht0 : 0 < t := div_pos (norm_pos_iff.mpr hp10) (norm_pos_iff.mpr hp20)
    have ht1 : t < 1 := (div_lt_one (norm_pos_iff.mpr hp20)).mpr hlt
    have hcomb : p₁ = (1 - t) • z + t • p₂ := by
      have hc1 : p₁.1 - z.1 = ‖toC (p₁ - z)‖ * Real.cos (Complex.arg (toC (p₁ - z))) := by
        rw [Complex.cos_arg hp10, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hp10)]; rfl
      have hc2 : p₂.1 - z.1 = ‖toC (p₂ - z)‖ * Real.cos (Complex.arg (toC (p₂ - z))) := by
        rw [Complex.cos_arg hp20, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hp20)]; rfl
      have hs1 : p₁.2 - z.2 = ‖toC (p₁ - z)‖ * Real.sin (Complex.arg (toC (p₁ - z))) := by
        rw [Complex.sin_arg, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hp10)]; rfl
      have hs2 : p₂.2 - z.2 = ‖toC (p₂ - z)‖ * Real.sin (Complex.arg (toC (p₂ - z))) := by
        rw [Complex.sin_arg, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hp20)]; rfl
      rw [ha] at hc1 hs1
      have hre : p₁.1 - z.1 = t * (p₂.1 - z.1) := by
        rw [hc1, hc2]; dsimp [t]; field_simp [norm_ne_zero_iff.mpr hp20]
      have him : p₁.2 - z.2 = t * (p₂.2 - z.2) := by
        rw [hs1, hs2]; dsimp [t]; field_simp [norm_ne_zero_iff.mpr hp20]
      ext <;> simp <;> linarith
    obtain ⟨_, a, b, hab, hmax⟩ := mem_hullBoundary.mp hp₁
    obtain ⟨x, hxQ, hzx⟩ := hz a b hab
    have hp2Q : p₂ ∈ Q := (mem_hullBoundary.mp hp₂).1
    have hL1 : a * p₁.1 + b * p₁.2 = (1 - t) * (a * z.1 + b * z.2) + t * (a * p₂.1 + b * p₂.2) := by
      rw [hcomb]; simp; ring
    have hLz : a * z.1 + b * z.2 < a * p₁.1 + b * p₁.2 := lt_of_lt_of_le hzx (hmax x hxQ)
    have hLp2 : a * p₂.1 + b * p₂.2 ≤ a * p₁.1 + b * p₁.2 := hmax p₂ hp2Q
    nlinarith
  rcases lt_trichotomy ‖toC (q₁ - z)‖ ‖toC (q₂ - z)‖ with hlt | heq | hgt
  · exact hprop q₁ q₂ hq₁ hq₂ hne1 hne2 harg hlt
  · apply h12
    dsimp only at harg
    have hre : q₁.1 - z.1 = ‖toC (q₁ - z)‖ * Real.cos (Complex.arg (toC (q₁ - z))) := by
      rw [Complex.cos_arg h01, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr h01)]; rfl
    have hre2 : q₂.1 - z.1 = ‖toC (q₂ - z)‖ * Real.cos (Complex.arg (toC (q₂ - z))) := by
      rw [Complex.cos_arg h02, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr h02)]; rfl
    have him : q₁.2 - z.2 = ‖toC (q₁ - z)‖ * Real.sin (Complex.arg (toC (q₁ - z))) := by
      rw [Complex.sin_arg, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr h01)]; rfl
    have him2 : q₂.2 - z.2 = ‖toC (q₂ - z)‖ * Real.sin (Complex.arg (toC (q₂ - z))) := by
      rw [Complex.sin_arg, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr h02)]; rfl
    rw [harg, heq] at hre him
    have hx : q₁.1 - z.1 = q₂.1 - z.1 := by linarith
    have hy : q₁.2 - z.2 = q₂.2 - z.2 := by linarith
    exact Prod.ext (by linarith) (by linarith)
  · exact hprop q₂ q₁ hq₂ hq₁ hne2 hne1 harg.symm hgt

/-- Ordering `hullBoundary Q` by increasing `Complex.arg (q - z)` gives `orient ≥ 0` on all
    increasing triples! -/
private lemma orient_nonneg_of_arg_lt {Q : Finset (ℝ × ℝ)} {z a b c : ℝ × ℝ}
    (hz : ∀ u v : ℝ, (u ≠ 0 ∨ v ≠ 0) → ∃ x ∈ Q, u * z.1 + v * z.2 < u * x.1 + v * x.2)
    (ha : a ∈ hullBoundary Q) (hb : b ∈ hullBoundary Q) (hc : c ∈ hullBoundary Q)
    (hab : Complex.arg (toC (a - z)) < Complex.arg (toC (b - z)))
    (hbc : Complex.arg (toC (b - z)) < Complex.arg (toC (c - z))) :
    0 ≤ orient a b c := by
  have ⟨hne, _⟩ := arg_injOn_hullBoundary hz
  have haz : a ≠ z := hne a ha
  have hbz : b ≠ z := hne b hb
  have hcz : c ≠ z := hne c hc
  set θa := Complex.arg (toC (a - z))
  set θb := Complex.arg (toC (b - z))
  set θc := Complex.arg (toC (c - z))
  have hθa_lo : -Real.pi < θa := Complex.neg_pi_lt_arg _
  have hθc_hi : θc ≤ Real.pi := Complex.arg_le_pi _
  -- Helper: if orient z p r > 0, orient z p q > 0, orient z q r > 0, and q ∈ hullBoundary Q,
  -- then orient p q r ≥ 0 (otherwise q is a strict convex combination of z, p, r).
  have hno_neg : ∀ (p q r : ℝ × ℝ), p ∈ hullBoundary Q → q ∈ hullBoundary Q → r ∈ hullBoundary Q →
      0 < orient z p r → 0 < orient z p q → 0 < orient z q r → 0 ≤ orient p q r := by
    intro p q r hp hq hr hpr hpq hqr
    by_contra hneg
    push Not at hneg
    have hsum : orient p q r = orient z p q + orient z q r - orient z p r := by
      rw [orient_sum_four z p q r, orient_swap_bc z r p]; ring
    have hlt1 : orient z p q + orient z q r < orient z p r := by linarith
    obtain ⟨_, u, v, huv, hmax⟩ := mem_hullBoundary.mp hq
    obtain ⟨x, hxQ, hzx⟩ := hz u v huv
    have hLz : u * z.1 + v * z.2 < u * q.1 + v * q.2 := lt_of_lt_of_le hzx (hmax x hxQ)
    have hLp : u * p.1 + v * p.2 ≤ u * q.1 + v * q.2 := hmax p (mem_hullBoundary.mp hp).1
    have hLr : u * r.1 + v * r.2 ≤ u * q.1 + v * q.2 := hmax r (mem_hullBoundary.mp hr).1
    have hcr := cramer_2d z p q r
    have hcr1 := congrArg Prod.fst hcr
    have hcr2 := congrArg Prod.snd hcr
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      smul_eq_mul] at hcr1 hcr2
    have hL : orient z p r * (u * q.1 + v * q.2 - (u * z.1 + v * z.2)) =
        orient z q r * (u * p.1 + v * p.2 - (u * z.1 + v * z.2)) +
        orient z p q * (u * r.1 + v * r.2 - (u * z.1 + v * z.2)) := by
      linear_combination u * hcr1 + v * hcr2
    nlinarith
  have hsin_pos : ∀ p q : ℝ × ℝ, p ≠ z → q ≠ z →
      0 < Complex.arg (toC (q - z)) - Complex.arg (toC (p - z)) →
      Complex.arg (toC (q - z)) - Complex.arg (toC (p - z)) < Real.pi →
      0 < orient z p q := by
    intro p q hp hq h1 h2
    rw [orient_eq_norm_mul_sin_sub z p q hp hq]
    have hp0 : 0 < ‖toC (p - z)‖ := norm_pos_iff.mpr ((toC_ne_zero_iff p z).mpr hp)
    have hq0 : 0 < ‖toC (q - z)‖ := norm_pos_iff.mpr ((toC_ne_zero_iff q z).mpr hq)
    exact mul_pos (mul_pos hp0 hq0) (Real.sin_pos_of_pos_of_lt_pi h1 h2)
  have hsin_neg : ∀ p q : ℝ × ℝ, p ≠ z → q ≠ z →
      Real.pi < Complex.arg (toC (q - z)) - Complex.arg (toC (p - z)) →
      Complex.arg (toC (q - z)) - Complex.arg (toC (p - z)) < 2 * Real.pi →
      orient z p q < 0 := by
    intro p q hp hq h1 h2
    rw [orient_eq_norm_mul_sin_sub z p q hp hq]
    have hp0 : 0 < ‖toC (p - z)‖ := norm_pos_iff.mpr ((toC_ne_zero_iff p z).mpr hp)
    have hq0 : 0 < ‖toC (q - z)‖ := norm_pos_iff.mpr ((toC_ne_zero_iff q z).mpr hq)
    have hs : Real.sin (Complex.arg (toC (q - z)) - Complex.arg (toC (p - z))) < 0 := by
      have := Real.sin_pos_of_pos_of_lt_pi (x := Complex.arg (toC (q - z)) - Complex.arg (toC (p - z)) - Real.pi)
        (by linarith) (by linarith)
      rw [Real.sin_sub_pi] at this; linarith
    nlinarith [mul_pos hp0 hq0]
  rcases lt_trichotomy (θc - θa) Real.pi with hca_lt | hca_eq | hca_gt
  · exact hno_neg a b c ha hb hc
      (hsin_pos a c haz hcz (by linarith) hca_lt)
      (hsin_pos a b haz hbz (by linarith) (by linarith))
      (hsin_pos b c hbz hcz (by linarith) (by linarith))
  · have ho_ca : orient z c a = 0 := by
      rw [orient_swap_bc, orient_eq_norm_mul_sin_sub z a c haz hcz]
      have : Complex.arg (toC (c - z)) - Complex.arg (toC (a - z)) = Real.pi := hca_eq
      rw [this, Real.sin_pi]; ring
    have ho_ab := hsin_pos a b haz hbz (by linarith) (by linarith)
    have ho_bc := hsin_pos b c hbz hcz (by linarith) (by linarith)
    rw [orient_sum_four z a b c, ho_ca]; linarith
  · have ho_ca : 0 < orient z c a := by
      rw [orient_swap_bc]
      have := hsin_neg a c haz hcz hca_gt (by linarith)
      linarith
    rcases lt_or_ge Real.pi (θb - θa) with hba_gt | hba_le
    · rw [orient_cyclic]
      have ho_ba : 0 < orient z b a := by
        rw [orient_swap_bc]
        linarith [hsin_neg a b haz hbz hba_gt (by linarith)]
      exact hno_neg b c a hb hc ha ho_ba
        (hsin_pos b c hbz hcz (by linarith) (by linarith)) ho_ca
    · rcases lt_or_ge Real.pi (θc - θb) with hcb_gt | hcb_le
      · rw [orient_cyclic, orient_cyclic]
        have ho_cb : 0 < orient z c b := by
          rw [orient_swap_bc]
          linarith [hsin_neg b c hbz hcz hcb_gt (by linarith)]
        exact hno_neg c a b hc ha hb ho_cb ho_ca
          (hsin_pos a b haz hbz (by linarith) (by linarith))
      · have ho_ab : 0 ≤ orient z a b := by
          rcases eq_or_lt_of_le hba_le with h | h
          · rw [orient_eq_norm_mul_sin_sub z a b haz hbz, show _ = Real.pi from h, Real.sin_pi]; simp
          · exact (hsin_pos a b haz hbz (by linarith) h).le
        have ho_bc : 0 ≤ orient z b c := by
          rcases eq_or_lt_of_le hcb_le with h | h
          · rw [orient_eq_norm_mul_sin_sub z b c hbz hcz, show _ = Real.pi from h, Real.sin_pi]; simp
          · exact (hsin_pos b c hbz hcz (by linarith) h).le
        rw [orient_sum_four z a b c]; linarith

private lemma inConvexPos_hullBoundary (Q : Finset (ℝ × ℝ)) : InConvexPos (hullBoundary Q) := by
  classical
  by_cases hcol : ∀ u ∈ Q, ∀ v ∈ Q, ∀ w ∈ Q, orient u v w = 0
  · refine ⟨(hullBoundary Q).equivFin.symm, fun i j k _ _ => ?_⟩
    have := hcol _ (hullBoundary_subset Q ((hullBoundary Q).equivFin.symm i).2)
      _ (hullBoundary_subset Q ((hullBoundary Q).equivFin.symm j).2)
      _ (hullBoundary_subset Q ((hullBoundary Q).equivFin.symm k).2)
    linarith
  · push Not at hcol
    obtain ⟨u, hu, v, hv, w, hw, ho⟩ := hcol
    let z : ℝ × ℝ := ((u.1 + v.1 + w.1) / 3, (u.2 + v.2 + w.2) / 3)
    have hz := isStrictInterior_centroid hu hv hw ho
    have ⟨_, hinj⟩ := arg_injOn_hullBoundary hz
    let θ : (ℝ × ℝ) → ℝ := fun q => Complex.arg (toC (q - z))
    let S : Finset ℝ := (hullBoundary Q).image θ
    have hcard : #S = #(hullBoundary Q) := Finset.card_image_of_injOn hinj
    let eS : Fin #(hullBoundary Q) ≃o S := (S.orderIsoOfFin hcard)
    let eB : (hullBoundary Q) ≃ S :=
      Equiv.ofBijective
        (fun q : hullBoundary Q => ⟨θ q.1, Finset.mem_image.mpr ⟨q.1, q.2, rfl⟩⟩)
        ⟨fun q₁ q₂ h => Subtype.ext (hinj q₁.2 q₂.2 (congrArg Subtype.val h)),
         fun ⟨t, ht⟩ =>
           let ⟨q, hq, hqt⟩ := Finset.mem_image.mp ht
           ⟨⟨q, hq⟩, Subtype.ext hqt⟩⟩
    let p : Fin #(hullBoundary Q) ≃ hullBoundary Q := eS.toEquiv.trans eB.symm
    refine ⟨p, fun i j k hij hjk => ?_⟩
    have hθ : ∀ t : Fin #(hullBoundary Q), θ (p t).1 = (eS t).1 := fun t => by
      have h1 := eB.apply_symm_apply (eS t)
      exact congrArg Subtype.val h1
    have hab : θ (p i).1 < θ (p j).1 := by
      rw [hθ i, hθ j]; exact eS.strictMono hij
    have hbc : θ (p j).1 < θ (p k).1 := by
      rw [hθ j, hθ k]; exact eS.strictMono hjk
    exact orient_nonneg_of_arg_lt hz (p i).2 (p j).2 (p k).2 hab hbc

private lemma hasEmptyPentagon_of_cyclic_orient {P : Finset (ℝ × ℝ)} (p : Fin 5 → ℝ × ℝ)
    (hpP : ∀ i, p i ∈ P)
    (ho : ∀ i j k : Fin 5, i < j → j < k → 0 < orient (p i) (p j) (p k))
    (hempty : ∀ q ∈ P, q ∈ convexHull ℝ (Set.range p) → q ∈ Set.range p) :
    HasEmptyPentagon P := by
  classical
  have hinj : Function.Injective p := by
    intro i j hij
    by_contra hne
    wlog hlt : i < j generalizing i j
    · exact this hij.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
    by_cases hj : j.1 + 1 < 5
    · have h := ho i j ⟨j.1 + 1, hj⟩ hlt (by show j.1 < j.1 + 1; omega)
      rw [hij, orient_self_left] at h; exact lt_irrefl 0 h
    · by_cases hi : 0 < i.1
      · have h := ho ⟨0, by omega⟩ i j (by show 0 < i.1; omega) hlt
        rw [hij, orient_self_right] at h; exact lt_irrefl 0 h
      · have h := ho i ⟨i.1 + 1, by omega⟩ j (by show i.1 < i.1 + 1; omega)
          (by show i.1 + 1 < j.1; omega)
        rw [hij, orient_self_mid] at h; exact lt_irrefl 0 h
  let S : Finset (ℝ × ℝ) := Finset.univ.image p
  have hS_coe : (S : Set (ℝ × ℝ)) = Set.range p := by
    ext x; simp [S]
  have hSP : S ⊆ P := by
    intro x hx; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx; exact hpP i
  have hScard : #S = 5 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
  have hciS : ConvexIndependent ℝ ((↑) : ↥(S : Set (ℝ × ℝ)) → ℝ × ℝ) := by
    rw [hS_coe]
    exact convexIndependent_range_of_cyclic_orient (by omega) p ho
  refine ⟨S, hSP, hScard, hciS, fun q hq hqconv => ?_⟩
  rw [hS_coe] at hqconv
  rw [← Finset.mem_coe, hS_coe]
  exact hempty q hq hqconv

private lemma extract_turns {P A : Finset (ℝ × ℝ)} {ℓ : ℕ} (hℓ : 3 ≤ ℓ)
    (hAP : A ⊆ P) (hcol : ¬ HasCollinear ℓ P) (p : Fin #A ≃ A)
    (ho : ∀ i j k : Fin #A, i < j → j < k → 0 ≤ orient (p i) (p j) (p k))
    (start : ℕ) :
    ∀ m : ℕ, 1 ≤ m → start + m * (ℓ - 1) < #A →
      ∃ c : Fin (m + 1) → Fin #A,
        (c 0).1 = start ∧
        (c ⟨m, by omega⟩).1 ≤ start + m * (ℓ - 1) ∧
        StrictMono c ∧
        ∀ t : ℕ, (ht : t + 2 ≤ m) →
          0 < orient (p (c ⟨t, by omega⟩)) (p (c ⟨t + 1, by omega⟩)) (p (c ⟨t + 2, by omega⟩)) := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    intro hbound
    by_cases hm0 : m = 0
    · subst hm0
      refine ⟨fun i => if i.1 = 0 then ⟨start, by omega⟩ else ⟨start + 1, by omega⟩,
        by simp, by simp; omega, ?_, fun t ht => by omega⟩
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [Fin.lt_def] at hij ⊢
    · have hmul : (m + 1) * (ℓ - 1) = m * (ℓ - 1) + (ℓ - 1) := by ring
      obtain ⟨c, hc0, hclast, hcmono, hcturn⟩ := ih (by omega) (by omega)
      let prev := c ⟨m - 1, by omega⟩
      let last := c ⟨m, by omega⟩
      have hpl : prev < last := hcmono (by show m - 1 < m; omega)
      -- Among the (ℓ - 2) indices last+1, ..., last+(ℓ-2), or last+(ℓ-1), one must not be collinear with prev, last!
      have hex : ∃ j : Fin #A, last < j ∧ j.1 ≤ last.1 + (ℓ - 1) ∧
          0 < orient (p prev) (p last) (p j) := by
        by_contra hall
        push Not at hall
        have hzero : ∀ j : Fin #A, last < j → j.1 ≤ last.1 + (ℓ - 2) →
            orient (p prev) (p last) (p j) = 0 := fun j hj1 hj2 =>
          le_antisymm (hall j hj1 (by omega)) (ho prev last j hpl hj1)
        -- Build ℓ collinear points: p prev, p last, and p(last+1), ..., p(last+ℓ-2)
        let idx : Fin ℓ → Fin #A := fun i =>
          if i.1 = 0 then prev
          else if i.1 = 1 then last
          else ⟨last.1 + (i.1 - 1), by omega⟩
        have hidx_inj : Function.Injective idx := by
          intro i j hij
          by_contra hne
          wlog hlt : i < j generalizing i j
          · exact this hij.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
          have hval := congrArg Fin.val hij
          have hpl' : prev.1 < last.1 := hpl
          have hlt' : i.1 < j.1 := hlt
          dsimp only [idx] at hval
          by_cases hi0 : i.1 = 0 <;> by_cases hi1 : i.1 = 1 <;>
          by_cases hj0 : j.1 = 0 <;> by_cases hj1 : j.1 = 1 <;>
          simp [hi0, hi1, hj0, hj1] at hval <;> omega
        let S : Finset (ℝ × ℝ) := Finset.univ.image (fun i => (p (idx i)).1)
        have hS_inj : Function.Injective (fun i : Fin ℓ => (p (idx i)).1) :=
          fun i j h => hidx_inj (p.injective (Subtype.ext h))
        apply hcol
        refine ⟨S, ?_, ?_, ?_⟩
        · intro x hx
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
          exact hAP (p (idx i)).2
        · rw [Finset.card_image_of_injective _ hS_inj, Finset.card_fin]
        · refine collinear_of_orient_eq_zero (a := (p prev).1) (b := (p last).1)
            (fun h => ne_of_lt hpl (p.injective (Subtype.ext h))) ?_
          intro x hx
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
          dsimp only [idx]
          split_ifs with h0 h1
          · exact orient_self_mid _ _
          · exact orient_self_right _ _
          · exact hzero ⟨last.1 + (i.1 - 1), by omega⟩ (by show last.1 < last.1 + (i.1 - 1); omega)
              (by dsimp; omega)
      obtain ⟨j, hlj, hjle, hjpos⟩ := hex
      let c' : Fin (m + 2) → Fin #A := fun i =>
        if h : i.1 ≤ m then c ⟨i.1, by omega⟩ else j
      refine ⟨c', ?_, ?_, ?_, ?_⟩
      · simp [c', hc0]
      · simp only [c', show ¬(m + 1 ≤ m) by omega, ↓reduceDIte]
        have : (m + 1) * (ℓ - 1) = m * (ℓ - 1) + (ℓ - 1) := by ring
        omega
      · intro a b hab
        dsimp only [c']
        split_ifs with ha hb hb
        · exact hcmono (by show a.1 < b.1; omega)
        · exact lt_of_le_of_lt (hcmono.monotone (by show a.1 ≤ m; omega)) hlj
        · omega
        · omega
      · intro t ht
        by_cases htm : t + 2 ≤ m
        · have h1 : c' ⟨t, by omega⟩ = c ⟨t, by omega⟩ := by simp [c', show t ≤ m by omega]
          have h2 : c' ⟨t + 1, by omega⟩ = c ⟨t + 1, by omega⟩ := by simp [c', show t + 1 ≤ m by omega]
          have h3 : c' ⟨t + 2, by omega⟩ = c ⟨t + 2, by omega⟩ := by simp [c', show t + 2 ≤ m by omega]
          rw [h1, h2, h3]
          exact hcturn t htm
        · have ht_eq : t = m - 1 := by have : t + 2 ≤ m + 1 := ht; omega
          subst ht_eq
          have h1 : c' ⟨m - 1, by omega⟩ = prev := by simp [c', prev, show m - 1 ≤ m by omega]
          have h2 : c' ⟨m - 1 + 1, by omega⟩ = last := by
            simp only [c', last, show m - 1 + 1 ≤ m by omega, ↓reduceDIte]
            congr 1; apply Fin.ext; dsimp; omega
          have h3 : c' ⟨m - 1 + 2, by omega⟩ = j := by
            simp [c', show ¬(m - 1 + 2 ≤ m) by omega]
          rw [h1, h2, h3]
          exact hjpos

/-- If `a, b, d` are on `hullBoundary Q` in increasing angle order around an interior point `z`,
    and `orient a b d = 0`, then `b` lies strictly between `a` and `d` on the segment `[a, d]`,
    so every boundary point `t` with angle strictly between `a` and `d` also satisfies `orient a t d = 0`. -/
private lemma orient_eq_zero_between_of_arg {Q : Finset (ℝ × ℝ)} {z a b d t : ℝ × ℝ}
    (hz : ∀ u v : ℝ, (u ≠ 0 ∨ v ≠ 0) → ∃ x ∈ Q, u * z.1 + v * z.2 < u * x.1 + v * x.2)
    (ha : a ∈ hullBoundary Q) (hb : b ∈ hullBoundary Q) (hd : d ∈ hullBoundary Q)
    (ht : t ∈ hullBoundary Q)
    (hab : Complex.arg (toC (a - z)) < Complex.arg (toC (b - z)))
    (hbd : Complex.arg (toC (b - z)) < Complex.arg (toC (d - z)))
    (hat : Complex.arg (toC (a - z)) < Complex.arg (toC (t - z)))
    (htd : Complex.arg (toC (t - z)) < Complex.arg (toC (d - z)))
    (hda_lt : Complex.arg (toC (d - z)) - Complex.arg (toC (a - z)) < Real.pi)
    (h0 : orient a b d = 0) : orient a t d = 0 := by
  have ⟨hne, _⟩ := arg_injOn_hullBoundary hz
  have haz : a ≠ z := hne a ha
  have hbz : b ≠ z := hne b hb
  have hdz : d ≠ z := hne d hd
  set θa := Complex.arg (toC (a - z))
  set θb := Complex.arg (toC (b - z))
  set θd := Complex.arg (toC (d - z))
  have hsin_pos : ∀ p q : ℝ × ℝ, p ≠ z → q ≠ z →
      0 < Complex.arg (toC (q - z)) - Complex.arg (toC (p - z)) →
      Complex.arg (toC (q - z)) - Complex.arg (toC (p - z)) < Real.pi →
      0 < orient z p q := by
    intro p q hp hq h1 h2
    rw [orient_eq_norm_mul_sin_sub z p q hp hq]
    exact mul_pos (mul_pos (norm_pos_iff.mpr ((toC_ne_zero_iff p z).mpr hp))
      (norm_pos_iff.mpr ((toC_ne_zero_iff q z).mpr hq))) (Real.sin_pos_of_pos_of_lt_pi h1 h2)
  have ho_ad := hsin_pos a d haz hdz (by linarith) hda_lt
  have ho_ab := hsin_pos a b haz hbz (by linarith) (by linarith)
  have ho_bd := hsin_pos b d hbz hdz (by linarith) (by linarith)
  have hsum : orient z a b + orient z b d = orient z a d := by
    have := orient_sum_four z a b d
    have hsw : orient z d a = -orient z a d := by unfold orient; ring
    linarith
  have hcr := cramer_2d z a b d
  set s := orient z b d / orient z a d
  set r := orient z a b / orient z a d
  have hs0 : 0 < s := div_pos ho_bd ho_ad
  have hr0 : 0 < r := div_pos ho_ab ho_ad
  have hsr : s + r = 1 := by
    dsimp [s, r]; rw [← add_div, add_comm, hsum, div_self (ne_of_gt ho_ad)]
  have hb_eq : b = s • a + r • d := by
    have hcr1 := congrArg Prod.fst hcr
    have hcr2 := congrArg Prod.snd hcr
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      smul_eq_mul] at hcr1 hcr2
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    · dsimp [s, r]; field_simp [ne_of_gt ho_ad]; linear_combination hcr1 - z.1 * hsum
    · dsimp [s, r]; field_simp [ne_of_gt ho_ad]; linear_combination hcr2 - z.2 * hsum
  have hge : 0 ≤ orient a t d := orient_nonneg_of_arg_lt hz ha ht hd hat htd
  by_contra hne0
  have hpos : 0 < orient a t d := lt_of_le_of_ne hge (Ne.symm hne0)
  rcases lt_trichotomy (Complex.arg (toC (t - z))) θb with htb | hteq | hbt
  · have h1 : 0 ≤ orient t b d := orient_nonneg_of_arg_lt hz ht hb hd htb hbd
    have h2 : orient t b d = -s * orient a t d := by
      have hswap : orient t b d = -orient t d b := by unfold orient; ring
      rw [hswap, hb_eq, orient_add_smul t d a d s r hsr, orient_self_right]
      have hta : orient t d a = orient a t d := by unfold orient; ring
      rw [hta]; ring
    nlinarith
  · have htb : t = b := (arg_injOn_hullBoundary hz).2 ht hb hteq
    subst htb; exact absurd h0 (ne_of_gt hpos)
  · have h1 : 0 ≤ orient a b t := orient_nonneg_of_arg_lt hz ha hb ht hab hbt
    have h2 : orient a b t = -r * orient a t d := by
      have hswap : orient a b t = -orient a t b := by unfold orient; ring
      rw [hswap, hb_eq, orient_add_smul a t a d s r hsr, orient_self_mid]
      ring
    nlinarith

/-- Any supporting functional of `Q` that is equal at two distinct points `a, b` cannot exist
    if `orient a b` takes both strictly positive and strictly negative values on `Q`. -/
private lemma no_supporting_functional_through_chord {Q : Finset (ℝ × ℝ)} {a b u v : ℝ × ℝ}
    (hu : u ∈ Q) (hv : v ∈ Q) (hneg : orient a b u < 0) (hpos : 0 < orient a b v)
    {c₁ c₂ : ℝ} (hc : c₁ ≠ 0 ∨ c₂ ≠ 0)
    (heq : c₁ * a.1 + c₂ * a.2 = c₁ * b.1 + c₂ * b.2)
    (hmax : ∀ x ∈ Q, c₁ * x.1 + c₂ * x.2 ≤ c₁ * a.1 + c₂ * a.2) : False := by
  have hne : a ≠ b := by
    intro h; subst h; rw [orient_self_left] at hneg; exact lt_irrefl 0 hneg
  have hdiff : c₁ * (b.1 - a.1) + c₂ * (b.2 - a.2) = 0 := by linarith
  have h1 := hmax u hu
  have h2 := hmax v hv
  -- Show (c₁ * (x.1 - a.1) + c₂ * (x.2 - a.2)) is a nonzero scalar multiple of orient a b x!
  by_cases hx : b.1 - a.1 ≠ 0
  · have hc1 : c₁ = -c₂ * (b.2 - a.2) / (b.1 - a.1) := by
      field_simp; linarith
    have hc2 : c₂ ≠ 0 := by
      intro h0; subst h0; simp at hc1; exact hc.elim (fun h => h hc1) (fun h => h rfl)
    have hrel : ∀ x : ℝ × ℝ, (b.1 - a.1) * (c₁ * (x.1 - a.1) + c₂ * (x.2 - a.2)) =
        c₂ * orient a b x := by
      intro x; unfold orient; rw [hc1]; field_simp; ring
    have hu' : (b.1 - a.1) * (c₁ * (u.1 - a.1) + c₂ * (u.2 - a.2)) = c₂ * orient a b u := hrel u
    have hv' : (b.1 - a.1) * (c₁ * (v.1 - a.1) + c₂ * (v.2 - a.2)) = c₂ * orient a b v := hrel v
    have hlu : c₁ * (u.1 - a.1) + c₂ * (u.2 - a.2) ≤ 0 := by linarith
    have hlv : c₁ * (v.1 - a.1) + c₂ * (v.2 - a.2) ≤ 0 := by linarith
    rcases lt_or_gt_of_ne hx with hxn | hxp <;> rcases lt_or_gt_of_ne hc2 with hc2n | hc2p <;> nlinarith
  · push Not at hx
    have hy : b.2 - a.2 ≠ 0 := fun h => hne (Prod.ext (by linarith) (by linarith))
    have hc2 : c₂ = 0 := by
      rw [hx] at hdiff
      have : c₂ * (b.2 - a.2) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right hy
    have hc1 : c₁ ≠ 0 := hc.resolve_right (not_not.mpr hc2)
    have hrel : ∀ x : ℝ × ℝ, (b.2 - a.2) * (c₁ * (x.1 - a.1) + c₂ * (x.2 - a.2)) =
        -c₁ * orient a b x := by
      intro x; unfold orient; rw [hx, hc2]; ring
    have hu' := hrel u
    have hv' := hrel v
    have hlu : c₁ * (u.1 - a.1) + c₂ * (u.2 - a.2) ≤ 0 := by linarith
    have hlv : c₁ * (v.1 - a.1) + c₂ * (v.2 - a.2) ≤ 0 := by linarith
    rcases lt_or_gt_of_ne hy with hyn | hyp <;> rcases lt_or_gt_of_ne hc1 with hc1n | hc1p <;> nlinarith

/-- If `a, b ∈ hullBoundary Q` and `orient a b` takes both `< 0` and `> 0` on `Q`, then every
    point `w ∈ convexHull ℝ Q` with `orient a b w = 0` lies in `segment ℝ a b`. -/
private lemma mem_segment_of_orient_eq_zero_of_mem_convexHull {Q : Finset (ℝ × ℝ)}
    {a b u v w : ℝ × ℝ}
    (ha : a ∈ hullBoundary Q) (hb : b ∈ hullBoundary Q)
    (hu : u ∈ Q) (hv : v ∈ Q) (hneg : orient a b u < 0) (hpos : 0 < orient a b v)
    (hw : w ∈ convexHull ℝ (Q : Set (ℝ × ℝ))) (hw0 : orient a b w = 0) :
    w ∈ segment ℝ a b := by
  have hne : a ≠ b := by
    intro h; subst h; rw [orient_self_left] at hneg; exact lt_irrefl 0 hneg
  -- Write w = a + t • (b - a) for a unique t : ℝ
  have hex_t : ∃ t : ℝ, w = (1 - t) • a + t • b := by
    by_cases h1 : b.1 - a.1 ≠ 0
    · refine ⟨(w.1 - a.1) / (b.1 - a.1), ?_⟩
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; field_simp; ring
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        unfold orient at hw0; field_simp; linear_combination hw0
    · push Not at h1
      have h2 : b.2 - a.2 ≠ 0 := fun h => hne (Prod.ext (by linarith) (by linarith))
      refine ⟨(w.2 - a.2) / (b.2 - a.2), ?_⟩
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        unfold orient at hw0; rw [h1] at hw0
        have hw1 : (b.2 - a.2) * (w.1 - a.1) = 0 := by linarith
        have : w.1 - a.1 = 0 := (mul_eq_zero.mp hw1).resolve_left h2
        have hb1 : b.1 = a.1 := by linarith
        rw [hb1]; ring_nf; linarith
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; field_simp; ring
  obtain ⟨t, hwt⟩ := hex_t
  -- Show 0 ≤ t ≤ 1 using the supporting functionals at a and b!
  have ht0 : 0 ≤ t := by
    by_contra htneg
    push Not at htneg
    obtain ⟨_, c₁, c₂, hc, hmax⟩ := mem_hullBoundary.mp ha
    have hLw : c₁ * w.1 + c₂ * w.2 ≤ c₁ * a.1 + c₂ * a.2 := by
      have hconv : Convex ℝ {x : ℝ × ℝ | c₁ * x.1 + c₂ * x.2 ≤ c₁ * a.1 + c₂ * a.2} := by
        intro x hx y hy r₁ r₂ hr₁ hr₂ hr12
        simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul] at hx hy ⊢
        have : c₁ * (r₁ * x.1 + r₂ * y.1) + c₂ * (r₁ * x.2 + r₂ * y.2) =
            r₁ * (c₁ * x.1 + c₂ * x.2) + r₂ * (c₁ * y.1 + c₂ * y.2) := by ring
        rw [this]
        have h1' := mul_le_mul_of_nonneg_left hx hr₁
        have h2' := mul_le_mul_of_nonneg_left hy hr₂
        linarith [show r₁ * (c₁ * a.1 + c₂ * a.2) + r₂ * (c₁ * a.1 + c₂ * a.2) =
          c₁ * a.1 + c₂ * a.2 by linear_combination (c₁ * a.1 + c₂ * a.2) * hr12]
      exact convexHull_min (fun x hx => hmax x hx) hconv hw
    have hLb : c₁ * b.1 + c₂ * b.2 ≤ c₁ * a.1 + c₂ * a.2 := hmax b (mem_hullBoundary.mp hb).1
    have hrel : c₁ * w.1 + c₂ * w.2 - (c₁ * a.1 + c₂ * a.2) =
        t * (c₁ * b.1 + c₂ * b.2 - (c₁ * a.1 + c₂ * a.2)) := by
      rw [hwt]; simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    have heq : c₁ * a.1 + c₂ * a.2 = c₁ * b.1 + c₂ * b.2 := by nlinarith
    exact no_supporting_functional_through_chord hu hv hneg hpos hc heq hmax
  have ht1 : t ≤ 1 := by
    by_contra htgt
    push Not at htgt
    obtain ⟨_, c₁, c₂, hc, hmax⟩ := mem_hullBoundary.mp hb
    have hLw : c₁ * w.1 + c₂ * w.2 ≤ c₁ * b.1 + c₂ * b.2 := by
      have hconv : Convex ℝ {x : ℝ × ℝ | c₁ * x.1 + c₂ * x.2 ≤ c₁ * b.1 + c₂ * b.2} := by
        intro x hx y hy r₁ r₂ hr₁ hr₂ hr12
        simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul] at hx hy ⊢
        have : c₁ * (r₁ * x.1 + r₂ * y.1) + c₂ * (r₁ * x.2 + r₂ * y.2) =
            r₁ * (c₁ * x.1 + c₂ * x.2) + r₂ * (c₁ * y.1 + c₂ * y.2) := by ring
        rw [this]
        have h1' := mul_le_mul_of_nonneg_left hx hr₁
        have h2' := mul_le_mul_of_nonneg_left hy hr₂
        linarith [show r₁ * (c₁ * b.1 + c₂ * b.2) + r₂ * (c₁ * b.1 + c₂ * b.2) =
          c₁ * b.1 + c₂ * b.2 by linear_combination (c₁ * b.1 + c₂ * b.2) * hr12]
      exact convexHull_min (fun x hx => hmax x hx) hconv hw
    have hLa : c₁ * a.1 + c₂ * a.2 ≤ c₁ * b.1 + c₂ * b.2 := hmax a (mem_hullBoundary.mp ha).1
    have hrel : c₁ * w.1 + c₂ * w.2 - (c₁ * b.1 + c₂ * b.2) =
        (1 - t) * (c₁ * a.1 + c₂ * a.2 - (c₁ * b.1 + c₂ * b.2)) := by
      rw [hwt]; simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    have heq : c₁ * a.1 + c₂ * a.2 = c₁ * b.1 + c₂ * b.2 := by nlinarith
    have hmax' : ∀ x ∈ Q, c₁ * x.1 + c₂ * x.2 ≤ c₁ * a.1 + c₂ * a.2 := fun x hx => by
      linarith [hmax x hx]
    exact no_supporting_functional_through_chord hu hv hneg hpos hc heq hmax'
  exact ⟨1 - t, t, by linarith, ht0, by linarith, hwt.symm⟩

private lemma orient_centerMass (u v : ℝ × ℝ) (s : Finset (ℝ × ℝ)) (w : (ℝ × ℝ) → ℝ)
    (hw1 : ∑ x ∈ s, w x = 1) :
    orient u v (s.centerMass w id) = ∑ x ∈ s, w x * orient u v x := by
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw1]
  unfold orient
  simp only [id_eq, Finset.sum_apply, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  have h1 : (∑ x ∈ s, w x * x.2) - u.2 = ∑ x ∈ s, w x * (x.2 - u.2) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
  have h2 : (∑ x ∈ s, w x * x.1) - u.1 = ∑ x ∈ s, w x * (x.1 - u.1) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
  rw [h1, h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => by ring

/-- Cap containment: any point in `convexHull ℝ A` strictly on the `< 0` side of a chord `a — b`
    separating `B ⊆ A` from `A \ B` lies in `convexHull ℝ B`. -/
private lemma hullBoundary_convexHull_cap {Q B : Finset (ℝ × ℝ)} {a b u v y : ℝ × ℝ}
    (hBA : B ⊆ hullBoundary Q) (ha : a ∈ B) (hb : b ∈ B)
    (hu : u ∈ Q) (hv : v ∈ Q) (hneg : orient a b u < 0) (hpos : 0 < orient a b v)
    (hB_le : ∀ x ∈ B, orient a b x ≤ 0)
    (hAB_ge : ∀ x ∈ hullBoundary Q \ B, 0 ≤ orient a b x)
    (hy : y ∈ convexHull ℝ (hullBoundary Q : Set (ℝ × ℝ))) (hy_neg : orient a b y < 0) :
    y ∈ convexHull ℝ (B : Set (ℝ × ℝ)) := by
  classical
  rw [convexHull_eq] at hy
  obtain ⟨ι, s, w, z, hw0, hw1, hzA, hcm⟩ := hy
  -- Push forward to Finset (ℝ × ℝ) via centerMass directly on ι
  let s₁ := s.filter fun i => z i ∈ B
  let s₂ := s.filter fun i => z i ∉ B
  let W₁ := ∑ i ∈ s₁, w i
  let W₂ := ∑ i ∈ s₂, w i
  have hs_disj : Disjoint s₁ s₂ := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
  have hs_union : s₁ ∪ s₂ = s := Finset.filter_union_filter_not_eq _ s
  have hWsum : W₁ + W₂ = 1 := by
    dsimp [W₁, W₂]; rw [← Finset.sum_union hs_disj, hs_union, hw1]
  have hW1_nonneg : 0 ≤ W₁ := Finset.sum_nonneg fun i hi => hw0 i (Finset.mem_filter.mp hi).1
  have hW2_nonneg : 0 ≤ W₂ := Finset.sum_nonneg fun i hi => hw0 i (Finset.mem_filter.mp hi).1
  have horient_y : orient a b y = (∑ i ∈ s₁, w i * orient a b (z i)) +
      (∑ i ∈ s₂, w i * orient a b (z i)) := by
    rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hw1]
    have hsum_all : orient a b (∑ i ∈ s, w i • z i) = ∑ i ∈ s, w i * orient a b (z i) := by
      unfold orient
      simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      have h1 : (∑ i ∈ s, w i * (z i).2) - a.2 = ∑ i ∈ s, w i * ((z i).2 - a.2) := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
      have h2 : (∑ i ∈ s, w i * (z i).1) - a.1 = ∑ i ∈ s, w i * ((z i).1 - a.1) := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
      rw [h1, h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hsum_all, ← hs_union, Finset.sum_union hs_disj]
  have hsum2_ge : 0 ≤ ∑ i ∈ s₂, w i * orient a b (z i) := by
    refine Finset.sum_nonneg fun i hi => mul_nonneg (hw0 i (Finset.mem_filter.mp hi).1) ?_
    exact hAB_ge (z i) (Finset.mem_sdiff.mpr ⟨hzA i (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩)
  have hsum1_neg : ∑ i ∈ s₁, w i * orient a b (z i) < 0 := by linarith
  have hW1_pos : 0 < W₁ := by
    rcases eq_or_lt_of_le hW1_nonneg with h0 | hpos'
    · exfalso
      have hall0 : ∀ i ∈ s₁, w i = 0 := fun i hi =>
        (Finset.sum_eq_zero_iff_of_nonneg fun j hj => hw0 j (Finset.mem_filter.mp hj).1).mp h0.symm i hi
      have : ∑ i ∈ s₁, w i * orient a b (z i) = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [hall0 i hi, zero_mul]
      linarith
    · exact hpos'
  let u₀ : ℝ × ℝ := s₁.centerMass (fun i => w i / W₁) z
  have hu₀_mem : u₀ ∈ convexHull ℝ (B : Set (ℝ × ℝ)) := by
    rw [convexHull_eq]
    refine ⟨ι, s₁, fun i => w i / W₁, z,
      fun i hi => div_nonneg (hw0 i (Finset.mem_filter.mp hi).1) hW1_pos.le,
      by rw [← Finset.sum_div, div_self (ne_of_gt hW1_pos)],
      fun i hi => (Finset.mem_filter.mp hi).2, rfl⟩
  have hW1u₀ : W₁ • u₀ = ∑ i ∈ s₁, w i • z i := by
    have h1 : ∑ i ∈ s₁, w i / W₁ = 1 := by rw [← Finset.sum_div, div_self (ne_of_gt hW1_pos)]
    dsimp only [u₀]
    rw [Finset.centerMass_eq_of_sum_1 _ _ h1, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_div_cancel₀ _ (ne_of_gt hW1_pos)]
  rcases eq_or_lt_of_le hW2_nonneg with hW20 | hW2_pos
  · have hall0 : ∀ i ∈ s₂, w i = 0 := fun i hi =>
      (Finset.sum_eq_zero_iff_of_nonneg fun j hj => hw0 j (Finset.mem_filter.mp hj).1).mp hW20.symm i hi
    have hy_eq : y = u₀ := by
      have hW1_1 : W₁ = 1 := by linarith
      have hs2_zero : ∑ i ∈ s₂, w i • z i = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [hall0 i hi, zero_smul]
      rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hw1, ← hs_union, Finset.sum_union hs_disj,
        hs2_zero, add_zero, ← hW1u₀, hW1_1, one_smul]
    rwa [hy_eq]
  · let v₀ : ℝ × ℝ := s₂.centerMass (fun i => w i / W₂) z
    have hv₀_mem : v₀ ∈ convexHull ℝ (hullBoundary Q : Set (ℝ × ℝ)) := by
      rw [convexHull_eq]
      refine ⟨ι, s₂, fun i => w i / W₂, z,
        fun i hi => div_nonneg (hw0 i (Finset.mem_filter.mp hi).1) hW2_pos.le,
        by rw [← Finset.sum_div, div_self (ne_of_gt hW2_pos)],
        fun i hi => hzA i (Finset.mem_filter.mp hi).1, rfl⟩
    have hW2v₀ : W₂ • v₀ = ∑ i ∈ s₂, w i • z i := by
      have h1 : ∑ i ∈ s₂, w i / W₂ = 1 := by rw [← Finset.sum_div, div_self (ne_of_gt hW2_pos)]
      dsimp only [v₀]
      rw [Finset.centerMass_eq_of_sum_1 _ _ h1, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, mul_div_cancel₀ _ (ne_of_gt hW2_pos)]
    have hy_comb : y = W₁ • u₀ + W₂ • v₀ := by
      rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hw1, ← hs_union, Finset.sum_union hs_disj, hW1u₀, hW2v₀]
    have hu₀_neg : orient a b u₀ < 0 := by
      have h1 : orient a b u₀ = (∑ i ∈ s₁, w i * orient a b (z i)) / W₁ := by
        have hsum1 : ∑ i ∈ s₁, w i / W₁ = 1 := by rw [← Finset.sum_div, div_self (ne_of_gt hW1_pos)]
        dsimp only [u₀]
        rw [Finset.centerMass_eq_of_sum_1 _ _ hsum1]
        unfold orient
        simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        have ha1 : (∑ i ∈ s₁, w i / W₁ * (z i).2) - a.2 = ∑ i ∈ s₁, w i / W₁ * ((z i).2 - a.2) := by
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum1, one_mul]
        have ha2 : (∑ i ∈ s₁, w i / W₁ * (z i).1) - a.1 = ∑ i ∈ s₁, w i / W₁ * ((z i).1 - a.1) := by
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum1, one_mul]
        rw [ha1, ha2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [h1]; exact div_neg_of_neg_of_pos hsum1_neg hW1_pos
    have hv₀_ge : 0 ≤ orient a b v₀ := by
      refine orient_ge_of_mem_convexHull (S := (hullBoundary Q \ B : Set (ℝ × ℝ))) ?_ ?_
      · rw [convexHull_eq]
        refine ⟨ι, s₂, fun i => w i / W₂, z,
          fun i hi => div_nonneg (hw0 i (Finset.mem_filter.mp hi).1) hW2_pos.le,
          by rw [← Finset.sum_div, div_self (ne_of_gt hW2_pos)],
          fun i hi => ⟨hzA i (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩, rfl⟩
      · intro x hx
        exact hAB_ge x (Finset.mem_sdiff.mpr hx)
    set t := (-orient a b u₀) / (orient a b v₀ - orient a b u₀)
    have hden_pos : 0 < orient a b v₀ - orient a b u₀ := by linarith
    have ht_pos : 0 < t := div_pos (by linarith) hden_pos
    have ht_le1 : t ≤ 1 := (div_le_one hden_pos).mpr (by linarith)
    let w₀ : ℝ × ℝ := (1 - t) • u₀ + t • v₀
    have hw₀_0 : orient a b w₀ = 0 := by
      dsimp [w₀]; rw [orient_add_smul a b u₀ v₀ (1 - t) t (by ring)]
      dsimp [t]; field_simp [ne_of_gt hden_pos]; ring
    have hw₀_Q : w₀ ∈ convexHull ℝ (Q : Set (ℝ × ℝ)) := by
      have huQ : u₀ ∈ convexHull ℝ (Q : Set (ℝ × ℝ)) :=
        convexHull_mono (Finset.coe_subset.mpr (hBA.trans (hullBoundary_subset Q))) hu₀_mem
      have hvQ : v₀ ∈ convexHull ℝ (Q : Set (ℝ × ℝ)) :=
        convexHull_mono (Finset.coe_subset.mpr (hullBoundary_subset Q)) hv₀_mem
      exact (convex_convexHull ℝ _) huQ hvQ (by linarith) ht_pos.le (by ring)
    have hw₀_seg : w₀ ∈ segment ℝ a b :=
      mem_segment_of_orient_eq_zero_of_mem_convexHull (hBA ha) (hBA hb) hu hv hneg hpos hw₀_Q hw₀_0
    have hw₀_B : w₀ ∈ convexHull ℝ (B : Set (ℝ × ℝ)) :=
      segment_subset_convexHull ha hb hw₀_seg
    have hW2_lt_t : W₂ < t := by
      have hW1' : W₁ = 1 - W₂ := by linarith
      have h1 : orient a b y = (1 - W₂) * orient a b u₀ + W₂ * orient a b v₀ := by
        rw [hy_comb, orient_add_smul a b u₀ v₀ W₁ W₂ hWsum, hW1']
      dsimp [t]
      rw [lt_div_iff₀ hden_pos]
      linarith
    have hy_uw' : y = (1 - W₂ / t) • u₀ + (W₂ / t) • w₀ := by
      rw [hy_comb]; dsimp [w₀]
      have hW1' : W₁ = 1 - W₂ := by linarith
      rw [hW1']
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
        (field_simp [ne_of_gt ht_pos]; ring)
    rw [hy_uw']
    exact (convex_convexHull ℝ _) hu₀_mem hw₀_B (by rw [sub_nonneg]; exact (div_le_one ht_pos).mpr hW2_lt_t.le)
      (div_nonneg hW2_pos.le ht_pos.le) (by ring)

/-- Every finite set `Q ⊆ ℝ²` is contained in the convex hull of its boundary `hullBoundary Q`. -/
private lemma subset_convexHull_hullBoundary (Q : Finset (ℝ × ℝ)) :
    (Q : Set (ℝ × ℝ)) ⊆ convexHull ℝ (hullBoundary Q : Set (ℝ × ℝ)) := by
  intro q hq
  by_contra hnot
  have hclosed : IsClosed (convexHull ℝ (hullBoundary Q : Set (ℝ × ℝ))) :=
    (Set.Finite.isCompact_convexHull (𝕜 := ℝ) (Finset.finite_toSet (hullBoundary Q))).isClosed
  obtain ⟨f, u, hfu, hfq⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hclosed hnot
  have hQne : Q.Nonempty := ⟨q, hq⟩
  obtain ⟨qmax, hqmaxQ, hmax⟩ := Q.exists_max_image f hQne
  have hne0 : f (1, 0) ≠ 0 ∨ f (0, 1) ≠ 0 := by
    by_contra h0
    push Not at h0
    have hf0 : ∀ x : ℝ × ℝ, f x = 0 := fun x => by
      have hx : x = x.1 • (1, 0) + x.2 • (0, 1) := by ext <;> simp
      rw [hx, map_add, map_smul, map_smul, h0.1, h0.2]; simp
    have hBne : (hullBoundary Q).Nonempty := hullBoundary_nonempty hQne
    obtain ⟨b, hb⟩ := hBne
    have h1 := hfu b (subset_convexHull ℝ _ hb)
    rw [hf0 b] at h1
    rw [hf0 q] at hfq
    linarith
  have hqmaxB : qmax ∈ hullBoundary Q := by
    rw [mem_hullBoundary]
    refine ⟨hqmaxQ, f (1, 0), f (0, 1), hne0, fun x hx => ?_⟩
    have hfx : ∀ y : ℝ × ℝ, f (1, 0) * y.1 + f (0, 1) * y.2 = f y := fun y => by
      have hy : y = y.1 • (1, 0) + y.2 • (0, 1) := by ext <;> simp
      conv_rhs => rw [hy, map_add, map_smul, map_smul]
      simp [mul_comm]
    rw [hfx x, hfx qmax]
    exact hmax x hx
  have h1 := hfu qmax (subset_convexHull ℝ _ hqmaxB)
  have h2 := hmax q hq
  linarith

/-- Core layer-shrinking bound: if `Q ⊆ P` is convex-closed in `P`, and `P` has no `ℓ` collinear
    points and no empty pentagon, then `#(hullBoundary Q) < (11 * (ℓ - 1) + 1) * (#(hullBoundary (Q \ hullBoundary Q)) + 3)`. -/
private lemma card_layer_bound {P Q : Finset (ℝ × ℝ)} {ℓ : ℕ} (hℓ : 3 ≤ ℓ)
    (hQP : Q ⊆ P)
    (hQclosed : ∀ x ∈ P, x ∈ convexHull ℝ (Q : Set (ℝ × ℝ)) → x ∈ Q)
    (hcol : ¬ HasCollinear ℓ P) (hpent : ¬ HasEmptyPentagon P) :
    #(hullBoundary Q) < (11 * (ℓ - 1) + 1) * (#(hullBoundary (Q \ hullBoundary Q)) + 3) := by
  classical
  set A := hullBoundary Q
  set Q' := Q \ A
  set A' := hullBoundary Q'
  set C := 11 * (ℓ - 1) + 1
  by_cases hsmall : #A < 3 * C
  · have : 3 * C ≤ C * (#A' + 3) := by nlinarith
    omega
  push Not at hsmall
  have hC_pos : 0 < C := by dsimp [C]; omega
  -- Q cannot be all collinear since #A ≥ 3 * C ≥ ℓ
  have hnoncol : ∃ u ∈ Q, ∃ v ∈ Q, ∃ w ∈ Q, orient u v w ≠ 0 := by
    by_contra hall
    push Not at hall
    have hA2 : 2 ≤ #A := by dsimp [C] at hsmall; omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < #A)
    obtain ⟨S, hSA, hScard⟩ := Finset.exists_subset_card_eq (show ℓ ≤ #A by dsimp [C] at hsmall; omega)
    apply hcol
    refine ⟨S, hSA.trans ((hullBoundary_subset Q).trans hQP), hScard, ?_⟩
    refine collinear_of_orient_eq_zero hab fun x hx =>
      hall a (hullBoundary_subset Q ha) b (hullBoundary_subset Q hb) x
        (hullBoundary_subset Q (hSA (Finset.mem_coe.mp hx)))
  obtain ⟨u₀, hu₀, v₀, hv₀, w₀, hw₀, ho₀⟩ := hnoncol
  let z : ℝ × ℝ := ((u₀.1 + v₀.1 + w₀.1) / 3, (u₀.2 + v₀.2 + w₀.2) / 3)
  have hz := isStrictInterior_centroid hu₀ hv₀ hw₀ ho₀
  have ⟨_, hinj⟩ := arg_injOn_hullBoundary hz
  let θ : (ℝ × ℝ) → ℝ := fun q => Complex.arg (toC (q - z))
  let Sθ : Finset ℝ := A.image θ
  have hcardS : #Sθ = #A := Finset.card_image_of_injOn hinj
  let eS : Fin #A ≃o Sθ := Sθ.orderIsoOfFin hcardS
  let eB : A ≃ Sθ :=
    Equiv.ofBijective
      (fun q : A => ⟨θ q.1, Finset.mem_image.mpr ⟨q.1, q.2, rfl⟩⟩)
      ⟨fun q₁ q₂ h => Subtype.ext (hinj q₁.2 q₂.2 (congrArg Subtype.val h)),
       fun ⟨t, ht⟩ => let ⟨q, hq, hqt⟩ := Finset.mem_image.mp ht; ⟨⟨q, hq⟩, Subtype.ext hqt⟩⟩
  let p : Fin #A ≃ A := eS.toEquiv.trans eB.symm
  have hθp : ∀ t : Fin #A, θ (p t).1 = (eS t).1 := fun t =>
    congrArg Subtype.val (eB.apply_symm_apply (eS t))
  have hθ_strict : StrictMono (fun t : Fin #A => θ (p t).1) := fun i j hij => by
    dsimp only; rw [hθp i, hθp j]; exact eS.strictMono hij
  have ho_nonneg : ∀ i j k : Fin #A, i < j → j < k → 0 ≤ orient (p i) (p j) (p k) :=
    fun i j k hij hjk => orient_nonneg_of_arg_lt hz (p i).2 (p j).2 (p k).2
      (hθ_strict hij) (hθ_strict hjk)
  -- Split Fin #A into negative-angle prefix [0, m₁) and positive-angle suffix [m₂, #A)
  let I_neg : Finset (Fin #A) := Finset.univ.filter fun i => θ (p i).1 < 0
  let I_pos : Finset (Fin #A) := Finset.univ.filter fun i => 0 < θ (p i).1
  set m₁ := #I_neg
  set m₂ := #A - #I_pos
  have hm1_prop : ∀ i : Fin #A, i.1 < m₁ ↔ θ (p i).1 < 0 := by
    intro i
    have hpref : I_neg = Finset.univ.filter (fun j : Fin #A => j.1 < m₁) := by
      -- Since θ ∘ p is strictly increasing, I_neg is a downward-closed subset of Fin #A of card m₁!
      by_cases hne : I_neg.Nonempty
      · have hdown : ∀ a b : Fin #A, a ≤ b → b ∈ I_neg → a ∈ I_neg := by
          intro a b hab hb
          rw [Finset.mem_filter] at hb ⊢
          exact ⟨Finset.mem_univ _, lt_of_le_of_lt (hθ_strict.monotone hab) hb.2⟩
        have hlt : ∀ j : Fin #A, j ∈ I_neg → j.1 < m₁ := by
          intro j hj
          have hsub : (Finset.univ.filter fun a : Fin #A => a.1 ≤ j.1) ⊆ I_neg := fun a ha =>
            hdown a j (Finset.mem_filter.mp ha).2 hj
          have hcard_le := Finset.card_le_card hsub
          have hcard_eq : #(Finset.univ.filter fun a : Fin #A => a.1 ≤ j.1) = j.1 + 1 := by
            have : (Finset.univ.filter fun a : Fin #A => a.1 ≤ j.1) =
                (Finset.range (j.1 + 1)).attach.image (fun x => ⟨x.1, by have := Finset.mem_range.mp x.2; omega⟩) := by
              ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
                Finset.mem_attach, Subtype.exists, Finset.mem_range]
              constructor
              · intro ha; exact ⟨a.1, by omega, Fin.ext rfl⟩
              · rintro ⟨x, hx, rfl⟩; dsimp; omega
            rw [this, Finset.card_image_of_injective _ (fun x y h => Subtype.ext (congrArg Fin.val h)),
              Finset.card_attach, Finset.card_range]
          omega
        have hsub : I_neg ⊆ Finset.univ.filter (fun j : Fin #A => j.1 < m₁) := fun j hj =>
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt j hj⟩
        have hcard_rhs : #(Finset.univ.filter fun j : Fin #A => j.1 < m₁) = m₁ := by
          have hm1_le : m₁ ≤ #A := by simpa using Finset.card_le_univ I_neg
          have : (Finset.univ.filter fun j : Fin #A => j.1 < m₁) =
              (Finset.range m₁).attach.image (fun x => ⟨x.1, by have := Finset.mem_range.mp x.2; omega⟩) := by
            ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
              Finset.mem_attach, Subtype.exists, Finset.mem_range]
            constructor
            · intro ha; exact ⟨a.1, ha, Fin.ext rfl⟩
            · rintro ⟨x, hx, rfl⟩; exact hx
          rw [this, Finset.card_image_of_injective _ (fun x y h => Subtype.ext (congrArg Fin.val h)),
            Finset.card_attach, Finset.card_range]
        exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard_rhs])
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        have hm0 : m₁ = 0 := by simp [m₁, hne]
        rw [hne, hm0]; ext a; simp
    have hiff : i ∈ I_neg ↔ i.1 < m₁ := by rw [hpref]; simp
    simp only [I_neg, Finset.mem_filter, Finset.mem_univ, true_and] at hiff
    exact hiff.symm
  have hm2_prop : ∀ i : Fin #A, m₂ ≤ i.1 ↔ 0 < θ (p i).1 := by
    intro i
    have hsuf : I_pos = Finset.univ.filter (fun j : Fin #A => m₂ ≤ j.1) := by
      have hup : ∀ a b : Fin #A, a ≤ b → a ∈ I_pos → b ∈ I_pos := by
        intro a b hab ha
        rw [Finset.mem_filter] at ha ⊢
        exact ⟨Finset.mem_univ _, lt_of_lt_of_le ha.2 (hθ_strict.monotone hab)⟩
      have hge : ∀ j : Fin #A, j ∈ I_pos → m₂ ≤ j.1 := by
        intro j hj
        have hsub : (Finset.univ.filter fun a : Fin #A => j.1 ≤ a.1) ⊆ I_pos := fun a ha =>
          hup j a (Finset.mem_filter.mp ha).2 hj
        have hcard_le := Finset.card_le_card hsub
        have hcard_eq : #(Finset.univ.filter fun a : Fin #A => j.1 ≤ a.1) = #A - j.1 := by
          have : (Finset.univ.filter fun a : Fin #A => j.1 ≤ a.1) =
              (Finset.range (#A - j.1)).attach.image
                (fun x => ⟨j.1 + x.1, by have := Finset.mem_range.mp x.2; omega⟩) := by
            ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
              Finset.mem_attach, Subtype.exists, Finset.mem_range]
            constructor
            · intro ha; exact ⟨a.1 - j.1, by omega, Fin.ext (by dsimp; omega)⟩
            · rintro ⟨x, hx, rfl⟩; dsimp; omega
          rw [this, Finset.card_image_of_injective _ (fun x y h => Subtype.ext (by
              have := congrArg Fin.val h; dsimp at this; omega)),
            Finset.card_attach, Finset.card_range]
        omega
      have hsub : I_pos ⊆ Finset.univ.filter (fun j : Fin #A => m₂ ≤ j.1) := fun j hj =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hge j hj⟩
      have hcard_rhs : #(Finset.univ.filter fun j : Fin #A => m₂ ≤ j.1) = #I_pos := by
        have hle : #I_pos ≤ #A := by simpa using Finset.card_le_univ I_pos
        have : (Finset.univ.filter fun j : Fin #A => m₂ ≤ j.1) =
            (Finset.range #I_pos).attach.image
              (fun x => ⟨m₂ + x.1, by have := Finset.mem_range.mp x.2; omega⟩) := by
          ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
            Finset.mem_attach, Subtype.exists, Finset.mem_range]
          constructor
          · intro ha; exact ⟨a.1 - m₂, by omega, Fin.ext (by dsimp; omega)⟩
          · rintro ⟨x, hx, rfl⟩; dsimp; omega
        rw [this, Finset.card_image_of_injective _ (fun x y h => Subtype.ext (by
            have := congrArg Fin.val h; dsimp at this; omega)),
          Finset.card_attach, Finset.card_range]
      exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard_rhs])
    have hiff : i ∈ I_pos ↔ m₂ ≤ i.1 := by rw [hsuf]; simp
    simp only [I_pos, Finset.mem_filter, Finset.mem_univ, true_and] at hiff
    exact hiff.symm
  have hm1_le_A : m₁ ≤ #A := by simpa using Finset.card_le_univ I_neg
  have hm1_le_m2 : m₁ ≤ m₂ := by
    by_contra hgt
    push Not at hgt
    have hm2_lt : m₂ < #A := by omega
    have h1 := (hm1_prop ⟨m₂, hm2_lt⟩).mp (by dsimp; omega)
    have h2 := (hm2_prop ⟨m₂, hm2_lt⟩).mp (by dsimp; exact le_rfl)
    linarith
  have hm2_le_m1_add : m₂ ≤ m₁ + 1 := by
    by_contra hgt
    push Not at hgt
    have hi1 : m₁ < #A := by omega
    have hi2 : m₁ + 1 < #A := by omega
    have h1a : ¬ θ (p ⟨m₁, hi1⟩).1 < 0 := fun h => by
      have := (hm1_prop ⟨m₁, hi1⟩).mpr h; dsimp at this; omega
    have h1b : ¬ 0 < θ (p ⟨m₁, hi1⟩).1 := fun h => by
      have := (hm2_prop ⟨m₁, hi1⟩).mpr h; dsimp at this; omega
    have h2a : ¬ θ (p ⟨m₁ + 1, hi2⟩).1 < 0 := fun h => by
      have := (hm1_prop ⟨m₁ + 1, hi2⟩).mpr h; dsimp at this; omega
    have h2b : ¬ 0 < θ (p ⟨m₁ + 1, hi2⟩).1 := fun h => by
      have := (hm2_prop ⟨m₁ + 1, hi2⟩).mpr h; dsimp at this; omega
    have hlt := hθ_strict (show (⟨m₁, hi1⟩ : Fin #A) < ⟨m₁ + 1, hi2⟩ by simp [Fin.lt_def])
    linarith
  -- Key block lemma: any block [s, s + C - 1] with θ(p(s + C - 1)) - θ(p(s)) < π
  -- yields a point y ∈ A' strictly on the < 0 side of chord (p s, p (s + C - 1)) and inside convexHull ℝ B!
  have hblock : ∀ (s : ℕ) (hs : s + C ≤ #A),
      θ (p ⟨s + C - 1, by omega⟩).1 - θ (p ⟨s, by omega⟩).1 < Real.pi →
      ∃ y ∈ A', orient (p ⟨s, by omega⟩) (p ⟨s + C - 1, by omega⟩) y < 0 ∧
        y ∈ convexHull ℝ ((Finset.univ.filter (fun i : Fin #A => s ≤ i.1 ∧ i.1 < s + C)).image (fun i => (p i).1) : Set (ℝ × ℝ)) := by
    intro s hs hpi
    obtain ⟨c, hc0, hclast, hcmono, hcturn⟩ :=
      extract_turns hℓ ((hullBoundary_subset Q).trans hQP) hcol p ho_nonneg s 11 (by omega) (lt_of_lt_of_le (by dsimp [C]; omega) hs)
    -- Strict orient on any i < j < k in c 0, c 2, c 4, c 6, c 8, c 10!
    have hstrict_pair : ∀ (a b d : Fin #A),
        (c 0) ≤ a → a < b → b < d → d ≤ ⟨s + C - 1, by omega⟩ →
        (∃ t : ℕ, ∃ (ht : t + 2 ≤ 11), a ≤ c ⟨t, by omega⟩ ∧ c ⟨t + 2, by omega⟩ ≤ d) →
        0 < orient (p a) (p b) (p d) := by
      intro a b d ha hab hbd hd hex
      obtain ⟨t, ht, hat, htd⟩ := hex
      have hge := ho_nonneg a b d hab hbd
      by_contra hnot
      push Not at hnot
      have h0 : orient (p a) (p b) (p d) = 0 := le_antisymm hnot hge
      have hda_lt : θ (p d).1 - θ (p a).1 < Real.pi := by
        have h1 : θ (p ⟨s, by omega⟩).1 ≤ θ (p a).1 := hθ_strict.monotone (by show s ≤ a.1; have : (c 0).1 ≤ a.1 := ha; omega)
        have h2 : θ (p d).1 ≤ θ (p ⟨s + C - 1, by omega⟩).1 := hθ_strict.monotone hd
        linarith
      -- Every index strictly between a and d has orient (p a) (p _) (p d) = 0!
      have hmid0 : ∀ idx : Fin #A, a < idx → idx < d → orient (p a) (p idx) (p d) = 0 := fun idx h1 h2 =>
        orient_eq_zero_between_of_arg hz (p a).2 (p b).2 (p d).2 (p idx).2
          (hθ_strict hab) (hθ_strict hbd) (hθ_strict h1) (hθ_strict h2) hda_lt h0
      have h1 : orient (p a) (p (c ⟨t, by omega⟩)) (p d) = 0 := by
        rcases eq_or_lt_of_le hat with rfl | hlt
        · exact orient_self_left _ _
        · exact hmid0 _ hlt (lt_of_lt_of_le (hcmono (by show t < t + 2; omega)) htd)
      have h2 : orient (p a) (p (c ⟨t + 1, by omega⟩)) (p d) = 0 :=
        hmid0 _ (lt_of_le_of_lt hat (hcmono (by show t < t + 1; omega)))
          (lt_of_lt_of_le (hcmono (by show t + 1 < t + 2; omega)) htd)
      have h3 : orient (p a) (p (c ⟨t + 2, by omega⟩)) (p d) = 0 := by
        rcases eq_or_lt_of_le htd with rfl | hlt
        · exact orient_self_right _ _
        · exact hmid0 _ (lt_of_le_of_lt hat (hcmono (by show t < t + 2; omega))) hlt
      have hcol3 : Collinear ℝ ({(p (c ⟨t, by omega⟩)).1, (p (c ⟨t + 1, by omega⟩)).1, (p (c ⟨t + 2, by omega⟩)).1} : Set (ℝ × ℝ)) := by
        refine collinear_of_orient_eq_zero (a := (p a).1) (b := (p d).1)
          (fun h => ne_of_lt (lt_trans hab hbd) (p.injective (Subtype.ext h))) ?_
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · rw [orient_swap_bc]; linarith [h1]
        · rw [orient_swap_bc]; linarith [h2]
        · rw [orient_swap_bc]; linarith [h3]
      linarith [orient_eq_zero_of_collinear hcol3, hcturn t ht]
    let q5 : Fin 5 → ℝ × ℝ := fun i => (p (c ⟨2 * i.1, by omega⟩)).1
    have hq5_orient : ∀ i j k : Fin 5, i < j → j < k → 0 < orient (q5 i) (q5 j) (q5 k) := by
      intro i j k hij hjk
      refine hstrict_pair _ _ _ (hcmono.monotone (by show 0 ≤ 2 * i.1; omega))
        (hcmono (by show 2 * i.1 < 2 * j.1; omega)) (hcmono (by show 2 * j.1 < 2 * k.1; omega))
        (by show (c ⟨2 * k.1, by omega⟩).1 ≤ s + C - 1
            have h1 : (c ⟨2 * k.1, by omega⟩).1 ≤ (c ⟨11, by omega⟩).1 := hcmono.monotone (show (⟨2 * k.1, by omega⟩ : Fin 12) ≤ ⟨11, by omega⟩ by show 2 * k.1 ≤ 11; omega)
            have : C = 11 * (ℓ - 1) + 1 := rfl; omega)
        ⟨2 * i.1, by omega, le_rfl, hcmono.monotone (by show 2 * i.1 + 2 ≤ 2 * k.1; omega)⟩
    -- Since ¬ HasEmptyPentagon P, there exists x ∈ P \ range q5 in convexHull ℝ (range q5)!
    have hex_x : ∃ x ∈ P, x ∈ convexHull ℝ (Set.range q5) ∧ x ∉ Set.range q5 := by
      by_contra hall
      push Not at hall
      exact hpent (hasEmptyPentagon_of_cyclic_orient q5
        (fun i => hQP (hullBoundary_subset Q (p (c ⟨2 * i.1, by omega⟩)).2))
        hq5_orient hall)
    obtain ⟨x, hxP, hx_conv, hx_not⟩ := hex_x
    have hxQ : x ∈ Q := hQclosed x hxP (convexHull_mono (by
      rintro _ ⟨i, rfl⟩; exact hullBoundary_subset Q (p (c ⟨2 * i.1, by omega⟩)).2) hx_conv)
    -- Show x ∉ A = hullBoundary Q!
    have hx_notA : x ∉ A := by
      intro hxA
      obtain ⟨_, c₁, c₂, hc, hmax⟩ := mem_hullBoundary.mp hxA
      -- Write x as centerMass of q5; since x ∉ range q5, at least 2 distinct indices have positive weight!
      rw [convexHull_eq] at hx_conv
      obtain ⟨ι, s₀, w₀, f₀, hw0, hw1, hf₀, hcm⟩ := hx_conv
      -- Functional L(y) = c₁ * y.1 + c₂ * y.2 is maximized at x on Q, so L(f₀ i) = L(x) for all i with w₀ i > 0!
      have hL_eq : ∀ i ∈ s₀, 0 < w₀ i → c₁ * (f₀ i).1 + c₂ * (f₀ i).2 = c₁ * x.1 + c₂ * x.2 := by
        intro i hi hwi
        by_contra hne
        have hlt : c₁ * (f₀ i).1 + c₂ * (f₀ i).2 < c₁ * x.1 + c₂ * x.2 := by
          obtain ⟨k, hk⟩ := hf₀ i hi
          exact lt_of_le_of_ne (hmax _ (hk ▸ hullBoundary_subset Q (p (c ⟨2 * k.1, by omega⟩)).2)) hne
        have hsum_lt : ∑ j ∈ s₀, w₀ j * (c₁ * (f₀ j).1 + c₂ * (f₀ j).2) <
            ∑ j ∈ s₀, w₀ j * (c₁ * x.1 + c₂ * x.2) := by
          refine Finset.sum_lt_sum (fun j hj => ?_) ⟨i, hi, mul_lt_mul_of_pos_left hlt hwi⟩
          obtain ⟨k, hk⟩ := hf₀ j hj
          exact mul_le_mul_of_nonneg_left (hmax _ (hk ▸ hullBoundary_subset Q (p (c ⟨2 * k.1, by omega⟩)).2)) (hw0 j hj)
        have hLx : c₁ * x.1 + c₂ * x.2 = ∑ j ∈ s₀, w₀ j * (c₁ * (f₀ j).1 + c₂ * (f₀ j).2) := by
          rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hw1]
          simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
            Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => by ring
        rw [← Finset.sum_mul, hw1, one_mul] at hsum_lt
        linarith
      -- There must be two indices i₁, i₂ ∈ s₀ with w₀ i₁ > 0, w₀ i₂ > 0, and f₀ i₁ ≠ f₀ i₂!
      have hex2 : ∃ k₁ k₂ : Fin 5, k₁ < k₂ ∧
          c₁ * (q5 k₁).1 + c₂ * (q5 k₁).2 = c₁ * x.1 + c₂ * x.2 ∧
          c₁ * (q5 k₂).1 + c₂ * (q5 k₂).2 = c₁ * x.1 + c₂ * x.2 := by
        obtain ⟨i₁, hi₁, hwi₁⟩ : ∃ i ∈ s₀, 0 < w₀ i := by
          by_contra h0; push Not at h0
          have : ∑ i ∈ s₀, w₀ i = 0 := Finset.sum_eq_zero fun i hi => le_antisymm (h0 i hi) (hw0 i hi)
          linarith
        obtain ⟨i₂, hi₂, hwi₂, hne12⟩ : ∃ i ∈ s₀, 0 < w₀ i ∧ f₀ i ≠ f₀ i₁ := by
          by_contra h1; push Not at h1
          have hx_eq : x = f₀ i₁ := by
            rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hw1]
            have : ∑ i ∈ s₀, w₀ i • f₀ i = ∑ i ∈ s₀, w₀ i • f₀ i₁ := by
              refine Finset.sum_congr rfl fun i hi => ?_
              rcases eq_or_lt_of_le (hw0 i hi) with h0 | hp
              · rw [← h0, zero_smul, zero_smul]
              · rw [h1 i hi hp]
            rw [this, ← Finset.sum_smul, hw1, one_smul]
          exact hx_not (hx_eq ▸ hf₀ i₁ hi₁)
        obtain ⟨k₁, hk₁⟩ := hf₀ i₁ hi₁
        obtain ⟨k₂, hk₂⟩ := hf₀ i₂ hi₂
        have hk12 : k₁ ≠ k₂ := fun h => hne12 (by rw [← hk₁, ← hk₂, h])
        rcases lt_or_gt_of_ne hk12 with hlt | hgt
        · exact ⟨k₁, k₂, hlt, hk₁ ▸ hL_eq i₁ hi₁ hwi₁, hk₂ ▸ hL_eq i₂ hi₂ hwi₂⟩
        · exact ⟨k₂, k₁, hgt, hk₂ ▸ hL_eq i₂ hi₂ hwi₂, hk₁ ▸ hL_eq i₁ hi₁ hwi₁⟩
      obtain ⟨k₁, k₂, hk12, hLk1, hLk2⟩ := hex2
      -- Chord (q5 k₁, q5 k₂) has p(c (2*k₁+1)) on < 0 side and p(c 10) on > 0 side!
      have hneg_pt : orient (q5 k₁) (q5 k₂) (p (c ⟨2 * k₁.1 + 1, by omega⟩)) < 0 := by
        have hpos := hstrict_pair (c ⟨2 * k₁.1, by omega⟩) (c ⟨2 * k₁.1 + 1, by omega⟩) (c ⟨2 * k₂.1, by omega⟩)
          (hcmono.monotone (by show 0 ≤ 2 * k₁.1; omega))
          (hcmono (by show 2 * k₁.1 < 2 * k₁.1 + 1; omega))
          (hcmono (by show 2 * k₁.1 + 1 < 2 * k₂.1; omega))
          (by show (c ⟨2 * k₂.1, by omega⟩).1 ≤ s + C - 1
              have h1 : (c ⟨2 * k₂.1, by omega⟩).1 ≤ (c ⟨11, by omega⟩).1 := hcmono.monotone (show (⟨2 * k₂.1, by omega⟩ : Fin 12) ≤ ⟨11, by omega⟩ by show 2 * k₂.1 ≤ 11; omega)
              have : C = 11 * (ℓ - 1) + 1 := rfl; omega)
          ⟨2 * k₁.1, by omega, le_rfl, hcmono.monotone (by show 2 * k₁.1 + 2 ≤ 2 * k₂.1; omega)⟩
        rw [orient_swap_bc] at hpos; linarith
      have hpos_pt : 0 < orient (q5 k₁) (q5 k₂) (p (c ⟨10, by omega⟩)) := by
        refine hstrict_pair (c ⟨2 * k₁.1, by omega⟩) (c ⟨2 * k₂.1, by omega⟩) (c ⟨10, by omega⟩)
          (hcmono.monotone (by show 0 ≤ 2 * k₁.1; omega))
          (hcmono (by show 2 * k₁.1 < 2 * k₂.1; omega))
          (hcmono (by show 2 * k₂.1 < 10; omega))
          (by show (c ⟨10, by omega⟩).1 ≤ s + C - 1
              have h1 : (c ⟨10, by omega⟩).1 ≤ (c ⟨11, by omega⟩).1 := hcmono.monotone (show (⟨10, by omega⟩ : Fin 12) ≤ ⟨11, by omega⟩ by show 10 ≤ 11; omega)
              have : C = 11 * (ℓ - 1) + 1 := rfl; omega)
          ⟨2 * k₁.1, by omega, le_rfl, hcmono.monotone (by show 2 * k₁.1 + 2 ≤ 10; omega)⟩
      exact no_supporting_functional_through_chord
        (hullBoundary_subset Q (p (c ⟨2 * k₁.1 + 1, by omega⟩)).2)
        (hullBoundary_subset Q (p (c ⟨10, by omega⟩)).2)
        hneg_pt hpos_pt hc (by linarith) (fun y hy => by linarith [hmax y hy])
    have hxQ' : x ∈ Q' := Finset.mem_sdiff.mpr ⟨hxQ, hx_notA⟩
    -- Show orient a_s b_s x < 0 where a_s = p s, b_s = p (s + C - 1)
    let a_s : ℝ × ℝ := (p ⟨s, by omega⟩).1
    let b_s : ℝ × ℝ := (p ⟨s + C - 1, by omega⟩).1
    have hq5_0 : q5 0 = a_s := by
      dsimp [q5, a_s]; congr 2; apply Fin.ext; exact hc0
    have hx_neg : orient a_s b_s x < 0 := by
      rw [convexHull_eq] at hx_conv
      obtain ⟨ι, s₀, w₀, f₀, hw0, hw1, hf₀, hcm⟩ := hx_conv
      have hle_all : ∀ i ∈ s₀, orient a_s b_s (f₀ i) ≤ 0 := by
        intro i hi
        obtain ⟨k, hk⟩ := hf₀ i hi
        rw [← hk]
        by_cases hk0 : k.1 = 0
        · have : k = 0 := Fin.ext hk0; rw [this, hq5_0, orient_self_mid]
        · have hpos := hstrict_pair ⟨s, by omega⟩ (c ⟨2 * k.1, by omega⟩) ⟨s + C - 1, by omega⟩
            (by show (c 0).1 ≤ s; omega)
            (by show s < (c ⟨2 * k.1, by omega⟩).1
                have h1 : (c 0).1 < (c ⟨2 * k.1, by omega⟩).1 := hcmono (show (0 : Fin 12) < ⟨2 * k.1, by omega⟩ by show 0 < 2 * k.1; omega)
                omega)
            (by show (c ⟨2 * k.1, by omega⟩).1 < s + C - 1
                have h1 : (c ⟨2 * k.1, by omega⟩).1 < (c ⟨11, by omega⟩).1 := hcmono (show (⟨2 * k.1, by omega⟩ : Fin 12) < ⟨11, by omega⟩ by show 2 * k.1 < 11; omega)
                have : C = 11 * (ℓ - 1) + 1 := rfl; omega)
            le_rfl
            ⟨0, by omega, (by show s ≤ (c 0).1; omega), by
              show (c ⟨2, by omega⟩).1 ≤ s + C - 1
              have h1 : (c ⟨2, by omega⟩).1 ≤ (c ⟨11, by omega⟩).1 :=
                hcmono.monotone (show (⟨2, by omega⟩ : Fin 12) ≤ ⟨11, by omega⟩ by show 2 ≤ 11; omega)
              have : C = 11 * (ℓ - 1) + 1 := rfl
              omega⟩
          have : orient a_s b_s (q5 k) = -orient (p ⟨s, by omega⟩) (p (c ⟨2 * k.1, by omega⟩)) (p ⟨s + C - 1, by omega⟩) :=
            orient_swap_bc _ _ _
          linarith
      obtain ⟨i₀, hi₀, hwi₀, hne_a⟩ : ∃ i ∈ s₀, 0 < w₀ i ∧ f₀ i ≠ a_s := by
        by_contra h1; push Not at h1
        have hx_eq : x = a_s := by
          rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hw1]
          have : ∑ i ∈ s₀, w₀ i • f₀ i = ∑ i ∈ s₀, w₀ i • a_s := by
            refine Finset.sum_congr rfl fun i hi => ?_
            rcases eq_or_lt_of_le (hw0 i hi) with h0 | hp
            · rw [← h0, zero_smul, zero_smul]
            · rw [h1 i hi hp]
          rw [this, ← Finset.sum_smul, hw1, one_smul]
        exact hx_not ⟨0, hq5_0.trans hx_eq.symm⟩
      obtain ⟨k₀, hk₀⟩ := hf₀ i₀ hi₀
      have hk0_ne : k₀.1 ≠ 0 := fun h => hne_a (by rw [← hk₀, show k₀ = 0 from Fin.ext h, hq5_0])
      have hlt0 : orient a_s b_s (f₀ i₀) < 0 := by
        rw [← hk₀]
        have hpos := hstrict_pair ⟨s, by omega⟩ (c ⟨2 * k₀.1, by omega⟩) ⟨s + C - 1, by omega⟩
          (by show (c 0).1 ≤ s; omega)
          (by show s < (c ⟨2 * k₀.1, by omega⟩).1
              have h1 : (c 0).1 < (c ⟨2 * k₀.1, by omega⟩).1 := hcmono (show (0 : Fin 12) < ⟨2 * k₀.1, by omega⟩ by show 0 < 2 * k₀.1; omega)
              omega)
          (by show (c ⟨2 * k₀.1, by omega⟩).1 < s + C - 1
              have h1 : (c ⟨2 * k₀.1, by omega⟩).1 < (c ⟨11, by omega⟩).1 := hcmono (show (⟨2 * k₀.1, by omega⟩ : Fin 12) < ⟨11, by omega⟩ by show 2 * k₀.1 < 11; omega)
              have : C = 11 * (ℓ - 1) + 1 := rfl; omega)
          le_rfl
          ⟨0, by omega, (by show s ≤ (c 0).1; omega), by
            show (c ⟨2, by omega⟩).1 ≤ s + C - 1
            have h1 : (c ⟨2, by omega⟩).1 ≤ (c ⟨11, by omega⟩).1 :=
              hcmono.monotone (show (⟨2, by omega⟩ : Fin 12) ≤ ⟨11, by omega⟩ by show 2 ≤ 11; omega)
            have : C = 11 * (ℓ - 1) + 1 := rfl
            omega⟩
        have : orient a_s b_s (q5 k₀) = -orient (p ⟨s, by omega⟩) (p (c ⟨2 * k₀.1, by omega⟩)) (p ⟨s + C - 1, by omega⟩) :=
          orient_swap_bc _ _ _
        linarith
      have horient_x : orient a_s b_s x = ∑ i ∈ s₀, w₀ i * orient a_s b_s (f₀ i) := by
        rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hw1]
        unfold orient
        simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        have ha1 : (∑ i ∈ s₀, w₀ i * (f₀ i).2) - a_s.2 = ∑ i ∈ s₀, w₀ i * ((f₀ i).2 - a_s.2) := by
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
        have ha2 : (∑ i ∈ s₀, w₀ i * (f₀ i).1) - a_s.1 = ∑ i ∈ s₀, w₀ i * ((f₀ i).1 - a_s.1) := by
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
        rw [ha1, ha2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [horient_x]
      have hsum_lt : ∑ i ∈ s₀, w₀ i * orient a_s b_s (f₀ i) < ∑ i ∈ s₀, (0 : ℝ) :=
        Finset.sum_lt_sum (fun i hi => mul_nonpos_of_nonneg_of_nonpos (hw0 i hi) (hle_all i hi))
          ⟨i₀, hi₀, mul_neg_of_pos_of_neg hwi₀ hlt0⟩
      simpa using hsum_lt
    -- Pick y ∈ Q' minimizing orient a_s b_s y!
    obtain ⟨y, hyQ', hymin⟩ := Q'.exists_min_image (fun q => orient a_s b_s q) ⟨x, hxQ'⟩
    have hy_neg : orient a_s b_s y < 0 := lt_of_le_of_lt (hymin x hxQ') hx_neg
    have hab_ne : a_s ≠ b_s := fun h => by
      have := p.injective (Subtype.ext h); have := congrArg Fin.val this; dsimp [C] at this; omega
    have hyA' : y ∈ A' := by
      rw [mem_hullBoundary]
      refine ⟨hyQ', b_s.2 - a_s.2, -(b_s.1 - a_s.1), ?_, fun w hw => ?_⟩
      · by_contra h0; push Not at h0; exact hab_ne (Prod.ext (by linarith) (by linarith))
      · have hle := hymin w hw
        unfold orient at hle; linarith
    -- Show y ∈ convexHull ℝ B_s via hullBoundary_convexHull_cap!
    let B_s : Finset (ℝ × ℝ) := (Finset.univ.filter (fun i : Fin #A => s ≤ i.1 ∧ i.1 < s + C)).image (fun i => (p i).1)
    have hBA : B_s ⊆ A := by
      intro w hw; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw; exact (p i).2
    have haB : a_s ∈ B_s := Finset.mem_image.mpr ⟨⟨s, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, by dsimp; omega⟩, rfl⟩
    have hbB : b_s ∈ B_s := Finset.mem_image.mpr ⟨⟨s + C - 1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, by dsimp; omega⟩, rfl⟩
    -- Find a point v_out ∈ A \ B_s with orient a_s b_s v_out > 0 (exists since #A ≥ 3 * C and ¬ HasCollinear ℓ P)!
    have hv_out : ∃ v ∈ Q, 0 < orient a_s b_s v := by
      by_contra hall; push Not at hall
      have hzero : ∀ w ∈ A \ B_s, orient a_s b_s w = 0 := fun w hw => by
        have hwA := (Finset.mem_sdiff.mp hw).1
        have hwB := (Finset.mem_sdiff.mp hw).2
        let idx := p.symm ⟨w, hwA⟩
        have hidx_eq : (p idx).1 = w := congrArg Subtype.val (p.apply_symm_apply ⟨w, hwA⟩)
        have hidx_not : ¬(s ≤ idx.1 ∧ idx.1 < s + C) := fun h =>
          hwB (Finset.mem_image.mpr ⟨idx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hidx_eq⟩)
        have hge : 0 ≤ orient a_s b_s w := by
          rw [← hidx_eq]
          rcases lt_or_ge idx.1 s with hlt | hge'
          · rw [orient_cyclic, orient_cyclic]
            exact ho_nonneg idx ⟨s, by omega⟩ ⟨s + C - 1, by omega⟩
              (Fin.mk_lt_mk.mpr hlt) (Fin.mk_lt_mk.mpr (by dsimp [C]; omega))
          · exact ho_nonneg ⟨s, by omega⟩ ⟨s + C - 1, by omega⟩ idx
              (Fin.mk_lt_mk.mpr (by dsimp [C]; omega)) (by show s + C - 1 < idx.1; have : ¬(s ≤ idx.1 ∧ idx.1 < s + C) := hidx_not; omega)
        exact le_antisymm (hall w (hullBoundary_subset Q hwA)) hge
      have hcard_sdiff : ℓ ≤ #(A \ B_s) := by
        have h1 : #B_s ≤ C := by
          calc #B_s ≤ #(Finset.univ.filter fun i : Fin #A => s ≤ i.1 ∧ i.1 < s + C) := Finset.card_image_le
            _ ≤ C := by
              have hsub : (Finset.univ.filter fun i : Fin #A => s ≤ i.1 ∧ i.1 < s + C) ⊆
                  (Finset.range C).attach.image (fun x => ⟨s + x.1, by have := Finset.mem_range.mp x.2; omega⟩) := by
                intro i hi
                have hi' := (Finset.mem_filter.mp hi).2
                exact Finset.mem_image.mpr ⟨⟨i.1 - s, Finset.mem_range.mpr (by omega)⟩, Finset.mem_attach _ _,
                  Fin.ext (by dsimp; omega)⟩
              calc _ ≤ #((Finset.range C).attach.image _) := Finset.card_le_card hsub
                _ ≤ #(Finset.range C).attach := Finset.card_image_le
                _ = C := by rw [Finset.card_attach, Finset.card_range]
        have h2 := Finset.card_sdiff_add_card_eq_card hBA
        dsimp [C] at hsmall ⊢; omega
      obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcard_sdiff
      exact hcol ⟨S, hSsub.trans ((Finset.sdiff_subset.trans (hullBoundary_subset Q)).trans hQP), hScard,
        collinear_of_orient_eq_zero hab_ne fun w hw => hzero w (hSsub (Finset.mem_coe.mp hw))⟩
    obtain ⟨v_pt, hvQ, hv_pos⟩ := hv_out
    have hy_cap : y ∈ convexHull ℝ (B_s : Set (ℝ × ℝ)) := by
      refine hullBoundary_convexHull_cap hBA haB hbB hxQ hvQ hx_neg hv_pos ?_ ?_
        (subset_convexHull_hullBoundary Q (Finset.mem_sdiff.mp hyQ').1) hy_neg
      · intro w hw
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
        have hi' := (Finset.mem_filter.mp hi).2
        by_cases h1 : i.1 = s
        · have : i = ⟨s, by omega⟩ := Fin.ext h1; rw [this]; exact (orient_self_mid _ _).le
        · by_cases h2 : i.1 = s + C - 1
          · have : i = ⟨s + C - 1, by omega⟩ := Fin.ext h2; rw [this]; exact (orient_self_right _ _).le
          · have hge := ho_nonneg ⟨s, by omega⟩ i ⟨s + C - 1, by omega⟩
              (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
            rw [orient_swap_bc] at hge; linarith
      · intro w hw
        have hwA := (Finset.mem_sdiff.mp hw).1
        have hwB := (Finset.mem_sdiff.mp hw).2
        let idx := p.symm ⟨w, hwA⟩
        have hidx_eq : (p idx).1 = w := congrArg Subtype.val (p.apply_symm_apply ⟨w, hwA⟩)
        have hidx_not : ¬(s ≤ idx.1 ∧ idx.1 < s + C) := fun h =>
          hwB (Finset.mem_image.mpr ⟨idx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hidx_eq⟩)
        rw [← hidx_eq]
        rcases lt_or_ge idx.1 s with hlt | hge'
        · rw [orient_cyclic, orient_cyclic]
          exact ho_nonneg idx ⟨s, by omega⟩ ⟨s + C - 1, by omega⟩
            (Fin.mk_lt_mk.mpr hlt) (Fin.mk_lt_mk.mpr (by dsimp [C]; omega))
        · exact ho_nonneg ⟨s, by omega⟩ ⟨s + C - 1, by omega⟩ idx
            (Fin.mk_lt_mk.mpr (by dsimp [C]; omega)) (by show s + C - 1 < idx.1; have : ¬(s ≤ idx.1 ∧ idx.1 < s + C) := hidx_not; omega)
    exact ⟨y, hyA', hy_neg, hy_cap⟩
  -- Apply hblock to all q₁ = m₁ / C blocks in [0, m₁) and q₂ = (#A - m₂) / C blocks in [m₂, #A)!
  set q₁ := m₁ / C
  set q₂ := (#A - m₂) / C
  let startOf : Fin q₁ ⊕ Fin q₂ → ℕ := fun r =>
    match r with
    | Sum.inl i => i.1 * C
    | Sum.inr j => m₂ + j.1 * C
  have hstart_bd : ∀ r, startOf r + C ≤ #A := by
    rintro (i | j)
    · dsimp [startOf]
      have h1 : (i.1 + 1) * C ≤ q₁ * C := Nat.mul_le_mul_right C (by omega)
      have h2 : q₁ * C ≤ m₁ := Nat.div_mul_le_self m₁ C
      have h3 : m₁ ≤ #A := by simpa using Finset.card_le_univ I_neg
      linarith
    · dsimp [startOf]
      have h1 : (j.1 + 1) * C ≤ q₂ * C := Nat.mul_le_mul_right C (by omega)
      have h2 : q₂ * C ≤ #A - m₂ := Nat.div_mul_le_self (#A - m₂) C
      have hmul : j.1 * C + C = (j.1 + 1) * C := by ring
      have hm2_le : m₂ ≤ #A := Nat.sub_le _ _
      omega
  have hstart_pi : ∀ r, θ (p ⟨startOf r + C - 1, by have := hstart_bd r; omega⟩).1 -
      θ (p ⟨startOf r, by have := hstart_bd r; omega⟩).1 < Real.pi := by
    rintro (i | j)
    · have h1 : (i.1 + 1) * C ≤ m₁ := le_trans (Nat.mul_le_mul_right C (by omega)) (Nat.div_mul_le_self m₁ C)
      have hhi : θ (p ⟨startOf (Sum.inl i) + C - 1, by have := hstart_bd (Sum.inl i); omega⟩).1 < 0 :=
        (hm1_prop _).mp (by
          show startOf (Sum.inl i) + C - 1 < m₁
          dsimp [startOf]
          have : i.1 * C + C = (i.1 + 1) * C := by ring
          omega)
      have hlo : -Real.pi < θ (p ⟨startOf (Sum.inl i), by have := hstart_bd (Sum.inl i); omega⟩).1 :=
        Complex.neg_pi_lt_arg _
      linarith
    · have hlo : 0 < θ (p ⟨startOf (Sum.inr j), by have := hstart_bd (Sum.inr j); omega⟩).1 :=
        (hm2_prop _).mp (by dsimp [startOf]; omega)
      have hhi : θ (p ⟨startOf (Sum.inr j) + C - 1, by have := hstart_bd (Sum.inr j); omega⟩).1 ≤ Real.pi :=
        Complex.arg_le_pi _
      linarith
  choose y hyA' hy_neg hy_cap using fun r => hblock (startOf r) (hstart_bd r) (hstart_pi r)
  have hy_inj : Function.Injective y := by
    intro r₁ r₂ heq
    by_contra hne
    have hdisj : ∀ i : Fin #A, startOf r₂ ≤ i.1 → i.1 < startOf r₂ + C →
        ¬(startOf r₁ ≤ i.1 ∧ i.1 < startOf r₁ + C) := by
      intro i hi1 hi2 ⟨h1, h2⟩
      cases r₁ with
      | inl i₁ =>
        cases r₂ with
        | inl i₂ =>
          have hi12 : i₁.1 ≠ i₂.1 := fun h => hne (congrArg Sum.inl (Fin.ext h))
          dsimp [startOf] at hi1 hi2 h1 h2
          rcases lt_or_gt_of_ne hi12 with hlt | hgt
          · have : (i₁.1 + 1) * C ≤ i₂.1 * C := Nat.mul_le_mul_right C (by omega)
            linarith
          · have : (i₂.1 + 1) * C ≤ i₁.1 * C := Nat.mul_le_mul_right C (by omega)
            linarith
        | inr j₂ =>
          dsimp [startOf] at hi1 hi2 h1 h2
          have hmul : i₁.1 * C + C = (i₁.1 + 1) * C := by ring
          have : (i₁.1 + 1) * C ≤ m₁ := le_trans (Nat.mul_le_mul_right C (by omega)) (Nat.div_mul_le_self m₁ C)
          omega
      | inr j₁ =>
        cases r₂ with
        | inl i₂ =>
          dsimp [startOf] at hi1 hi2 h1 h2
          have hmul : i₂.1 * C + C = (i₂.1 + 1) * C := by ring
          have : (i₂.1 + 1) * C ≤ m₁ := le_trans (Nat.mul_le_mul_right C (by omega)) (Nat.div_mul_le_self m₁ C)
          omega
        | inr j₂ =>
          have hj12 : j₁.1 ≠ j₂.1 := fun h => hne (congrArg Sum.inr (Fin.ext h))
          dsimp [startOf] at hi1 hi2 h1 h2
          rcases lt_or_gt_of_ne hj12 with hlt | hgt
          · have : (j₁.1 + 1) * C ≤ j₂.1 * C := Nat.mul_le_mul_right C (by omega)
            linarith
          · have : (j₂.1 + 1) * C ≤ j₁.1 * C := Nat.mul_le_mul_right C (by omega)
            linarith
    have hge : 0 ≤ orient (p ⟨startOf r₁, by have := hstart_bd r₁; omega⟩)
        (p ⟨startOf r₁ + C - 1, by have := hstart_bd r₁; omega⟩) (y r₂) := by
      refine orient_ge_of_mem_convexHull (hy_cap r₂) ?_
      intro w hw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw)
      have hi' := (Finset.mem_filter.mp hi).2
      have hnot := hdisj i hi'.1 hi'.2
      rcases lt_or_ge i.1 (startOf r₁) with hlt | hge'
      · rw [orient_cyclic, orient_cyclic]
        exact ho_nonneg i ⟨startOf r₁, by have := hstart_bd r₁; omega⟩
          ⟨startOf r₁ + C - 1, by have := hstart_bd r₁; omega⟩
          (Fin.mk_lt_mk.mpr hlt) (Fin.mk_lt_mk.mpr (by dsimp [C]; omega))
      · exact ho_nonneg ⟨startOf r₁, by have := hstart_bd r₁; omega⟩
          ⟨startOf r₁ + C - 1, by have := hstart_bd r₁; omega⟩ i
          (Fin.mk_lt_mk.mpr (by dsimp [C]; omega)) (by show startOf r₁ + C - 1 < i.1; omega)
    rw [← heq] at hge
    linarith [hy_neg r₁]
  have hcard_q : q₁ + q₂ ≤ #A' := by
    have h1 : #(Finset.univ.image y) ≤ #A' := Finset.card_le_card fun w hw => by
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hw; exact hyA' r
    rw [Finset.card_image_of_injective _ hy_inj, Finset.card_univ, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin] at h1
    exact h1
  have hdiv1 : m₁ < C * (q₁ + 1) := by
    simpa [q₁, mul_add] using Nat.lt_mul_div_succ m₁ hC_pos
  have hdiv2 : #A - m₂ < C * (q₂ + 1) := by
    simpa [q₂, mul_add] using Nat.lt_mul_div_succ (#A - m₂) hC_pos
  have hm2_le_A : m₂ ≤ #A := Nat.sub_le _ _
  have hA_le : #A ≤ m₁ + (#A - m₂) + 1 := by omega
  nlinarith

/- ### Part 4: Convex layer recursion, empty-arc followers, Claims B & C, and 5-hole construction -/

private lemma layer_convexClosed {P Q : Finset (ℝ × ℝ)}
    (hQclosed : ∀ x ∈ P, x ∈ convexHull ℝ (Q : Set (ℝ × ℝ)) → x ∈ Q) :
    ∀ x ∈ P, x ∈ convexHull ℝ ((Q \ hullBoundary Q : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) →
      x ∈ Q \ hullBoundary Q := by
  intro x hxP hxconv
  have hxQ : x ∈ Q := hQclosed x hxP (convexHull_mono (Finset.coe_subset.mpr Finset.sdiff_subset) hxconv)
  refine Finset.mem_sdiff.mpr ⟨hxQ, fun hxB => ?_⟩
  obtain ⟨_, a, b, hab, hmax⟩ := mem_hullBoundary.mp hxB
  have hlt_all : ∀ y ∈ (Q \ hullBoundary Q : Finset (ℝ × ℝ)),
      a * y.1 + b * y.2 < a * x.1 + b * x.2 := by
    intro y hy
    have hyQ := (Finset.mem_sdiff.mp hy).1
    have hyB := (Finset.mem_sdiff.mp hy).2
    refine lt_of_le_of_ne (hmax y hyQ) (fun heq => hyB ?_)
    exact mem_hullBoundary.mpr ⟨hyQ, a, b, hab, fun w hw => by linarith [hmax w hw]⟩
  have hconv_lt : Convex ℝ {y : ℝ × ℝ | a * y.1 + b * y.2 < a * x.1 + b * x.2} := by
    intro u hu v hv r₁ r₂ hr₁ hr₂ hr12
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hu hv ⊢
    have hlin : a * (r₁ * u.1 + r₂ * v.1) + b * (r₁ * u.2 + r₂ * v.2) =
        r₁ * (a * u.1 + b * u.2) + r₂ * (a * v.1 + b * v.2) := by ring
    rw [hlin]
    rcases eq_or_lt_of_le hr₁ with rfl | hr₁'
    · have : r₂ = 1 := by linarith
      subst this; linarith
    · have h1 := mul_lt_mul_of_pos_left hu hr₁'
      have h2 := mul_le_mul_of_nonneg_left hv.le hr₂
      linarith [show r₁ * (a * x.1 + b * x.2) + r₂ * (a * x.1 + b * x.2) =
        a * x.1 + b * x.2 by linear_combination (a * x.1 + b * x.2) * hr12]
  have hlt_x : a * x.1 + b * x.2 < a * x.1 + b * x.2 :=
    convexHull_min (fun y hy => hlt_all y (Finset.mem_coe.mp hy)) hconv_lt hxconv
  exact lt_irrefl _ hlt_x

private lemma inConvexPos_subset_hullBoundary {P X : Finset (ℝ × ℝ)}
    (hXP : X ⊆ P) (hX3 : 3 ≤ #X) (hX : InConvexPos X) :
    let Q := by classical exact P.filter fun x => x ∈ convexHull ℝ (X : Set (ℝ × ℝ))
    Q ⊆ P ∧
    (∀ x ∈ P, x ∈ convexHull ℝ (Q : Set (ℝ × ℝ)) → x ∈ Q) ∧
    X ⊆ hullBoundary Q := by
  classical
  intro Q
  have hQP : Q ⊆ P := Finset.filter_subset _ P
  have hXQ : X ⊆ Q := fun x hx => Finset.mem_filter.mpr ⟨hXP hx, subset_convexHull ℝ _ hx⟩
  have hQconv : ∀ x ∈ Q, x ∈ convexHull ℝ (X : Set (ℝ × ℝ)) := fun x hx => (Finset.mem_filter.mp hx).2
  have hQclosed : ∀ x ∈ P, x ∈ convexHull ℝ (Q : Set (ℝ × ℝ)) → x ∈ Q := fun x hxP hx =>
    Finset.mem_filter.mpr ⟨hxP, convexHull_min hQconv (convex_convexHull ℝ _) hx⟩
  refine ⟨hQP, hQclosed, fun x hx => ?_⟩
  obtain ⟨p, ho⟩ := hX
  let i := p.symm ⟨x, hx⟩
  have hi_eq : (p i).1 = x := congrArg Subtype.val (p.apply_symm_apply ⟨x, hx⟩)
  let j : Fin #X := ⟨(i.1 + 1) % #X, Nat.mod_lt _ (by omega)⟩
  have hij_ne : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [j] at hv
    by_cases h1 : i.1 + 1 < #X
    · rw [Nat.mod_eq_of_lt h1] at hv; omega
    · have : i.1 + 1 = #X := by omega
      rw [this, Nat.mod_self] at hv; omega
  have hxy_ne : (p i).1 ≠ (p j).1 := fun h => hij_ne (p.injective (Subtype.ext h))
  -- Show orient (p i) (p j) y ≥ 0 for all y ∈ X, hence for all y ∈ Q ⊆ convexHull ℝ X!
  have hge_X : ∀ y ∈ X, 0 ≤ orient (p i) (p j) y := by
    intro y hy
    let k := p.symm ⟨y, hy⟩
    have hk_eq : (p k).1 = y := congrArg Subtype.val (p.apply_symm_apply ⟨y, hy⟩)
    rw [← hk_eq]
    by_cases hki : k = i
    · rw [hki, orient_self_mid]
    · by_cases hkj : k = j
      · rw [hkj, orient_self_right]
      · by_cases h1 : i.1 + 1 < #X
        · have hjval : j.1 = i.1 + 1 := Nat.mod_eq_of_lt h1
          rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hki) with hlt | hgt
          · rw [orient_cyclic, orient_cyclic]
            exact ho k i j (by show k.1 < i.1; exact hlt) (by show i.1 < j.1; omega)
          · have hkgt : j.1 < k.1 := by have := Fin.val_ne_of_ne hkj; omega
            exact ho i j k (by show i.1 < j.1; omega) (by show j.1 < k.1; exact hkgt)
        · have hival : i.1 = #X - 1 := by omega
          have hjval : j.1 = 0 := by dsimp [j]; rw [show i.1 + 1 = #X by omega, Nat.mod_self]
          have h1' : j < k := by show j.1 < k.1; have := Fin.val_ne_of_ne hkj; omega
          have h2' : k < i := by show k.1 < i.1; have := Fin.val_ne_of_ne hki; omega
          rw [orient_cyclic]
          exact ho j k i h1' h2'
  rw [mem_hullBoundary]
  refine ⟨hXQ hx, (p j).1.2 - (p i).1.2, -((p j).1.1 - (p i).1.1), ?_, fun y hy => ?_⟩
  · by_contra h0; push Not at h0; exact hxy_ne (Prod.ext (by linarith) (by linarith))
  · have hge : 0 ≤ orient (p i) (p j) y :=
      orient_ge_of_mem_convexHull (hQconv y hy) (fun w hw => hge_X w (Finset.mem_coe.mp hw))
    rw [← hi_eq]
    unfold orient at hge; linarith

/-- Every consecutive arc `(x, y)` of `hullBoundary Q` (ordered by angle around a strict interior
    point `z`) satisfies `0 < orient z x y`, `0 ≤ orient x y w` for all `w ∈ Q`, and
    `0 < orient x y w` for all `w ∈ Q \ hullBoundary Q`. -/
private lemma arc_orient_props {Q : Finset (ℝ × ℝ)} {z : ℝ × ℝ}
    (hz : ∀ u v : ℝ, (u ≠ 0 ∨ v ≠ 0) → ∃ w ∈ Q, u * z.1 + v * z.2 < u * w.1 + v * w.2)
    (hA3 : 3 ≤ #(hullBoundary Q))
    (p : Fin #(hullBoundary Q) ≃ hullBoundary Q)
    (hp_arg : StrictMono fun t => Complex.arg (toC ((p t).1 - z)))
    (k : Fin #(hullBoundary Q)) :
    let x := (p k).1
    let y := (p ⟨(k.1 + 1) % #(hullBoundary Q), Nat.mod_lt _ (by omega)⟩).1
    0 < orient z x y ∧
    (∀ w ∈ Q, 0 ≤ orient x y w) ∧
    (∀ w ∈ Q \ hullBoundary Q, 0 < orient x y w) := by
  intro x y
  let k' : Fin #(hullBoundary Q) := ⟨(k.1 + 1) % #(hullBoundary Q), Nat.mod_lt _ (by omega)⟩
  have hkk' : k ≠ k' := by
    intro h; have hv := congrArg Fin.val h; dsimp [k'] at hv
    by_cases h1 : k.1 + 1 < #(hullBoundary Q)
    · rw [Nat.mod_eq_of_lt h1] at hv; omega
    · rw [show k.1 + 1 = #(hullBoundary Q) by omega, Nat.mod_self] at hv; omega
  have hxy_ne : x ≠ y := fun h => hkk' (p.injective (Subtype.ext h))
  have ho_nonneg : ∀ i j m : Fin #(hullBoundary Q), i < j → j < m → 0 ≤ orient (p i) (p j) (p m) :=
    fun i j m hij hjm => orient_nonneg_of_arg_lt hz (p i).2 (p j).2 (p m).2 (hp_arg hij) (hp_arg hjm)
  -- First: orient x y w ≥ 0 for all w ∈ hullBoundary Q, hence for all w ∈ Q ⊆ convexHull (hullBoundary Q)!
  have hge_A : ∀ w ∈ hullBoundary Q, 0 ≤ orient x y w := by
    intro w hw
    let m := p.symm ⟨w, hw⟩
    have hm_eq : (p m).1 = w := congrArg Subtype.val (p.apply_symm_apply ⟨w, hw⟩)
    rw [← hm_eq]
    by_cases hmk : m = k
    · rw [hmk]; exact (orient_self_mid _ _).ge
    · by_cases hmk' : m = k'
      · rw [hmk']; exact (orient_self_right _ _).ge
      · by_cases h1 : k.1 + 1 < #(hullBoundary Q)
        · have hk'v : k'.1 = k.1 + 1 := Nat.mod_eq_of_lt h1
          rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hmk) with hlt | hgt
          · rw [orient_cyclic, orient_cyclic]
            exact ho_nonneg m k k' (by show m.1 < k.1; exact hlt) (by show k.1 < k'.1; omega)
          · exact ho_nonneg k k' m (by show k.1 < k'.1; omega)
              (by show k'.1 < m.1; have := Fin.val_ne_of_ne hmk'; omega)
        · have hkv : k.1 = #(hullBoundary Q) - 1 := by omega
          have hk'v : k'.1 = 0 := by dsimp [k']; rw [show k.1 + 1 = #(hullBoundary Q) by omega, Nat.mod_self]
          rw [orient_cyclic]
          exact ho_nonneg k' m k (by show k'.1 < m.1; have := Fin.val_ne_of_ne hmk'; omega)
            (by show m.1 < k.1; have := Fin.val_ne_of_ne hmk; omega)
  have hge_Q : ∀ w ∈ Q, 0 ≤ orient x y w := fun w hw =>
    orient_ge_of_mem_convexHull (subset_convexHull_hullBoundary Q hw)
      (fun u hu => hge_A u (Finset.mem_coe.mp hu))
  have hpos_int : ∀ w ∈ Q \ hullBoundary Q, 0 < orient x y w := by
    intro w hw
    have hwQ := (Finset.mem_sdiff.mp hw).1
    have hwB := (Finset.mem_sdiff.mp hw).2
    refine lt_of_le_of_ne (hge_Q w hwQ) (fun h0 => hwB ?_)
    rw [mem_hullBoundary]
    refine ⟨hwQ, y.2 - x.2, -(y.1 - x.1), ?_, fun u hu => ?_⟩
    · by_contra h'; push Not at h'; exact hxy_ne (Prod.ext (by linarith) (by linarith))
    · have h1 := hge_Q u hu
      unfold orient at h1 h0; linarith
  have hz_pos : 0 < orient z x y := by
    rw [orient_cyclic]
    have hz_ge : 0 ≤ orient x y z := by
      -- Since orient x y u ≥ 0 for all u ∈ Q, if orient x y z ≤ 0 then -(orient x y) would be maximized at z?
      -- Wait: z is strictly interior, so ∃ u ∈ Q with a*z.1 + b*z.2 < a*u.1 + b*u.2 for a = y.2 - x.2, b = -(y.1 - x.1)!
      -- Wait: a*u.1 + b*u.2 = -orient x y u + (y.2 - x.2)*x.1 - (y.1 - x.1)*x.2 ≤ const!
      -- So a*z.1 + b*z.2 < a*u.1 + b*u.2 ≤ const = a*x.1 + b*x.2, which IS orient x y z > 0!!
      have hab : y.2 - x.2 ≠ 0 ∨ -(y.1 - x.1) ≠ 0 := by
        by_contra h'; push Not at h'; exact hxy_ne (Prod.ext (by linarith) (by linarith))
      obtain ⟨u, huQ, hlt⟩ := hz (y.2 - x.2) (-(y.1 - x.1)) hab
      have hu := hge_Q u huQ
      unfold orient at hu ⊢; linarith
    -- Actually the same 3 lines give 0 < orient x y z directly!
    have hab : y.2 - x.2 ≠ 0 ∨ -(y.1 - x.1) ≠ 0 := by
      by_contra h'; push Not at h'; exact hxy_ne (Prod.ext (by linarith) (by linarith))
    obtain ⟨u, huQ, hlt⟩ := hz (y.2 - x.2) (-(y.1 - x.1)) hab
    have hu := hge_Q u huQ
    unfold orient at hu ⊢; linarith
  exact ⟨hz_pos, hge_Q, hpos_int⟩

/-- Unified Claims B & C: from an empty 4-hole `(x, y, q, p)` and `¬ HasEmptyPentagon P`,
    no point `r ∈ P` can lie in the cone `orient p q r > 0 ∧ orient y q r > 0 ∧ orient x r p > 0 ∧ orient x y r > 0`. -/
private lemma mem_convexHull_quad_of_pentagon_le {x y q r p w : ℝ × ℝ}
    (hxyq : 0 < orient x y q) (hxyp : 0 < orient x y p)
    (hxqp : 0 < orient x q p) (hyqp : 0 < orient y q p)
    (hpqr : 0 < orient p q r) (hyqr : 0 < orient y q r) (hxrp : 0 < orient x r p)
    (hwconv : w ∈ convexHull ℝ (Set.range (fun i : Fin 5 => match i with | ⟨0, _⟩ => x | ⟨1, _⟩ => y | ⟨2, _⟩ => q | ⟨3, _⟩ => r | ⟨4, _⟩ => p)))
    (hpqw : orient p q w ≤ 0) :
    w ∈ convexHull ℝ ({x, y, q, p} : Set (ℝ × ℝ)) := by
  let q5 : Fin 5 → ℝ × ℝ := fun i => match i with | ⟨0, _⟩ => x | ⟨1, _⟩ => y | ⟨2, _⟩ => q | ⟨3, _⟩ => r | ⟨4, _⟩ => p
  classical
  rw [convexHull_eq] at hwconv
  obtain ⟨ι, s, f, g, hf0, hf1, hg, hcm⟩ := hwconv
  -- Wait: if w is a convex combination of {x, y, q, r, p} with orient p q w ≤ 0,
  -- replace any r-weight with a point on segment [p, q] via the crossing point of [u, r] with line p—q!
  let s₁ := s.filter fun i => g i ≠ r
  let s₂ := s.filter fun i => g i = r
  let W₁ := ∑ i ∈ s₁, f i
  let W₂ := ∑ i ∈ s₂, f i
  have hdisj : Disjoint s₁ s₂ := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h1 h2
  have hunion : s₁ ∪ s₂ = s := by
    ext i; simp only [s₁, s₂, Finset.mem_union, Finset.mem_filter]; tauto
  have hWsum : W₁ + W₂ = 1 := by dsimp [W₁, W₂]; rw [← Finset.sum_union hdisj, hunion, hf1]
  have hW1_0 : 0 ≤ W₁ := Finset.sum_nonneg fun i hi => hf0 i (Finset.mem_filter.mp hi).1
  have hW2_0 : 0 ≤ W₂ := Finset.sum_nonneg fun i hi => hf0 i (Finset.mem_filter.mp hi).1
  have hgi4 : ∀ i ∈ s₁, g i ∈ ({x, y, q, p} : Set (ℝ × ℝ)) := by
    intro i hi
    have hmem := hg i (Finset.mem_filter.mp hi).1
    have hne := (Finset.mem_filter.mp hi).2
    obtain ⟨idx, hidx⟩ := hmem
    fin_cases idx <;> dsimp only [q5] at hidx <;> rw [← hidx] at hne ⊢ <;> first | exact absurd rfl hne | simp
  have hW1_pos : 0 < W₁ := by
    rcases eq_or_lt_of_le hW1_0 with h0 | hp
    · exfalso
      have hall0 : ∀ i ∈ s₁, f i = 0 := fun i hi =>
        (Finset.sum_eq_zero_iff_of_nonneg fun j hj => hf0 j (Finset.mem_filter.mp hj).1).mp h0.symm i hi
      have hw_eq : w = r := by
        have hW2_1 : W₂ = 1 := by linarith
        rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hf1, ← hunion, Finset.sum_union hdisj,
          Finset.sum_eq_zero (fun i hi => by rw [hall0 i hi, zero_smul]), zero_add]
        have : ∑ i ∈ s₂, f i • g i = ∑ i ∈ s₂, f i • r :=
          Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
        rw [this, ← Finset.sum_smul]; change W₂ • r = r; rw [hW2_1, one_smul]
      rw [hw_eq] at hpqw; linarith
    · exact hp
  let u := s₁.centerMass (fun i => f i / W₁) g
  have hu4 : u ∈ convexHull ℝ ({x, y, q, p} : Set (ℝ × ℝ)) := by
    rw [convexHull_eq]
    exact ⟨ι, s₁, fun i => f i / W₁, g,
      fun i hi => div_nonneg (hf0 i (Finset.mem_filter.mp hi).1) hW1_pos.le,
      by rw [← Finset.sum_div, div_self (ne_of_gt hW1_pos)], hgi4, rfl⟩
  have hW1u : W₁ • u = ∑ i ∈ s₁, f i • g i := by
    have h1 : ∑ i ∈ s₁, f i / W₁ = 1 := by rw [← Finset.sum_div, div_self (ne_of_gt hW1_pos)]
    dsimp only [u]; rw [Finset.centerMass_eq_of_sum_1 _ _ h1, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_div_cancel₀ _ (ne_of_gt hW1_pos)]
  have hw_comb : w = W₁ • u + W₂ • r := by
    rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hf1, ← hunion, Finset.sum_union hdisj, hW1u]
    congr 1
    have : ∑ i ∈ s₂, f i • g i = ∑ i ∈ s₂, f i • r :=
      Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
    rw [this, ← Finset.sum_smul]
  rcases eq_or_lt_of_le hW2_0 with hW20 | hW2_pos
  · have hW1_1 : W₁ = 1 := by linarith
    rw [hw_comb, ← hW20, zero_smul, add_zero, hW1_1, one_smul]; exact hu4
  · -- u ∈ conv{x, y, q, p} has orient p q u ≤ 0 (actually < 0 since W₂ > 0, orient p q r > 0, orient p q w ≤ 0)!
    have hu_neg : orient p q u < 0 := by
      have := orient_add_smul p q u r W₁ W₂ hWsum
      rw [← hw_comb] at this; nlinarith
    -- Crossing point w₀ of [u, r] with line p—q satisfies orient p q w₀ = 0 and lies in segment [p, q]!
    set t := (-orient p q u) / (orient p q r - orient p q u)
    have hden : 0 < orient p q r - orient p q u := by linarith
    have ht0 : 0 < t := div_pos (by linarith) hden
    have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
    let w₀ : ℝ × ℝ := (1 - t) • u + t • r
    have hw₀_0 : orient p q w₀ = 0 := by
      dsimp [w₀]; rw [orient_add_smul p q u r (1 - t) t (by ring)]
      dsimp [t]; field_simp [ne_of_gt hden]; ring
    -- Show w₀ ∈ segment ℝ p q using orient y q w₀ ≥ 0 and orient x w₀ p ≥ 0!
    have hw₀_yq : 0 ≤ orient y q w₀ := by
      dsimp [w₀]; rw [orient_add_smul y q u r (1 - t) t (by ring)]
      have huyq : 0 ≤ orient y q u := orient_ge_of_mem_convexHull hu4 fun v hv => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with hv | hv | hv | hv <;> rw [hv]
        · have : orient y q x = orient x y q := by unfold orient; ring
          linarith
        · exact (orient_self_mid _ _).ge
        · exact (orient_self_right _ _).ge
        · exact hyqp.le
      nlinarith
    have hw₀_xp : 0 ≤ orient x w₀ p := by
      have hsw : orient x w₀ p = -orient x p w₀ := by unfold orient; ring
      rw [hsw]; dsimp [w₀]; rw [orient_add_smul x p u r (1 - t) t (by ring)]
      have huxp : orient x p u ≤ 0 := orient_le_of_mem_convexHull hu4 fun v hv => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with hv | hv | hv | hv <;> rw [hv]
        · exact (orient_self_mid _ _).le
        · have : orient x p y = -orient x y p := by unfold orient; ring
          linarith
        · have : orient x p q = -orient x q p := by unfold orient; ring
          linarith
        · exact (orient_self_right _ _).le
      have hrxp : orient x p r < 0 := by
        have : orient x p r = -orient x r p := by unfold orient; ring
        linarith
      nlinarith
    have hw₀_seg : w₀ ∈ segment ℝ p q := by
      -- Express w₀ = (1 - s) • p + s • q; orient y q w₀ ≥ 0 => (1 - s) * orient y q p ≥ 0 => s ≤ 1!
      -- orient x w₀ p ≥ 0 => s * orient x q p ≥ 0 => 0 ≤ s!
      have hpq_ne : p ≠ q := fun h => by rw [h, orient_self_left] at hpqr; exact lt_irrefl 0 hpqr
      have hex_s : ∃ s : ℝ, w₀ = (1 - s) • p + s • q := by
        by_cases h1 : q.1 - p.1 ≠ 0
        · refine ⟨(w₀.1 - p.1) / (q.1 - p.1), ?_⟩
          ext
          · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; field_simp; ring
          · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
            unfold orient at hw₀_0; field_simp; linear_combination hw₀_0
        · push Not at h1
          have h2 : q.2 - p.2 ≠ 0 := fun h => hpq_ne (Prod.ext (by linarith) (by linarith))
          refine ⟨(w₀.2 - p.2) / (q.2 - p.2), ?_⟩
          ext
          · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
            unfold orient at hw₀_0; rw [h1] at hw₀_0
            have : (q.2 - p.2) * (w₀.1 - p.1) = 0 := by linarith
            have : w₀.1 - p.1 = 0 := (mul_eq_zero.mp this).resolve_left h2
            have hq1 : q.1 = p.1 := by linarith
            rw [hq1]; ring_nf; linarith
          · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; field_simp; ring
      obtain ⟨s, hs⟩ := hex_s
      have hs1 : s ≤ 1 := by
        rw [hs, orient_add_smul y q p q (1 - s) s (by ring), orient_self_right] at hw₀_yq
        nlinarith
      have hs0 : 0 ≤ s := by
        have hsw : orient x w₀ p = -orient x p w₀ := by unfold orient; ring
        rw [hsw, hs, orient_add_smul x p p q (1 - s) s (by ring), orient_self_right] at hw₀_xp
        have : orient x p q = -orient x q p := by unfold orient; ring
        nlinarith
      exact ⟨1 - s, s, by linarith, hs0, by linarith, hs.symm⟩
    have hw₀_4 : w₀ ∈ convexHull ℝ ({x, y, q, p} : Set (ℝ × ℝ)) :=
      segment_subset_convexHull (by simp) (by simp) hw₀_seg
    have hW2_le_t : W₂ ≤ t := by
      have hW1' : W₁ = 1 - W₂ := by linarith
      have h1 : orient p q w = (1 - W₂) * orient p q u + W₂ * orient p q r := by
        rw [hw_comb, orient_add_smul p q u r W₁ W₂ hWsum, hW1']
      dsimp [t]; rw [le_div_iff₀ hden]; linarith
    have hw_uw₀ : w = (1 - W₂ / t) • u + (W₂ / t) • w₀ := by
      have hW1' : W₁ = 1 - W₂ := by linarith
      rw [hw_comb, hW1']; dsimp [w₀]
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
        (field_simp [ne_of_gt ht0]; ring)
    rw [hw_uw₀]
    exact (convex_convexHull ℝ _) hu4 hw₀_4 (by rw [sub_nonneg]; exact (div_le_one ht0).mpr hW2_le_t)
      (div_nonneg hW2_pos.le ht0.le) (by ring)

private lemma no_cone_point_of_empty_quad {P : Finset (ℝ × ℝ)} {x y q p : ℝ × ℝ}
    (hpent : ¬ HasEmptyPentagon P)
    (hxP : x ∈ P) (hyP : y ∈ P) (hqP : q ∈ P) (hpP : p ∈ P)
    (hxyq : 0 < orient x y q) (hxyp : 0 < orient x y p)
    (hxqp : 0 < orient x q p) (hyqp : 0 < orient y q p)
    (h4empty : ∀ w ∈ P, w ∈ convexHull ℝ ({x, y, q, p} : Set (ℝ × ℝ)) → w ∈ ({x, y, q, p} : Set (ℝ × ℝ))) :
    ∀ r ∈ P, ¬(0 < orient p q r ∧ 0 < orient y q r ∧ 0 < orient x r p ∧ 0 < orient x y r) := by
  classical
  intro r₀ hr₀P hcone₀
  let Cone : Finset (ℝ × ℝ) := P.filter fun r =>
    0 < orient p q r ∧ 0 < orient y q r ∧ 0 < orient x r p ∧ 0 < orient x y r
  have hCone_ne : Cone.Nonempty := ⟨r₀, Finset.mem_filter.mpr ⟨hr₀P, hcone₀⟩⟩
  obtain ⟨r, hrC, hrmin⟩ := Cone.exists_min_image (fun w => orient p q w) hCone_ne
  obtain ⟨hrP, hpqr, hyqr, hxrp, hxyr⟩ := Finset.mem_filter.mp hrC
  -- Check all 10 triples of (x, y, q, r, p) are strictly positive!
  have hqrp : 0 < orient q r p := by rw [orient_cyclic, orient_cyclic]; exact hpqr
  have hxqr : 0 < orient x q r := by
    have hpl : orient q p x * orient q y r - orient q p y * orient q x r +
        orient q p r * orient q x y = 0 := by unfold orient; ring
    have h1 : orient q p x = orient x q p := by unfold orient; ring
    have h2 : orient q y r = -orient y q r := by unfold orient; ring
    have h3 : orient q p y = orient y q p := by unfold orient; ring
    have h4 : orient q x r = -orient x q r := by unfold orient; ring
    have h5 : orient q p r = -orient p q r := by unfold orient; ring
    have h6 : orient q x y = orient x y q := by unfold orient; ring
    nlinarith
  have hyrp : 0 < orient y r p := by
    have hpl : orient p x q * orient p y r = orient p x y * orient p q r + orient p x r * orient p y q := by
      unfold orient; ring
    have h1 : orient p x q = orient x q p := by unfold orient; ring
    have h2 : orient p y r = orient y r p := by unfold orient; ring
    have h3 : orient p x y = orient x y p := by unfold orient; ring
    have h4 : orient p x r = orient x r p := by unfold orient; ring
    have h5 : orient p y q = orient y q p := by unfold orient; ring
    nlinarith
  let q5 : Fin 5 → ℝ × ℝ := fun i => match i with | ⟨0, _⟩ => x | ⟨1, _⟩ => y | ⟨2, _⟩ => q | ⟨3, _⟩ => r | ⟨4, _⟩ => p
  have hq5_orient : ∀ i j k : Fin 5, i < j → j < k → 0 < orient (q5 i) (q5 j) (q5 k) := by
    intro i j k hij hjk
    have h1 : i.1 < j.1 := hij
    have h2 : j.1 < k.1 := hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> first
      | (dsimp at h1 h2; omega)
      | (dsimp only [q5]; assumption)
  apply hpent
  refine hasEmptyPentagon_of_cyclic_orient q5 (fun i => by fin_cases i <;> dsimp only [q5] <;> assumption)
    hq5_orient ?_
  intro w hwP hwconv
  -- Split on whether orient p q w ≤ 0 (then w ∈ conv{x, y, q, p}) or orient p q w > 0 (contradicts minimality of r)!
  by_cases hpqw : orient p q w ≤ 0
  · -- Show w ∈ convexHull ℝ {x, y, q, p} by splitting r out of the convex combination of {x, y, q, r, p}!
    have hw4 : w ∈ convexHull ℝ ({x, y, q, p} : Set (ℝ × ℝ)) :=
      mem_convexHull_quad_of_pentagon_le hxyq hxyp hxqp hyqp hpqr hyqr hxrp hwconv hpqw
    have hmem4 := h4empty w hwP hw4
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem4
    rcases hmem4 with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨4, rfl⟩
  · -- orient p q w > 0: if w ≠ r, then w ∈ Cone with orient p q w < orient p q r, contradiction!
    push Not at hpqw
    by_cases hwr : w = r
    · exact ⟨3, hwr.symm⟩
    · exfalso
      -- First show orient p q w < orient p q r!
      have hpqw_lt : orient p q w < orient p q r := by
        rw [convexHull_eq] at hwconv
        obtain ⟨ι, s, f, g, hf0, hf1, hg, hcm⟩ := hwconv
        have hle_all : ∀ i ∈ s, orient p q (g i) ≤ orient p q r := by
          intro i hi
          obtain ⟨idx, hidx⟩ := hg i hi
          rw [← hidx]
          fin_cases idx <;> dsimp only [q5]
          · have : orient p q x = -orient x q p := by unfold orient; ring
            linarith
          · have : orient p q y = -orient y q p := by unfold orient; ring
            linarith
          · rw [orient_self_right]; linarith
          · exact le_rfl
          · rw [orient_self_mid]; linarith
        obtain ⟨i₀, hi₀, hfi₀, hne_r⟩ : ∃ i ∈ s, 0 < f i ∧ g i ≠ r := by
          by_contra h1; push Not at h1
          have : w = r := by
            rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hf1]
            have : ∑ i ∈ s, f i • g i = ∑ i ∈ s, f i • r :=
              Finset.sum_congr rfl fun i hi => by
                rcases eq_or_lt_of_le (hf0 i hi) with h0 | hp
                · rw [← h0, zero_smul, zero_smul]
                · rw [h1 i hi hp]
            rw [this, ← Finset.sum_smul, hf1, one_smul]
          exact hwr this
        have hlt_i0 : orient p q (g i₀) < orient p q r := by
          obtain ⟨idx, hidx⟩ := hg i₀ hi₀
          rw [← hidx] at hne_r ⊢
          fin_cases idx <;> dsimp only [q5] at hne_r ⊢
          · have : orient p q x = -orient x q p := by unfold orient; ring
            linarith
          · have : orient p q y = -orient y q p := by unfold orient; ring
            linarith
          · rw [orient_self_right]; linarith
          · exact absurd rfl hne_r
          · rw [orient_self_mid]; linarith
        have horient_w : orient p q w = ∑ i ∈ s, f i * orient p q (g i) := by
          rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hf1]
          unfold orient
          simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
          have ha1 : (∑ i ∈ s, f i * (g i).2) - p.2 = ∑ i ∈ s, f i * ((g i).2 - p.2) := by
            simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hf1, one_mul]
          have ha2 : (∑ i ∈ s, f i * (g i).1) - p.1 = ∑ i ∈ s, f i * ((g i).1 - p.1) := by
            simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hf1, one_mul]
          rw [ha1, ha2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => by ring
        rw [horient_w]
        have hsum := Finset.sum_lt_sum (fun i hi => mul_le_mul_of_nonneg_left (hle_all i hi) (hf0 i hi))
          ⟨i₀, hi₀, mul_lt_mul_of_pos_left hlt_i0 hfi₀⟩
        rw [← Finset.sum_mul, hf1, one_mul] at hsum
        exact hsum
      -- Now show w ∈ Cone (orient y q w > 0, orient x w p > 0, orient x y w > 0)!
      have hxyw : 0 < orient x y w := by
        -- Every vertex of q5 has orient x y ≥ 0, and if orient x y w = 0 then w ∈ segment [x, y] so orient p q w < 0!
        have hge : 0 ≤ orient x y w := orient_ge_of_mem_convexHull hwconv fun v hv => by
          obtain ⟨idx, rfl⟩ := hv
          fin_cases idx <;> dsimp only [q5]
          · exact (orient_self_mid _ _).ge
          · exact (orient_self_right _ _).ge
          · exact hxyq.le
          · exact hxyr.le
          · exact hxyp.le
        refine lt_of_le_of_ne hge (fun h0 => ?_)
        -- If orient x y w = 0, then in convex combination only x and y can have positive weight, so orient p q w < 0!
        have hpqw_neg : orient p q w < 0 := by
          rw [convexHull_eq] at hwconv
          obtain ⟨ι, s, f, g, hf0, hf1, hg, hcm⟩ := hwconv
          have hxy_sum : orient x y w = ∑ i ∈ s, f i * orient x y (g i) := by
            rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hf1]
            unfold orient
            simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
            have ha1 : (∑ i ∈ s, f i * (g i).2) - x.2 = ∑ i ∈ s, f i * ((g i).2 - x.2) := by
              simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hf1, one_mul]
            have ha2 : (∑ i ∈ s, f i * (g i).1) - x.1 = ∑ i ∈ s, f i * ((g i).1 - x.1) := by
              simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hf1, one_mul]
            rw [ha1, ha2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun i _ => by ring
          have hzero : ∀ i ∈ s, f i * orient x y (g i) = 0 :=
            (Finset.sum_eq_zero_iff_of_nonneg fun i hi => mul_nonneg (hf0 i hi) (by
              obtain ⟨idx, hidx⟩ := hg i hi; rw [← hidx]
              fin_cases idx <;> dsimp only [q5]
              · exact (orient_self_mid _ _).ge
              · exact (orient_self_right _ _).ge
              · exact hxyq.le
              · exact hxyr.le
              · exact hxyp.le)).mp (by linarith)
          have hmem_xy : w ∈ convexHull ℝ ({x, y} : Set (ℝ × ℝ)) := by
            rw [convexHull_eq]
            refine ⟨ι, s.filter (fun i => 0 < f i), f, g,
              fun i hi => hf0 i (Finset.mem_filter.mp hi).1, ?_, ?_, ?_⟩
            · have h1 := Finset.sum_filter_add_sum_filter_not s (fun i => 0 < f i) f
              have h2 : ∑ i ∈ s.filter (fun i => ¬ 0 < f i), f i = 0 :=
                Finset.sum_eq_zero fun i hi => le_antisymm (not_lt.mp (Finset.mem_filter.mp hi).2)
                  (hf0 i (Finset.mem_filter.mp hi).1)
              linarith
            · intro i hi
              have hfi := (Finset.mem_filter.mp hi).2
              have h0i := (mul_eq_zero.mp (hzero i (Finset.mem_filter.mp hi).1)).resolve_left (ne_of_gt hfi)
              obtain ⟨idx, hidx⟩ := hg i (Finset.mem_filter.mp hi).1
              rw [← hidx] at h0i ⊢
              fin_cases idx <;> dsimp only [q5] at h0i ⊢
              · simp
              · simp
              · linarith
              · linarith
              · linarith
            · have hsum1 : ∑ i ∈ s.filter (fun i => 0 < f i), f i = 1 := by
                have h1 := Finset.sum_filter_add_sum_filter_not s (fun i => 0 < f i) f
                have h2 : ∑ i ∈ s.filter (fun i => ¬ 0 < f i), f i = 0 :=
                  Finset.sum_eq_zero fun i hi => le_antisymm (not_lt.mp (Finset.mem_filter.mp hi).2)
                    (hf0 i (Finset.mem_filter.mp hi).1)
                linarith
              rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hf1, Finset.centerMass_eq_of_sum_1 _ _ hsum1]
              have h1 := Finset.sum_filter_add_sum_filter_not s (fun i => 0 < f i) (fun i => f i • g i)
              have h2 : ∑ i ∈ s.filter (fun i => ¬ 0 < f i), f i • g i = 0 :=
                Finset.sum_eq_zero fun i hi => by
                  rw [le_antisymm (not_lt.mp (Finset.mem_filter.mp hi).2) (hf0 i (Finset.mem_filter.mp hi).1), zero_smul]
              rw [h2, add_zero] at h1; exact h1
          exact orient_lt_of_mem_convexHull hmem_xy fun v hv => by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
            rcases hv with hv | hv <;> rw [hv]
            · have : orient p q x = -orient x q p := by unfold orient; ring
              linarith
            · have : orient p q y = -orient y q p := by unfold orient; ring
              linarith
        linarith
      -- Similarly orient y q w > 0 and orient x w p > 0!
      have hyqw : 0 < orient y q w := by
        have hge : 0 ≤ orient y q w := orient_ge_of_mem_convexHull hwconv fun v hv => by
          obtain ⟨idx, rfl⟩ := hv
          fin_cases idx <;> dsimp only [q5]
          · have : orient y q x = orient x y q := by unfold orient; ring
            linarith
          · exact (orient_self_mid _ _).ge
          · exact (orient_self_right _ _).ge
          · exact hyqr.le
          · exact hyqp.le
        refine lt_of_le_of_ne hge (fun h0 => ?_)
        -- If orient y q w = 0, then w ∈ conv{y, q}, where orient p q ≤ 0!
        have hpqw_le : orient p q w ≤ 0 := by
          rw [convexHull_eq] at hwconv
          obtain ⟨ι, s, f, g, hf0, hf1, hg, hcm⟩ := hwconv
          have hsum : orient y q w = ∑ i ∈ s, f i * orient y q (g i) := by
            rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hf1]
            unfold orient
            simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
            have ha1 : (∑ i ∈ s, f i * (g i).2) - y.2 = ∑ i ∈ s, f i * ((g i).2 - y.2) := by
              simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hf1, one_mul]
            have ha2 : (∑ i ∈ s, f i * (g i).1) - y.1 = ∑ i ∈ s, f i * ((g i).1 - y.1) := by
              simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hf1, one_mul]
            rw [ha1, ha2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun i _ => by ring
          have hzero : ∀ i ∈ s, f i * orient y q (g i) = 0 :=
            (Finset.sum_eq_zero_iff_of_nonneg fun i hi => mul_nonneg (hf0 i hi) (by
              obtain ⟨idx, hidx⟩ := hg i hi; rw [← hidx]
              fin_cases idx <;> dsimp only [q5]
              · have : orient y q x = orient x y q := by unfold orient; ring
                linarith
              · exact (orient_self_mid _ _).ge
              · exact (orient_self_right _ _).ge
              · exact hyqr.le
              · exact hyqp.le)).mp (by linarith)
          have hpq_sum : orient p q w = ∑ i ∈ s, f i * orient p q (g i) := by
            rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hf1]
            unfold orient
            simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
            have ha1 : (∑ i ∈ s, f i * (g i).2) - p.2 = ∑ i ∈ s, f i * ((g i).2 - p.2) := by
              simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hf1, one_mul]
            have ha2 : (∑ i ∈ s, f i * (g i).1) - p.1 = ∑ i ∈ s, f i * ((g i).1 - p.1) := by
              simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hf1, one_mul]
            rw [ha1, ha2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun i _ => by ring
          rw [hpq_sum]
          refine Finset.sum_nonpos fun i hi => ?_
          rcases eq_or_lt_of_le (hf0 i hi) with hfi0 | hfip
          · rw [← hfi0, zero_mul]
          · have h0i := (mul_eq_zero.mp (hzero i hi)).resolve_left (ne_of_gt hfip)
            obtain ⟨idx, hidx⟩ := hg i hi
            rw [← hidx] at h0i ⊢
            fin_cases idx <;> dsimp only [q5] at h0i ⊢
            · have : orient y q x = orient x y q := by unfold orient; ring
              linarith
            · have : orient p q y = -orient y q p := by unfold orient; ring
              nlinarith
            · rw [orient_self_right, mul_zero]
            · linarith
            · linarith
        linarith
      have hxwp : 0 < orient x w p := by
        have hge : 0 ≤ orient x w p := by
          have hsw : orient x w p = -orient x p w := by unfold orient; ring
          rw [hsw]
          have : orient x p w ≤ 0 := orient_le_of_mem_convexHull hwconv fun v hv => by
            obtain ⟨idx, rfl⟩ := hv
            fin_cases idx <;> dsimp only [q5]
            · exact (orient_self_mid _ _).le
            · have : orient x p y = -orient x y p := by unfold orient; ring
              linarith
            · have : orient x p q = -orient x q p := by unfold orient; ring
              linarith
            · have : orient x p r = -orient x r p := by unfold orient; ring
              linarith
            · exact (orient_self_right _ _).le
          linarith
        refine lt_of_le_of_ne hge (fun h0 => ?_)
        have hpqw_le : orient p q w ≤ 0 := by
          rw [convexHull_eq] at hwconv
          obtain ⟨ι, s, f, g, hf0, hf1, hg, hcm⟩ := hwconv
          have hsum : orient x p w = ∑ i ∈ s, f i * orient x p (g i) := by
            rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hf1]
            unfold orient
            simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
            have ha1 : (∑ i ∈ s, f i * (g i).2) - x.2 = ∑ i ∈ s, f i * ((g i).2 - x.2) := by
              simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hf1, one_mul]
            have ha2 : (∑ i ∈ s, f i * (g i).1) - x.1 = ∑ i ∈ s, f i * ((g i).1 - x.1) := by
              simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hf1, one_mul]
            rw [ha1, ha2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun i _ => by ring
          have h0' : orient x p w = 0 := by
            have : orient x p w = -orient x w p := by unfold orient; ring
            linarith
          have hzero : ∀ i ∈ s, f i * (-orient x p (g i)) = 0 :=
            (Finset.sum_eq_zero_iff_of_nonneg fun i hi => mul_nonneg (hf0 i hi) (by
              obtain ⟨idx, hidx⟩ := hg i hi; rw [← hidx]
              fin_cases idx <;> dsimp only [q5]
              · rw [orient_self_mid]; linarith
              · have : orient x p y = -orient x y p := by unfold orient; ring
                linarith
              · have : orient x p q = -orient x q p := by unfold orient; ring
                linarith
              · have : orient x p r = -orient x r p := by unfold orient; ring
                linarith
              · rw [orient_self_right]; linarith)).mp (by
              simp only [mul_neg, Finset.sum_neg_distrib]; linarith)
          have hpq_sum : orient p q w = ∑ i ∈ s, f i * orient p q (g i) := by
            rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hf1]
            unfold orient
            simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
            have ha1 : (∑ i ∈ s, f i * (g i).2) - p.2 = ∑ i ∈ s, f i * ((g i).2 - p.2) := by
              simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hf1, one_mul]
            have ha2 : (∑ i ∈ s, f i * (g i).1) - p.1 = ∑ i ∈ s, f i * ((g i).1 - p.1) := by
              simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hf1, one_mul]
            rw [ha1, ha2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun i _ => by ring
          rw [hpq_sum]
          refine Finset.sum_nonpos fun i hi => ?_
          rcases eq_or_lt_of_le (hf0 i hi) with hfi0 | hfip
          · rw [← hfi0, zero_mul]
          · have h0i := (mul_eq_zero.mp (hzero i hi)).resolve_left (ne_of_gt hfip)
            obtain ⟨idx, hidx⟩ := hg i hi
            rw [← hidx] at h0i ⊢
            fin_cases idx <;> dsimp only [q5] at h0i ⊢
            · have : orient p q x = -orient x q p := by unfold orient; ring
              nlinarith
            · have : orient x p y = -orient x y p := by unfold orient; ring
              linarith
            · have : orient x p q = -orient x q p := by unfold orient; ring
              linarith
            · have : orient x p r = -orient x r p := by unfold orient; ring
              linarith
            · rw [orient_self_mid, mul_zero]
        linarith
      have hwC : w ∈ Cone := Finset.mem_filter.mpr ⟨hwP, hpqw, hyqw, hxwp, hxyw⟩
      linarith [hrmin w hwC]

private lemma arg_between_of_orient_pos {z a b w : ℝ × ℝ}
    (hab : 0 < orient z a b) (haw : 0 < orient z a w) (hwb : 0 < orient z w b) :
    let θ := fun u : ℝ × ℝ => Complex.arg (toC (u - z))
    (θ a < θ b → θ a < θ w ∧ θ w < θ b) ∧
    (θ b < θ a → θ a < θ w ∨ θ w < θ b) := by
  intro θ
  have ha_ne : a ≠ z := fun h => by rw [h, orient_self_left] at hab; exact lt_irrefl 0 hab
  have hb_ne : b ≠ z := fun h => by rw [h, orient_self_mid] at hab; exact lt_irrefl 0 hab
  have hw_ne : w ≠ z := fun h => by rw [h, orient_self_mid] at haw; exact lt_irrefl 0 haw
  have hna : 0 < ‖toC (a - z)‖ := norm_pos_iff.mpr ((toC_ne_zero_iff a z).mpr ha_ne)
  have hnb : 0 < ‖toC (b - z)‖ := norm_pos_iff.mpr ((toC_ne_zero_iff b z).mpr hb_ne)
  have hnw : 0 < ‖toC (w - z)‖ := norm_pos_iff.mpr ((toC_ne_zero_iff w z).mpr hw_ne)
  have hsab : 0 < Real.sin (θ b - θ a) := by
    have h := orient_eq_norm_mul_sin_sub z a b ha_ne hb_ne
    nlinarith [mul_pos hna hnb]
  have hsaw : 0 < Real.sin (θ w - θ a) := by
    have h := orient_eq_norm_mul_sin_sub z a w ha_ne hw_ne
    nlinarith [mul_pos hna hnw]
  have hswb : 0 < Real.sin (θ b - θ w) := by
    have h := orient_eq_norm_mul_sin_sub z w b hw_ne hb_ne
    nlinarith [mul_pos hnw hnb]
  have ha_lo := Complex.neg_pi_lt_arg (toC (a - z))
  have ha_hi := Complex.arg_le_pi (toC (a - z))
  have hb_lo := Complex.neg_pi_lt_arg (toC (b - z))
  have hb_hi := Complex.arg_le_pi (toC (b - z))
  have hw_lo := Complex.neg_pi_lt_arg (toC (w - z))
  have hw_hi := Complex.arg_le_pi (toC (w - z))
  have hsin_neg_pi : ∀ t : ℝ, -Real.pi ≤ t → t ≤ 0 → Real.sin t ≤ 0 := fun t h1 h2 => by
    rcases eq_or_lt_of_le h2 with rfl | h2'
    · rw [Real.sin_zero]
    · rcases eq_or_lt_of_le h1 with rfl | h1'
      · rw [Real.sin_neg, Real.sin_pi, neg_zero]
      · exact (Real.sin_neg_of_neg_of_neg_pi_lt h2' h1').le
  have hsin_pos_pi : ∀ t : ℝ, Real.pi ≤ t → t ≤ 2 * Real.pi → Real.sin t ≤ 0 := fun t h1 h2 => by
    have h := hsin_neg_pi (t - 2 * Real.pi) (by linarith) (by linarith)
    rwa [Real.sin_sub_two_pi] at h
  constructor
  · intro hlt
    have hab_pi : θ b - θ a < Real.pi := by
      by_contra h; push Not at h
      linarith [hsin_pos_pi (θ b - θ a) h (by linarith)]
    constructor
    · by_contra h; push Not at h
      have hwa_lt : θ w - θ a < -Real.pi := by
        by_contra h'; push Not at h'
        linarith [hsin_neg_pi (θ w - θ a) h' (by linarith)]
      linarith [hsin_pos_pi (θ b - θ w) (by linarith) (by linarith)]
    · by_contra h; push Not at h
      have hbw_lt : θ b - θ w < -Real.pi := by
        by_contra h'; push Not at h'
        linarith [hsin_neg_pi (θ b - θ w) h' (by linarith)]
      linarith [hsin_pos_pi (θ w - θ a) (by linarith) (by linarith)]
  · intro hlt
    by_contra h; push Not at h
    have hwa_lt : θ w - θ a < -Real.pi := by
      by_contra h'; push Not at h'
      linarith [hsin_neg_pi (θ w - θ a) h' (by linarith)]
    have hbw_lt : θ b - θ w < -Real.pi := by
      by_contra h'; push Not at h'
      linarith [hsin_neg_pi (θ b - θ w) h' (by linarith)]
    linarith

private lemma no_mem_between_consecutive_arc {Q : Finset (ℝ × ℝ)} {z : ℝ × ℝ}
    (hz : IsStrictInterior Q z)
    (hA3 : 3 ≤ #(hullBoundary Q))
    (p : Fin #(hullBoundary Q) ≃ hullBoundary Q)
    (hp_arg : StrictMono fun t => Complex.arg (toC ((p t).1 - z)))
    (k : Fin #(hullBoundary Q)) :
    let x := (p k).1
    let y := (p ⟨(k.1 + 1) % #(hullBoundary Q), Nat.mod_lt _ (by omega)⟩).1
    ∀ w ∈ hullBoundary Q, ¬(0 < orient z x w ∧ 0 < orient z w y) := by
  intro x y w hw ⟨hxw, hwy⟩
  have hxy := (arc_orient_props hz hA3 p hp_arg k).1
  let k' : Fin #(hullBoundary Q) := ⟨(k.1 + 1) % #(hullBoundary Q), Nat.mod_lt _ (by omega)⟩
  let m := p.symm ⟨w, hw⟩
  have hm_eq : (p m).1 = w := congrArg Subtype.val (p.apply_symm_apply ⟨w, hw⟩)
  have ⟨h1, h2⟩ := arg_between_of_orient_pos hxy hxw hwy
  by_cases hlt : k.1 + 1 < #(hullBoundary Q)
  · have hk'v : k'.1 = k.1 + 1 := Nat.mod_eq_of_lt hlt
    have hkk' : k < k' := by show k.1 < k'.1; omega
    have ⟨hkm, hmk'⟩ := h1 (hp_arg hkk')
    rw [← hm_eq] at hkm hmk'
    have hkm' : k < m := hp_arg.lt_iff_lt.mp hkm
    have hmk'' : m < k' := hp_arg.lt_iff_lt.mp hmk'
    have : k.1 < m.1 := hkm'
    have : m.1 < k'.1 := hmk''
    omega
  · have hkv : k.1 = #(hullBoundary Q) - 1 := by omega
    have hk'v : k'.1 = 0 := by dsimp [k']; rw [show k.1 + 1 = #(hullBoundary Q) by omega, Nat.mod_self]
    have hk'k : k' < k := by show k'.1 < k.1; omega
    rcases h2 (hp_arg hk'k) with hkm | hmk'
    · rw [← hm_eq] at hkm
      have : k.1 < m.1 := hp_arg.lt_iff_lt.mp hkm
      omega
    · rw [← hm_eq] at hmk'
      have : m.1 < k'.1 := hp_arg.lt_iff_lt.mp hmk'
      omega

private lemma exists_arc_enum {Q : Finset (ℝ × ℝ)} {z : ℝ × ℝ} (hz : IsStrictInterior Q z) :
    ∃ p : Fin #(hullBoundary Q) ≃ hullBoundary Q,
      StrictMono (fun t => Complex.arg (toC ((p t).1 - z))) := by
  classical
  have ⟨_, hinj⟩ := arg_injOn_hullBoundary hz
  let θ : (ℝ × ℝ) → ℝ := fun q => Complex.arg (toC (q - z))
  let Sθ : Finset ℝ := (hullBoundary Q).image θ
  have hcardS : #Sθ = #(hullBoundary Q) := Finset.card_image_of_injOn hinj
  let eS : Fin #(hullBoundary Q) ≃o Sθ := Sθ.orderIsoOfFin hcardS
  let eB : hullBoundary Q ≃ Sθ :=
    Equiv.ofBijective
      (fun q : hullBoundary Q => ⟨θ q.1, Finset.mem_image.mpr ⟨q.1, q.2, rfl⟩⟩)
      ⟨fun q₁ q₂ h => Subtype.ext (hinj q₁.2 q₂.2 (congrArg Subtype.val h)),
       fun ⟨t, ht⟩ => let ⟨q, hq, hqt⟩ := Finset.mem_image.mp ht; ⟨⟨q, hq⟩, Subtype.ext hqt⟩⟩
  refine ⟨eS.toEquiv.trans eB.symm, fun i j hij => ?_⟩
  have hθp : ∀ t : Fin #(hullBoundary Q), θ ((eS.toEquiv.trans eB.symm) t).1 = (eS t).1 := fun t =>
    congrArg Subtype.val (eB.apply_symm_apply (eS t))
  change θ _ < θ _; rw [hθp i, hθp j]; exact eS.strictMono hij

private lemma exists_empty_arc_of_card_lt {Q₁ Q₂ : Finset (ℝ × ℝ)} {z : ℝ × ℝ}
    (hz : IsStrictInterior Q₁ z)
    (hA3 : 3 ≤ #(hullBoundary Q₁))
    (hcard : #(hullBoundary Q₂) < #(hullBoundary Q₁))
    (p : Fin #(hullBoundary Q₁) ≃ hullBoundary Q₁)
    (hp_arg : StrictMono fun t => Complex.arg (toC ((p t).1 - z))) :
    ∃ k : Fin #(hullBoundary Q₁),
      let x := (p k).1
      let y := (p ⟨(k.1 + 1) % #(hullBoundary Q₁), Nat.mod_lt _ (by omega)⟩).1
      ∀ w ∈ hullBoundary Q₂, ¬(0 < orient z x w ∧ 0 < orient z w y) := by
  classical
  by_contra hall
  push Not at hall
  have hall' : ∀ k : Fin #(hullBoundary Q₁), ∃ w, w ∈ hullBoundary Q₂ ∧
      0 < orient z (p k).1 w ∧ 0 < orient z w (p ⟨(k.1 + 1) % #(hullBoundary Q₁), Nat.mod_lt _ (by omega)⟩).1 := fun k => by
    have hk := hall k; dsimp only at hk; push Not at hk; exact hk
  choose f hfA hf1 hf2 using hall'
  have hinj : Function.Injective f := by
    intro k₁ k₂ hfeq
    by_contra hne
    wlog hlt : k₁ < k₂ generalizing k₁ k₂
    · exact this hfeq.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
    have ha1 := (arc_orient_props hz hA3 p hp_arg k₁).1
    have ha2 := (arc_orient_props hz hA3 p hp_arg k₂).1
    have h1 := arg_between_of_orient_pos ha1 (hf1 k₁) (hf2 k₁)
    have h2 := arg_between_of_orient_pos ha2 (hfeq ▸ hf1 k₂) (hfeq ▸ hf2 k₂)
    have hk1_lt : k₁.1 + 1 < #(hullBoundary Q₁) := by have : k₁.1 < k₂.1 := hlt; omega
    have hk1' : (⟨(k₁.1 + 1) % #(hullBoundary Q₁), Nat.mod_lt _ (by omega)⟩ : Fin #(hullBoundary Q₁)) =
        ⟨k₁.1 + 1, hk1_lt⟩ := Fin.ext (Nat.mod_eq_of_lt hk1_lt)
    have ⟨hlo1, hhi1⟩ := h1.1 (by rw [hk1']; exact hp_arg (by show k₁.1 < k₁.1 + 1; omega))
    rw [hk1'] at hhi1
    by_cases hk2_lt : k₂.1 + 1 < #(hullBoundary Q₁)
    · have hk2' : (⟨(k₂.1 + 1) % #(hullBoundary Q₁), Nat.mod_lt _ (by omega)⟩ : Fin #(hullBoundary Q₁)) =
          ⟨k₂.1 + 1, hk2_lt⟩ := Fin.ext (Nat.mod_eq_of_lt hk2_lt)
      have ⟨hlo2, _⟩ := h2.1 (by rw [hk2']; exact hp_arg (by show k₂.1 < k₂.1 + 1; omega))
      have h12 : Complex.arg (toC ((p ⟨k₁.1 + 1, hk1_lt⟩).1 - z)) ≤ Complex.arg (toC ((p k₂).1 - z)) :=
        hp_arg.monotone (by show k₁.1 + 1 ≤ k₂.1; have : k₁.1 < k₂.1 := hlt; omega)
      linarith
    · have hk2_eq : k₂.1 = #(hullBoundary Q₁) - 1 := by omega
      have hk2' : (⟨(k₂.1 + 1) % #(hullBoundary Q₁), Nat.mod_lt _ (by omega)⟩ : Fin #(hullBoundary Q₁)) =
          ⟨0, by omega⟩ := Fin.ext (by dsimp; rw [show k₂.1 + 1 = #(hullBoundary Q₁) by omega, Nat.mod_self])
      have hor := h2.2 (by rw [hk2']; exact hp_arg (by show 0 < k₂.1; omega))
      rw [hk2'] at hor
      have h0le : Complex.arg (toC ((p ⟨0, by omega⟩).1 - z)) ≤ Complex.arg (toC ((p k₁).1 - z)) :=
        hp_arg.monotone (by show 0 ≤ k₁.1; omega)
      have hle2 : Complex.arg (toC ((p ⟨k₁.1 + 1, hk1_lt⟩).1 - z)) ≤ Complex.arg (toC ((p k₂).1 - z)) :=
        hp_arg.monotone (by show k₁.1 + 1 ≤ k₂.1; have : k₁.1 < k₂.1 := hlt; omega)
      rcases hor with hgt | hlt0 <;> linarith
  have hle : #(hullBoundary Q₁) ≤ #(hullBoundary Q₂) := by
    calc #(hullBoundary Q₁) = #(Finset.univ.image f) := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
      _ ≤ #(hullBoundary Q₂) := Finset.card_le_card fun w hw => by
          obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hw; exact hfA k
  omega

/-- Follower construction + Claims B and C of Abel et al. (2011). -/
private lemma follower_of_empty_arc {P Q₁ : Finset (ℝ × ℝ)} {z x y : ℝ × ℝ}
    (hpent : ¬ HasEmptyPentagon P)
    (hQ₁P : Q₁ ⊆ P)
    (hQ₁closed : ∀ w ∈ P, w ∈ convexHull ℝ (Q₁ : Set (ℝ × ℝ)) → w ∈ Q₁)
    (hz3 : z ∈ (Q₁ \ hullBoundary Q₁) \ hullBoundary (Q₁ \ hullBoundary Q₁))
    (hA2_3 : 3 ≤ #(hullBoundary (Q₁ \ hullBoundary Q₁)))
    (hxA1 : x ∈ hullBoundary Q₁) (hyA1 : y ∈ hullBoundary Q₁)
    (hzxy : 0 < orient z x y)
    (hxy_int : ∀ w ∈ Q₁ \ hullBoundary Q₁, 0 < orient x y w)
    (hxy_consec : ∀ w ∈ hullBoundary Q₁, ¬(0 < orient z x w ∧ 0 < orient z w y))
    (hxy_empty : ∀ w ∈ hullBoundary (Q₁ \ hullBoundary Q₁), ¬(0 < orient z x w ∧ 0 < orient z w y)) :
    let Q₂ := Q₁ \ hullBoundary Q₁
    let Q₃ := Q₂ \ hullBoundary Q₂
    ∃ p q : ℝ × ℝ,
      p ∈ hullBoundary Q₂ ∧ q ∈ hullBoundary Q₂ ∧
      0 < orient z p q ∧
      (∀ w ∈ Q₂, 0 ≤ orient p q w) ∧
      (∀ w ∈ Q₃, 0 < orient p q w) ∧
      (∀ w ∈ hullBoundary Q₂, ¬(0 < orient z p w ∧ 0 < orient z w q)) ∧
      0 ≤ orient z p x ∧ 0 < orient z x q ∧ 0 ≤ orient z y q ∧ 0 < orient z p y ∧
      0 < orient x y q ∧ 0 < orient x y p ∧ 0 < orient x q p ∧ 0 < orient y q p ∧
      (∀ w ∈ P, w ∈ convexHull ℝ ({x, y, q, p} : Set (ℝ × ℝ)) → w ∈ ({x, y, q, p} : Set (ℝ × ℝ))) ∧
      (∀ w ∈ hullBoundary Q₃, ¬(0 < orient z p w ∧ 0 < orient z w q)) ∧
      (orient z p x = 0 ∨ orient z y q = 0) := by
  classical
  intro Q₂ Q₃
  have hA2_3' : 3 ≤ #(hullBoundary Q₂) := hA2_3
  have hQ₂closed := layer_convexClosed hQ₁closed
  have hz2 : IsStrictInterior Q₂ z :=
    isStrictInterior_of_not_mem_hullBoundary (Finset.mem_sdiff.mp hz3).1 (Finset.mem_sdiff.mp hz3).2
  have hzQ₂ : z ∈ Q₂ := (Finset.mem_sdiff.mp hz3).1
  have hzP : z ∈ P := hQ₁P (Finset.mem_sdiff.mp hzQ₂).1
  obtain ⟨pe, hpe_arg⟩ := exists_arc_enum hz2
  -- Find a consecutive arc (p, q) of hullBoundary Q₂ with 0 ≤ orient z p x ∧ 0 < orient z x q
  have hne_xz : x ≠ z := fun h => by rw [h, orient_self_left] at hzxy; exact lt_irrefl 0 hzxy
  have hab_xz : -(x.2 - z.2) ≠ 0 ∨ (x.1 - z.1) ≠ 0 := by
    by_contra h; push Not at h; exact hne_xz (Prod.ext (by linarith) (by linarith))
  have hex_pos : ∃ i : Fin #(hullBoundary Q₂), 0 < orient z x (pe i).1 := by
    obtain ⟨u, huQ₂, hlt⟩ := hz2 (-(x.2 - z.2)) (x.1 - z.1) hab_xz
    have hu_pos : 0 < orient z x u := by unfold orient; linarith
    by_contra h; push Not at h
    have hle : orient z x u ≤ 0 := orient_le_of_mem_convexHull (subset_convexHull_hullBoundary Q₂ huQ₂)
      fun v hv => by
        let idx := pe.symm ⟨v, Finset.mem_coe.mp hv⟩
        have hidx : (pe idx).1 = v := congrArg Subtype.val (pe.apply_symm_apply ⟨v, Finset.mem_coe.mp hv⟩)
        rw [← hidx]; exact h idx
    linarith
  have hex_nonpos : ∃ i : Fin #(hullBoundary Q₂), orient z x (pe i).1 ≤ 0 := by
    obtain ⟨u, huQ₂, hlt⟩ := hz2 (x.2 - z.2) (-(x.1 - z.1)) (by rcases hab_xz with h | h; exact Or.inl (fun h0 => h (by linarith)); exact Or.inr (fun h0 => h (by linarith)))
    have hu_neg : orient z x u < 0 := by unfold orient; linarith
    by_contra h; push Not at h
    have hge : 0 ≤ orient z x u := orient_ge_of_mem_convexHull (subset_convexHull_hullBoundary Q₂ huQ₂)
      fun v hv => by
        let idx := pe.symm ⟨v, Finset.mem_coe.mp hv⟩
        have hidx : (pe idx).1 = v := congrArg Subtype.val (pe.apply_symm_apply ⟨v, Finset.mem_coe.mp hv⟩)
        rw [← hidx]; exact (h idx).le
    linarith
  obtain ⟨k₁, hk₁⟩ := hex_pos
  obtain ⟨k₂, hk₂⟩ := hex_nonpos
  have hex_trans : ∃ k : Fin #(hullBoundary Q₂),
      orient z x (pe k).1 ≤ 0 ∧
      0 < orient z x (pe ⟨(k.1 + 1) % #(hullBoundary Q₂), Nat.mod_lt _ (by omega)⟩).1 := by
    by_contra h; push Not at h
    have hall_le : ∀ m : ℕ, orient z x (pe ⟨(k₂.1 + m) % #(hullBoundary Q₂), Nat.mod_lt _ (by omega)⟩).1 ≤ 0 := by
      intro m
      induction m with
      | zero =>
        have : (⟨(k₂.1 + 0) % #(hullBoundary Q₂), Nat.mod_lt _ (by omega)⟩ : Fin #(hullBoundary Q₂)) = k₂ :=
          Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt k₂.2])
        rw [this]; exact hk₂
      | succ m ih =>
        have hstep := h ⟨(k₂.1 + m) % #(hullBoundary Q₂), Nat.mod_lt _ (by omega)⟩ ih
        have heq : (⟨(((k₂.1 + m) % #(hullBoundary Q₂)) + 1) % #(hullBoundary Q₂), Nat.mod_lt _ (by omega)⟩ : Fin #(hullBoundary Q₂)) =
            ⟨(k₂.1 + (m + 1)) % #(hullBoundary Q₂), Nat.mod_lt _ (by omega)⟩ := by
          ext; dsimp; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, add_assoc]
        rw [heq] at hstep; exact hstep
    have h1 := hall_le (#(hullBoundary Q₂) + k₁.1 - k₂.1)
    have heq : (⟨(k₂.1 + (#(hullBoundary Q₂) + k₁.1 - k₂.1)) % #(hullBoundary Q₂), Nat.mod_lt _ (by omega)⟩ : Fin #(hullBoundary Q₂)) = k₁ := by
      ext; dsimp
      have : k₂.1 + (#(hullBoundary Q₂) + k₁.1 - k₂.1) = k₁.1 + #(hullBoundary Q₂) := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt k₁.2]
    rw [heq] at h1; linarith
  obtain ⟨k, hk_le, hk_pos⟩ := hex_trans
  let k' : Fin #(hullBoundary Q₂) := ⟨(k.1 + 1) % #(hullBoundary Q₂), Nat.mod_lt _ (by omega)⟩
  set p := (pe k).1
  set q := (pe k').1
  have hpA2 : p ∈ hullBoundary Q₂ := (pe k).2
  have hqA2 : q ∈ hullBoundary Q₂ := (pe k').2
  have ⟨hzpq, hpq_ge, hpq_int⟩ := arc_orient_props hz2 hA2_3 pe hpe_arg k
  change 0 < orient z p q at hzpq
  change ∀ w ∈ Q₂, 0 ≤ orient p q w at hpq_ge
  change ∀ w ∈ Q₃, 0 < orient p q w at hpq_int
  have hpq_consec := no_mem_between_consecutive_arc hz2 hA2_3 pe hpe_arg k
  have hzpx : 0 ≤ orient z p x := by
    have : orient z p x = -orient z x p := by unfold orient; ring
    linarith
  have hzxq : 0 < orient z x q := hk_pos
  have hzyq : 0 ≤ orient z y q := by
    by_contra h; push Not at h
    have : 0 < orient z q y := by
      have : orient z q y = -orient z y q := by unfold orient; ring
      linarith
    exact hxy_empty q hqA2 ⟨hzxq, this⟩
  have hzpy : 0 < orient z p y := by
    have hpl : orient z p y * orient z x q = orient z p x * orient z y q + orient z p q * orient z x y := by
      unfold orient; ring
    nlinarith
  have hxyq : 0 < orient x y q := hxy_int q (hullBoundary_subset Q₂ hqA2)
  have hxyp : 0 < orient x y p := hxy_int p (hullBoundary_subset Q₂ hpA2)
  -- Show orient p q x < 0 (i.e. 0 < orient x q p) and orient p q y < 0 (i.e. 0 < orient y q p)!
  have hxqp : 0 < orient x q p := by
    have hcram : orient z p q • (x - z) = (orient z x q) • (p - z) + (orient z p x) • (q - z) := by
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, smul_eq_mul] <;>
        (unfold orient; ring)
    set l1 := orient z x q / orient z p q
    set l2 := orient z p x / orient z p q
    have hl1 : 0 < l1 := div_pos hzxq hzpq
    have hl2 : 0 ≤ l2 := div_nonneg hzpx hzpq.le
    have hx_eq : x = (1 - l1 - l2) • z + l1 • p + l2 • q := by
      ext
      · have h1 := congrArg Prod.fst hcram
        simp only [Prod.smul_fst, Prod.fst_add, Prod.fst_sub, smul_eq_mul] at h1 ⊢
        dsimp [l1, l2]; field_simp [ne_of_gt hzpq]; linarith
      · have h2 := congrArg Prod.snd hcram
        simp only [Prod.smul_snd, Prod.snd_add, Prod.snd_sub, smul_eq_mul] at h2 ⊢
        dsimp [l1, l2]; field_simp [ne_of_gt hzpq]; linarith
    have hl_gt : 1 < l1 + l2 := by
      by_contra hle; push Not at hle
      have hx_conv : x ∈ convexHull ℝ (Q₂ : Set (ℝ × ℝ)) := by
        have hmem_z : z ∈ convexHull ℝ (Q₂ : Set (ℝ × ℝ)) := subset_convexHull ℝ _ hzQ₂
        have hmem_p : p ∈ convexHull ℝ (Q₂ : Set (ℝ × ℝ)) := subset_convexHull ℝ _ (hullBoundary_subset Q₂ hpA2)
        have hmem_q : q ∈ convexHull ℝ (Q₂ : Set (ℝ × ℝ)) := subset_convexHull ℝ _ (hullBoundary_subset Q₂ hqA2)
        have h12 : l1 + l2 > 0 := by linarith
        let u := (l1 / (l1 + l2)) • p + (l2 / (l1 + l2)) • q
        have hu : u ∈ convexHull ℝ (Q₂ : Set (ℝ × ℝ)) :=
          (convex_convexHull ℝ _) hmem_p hmem_q (div_nonneg hl1.le h12.le) (div_nonneg hl2 h12.le)
            (by rw [← add_div, div_self (ne_of_gt h12)])
        have hx_u : x = (1 - (l1 + l2)) • z + (l1 + l2) • u := by
          rw [hx_eq]; dsimp [u]
          ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
            (field_simp [ne_of_gt h12]; ring)
        rw [hx_u]
        exact (convex_convexHull ℝ _) hmem_z hu (by linarith) h12.le (by ring)
      have hxQ₂ := hQ₂closed x (hQ₁P (hullBoundary_subset Q₁ hxA1)) hx_conv
      exact (Finset.mem_sdiff.mp hxQ₂).2 hxA1
    have hpqx : orient p q x = (1 - l1 - l2) * orient p q z := by
      rw [hx_eq]
      have h1 : orient p q ((1 - l1 - l2) • z + (l1 • p + l2 • q)) =
          (1 - l1 - l2) * orient p q z + l1 * orient p q p + l2 * orient p q q := by
        unfold orient
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      rw [add_assoc, h1, orient_self_mid, orient_self_right]; ring
    have hpqz : orient p q z = orient z p q := by unfold orient; ring
    have hxqp_eq : orient x q p = -orient p q x := by unfold orient; ring
    nlinarith
  have hyqp : 0 < orient y q p := by
    have hcram : orient z p q • (y - z) = (orient z y q) • (p - z) + (orient z p y) • (q - z) := by
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, smul_eq_mul] <;>
        (unfold orient; ring)
    set l1 := orient z y q / orient z p q
    set l2 := orient z p y / orient z p q
    have hl1 : 0 ≤ l1 := div_nonneg hzyq hzpq.le
    have hl2 : 0 < l2 := div_pos hzpy hzpq
    have hy_eq : y = (1 - l1 - l2) • z + l1 • p + l2 • q := by
      ext
      · have h1 := congrArg Prod.fst hcram
        simp only [Prod.smul_fst, Prod.fst_add, Prod.fst_sub, smul_eq_mul] at h1 ⊢
        dsimp [l1, l2]; field_simp [ne_of_gt hzpq]; linarith
      · have h2 := congrArg Prod.snd hcram
        simp only [Prod.smul_snd, Prod.snd_add, Prod.snd_sub, smul_eq_mul] at h2 ⊢
        dsimp [l1, l2]; field_simp [ne_of_gt hzpq]; linarith
    have hl_gt : 1 < l1 + l2 := by
      by_contra hle; push Not at hle
      have hy_conv : y ∈ convexHull ℝ (Q₂ : Set (ℝ × ℝ)) := by
        have hmem_z : z ∈ convexHull ℝ (Q₂ : Set (ℝ × ℝ)) := subset_convexHull ℝ _ hzQ₂
        have hmem_p : p ∈ convexHull ℝ (Q₂ : Set (ℝ × ℝ)) := subset_convexHull ℝ _ (hullBoundary_subset Q₂ hpA2)
        have hmem_q : q ∈ convexHull ℝ (Q₂ : Set (ℝ × ℝ)) := subset_convexHull ℝ _ (hullBoundary_subset Q₂ hqA2)
        have h12 : l1 + l2 > 0 := by linarith
        let u := (l1 / (l1 + l2)) • p + (l2 / (l1 + l2)) • q
        have hu : u ∈ convexHull ℝ (Q₂ : Set (ℝ × ℝ)) :=
          (convex_convexHull ℝ _) hmem_p hmem_q (div_nonneg hl1 h12.le) (div_nonneg hl2.le h12.le)
            (by rw [← add_div, div_self (ne_of_gt h12)])
        have hy_u : y = (1 - (l1 + l2)) • z + (l1 + l2) • u := by
          rw [hy_eq]; dsimp [u]
          ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
            (field_simp [ne_of_gt h12]; ring)
        rw [hy_u]
        exact (convex_convexHull ℝ _) hmem_z hu (by linarith) h12.le (by ring)
      have hyQ₂ := hQ₂closed y (hQ₁P (hullBoundary_subset Q₁ hyA1)) hy_conv
      exact (Finset.mem_sdiff.mp hyQ₂).2 hyA1
    have hpqy : orient p q y = (1 - l1 - l2) * orient p q z := by
      rw [hy_eq]
      have h1 : orient p q ((1 - l1 - l2) • z + (l1 • p + l2 • q)) =
          (1 - l1 - l2) * orient p q z + l1 * orient p q p + l2 * orient p q q := by
        unfold orient
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      rw [add_assoc, h1, orient_self_mid, orient_self_right]; ring
    have hpqz : orient p q z = orient z p q := by unfold orient; ring
    have hyqp_eq : orient y q p = -orient p q y := by unfold orient; ring
    nlinarith
  -- Show (x, y, q, p) is an empty 4-hole in P!
  have h4empty : ∀ w ∈ P, w ∈ convexHull ℝ ({x, y, q, p} : Set (ℝ × ℝ)) → w ∈ ({x, y, q, p} : Set (ℝ × ℝ)) := by
    intro w hwP hwconv
    have hsubQ₁ : ({x, y, q, p} : Set (ℝ × ℝ)) ⊆ (Q₁ : Set (ℝ × ℝ)) := by
      intro u hu; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact hullBoundary_subset Q₁ hxA1
      · exact hullBoundary_subset Q₁ hyA1
      · exact (Finset.mem_sdiff.mp (hullBoundary_subset Q₂ hqA2)).1
      · exact (Finset.mem_sdiff.mp (hullBoundary_subset Q₂ hpA2)).1
    have hwQ₁ : w ∈ Q₁ := hQ₁closed w hwP (convexHull_mono hsubQ₁ hwconv)
    by_cases hwA1 : w ∈ hullBoundary Q₁
    · -- w ∈ A₁: supporting functional of w on Q₁ forces p, q to have weight 0, so w ∈ segment [x, y]!
      obtain ⟨_, a, b, hab, hmax⟩ := mem_hullBoundary.mp hwA1
      have hlt_p : a * p.1 + b * p.2 < a * w.1 + b * w.2 := by
        have hpQ₁ := (Finset.mem_sdiff.mp (hullBoundary_subset Q₂ hpA2)).1
        have hp_not := (Finset.mem_sdiff.mp (hullBoundary_subset Q₂ hpA2)).2
        refine lt_of_le_of_ne (hmax p hpQ₁) (fun heq => hp_not ?_)
        exact mem_hullBoundary.mpr ⟨hpQ₁, a, b, hab, fun u hu => by linarith [hmax u hu]⟩
      have hlt_q : a * q.1 + b * q.2 < a * w.1 + b * w.2 := by
        have hqQ₁ := (Finset.mem_sdiff.mp (hullBoundary_subset Q₂ hqA2)).1
        have hq_not := (Finset.mem_sdiff.mp (hullBoundary_subset Q₂ hqA2)).2
        refine lt_of_le_of_ne (hmax q hqQ₁) (fun heq => hq_not ?_)
        exact mem_hullBoundary.mpr ⟨hqQ₁, a, b, hab, fun u hu => by linarith [hmax u hu]⟩
      rw [convexHull_eq] at hwconv
      obtain ⟨ι, s, f, g, hf0, hf1, hg, hcm⟩ := hwconv
      have hsum_ab : a * w.1 + b * w.2 = ∑ i ∈ s, f i * (a * (g i).1 + b * (g i).2) := by
        rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hf1]
        simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
          Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
      have hdiff0 : ∀ i ∈ s, f i * ((a * w.1 + b * w.2) - (a * (g i).1 + b * (g i).2)) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun i hi => mul_nonneg (hf0 i hi) (by
          have := hmax (g i) (hsubQ₁ (hg i hi)); linarith)).mp (by
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hf1, one_mul, ← hsum_ab, sub_self])
      have hw_seg : w ∈ segment ℝ x y := by
        have hmem_xy : w ∈ convexHull ℝ ({x, y} : Set (ℝ × ℝ)) := by
          rw [convexHull_eq]
          refine ⟨ι, s.filter (fun i => 0 < f i), f, g,
            fun i hi => hf0 i (Finset.mem_filter.mp hi).1, ?_, ?_, ?_⟩
          · have h1 := Finset.sum_filter_add_sum_filter_not s (fun i => 0 < f i) f
            have h2 : ∑ i ∈ s.filter (fun i => ¬ 0 < f i), f i = 0 :=
              Finset.sum_eq_zero fun i hi => le_antisymm (not_lt.mp (Finset.mem_filter.mp hi).2)
                (hf0 i (Finset.mem_filter.mp hi).1)
            linarith
          · intro i hi
            have hfi := (Finset.mem_filter.mp hi).2
            have h0i := (mul_eq_zero.mp (hdiff0 i (Finset.mem_filter.mp hi).1)).resolve_left (ne_of_gt hfi)
            have hgi := hg i (Finset.mem_filter.mp hi).1
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgi ⊢
            rcases hgi with hgi | hgi | hgi | hgi <;> rw [hgi] at h0i ⊢
            · exact Or.inl rfl
            · exact Or.inr rfl
            · linarith
            · linarith
          · have hsum1 : ∑ i ∈ s.filter (fun i => 0 < f i), f i = 1 := by
              have h1 := Finset.sum_filter_add_sum_filter_not s (fun i => 0 < f i) f
              have h2 : ∑ i ∈ s.filter (fun i => ¬ 0 < f i), f i = 0 :=
                Finset.sum_eq_zero fun i hi => le_antisymm (not_lt.mp (Finset.mem_filter.mp hi).2)
                  (hf0 i (Finset.mem_filter.mp hi).1)
              linarith
            rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hf1, Finset.centerMass_eq_of_sum_1 _ _ hsum1]
            have h1 := Finset.sum_filter_add_sum_filter_not s (fun i => 0 < f i) (fun i => f i • g i)
            have h2 : ∑ i ∈ s.filter (fun i => ¬ 0 < f i), f i • g i = 0 :=
              Finset.sum_eq_zero fun i hi => by
                rw [le_antisymm (not_lt.mp (Finset.mem_filter.mp hi).2) (hf0 i (Finset.mem_filter.mp hi).1), zero_smul]
            rw [h2, add_zero] at h1; exact h1
        rwa [← convexHull_pair]
      obtain ⟨r1, r2, hr1, hr2, hr12, hrw⟩ := hw_seg
      rcases eq_or_lt_of_le hr1 with rfl | hr1'
      · have : r2 = 1 := by linarith
        rw [this, zero_smul, zero_add, one_smul] at hrw; simp [← hrw]
      · rcases eq_or_lt_of_le hr2 with rfl | hr2'
        · have : r1 = 1 := by linarith
          rw [this, zero_smul, add_zero, one_smul] at hrw; simp [← hrw]
        · exfalso
          have hzxw : 0 < orient z x w := by
            rw [← hrw, orient_add_smul z x x y r1 r2 hr12, orient_self_right]; nlinarith
          have hzwy : 0 < orient z w y := by
            have : orient z w y = -orient z y w := by unfold orient; ring
            rw [this, ← hrw, orient_add_smul z y x y r1 r2 hr12, orient_self_right]
            have : orient z y x = -orient z x y := by unfold orient; ring
            nlinarith
          exact hxy_consec w hwA1 ⟨hzxw, hzwy⟩
    · -- w ∈ Q₂: since orient p q w ≥ 0 on Q₂ and orient p q ≤ 0 on {x, y, q, p}, w ∈ segment [p, q]!
      have hwQ₂ : w ∈ Q₂ := Finset.mem_sdiff.mpr ⟨hwQ₁, hwA1⟩
      have hpqw_ge : 0 ≤ orient p q w := hpq_ge w hwQ₂
      have hpqw_le : orient p q w ≤ 0 := orient_le_of_mem_convexHull hwconv fun v hv => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with hv | hv | hv | hv <;> rw [hv]
        · have : orient p q x = -orient x q p := by unfold orient; ring
          linarith
        · have : orient p q y = -orient y q p := by unfold orient; ring
          linarith
        · exact (orient_self_right _ _).le
        · exact (orient_self_mid _ _).le
      have hpqw_0 : orient p q w = 0 := le_antisymm hpqw_le hpqw_ge
      have hwA2 : w ∈ hullBoundary Q₂ := by
        by_contra hnot
        have := hpq_int w (Finset.mem_sdiff.mpr ⟨hwQ₂, hnot⟩)
        linarith
      rw [convexHull_eq] at hwconv
      obtain ⟨ι, s, f, g, hf0, hf1, hg, hcm⟩ := hwconv
      have hsum_pq : orient p q w = ∑ i ∈ s, f i * orient p q (g i) := by
        rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hf1]
        unfold orient
        simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        have ha1 : (∑ i ∈ s, f i * (g i).2) - p.2 = ∑ i ∈ s, f i * ((g i).2 - p.2) := by
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hf1, one_mul]
        have ha2 : (∑ i ∈ s, f i * (g i).1) - p.1 = ∑ i ∈ s, f i * ((g i).1 - p.1) := by
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hf1, one_mul]
        rw [ha1, ha2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
      have hzero : ∀ i ∈ s, f i * (-orient p q (g i)) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun i hi => mul_nonneg (hf0 i hi) (by
          have hgi := hg i hi
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgi
          rcases hgi with hgi | hgi | hgi | hgi <;> rw [hgi]
          · have : orient p q x = -orient x q p := by unfold orient; ring
            linarith
          · have : orient p q y = -orient y q p := by unfold orient; ring
            linarith
          · rw [orient_self_right]; linarith
          · rw [orient_self_mid]; linarith)).mp (by
          simp only [mul_neg, Finset.sum_neg_distrib]; linarith)
      have hw_seg : w ∈ segment ℝ p q := by
        have hmem_pq : w ∈ convexHull ℝ ({p, q} : Set (ℝ × ℝ)) := by
          rw [convexHull_eq]
          refine ⟨ι, s.filter (fun i => 0 < f i), f, g,
            fun i hi => hf0 i (Finset.mem_filter.mp hi).1, ?_, ?_, ?_⟩
          · have h1 := Finset.sum_filter_add_sum_filter_not s (fun i => 0 < f i) f
            have h2 : ∑ i ∈ s.filter (fun i => ¬ 0 < f i), f i = 0 :=
              Finset.sum_eq_zero fun i hi => le_antisymm (not_lt.mp (Finset.mem_filter.mp hi).2)
                (hf0 i (Finset.mem_filter.mp hi).1)
            linarith
          · intro i hi
            have hfi := (Finset.mem_filter.mp hi).2
            have h0i := (mul_eq_zero.mp (hzero i (Finset.mem_filter.mp hi).1)).resolve_left (ne_of_gt hfi)
            have hgi := hg i (Finset.mem_filter.mp hi).1
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgi ⊢
            rcases hgi with hgi | hgi | hgi | hgi <;> rw [hgi] at h0i ⊢
            · have : orient p q x = -orient x q p := by unfold orient; ring
              linarith
            · have : orient p q y = -orient y q p := by unfold orient; ring
              linarith
            · exact Or.inr rfl
            · exact Or.inl rfl
          · have hsum1 : ∑ i ∈ s.filter (fun i => 0 < f i), f i = 1 := by
              have h1 := Finset.sum_filter_add_sum_filter_not s (fun i => 0 < f i) f
              have h2 : ∑ i ∈ s.filter (fun i => ¬ 0 < f i), f i = 0 :=
                Finset.sum_eq_zero fun i hi => le_antisymm (not_lt.mp (Finset.mem_filter.mp hi).2)
                  (hf0 i (Finset.mem_filter.mp hi).1)
              linarith
            rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hf1, Finset.centerMass_eq_of_sum_1 _ _ hsum1]
            have h1 := Finset.sum_filter_add_sum_filter_not s (fun i => 0 < f i) (fun i => f i • g i)
            have h2 : ∑ i ∈ s.filter (fun i => ¬ 0 < f i), f i • g i = 0 :=
              Finset.sum_eq_zero fun i hi => by
                rw [le_antisymm (not_lt.mp (Finset.mem_filter.mp hi).2) (hf0 i (Finset.mem_filter.mp hi).1), zero_smul]
            rw [h2, add_zero] at h1; exact h1
        rwa [← convexHull_pair]
      obtain ⟨r1, r2, hr1, hr2, hr12, hrw⟩ := hw_seg
      rcases eq_or_lt_of_le hr1 with rfl | hr1'
      · have : r2 = 1 := by linarith
        rw [this, zero_smul, zero_add, one_smul] at hrw; simp [← hrw]
      · rcases eq_or_lt_of_le hr2 with rfl | hr2'
        · have : r1 = 1 := by linarith
          rw [this, zero_smul, add_zero, one_smul] at hrw; simp [← hrw]
        · exfalso
          have hzpw : 0 < orient z p w := by
            rw [← hrw, orient_add_smul z p p q r1 r2 hr12, orient_self_right]; nlinarith
          have hzwq : 0 < orient z w q := by
            have : orient z w q = -orient z q w := by unfold orient; ring
            rw [this, ← hrw, orient_add_smul z q p q r1 r2 hr12, orient_self_right]
            have : orient z q p = -orient z p q := by unfold orient; ring
            nlinarith
          exact hpq_consec w hwA2 ⟨hzpw, hzwq⟩
  have hxP : x ∈ P := hQ₁P (hullBoundary_subset Q₁ hxA1)
  have hyP : y ∈ P := hQ₁P (hullBoundary_subset Q₁ hyA1)
  have hqP : q ∈ P := hQ₁P (Finset.mem_sdiff.mp (hullBoundary_subset Q₂ hqA2)).1
  have hpP : p ∈ P := hQ₁P (Finset.mem_sdiff.mp (hullBoundary_subset Q₂ hpA2)).1
  have hnocone := no_cone_point_of_empty_quad hpent hxP hyP hqP hpP hxyq hxyp hxqp hyqp h4empty
  -- Claim B: (p, q) is empty in hullBoundary Q₃!
  have hpq_empty : ∀ r ∈ hullBoundary Q₃, ¬(0 < orient z p r ∧ 0 < orient z r q) := by
    intro r hrA3 ⟨hzpr, hzrq⟩
    have hrQ₃ : r ∈ Q₃ := hullBoundary_subset Q₃ hrA3
    have hrQ₂ : r ∈ Q₂ := (Finset.mem_sdiff.mp hrQ₃).1
    have hrP : r ∈ P := hQ₁P (Finset.mem_sdiff.mp hrQ₂).1
    have hpqr : 0 < orient p q r := hpq_int r hrQ₃
    have hxyr : 0 < orient x y r := hxy_int r hrQ₂
    have hyqr : 0 < orient y q r := by
      have hid : orient z p q * orient y q r = orient p q r * orient z y q + orient z r q * orient y q p := by
        unfold orient; ring
      nlinarith
    have hxrp : 0 < orient x r p := by
      have hid : orient z p q * orient x r p = orient p q r * orient z p x + orient z p r * orient x q p := by
        unfold orient; ring
      nlinarith
    exact hnocone r hrP ⟨hpqr, hyqr, hxrp, hxyr⟩
  -- Claim C: orient z p x = 0 ∨ orient z y q = 0!
  have halign : orient z p x = 0 ∨ orient z y q = 0 := by
    by_contra h; push Not at h
    have h1 : 0 < orient z p x := lt_of_le_of_ne hzpx (Ne.symm h.1)
    have h2 : 0 < orient z y q := lt_of_le_of_ne hzyq (Ne.symm h.2)
    have hpqz : 0 < orient p q z := by rw [orient_cyclic, orient_cyclic]; exact hzpq
    have hyqz : 0 < orient y q z := by rw [orient_cyclic, orient_cyclic]; exact h2
    have hxzp : 0 < orient x z p := by rw [orient_cyclic]; exact h1
    have hxyz : 0 < orient x y z := by rw [orient_cyclic, orient_cyclic]; exact hzxy
    exact hnocone z hzP ⟨hpqz, hyqz, hxzp, hxyz⟩
  exact ⟨p, q, hpA2, hqA2, hzpq, hpq_ge, hpq_int, hpq_consec,
    hzpx, hzxq, hzyq, hzpy, hxyq, hxyp, hxqp, hyqp, h4empty, hpq_empty, halign⟩

private lemma alignment_switch_left_right {P : Finset (ℝ × ℝ)} {z a b c d e : ℝ × ℝ}
    (hpent : ¬ HasEmptyPentagon P)
    (haP : a ∈ P) (hbP : b ∈ P) (hcP : c ∈ P) (hdP : d ∈ P) (heP : e ∈ P)
    (habc : 0 < orient a b c) (habe : 0 < orient a b e)
    (hace : 0 < orient a c e) (hbce : 0 < orient b c e)
    (h4empty : ∀ w ∈ P, w ∈ convexHull ℝ ({a, b, c, e} : Set (ℝ × ℝ)) → w ∈ ({a, b, c, e} : Set (ℝ × ℝ)))
    (hzec : 0 < orient z e c) (hzac : 0 < orient z a c)
    (hzea : orient z e a = 0) (hzbc : 0 < orient z b c)
    (hecd : 0 < orient e c d) (habd : 0 < orient a b d)
    (hzcd : orient z c d = 0) (hzed : 0 < orient z e d) :
    False := by
  have hnocone := no_cone_point_of_empty_quad hpent haP hbP hcP heP habc habe hace hbce h4empty
  -- First: d = (1 - t) • z + t • c with 0 < t < 1, giving 0 < orient b c d!
  have hd_comb : orient z e c • (d - z) = orient z e d • (c - z) := by
    ext
    · simp only [Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
      unfold orient at hzcd ⊢; linear_combination -(e.1 - z.1) * hzcd
    · simp only [Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
      unfold orient at hzcd ⊢; linear_combination -(e.2 - z.2) * hzcd
  set t := orient z e d / orient z e c
  have ht0 : 0 < t := div_pos hzed hzec
  have hd_eq : d = (1 - t) • z + t • c := by
    ext
    · have h1 := congrArg Prod.fst hd_comb
      simp only [Prod.smul_fst, Prod.fst_sub, Prod.fst_add, smul_eq_mul] at h1 ⊢
      dsimp [t]; field_simp [ne_of_gt hzec]; linarith
    · have h2 := congrArg Prod.snd hd_comb
      simp only [Prod.smul_snd, Prod.snd_sub, Prod.snd_add, smul_eq_mul] at h2 ⊢
      dsimp [t]; field_simp [ne_of_gt hzec]; linarith
  have ht1 : t < 1 := by
    have h1 : orient e c d = (1 - t) * orient e c z := by
      rw [hd_eq, orient_add_smul e c z c (1 - t) t (by ring), orient_self_right]; ring
    have hecz : 0 < orient e c z := by rw [orient_cyclic, orient_cyclic]; exact hzec
    -- Actually hecd : 0 < orient e c d and hefd_c : orient e c d < orient e c z!
    -- Wait: orient e c d = (1 - t) * orient e c z, and 0 < orient e c d gives t < 1!
    nlinarith
  have hbcd : 0 < orient b c d := by
    rw [hd_eq, orient_add_smul b c z c (1 - t) t (by ring), orient_self_right]
    have hbcz : orient b c z = orient z b c := by unfold orient; ring
    rw [hbcz]; nlinarith
  -- Second: e = (1 - u) • z + u • a with 0 < u < 1, giving 0 < orient a d e!
  have he_comb : orient z a c • (e - z) = orient z e c • (a - z) := by
    ext
    · simp only [Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
      unfold orient at hzea ⊢; linear_combination -(c.1 - z.1) * hzea
    · simp only [Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
      unfold orient at hzea ⊢; linear_combination -(c.2 - z.2) * hzea
  set u := orient z e c / orient z a c
  have hu0 : 0 < u := div_pos hzec hzac
  have ha_eq : a = (1 - u⁻¹) • z + u⁻¹ • e := by
    have hne_u : u ≠ 0 := ne_of_gt hu0
    ext
    · have h1 := congrArg Prod.fst he_comb
      simp only [Prod.smul_fst, Prod.fst_sub, Prod.fst_add, smul_eq_mul] at h1 ⊢
      dsimp [u]; field_simp [ne_of_gt hzec, ne_of_gt hzac]; linarith
    · have h2 := congrArg Prod.snd he_comb
      simp only [Prod.smul_snd, Prod.snd_sub, Prod.snd_add, smul_eq_mul] at h2 ⊢
      dsimp [u]; field_simp [ne_of_gt hzec, ne_of_gt hzac]; linarith
  have hu1 : 1 < u⁻¹ := by
    have h1 : orient e c a = (1 - u⁻¹) * orient e c z := by
      rw [ha_eq, orient_add_smul e c z e (1 - u⁻¹) u⁻¹ (by ring), orient_self_mid]; ring
    have hecz : 0 < orient e c z := by rw [orient_cyclic, orient_cyclic]; exact hzec
    have heca : orient e c a < 0 := by
      have : orient e c a = -orient a c e := by unfold orient; ring
      linarith
    nlinarith
  have hade : 0 < orient a d e := by
    have h1 : orient a d e = orient e a d := by unfold orient; ring
    rw [h1]
    have h2 : orient e a d = (u⁻¹ - 1) * orient z e d := by
      rw [ha_eq]; unfold orient
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [h2]; nlinarith
  exact hnocone d hdP ⟨hecd, hbcd, hade, habd⟩

private lemma alignment_switch_right_left {P : Finset (ℝ × ℝ)} {z a b c f e : ℝ × ℝ}
    (hpent : ¬ HasEmptyPentagon P)
    (haP : a ∈ P) (hbP : b ∈ P) (hcP : c ∈ P) (hfP : f ∈ P) (heP : e ∈ P)
    (habc : 0 < orient a b c) (habe : 0 < orient a b e)
    (hace : 0 < orient a c e) (hbce : 0 < orient b c e)
    (h4empty : ∀ w ∈ P, w ∈ convexHull ℝ ({a, b, c, e} : Set (ℝ × ℝ)) → w ∈ ({a, b, c, e} : Set (ℝ × ℝ)))
    (hzec : 0 < orient z e c) (hzeb : 0 < orient z e b)
    (hzbc : orient z b c = 0) (hzea : 0 < orient z e a)
    (hecf : 0 < orient e c f) (habf : 0 < orient a b f)
    (hzfe : orient z f e = 0) (hzfc : 0 < orient z f c) :
    False := by
  have hnocone := no_cone_point_of_empty_quad hpent haP hbP hcP heP habc habe hace hbce h4empty
  -- First: f = (1 - t) • z + t • e with 0 < t < 1, giving 0 < orient a f e!
  have hf_comb : orient z e c • (f - z) = orient z f c • (e - z) := by
    ext
    · simp only [Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
      unfold orient at hzfe ⊢; linear_combination -(c.1 - z.1) * hzfe
    · simp only [Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
      unfold orient at hzfe ⊢; linear_combination -(c.2 - z.2) * hzfe
  set t := orient z f c / orient z e c
  have ht0 : 0 < t := div_pos hzfc hzec
  have hf_eq : f = (1 - t) • z + t • e := by
    ext
    · have h1 := congrArg Prod.fst hf_comb
      simp only [Prod.smul_fst, Prod.fst_sub, Prod.fst_add, smul_eq_mul] at h1 ⊢
      dsimp [t]; field_simp [ne_of_gt hzec]; linarith
    · have h2 := congrArg Prod.snd hf_comb
      simp only [Prod.smul_snd, Prod.snd_sub, Prod.snd_add, smul_eq_mul] at h2 ⊢
      dsimp [t]; field_simp [ne_of_gt hzec]; linarith
  have ht1 : t < 1 := by
    have h1 : orient e c f = (1 - t) * orient e c z := by
      rw [hf_eq, orient_add_smul e c z e (1 - t) t (by ring), orient_self_mid]; ring
    have hecz : 0 < orient e c z := by rw [orient_cyclic, orient_cyclic]; exact hzec
    nlinarith
  have hafe : 0 < orient a f e := by
    have h1 : orient a f e = -orient a e f := by unfold orient; ring
    rw [h1, hf_eq, orient_add_smul a e z e (1 - t) t (by ring), orient_self_right]
    have haez : orient a e z = -orient z e a := by unfold orient; ring
    rw [haez]; nlinarith
  -- Second: b = (1 - u⁻¹) • z + u⁻¹ • c with 1 < u⁻¹, giving 0 < orient b c f!
  have hc_comb : orient z e b • (c - z) = orient z e c • (b - z) := by
    ext
    · simp only [Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
      unfold orient at hzbc ⊢; linear_combination -(e.1 - z.1) * hzbc
    · simp only [Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
      unfold orient at hzbc ⊢; linear_combination -(e.2 - z.2) * hzbc
  set u := orient z e c / orient z e b
  have hu0 : 0 < u := div_pos hzec hzeb
  have hb_eq : b = (1 - u⁻¹) • z + u⁻¹ • c := by
    ext
    · have h1 := congrArg Prod.fst hc_comb
      simp only [Prod.smul_fst, Prod.fst_sub, Prod.fst_add, smul_eq_mul] at h1 ⊢
      dsimp [u]; field_simp [ne_of_gt hzec, ne_of_gt hzeb]; linarith
    · have h2 := congrArg Prod.snd hc_comb
      simp only [Prod.smul_snd, Prod.snd_sub, Prod.snd_add, smul_eq_mul] at h2 ⊢
      dsimp [u]; field_simp [ne_of_gt hzec, ne_of_gt hzeb]; linarith
  have hu1 : 1 < u⁻¹ := by
    have h1 : orient e c b = (1 - u⁻¹) * orient e c z := by
      rw [hb_eq, orient_add_smul e c z c (1 - u⁻¹) u⁻¹ (by ring), orient_self_right]; ring
    have hecz : 0 < orient e c z := by rw [orient_cyclic, orient_cyclic]; exact hzec
    have hecb : orient e c b < 0 := by
      have : orient e c b = -orient b c e := by unfold orient; ring
      linarith
    nlinarith
  have hbcf : 0 < orient b c f := by
    have h2 : orient b c f = (u⁻¹ - 1) * orient z f c := by
      rw [hb_eq]; unfold orient
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [h2]; nlinarith
  exact hnocone f hfP ⟨hecf, hbcf, hafe, habf⟩

private lemma collinear_of_ray_chain {P : Finset (ℝ × ℝ)} {k : ℕ} (hk : 3 ≤ k)
    (z : ℝ × ℝ) (hzP : z ∈ P)
    (u : Fin (k - 1) → ℝ × ℝ)
    (huP : ∀ i, u i ∈ P)
    (hu_ne_z : ∀ i, u i ≠ z)
    (hu_inj : Function.Injective u)
    (hchain : ∀ i : ℕ, (hi : i + 1 < k - 1) → orient z (u ⟨i, by omega⟩) (u ⟨i + 1, hi⟩) = 0) :
    HasCollinear k P := by
  classical
  have h0_lt : 0 < k - 1 := by omega
  have hall_col : ∀ i : Fin (k - 1), orient z (u ⟨0, h0_lt⟩) (u i) = 0 := by
    intro ⟨i, hi⟩
    induction i with
    | zero => exact orient_self_right _ _
    | succ m ih =>
      have hm := ih (by omega)
      have hstep := hchain m hi
      have hne : u ⟨m, by omega⟩ ≠ z := hu_ne_z ⟨m, by omega⟩
      have hpl : orient z (u ⟨0, h0_lt⟩) (u ⟨m + 1, hi⟩) * ((u ⟨m, by omega⟩).1 - z.1) =
          orient z (u ⟨0, h0_lt⟩) (u ⟨m, by omega⟩) * ((u ⟨m + 1, hi⟩).1 - z.1) +
          orient z (u ⟨m, by omega⟩) (u ⟨m + 1, hi⟩) * ((u ⟨0, h0_lt⟩).1 - z.1) := by
        unfold orient; ring
      have hpl2 : orient z (u ⟨0, h0_lt⟩) (u ⟨m + 1, hi⟩) * ((u ⟨m, by omega⟩).2 - z.2) =
          orient z (u ⟨0, h0_lt⟩) (u ⟨m, by omega⟩) * ((u ⟨m + 1, hi⟩).2 - z.2) +
          orient z (u ⟨m, by omega⟩) (u ⟨m + 1, hi⟩) * ((u ⟨0, h0_lt⟩).2 - z.2) := by
        unfold orient; ring
      rw [hm, hstep, zero_mul, zero_mul, add_zero] at hpl hpl2
      by_cases hx : (u ⟨m, by omega⟩).1 - z.1 ≠ 0
      · exact (mul_eq_zero.mp hpl).resolve_right hx
      · push Not at hx
        have hy : (u ⟨m, by omega⟩).2 - z.2 ≠ 0 := fun h => hne (Prod.ext (by linarith) (by linarith))
        exact (mul_eq_zero.mp hpl2).resolve_right hy
  let S : Finset (ℝ × ℝ) := insert z (Finset.univ.image u)
  have hSP : S ⊆ P := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw'
    · exact hzP
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw'; exact huP i
  have hz_not : z ∉ Finset.univ.image u := by
    intro h; obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h; exact hu_ne_z i hi
  have hScard : #S = k := by
    rw [Finset.card_insert_of_notMem hz_not, Finset.card_image_of_injective _ hu_inj, Finset.card_fin]
    omega
  refine ⟨S, hSP, hScard, collinear_of_orient_eq_zero (Ne.symm (hu_ne_z ⟨0, h0_lt⟩)) fun w hw => ?_⟩
  rcases Finset.mem_insert.mp (Finset.mem_coe.mp hw) with rfl | hw'
  · exact orient_self_mid _ _
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw'; exact hall_col i

private lemma empty_pentagon_ge_three (k : ℕ) (hk : 3 ≤ k) :
    ∃ n₀ : ℕ, ∀ P : Finset (ℝ × ℝ),
      n₀ ≤ #P → HasCollinear k P ∨ HasEmptyPentagon P := by
  classical
  set C := 11 * (k - 1) + 1
  set M := (4 * C) ^ k
  have hC_ge : 23 ≤ C := by dsimp [C]; omega
  have h4C_ge : 92 ≤ 4 * C := by omega
  have hM_ge3 : 3 ≤ M := by
    have : 92 ≤ (4 * C) ^ k := le_trans h4C_ge (Nat.le_self_pow (by omega) _)
    omega
  refine ⟨esNum M M, fun P hP => ?_⟩
  by_contra hboth
  push Not at hboth
  obtain ⟨hcol, hpent⟩ := hboth
  -- Step 1: find minimal convex-closed Q₀ ⊆ P with M ≤ #(hullBoundary Q₀)
  let Good : Finset (Finset (ℝ × ℝ)) := P.powerset.filter fun Q =>
    (∀ w ∈ P, w ∈ convexHull ℝ (Q : Set (ℝ × ℝ)) → w ∈ Q) ∧ M ≤ #(hullBoundary Q)
  have hGood_ne : Good.Nonempty := by
    obtain ⟨X, hXP, hXcard, hXconv⟩ := exists_inConvexPos M (by omega) P hP
    let Q := P.filter fun x => x ∈ convexHull ℝ (X : Set (ℝ × ℝ))
    have ⟨hQP, hQclosed, hXsub⟩ := inConvexPos_subset_hullBoundary hXP (by omega) hXconv
    refine ⟨Q, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hQP, hQclosed, ?_⟩⟩
    exact le_trans (by omega : M ≤ #X) (Finset.card_le_card hXsub)
  obtain ⟨Q₀, hQ₀Good, hQ₀min⟩ := Good.exists_min_image Finset.card hGood_ne
  obtain ⟨hQ₀pow, hQ₀closed, hQ₀M⟩ := Finset.mem_filter.mp hQ₀Good
  have hQ₀P : Q₀ ⊆ P := Finset.mem_powerset.mp hQ₀pow
  -- Step 2: define convex layers layerQ i and layerA i
  let layerQ : ℕ → Finset (ℝ × ℝ) := fun i => Nat.rec Q₀ (fun _ Q => Q \ hullBoundary Q) i
  let layerA : ℕ → Finset (ℝ × ℝ) := fun i => hullBoundary (layerQ i)
  have hlayerQ_step : ∀ i, layerQ (i + 1) = layerQ i \ layerA i := fun _ => rfl
  have hlayerQ_sub : ∀ i, layerQ i ⊆ P := by
    intro i; induction i with
    | zero => exact hQ₀P
    | succ i ih => exact Finset.sdiff_subset.trans ih
  have hlayerQ_closed : ∀ i, ∀ w ∈ P, w ∈ convexHull ℝ (SetLike.coe (layerQ i)) → w ∈ layerQ i := by
    intro i; induction i with
    | zero => exact hQ₀closed
    | succ i ih => exact layer_convexClosed ih
  have hlayerQ_mono : ∀ i j, i ≤ j → layerQ j ⊆ layerQ i := by
    intro i j hij
    induction hij with
    | refl => exact Finset.Subset.rfl
    | step _ ih => exact Finset.sdiff_subset.trans ih
  -- Step 3: prove #(layerA i) ≥ (4 * C) ^ (k - i) for all i ≤ k - 1
  have hlayerA_size : ∀ i, i ≤ k - 1 → (4 * C) ^ (k - i) ≤ #(layerA i) := by
    intro i hi
    induction i with
    | zero => exact hQ₀M
    | succ i ih =>
      have hprev := ih (by omega)
      have hbd := card_layer_bound hk (hlayerQ_sub i) (hlayerQ_closed i) hcol hpent
      change #(layerA i) < C * (#(layerA (i + 1)) + 3) at hbd
      have hpow : (4 * C) ^ (k - i) = 4 * C * (4 * C) ^ (k - (i + 1)) := by
        rw [show k - i = (k - (i + 1)) + 1 by omega, pow_succ']
      have h1 : (4 * C) ^ (k - (i + 1)) ≥ 1 := Nat.one_le_pow _ _ (by omega)
      have h2 : C * ((4 * C) ^ (k - (i + 1)) + 3) ≤ (4 * C) ^ (k - i) := by
        rw [hpow]
        have : (4 * C) ^ (k - (i + 1)) + 3 ≤ 4 * (4 * C) ^ (k - (i + 1)) := by omega
        nlinarith
      have h3 : C * ((4 * C) ^ (k - (i + 1)) + 3) < C * (#(layerA (i + 1)) + 3) :=
        lt_of_le_of_lt h2 (lt_of_le_of_lt hprev hbd)
      have h4 : (4 * C) ^ (k - (i + 1)) + 3 < #(layerA (i + 1)) + 3 :=
        Nat.lt_of_mul_lt_mul_left h3
      omega
  -- Pick z ∈ layerA (k - 1) ⊆ layerQ (k - 1)
  have hAk1_pos : 1 ≤ #(layerA (k - 1)) := by
    have h := hlayerA_size (k - 1) le_rfl
    have : 1 ≤ (4 * C) ^ (k - (k - 1)) := Nat.one_le_pow _ _ (by omega)
    omega
  obtain ⟨z, hzAk1⟩ := Finset.card_pos.mp (by omega : 0 < #(layerA (k - 1)))
  have hzQk1 : z ∈ layerQ (k - 1) := hullBoundary_subset _ hzAk1
  have hzP : z ∈ P := hlayerQ_sub (k - 1) hzQk1
  have hAi_ge3 : ∀ i, i ≤ k - 2 → 3 ≤ #(layerA i) := by
    intro i hi
    have h := hlayerA_size i (by omega)
    have : 92 ≤ (4 * C) ^ (k - i) := le_trans h4C_ge (Nat.le_self_pow (by omega) _)
    omega
  -- Step 4: #(layerA 1) < #(layerA 0) by minimality of Q₀!
  have hA1_lt_A0 : #(layerA 1) < #(layerA 0) := by
    have hQ1_lt : #(layerQ 1) < #Q₀ := by
      have hne : (layerA 0).Nonempty := Finset.card_pos.mp (by have := hAi_ge3 0 (by omega); omega)
      obtain ⟨w₀, hw₀⟩ := hne
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, fun heq => by
        have : w₀ ∈ layerQ 1 := by rw [heq]; exact hullBoundary_subset Q₀ hw₀
        exact (Finset.mem_sdiff.mp this).2 hw₀⟩)
    by_contra hge; push Not at hge
    have hQ1Good : layerQ 1 ∈ Good := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (hlayerQ_sub 1), hlayerQ_closed 1, le_trans hQ₀M hge⟩
    have := hQ₀min (layerQ 1) hQ1Good
    omega
  -- Step 5: get an empty arc (x₀, y₀) of layerA 0!
  have hzQ1 : z ∈ layerQ 1 := hlayerQ_mono 1 (k - 1) (by omega) hzQk1
  have hz0 : IsStrictInterior (layerQ 0) z :=
    isStrictInterior_of_not_mem_hullBoundary (Finset.mem_sdiff.mp hzQ1).1 (Finset.mem_sdiff.mp hzQ1).2
  obtain ⟨p₀, hp₀_arg⟩ := exists_arc_enum hz0
  obtain ⟨k₀, hk₀_empty⟩ := exists_empty_arc_of_card_lt hz0 (hAi_ge3 0 (by omega)) hA1_lt_A0 p₀ hp₀_arg
  -- Step 6: build the follower chain of length k - 1 (indices 0, ..., k - 2)!
  -- Package arc invariant at layer i ≤ k - 2
  let ArcInv (i : ℕ) (x y : ℝ × ℝ) : Prop :=
    x ∈ layerA i ∧ y ∈ layerA i ∧
    0 < orient z x y ∧
    (∀ w ∈ layerQ (i + 1), 0 < orient x y w) ∧
    (∀ w ∈ layerA i, ¬(0 < orient z x w ∧ 0 < orient z w y)) ∧
    (∀ w ∈ layerA (i + 1), ¬(0 < orient z x w ∧ 0 < orient z w y))
  let StepRel (x y p q : ℝ × ℝ) : Prop :=
    0 ≤ orient z p x ∧ 0 < orient z x q ∧ 0 ≤ orient z y q ∧ 0 < orient z p y ∧
    0 < orient x y q ∧ 0 < orient x y p ∧ 0 < orient x q p ∧ 0 < orient y q p ∧
    (∀ w ∈ P, w ∈ convexHull ℝ ({x, y, q, p} : Set (ℝ × ℝ)) → w ∈ ({x, y, q, p} : Set (ℝ × ℝ))) ∧
    (orient z p x = 0 ∨ orient z y q = 0)
  have hstep_ex : ∀ i, i + 1 ≤ k - 2 → ∀ x y, ArcInv i x y →
      ∃ p q, ArcInv (i + 1) p q ∧ StepRel x y p q := by
    intro i hi x y ⟨hxA, hyA, hzxy, hxy_int, hxy_consec, hxy_empty⟩
    have hz_i2 : z ∈ (layerQ i \ hullBoundary (layerQ i)) \ hullBoundary (layerQ i \ hullBoundary (layerQ i)) :=
      hlayerQ_mono (i + 2) (k - 1) (by omega) hzQk1
    obtain ⟨p, q, hpA, hqA, hzpq, _, hpq_int, hpq_consec,
      hzpx, hzxq, hzyq, hzpy, hxyq, hxyp, hxqp, hyqp, h4empty, hpq_empty, halign⟩ :=
      follower_of_empty_arc hpent (hlayerQ_sub i) (hlayerQ_closed i) hz_i2 (hAi_ge3 (i + 1) hi)
        hxA hyA hzxy hxy_int hxy_consec hxy_empty
    exact ⟨p, q, ⟨hpA, hqA, hzpq, hpq_int, hpq_consec, hpq_empty⟩,
      ⟨hzpx, hzxq, hzyq, hzpy, hxyq, hxyp, hxqp, hyqp, h4empty, halign⟩⟩
  have h0_inv : ArcInv 0 (p₀ k₀).1 (p₀ ⟨(k₀.1 + 1) % #(layerA 0), Nat.mod_lt _ (by have := hAi_ge3 0 (by omega); omega)⟩).1 := by
    have ⟨hzxy, _, hxy_int⟩ := arc_orient_props hz0 (hAi_ge3 0 (by omega)) p₀ hp₀_arg k₀
    have hconsec := no_mem_between_consecutive_arc hz0 (hAi_ge3 0 (by omega)) p₀ hp₀_arg k₀
    exact ⟨(p₀ k₀).2, (p₀ _).2, hzxy, hxy_int, hconsec, hk₀_empty⟩
  -- Build chain by recursion on i < k - 1
  have hchain_ex : ∀ m, m ≤ k - 2 → ∃ f : (i : ℕ) → i ≤ m → (ℝ × ℝ) × (ℝ × ℝ),
      (∀ i (hi : i ≤ m), ArcInv i (f i hi).1 (f i hi).2) ∧
      (∀ i (hi : i + 1 ≤ m), StepRel (f i (by omega)).1 (f i (by omega)).2
        (f (i + 1) hi).1 (f (i + 1) hi).2) := by
    intro m hm
    induction m with
    | zero =>
      refine ⟨fun _ _ => ((p₀ k₀).1, (p₀ ⟨(k₀.1 + 1) % #(layerA 0), Nat.mod_lt _ (by have := hAi_ge3 0 (by omega); omega)⟩).1),
        fun i hi => by dsimp only; rw [show i = 0 by omega]; exact h0_inv,
        fun i hi => by omega⟩
    | succ m ih =>
      obtain ⟨f, hinv, hrel⟩ := ih (by omega)
      obtain ⟨pm, qm, hpm_inv, hpm_rel⟩ := hstep_ex m hm (f m le_rfl).1 (f m le_rfl).2 (hinv m le_rfl)
      refine ⟨fun i hi => if h : i ≤ m then f i h else (pm, qm), ?_, ?_⟩
      · intro i hi
        by_cases h : i ≤ m
        · simp only [dif_pos h]; exact hinv i h
        · simp only [dif_neg h]; rw [show i = m + 1 by omega]; exact hpm_inv
      · intro i hi
        by_cases h : i + 1 ≤ m
        · have hi' : i ≤ m := by omega
          simp only [dif_pos hi', dif_pos h]; exact hrel i h
        · have him : i = m := by omega
          subst him
          simp only [dif_pos le_rfl, dif_neg (by omega : ¬ i + 1 ≤ i)]
          exact hpm_rel
  obtain ⟨F, hFinv, hFrel⟩ := hchain_ex (k - 2) le_rfl
  let X : Fin (k - 1) → ℝ × ℝ := fun i => (F i.1 (by omega)).1
  let Y : Fin (k - 1) → ℝ × ℝ := fun i => (F i.1 (by omega)).2
  -- All X i, Y i lie in pairwise disjoint layers layerA i, all disjoint from {z}
  have hX_mem : ∀ i : Fin (k - 1), X i ∈ layerA i.1 := fun i => (hFinv i.1 (by omega)).1
  have hY_mem : ∀ i : Fin (k - 1), Y i ∈ layerA i.1 := fun i => (hFinv i.1 (by omega)).2.1
  have hX_P : ∀ i : Fin (k - 1), X i ∈ P := fun i => hlayerQ_sub i.1 (hullBoundary_subset _ (hX_mem i))
  have hY_P : ∀ i : Fin (k - 1), Y i ∈ P := fun i => hlayerQ_sub i.1 (hullBoundary_subset _ (hY_mem i))
  have hlayerA_disj : ∀ i j, i < j → ∀ w, w ∈ layerA i → w ∉ layerQ j := by
    intro i j hij w hwA hwQ
    have hwQ1 : w ∈ layerQ (i + 1) := hlayerQ_mono (i + 1) j (by omega) hwQ
    exact (Finset.mem_sdiff.mp hwQ1).2 hwA
  have hX_ne_z : ∀ i : Fin (k - 1), X i ≠ z := fun i h =>
    hlayerA_disj i.1 (k - 1) (by omega) (X i) (hX_mem i) (h ▸ hzQk1)
  have hY_ne_z : ∀ i : Fin (k - 1), Y i ≠ z := fun i h =>
    hlayerA_disj i.1 (k - 1) (by omega) (Y i) (hY_mem i) (h ▸ hzQk1)
  have hX_inj : Function.Injective X := by
    intro i j hij; by_contra hne
    wlog hlt : i < j generalizing i j
    · exact this hij.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
    exact hlayerA_disj i.1 j.1 hlt (X i) (hX_mem i) (hij ▸ hullBoundary_subset _ (hX_mem j))
  have hY_inj : Function.Injective Y := by
    intro i j hij; by_contra hne
    wlog hlt : i < j generalizing i j
    · exact this hij.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
    exact hlayerA_disj i.1 j.1 hlt (Y i) (hY_mem i) (hij ▸ hullBoundary_subset _ (hY_mem j))
  -- Step 7: alignment analysis on steps 0, ..., k - 3!
  let L : ℕ → Prop := fun i => ∀ (hi : i + 1 ≤ k - 2), orient z (X ⟨i + 1, by omega⟩) (X ⟨i, by omega⟩) = 0
  let R : ℕ → Prop := fun i => ∀ (hi : i + 1 ≤ k - 2), orient z (Y ⟨i, by omega⟩) (Y ⟨i + 1, by omega⟩) = 0
  have hnot_all_L : ¬ ∀ i : ℕ, (hi : i + 1 < k - 1) → orient z (X ⟨i + 1, hi⟩) (X ⟨i, by omega⟩) = 0 := by
    intro hall
    exact hcol (collinear_of_ray_chain hk z hzP X hX_P hX_ne_z hX_inj fun i hi => by
      have h := hall i hi
      have : orient z (X ⟨i, by omega⟩) (X ⟨i + 1, hi⟩) = -orient z (X ⟨i + 1, hi⟩) (X ⟨i, by omega⟩) := by
        unfold orient; ring
      linarith)
  have hnot_all_R : ¬ ∀ i : ℕ, (hi : i + 1 < k - 1) → orient z (Y ⟨i, by omega⟩) (Y ⟨i + 1, hi⟩) = 0 := by
    intro hall
    exact hcol (collinear_of_ray_chain hk z hzP Y hY_P hY_ne_z hY_inj hall)
  -- Find first non-double-aligned step m < k - 2
  have hex_nd : ∃ m, ∃ (hm : m < k - 2), ¬(orient z (X ⟨m + 1, by omega⟩) (X ⟨m, by omega⟩) = 0 ∧
      orient z (Y ⟨m, by omega⟩) (Y ⟨m + 1, by omega⟩) = 0) := by
    by_contra h; push Not at h
    exact hnot_all_L fun i hi => (h i (by omega)).1
  let m := Nat.find hex_nd
  have hm_spec := Nat.find_spec hex_nd
  have hm_lt : m < k - 2 := hm_spec.1
  have hm_nd : ¬(orient z (X ⟨m + 1, by omega⟩) (X ⟨m, by omega⟩) = 0 ∧
      orient z (Y ⟨m, by omega⟩) (Y ⟨m + 1, by omega⟩) = 0) := hm_spec.2
  have hm_min : ∀ i (hi : i < m), orient z (X ⟨i + 1, by omega⟩) (X ⟨i, by omega⟩) = 0 ∧
      orient z (Y ⟨i, by omega⟩) (Y ⟨i + 1, by omega⟩) = 0 := by
    intro i hi
    have hnot := Nat.find_min hex_nd hi
    push Not at hnot; exact hnot (by omega)
  have hm_rel := hFrel m (by omega)
  rcases hm_rel.2.2.2.2.2.2.2.2.2 with hmL | hmR
  · -- m is left-only (¬ orient z (Y m) (Y (m+1)) = 0); find first t > m with right-aligned!
    have hm_notR : orient z (Y ⟨m, by omega⟩) (Y ⟨m + 1, by omega⟩) ≠ 0 := fun hR => hm_nd ⟨hmL, hR⟩
    have hex_t : ∃ t, m < t ∧ ∃ (ht : t < k - 2), orient z (Y ⟨t, by omega⟩) (Y ⟨t + 1, by omega⟩) = 0 := by
      push Not at hnot_all_L
      obtain ⟨j, hj, hj_notL⟩ := hnot_all_L
      have hmj : m < j := by
        by_contra hle; push Not at hle
        rcases eq_or_lt_of_le hle with rfl | hlt
        · exact hj_notL hmL
        · exact hj_notL (hm_min j hlt).1
      have hj_rel := hFrel j (by omega)
      exact ⟨j, hmj, by omega, hj_rel.2.2.2.2.2.2.2.2.2.resolve_left hj_notL⟩
    let t := Nat.find hex_t
    have ht_spec := Nat.find_spec hex_t
    have hmt : m < t := ht_spec.1
    have ht_lt : t < k - 2 := ht_spec.2.1
    have ht_R : orient z (Y ⟨t, by omega⟩) (Y ⟨t + 1, by omega⟩) = 0 := ht_spec.2.2
    have htm1_notR : orient z (Y ⟨t - 1, by omega⟩) (Y ⟨t, by omega⟩) ≠ 0 := by
      by_cases heq : t - 1 = m
      · have h1 : (⟨t - 1, by omega⟩ : Fin (k - 1)) = ⟨m, by omega⟩ := Fin.ext heq
        have h2 : (⟨t, by omega⟩ : Fin (k - 1)) = ⟨m + 1, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [h1, h2]; exact hm_notR
      · intro hR
        exact Nat.find_min hex_t (by omega : t - 1 < t) ⟨by omega, by omega, by
          have : (⟨t - 1 + 1, by omega⟩ : Fin (k - 1)) = ⟨t, by omega⟩ := Fin.ext (by dsimp; omega)
          rw [this]; exact hR⟩
    have htm1_rel := hFrel (t - 1) (by omega)
    have ht_rel := hFrel t (by omega)
    have htm1_inv := hFinv (t - 1) (by omega)
    have ht_inv := hFinv t (by omega)
    have htm1_eq : t - 1 + 1 = t := by omega
    -- Relate F (t - 1 + 1) to F t via Fin.ext / subst
    set a := X ⟨t - 1, by omega⟩
    set b := Y ⟨t - 1, by omega⟩
    set c := Y ⟨t, by omega⟩
    set d := Y ⟨t + 1, by omega⟩
    set e := X ⟨t, by omega⟩
    have hStep1 : StepRel a b e c := by
      have := hFrel (t - 1) (by omega)
      convert this using 2 <;> simp [htm1_eq]
    have hStep2 : StepRel e c (X ⟨t + 1, by omega⟩) d := by
      have := hFrel t (by omega)
      convert this using 2
    have htm1_L : orient z e a = 0 := hStep1.2.2.2.2.2.2.2.2.2.resolve_right htm1_notR
    have htm1_zbc : 0 < orient z b c := lt_of_le_of_ne hStep1.2.2.1 (Ne.symm htm1_notR)
    have hzec : 0 < orient z e c := ht_inv.2.2.1
    have hzac : 0 < orient z a c := hStep1.2.1
    have hecd : 0 < orient e c d := ht_inv.2.2.2.1 d (hullBoundary_subset _ (hY_mem ⟨t + 1, by omega⟩))
    have habd : 0 < orient a b d := by
      have hdQ : d ∈ layerQ (t - 1 + 1) := hlayerQ_mono (t - 1 + 1) (t + 1) (by omega) (hullBoundary_subset _ (hY_mem ⟨t + 1, by omega⟩))
      exact htm1_inv.2.2.2.1 d hdQ
    have hzed : 0 < orient z e d := hStep2.2.1
    exact alignment_switch_left_right hpent (hX_P _) (hY_P _) (hY_P _) (hY_P _) (hX_P _)
      hStep1.2.2.2.2.1 hStep1.2.2.2.2.2.1 hStep1.2.2.2.2.2.2.1 hStep1.2.2.2.2.2.2.2.1
      hStep1.2.2.2.2.2.2.2.2.1 hzec hzac htm1_L htm1_zbc hecd habd ht_R hzed
  · -- m is right-only (¬ orient z (X (m+1)) (X m) = 0); find first t > m with left-aligned!
    have hm_notL : orient z (X ⟨m + 1, by omega⟩) (X ⟨m, by omega⟩) ≠ 0 := fun hL => hm_nd ⟨hL, hmR⟩
    have hex_t : ∃ t, m < t ∧ ∃ (ht : t < k - 2), orient z (X ⟨t + 1, by omega⟩) (X ⟨t, by omega⟩) = 0 := by
      push Not at hnot_all_R
      obtain ⟨j, hj, hj_notR⟩ := hnot_all_R
      have hmj : m < j := by
        by_contra hle; push Not at hle
        rcases eq_or_lt_of_le hle with rfl | hlt
        · exact hj_notR hmR
        · exact hj_notR (hm_min j hlt).2
      have hj_rel := hFrel j (by omega)
      exact ⟨j, hmj, by omega, hj_rel.2.2.2.2.2.2.2.2.2.resolve_right hj_notR⟩
    let t := Nat.find hex_t
    have ht_spec := Nat.find_spec hex_t
    have hmt : m < t := ht_spec.1
    have ht_lt : t < k - 2 := ht_spec.2.1
    have ht_L : orient z (X ⟨t + 1, by omega⟩) (X ⟨t, by omega⟩) = 0 := ht_spec.2.2
    have htm1_notL : orient z (X ⟨t, by omega⟩) (X ⟨t - 1, by omega⟩) ≠ 0 := by
      by_cases heq : t - 1 = m
      · have h1 : (⟨t - 1, by omega⟩ : Fin (k - 1)) = ⟨m, by omega⟩ := Fin.ext heq
        have h2 : (⟨t, by omega⟩ : Fin (k - 1)) = ⟨m + 1, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [h1, h2]; exact hm_notL
      · intro hL
        exact Nat.find_min hex_t (by omega : t - 1 < t) ⟨by omega, by omega, by
          have : (⟨t - 1 + 1, by omega⟩ : Fin (k - 1)) = ⟨t, by omega⟩ := Fin.ext (by dsimp; omega)
          rw [this]; exact hL⟩
    have htm1_inv := hFinv (t - 1) (by omega)
    have ht_inv := hFinv t (by omega)
    have htm1_eq : t - 1 + 1 = t := by omega
    set a := X ⟨t - 1, by omega⟩
    set b := Y ⟨t - 1, by omega⟩
    set c := Y ⟨t, by omega⟩
    set f := X ⟨t + 1, by omega⟩
    set e := X ⟨t, by omega⟩
    have hStep1 : StepRel a b e c := by
      have := hFrel (t - 1) (by omega)
      convert this using 2 <;> simp [htm1_eq]
    have hStep2 : StepRel e c f (Y ⟨t + 1, by omega⟩) := by
      have := hFrel t (by omega)
      convert this using 2
    have htm1_R : orient z b c = 0 := hStep1.2.2.2.2.2.2.2.2.2.resolve_left htm1_notL
    have htm1_zea : 0 < orient z e a := lt_of_le_of_ne hStep1.1 (Ne.symm htm1_notL)
    have hzec : 0 < orient z e c := ht_inv.2.2.1
    have hzeb : 0 < orient z e b := hStep1.2.2.2.1
    have hecf : 0 < orient e c f := ht_inv.2.2.2.1 f (hullBoundary_subset _ (hX_mem ⟨t + 1, by omega⟩))
    have habf : 0 < orient a b f := by
      have hfQ : f ∈ layerQ (t - 1 + 1) := hlayerQ_mono (t - 1 + 1) (t + 1) (by omega) (hullBoundary_subset _ (hX_mem ⟨t + 1, by omega⟩))
      exact htm1_inv.2.2.2.1 f hfQ
    have hzfc : 0 < orient z f c := hStep2.2.2.2.1
    exact alignment_switch_right_left hpent (hX_P _) (hY_P _) (hY_P _) (hX_P _) (hX_P _)
      hStep1.2.2.2.2.1 hStep1.2.2.2.2.2.1 hStep1.2.2.2.2.2.2.1 hStep1.2.2.2.2.2.2.2.1
      hStep1.2.2.2.2.2.2.2.2.1 hzec hzeb htm1_R htm1_zea hecf habf ht_L hzfc

private theorem empty_pentagon_main :
    ∀ k : ℕ, 2 ≤ k → ∃ n₀ : ℕ, ∀ P : Finset (ℝ × ℝ),
      n₀ ≤ #P → HasCollinear k P ∨ HasEmptyPentagon P := by
  intro k hk
  rcases eq_or_lt_of_le hk with rfl | hk3
  · refine ⟨2, fun P hP => Or.inl ?_⟩
    obtain ⟨S, hSP, hScard⟩ := Finset.exists_subset_card_eq hP
    refine ⟨S, hSP, hScard, ?_⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hScard
    simpa [Finset.coe_insert, Finset.coe_singleton] using collinear_pair ℝ a b
  · exact empty_pentagon_ge_three k hk3

end Green70

theorem OMA.solution : type_of% @Green70.green_70.variants.empty_pentagon :=
  Green70.empty_pentagon_main
