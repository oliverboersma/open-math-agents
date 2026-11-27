import FormalConjectures.ErdosProblems.«963»

/-! An integer, congruence-based reduction for Erdős 963. -/

-- Credit: @MrSeizy

open Finset

namespace OMA.R_Erdos963_erdos_963_parts_ii_R1

-- The established small positive-set bounds, including the sharper bound at dimension four.
def H1 : Prop :=
  ∀ (d : ℕ), d ≤ 4 → ∀ P : Finset ℤ, (∀ x ∈ P, 0 < x) →
    (∀ D ⊆ P, D.card = d + 1 → ¬ AddDissociated (D : Set ℤ)) →
    P.card < 2 ^ d ∧ (d = 4 → P.card ≤ 14)

-- Affine extraction and common triple subsums.
def H2 : Prop :=
  let aff := (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S)
  let triples := (fun (M : Finset ℤ) ↦ (M.powersetCard 3).image (fun S ↦ S.sum id))
  (∀ (X : Finset ℤ) (k : ℕ),
    (k = 4 ∧ 5 ≤ X.card) ∨ (k = 5 ∧ 8 ≤ X.card) ∨ (k = 6 ∧ 14 ≤ X.card) →
    ∃ D ⊆ X, D.card = k ∧ aff D) ∧
  (∀ (X : Finset ℤ) (k : ℕ), (k = 4 ∧ 5 ≤ X.card) ∨ (k = 5 ∧ 9 ≤ X.card) →
    ∃ D ⊆ X, ∃ E ⊆ X, D.card = k ∧ E.card = k ∧ aff D ∧ aff E ∧ D.sum id ≠ E.sum id) ∧
  (∀ X W : Finset ℤ, 5 ≤ X.card →
    (∀ F ⊆ X, F.card = 4 → aff F → W ⊆ triples F) →
    W.card ≤ if 6 ≤ X.card then 2 else 3)

-- Classification of seven-point affine extremizers from the public affine-fourteen argument.
def H3 : Prop :=
  let aff := (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S)
  ∀ X : Finset ℤ, X.card = 7 →
    (∀ F ⊆ X, F.card = 5 → ¬ aff F) →
    ∃ x a b : ℤ, 0 < a ∧ a < b ∧ X = {x,x-a,x+a,x-b,x+b,x-(a+b),x+(a+b)}

-- The still open exact positive-set bound above dimension five.
def H4 : Prop :=
  ∀ (d : ℕ), 6 ≤ d → ∀ P : Finset ℤ, (∀ x ∈ P, 0 < x) →
    (∀ D ⊆ P, D.card = d + 1 → ¬ AddDissociated (D : Set ℤ)) → P.card < 2 ^ d

section

private theorem subset_sum_congr {F T : Finset ℤ} (hT : T ⊆ F) {q r : ℤ}
    (hF : ∀ x ∈ F, x ≡ r [ZMOD q]) : T.sum id ≡ (T.card : ℤ) * r [ZMOD q] := by
  simpa using (Int.ModEq.sum (s := T) (f := id) (g := fun _ ↦ r)
    (fun x hx ↦ hF x (hT hx)))

private theorem cancel_odd_pow {r x y : ℤ} (hr : r % 2 = 1) (k : ℕ)
    (h : x*r ≡ y*r [ZMOD (2 : ℤ)^k]) : x ≡ y [ZMOD (2 : ℤ)^k] := by
  have hnd : ¬ (2 : ℕ) ∣ r.natAbs := by
    intro h'
    have hh : (2 : ℤ) ∣ r := Int.natAbs_dvd_natAbs.mp (by simpa using h')
    rw [Int.dvd_iff_emod_eq_zero] at hh
    omega
  have hg : ((2 : ℤ)^k).gcd r = 1 := by
    rw [Int.gcd, Int.natAbs_pow]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnd |>.pow_left k
  have h' := Int.ModEq.cancel_right_div_gcd (by positivity) h
  simpa [hg] using h'

private theorem aff_to_diss {F : Finset ℤ} (hc : F.card ≤ 6) (ha : (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S) F)
    {r : ℤ} (hr : r % 2 = 1) (hF : ∀ x ∈ F, x ≡ r [ZMOD 8]) :
    AddDissociated (F : Set ℤ) := by
  by_contra h
  obtain ⟨T,S,hT,hS,hd,hne,hs⟩ := not_addDissociated_iff_exists_disjoint.mp h
  have hT' := Finset.coe_subset.mp hT
  have hS' := Finset.coe_subset.mp hS
  have hTcard := card_le_card hT'
  have hScard := card_le_card hS'
  have hmod := (subset_sum_congr hT' hF).symm.trans (hs ▸ subset_sum_congr hS' hF)
  have hcard : T.card = S.card := by
    have hmod' := cancel_odd_pow hr 3 (by exact hmod)
    change ((T.card : ℤ) % 8) = ((S.card : ℤ) % 8) at hmod'
    omega
  exact hne (ha T hT' S hS' hd hcard hs)

private theorem mod_rep {D : Finset ℤ} {b : ℤ} (_hb : b ∉ D)
    (hd : AddDissociated (D : Set ℤ)) (hbad : ¬ AddDissociated (↑(insert b D) : Set ℤ)) :
    ∃ T ⊆ D, ∃ S ⊆ D, Disjoint T S ∧ b = T.sum id - S.sum id := by
  obtain ⟨U,V,hU,hV,hdisj,hne,heq⟩ := not_addDissociated_iff_exists_disjoint.mp hbad
  have finish {X Y : Finset ℤ} (hX : X ⊆ insert b D) (hY : Y ⊆ insert b D)
      (hXY : Disjoint X Y) (hbX : b ∈ X) (hEq : X.sum id = Y.sum id) :
      ∃ T ⊆ D, ∃ S ⊆ D, Disjoint T S ∧ b = T.sum id - S.sum id := by
    have hbY : b ∉ Y := fun hbY ↦ (Finset.disjoint_left.mp hXY hbX hbY)
    have hY' : Y ⊆ D := fun x hx ↦ (mem_insert.mp (hY hx)).resolve_left
      (fun h ↦ hbY (h ▸ hx))
    have hX' : X.erase b ⊆ D := fun x hx ↦ (mem_insert.mp (hX (mem_erase.mp hx).2)).resolve_left
      (mem_erase.mp hx).1
    have hs := Finset.sum_erase_add X id hbX
    exact ⟨Y,hY',X.erase b,hX',hXY.symm.mono_right (erase_subset _ _),by
      change (X.erase b).sum id + b = X.sum id at hs
      rw [← hEq]
      exact eq_sub_of_add_eq (by simpa [add_comm] using hs)⟩
  by_cases hbU : b ∈ U
  · exact finish (coe_subset.mp hU) (coe_subset.mp hV) hdisj hbU heq
  by_cases hbV : b ∈ V
  · exact finish (coe_subset.mp hV) (coe_subset.mp hU) hdisj.symm hbV heq.symm
  have hU' : U ⊆ D := fun x hx ↦ (mem_insert.mp (hU hx : x ∈ insert b D)).resolve_left
    (fun h ↦ hbU (h ▸ hx))
  have hV' : V ⊆ D := fun x hx ↦ (mem_insert.mp (hV hx : x ∈ insert b D)).resolve_left
    (fun h ↦ hbV (h ▸ hx))
  exact (hne (hd (coe_subset.mpr hU') (coe_subset.mpr hV') heq)).elim

private theorem split_sum_congr {F T : Finset ℤ} {a q r : ℤ} (_ha : a ∉ F)
    (hT : T ⊆ insert a F) (hF : ∀ x ∈ F, x ≡ r [ZMOD 2*q])
    (hA : a ≡ r+q [ZMOD 2*q]) :
    T.sum id ≡ (T.card : ℤ)*r + (if a ∈ T then q else 0) [ZMOD 2*q] := by
  have hSub : T.erase a ⊆ F := fun x hx ↦ (mem_insert.mp (hT (mem_erase.mp hx).2)).resolve_left
    (mem_erase.mp hx).1
  by_cases hm : a ∈ T
  · have hcard : (T.card : ℤ) = ((T.erase a).card : ℤ) + 1 := by
      have hh := card_erase_of_mem hm
      have hpos := card_pos.mpr ⟨a,hm⟩
      omega
    have hh := (subset_sum_congr hSub hF).add hA
    have hs := sum_erase_add T id hm
    rw [if_pos hm, hcard]
    convert hh using 1 <;> simp_all only [id_eq] <;> ring
  · rw [if_neg hm, add_zero]
    exact subset_sum_congr (by simpa [erase_eq_of_notMem hm] using hSub) hF

private theorem aff_insert_of_split {F : Finset ℤ} {a q r : ℤ}
    (hq : 0 < q) (hF : ∀ x ∈ F, x ≡ r [ZMOD 2*q])
    (hA : a ≡ r+q [ZMOD 2*q]) (haff : (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S) F) : a ∉ F ∧ (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S) (insert a F) := by
  have hne : a ∉ F := by
    intro hm
    have hc := Int.ModEq.add_left_cancel' r (show r+0 ≡ r+q [ZMOD 2*q] from by
      simpa using (hF a hm).symm.trans hA)
    unfold Int.ModEq at hc
    have hp : q < 2*q := by omega
    rw [Int.zero_emod, Int.emod_eq_of_lt hq.le hp] at hc
    omega
  refine ⟨hne, ?_⟩
  intro T hT S hS hdisj hc hsum
  have hmod := (split_sum_congr hne hT hF hA).symm.trans
    (hsum ▸ split_sum_congr hne hS hF hA)
  rw [hc] at hmod
  have hmod := Int.ModEq.add_left_cancel' _ hmod
  have hqmod : q % (2*q) = q := Int.emod_eq_of_lt hq.le (by omega)
  have hTb : a ∉ T := by
    intro hm
    have hn : a ∉ S := fun h ↦ Finset.disjoint_left.mp hdisj hm h
    rw [if_pos hm, if_neg hn] at hmod
    unfold Int.ModEq at hmod
    simp [hqmod] at hmod
    omega
  have hSb : a ∉ S := by
    intro hm
    rw [if_neg hTb, if_pos hm] at hmod
    unfold Int.ModEq at hmod
    simp [hqmod] at hmod
    omega
  exact haff T (fun x hx ↦ (mem_insert.mp (hT hx)).resolve_left (fun h ↦ hTb (h ▸ hx)))
    S (fun x hx ↦ (mem_insert.mp (hS hx)).resolve_left (fun h ↦ hSb (h ▸ hx))) hdisj hc hsum

private theorem five_rep {P D : Finset ℤ} {b : ℤ} (hD : D ⊆ P) (hcard : D.card = 5)
    (hdiss : AddDissociated (D : Set ℤ)) (hbP : b ∈ P) (hbD : b ∉ D)
    (hbad : ∀ S ⊆ P, S.card = 6 → ¬ AddDissociated (S : Set ℤ)) :
    ∃ T ⊆ D, ∃ S ⊆ D, Disjoint T S ∧ b = T.sum id - S.sum id :=
  mod_rep hbD hdiss (hbad (insert b D) (insert_subset hbP hD) (by rw [card_insert_of_notMem hbD, hcard]))

private theorem rep_size {D T S : Finset ℤ} (hT : T ⊆ D) (hS : S ⊆ D)
    (hdisj : Disjoint T S) : T.card + S.card ≤ D.card := by
  rw [← card_union_of_disjoint hdisj]
  exact card_le_card (union_subset hT hS)

private theorem rep_degree {D T S : Finset ℤ} {b r : ℤ} (hc : D.card = 5)
    (hr : r % 2 = 1) (hD : ∀ x ∈ D, x ≡ r [ZMOD 8]) (hb : b ≡ 3*r [ZMOD 8])
    (hT : T ⊆ D) (hS : S ⊆ D) (hTS : Disjoint T S) (he : b = T.sum id - S.sum id) :
    ((T.card : ℤ) - S.card = 3) ∨ ((T.card : ℤ) - S.card = -5) := by
  have hsz := rep_size hT hS hTS
  have hcalc : b ≡ ((T.card : ℤ) - S.card)*r [ZMOD 8] := by
    rw [he, sub_mul]
    exact (subset_sum_congr hT hD).sub (subset_sum_congr hS hD)
  have h := cancel_odd_pow hr 3 (hcalc.symm.trans hb)
  change ((T.card : ℤ) - S.card) % 8 = 3 % 8 at h
  omega

private theorem neg_five_eval {D T S : Finset ℤ} {b : ℤ} (hc : D.card = 5)
    (hT : T ⊆ D) (hS : S ⊆ D) (hTS : Disjoint T S) (he : b = T.sum id - S.sum id)
    (hd : (T.card : ℤ) - S.card = -5) : b = -D.sum id := by
  have hsz := rep_size hT hS hTS
  have ht : T.card = 0 := by omega
  have hs : D.card ≤ S.card := by omega
  rw [card_eq_zero.mp ht, eq_of_subset_of_card_le hS hs] at he
  simpa using he

private theorem neg_five_fiber {P D : Finset ℤ} {b r : ℤ} (hD : D ⊆ P) (hc : D.card = 5)
    (haff : (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S) D) (hD16 : ∀ x ∈ D, x ≡ r [ZMOD 16]) (hr : r % 2 = 1)
    (hbP : b ∈ P) (hb16 : b ≡ 3*r+8 [ZMOD 16])
    (hbad : ∀ S ⊆ P, S.card = 6 → ¬ AddDissociated (S : Set ℤ)) : b = -D.sum id := by
  have hD8 : ∀ x ∈ D, x ≡ r [ZMOD 8] := fun x hx ↦ (hD16 x hx).of_dvd (by decide)
  have hb8 : b ≡ 3*r [ZMOD 8] := by
    have hh := hb16.of_dvd (m := (8 : ℤ)) (by decide)
    unfold Int.ModEq at *; omega
  have hbD : b ∉ D := by
    intro hbD
    have h := cancel_odd_pow hr 3 (show 1*r ≡ 3*r [ZMOD 2^3] from by simpa using (hD8 b hbD).symm.trans hb8)
    contradiction
  obtain ⟨T,hT,S,hS,hd,he⟩ := five_rep hD hc (aff_to_diss (by omega) haff hr hD8) hbP hbD hbad
  rcases rep_degree hc hr hD8 hb8 hT hS hd he with hs | hs
  · have hcalc := (subset_sum_congr hT hD16).sub (subset_sum_congr hS hD16)
    rw [← he, ← sub_mul, hs] at hcalc
    have hh := hcalc.symm.trans hb16
    unfold Int.ModEq at hh
    omega
  · exact neg_five_eval hc hT hS hd he hs

private theorem mixed_five {P F : Finset ℤ} {a b r q : ℤ} (hq : 0 < q) (hq8 : 8 ∣ q)
    (hFP : F ⊆ P) (hc : F.card = 4) (haff : (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S) F)
    (hF : ∀ x ∈ F, x ≡ r [ZMOD 2*q]) (hA : a ≡ r+q [ZMOD 2*q])
    (haP : a ∈ P) (hbP : b ∈ P) (hb8 : b ≡ 3*r [ZMOD 8]) (hr : r % 2 = 1)
    (hbad : ∀ S ⊆ P, S.card = 6 → ¬ AddDissociated (S : Set ℤ)) :
    ∃ T ⊆ insert a F, ∃ S ⊆ insert a F, Disjoint T S ∧ b = T.sum id - S.sum id ∧
      ((T.card : ℤ) - S.card = 3 ∨ (T.card : ℤ) - S.card = -5) := by
  obtain ⟨hna,haffD⟩ := aff_insert_of_split hq hF hA haff
  have hmod8 : 8 ∣ 2*q := dvd_mul_of_dvd_right hq8 2
  have hD8 : ∀ x ∈ insert a F, x ≡ r [ZMOD 8] := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · have h := hA.of_dvd hmod8
      have hh := Int.dvd_iff_emod_eq_zero.mp hq8
      unfold Int.ModEq at *; omega
    · exact (hF x hx).of_dvd hmod8
  have hbD : b ∉ insert a F := by
    intro hbD
    have h := cancel_odd_pow hr 3 (show 1*r ≡ 3*r [ZMOD 2^3] from by simpa using (hD8 b hbD).symm.trans hb8)
    contradiction
  have hDcard : (insert a F).card = 5 := by rw [card_insert_of_notMem hna, hc]
  obtain ⟨T,hT,S,hS,hTS,he⟩ := five_rep (insert_subset haP hFP) hDcard
    (aff_to_diss (by omega) haffD hr hD8) hbP hbD hbad
  exact ⟨T,hT,S,hS,hTS,he,rep_degree hDcard hr hD8 hb8 hT hS hTS he⟩

private theorem mixed_aligned {F T S : Finset ℤ} {a b r q : ℤ} (hq : 0 < q)
    (hc : F.card = 4) (hna : a ∉ F) (hF : ∀ x ∈ F, x ≡ r [ZMOD 2*q])
    (hA : a ≡ r+q [ZMOD 2*q]) (hb : b ≡ 3*r [ZMOD 2*q])
    (hT : T ⊆ insert a F) (hS : S ⊆ insert a F) (hTS : Disjoint T S)
    (he : b = T.sum id - S.sum id) (hg : (T.card : ℤ) - S.card = 3) : b ∈ (fun (M : Finset ℤ) ↦ (M.powersetCard 3).image (fun S ↦ S.sum id)) F := by
  have hh := (split_sum_congr hna hT hF hA).sub (split_sum_congr hna hS hF hA)
  rw [← he] at hh
  have hh' : b ≡ 3*r + ((if a ∈ T then q else 0) - (if a ∈ S then q else 0)) [ZMOD 2*q] := by
    convert hh using 1
    rw [← hg]
    ring
  have hz := Int.ModEq.add_left_cancel' (3*r) (show 3*r+0 ≡ _ [ZMOD 2*q] from by
    simpa using hb.symm.trans hh')
  have hqmod : q % (2*q) = q := Int.emod_eq_of_lt hq.le (by omega)
  have hneg : (-q) % (2*q) = q := by
    rw [show -q = q - (2*q) by ring, Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod, hqmod]
  have hTa : a ∉ T := by
    intro h
    have hn : a ∉ S := fun h' ↦ disjoint_left.mp hTS h h'
    rw [if_pos h, if_neg hn, sub_zero] at hz
    unfold Int.ModEq at hz
    rw [Int.zero_emod, hqmod] at hz
    omega
  have hSa : a ∉ S := by
    intro h
    rw [if_neg hTa, if_pos h, zero_sub] at hz
    unfold Int.ModEq at hz
    rw [Int.zero_emod, hneg] at hz
    omega
  have hT' : T ⊆ F := fun x hx ↦ (mem_insert.mp (hT hx)).resolve_left (fun h ↦ hTa (h ▸ hx))
  have hS' : S ⊆ F := fun x hx ↦ (mem_insert.mp (hS hx)).resolve_left (fun h ↦ hSa (h ▸ hx))
  have hsize := rep_size hT' hS' hTS
  have hS0 : S = ∅ := card_eq_zero.mp (by omega)
  have hTc : T.card = 3 := by simp only [hS0, card_empty, Nat.cast_zero, sub_zero] at hg; omega
  refine mem_image.mpr ⟨T, mem_powersetCard.mpr ⟨hT', hTc⟩, ?_⟩
  simpa [hS0] using he.symm

private theorem mixed_aligned_eight {P F : Finset ℤ} {a b r : ℤ}
    (hFP : F ⊆ P) (hc : F.card = 4) (haff : (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S) F)
    (hF : ∀ x ∈ F, x ≡ r [ZMOD 16]) (hA : a ≡ r+8 [ZMOD 16])
    (haP : a ∈ P) (hbP : b ∈ P) (hb : b ≡ 3*r [ZMOD 16]) (hr : r % 2 = 1)
    (hbad : ∀ S ⊆ P, S.card = 6 → ¬ AddDissociated (S : Set ℤ)) :
    b ∈ (fun (M : Finset ℤ) ↦ (M.powersetCard 3).image (fun S ↦ S.sum id)) F ∨ b = -F.sum id - a := by
  have hna : a ∉ F := (aff_insert_of_split (q := 8) (by decide) hF hA haff).1
  obtain ⟨T,hT,S,hS,hTS,he,hg⟩ := mixed_five (q := 8) (by decide) (by decide)
    hFP hc haff hF hA haP hbP (hb.of_dvd (by decide)) hr hbad
  rcases hg with h3 | hn
  · exact Or.inl (mixed_aligned (q := 8) (by decide) hc hna hF hA hb hT hS hTS he h3)
  · have h := neg_five_eval (D := insert a F) (by rw [card_insert_of_notMem hna,hc]) hT hS hTS he hn
    exact Or.inr (by simpa [sum_insert hna, neg_add_rev, sub_eq_add_neg, add_comm] using h)

private theorem triple_sums_image {F : Finset ℤ} (hc : F.card = 4) :
    (fun (M : Finset ℤ) ↦ (M.powersetCard 3).image (fun S ↦ S.sum id)) F = F.image (fun x ↦ F.sum id - x) := by
  ext b
  constructor
  · intro hb
    obtain ⟨T,hT,heq⟩ := mem_image.mp hb
    obtain ⟨ht,htc⟩ := mem_powersetCard.mp hT
    have hcard := card_sdiff_add_card_eq_card ht
    obtain ⟨x,hx⟩ := card_eq_one.mp (show (F \ T).card = 1 by omega)
    have hxf : x ∈ F := (mem_sdiff.mp (show x ∈ F \ T by rw [hx]; simp)).1
    have htf : T = F.erase x := by
      ext y
      constructor
      · intro hy
        apply mem_erase.mpr
        refine ⟨?_,ht hy⟩
        rintro rfl
        exact (mem_sdiff.mp (show y ∈ F \ T by rw [hx]; simp)).2 hy
      · intro hy
        by_contra h
        have hm : y ∈ F \ T := mem_sdiff.mpr ⟨(mem_erase.mp hy).2,h⟩
        rw [hx, mem_singleton] at hm
        exact (mem_erase.mp hy).1 hm
    have hs : (F.erase x).sum id + x = F.sum id := sum_erase_add F id hxf
    refine mem_image.mpr ⟨x,hxf,?_⟩
    rw [htf] at heq
    omega
  · intro hb
    obtain ⟨x,hx,heq⟩ := mem_image.mp hb
    have hs : (F.erase x).sum id + x = F.sum id := sum_erase_add F id hx
    refine mem_image.mpr ⟨F.erase x,mem_powersetCard.mpr ⟨erase_subset _ _,?_⟩,?_⟩
    · rw [card_erase_of_mem hx,hc]
    · omega

private theorem triple_sums_card {F : Finset ℤ} (hc : F.card = 4) : ((fun (M : Finset ℤ) ↦ (M.powersetCard 3).image (fun S ↦ S.sum id)) F).card = 4 := by
  rw [triple_sums_image hc, card_image_of_injOn]
  · exact hc
  · intro x _ y _ h; exact sub_right_inj.mp h

private theorem triple_sums_sum {F : Finset ℤ} (hc : F.card = 4) :
    ((fun (M : Finset ℤ) ↦ (M.powersetCard 3).image (fun S ↦ S.sum id)) F).sum id = 3*F.sum id := by
  rw [triple_sums_image hc, sum_image (show Set.InjOn (fun x : ℤ ↦ F.sum id - x) F from
    fun x _ y _ h ↦ sub_right_inj.mp h)]
  change (∑ x ∈ F, (F.sum id - x)) = 3 * F.sum id
  rw [sum_sub_distrib, sum_const, hc]
  norm_num [nsmul_eq_mul]
  ring

private theorem sparse_image {X : Finset ℤ} {v : ℤ} (h : ∀ x ∈ X, x = v) : X.card ≤ 1 := by
  have hsub : X ⊆ {v} := fun x hx ↦ mem_singleton.mpr (h x hx)
  simpa using card_le_card hsub

private theorem off_sparse_of_aff {P F B : Finset ℤ} {r : ℤ}
    (hF : F ⊆ P) (hB : B ⊆ P) (hc : F.card = 5) (haff : (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S) F)
    (hr : r % 2 = 1) (hFr : ∀ x ∈ F, x ≡ r [ZMOD 16])
    (hBr : ∀ b ∈ B, b ≡ 3*r+8 [ZMOD 16])
    (hbad : ∀ S ⊆ P, S.card = 6 → ¬ AddDissociated (S : Set ℤ)) : B.card ≤ 1 :=
  sparse_image (fun b hb ↦ neg_five_fiber hF hc haff hFr hr (hB hb) (hBr b hb) hbad)

private theorem off_bounds (h2 : H2) {P U B : Finset ℤ} {r : ℤ}
    (hU : U ⊆ P) (hB : B ⊆ P) (hUc : 8 ≤ U.card)
    (hr : r % 2 = 1) (hUr : ∀ x ∈ U, x ≡ r [ZMOD 16])
    (hBr : ∀ b ∈ B, b ≡ 3*r+8 [ZMOD 16])
    (hbad : ∀ S ⊆ P, S.card = 6 → ¬ AddDissociated (S : Set ℤ)) :
    B.card ≤ 1 ∧ (9 ≤ U.card → B.card = 0) := by
  obtain ⟨hex,hvar,_⟩ := h2
  obtain ⟨F,hF,hFc,haff⟩ := hex U 5 (Or.inr (Or.inl ⟨rfl,hUc⟩))
  refine ⟨off_sparse_of_aff (hF.trans hU) hB hFc haff hr (fun x hx ↦ hUr x (hF hx)) hBr hbad,?_⟩
  intro hU9
  obtain ⟨D,hD,E,hE,hDc,hEc,hDaff,hEaff,hneq⟩ := hvar U 5 (Or.inr ⟨rfl,hU9⟩)
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hleft := neg_five_fiber (hD.trans hU) hDc hDaff
    (fun x hx ↦ hUr x (hD hx)) hr (hB hb) (hBr b hb) hbad
  have hright := neg_five_fiber (hE.trans hU) hEc hEaff
    (fun x hx ↦ hUr x (hE hx)) hr (hB hb) (hBr b hb) hbad
  exact hneq (by omega)

private theorem aligned_bound (h2 : H2) {P U V B : Finset ℤ} {r : ℤ}
    (hU : U ⊆ P) (hV : V ⊆ P) (hB : B ⊆ P) (hU5 : 5 ≤ U.card) (hVne : V.Nonempty)
    (hr : r % 2 = 1)
    (hUr : ∀ x ∈ U, x ≡ r [ZMOD 16]) (hVr : ∀ x ∈ V, x ≡ r+8 [ZMOD 16])
    (hBr : ∀ b ∈ B, b ≡ 3*r [ZMOD 16])
    (hbad : ∀ S ⊆ P, S.card = 6 → ¬ AddDissociated (S : Set ℤ)) :
    B.card ≤ if 2 ≤ V.card then (if 6 ≤ U.card then 2 else 3) else 4 := by
  obtain ⟨_,hvar,hcommon⟩ := h2
  have hcover {F : Finset ℤ} (hF : F ⊆ U) (hc : F.card = 4) (haff : (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S) F)
      {v : ℤ} (hv : v ∈ V) : B ⊆ insert (-F.sum id-v) ((fun (M : Finset ℤ) ↦ (M.powersetCard 3).image (fun S ↦ S.sum id)) F) := by
    intro b hb
    rcases mixed_aligned_eight (hF.trans hU) hc haff (fun x hx ↦ hUr x (hF hx)) (hVr v hv)
      (hV hv) (hB hb) (hBr b hb) hr hbad with h | h
    · exact mem_insert_of_mem h
    · exact mem_insert.mpr (Or.inl h)
  by_cases hv2 : 2 ≤ V.card
  · rw [if_pos hv2]
    obtain ⟨v,hv,w,hw,hvw⟩ := one_lt_card.mp (show 1 < V.card by omega)
    apply hcommon U B hU5
    intro F hF hc haff b hb
    have h1 := hcover hF hc haff hv hb
    have h2' := hcover hF hc haff hw hb
    by_contra hn
    have h1' := (mem_insert.mp h1).resolve_right hn
    have h2'' := (mem_insert.mp h2').resolve_right hn
    exact hvw (by omega)
  · rw [if_neg hv2]
    obtain ⟨v,hv⟩ := hVne
    obtain ⟨F,hF,G,hG,hFc,hGc,hFaff,hGaff,hne⟩ := hvar U 4 (Or.inl ⟨rfl,hU5⟩)
    have hsum_eq {D : Finset ℤ} (hD : D ⊆ U) (hd : D.card = 4) (ha : (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S) D)
        (hB5 : 5 ≤ B.card) : B.sum id = 2*D.sum id-v := by
      have hsub := hcover hD hd ha hv
      have hcard := triple_sums_card hd
      have hn : -D.sum id-v ∉ (fun (M : Finset ℤ) ↦ (M.powersetCard 3).image (fun S ↦ S.sum id)) D := by
        intro hh
        have hc' := card_le_card hsub
        rw [insert_eq_of_mem hh] at hc'
        omega
      have he := eq_of_subset_of_card_le hsub (by rw [card_insert_of_notMem hn,hcard]; exact hB5)
      rw [he, sum_insert hn, triple_sums_sum hd]
      simp only [id_eq]
      ring
    by_contra hn
    have hFsum := hsum_eq hF hFc hFaff (by omega)
    have hGsum := hsum_eq hG hGc hGaff (by omega)
    exact hne (by omega)

private theorem mixed_card_le_four {P F V B : Finset ℤ} {r : ℤ}
    (hF : F ⊆ P) (hV : V ⊆ P) (hB : B ⊆ P) (hc : F.card = 4) (ha : (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S) F)
    (hr : r % 2 = 1) (hFr : ∀ x ∈ F, x ≡ r [ZMOD 16])
    (hVr : ∀ x ∈ V, x ≡ r+8 [ZMOD 16]) (hBr : ∀ b ∈ B, b ≡ 3*r [ZMOD 16])
    (hbad : ∀ S ⊆ P, S.card = 6 → ¬ AddDissociated (S : Set ℤ))
    (hv : V.Nonempty) : B.card ≤ 5 ∧ (2 ≤ V.card → B.card ≤ 4) := by
  have hc' := triple_sums_card hc
  have hm (v : ℤ) (hv : v ∈ V) (b : ℤ) (hb : b ∈ B) :=
    mixed_aligned_eight hF hc ha hFr (hVr v hv) (hV hv) (hB hb) (hBr b hb) hr hbad
  obtain ⟨v,hv⟩ := hv
  constructor
  · have hsub : B ⊆ insert (-F.sum id-v) ((fun (M : Finset ℤ) ↦ (M.powersetCard 3).image (fun S ↦ S.sum id)) F) := fun b hb ↦
      (hm v hv b hb).elim mem_insert_of_mem (fun h ↦ mem_insert.mpr (Or.inl h))
    have hcard := card_le_card hsub
    have hin := card_insert_le (a := -F.sum id-v) (s := (fun (M : Finset ℤ) ↦ (M.powersetCard 3).image (fun S ↦ S.sum id)) F)
    omega
  · intro hv2
    obtain ⟨a,ha',b,hb',hab⟩ := one_lt_card.mp (show 1 < V.card by omega)
    have hsub : B ⊆ (fun (M : Finset ℤ) ↦ (M.powersetCard 3).image (fun S ↦ S.sum id)) F := by
      intro x hx
      by_contra hn
      have u := (hm a ha' x hx).resolve_left hn
      have v := (hm b hb' x hx).resolve_left hn
      exact hab (by omega)
    have hcard := card_le_card hsub
    omega

private theorem zero_parts {X T S : Finset ℤ} (hc : X.card = 3) (hT : T ⊆ X) (hS : S ⊆ X)
    (hd : Disjoint T S) (hc' : (T.card : ℤ)-S.card = 0) :
    (T = ∅ ∧ S = ∅) ∨ ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ T.sum id - S.sum id = x-y := by
  have hh := rep_size hT hS hd
  by_cases ht : T.card = 0
  · exact Or.inl ⟨card_eq_zero.mp ht, card_eq_zero.mp (by omega)⟩
  · obtain ⟨x,rfl⟩ := card_eq_one.mp (show T.card = 1 by omega)
    obtain ⟨y,rfl⟩ := card_eq_one.mp (show S.card = 1 by simp at hc'; omega)
    refine Or.inr ⟨x,hT (by simp),y,hS (by simp),?_,by simp⟩
    intro h
    subst y
    have hx' : x ∈ ({x} : Finset ℤ) := by simp
    exact Finset.disjoint_left.mp hd hx' hx' 

private theorem three_parts {X T S : Finset ℤ} (hc : X.card = 3) (hT : T ⊆ X) (hS : S ⊆ X)
    (hd : Disjoint T S) (hc' : (T.card : ℤ)-S.card = 3) : T.sum id - S.sum id = X.sum id := by
  have hh := rep_size hT hS hd
  have hs := card_eq_zero.mp (show S.card = 0 by omega)
  have ht := eq_of_subset_of_card_le hT (by omega)
  simp [hs,ht]

private theorem one_parts {X T S : Finset ℤ} (hc : X.card = 3) (hT : T ⊆ X) (hS : S ⊆ X)
    (hd : Disjoint T S) (hc' : (T.card : ℤ)-S.card = 1) :
    ∃ x ∈ X, T.sum id - S.sum id = x ∨ T.sum id - S.sum id = X.sum id - 2*x := by
  have hh := rep_size hT hS hd
  by_cases hs : S.card = 0
  · obtain ⟨x,hx⟩ := card_eq_one.mp (show T.card = 1 by omega)
    refine ⟨x,hT (by simp [hx]),Or.inl ?_⟩
    simp [hx,card_eq_zero.mp hs]
  · obtain ⟨x,hx⟩ := card_eq_one.mp (show S.card = 1 by omega)
    have hu : T ∪ S = X := by
      apply eq_of_subset_of_card_le (union_subset hT hS)
      rw [card_union_of_disjoint hd]
      omega
    have hsU := sum_union (f := id) hd
    rw [hu] at hsU
    refine ⟨x,hS (by simp [hx]),Or.inr ?_⟩
    rw [hx] at hsU ⊢
    simp only [sum_singleton, id_eq] at hsU ⊢
    omega

private theorem split_sum_of_subset {T X Y : Finset ℤ} (h : T ⊆ X∪Y) (hd : Disjoint X Y) :
    T.sum id = (T∩X).sum id + (T∩Y).sum id := by
  have he : (T∩X)∪(T∩Y)=T := by
    ext t
    simp only [mem_union,mem_inter]
    constructor
    · tauto
    · intro ht
      have := mem_union.mp (h ht)
      tauto
  rw [← sum_union (hd.mono inter_subset_right inter_subset_right),he]

private theorem dissociate_two_triples {X Y : Finset ℤ} {r e : ℤ}
    (hr : r % 2 = 1) (he : e = 0 ∨ e = 8) (hx : X.card = 3) (hy : Y.card = 3)
    (hX : ∀ x ∈ X, x ≡ r [ZMOD 16]) (hY : ∀ y ∈ Y, y ≡ 3*r+e [ZMOD 16])
    (hsep : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → |x-x'| ≠ |y-y'|)
    (hdegree : (e = 8 → ∀ x ∈ X, Y.sum id ≠ x ∧ Y.sum id ≠ X.sum id - 2*x) ∧
      (e = 0 → ∀ y ∈ Y, X.sum id ≠ y ∧ X.sum id ≠ Y.sum id - 2*y)) :
    (X ∪ Y).card = 6 ∧ AddDissociated ((X ∪ Y : Finset ℤ) : Set ℤ) := by
  have hXY : Disjoint X Y := by
    apply disjoint_left.mpr
    intro x hx hy
    have hxy := (hX x hx).symm.trans (hY x hy)
    rcases he with rfl | rfl <;> unfold Int.ModEq at hxy <;> omega
  refine ⟨by rw [card_union_of_disjoint hXY,hx,hy],?_⟩
  by_contra hn
  obtain ⟨T,S,hT,hS,hd,hne,hs⟩ := not_addDissociated_iff_exists_disjoint.mp hn
  let Tx := T∩X
  let Ty := T∩Y
  let Sx := S∩X
  let Sy := S∩Y
  have hTx : Tx ⊆ X := inter_subset_right
  have hTy : Ty ⊆ Y := inter_subset_right
  have hSx : Sx ⊆ X := inter_subset_right
  have hSy : Sy ⊆ Y := inter_subset_right
  have hdX : Disjoint Tx Sx := hd.mono inter_subset_left inter_subset_left
  have hdY : Disjoint Ty Sy := hd.mono inter_subset_left inter_subset_left
  have hsumT : T.sum id = Tx.sum id + Ty.sum id := split_sum_of_subset (coe_subset.mp hT) hXY
  have hsumS : S.sum id = Sx.sum id + Sy.sum id := split_sum_of_subset (coe_subset.mp hS) hXY
  have hz : Tx.sum id - Sx.sum id + (Ty.sum id - Sy.sum id) = 0 := by
    change T.sum id = S.sum id at hs
    omega
  let a : ℤ := (Tx.card : ℤ)-Sx.card
  let b : ℤ := (Ty.card : ℤ)-Sy.card
  have hszX := rep_size hTx hSx hdX
  have hszY := rep_size hTy hSy hdY
  have hab : -3 ≤ a ∧ a ≤ 3 ∧ -3 ≤ b ∧ b ≤ 3 := by dsimp [a,b]; omega
  have hmod : 0 ≡ a*r+b*(3*r+e) [ZMOD 16] := by
    have hh := ((subset_sum_congr hTx hX).sub (subset_sum_congr hSx hX)).add
      ((subset_sum_congr hTy hY).sub (subset_sum_congr hSy hY))
    rw [hz] at hh
    dsimp only [a,b]
    convert hh using 1
    ring
  have hemod : e ≡ e*r [ZMOD 16] := by
    rcases he with rfl | rfl
    · simp
    · unfold Int.ModEq; omega
  have hmod' := hmod.trans ((Int.ModEq.refl (a*r)).add
    (((Int.ModEq.refl (3*r)).add hemod).mul_left b))
  have hnorm : 0*r ≡ (a+(3+e)*b)*r [ZMOD (2 : ℤ)^4] := by
    convert hmod' using 1 <;> ring
  have hcnt := cancel_odd_pow hr 4 hnorm
  change 0 % 16 = (a+(3+e)*b) % 16 at hcnt
  by_cases hzero : a = 0 ∧ b = 0
  · have hxx := zero_parts hx hTx hSx hdX hzero.1
    have hyy := zero_parts hy hTy hSy hdY hzero.2
    have hz0 : Tx = ∅ ∧ Sx = ∅ ∧ Ty = ∅ ∧ Sy = ∅ := by
      rcases hxx with ⟨ht0,hs0⟩ | ⟨x,hx',x',hx'',hnx,heqX⟩ <;>
        rcases hyy with ⟨ht1,hs1⟩ | ⟨y,hy',y',hy'',hny,heqY⟩
      · exact ⟨ht0,hs0,ht1,hs1⟩
      · exfalso
        rw [ht0,hs0,heqY] at hz
        simp at hz
        omega
      · exfalso
        rw [ht1,hs1,heqX] at hz
        simp at hz
        omega
      · exfalso
        have hxy : x-x' = -(y-y') := by omega
        exact hsep x hx' x' hx'' hnx y hy' y' hy'' hny (by rw [hxy,abs_neg])
    apply hne
    ext z
    have htempty : z ∉ T := by
      intro hm
      rcases mem_union.mp (hT hm : z ∈ X∪Y) with hX' | hY'
      · have hh : z ∈ Tx := mem_inter.mpr ⟨hm,hX'⟩
        simp [hz0.1] at hh
      · have hh : z ∈ Ty := mem_inter.mpr ⟨hm,hY'⟩
        simp [hz0.2.2.1] at hh
    have hsempty : z ∉ S := by
      intro hm
      rcases mem_union.mp (hS hm : z ∈ X∪Y) with hX' | hY'
      · have hh : z ∈ Sx := mem_inter.mpr ⟨hm,hX'⟩
        simp [hz0.2.1] at hh
      · have hh : z ∈ Sy := mem_inter.mpr ⟨hm,hY'⟩
        simp [hz0.2.2.2] at hh
    simp [htempty,hsempty]
  · rcases he with rfl | rfl
    · have classify (m n : ℤ) (hb : -3 ≤ m ∧ m ≤ 3 ∧ -3 ≤ n ∧ n ≤ 3)
          (hm : (m+3*n)%16 = 0) (hz : ¬ (m=0 ∧ n=0)) :
          (m=3 ∧ n = -1) ∨ (m = -3 ∧ n=1) := by
        obtain ⟨hmlo,hmhi,hnlo,hnhi⟩ := hb
        obtain ⟨j,hj⟩ := Int.dvd_iff_emod_eq_zero.mpr hm
        interval_cases n <;> omega
      have hcases := classify a b hab (by simpa using hcnt.symm) hzero
      rcases hcases with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · have hxsum := three_parts hx hTx hSx hdX ha
        obtain ⟨y,hy',hh⟩ := one_parts hy hSy hTy hdY.symm (by change (Ty.card : ℤ)-Sy.card = -1 at hb; omega)
        rcases hh with hh | hh
        · exact (hdegree.2 rfl y hy').1 (by omega)
        · exact (hdegree.2 rfl y hy').2 (by omega)
      · have hxsum := three_parts hx hSx hTx hdX.symm (by change (Tx.card : ℤ)-Sx.card = -3 at ha; omega)
        obtain ⟨y,hy',hh⟩ := one_parts hy hTy hSy hdY hb
        rcases hh with hh | hh
        · exact (hdegree.2 rfl y hy').1 (by omega)
        · exact (hdegree.2 rfl y hy').2 (by omega)
    · have classify (m n : ℤ) (hb : -3 ≤ m ∧ m ≤ 3 ∧ -3 ≤ n ∧ n ≤ 3)
          (hm : (m+11*n)%16 = 0) (hz : ¬ (m=0 ∧ n=0)) :
          (n=3 ∧ m = -1) ∨ (n = -3 ∧ m=1) := by
        obtain ⟨hmlo,hmhi,hnlo,hnhi⟩ := hb
        obtain ⟨j,hj⟩ := Int.dvd_iff_emod_eq_zero.mpr hm
        interval_cases n <;> omega
      have hcases := classify a b hab (by simpa using hcnt.symm) hzero
      rcases hcases with ⟨hb,ha⟩ | ⟨hb,ha⟩
      · have hysum := three_parts hy hTy hSy hdY hb
        obtain ⟨x,hx',hh⟩ := one_parts hx hSx hTx hdX.symm (by change (Tx.card : ℤ)-Sx.card = -1 at ha; omega)
        rcases hh with hh | hh
        · exact (hdegree.1 rfl x hx').1 (by omega)
        · exact (hdegree.1 rfl x hx').2 (by omega)
      · have hysum := three_parts hy hSy hTy hdY.symm (by change (Ty.card : ℤ)-Sy.card = -3 at hb; omega)
        obtain ⟨x,hx',hh⟩ := one_parts hx hTx hSx hdX ha
        rcases hh with hh | hh
        · exact (hdegree.1 rfl x hx').1 (by omega)
        · exact (hdegree.1 rfl x hx').2 (by omega)

private theorem three_card_sum {x y z : ℤ} (h₁ : x < y) (h₂ : y < z) :
    ({x,y,z} : Finset ℤ).card = 3 ∧ ({x,y,z} : Finset ℤ).sum id = x+y+z := by
  have hxy : x ≠ y := by omega
  have hxz : x ≠ z := by omega
  have hyz : y ≠ z := by omega
  simp [hxy,hxz,hyz,add_assoc]

private theorem three_distances {x y z a b : ℤ} (h₁ : x < y) (h₂ : y < z)
    (ha : a ∈ ({x,y,z} : Finset ℤ)) (hb : b ∈ ({x,y,z} : Finset ℤ)) (hne : a ≠ b) :
    |a-b| = y-x ∨ |a-b| = z-y ∨ |a-b| = z-x := by
  have hxy : |x-y| = y-x := by rw [abs_of_nonpos (by omega)]; ring
  have hyx : |y-x| = y-x := abs_of_nonneg (by omega)
  have hxz : |x-z| = z-x := by rw [abs_of_nonpos (by omega)]; ring
  have hzx : |z-x| = z-x := abs_of_nonneg (by omega)
  have hyz : |y-z| = z-y := by rw [abs_of_nonpos (by omega)]; ring
  have hzy : |z-y| = z-y := abs_of_nonneg (by omega)
  simp only [mem_insert,mem_singleton] at ha hb
  rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl <;> tauto

private theorem hex_triples (x y a b c d : ℤ) (ha : 0 < a) (hab : a < b)
    (hc : 0 < c) (hcd : c < d) :
    ∃ X ⊆ ({x, x-a, x+a, x-b, x+b, x-(a+b), x+(a+b)} : Finset ℤ),
      ∃ Y ⊆ ({y, y-c, y+c, y-d, y+d, y-(c+d), y+(c+d)} : Finset ℤ),
      X.card = 3 ∧ Y.card = 3 ∧
      (∀ u ∈ X, ∀ u' ∈ X, u ≠ u' → ∀ v ∈ Y, ∀ v' ∈ Y, v ≠ v' → |u-u'| ≠ |v-v'|) ∧
      (∀ u ∈ X, Y.sum id ≠ u ∧ Y.sum id ≠ X.sum id-2*u) := by
  have sym_sub (u w p q : ℤ) (hu : u = p ∨ u = q ∨ u = p+q) :
      ({w-u,w,w+u} : Finset ℤ) ⊆ {w,w-p,w+p,w-q,w+q,w-(p+q),w+(p+q)} := by
    rcases hu with rfl|rfl|rfl <;> simp [Finset.insert_subset_iff]
  have sym_data (w u : ℤ) (hu : 0 < u) :
      ({w-u,w,w+u} : Finset ℤ).card = 3 ∧ ({w-u,w,w+u} : Finset ℤ).sum id = 3*w := by
    obtain ⟨h₁,h₂⟩ := three_card_sum (x := w-u) (y := w) (z := w+u) (by omega) (by omega)
    exact ⟨h₁,by omega⟩
  have sym_distance (w u s t : ℤ) (hu : 0 < u) (hs : s ∈ ({w-u,w,w+u} : Finset ℤ))
      (ht : t ∈ ({w-u,w,w+u} : Finset ℤ)) (hne : s ≠ t) : |s-t| = u ∨ |s-t| = 2*u := by
    have h := three_distances (by omega) (by omega) hs ht hne
    omega
  have symY (u : ℤ) (hu : 0 < u) :
      ∃ v, (v = c ∨ v = d ∨ v = c+d) ∧ v ≠ u ∧ 2*v ≠ u ∧ v ≠ 2*u := by
    by_contra! hn
    have classify (v : ℤ) (hv : v = c ∨ v = d ∨ v = c+d) : v = u ∨ 2*v = u ∨ v = 2*u := by
      by_cases h : v = u
      · exact Or.inl h
      by_cases h' : 2*v = u
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (hn v hv h h'))
    have f₁ := classify c (Or.inl rfl)
    have f₂ := classify d (Or.inr (Or.inl rfl))
    have f₃ := classify (c+d) (Or.inr (Or.inr rfl))
    rcases f₁ with h|h|h <;> rcases f₂ with h'|h'|h' <;> rcases f₃ with h''|h''|h'' <;> omega
  by_cases hg : x = 3*y
  · let L := a+b
    let P (v : ℤ) : Prop := v = b ∨ 2*v = b ∨ v = 2*a+b ∨ 2*v = 2*a+b ∨ v = L ∨ v = 2*L
    let Q (v : ℤ) : Prop := v = a ∨ 2*v = a ∨ v = a+2*b ∨ 2*v = a+2*b ∨ v = L ∨ v = 2*L
    have common (v : ℤ) (hp : P v) (hq : Q v) : v = L ∨ v = 2*L ∨ (v = a ∧ b = 2*a) := by
      dsimp [P] at hp
      dsimp [Q] at hq
      dsimp [L] at *
      rcases hp with h|h|h|h|h|h <;> rcases hq with h'|h'|h'|h'|h'|h' <;> omega
    have hex : ∃ v, (v = c ∨ v = d ∨ v = c+d) ∧ (¬ P v ∨ ¬ Q v) := by
      by_contra! hn
      have z₁ := common c (hn c (Or.inl rfl)).1 (hn c (Or.inl rfl)).2
      have z₂ := common d (hn d (Or.inr (Or.inl rfl))).1 (hn d (Or.inr (Or.inl rfl))).2
      have z₃ := common (c+d) (hn (c+d) (Or.inr (Or.inr rfl))).1 (hn (c+d) (Or.inr (Or.inr rfl))).2
      dsimp [L] at *
      rcases z₁ with h|h|h <;> rcases z₂ with h'|h'|h' <;> rcases z₃ with h''|h''|h'' <;> omega
    obtain ⟨v,hv,hV⟩ := hex
    have hvp : 0 < v := by rcases hv with rfl|rfl|rfl <;> omega
    obtain ⟨u,hu,hnu⟩ : ∃ u, (u = a ∨ u = b) ∧
        ¬ (v = L-u ∨ 2*v = L-u ∨ v = L+u ∨ 2*v = L+u ∨ v = L ∨ v = 2*L) := by
      rcases hV with h|h
      · refine ⟨a,Or.inl rfl,?_⟩
        dsimp [P,L] at h ⊢
        exact fun h' ↦ h (by omega)
      · refine ⟨b,Or.inr rfl,?_⟩
        dsimp [Q,L] at h ⊢
        exact fun h' ↦ h (by omega)
    have hup : 0 < u ∧ u < L := by rcases hu with rfl|rfl <;> dsimp [L] <;> omega
    let X : Finset ℤ := {x-L,x+u,x+L}
    let Y : Finset ℤ := {y-v,y,y+v}
    have hXsub : X ⊆ {x, x-a, x+a, x-b, x+b, x-(a+b), x+(a+b)} := by
      rcases hu with rfl|rfl <;> simp [X,L,Finset.insert_subset_iff]
    have hYsub := sym_sub v y c d hv
    obtain ⟨hXcard,hXsum⟩ := three_card_sum (x := x-L) (y := x+u) (z := x+L) (by omega) (by omega)
    obtain ⟨hYcard,hYsum⟩ := sym_data y v hvp
    refine ⟨X,hXsub,Y,hYsub,hXcard,hYcard,?_,?_⟩
    · intro s hs t ht hst s' hs' t' ht' hst' he
      have h₁ := three_distances (by omega) (by omega) hs ht hst
      have h₂ := sym_distance y v s' t' hvp hs' ht' hst'
      exact hnu (by omega)
    · intro s hs
      change X.sum id = _ at hXsum
      change Y.sum id = _ at hYsum
      rw [hXsum,hYsum]
      simp only [X,mem_insert,mem_singleton] at hs
      rcases hs with rfl|rfl|rfl <;> omega
  · have hex : ∃ u, (u = a ∨ u = b ∨ u = a+b) ∧
        ¬ (3*y-x = u ∨ 3*y-x = -u ∨ 3*y-x = 2*u ∨ 3*y-x = -2*u) := by
      by_contra! hn
      have z₁ := hn a (Or.inl rfl)
      have z₂ := hn b (Or.inr (Or.inl rfl))
      have z₃ := hn (a+b) (Or.inr (Or.inr rfl))
      rcases z₁ with h|h|h|h <;> rcases z₂ with h'|h'|h'|h' <;> rcases z₃ with h''|h''|h''|h'' <;> omega
    obtain ⟨u,hu,hn⟩ := hex
    have hup : 0 < u := by rcases hu with rfl|rfl|rfl <;> omega
    obtain ⟨v,hv,hv1,hv2,hv3⟩ := symY u hup
    have hvp : 0 < v := by rcases hv with rfl|rfl|rfl <;> omega
    let X : Finset ℤ := {x-u,x,x+u}
    let Y : Finset ℤ := {y-v,y,y+v}
    obtain ⟨hXcard,hXsum⟩ := sym_data x u hup
    obtain ⟨hYcard,hYsum⟩ := sym_data y v hvp
    refine ⟨X,sym_sub u x a b hu,Y,sym_sub v y c d hv,hXcard,hYcard,?_,?_⟩
    · intro s hs t ht hst s' hs' t' ht' hst' he
      have h₁ := sym_distance x u s t hup hs ht hst
      have h₂ := sym_distance y v s' t' hvp hs' ht' hst'
      omega
    · intro s hs
      change X.sum id = _ at hXsum
      change Y.sum id = _ at hYsum
      rw [hXsum,hYsum]
      simp only [X,mem_insert,mem_singleton] at hs
      rcases hs with rfl|rfl|rfl <;> omega

private theorem exceptional_pair (h3 : H3) (X Y : Finset ℤ) (r e : ℤ)
    (hr : r % 2 = 1) (he : e = 0 ∨ e = 8) (hx : X.card = 7) (hy : Y.card = 7)
    (hX : ∀ x ∈ X, x ≡ r [ZMOD 16]) (hY : ∀ y ∈ Y, y ≡ 3*r+e [ZMOD 16])
    (hNoX : ∀ F ⊆ X, F.card = 5 → ¬ (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S) F) (hNoY : ∀ F ⊆ Y, F.card = 5 → ¬ (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S) F) :
    ∃ D ⊆ X ∪ Y, D.card = 6 ∧ AddDissociated (D : Set ℤ) := by
  obtain ⟨x,a,b,ha,hab,rfl⟩ := h3 X hx hNoX
  obtain ⟨y,c,d,hc,hcd,rfl⟩ := h3 Y hy hNoY
  rcases he with rfl | rfl
  · obtain ⟨T,hT,S,hS,ht,hs,hsep,hcode⟩ := hex_triples y x c d a b hc hcd ha hab
    have hp := dissociate_two_triples hr (Or.inl rfl) hs ht
      (fun u hu ↦ hX u (hS hu)) (fun v hv ↦ hY v (hT hv))
      (fun u hu v hv hn u' hu' v' hv' hn' he ↦ hsep u' hu' v' hv' hn' u hu v hv hn he.symm)
      ⟨fun he ↦ by omega,fun _ ↦ hcode⟩
    exact ⟨S∪T,union_subset_union hS hT,hp.1,hp.2⟩
  · obtain ⟨S,hS,T,hT,hs,ht,hsep,hcode⟩ := hex_triples x y a b c d ha hab hc hcd
    have hp := dissociate_two_triples hr (Or.inr rfl) hs ht
      (fun u hu ↦ hX u (hS hu)) (fun v hv ↦ hY v (hT hv))
      hsep ⟨fun _ ↦ hcode,fun he ↦ by omega⟩
    exact ⟨S∪T,union_subset_union hS hT,hp.1,hp.2⟩

private theorem split_sixteen_case (h2 : H2) (h3 : H3) {P U V B₀ B₁ : Finset ℤ} {r : ℤ}
    (hU : U ⊆ P) (hV : V ⊆ P) (hB₀ : B₀ ⊆ P) (hB₁ : B₁ ⊆ P)
    (hcount : U.card + V.card + B₀.card + B₁.card = 18)
    (hbig : B₀.card + B₁.card ≤ U.card + V.card) (hcap : U.card + V.card ≤ 13)
    (hle : V.card ≤ U.card) (hv : V.Nonempty) (hr : r % 2 = 1)
    (hUr : ∀ x ∈ U, x ≡ r [ZMOD 16]) (hVr : ∀ x ∈ V, x ≡ r+8 [ZMOD 16])
    (hB₀r : ∀ b ∈ B₀, b ≡ 3*r [ZMOD 16]) (hB₁r : ∀ b ∈ B₁, b ≡ 3*r+8 [ZMOD 16])
    (hbad : ∀ S ⊆ P, S.card = 6 → ¬ AddDissociated (S : Set ℤ)) : False := by
  have hu5 : 5 ≤ U.card := by omega
  have hv1 : 1 ≤ V.card := card_pos.mpr hv
  have hB₀c := aligned_bound h2 hU hV hB₀ hu5 hv hr hUr hVr hB₀r hbad
  by_cases hu8 : 8 ≤ U.card
  · obtain ⟨hb1,hb0⟩ := off_bounds h2 hU hB₁ hu8 hr hUr hB₁r hbad
    by_cases hv2 : 2 ≤ V.card
    · simp [hv2, show 6 ≤ U.card by omega] at hB₀c
      omega
    · simp [hv2] at hB₀c
      by_cases hu9 : 9 ≤ U.card
      · have := hb0 hu9
        omega
      · omega
  by_cases hv5 : 5 ≤ V.card
  · have hswap : ∀ x ∈ U, x ≡ (r+8)+8 [ZMOD 16] := by
      intro x hx
      have h := hUr x hx
      unfold Int.ModEq at *; omega
    have hbshift : ∀ b ∈ B₁, b ≡ 3*(r+8) [ZMOD 16] := by
      intro b hb
      have h := hB₁r b hb
      unfold Int.ModEq at *; omega
    have hbcap := aligned_bound h2 hV hU hB₁ hv5 (card_pos.mp (by omega)) (by omega)
      hVr hswap hbshift hbad
    rw [if_pos (show 2 ≤ U.card by omega)] at hbcap
    rw [if_pos (show 2 ≤ V.card by omega)] at hB₀c
    split at hbcap <;> split at hB₀c <;> omega
  have hv2 : 2 ≤ V.card := by omega
  rw [if_pos hv2] at hB₀c
  have hb15 : 5 ≤ B₁.card := by split at hB₀c <;> omega
  have hvOff : ∀ x ∈ V, x ≡ 3*(3*r+8)+8 [ZMOD 16] := by
    intro x hx
    have h := hVr x hx
    unfold Int.ModEq at *; omega
  have hNoB₁ : ∀ F ⊆ B₁, F.card = 5 → ¬ (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S) F := by
    intro F hF hc ha
    have hh := off_sparse_of_aff (hF.trans hB₁) hV hc ha (by omega)
      (fun x hx ↦ hB₁r x (hF hx)) hvOff hbad
    omega
  obtain ⟨hex,_,_⟩ := h2
  have hb17 : B₁.card ≤ 7 := by
    by_contra hh
    obtain ⟨F,hF,hFc,hFa⟩ := hex B₁ 5 (Or.inr (Or.inl ⟨rfl,by omega⟩))
    exact hNoB₁ F hF hFc hFa
  have hb0empty : B₀.card = 0 := by
    by_contra hnonempty
    obtain ⟨F,hF,hFcard,hFaff⟩ := hex B₁ 4 (Or.inl ⟨rfl,hb15⟩)
    have hBshift : ∀ b ∈ B₀, b ≡ (3*r+8)+8 [ZMOD 16] := by
      intro b hb
      have h := hB₀r b hb
      unfold Int.ModEq at *; omega
    have hUaligned : ∀ u ∈ U, u ≡ 3*(3*r+8) [ZMOD 16] := by
      intro u hu
      have h := hUr u hu
      unfold Int.ModEq at *; omega
    obtain ⟨hule5,hu4⟩ := mixed_card_le_four (hF.trans hB₁) hB₀ hU hFcard hFaff
      (by omega) (fun x hx ↦ hB₁r x (hF hx)) hBshift hUaligned hbad (card_pos.mp (by omega))
    have hb0le1 : B₀.card ≤ 1 := by by_contra h'; have := hu4 (by omega); omega
    omega
  have hu7 : U.card = 7 := by omega
  have hb17' : B₁.card = 7 := by omega
  have hNoU : ∀ F ⊆ U, F.card = 5 → ¬ (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S) F := by
    intro F hF hc ha
    have hs := off_sparse_of_aff (hF.trans hU) hB₁ hc ha hr (fun x hx ↦ hUr x (hF hx)) hB₁r hbad
    omega
  obtain ⟨D,hD,hDc,hDa⟩ := exceptional_pair h3 U B₁ r 8 hr (Or.inr rfl) hu7 hb17' hUr hB₁r hNoU hNoB₁
  exact hbad D (hD.trans (union_subset hU hB₁)) hDc hDa

private theorem mod_two_classes {x r q : ℤ} (h : x ≡ r [ZMOD q]) :
    (x ≡ r [ZMOD 2*q]) ∨ (x ≡ r+q [ZMOD 2*q]) := by
  obtain ⟨k,hk⟩ := h.symm.dvd
  by_cases hk0 : k % 2 = 0
  · left
    refine Int.modEq_iff_dvd.mpr ⟨-(k/2),?_⟩
    have he : k = 2*(k/2) := by omega
    rw [show r-x = -(x-r) by ring,hk]
    nth_rw 1 [he]
    ring
  · right
    refine Int.modEq_iff_dvd.mpr ⟨-(k/2),?_⟩
    have he : k = 2*(k/2)+1 := by omega
    rw [show r+q-x = q-(x-r) by ring,hk]
    nth_rw 1 [he]
    ring

private theorem split_two_classes {A : Finset ℤ} {r q : ℤ} (hA : ∀ x ∈ A, x ≡ r [ZMOD q]) :
    ∃ U ⊆ A, ∃ V ⊆ A, U.card + V.card = A.card ∧
      (∀ x ∈ U, x ≡ r [ZMOD 2*q]) ∧ (∀ x ∈ V, x ≡ r+q [ZMOD 2*q]) ∧
      (∀ x ∈ A, x ∉ U → x ∈ V) ∧ (∀ x ∈ A, (x ≡ r [ZMOD 2*q]) → x ∈ U) := by
  classical
  let U := A.filter fun x ↦ x ≡ r [ZMOD 2*q]
  let V := A.filter fun x ↦ ¬ (x ≡ r [ZMOD 2*q])
  have hu : ∀ x ∈ U, x ≡ r [ZMOD 2*q] := fun x hx ↦ (mem_filter.mp hx).2
  have hv : ∀ x ∈ V, x ≡ r+q [ZMOD 2*q] := by
    intro x hx
    obtain ⟨hxA,hxR⟩ := mem_filter.mp hx
    exact (mod_two_classes (hA x hxA)).resolve_left hxR
  refine ⟨U,filter_subset _ _,V,filter_subset _ _,?_,hu,hv,?_,?_⟩
  · exact Finset.card_filter_add_card_filter_not (s := A) (fun x ↦ x ≡ r [ZMOD 2*q])
  · intro x hx hn
    exact mem_filter.mpr ⟨hx,fun h ↦ hn (mem_filter.mpr ⟨hx,h⟩)⟩
  · intro x hx h
    exact mem_filter.mpr ⟨hx,h⟩

private theorem sorted_split {A : Finset ℤ} {r q : ℤ}
    (hA : ∀ x ∈ A, x ≡ r [ZMOD q]) (hr : ∃ x ∈ A, x ≡ r [ZMOD 2*q])
    (hn : ¬ ∀ x ∈ A, x ≡ r [ZMOD 2*q]) :
    ∃ (s : ℤ) (U V : Finset ℤ), (s = r ∨ s = r+q) ∧ U ⊆ A ∧ V ⊆ A ∧
      U.card + V.card = A.card ∧ V.card ≤ U.card ∧ V.Nonempty ∧
      (∀ x ∈ U, x ≡ s [ZMOD 2*q]) ∧ (∀ x ∈ V, x ≡ s+q [ZMOD 2*q]) := by
  obtain ⟨U,hU,V,hV,hcard,hu,hv,hnot,hin⟩ := split_two_classes hA
  obtain ⟨x,hx,hrx⟩ := hr
  have hu' : U.Nonempty := ⟨x,hin x hx hrx⟩
  push Not at hn
  obtain ⟨y,hy,hny⟩ := hn
  have hv' : V.Nonempty := ⟨y,hnot y hy (fun hh ↦ hny (hu y hh))⟩
  by_cases hle : V.card ≤ U.card
  · exact ⟨r,U,V,Or.inl rfl,hU,hV,hcard,hle,hv',hu,hv⟩
  · refine ⟨r+q,V,U,Or.inr rfl,hV,hU,by omega,by omega,hu',hv,?_⟩
    intro z hz
    apply (hu z hz).trans
    refine Int.modEq_iff_dvd.mpr ⟨1,?_⟩
    ring

private theorem degree_three_only {D T S : Finset ℤ} {b r : ℤ} (hc : D.card = 5)
    (hr : r % 2 = 1) (hD : ∀ x ∈ D, x ≡ r [ZMOD 16]) (hb : b ≡ 3*r [ZMOD 16])
    (hT : T ⊆ D) (hS : S ⊆ D) (hTS : Disjoint T S) (he : b = T.sum id - S.sum id) :
    (T.card : ℤ) - S.card = 3 := by
  have hD8 : ∀ x ∈ D, x ≡ r [ZMOD 8] := fun x hx ↦ (hD x hx).of_dvd (by decide)
  rcases rep_degree hc hr hD8 (hb.of_dvd (by decide)) hT hS hTS he with h | h
  · exact h
  · have hcalc := (subset_sum_congr hT hD).sub (subset_sum_congr hS hD)
    rw [← he, ← sub_mul, h] at hcalc
    have hcontra := hcalc.symm.trans hb
    unfold Int.ModEq at hcontra
    omega

private theorem uniform_deep {P D : Finset ℤ} {b r q : ℤ} (hq16 : 16 ∣ q)
    (hD : D ⊆ P) (hc : D.card = 5) (haff : (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S) D) (hr : r % 2 = 1)
    (hDr : ∀ x ∈ D, x ≡ r [ZMOD 2*q]) (hb : b ≡ 3*r [ZMOD 16]) (hbP : b ∈ P)
    (hbad : ∀ S ⊆ P, S.card = 6 → ¬ AddDissociated (S : Set ℤ)) : b ≡ 3*r [ZMOD 2*q] := by
  have hD16 : ∀ x ∈ D, x ≡ r [ZMOD 16] := fun x hx ↦ (hDr x hx).of_dvd (dvd_mul_of_dvd_right hq16 2)
  have hD8 : ∀ x ∈ D, x ≡ r [ZMOD 8] := fun x hx ↦ (hD16 x hx).of_dvd (by decide)
  have hbD : b ∉ D := by
    intro hh
    have h := cancel_odd_pow hr 3 (show 1*r ≡ 3*r [ZMOD 2^3] from by
      simpa using (hD8 b hh).symm.trans (hb.of_dvd (by decide)))
    contradiction
  obtain ⟨T,hT,S,hS,hTS,he⟩ := five_rep hD hc (aff_to_diss (by omega) haff hr hD8) hbP hbD hbad
  have hd := degree_three_only hc hr hD16 hb hT hS hTS he
  have hh := (subset_sum_congr hT hDr).sub (subset_sum_congr hS hDr)
  rwa [← he, ← sub_mul, hd] at hh

private theorem mixed_deep {P F : Finset ℤ} {a b r q : ℤ} (hq : 0 < q) (hq16 : 16 ∣ q)
    (hFP : F ⊆ P) (hc : F.card = 4) (haff : (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S) F)
    (hF : ∀ x ∈ F, x ≡ r [ZMOD 2*q]) (hA : a ≡ r+q [ZMOD 2*q])
    (haP : a ∈ P) (hbP : b ∈ P) (hb16 : b ≡ 3*r [ZMOD 16]) (hr : r % 2 = 1)
    (hbad : ∀ S ⊆ P, S.card = 6 → ¬ AddDissociated (S : Set ℤ)) :
    (b ≡ 3*r [ZMOD 2*q] → b ∈ (fun (M : Finset ℤ) ↦ (M.powersetCard 3).image (fun S ↦ S.sum id)) F) ∧
    ((b ≡ 3*r [ZMOD 2*q]) ∨ (b ≡ 3*r+q [ZMOD 2*q])) := by
  have hq8 : 8 ∣ q := (show (8 : ℤ) ∣ 16 by decide).trans hq16
  have hna := (aff_insert_of_split hq hF hA haff).1
  obtain ⟨T,hT,S,hS,hTS,he,_⟩ := mixed_five hq hq8 hFP hc haff hF hA haP hbP
    (hb16.of_dvd (by decide)) hr hbad
  have hD16 : ∀ x ∈ insert a F, x ≡ r [ZMOD 16] := by
    intro x hx
    have hd := dvd_mul_of_dvd_right hq16 (2 : ℤ)
    rcases mem_insert.mp hx with rfl | hx
    · have hu := hA.of_dvd hd
      have hz := Int.dvd_iff_emod_eq_zero.mp hq16
      unfold Int.ModEq at *; omega
    · exact (hF x hx).of_dvd hd
  have hCard : (insert a F).card = 5 := by rw [card_insert_of_notMem hna,hc]
  have hdeg := degree_three_only hCard hr hD16 hb16 hT hS hTS he
  refine ⟨fun hb ↦ mixed_aligned hq hc hna hF hA hb hT hS hTS he hdeg,?_⟩
  have hcalc := (split_sum_congr hna hT hF hA).sub (split_sum_congr hna hS hF hA)
  rw [← he] at hcalc
  have calc' : b ≡ 3*r + ((if a ∈ T then q else 0)-(if a ∈ S then q else 0)) [ZMOD 2*q] := by
    convert hcalc using 1
    rw [← hdeg]
    ring
  apply mod_two_classes
  have hc := calc'.of_dvd (show q ∣ 2*q from dvd_mul_left _ _)
  have hz (E : Finset ℤ) : (if a ∈ E then q else 0) ≡ 0 [ZMOD q] := by
    split_ifs <;> simp [Int.ModEq]
  exact hc.trans (by simpa using (Int.ModEq.refl (3*r)).add ((hz T).sub (hz S)))

private theorem deep_case (h2 : H2) (h3 : H3) {P U V B : Finset ℤ} {r q : ℤ}
    (hq : 0 < q) (hq16 : 16 ∣ q) (hr : r % 2 = 1)
    (hU : U ⊆ P) (hV : V ⊆ P) (hB : B ⊆ P)
    (hcount : U.card + V.card + B.card = 18) (hbig : B.card ≤ U.card + V.card) (hcap : U.card + V.card ≤ 13)
    (hle : V.card ≤ U.card) (hv : V.Nonempty)
    (hUr : ∀ x ∈ U, x ≡ r [ZMOD 2*q]) (hVr : ∀ x ∈ V, x ≡ r+q [ZMOD 2*q])
    (hBr : ∀ b ∈ B, b ≡ 3*r [ZMOD 16])
    (hbad : ∀ S ⊆ P, S.card = 6 → ¬ AddDissociated (S : Set ℤ)) : False := by
  obtain ⟨hex,_,hcommon⟩ := h2
  have hUr16 : ∀ x ∈ U, x ≡ r [ZMOD 16] := fun x hx ↦
    (hUr x hx).of_dvd (dvd_mul_of_dvd_right hq16 2)
  have hUoff : ∀ a ∈ U, a ≡ 3*(3*r)+8 [ZMOD 16] := by
    intro a ha
    have h := hUr16 a ha
    unfold Int.ModEq at *; omega
  have hNoB : ∀ D ⊆ B, D.card = 5 → ¬ (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S) D := by
    intro D hD hDc hd
    have hs := off_sparse_of_aff (hD.trans hB) hU hDc hd (by omega)
      (fun x hx ↦ hBr x (hD hx)) hUoff hbad
    omega
  have hb7 : B.card ≤ 7 := by
    by_contra hn
    obtain ⟨D,hD,hDc,hda⟩ := hex B 5 (Or.inr (Or.inl ⟨rfl,by omega⟩))
    exact hNoB D hD hDc hda
  have hu6 : 6 ≤ U.card := by omega
  obtain ⟨v,hv⟩ := hv
  obtain ⟨F,hF,hFc,hfa⟩ := hex U 4 (Or.inl ⟨rfl,by omega⟩)
  have hBq : ∀ b ∈ B, b ≡ 3*r [ZMOD q] := by
    intro b hb
    rcases (mixed_deep hq hq16 (hF.trans hU) hFc hfa (fun x hx ↦ hUr x (hF hx))
      (hVr v hv) (hV hv) (hB hb) (hBr b hb) hr hbad).2 with h | h
    · exact h.of_dvd (dvd_mul_left _ _)
    · have hh := h.of_dvd (show q ∣ 2*q from dvd_mul_left _ _)
      exact hh.trans (Int.modEq_iff_dvd.mpr ⟨-1,by ring⟩)
  obtain ⟨B₀,hB₀,B₁,hB₁,hBcount,hB₀r,hB₁r,_,_⟩ := split_two_classes hBq
  have hb0c : B₀.card ≤ 2 := by
    have hh := hcommon U B₀ (by omega) (by
      intro D hD hDc hda b hb
      exact (mixed_deep hq hq16 (hD.trans hU) hDc hda (fun x hx ↦ hUr x (hD hx))
        (hVr v hv) (hV hv) (hB (hB₀ hb)) (hBr b (hB₀ hb)) hr hbad).1 (hB₀r b hb))
    simpa [hu6] using hh
  have hNoU : ∀ D ⊆ U, D.card = 5 → ¬ (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S) D := by
    intro D hD hDc hda
    have hz : B₁.card = 0 := by
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro b hb
      have hh := uniform_deep hq16 (hD.trans hU) hDc hda hr (fun x hx ↦ hUr x (hD hx))
        (hBr b (hB₁ hb)) (hB (hB₁ hb)) hbad
      have hcontra := Int.ModEq.add_left_cancel' (3*r) (show 3*r+0 ≡ 3*r+q [ZMOD 2*q] from
        by simpa using hh.symm.trans (hB₁r b hb))
      unfold Int.ModEq at hcontra
      rw [Int.zero_emod, Int.emod_eq_of_lt hq.le (by omega)] at hcontra
      omega
    omega
  have hu7 : U.card ≤ 7 := by
    by_contra hn
    obtain ⟨D,hD,hDc,hda⟩ := hex U 5 (Or.inr (Or.inl ⟨rfl,by omega⟩))
    exact hNoU D hD hDc hda
  by_cases hv5 : 5 ≤ V.card
  · have hq0 : q % 16 = 0 := Int.dvd_iff_emod_eq_zero.mp hq16
    have hr' : (r+q) % 2 = 1 := by omega
    have hu' : ∀ x ∈ U, x ≡ (r+q)+q [ZMOD 2*q] := fun x hx ↦
      (hUr x hx).trans (Int.modEq_iff_dvd.mpr ⟨1,by ring⟩)
    have bmod (b : ℤ) (hb : b ∈ B₁) : b ≡ 3*(r+q) [ZMOD 16] := by
      have hh := hBr b (hB₁ hb)
      unfold Int.ModEq at *; omega
    have hb' (b : ℤ) (hb : b ∈ B₁) : b ≡ 3*(r+q) [ZMOD 2*q] :=
      (hB₁r b hb).trans (Int.modEq_iff_dvd.mpr ⟨1,by ring⟩)
    obtain ⟨u,hu⟩ := card_pos.mp (show 0 < U.card by omega)
    have hc' := hcommon V B₁ hv5 (by
      intro D hD hDc hd b hb
      exact (mixed_deep hq hq16 (hD.trans hV) hDc hd (fun x hx ↦ hVr x (hD hx)) (hu' u hu)
        (hU hu) (hB (hB₁ hb)) (bmod b hb) hr' hbad).1 (hb' b hb))
    split at hc' <;> omega
  have hu7' : U.card = 7 := by omega
  have hb7' : B.card = 7 := by omega
  obtain ⟨D,hD,hDc,hd⟩ := exceptional_pair h3 U B r 0 hr (Or.inl rfl) hu7' hb7' hUr16
    (fun x hx ↦ by simpa using hBr x hx) hNoU hNoB
  exact hbad D (hD.trans (union_subset hU hB)) hDc hd

private theorem first_split {A : Finset ℤ} {r : ℤ} (hc : 2 ≤ A.card)
    (h16 : ∀ x ∈ A, x ≡ r [ZMOD 16]) :
    ∃ q : ℤ, 0 < q ∧ 16 ∣ q ∧ (∀ x ∈ A, x ≡ r [ZMOD q]) ∧
      ¬ (∀ x ∈ A, x ≡ r [ZMOD 2*q]) := by
  classical
  obtain ⟨x,hx,hxr⟩ : ∃ x ∈ A, x ≠ r := by
    by_contra! hn
    have hh := sparse_image hn
    omega
  let bad (m : ℕ) : Prop := ¬ (∀ x ∈ A, x ≡ r [ZMOD (2 : ℤ)^(m+4)])
  have he : ∃ m, bad m := by
    refine ⟨(r-x).natAbs,?_⟩
    intro hall
    have hd := (hall x hx).dvd
    have hd' : (2 : ℕ)^((r-x).natAbs+4) ∣ (r-x).natAbs := by
      simpa using Int.natAbs_dvd_natAbs.mpr hd
    have hp : 0 < (r-x).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hxr.symm)
    have hh := Nat.le_of_dvd hp hd'
    have hlt : (r-x).natAbs+4 < 2^((r-x).natAbs+4) := Nat.lt_two_pow_self
    omega
  let m := Nat.find he
  have hm : 0 < m := by
    by_contra hn
    have hm0 : m = 0 := by omega
    have hf : bad m := Nat.find_spec he
    rw [hm0] at hf
    exact hf h16
  refine ⟨(2 : ℤ)^((m-1)+4),by positivity,?_,?_,?_⟩
  · rw [pow_add]
    exact dvd_mul_left 16 _
  · by_contra hh
    exact (Nat.find_min he (show m-1 < m by omega)) hh
  · have hs : 2*(2 : ℤ)^((m-1)+4) = (2 : ℤ)^(m+4) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hs]
    exact Nat.find_spec he

private theorem signed_classes_odd_eighteen (h2 : H2) (h3 : H3) {P A B : Finset ℤ} {r : ℤ}
    (hA : A ⊆ P) (hB : B ⊆ P) (hcount : A.card + B.card = 18) (hbig : B.card ≤ A.card)
    (hr : r % 2 = 1) (ha : ∀ x ∈ A, x ≡ r [ZMOD 8]) (hb : ∀ y ∈ B, y ≡ 3*r [ZMOD 8])
    (hbad : ∀ S ⊆ P, S.card = 6 → ¬ AddDissociated (S : Set ℤ)) : False := by
  have hExt := h2.1
  have ha13 : A.card ≤ 13 := by
    by_contra hn
    obtain ⟨F,hF,hFc,hFa⟩ := hExt A 6 (Or.inr (Or.inr ⟨rfl,by omega⟩))
    exact hbad F (hF.trans hA) hFc (aff_to_diss (by omega) hFa hr (fun x hx ↦ ha x (hF hx)))
  have ha9 : 9 ≤ A.card := by omega
  obtain ⟨a,hamem⟩ := card_pos.mp (show 0 < A.card by omega)
  have ha8 (x : ℤ) (hx : x ∈ A) : x ≡ a [ZMOD 8] := (ha x hx).trans (ha a hamem).symm
  have hb8 (b : ℤ) (hm : b ∈ B) : b ≡ 3*a [ZMOD 8] := (hb b hm).trans ((ha a hamem).mul_left 3).symm
  have haodd : a % 2 = 1 := by
    have hh := ha a hamem
    unfold Int.ModEq at hh
    omega
  by_cases hall : ∀ x ∈ A, x ≡ a [ZMOD 16]
  · obtain ⟨B₀,hB₀,B₁,hB₁,hBc,hBr,hB₁r,_,_⟩ := split_two_classes hb8
    have hbempty := (off_bounds h2 hA (hB₁.trans hB) (by omega) haodd hall hB₁r hbad).2 ha9
    obtain ⟨q,hq,hq16,hAq,hn⟩ := first_split (by omega) hall
    obtain ⟨s,U,V,hs,hU,hV,hcard,hle,hv,hUr,hVr⟩ := sorted_split hAq
      ⟨a,hamem,Int.ModEq.refl _⟩ hn
    have hqmod := Int.dvd_iff_emod_eq_zero.mp hq16
    have hsodd : s % 2 = 1 := by rcases hs with rfl | rfl <;> omega
    have hB' : ∀ b ∈ B₀, b ≡ 3*s [ZMOD 16] := by
      intro b hb
      have hh := hBr b hb
      unfold Int.ModEq at *
      rcases hs with rfl | rfl <;> omega
    exact deep_case h2 h3 hq hq16 hsodd (hU.trans hA) (hV.trans hA) (hB₀.trans hB)
      (by omega) (by omega) (by omega) hle hv hUr hVr hB' hbad
  · obtain ⟨s,U,V,hs,hU,hV,hcard,hle,hv,hUr,hVr⟩ := sorted_split (q := 8) ha8
      ⟨a,hamem,Int.ModEq.refl _⟩ hall
    have hsodd : s % 2 = 1 := by rcases hs with rfl | rfl <;> omega
    have hB8' : ∀ b ∈ B, b ≡ 3*s [ZMOD 8] := by
      intro b hb
      have hh := hb8 b hb
      unfold Int.ModEq at *
      rcases hs with rfl | rfl <;> omega
    obtain ⟨B₀,hB₀,B₁,hB₁,hBc,hB₀r,hB₁r,_,_⟩ := split_two_classes hB8'
    exact split_sixteen_case h2 h3 (hU.trans hA) (hV.trans hA) (hB₀.trans hB) (hB₁.trans hB)
      (by omega) (by omega) (by omega) hle hv hsodd hUr hVr hB₀r hB₁r hbad

private theorem odd_eighteen_normalized (h2 : H2) (h3 : H3) {P : Finset ℤ} (hc : P.card = 18)
    (hp : ∀ x ∈ P, x % 8 = 1 ∨ x % 8 = 3)
    (hbad : ∀ S ⊆ P, S.card = 6 → ¬ AddDissociated (S : Set ℤ)) : False := by
  let A := P.filter fun x ↦ x % 8 = 1
  let B := P.filter fun x ↦ ¬ x % 8 = 1
  have hA : A ⊆ P := filter_subset _ _
  have hB : B ⊆ P := filter_subset _ _
  have hcard : A.card + B.card = 18 := by
    rw [←hc]
    exact card_filter_add_card_filter_not (s := P) (fun x ↦ x % 8 = 1)
  have ha : ∀ x ∈ A, x ≡ 1 [ZMOD 8] := fun x hx ↦ (mem_filter.mp hx).2
  have hb : ∀ x ∈ B, x ≡ 3 [ZMOD 8] := fun x hx ↦ (hp x (hB hx)).resolve_left (mem_filter.mp hx).2
  by_cases hle : B.card ≤ A.card
  · exact signed_classes_odd_eighteen h2 h3 hA hB hcard hle (by decide : (1 : ℤ) % 2 = 1) ha hb hbad
  · exact signed_classes_odd_eighteen h2 h3 hB hA (by omega) (by omega) (by decide : (3 : ℤ) % 2 = 1) hb ha hbad

private theorem lift_subfinset {α β : Type*} [DecidableEq α] [DecidableEq β]
    {A : Finset α} {B : Finset β} {g : α → β} (hB : B ⊆ A.image g) :
    ∃ C ⊆ A, C.image g = B ∧ Set.InjOn g C := by
  classical
  have hex (y : B) : ∃ x ∈ A, g x = y := mem_image.mp (hB y.property)
  choose l hlA hlg using hex
  let C := B.attach.image l
  have hCA : C ⊆ A := fun x hx ↦ by
    obtain ⟨y,_,rfl⟩ := mem_image.mp hx
    exact hlA y
  have hCB : C.image g = B := by
    ext y
    constructor
    · intro hy
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
      obtain ⟨z,_,rfl⟩ := mem_image.mp hx
      rw [hlg]
      exact z.property
    · intro hy
      exact mem_image.mpr ⟨l ⟨y,hy⟩,mem_image.mpr ⟨⟨y,hy⟩,mem_attach _ _,rfl⟩,hlg ⟨y,hy⟩⟩
  refine ⟨C,hCA,hCB,?_⟩
  intro x hx y hy hxy
  obtain ⟨u,_,rfl⟩ := mem_image.mp hx
  obtain ⟨v,_,rfl⟩ := mem_image.mp hy
  rw [hlg,hlg] at hxy
  exact congrArg l (Subtype.ext hxy)

private theorem signed_image_pull {C : Finset ℤ} {g : ℤ → ℤ} (hi : Set.InjOn g C)
    (hg : ∀ x ∈ C, g x = x ∨ g x = -x) (hd : AddDissociated (C.image g : Set ℤ)) :
    AddDissociated (C : Set ℤ) := by
  classical
  by_contra hn
  obtain ⟨T,S,hT,hS,hdisj,hne,hs⟩ := not_addDissociated_iff_exists_disjoint.mp hn
  let pos (x : ℤ) := g x = x
  let W := T.filter pos ∪ S.filter (fun x ↦ ¬ pos x)
  let Z := S.filter pos ∪ T.filter (fun x ↦ ¬ pos x)
  have hT' := coe_subset.mp hT
  have hS' := coe_subset.mp hS
  have hW : W ⊆ C := union_subset ((filter_subset _ _).trans hT') ((filter_subset _ _).trans hS')
  have hZ : Z ⊆ C := union_subset ((filter_subset _ _).trans hS') ((filter_subset _ _).trans hT')
  have hpos {R : Finset ℤ} : (R.filter pos).sum g = (R.filter pos).sum id :=
    sum_congr rfl (fun x hx ↦ (mem_filter.mp hx).2)
  have hneg {R : Finset ℤ} (hR : R ⊆ C) :
      (R.filter (fun x ↦ ¬ pos x)).sum g = -(R.filter (fun x ↦ ¬ pos x)).sum id := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl (fun x hx ↦
      (hg x (hR (mem_filter.mp hx).1)).resolve_left (mem_filter.mp hx).2)
  have hWsum : W.sum g = (T.filter pos).sum id - (S.filter (fun x ↦ ¬ pos x)).sum id := by
    dsimp only [W]
    rw [sum_union (hdisj.mono (filter_subset _ _) (filter_subset _ _)),hpos,hneg hS',sub_eq_add_neg]
  have hZsum : Z.sum g = (S.filter pos).sum id - (T.filter (fun x ↦ ¬ pos x)).sum id := by
    dsimp only [Z]
    rw [sum_union (hdisj.symm.mono (filter_subset _ _) (filter_subset _ _)),hpos,hneg hT',sub_eq_add_neg]
  have hsumT := sum_filter_add_sum_filter_not T pos id
  have hsumS := sum_filter_add_sum_filter_not S pos id
  have he : (W.image g).sum id = (Z.image g).sum id := by
    rw [sum_image (hi.mono (coe_subset.mpr hW)),sum_image (hi.mono (coe_subset.mpr hZ))]
    change W.sum g = Z.sum g
    rw [hWsum,hZsum]
    change T.sum id = S.sum id at hs
    change (T.filter pos).sum id + (T.filter (fun x ↦ ¬ pos x)).sum id = T.sum id at hsumT
    change (S.filter pos).sum id + (S.filter (fun x ↦ ¬ pos x)).sum id = S.sum id at hsumS
    omega
  have he' := hd (coe_subset.mpr (image_subset_image hW)) (coe_subset.mpr (image_subset_image hZ)) he
  have hWZ : W = Z := by
    ext x
    constructor
    · intro hx
      have hx' : g x ∈ Z.image g := he' ▸ mem_image_of_mem g hx
      obtain ⟨y,hy,hyx⟩ := mem_image.mp hx'
      have hh := hi (hZ hy) (hW hx) hyx
      simpa [←hh] using hy
    · intro hx
      have hx' : g x ∈ W.image g := he'.symm ▸ mem_image_of_mem g hx
      obtain ⟨y,hy,hyx⟩ := mem_image.mp hx'
      have hh := hi (hW hy) (hZ hx) hyx
      simpa [←hh] using hy
  apply hne
  ext x
  have hh : x ∈ W ↔ x ∈ Z := by rw [hWZ]
  simp only [W,Z,mem_union,mem_filter] at hh
  by_cases hx : pos x <;> tauto

private theorem odd_eighteen (h2 : H2) (h3 : H3) {P : Finset ℤ} (hc : P.card = 18)
    (hp : ∀ x ∈ P, 0 < x) (ho : ∀ x ∈ P, x % 2 = 1)
    (hbad : ∀ S ⊆ P, S.card = 6 → ¬ AddDissociated (S : Set ℤ)) : False := by
  let g (x : ℤ) := if x % 8 = 1 ∨ x % 8 = 3 then x else -x
  have hg (x : ℤ) : g x = x ∨ g x = -x := by dsimp [g]; split_ifs <;> simp
  have habs (x : ℤ) : |g x| = |x| := (hg x).elim (fun h ↦ by rw [h]) (fun h ↦ by rw [h,abs_neg])
  have hi : Set.InjOn g P := by
    intro x hx y hy he
    have hx' := hp x hx
    have hy' := hp y hy
    have h := congrArg abs he
    simpa [habs, abs_of_pos hx', abs_of_pos hy'] using h
  have hcard : (P.image g).card = 18 := by rw [card_image_of_injOn hi,hc]
  apply odd_eighteen_normalized h2 h3 hcard
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    have hyodd := ho y hy
    dsimp [g]
    split_ifs <;> omega
  · intro D hD hd hdis
    obtain ⟨C,hC,hImg,hI⟩ := lift_subfinset hD
    have hh := card_image_of_injOn hI
    rw [hImg,hd] at hh
    exact hbad C hC hh.symm (signed_image_pull hI (fun x _ ↦ hg x) (hImg ▸ hdis))

private theorem mul_image_addDissociated {D : Finset ℤ} {c : ℤ} (hc : c ≠ 0)
    (hD : AddDissociated (D : Set ℤ)) : AddDissociated (D.image (fun x ↦ c*x) : Set ℤ) := by
  classical
  intro T hT S hS he
  obtain ⟨U,hU,hUi,hUinj⟩ := lift_subfinset (coe_subset.mp hT)
  obtain ⟨V,hV,hVi,hVinj⟩ := lift_subfinset (coe_subset.mp hS)
  change T.sum id = S.sum id at he
  rw [←hUi,←hVi] at he
  change (∑ x ∈ U.image (fun x ↦ c*x), x) = (∑ x ∈ V.image (fun x ↦ c*x), x) at he
  rw [sum_image hUinj,sum_image hVinj,←mul_sum,←mul_sum] at he
  have hh := hD (coe_subset.mpr hU) (coe_subset.mpr hV) (mul_left_cancel₀ hc he)
  rw [hh,hVi] at hUi
  exact hUi.symm

private theorem dimension_five (h1 : H1) (h2 : H2) (h3 : H3) {P : Finset ℤ}
    (hp : ∀ x ∈ P, 0 < x) (hbad : ∀ D ⊆ P, D.card = 6 → ¬ AddDissociated (D : Set ℤ)) :
    P.card < 32 := by
  generalize hs : (P.sum fun x ↦ x.natAbs) = w
  induction w using Nat.strong_induction_on generalizing P with
  | h w ih =>
    let E := P.filter fun x ↦ x % 2 = 0
    let O := P.filter fun x ↦ ¬ (x % 2 = 0)
    by_cases hn : O.Nonempty
    · obtain ⟨a,ha⟩ := hn
      have ha' := (mem_filter.mp ha)
      have haodd : a % 2 = 1 := by omega
      have heven : ∀ D ⊆ E, D.card = 4 + 1 → ¬ AddDissociated (D : Set ℤ) := by
        intro D hD hc hd
        have hD2 : ∀ x ∈ D, x ≡ 0 [ZMOD 2] := fun x hx ↦ (mem_filter.mp (hD hx)).2
        have hna : a ∉ D := fun hm ↦ by have hm' := hD2 a hm; unfold Int.ModEq at hm'; omega
        have hDP : D ⊆ P := hD.trans (filter_subset _ _)
        obtain ⟨T,hT,S,hS,hTS,he⟩ := five_rep hDP hc hd ha'.1 hna hbad
        have hh := (subset_sum_congr hT hD2).sub (subset_sum_congr hS hD2)
        rw [← he] at hh
        unfold Int.ModEq at hh
        simp_all
      have hce := (h1 4 (by decide) E (fun x hx ↦ hp x (mem_filter.mp hx).1) heven).2 rfl
      have hsum := card_filter_add_card_filter_not (s := P) (fun x ↦ x % 2 = 0)
      change E.card + O.card = P.card at hsum
      by_contra hc
      obtain ⟨Q,hQ,hQc⟩ := exists_subset_card_eq (s := O) (show 18 ≤ O.card by omega)
      exact odd_eighteen h2 h3 hQc (fun x hx ↦ hp x (mem_filter.mp (hQ hx)).1)
        (fun x hx ↦ by have hh := (mem_filter.mp (hQ hx)).2; omega)
        (fun D hD ↦ hbad D (hD.trans (hQ.trans (filter_subset _ _))))
    · have heven (x : ℤ) (hx : x ∈ P) : x % 2 = 0 := by
        by_contra hh
        exact hn ⟨x,mem_filter.mpr ⟨hx,hh⟩⟩
      by_cases hP : P.Nonempty
      · let Q := P.image (fun x ↦ x/2)
        have hInj : Set.InjOn (fun x : ℤ ↦ x/2) P := by
          intro x hx y hy hh
          have ex := heven x hx
          have ey := heven y hy
          change x/2 = y/2 at hh
          omega
        have hQc : Q.card = P.card := card_image_of_injOn hInj
        have hQpos : ∀ x ∈ Q, 0 < x := by
          intro x hx
          obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
          have hyp := hp y hy
          have hye := heven y hy
          omega
        have hQbad : ∀ D ⊆ Q, D.card = 6 → ¬AddDissociated (D : Set ℤ) := by
          intro D hD hDc hd
          have hsub : D.image (fun x ↦ 2*x) ⊆ P := by
            intro t ht
            obtain ⟨z,hz,rfl⟩ := mem_image.mp ht
            obtain ⟨u,hu,rfl⟩ := mem_image.mp (hD hz)
            have huu : 2*(u/2) = u := by have h := heven u hu; omega
            simpa [huu] using hu
          have hcard : (D.image (fun x ↦ 2*x)).card = 6 := by
            rw [card_image_of_injOn, hDc]
            intro x _ y _ h
            change (2 : ℤ)*x = 2*y at h
            omega
          exact hbad _ hsub hcard (mul_image_addDissociated (by decide) hd)
        have hsmaller : (Q.sum fun x ↦ x.natAbs) < w := by
          rw [show Q = P.image (fun x ↦ x/2) from rfl, sum_image hInj, ←hs]
          apply sum_lt_sum
          · intro x hx
            apply (Int.natAbs_lt_natAbs_of_nonneg_of_lt (by have h := hp x hx; omega) (by have h := hp x hx; omega)).le
          · obtain ⟨x,hx⟩ := hP
            exact ⟨x,hx,Int.natAbs_lt_natAbs_of_nonneg_of_lt (by have h := hp x hx; omega) (by have h := hp x hx; omega)⟩
        rw [←hQc]
        exact ih _ hsmaller hQpos hQbad rfl
      · simp [not_nonempty_iff_eq_empty.mp hP]

private theorem positive_bound_below_six (h1 : H1) (h2 : H2) (h3 : H3)
    {d : ℕ} (hd : d ≤ 5) (P : Finset ℤ) (hp : ∀ x ∈ P, 0 < x)
    (hnop : ∀ B ⊆ P, B.card = d+1 → ¬ AddDissociated (B : Set ℤ)) : P.card < 2^d := by
  by_cases h4 : d ≤ 4
  · exact (h1 d h4 P hp hnop).1
  · obtain rfl : d = 5 := by omega
    simpa using dimension_five h1 h2 h3 hp hnop

private theorem integer_extraction (A : Finset ℤ) (d : ℕ) (hs : 2 ^ (d+1) ≤ A.card)
    (hbound : ∀ P : Finset ℤ, (∀ x ∈ P, 0 < x) →
      (∀ B ⊆ P, B.card = d+1 → ¬ AddDissociated (B : Set ℤ)) → P.card < 2^d) :
    ∃ B ⊆ A, B.card = d+1 ∧ AddDissociated (B : Set ℤ) := by
  classical
  by_contra! hbad
  let P := (A.erase 0).image abs
  have hp : ∀ x ∈ P, 0 < x := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    exact abs_pos.mpr (mem_erase.mp hy).1
  have hnop : ∀ B ⊆ P, B.card = d+1 → ¬ AddDissociated (B : Set ℤ) := by
    intro B hB hBc hd
    obtain ⟨C,hC,hCp,hCi⟩ := lift_subfinset hB
    have hh := card_image_of_injOn hCi
    rw [hCp,hBc] at hh
    apply hbad C (hC.trans (erase_subset _ _)) hh.symm
    exact signed_image_pull hCi (fun x _ ↦ abs_choice x) (hCp ▸ hd)
  have hPbound := hbound P hp hnop
  have hsub : A ⊆ insert 0 (P ∪ P.image Neg.neg) := by
    intro x hx
    by_cases h0 : x = 0
    · simp [h0]
    have hab : |x| ∈ P := mem_image_of_mem abs (mem_erase.mpr ⟨h0,hx⟩)
    cases abs_choice x with
    | inl h => exact mem_insert_of_mem (mem_union_left _ (h ▸ hab))
    | inr h =>
      apply mem_insert_of_mem (mem_union_right _ (mem_image.mpr ⟨|x|,hab,?_⟩))
      simp [h]
  have h1' := card_le_card hsub
  have h2' := card_insert_le (a := (0 : ℤ)) (s := P ∪ P.image Neg.neg)
  have h3' := card_union_le P (P.image Neg.neg)
  have h4' := card_image_le (s := P) (f := Neg.neg)
  rw [pow_succ] at hs
  omega

-- Integer model adapted from Manuel Lopez's Apache-2.0 formalization for part i.
-- Source: github.com/jmanuellb/erdos-963-lean, commit dc3acbaf7e75fdb442f86444a7d29950c0ed45a0.
-- Copyright Manuel Lopez. Licensed under the Apache License, Version 2.0.
-- The earlier part i port credited KoishiChan for the mathematical argument.
private theorem exists_int_model (A : Finset ℝ) :
    ∃ φ : ℝ → ℤ, Set.InjOn φ A ∧
      ∀ B ⊆ A, AddDissociated ((B.image φ : Finset ℤ) : Set ℤ) →
        AddDissociated (B : Set ℝ) := by
  classical
  set S : Finset ℝ := ((A ×ˢ A).image fun p ↦ p.1 - p.2).filter (· ≠ 0) with hS
  obtain ⟨g, hg⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℚ) (M := ℝ)
    (fun i : S ↦ (i : ℝ)) (fun i ↦ (mem_filter.1 i.2).2)
  have hginj : Set.InjOn g A := by
    intro x hx y hy hxy
    by_contra hne
    have hmem : x - y ∈ S :=
      mem_filter.2 ⟨mem_image.2 ⟨(x, y), mem_product.2 ⟨hx, hy⟩, rfl⟩, sub_ne_zero.2 hne⟩
    apply hg ⟨_, hmem⟩
    simp only [map_sub, hxy, sub_self]
  set N : ℕ := ∏ a ∈ A, (g a).den with hN
  have hint : ∀ a ∈ A, ∃ z : ℤ, (z : ℚ) = N * g a := by
    intro a ha
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun a ↦ (g a).den) ha
    refine ⟨c * (g a).num, ?_⟩
    rw [hN, hc]
    push_cast
    have := Rat.mul_den_eq_num (g a)
    rw [← this]; ring
  set φ : ℝ → ℤ := fun x ↦ ⌊(N : ℚ) * g x⌋ with hφ
  have hφ' : ∀ a ∈ A, (φ a : ℚ) = N * g a := by
    intro a ha
    obtain ⟨z, hz⟩ := hint a ha
    simp only [hφ]
    rw [← hz, Int.floor_intCast]
  have hNpos : (0 : ℚ) < N := by
    have : 0 < N := Finset.prod_pos fun a _ ↦ (g a).den_pos
    exact_mod_cast this
  have hφinj : Set.InjOn φ A := by
    intro x hx y hy hxy
    apply hginj hx hy
    have : (N : ℚ) * g x = N * g y := by rw [← hφ' x hx, ← hφ' y hy, hxy]
    exact mul_left_cancel₀ hNpos.ne' this
  refine ⟨φ, hφinj, ?_⟩
  intro B hB hdiss t ht u hu hsum
  have ht' : t ⊆ B := coe_subset.1 ht
  have hu' : u ⊆ B := coe_subset.1 hu
  have hsumφ : ∀ s : Finset ℝ, s ⊆ B →
      ((∑ y ∈ s.image φ, y : ℤ) : ℚ) = N * g (∑ x ∈ s, x) := by
    intro s hs
    rw [sum_image (fun x hx y hy h ↦ hφinj (hB (hs hx)) (hB (hs hy)) h), Int.cast_sum,
      map_sum, mul_sum]
    exact sum_congr rfl fun x hx ↦ hφ' x (hB (hs hx))
  have heq : ∑ y ∈ t.image φ, y = ∑ y ∈ u.image φ, y := by
    have h1 : ((∑ y ∈ t.image φ, y : ℤ) : ℚ) = ((∑ y ∈ u.image φ, y : ℤ) : ℚ) := by
      rw [hsumφ t ht', hsumφ u hu']
      have : ∑ x ∈ t, x = ∑ x ∈ u, x := hsum
      rw [this]
    exact_mod_cast h1
  have himg : t.image φ = u.image φ :=
    hdiss (coe_subset.2 (image_subset_image ht')) (coe_subset.2 (image_subset_image hu')) heq
  ext x
  constructor
  · intro hx
    have h1 : φ x ∈ u.image φ := himg ▸ mem_image_of_mem φ hx
    obtain ⟨y, hy, hyx⟩ := mem_image.1 h1
    have h2 := hφinj (hB (hu' hy)) (hB (ht' hx)) hyx
    rwa [← h2]
  · intro hx
    have h1 : φ x ∈ t.image φ := himg ▸ mem_image_of_mem φ hx
    obtain ⟨y, hy, hyx⟩ := mem_image.1 h1
    have h2 := hφinj (hB (ht' hy)) (hB (hu' hx)) hyx
    rwa [← h2]


private theorem real_bound_of_positive {n d : ℕ} (hpow : 2 ^ (d+1) ≤ n)
    (hbound : ∀ P : Finset ℤ, (∀ x ∈ P, 0 < x) →
      (∀ B ⊆ P, B.card = d+1 → ¬ AddDissociated (B : Set ℤ)) → P.card < 2^d) :
    d+1 ≤ Erdos963.f n := by
  classical
  apply Erdos963.le_f
  intro A hA
  obtain ⟨φ,hφ,hD⟩ := exists_int_model A
  have hcard : (A.image φ).card = n := (card_image_of_injOn hφ).trans hA
  obtain ⟨D,hDA,hDc,hDa⟩ := integer_extraction (A.image φ) d (hcard ▸ hpow) hbound
  obtain ⟨B,hBA,hBD,hBi⟩ := lift_subfinset hDA
  have hBcard : D.card = B.card := by rw [←hBD,card_image_of_injOn hBi]
  exact ⟨B,hBA,by omega,hD B hBA (hBD ▸ hDa)⟩

/-- The exact floor bound through 127 uses only the finite-dimensional premises. -/
theorem floor_through127 (h1 : H1) (h2 : H2) (h3 : H3) {n : ℕ} (hn : 1 ≤ n)
    (hn' : n ≤ 127) : Nat.log 2 n ≤ Erdos963.f n := by
  by_cases hk : Nat.log 2 n = 0
  · simp [hk]
  let d := Nat.log 2 n - 1
  have hd : d+1 = Nat.log 2 n := by omega
  have hpow : 2 ^ (d+1) ≤ n := hd ▸ Nat.pow_log_le_self 2 (by omega)
  have hd' : d ≤ 5 := by
    by_contra h
    have hh : (2 : ℕ)^7 ≤ 2^(d+1) := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at hh
    omega
  rw [←hd]
  exact real_bound_of_positive hpow (positive_bound_below_six h1 h2 h3 hd')

theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos963.erdos_963.parts.ii := by
  intro h1 h2 h3 h4 n hn
  by_cases hk : Nat.log 2 n = 0
  · simp [hk]
  let d := Nat.log 2 n - 1
  have hd : d+1 = Nat.log 2 n := by omega
  have hpow : 2 ^ (d+1) ≤ n := hd ▸ Nat.pow_log_le_self 2 (by omega)
  rw [←hd]
  by_cases hsmall : d ≤ 5
  · exact real_bound_of_positive hpow (positive_bound_below_six h1 h2 h3 hsmall)
  · exact real_bound_of_positive hpow (h4 d (by omega))

end

end OMA.R_Erdos963_erdos_963_parts_ii_R1
