import OMAReductions.R_Erdos360_erdos_360_R1_H4_R1
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.ZMod.Basic

/-! Proof of Erdos360.erdos_360.R1.H4.R1.H3 via Kneser theorem and Lev (2010) sumset interval theorem. -/

section Kneser

open Finset Classical
open scoped Pointwise

private def addStab {G : Type} [AddCommGroup G] [DecidableEq G] (S : Finset G) : AddSubgroup G where
  carrier := {g : G | g +ᵥ S = S}
  zero_mem' := zero_vadd G S
  add_mem' {a b} ha hb := by
    change (a + b) +ᵥ S = S
    rw [add_vadd, hb, ha]
  neg_mem' {a} ha := by
    change -a +ᵥ S = S
    have h := congrArg ((-a) +ᵥ ·) ha
    simpa [← add_vadd] using h.symm

private lemma mem_addStab_iff {G : Type} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) (g : G) : g ∈ addStab S ↔ g +ᵥ S = S := Iff.rfl

private noncomputable def subFin {G : Type} [AddCommGroup G] [Fintype G] (H : AddSubgroup G) : Finset G :=
  Finset.univ.filter (· ∈ H)

@[simp]
private lemma mem_subFin {G : Type} [AddCommGroup G] [Fintype G] (H : AddSubgroup G) (g : G) :
    g ∈ subFin H ↔ g ∈ H := by
  simp [subFin]

private lemma zero_mem_subFin {G : Type} [AddCommGroup G] [Fintype G] (H : AddSubgroup G) :
    (0 : G) ∈ subFin H := by
  simp [H.zero_mem]

private lemma subFin_nonempty {G : Type} [AddCommGroup G] [Fintype G] (H : AddSubgroup G) :
    (subFin H).Nonempty := ⟨0, zero_mem_subFin H⟩

private lemma vadd_subFin_eq {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) {x : G} (hx : x ∈ H) : x +ᵥ subFin H = subFin H := by
  ext y
  rw [mem_vadd_finset]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [mem_subFin] at hh ⊢
    exact H.add_mem hx hh
  · intro hy
    rw [mem_subFin] at hy
    refine ⟨y - x, ?_, by simp⟩
    rw [mem_subFin]
    exact H.sub_mem hy hx

private lemma vadd_finset_add' {G : Type} [AddCommGroup G] [DecidableEq G]
    (g : G) (A B : Finset G) : g +ᵥ (A + B) = (g +ᵥ A) + B := by
  ext x
  simp only [mem_vadd_finset, mem_add]
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    refine ⟨g +ᵥ a, ⟨a, ha, rfl⟩, b, hb, ?_⟩
    simp only [vadd_eq_add]; abel
  · rintro ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩
    refine ⟨a + b, ⟨a, ha, b, hb, rfl⟩, ?_⟩
    simp only [vadd_eq_add]; abel

private lemma addStab_mono_add_left {G : Type} [AddCommGroup G] [DecidableEq G]
    (A B : Finset G) : addStab B ≤ addStab (A + B) := by
  intro g hg
  rw [mem_addStab_iff] at hg ⊢
  rw [add_comm A B, vadd_finset_add', hg, add_comm]

private lemma addStab_add_subFin {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) (H : AddSubgroup G) : H ≤ addStab (A + subFin H) := by
  intro g hg
  rw [mem_addStab_iff, add_comm A (subFin H), vadd_finset_add', vadd_subFin_eq H hg, add_comm]

private lemma card_of_le_addStab {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {S : Finset G} {H : AddSubgroup G} (hH : H ≤ addStab S) :
    S.card = (S.image (QuotientAddGroup.mk' H)).card * (subFin H).card := by
  let φ := QuotientAddGroup.mk' H
  rw [Finset.card_eq_sum_card_fiberwise (f := φ) (t := S.image φ) (fun x hx ↦ mem_image_of_mem φ hx)]
  have hfib : ∀ y ∈ S.image φ, (S.filter (fun x ↦ φ x = y)).card = (subFin H).card := by
    intro y hy
    obtain ⟨x₀, hx₀, rfl⟩ := mem_image.mp hy
    have heq : S.filter (fun x ↦ φ x = φ x₀) = x₀ +ᵥ subFin H := by
      ext x
      simp only [mem_filter, mem_vadd_finset, mem_subFin]
      constructor
      · rintro ⟨hx, hφ⟩
        have hd : x - x₀ ∈ H := by
          have h1 : (x : G ⧸ H) = (x₀ : G ⧸ H) := hφ
          rwa [QuotientAddGroup.eq_iff_sub_mem] at h1
        exact ⟨x - x₀, hd, by simp⟩
      · rintro ⟨h, hh, rfl⟩
        refine ⟨?_, ?_⟩
        · have hstab : h +ᵥ S = S := hH hh
          rw [← hstab, mem_vadd_finset]
          exact ⟨x₀, hx₀, add_comm h x₀⟩
        · simp [φ, QuotientAddGroup.mk'_apply, hh]
    rw [heq, card_vadd_finset]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]

private lemma image_add_subFin {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) (H : AddSubgroup G) :
    (A + subFin H).image (QuotientAddGroup.mk' H) = A.image (QuotientAddGroup.mk' H) := by
  ext y
  simp only [mem_image, mem_add]
  constructor
  · rintro ⟨z, ⟨a, ha, h, hh, rfl⟩, rfl⟩
    refine ⟨a, ha, ?_⟩
    rw [mem_subFin] at hh
    simp [QuotientAddGroup.mk'_apply, hh]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a + 0, ⟨a, ha, 0, zero_mem_subFin H, rfl⟩, by simp⟩

private lemma card_add_subFin {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) (H : AddSubgroup G) :
    (A + subFin H).card = (A.image (QuotientAddGroup.mk' H)).card * (subFin H).card := by
  rw [card_of_le_addStab (addStab_add_subFin A H), image_add_subFin]

private lemma card_subFin_dvd_of_le {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {H₁ H : AddSubgroup G} (h : H₁ ≤ H) : (subFin H₁).card ∣ (subFin H).card := by
  have h1 : H₁ ≤ addStab (subFin H) := fun g hg ↦ vadd_subFin_eq H (h hg)
  rw [card_of_le_addStab h1]
  exact dvd_mul_left _ _

private lemma card_subFin_dvd_add {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) (H : AddSubgroup G) : (subFin H).card ∣ (A + subFin H).card := by
  rw [card_add_subFin]
  exact dvd_mul_left _ _

private lemma addStab_image_quot {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) : addStab (S.image (QuotientAddGroup.mk' (addStab S))) = ⊥ := by
  let K := addStab S
  let φ := QuotientAddGroup.mk' K
  ext q
  rw [AddSubgroup.mem_bot, mem_addStab_iff]
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk'_surjective K q
  constructor
  · intro hq
    have hg : g ∈ K := by
      rw [mem_addStab_iff]
      ext x
      rw [mem_vadd_finset]
      constructor
      · rintro ⟨s, hs, rfl⟩
        have hmem : φ (g + s) ∈ S.image φ := by
          rw [← hq, mem_vadd_finset]
          exact ⟨φ s, mem_image_of_mem φ hs, by simp [φ]⟩
        obtain ⟨s', hs', hφ⟩ := mem_image.mp hmem
        have hdiff : (g + s) - s' ∈ K := by
          have h1 : φ (g + s) = φ s' := hφ.symm
          rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_iff_sub_mem] at h1
          exact h1
        have hstab : ((g + s) - s') +ᵥ S = S := hdiff
        rw [← hstab, mem_vadd_finset]
        exact ⟨s', hs', by simp⟩
      · intro hx
        have hmem : φ (x - g) ∈ S.image φ := by
          have hx' : φ x ∈ φ g +ᵥ (S.image φ) := by
            change φ x ∈ (QuotientAddGroup.mk' K) g +ᵥ (S.image φ)
            rw [hq]
            exact mem_image_of_mem φ hx
          rw [mem_vadd_finset] at hx'
          obtain ⟨y, hy, hyx⟩ := hx'
          have hy_eq : φ (x - g) = y := by
            have hyx' : φ g + y = φ x := hyx
            rw [map_sub, ← hyx', add_sub_cancel_left]
          exact hy_eq ▸ hy
        obtain ⟨s', hs', hφ⟩ := mem_image.mp hmem
        have hdiff : x - (g + s') ∈ K := by
          have h1 : φ (x - g) = φ s' := hφ.symm
          rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_iff_sub_mem] at h1
          convert h1 using 1; abel
        have hstab : (x - (g + s')) +ᵥ S = S := hdiff
        have hxs : x - g ∈ S := by
          rw [← hstab, mem_vadd_finset]
          exact ⟨s', hs', by change x - (g + s') + s' = x - g; abel⟩
        exact ⟨x - g, hxs, by simp⟩
    exact (QuotientAddGroup.eq_zero_iff g).mpr hg
  · intro h0
    rw [h0, zero_vadd]

private lemma card_addStab_bot {G : Type} [AddCommGroup G] [Fintype G] :
    (subFin (⊥ : AddSubgroup G)).card = 1 := by
  have heq : subFin (⊥ : AddSubgroup G) = ({(0 : G)} : Finset G) := by
    ext x
    rw [mem_subFin, AddSubgroup.mem_bot, mem_singleton]
  rw [heq, card_singleton]

private lemma add_subFin_bot {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] (A : Finset G) :
    A + subFin (⊥ : AddSubgroup G) = A := by
  ext x
  simp only [mem_add, mem_subFin]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    have hz0 : z = (0 : G) := (AddSubgroup.mem_bot (G := G)).mp hz
    subst hz0
    simpa using hy
  · intro hx
    exact ⟨x, hx, (0 : G), (⊥ : AddSubgroup G).zero_mem, add_zero x⟩

private lemma card_coset_diff_le {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {U X : Finset G} {H₁ H : AddSubgroup G} {c : G} (hH₁ : H₁ ≤ H) (hc : c ∈ U)
    (hX_sub : X ⊆ c +ᵥ subFin (G := G) H) (hU_inter : U ∩ (c +ᵥ subFin (G := G) H) ⊆ X) :
    (U + subFin (G := G) H₁).card + (subFin (G := G) H).card ≤
      (U + subFin (G := G) H).card + (X + subFin (G := G) H₁).card := by
  let S_H : Finset G := subFin H
  let S_H1 : Finset G := subFin H₁
  change (U + S_H1).card + S_H.card ≤ (U + S_H).card + (X + S_H1).card
  have hsub_tot : U + S_H1 ⊆ U + S_H :=
    add_subset_add Subset.rfl (fun h hh ↦ (mem_subFin H h).mpr (hH₁ ((mem_subFin H₁ h).mp hh)))
  have hcos_sub : c +ᵥ S_H ⊆ U + S_H := by
    intro y hy
    obtain ⟨h, hh, rfl⟩ := mem_vadd_finset.mp hy
    exact mem_add.mpr ⟨c, hc, h, hh, rfl⟩
  have hXH_sub : X + S_H1 ⊆ c +ᵥ S_H := by
    intro y hy
    obtain ⟨x, hx, h1, hh1, rfl⟩ := mem_add.mp hy
    obtain ⟨h, hh, hx_eq⟩ := mem_vadd_finset.mp (hX_sub hx)
    rw [mem_subFin] at hh hh1
    rw [mem_vadd_finset]
    refine ⟨h + h1, (mem_subFin H _).mpr (H.add_mem hh (hH₁ hh1)), ?_⟩
    simp only [vadd_eq_add] at hx_eq ⊢
    rw [← hx_eq]
    abel
  have hinter_sub : (U + S_H1) ∩ (c +ᵥ S_H) ⊆ X + S_H1 := by
    intro y hy
    rw [mem_inter] at hy
    obtain ⟨u, hu, h1, hh1, hy1⟩ := mem_add.mp hy.1
    obtain ⟨h, hh, hy2⟩ := mem_vadd_finset.mp hy.2
    rw [mem_subFin] at hh hh1
    have hu_cos : u ∈ c +ᵥ S_H := by
      rw [mem_vadd_finset]
      refine ⟨h - h1, (mem_subFin H _).mpr (H.sub_mem hh (hH₁ hh1)), ?_⟩
      simp only [vadd_eq_add] at hy2 ⊢
      have hy1' : u + h1 = y := hy1
      calc c + (h - h1) = (c + h) - h1 := by abel
        _ = (u + h1) - h1 := by rw [hy2, ← hy1']
        _ = u := by abel
    have huX : u ∈ X := hU_inter (mem_inter.mpr ⟨hu, hu_cos⟩)
    exact mem_add.mpr ⟨u, huX, h1, (mem_subFin H₁ h1).mpr hh1, hy1⟩
  have hsdiff : (c +ᵥ S_H) \ (X + S_H1) ⊆ (U + S_H) \ (U + S_H1) := by
    intro y hy
    rw [mem_sdiff] at hy ⊢
    exact ⟨hcos_sub hy.1, fun hyU ↦ hy.2 (hinter_sub (mem_inter.mpr ⟨hyU, hy.1⟩))⟩
  have hcard1 := card_le_card hsdiff
  rw [card_sdiff_of_subset hXH_sub, card_sdiff_of_subset hsub_tot, card_vadd_finset] at hcard1
  have hle1 : (X + S_H1).card ≤ S_H.card := by
    simpa [card_vadd_finset] using card_le_card hXH_sub
  have hle2 : (U + S_H1).card ≤ (U + S_H).card := card_le_card hsub_tot
  omega

private lemma kneser_aux_coset_le {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (U Ai Bi : Finset G) {H : AddSubgroup G}
    (hHi_le : addStab (Ai + Bi) ≤ H)
    (heq1 : (U + subFin H).card + (Ai + subFin (addStab (Ai + Bi))).card +
      (Bi + subFin (addStab (Ai + Bi))).card <
      (U + subFin (addStab (Ai + Bi))).card + (subFin H).card) :
    Ai.card + Bi.card + (subFin (addStab (Ai + Bi))).card ≤ (subFin H).card := by
  have hle_un : (U + subFin (addStab (Ai + Bi))).card ≤ (U + subFin H).card :=
    card_le_card (add_subset_add Subset.rfl fun h hh ↦
      (mem_subFin H h).mpr (hHi_le ((mem_subFin (addStab (Ai + Bi)) h).mp hh)))
  have hlt_sum : (Ai + subFin (addStab (Ai + Bi))).card + (Bi + subFin (addStab (Ai + Bi))).card <
      (subFin H).card := by omega
  obtain ⟨q1, hq1⟩ := card_subFin_dvd_add Ai (addStab (Ai + Bi))
  obtain ⟨q2, hq2⟩ := card_subFin_dvd_add Bi (addStab (Ai + Bi))
  obtain ⟨q3, hq3⟩ := card_subFin_dvd_of_le hHi_le
  have hpos_Hi : 0 < (subFin (addStab (Ai + Bi))).card :=
    card_pos.mpr (subFin_nonempty (addStab (Ai + Bi)))
  have hq_lt : q1 + q2 < q3 := by
    rw [hq1, hq2, hq3] at hlt_sum
    nlinarith
  have hsum_le : (Ai + subFin (addStab (Ai + Bi))).card + (Bi + subFin (addStab (Ai + Bi))).card +
      (subFin (addStab (Ai + Bi))).card ≤ (subFin H).card := by
    rw [hq1, hq2, hq3]
    nlinarith
  have hAi_le : Ai.card ≤ (Ai + subFin (addStab (Ai + Bi))).card :=
    card_le_card fun x hx ↦ mem_add.mpr ⟨x, hx, 0, zero_mem_subFin _, add_zero x⟩
  have hBi_le : Bi.card ≤ (Bi + subFin (addStab (Ai + Bi))).card :=
    card_le_card fun x hx ↦ mem_add.mpr ⟨x, hx, 0, zero_mem_subFin _, add_zero x⟩
  omega

private lemma kneser_aux :
    ∀ N : ℕ, ∀ {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
      (A B : Finset G), A.Nonempty → B.Nonempty → (A + B).card + A.card ≤ N →
      (A + subFin (G := G) (addStab (A + B))).card + (B + subFin (G := G) (addStab (A + B))).card ≤
        (A + B).card + (subFin (G := G) (addStab (A + B))).card := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro G _ _ _ A B hA hB hN
    let K := addStab (A + B)
    by_cases hK : K ≠ ⊥
    · let φ := QuotientAddGroup.mk' K
      let A' := A.image φ
      let B' := B.image φ
      have hA' : A'.Nonempty := hA.image φ
      have hB' : B'.Nonempty := hB.image φ
      have hAB' : A' + B' = (A + B).image φ := by
        ext q
        simp only [A', B', mem_add, mem_image]
        constructor
        · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
          exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, by simp [φ]⟩
        · rintro ⟨z, ⟨a, ha, b, hb, rfl⟩, rfl⟩
          exact ⟨φ a, ⟨a, ha, rfl⟩, φ b, ⟨b, hb, rfl⟩, by simp [φ]⟩
      have hK_ge2 : 2 ≤ (subFin K).card := by
        obtain ⟨g, hg⟩ : ∃ g ∈ K, g ≠ 0 := by
          by_contra h0
          push Not at h0
          apply hK
          ext g
          simp only [AddSubgroup.mem_bot]
          exact ⟨h0 g, fun hg ↦ hg ▸ K.zero_mem⟩
        have hsub : ({(0 : G), g} : Finset G) ⊆ subFin K := by
          intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact zero_mem_subFin K
          · simpa using hg.1
        have h2 : ({0, g} : Finset G).card = 2 := card_pair hg.2.symm
        exact h2 ▸ card_le_card hsub
      have hAB_pos : 0 < (A' + B').card := card_pos.mpr (hAB' ▸ (hA.add hB).image φ)
      have hAB_card : (A + B).card = (A' + B').card * (subFin K).card := by
        rw [hAB']
        exact card_of_le_addStab (le_refl K)
      have hlt : (A' + B').card + A'.card < N := by
        have h1 : (A' + B').card < (A + B).card := by
          rw [hAB_card]
          nlinarith
        have h2 : A'.card ≤ A.card := card_image_le
        omega
      have hK' : addStab (A' + B') = ⊥ := by
        rw [hAB']
        exact addStab_image_quot (A + B)
      have hind := ih ((A' + B').card + A'.card) hlt A' B' hA' hB' le_rfl
      rw [hK', card_addStab_bot, add_subFin_bot, add_subFin_bot] at hind
      rw [card_add_subFin A K, card_add_subFin B K, hAB_card]
      have hmul := Nat.mul_le_mul_right (subFin K).card hind
      nlinarith
    · rw [not_ne_iff] at hK
      have hK_eq : addStab (A + B) = ⊥ := hK
      rw [hK_eq, card_addStab_bot, add_subFin_bot, add_subFin_bot]
      by_cases hA1 : A.card = 1
      · obtain ⟨a, rfl⟩ := card_eq_one.mp hA1
        have hcard : ({a} + B).card = B.card := by
          rw [singleton_add, card_vadd_finset]
        omega
      · have hA2 : 2 ≤ A.card := by have := card_pos.mpr hA; omega
        obtain ⟨a, ha, a', ha', haa'⟩ := one_lt_card.mp hA2
        have hdiff_ne : a' - a ≠ 0 := sub_ne_zero.mpr haa'.symm
        have hnot_stab : a' - a ∉ addStab B := by
          intro hmem
          have hmemK : a' - a ∈ K := addStab_mono_add_left A B hmem
          rw [hK, AddSubgroup.mem_bot] at hmemK
          exact hdiff_ne hmemK
        rw [mem_addStab_iff] at hnot_stab
        have hnot_sub : ¬ ((a' - a) +ᵥ B ⊆ B) := by
          intro hsub
          exact hnot_stab (eq_of_subset_of_card_le hsub (card_vadd_finset _ _).ge)
        rw [Finset.not_subset] at hnot_sub
        obtain ⟨y, hy1, hy2⟩ := hnot_sub
        rw [mem_vadd_finset] at hy1
        obtain ⟨b, hb, rfl⟩ := hy1
        let B0 := (-b + a) +ᵥ B
        have hB0_ne : B0.Nonempty := ⟨(-b + a) +ᵥ b, mem_vadd_finset.mpr ⟨b, hb, rfl⟩⟩
        have hB0_card : B0.card = B.card := card_vadd_finset _ _
        have hAB0_card : (A + B0).card = (A + B).card := by
          rw [show A + B0 = (-b + a) +ᵥ (A + B) from by rw [add_comm A B0, add_comm A B, ← vadd_finset_add']]
          exact card_vadd_finset _ _
        have hAB0_stab : addStab (A + B0) = ⊥ := by
          ext g
          simp only [mem_addStab_iff, AddSubgroup.mem_bot]
          have heq : A + B0 = (-b + a) +ᵥ (A + B) := by
            rw [add_comm A B0, add_comm A B, ← vadd_finset_add']
          rw [heq, vadd_comm]
          constructor
          · intro hg
            have h1 : g +ᵥ (A + B) = A + B := by
              have := congrArg ((-(-b + a)) +ᵥ ·) hg
              rw [← add_vadd, ← add_vadd, neg_add_cancel, zero_add] at this
              rw [← add_vadd, neg_add_cancel, zero_vadd] at this
              exact this
            have hmemK : g ∈ K := h1
            rwa [hK, AddSubgroup.mem_bot] at hmemK
          · intro hg; subst hg; simp
        have ha_B0 : a ∈ A ∩ B0 := by
          rw [mem_inter, mem_vadd_finset]
          exact ⟨ha, ⟨b, hb, by simp only [vadd_eq_add]; abel⟩⟩
        have ha'_B0 : a' ∉ B0 := by
          rw [mem_vadd_finset]
          rintro ⟨b', hb', hbeq⟩
          have heq : b' = (a' - a) +ᵥ b := by
            simp only [vadd_eq_add] at hbeq ⊢
            calc b' = ((-b + a) + b') - (-b + a) := by abel
              _ = a' - (-b + a) := by rw [hbeq]
              _ = (a' - a) + b := by abel
          rw [← heq] at hy2
          exact hy2 hb'
        have hInt_ne : (A ∩ B0).Nonempty := ⟨a, ha_B0⟩
        have hInt_lt : (A ∩ B0).card < A.card :=
          card_lt_card ⟨inter_subset_left, fun hsub ↦ ha'_B0 (mem_inter.mp (hsub ha')).2⟩
        have hUn_ne : (A ∪ B0).Nonempty := hA.mono subset_union_left
        let isConv : Finset G → Prop := fun C ↦
          C ⊆ A + B0 ∧ C.Nonempty ∧
            (A ∩ B0).card + ((A ∪ B0) + subFin (addStab C)).card ≤ C.card + (subFin (addStab C)).card
        let C0 := (A ∩ B0) + (A ∪ B0)
        have hC0_sub : C0 ⊆ A + B0 := by
          intro x hx
          obtain ⟨u, hu, v, hv, rfl⟩ := mem_add.mp hx
          rw [mem_inter] at hu
          rcases mem_union.mp hv with hvA | hvB
          · rw [add_comm u v]
            exact add_mem_add hvA hu.2
          · exact add_mem_add hu.1 hvB
        have hC0_ne : C0.Nonempty := hInt_ne.add hUn_ne
        have hC0_lt : C0.card + (A ∩ B0).card < N := by
          have hc1 : C0.card ≤ (A + B0).card := card_le_card hC0_sub
          omega
        have hC0_ih := ih (C0.card + (A ∩ B0).card) hC0_lt (A ∩ B0) (A ∪ B0) hInt_ne hUn_ne le_rfl
        have hC0_conv : isConv C0 := by
          refine ⟨hC0_sub, hC0_ne, ?_⟩
          have hle : (A ∩ B0).card ≤ (A ∩ B0 + subFin (addStab C0)).card := by
            refine card_le_card (fun x hx ↦ mem_add.mpr ⟨x, hx, 0, zero_mem_subFin _, add_zero x⟩)
          have hC0_ih' : (A ∩ B0 + subFin (addStab C0)).card + ((A ∪ B0) + subFin (addStab C0)).card ≤
              C0.card + (subFin (addStab C0)).card := hC0_ih
          omega
        let convs := (A + B0).powerset.filter isConv
        have hC0_mem : C0 ∈ convs := mem_filter.mpr ⟨mem_powerset.mpr hC0_sub, hC0_conv⟩
        have hconvs_ne : convs.Nonempty := ⟨C0, hC0_mem⟩
        obtain ⟨C, hC_mem, hC_min⟩ := exists_min_image convs (fun X ↦ (subFin (addStab X)).card) hconvs_ne
        obtain ⟨hC_sub, hC_ne, hC_ineq⟩ := (mem_filter.mp hC_mem).2
        let H := addStab C
        by_cases hH : H = ⊥
        · have hH1 : (subFin H).card = 1 := by rw [hH, card_addStab_bot]
          have hUn_id : (A ∪ B0) + subFin H = A ∪ B0 := by
            rw [hH, add_subFin_bot]
          rw [hH1, hUn_id] at hC_ineq
          have hC_le : C.card ≤ (A + B0).card := card_le_card hC_sub
          have hcard_un : (A ∩ B0).card + (A ∪ B0).card = A.card + B0.card := by
            rw [add_comm, card_union_add_card_inter]
          omega
        · exfalso
          have hnot_sub_H : ∃ a1 ∈ A, ∃ b1 ∈ B0, ¬ (a1 + b1) +ᵥ subFin H ⊆ A + B0 := by
            by_contra hall
            push Not at hall
            have hH_le : H ≤ addStab (A + B0) := by
              intro g hg
              rw [mem_addStab_iff]
              refine eq_of_subset_of_card_le (fun x hx ↦ ?_) (card_vadd_finset _ _).ge
              rw [mem_vadd_finset] at hx
              obtain ⟨z, hz, rfl⟩ := hx
              obtain ⟨a1, ha1, b1, hb1, rfl⟩ := mem_add.mp hz
              refine hall a1 ha1 b1 hb1 ?_
              rw [mem_vadd_finset]
              exact ⟨g, by simpa using hg, by simp only [vadd_eq_add]; abel⟩
            rw [hAB0_stab] at hH_le
            exact hH (le_bot_iff.mp hH_le)
          obtain ⟨a1, ha1, b1, hb1, hnot_coset⟩ := hnot_sub_H
          have hcoset_disj : Disjoint ((a1 + b1) +ᵥ subFin H) C := by
            rw [disjoint_left]
            intro x hx1 hx2
            rw [mem_vadd_finset] at hx1
            obtain ⟨h, hh, rfl⟩ := hx1
            rw [mem_subFin] at hh
            apply hnot_coset
            intro y hy
            rw [mem_vadd_finset] at hy
            obtain ⟨h', hh', rfl⟩ := hy
            rw [mem_subFin] at hh'
            have hmemC : (h' - h) +ᵥ ((a1 + b1) +ᵥ h) ∈ C := by
              have hstab : (h' - h) +ᵥ C = C := H.sub_mem hh' hh
              rw [← hstab, mem_vadd_finset]
              exact ⟨(a1 + b1) +ᵥ h, hx2, rfl⟩
            have hEq : (h' - h) +ᵥ ((a1 + b1) +ᵥ h) = (a1 + b1) +ᵥ h' := by
              simp only [vadd_eq_add]; abel
            rw [hEq] at hmemC
            exact hC_sub hmemC
          let A1 := A ∩ (a1 +ᵥ subFin H)
          let A2 := A ∩ (b1 +ᵥ subFin H)
          let B1 := B0 ∩ (b1 +ᵥ subFin H)
          let B2 := B0 ∩ (a1 +ᵥ subFin H)
          have hA1_ne : A1.Nonempty := ⟨a1, mem_inter.mpr ⟨ha1, mem_vadd_finset.mpr ⟨0, zero_mem_subFin H, add_zero a1⟩⟩⟩
          have hB1_ne : B1.Nonempty := ⟨b1, mem_inter.mpr ⟨hb1, mem_vadd_finset.mpr ⟨0, zero_mem_subFin H, add_zero b1⟩⟩⟩
          have hAiBi_prop : ∀ (Ai Bi : Finset G), Ai.Nonempty → Bi.Nonempty → Ai ⊆ A → Bi ⊆ B0 →
              (Ai ⊆ a1 +ᵥ subFin H ∧ Bi ⊆ b1 +ᵥ subFin H ∨ Ai ⊆ b1 +ᵥ subFin H ∧ Bi ⊆ a1 +ᵥ subFin H) →
              Ai + Bi ⊆ (a1 + b1) +ᵥ subFin H ∧
                addStab (Ai + Bi) < H ∧
                (Ai + subFin (addStab (Ai + Bi))).card + (Bi + subFin (addStab (Ai + Bi))).card ≤
                  (Ai + Bi).card + (subFin (addStab (Ai + Bi))).card ∧
                ((A ∪ B0) + subFin H).card + (Ai + subFin (addStab (Ai + Bi))).card +
                  (Bi + subFin (addStab (Ai + Bi))).card <
                  ((A ∪ B0) + subFin (addStab (Ai + Bi))).card + (subFin H).card ∧
                ((A ∪ B0) + subFin H).card + (A ∩ B0).card + Ai.card + Bi.card ≤
                  (A + B0).card + (subFin H).card + (subFin (addStab (Ai + Bi))).card := by
            intro Ai Bi hAi_ne hBi_ne hAi_A hBi_B0 hcosets
            have hAiBi_sub : Ai + Bi ⊆ A + B0 := add_subset_add hAi_A hBi_B0
            have hsub_coset : Ai + Bi ⊆ (a1 + b1) +ᵥ subFin H := by
              intro x hx
              obtain ⟨u, hu, v, hv, rfl⟩ := mem_add.mp hx
              rcases hcosets with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
              · obtain ⟨h1, hh1, rfl⟩ := mem_vadd_finset.mp (hu' hu)
                obtain ⟨h2, hh2, rfl⟩ := mem_vadd_finset.mp (hv' hv)
                rw [mem_subFin] at hh1 hh2
                rw [mem_vadd_finset]
                exact ⟨h1 + h2, (mem_subFin H _).mpr (H.add_mem hh1 hh2), by simp only [vadd_eq_add]; abel⟩
              · obtain ⟨h1, hh1, rfl⟩ := mem_vadd_finset.mp (hu' hu)
                obtain ⟨h2, hh2, rfl⟩ := mem_vadd_finset.mp (hv' hv)
                rw [mem_subFin] at hh1 hh2
                rw [mem_vadd_finset]
                exact ⟨h1 + h2, (mem_subFin H _).mpr (H.add_mem hh1 hh2), by simp only [vadd_eq_add]; abel⟩
            have hdisj_i : Disjoint (Ai + Bi) C := disjoint_of_subset_left hsub_coset hcoset_disj
            let Hi := addStab (Ai + Bi)
            have hHi_le : Hi ≤ H := by
              intro g hg
              obtain ⟨x, hx⟩ := hAi_ne.add hBi_ne
              have hxg : g +ᵥ x ∈ Ai + Bi := by
                have hst : g +ᵥ (Ai + Bi) = Ai + Bi := hg
                rw [← hst, mem_vadd_finset]
                exact ⟨x, hx, rfl⟩
              obtain ⟨h1, hh1, hhx1⟩ := mem_vadd_finset.mp (hsub_coset hx)
              obtain ⟨h2, hh2, hhx2⟩ := mem_vadd_finset.mp (hsub_coset hxg)
              rw [mem_subFin] at hh1 hh2
              have hg_eq : g = h2 - h1 := by
                simp only [vadd_eq_add] at hhx1 hhx2
                calc g = (g + x) - x := by abel
                  _ = ((a1 + b1) + h2) - ((a1 + b1) + h1) := by rw [← hhx2, ← hhx1]
                  _ = h2 - h1 := by abel
              rw [hg_eq]
              exact H.sub_mem hh2 hh1
            have hHi_lt_coset : (Ai + Bi).card < (subFin H).card := by
              have hle : (Ai + Bi).card ≤ ((a1 + b1) +ᵥ subFin H).card := card_le_card hsub_coset
              rw [card_vadd_finset] at hle
              refine lt_of_le_of_ne hle fun heq ↦ hnot_coset ?_
              have hEq : Ai + Bi = (a1 + b1) +ᵥ subFin H :=
                eq_of_subset_of_card_le hsub_coset (by rw [card_vadd_finset, heq])
              rw [← hEq]
              exact hAiBi_sub
            have hHi_ne_H : Hi ≠ H := by
              intro heq
              have hH_sub : H ≤ Hi := heq.ge
              obtain ⟨x, hx⟩ := hAi_ne.add hBi_ne
              have hcos_sub : x +ᵥ subFin H ⊆ Ai + Bi := by
                intro y hy
                obtain ⟨h, hh, rfl⟩ := mem_vadd_finset.mp hy
                rw [mem_subFin] at hh
                have hst : h +ᵥ (Ai + Bi) = Ai + Bi := hH_sub hh
                rw [← hst, mem_vadd_finset]
                exact ⟨x, hx, add_comm h x⟩
              have hle := card_le_card hcos_sub
              rw [card_vadd_finset] at hle
              omega
            have hHi_lt : Hi < H := lt_of_le_of_ne hHi_le hHi_ne_H
            have hstab_Ci : addStab (C ∪ (Ai + Bi)) = Hi := by
              apply le_antisymm
              · intro g hg
                rw [mem_addStab_iff] at hg
                have hg_H : g ∈ H := by
                  have hfib_eq : ((C ∪ (Ai + Bi)) ∩ ((g +ᵥ (a1 + b1)) +ᵥ subFin H)).card = (Ai + Bi).card := by
                    have him : g +ᵥ ((C ∪ (Ai + Bi)) ∩ ((a1 + b1) +ᵥ subFin H)) =
                        (C ∪ (Ai + Bi)) ∩ ((g +ᵥ (a1 + b1)) +ᵥ subFin H) := by
                      rw [vadd_finset_inter, hg, vadd_assoc]
                    rw [← him, card_vadd_finset]
                    have heq_inter : (C ∪ (Ai + Bi)) ∩ ((a1 + b1) +ᵥ subFin H) = Ai + Bi := by
                      ext x
                      simp only [mem_inter, mem_union]
                      constructor
                      · rintro ⟨hxC | hxAB, hxc⟩
                        · exact absurd hxC (disjoint_left.mp hcoset_disj hxc)
                        · exact hxAB
                      · intro hx
                        exact ⟨Or.inr hx, hsub_coset hx⟩
                    rw [heq_inter]
                  have hne_inter : ((C ∪ (Ai + Bi)) ∩ ((g +ᵥ (a1 + b1)) +ᵥ subFin H)).Nonempty := by
                    rw [← card_pos, hfib_eq]
                    exact card_pos.mpr (hAi_ne.add hBi_ne)
                  have hnot_C : ¬ (g +ᵥ (a1 + b1)) +ᵥ subFin H ⊆ C := by
                    intro hsubC
                    have hle : (subFin H).card ≤ ((C ∪ (Ai + Bi)) ∩ ((g +ᵥ (a1 + b1)) +ᵥ subFin H)).card := by
                      calc (subFin H).card = ((g +ᵥ (a1 + b1)) +ᵥ subFin H).card := (card_vadd_finset _ _).symm
                        _ ≤ _ := card_le_card (subset_inter (hsubC.trans subset_union_left) le_rfl)
                    rw [hfib_eq] at hle
                    omega
                  obtain ⟨y, hy⟩ := hne_inter
                  rw [mem_inter, mem_union] at hy
                  rcases hy.1 with hyC | hyAB
                  · exfalso
                    apply hnot_C
                    intro z hz
                    obtain ⟨h', hh', rfl⟩ := mem_vadd_finset.mp hz
                    obtain ⟨h, hh, hy_eq⟩ := mem_vadd_finset.mp hy.2
                    rw [mem_subFin] at hh hh'
                    have hd : h' - h ∈ H := H.sub_mem hh' hh
                    have hst : (h' - h) +ᵥ C = C := hd
                    rw [← hst, mem_vadd_finset]
                    refine ⟨y, hyC, ?_⟩
                    simp only [vadd_eq_add] at hy_eq ⊢
                    calc (h' - h) + y = (h' - h) + ((g + (a1 + b1)) + h) := by rw [← hy_eq]
                      _ = (g + (a1 + b1)) + h' := by abel
                  · obtain ⟨h1, hh1, hy1⟩ := mem_vadd_finset.mp (hsub_coset hyAB)
                    obtain ⟨h2, hh2, hy2⟩ := mem_vadd_finset.mp hy.2
                    rw [mem_subFin] at hh1 hh2
                    simp only [vadd_eq_add] at hy1 hy2
                    have hg_eq : g = h1 - h2 := by
                      calc g = ((g + (a1 + b1)) + h2) - (a1 + b1) - h2 := by abel
                        _ = ((a1 + b1) + h1) - (a1 + b1) - h2 := by rw [hy2, ← hy1]
                        _ = h1 - h2 := by abel
                    rw [hg_eq]
                    exact H.sub_mem hh1 hh2
                rw [mem_addStab_iff]
                ext x
                rw [mem_vadd_finset]
                constructor
                · rintro ⟨z, hz, rfl⟩
                  have hmem_Ci : g +ᵥ z ∈ C ∪ (Ai + Bi) := by
                    rw [← hg, mem_vadd_finset]
                    exact ⟨z, mem_union_right C hz, rfl⟩
                  rcases mem_union.mp hmem_Ci with hzC | hzAB
                  · exfalso
                    have hmem_cos : g +ᵥ z ∈ (a1 + b1) +ᵥ subFin H := by
                      obtain ⟨h, hh, rfl⟩ := mem_vadd_finset.mp (hsub_coset hz)
                      rw [mem_subFin] at hh
                      rw [mem_vadd_finset]
                      refine ⟨g + h, (mem_subFin H _).mpr (H.add_mem hg_H hh), ?_⟩
                      simp only [vadd_eq_add]; abel
                    exact disjoint_left.mp hcoset_disj hmem_cos hzC
                  · exact hzAB
                · intro hx
                  have hx_Ci : (-g) +ᵥ x ∈ C ∪ (Ai + Bi) := by
                    have hst : (-g) +ᵥ (C ∪ (Ai + Bi)) = C ∪ (Ai + Bi) := by
                      have := congrArg ((-g) +ᵥ ·) hg
                      simpa [← add_vadd] using this.symm
                    rw [← hst, mem_vadd_finset]
                    exact ⟨x, mem_union_right C hx, rfl⟩
                  rcases mem_union.mp hx_Ci with hxC | hxAB
                  · exfalso
                    have hmem_cos : (-g) +ᵥ x ∈ (a1 + b1) +ᵥ subFin H := by
                      obtain ⟨h, hh, rfl⟩ := mem_vadd_finset.mp (hsub_coset hx)
                      rw [mem_subFin] at hh
                      rw [mem_vadd_finset]
                      refine ⟨-g + h, (mem_subFin H _).mpr (H.add_mem (H.neg_mem hg_H) hh), ?_⟩
                      simp only [vadd_eq_add]; abel
                    exact disjoint_left.mp hcoset_disj hmem_cos hxC
                  · exact ⟨(-g) +ᵥ x, hxAB, by simp⟩
              · intro g hg
                rw [mem_addStab_iff, vadd_finset_union]
                have h1 : g +ᵥ C = C := hHi_le hg
                have h2 : g +ᵥ (Ai + Bi) = Ai + Bi := hg
                rw [h1, h2]
            have hlt_ind : (Ai + Bi).card + Ai.card < N := by
              have hc1 : (Ai + Bi).card < (A + B0).card := by
                have hC_sub_i : C ∪ (Ai + Bi) ⊆ A + B0 := union_subset hC_sub hAiBi_sub
                have hcard_u : (C ∪ (Ai + Bi)).card = C.card + (Ai + Bi).card :=
                  card_union_of_disjoint hdisj_i.symm
                have hcard_le : C.card + (Ai + Bi).card ≤ (A + B0).card := hcard_u ▸ card_le_card hC_sub_i
                have hC_pos : 0 < C.card := card_pos.mpr hC_ne
                omega
              have hc2 : Ai.card ≤ A.card := card_le_card hAi_A
              omega
            have hind_i := ih ((Ai + Bi).card + Ai.card) hlt_ind Ai Bi hAi_ne hBi_ne le_rfl
            have hCi_not_conv : ¬ isConv (C ∪ (Ai + Bi)) := by
              intro hconv
              have hmem_Ci : C ∪ (Ai + Bi) ∈ convs :=
                mem_filter.mpr ⟨mem_powerset.mpr (union_subset hC_sub hAiBi_sub), hconv⟩
              have hmin := hC_min (C ∪ (Ai + Bi)) hmem_Ci
              rw [hstab_Ci] at hmin
              change (subFin H).card ≤ (subFin Hi).card at hmin
              have hsub_fin : subFin Hi ⊂ subFin H := by
                rw [ssubset_iff_of_subset (fun g hg ↦ (mem_subFin H g).mpr (hHi_le ((mem_subFin Hi g).mp hg)))]
                obtain ⟨g, hgH, hgHi⟩ : ∃ g ∈ H, g ∉ Hi := by
                  by_contra hnone
                  push Not at hnone
                  exact hHi_lt.ne (le_antisymm hHi_le hnone)
                exact ⟨g, (mem_subFin H g).mpr hgH, fun hg ↦ hgHi ((mem_subFin Hi g).mp hg)⟩
              have hlt_card : (subFin Hi).card < (subFin H).card := card_lt_card hsub_fin
              omega
            have hCi_lt : (C ∪ (Ai + Bi)).card + (subFin Hi).card <
                (A ∩ B0).card + ((A ∪ B0) + subFin Hi).card := by
              by_contra hge
              push Not at hge
              exact hCi_not_conv ⟨union_subset hC_sub hAiBi_sub, hC_ne.mono subset_union_left, hstab_Ci ▸ hge⟩
            have hCi_card : (C ∪ (Ai + Bi)).card = C.card + (Ai + Bi).card :=
              card_union_of_disjoint hdisj_i.symm
            have hCu_le : C.card + (Ai + Bi).card ≤ (A + B0).card :=
              hCi_card ▸ card_le_card (union_subset hC_sub hAiBi_sub)
            have hAi_le : Ai.card ≤ (Ai + subFin Hi).card :=
              card_le_card fun x hx ↦ mem_add.mpr ⟨x, hx, 0, zero_mem_subFin Hi, add_zero x⟩
            have hBi_le : Bi.card ≤ (Bi + subFin Hi).card :=
              card_le_card fun x hx ↦ mem_add.mpr ⟨x, hx, 0, zero_mem_subFin Hi, add_zero x⟩
            have hC_ineq' : (A ∩ B0).card + ((A ∪ B0) + subFin H).card ≤ C.card + (subFin H).card := hC_ineq
            have hind_i' : (Ai + subFin Hi).card + (Bi + subFin Hi).card ≤ (Ai + Bi).card + (subFin Hi).card := hind_i
            have hg1 : ((A ∪ B0) + subFin H).card + (Ai + subFin Hi).card + (Bi + subFin Hi).card <
                ((A ∪ B0) + subFin Hi).card + (subFin H).card := by omega
            have hg2 : ((A ∪ B0) + subFin H).card + (A ∩ B0).card + Ai.card + Bi.card ≤
                (A + B0).card + (subFin H).card + (subFin Hi).card := by omega
            exact ⟨hsub_coset, hHi_lt, hind_i, hg1, hg2⟩
          obtain ⟨hsub1, hH1_lt, hind1, heq1_1, heq3_1⟩ :=
            hAiBi_prop A1 B1 hA1_ne hB1_ne inter_subset_left inter_subset_left
              (Or.inl ⟨inter_subset_right, inter_subset_right⟩)
          have hB2_ne : B2.Nonempty := by
            by_contra hB2_emp
            rw [not_nonempty_iff_eq_empty] at hB2_emp
            have hU_inter : (A ∪ B0) ∩ (a1 +ᵥ subFin H) ⊆ A1 := by
              intro x hx
              rw [mem_inter] at hx
              rcases mem_union.mp hx.1 with hxA | hxB
              · exact mem_inter.mpr ⟨hxA, hx.2⟩
              · exfalso
                have hxB2 : x ∈ B2 := mem_inter.mpr ⟨hxB, hx.2⟩
                rw [hB2_emp] at hxB2
                simp at hxB2
            have hdiff := card_coset_diff_le hH1_lt.le (mem_union_left B0 ha1) inter_subset_right hU_inter
            change ((A ∪ B0) + subFin (addStab (A1 + B1))).card + (subFin H).card ≤
              ((A ∪ B0) + subFin H).card + (A1 + subFin (addStab (A1 + B1))).card at hdiff
            have hB1_pos : 1 ≤ (B1 + subFin (addStab (A1 + B1))).card :=
              card_pos.mpr (hB1_ne.add (subFin_nonempty _))
            omega
          have hA2_ne : A2.Nonempty := by
            by_contra hA2_emp
            rw [not_nonempty_iff_eq_empty] at hA2_emp
            have hU_inter : (A ∪ B0) ∩ (b1 +ᵥ subFin H) ⊆ B1 := by
              intro x hx
              rw [mem_inter] at hx
              rcases mem_union.mp hx.1 with hxA | hxB
              · exfalso
                have hxA2 : x ∈ A2 := mem_inter.mpr ⟨hxA, hx.2⟩
                rw [hA2_emp] at hxA2
                simp at hxA2
              · exact mem_inter.mpr ⟨hxB, hx.2⟩
            have hdiff := card_coset_diff_le hH1_lt.le (mem_union_right A hb1) inter_subset_right hU_inter
            change ((A ∪ B0) + subFin (addStab (A1 + B1))).card + (subFin H).card ≤
              ((A ∪ B0) + subFin H).card + (B1 + subFin (addStab (A1 + B1))).card at hdiff
            have hA1_pos : 1 ≤ (A1 + subFin (addStab (A1 + B1))).card :=
              card_pos.mpr (hA1_ne.add (subFin_nonempty _))
            omega
          obtain ⟨hsub2, hH2_lt, hind2, heq1_2, heq3_2⟩ :=
            hAiBi_prop A2 B2 hA2_ne hB2_ne inter_subset_left inter_subset_left
              (Or.inr ⟨inter_subset_right, inter_subset_right⟩)
          have hcos_ne : a1 +ᵥ subFin H ≠ b1 +ᵥ subFin H := by
            intro heq
            have hU_inter : (A ∪ B0) ∩ (a1 +ᵥ subFin H) ⊆ A1 ∪ B1 := by
              intro x hx
              rw [mem_inter] at hx
              rcases mem_union.mp hx.1 with hxA | hxB
              · exact mem_union_left B1 (mem_inter.mpr ⟨hxA, hx.2⟩)
              · exact mem_union_right A1 (mem_inter.mpr ⟨hxB, heq ▸ hx.2⟩)
            have hX_sub : A1 ∪ B1 ⊆ a1 +ᵥ subFin H :=
              union_subset inter_subset_right (heq ▸ inter_subset_right)
            have hdiff := card_coset_diff_le hH1_lt.le (mem_union_left B0 ha1) hX_sub hU_inter
            have hun : (A1 ∪ B1) + subFin (addStab (A1 + B1)) =
                (A1 + subFin (addStab (A1 + B1))) ∪ (B1 + subFin (addStab (A1 + B1))) :=
              union_add
            have hun_le : ((A1 ∪ B1) + subFin (addStab (A1 + B1))).card ≤
                (A1 + subFin (addStab (A1 + B1))).card + (B1 + subFin (addStab (A1 + B1))).card := by
              rw [hun]
              exact card_union_le _ _
            omega
          have hcos_disj : Disjoint (a1 +ᵥ subFin H) (b1 +ᵥ subFin H) := by
            rw [disjoint_left]
            intro x hx1 hx2
            apply hcos_ne
            obtain ⟨h1, hh1, rfl⟩ := mem_vadd_finset.mp hx1
            obtain ⟨h2, hh2, hx2'⟩ := mem_vadd_finset.mp hx2
            rw [mem_subFin] at hh1 hh2
            have heq_ab : a1 - b1 = h2 - h1 := by
              simp only [vadd_eq_add] at hx2'
              calc a1 - b1 = (a1 + h1) - b1 - h1 := by abel
                _ = (b1 + h2) - b1 - h1 := by rw [← hx2']
                _ = h2 - h1 := by abel
            ext y
            simp only [mem_vadd_finset, mem_subFin]
            constructor
            · rintro ⟨h, hh, rfl⟩
              refine ⟨h + (h2 - h1), H.add_mem hh (H.sub_mem hh2 hh1), ?_⟩
              simp only [vadd_eq_add]
              calc b1 + (h + (h2 - h1)) = (b1 + h) + (h2 - h1) := by abel
                _ = (b1 + h) + (a1 - b1) := by rw [← heq_ab]
                _ = a1 + h := by abel
            · rintro ⟨h, hh, rfl⟩
              refine ⟨h - (h2 - h1), H.sub_mem hh (H.sub_mem hh2 hh1), ?_⟩
              simp only [vadd_eq_add]
              calc a1 + (h - (h2 - h1)) = (a1 + h) - (h2 - h1) := by abel
                _ = (a1 + h) - (a1 - b1) := by rw [← heq_ab]
                _ = b1 + h := by abel
          have h2_1 := kneser_aux_coset_le (A ∪ B0) A1 B1 hH1_lt.le heq1_1
          have h2_2 := kneser_aux_coset_le (A ∪ B0) A2 B2 hH2_lt.le heq1_2
          have hAB0_not_conv : ¬ isConv (A + B0) := by
            intro hconv
            have hmem_all : A + B0 ∈ convs := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, hconv⟩
            have hmin := hC_min (A + B0) hmem_all
            have hH_le1 : (subFin H).card ≤ 1 := by
              change (subFin H).card ≤ (subFin (addStab (A + B0))).card at hmin
              rwa [hAB0_stab, card_addStab_bot] at hmin
            have hH_ge2 : 2 ≤ (subFin H).card := by
              obtain ⟨g, hgH, hg0⟩ : ∃ g ∈ H, g ≠ 0 := by
                by_contra h0
                push Not at h0
                apply hH
                ext g
                simp only [AddSubgroup.mem_bot]
                exact ⟨h0 g, fun hg ↦ hg ▸ H.zero_mem⟩
              have hsub : ({(0 : G), g} : Finset G) ⊆ subFin H := by
                intro x hx
                rcases mem_insert.mp hx with rfl | hx'
                · exact zero_mem_subFin H
                · rw [mem_singleton.mp hx']
                  exact (mem_subFin H g).mpr hgH
              have h2 : ({(0 : G), g} : Finset G).card = 2 := card_pair hg0.symm
              exact h2 ▸ card_le_card hsub
            omega
          have hAB0_lt : (A + B0).card + 1 < (A ∩ B0).card + (A ∪ B0).card := by
            by_contra hge
            push Not at hge
            apply hAB0_not_conv
            refine ⟨Subset.rfl, hA.add hB0_ne, ?_⟩
            rw [hAB0_stab, card_addStab_bot, add_subFin_bot]
            exact hge
          let S := (a1 +ᵥ subFin H) \ (A1 ∪ B2)
          let T := (b1 +ᵥ subFin H) \ (A2 ∪ B1)
          have hST_disj : Disjoint S T := disjoint_of_subset_left sdiff_subset (disjoint_of_subset_right sdiff_subset hcos_disj)
          have hST_sub : S ∪ T ⊆ ((A ∪ B0) + subFin H) \ (A ∪ B0) := by
            intro x hx
            rw [mem_sdiff]
            rcases mem_union.mp hx with hxS | hxT
            · rw [mem_sdiff] at hxS
              refine ⟨?_, fun hxU ↦ hxS.2 ?_⟩
              · obtain ⟨h, hh, rfl⟩ := mem_vadd_finset.mp hxS.1
                exact mem_add.mpr ⟨a1, mem_union_left B0 ha1, h, hh, (vadd_eq_add a1 h).symm⟩
              · rcases mem_union.mp hxU with hxA | hxB
                · exact mem_union_left B2 (mem_inter.mpr ⟨hxA, hxS.1⟩)
                · exact mem_union_right A1 (mem_inter.mpr ⟨hxB, hxS.1⟩)
            · rw [mem_sdiff] at hxT
              refine ⟨?_, fun hxU ↦ hxT.2 ?_⟩
              · obtain ⟨h, hh, rfl⟩ := mem_vadd_finset.mp hxT.1
                exact mem_add.mpr ⟨b1, mem_union_right A hb1, h, hh, (vadd_eq_add b1 h).symm⟩
              · rcases mem_union.mp hxU with hxA | hxB
                · exact mem_union_left B1 (mem_inter.mpr ⟨hxA, hxT.1⟩)
                · exact mem_union_right A2 (mem_inter.mpr ⟨hxB, hxT.1⟩)
          have hST_card : S.card + T.card + (A ∪ B0).card ≤ ((A ∪ B0) + subFin H).card := by
            have hU_sub : A ∪ B0 ⊆ (A ∪ B0) + subFin H :=
              fun x hx ↦ mem_add.mpr ⟨x, hx, 0, zero_mem_subFin H, add_zero x⟩
            have h1 := card_le_card hST_sub
            rw [card_union_of_disjoint hST_disj, card_sdiff_of_subset hU_sub] at h1
            have h2 := card_le_card hU_sub
            omega
          have ha_cov : (subFin H).card ≤ S.card + A1.card + B2.card := by
            have hsub : a1 +ᵥ subFin H ⊆ S ∪ (A1 ∪ B2) := fun x hx ↦ by
              by_cases hxU : x ∈ A1 ∪ B2
              · exact mem_union_right S hxU
              · exact mem_union_left _ (mem_sdiff.mpr ⟨hx, hxU⟩)
            have hle := card_le_card hsub
            rw [card_vadd_finset] at hle
            have h1 : (S ∪ (A1 ∪ B2)).card ≤ S.card + (A1 ∪ B2).card := card_union_le _ _
            have h2 : (A1 ∪ B2).card ≤ A1.card + B2.card := card_union_le _ _
            omega
          have hb_cov : (subFin H).card ≤ T.card + A2.card + B1.card := by
            have hsub : b1 +ᵥ subFin H ⊆ T ∪ (A2 ∪ B1) := fun x hx ↦ by
              by_cases hxU : x ∈ A2 ∪ B1
              · exact mem_union_right T hxU
              · exact mem_union_left _ (mem_sdiff.mpr ⟨hx, hxU⟩)
            have hle := card_le_card hsub
            rw [card_vadd_finset] at hle
            have h1 : (T ∪ (A2 ∪ B1)).card ≤ T.card + (A2 ∪ B1).card := card_union_le _ _
            have h2 : (A2 ∪ B1).card ≤ A2.card + B1.card := card_union_le _ _
            omega
          omega

private lemma kneser_two {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty) :
    (A + subFin (G := G) (addStab (A + B))).card + (B + subFin (G := G) (addStab (A + B))).card ≤
      (A + B).card + (subFin (G := G) (addStab (A + B))).card :=
  kneser_aux ((A + B).card + A.card) A B hA hB le_rfl

private def sumFinset {G : Type} [AddCommMonoid G] [DecidableEq G] :
    ∀ {k : ℕ}, (Fin k → Finset G) → Finset G
  | 0, _ => {0}
  | _ + 1, C => sumFinset (fun i ↦ C i.castSucc) + C (Fin.last _)

private lemma sumFinset_nonempty {G : Type} [AddCommMonoid G] [DecidableEq G] :
    ∀ {k : ℕ} (C : Fin k → Finset G), (∀ i, (C i).Nonempty) → (sumFinset C).Nonempty
  | 0, _, _ => ⟨0, mem_singleton_self 0⟩
  | _ + 1, C, hC => (sumFinset_nonempty (fun i ↦ C i.castSucc) (fun i ↦ hC i.castSucc)).add (hC _)

private lemma image_sumFinset {G H' : Type} [AddCommMonoid G] [AddCommMonoid H'] [DecidableEq G] [DecidableEq H']
    (φ : G →+ H') : ∀ {k : ℕ} (C : Fin k → Finset G),
      (sumFinset C).image φ = sumFinset (fun i ↦ (C i).image φ)
  | 0, _ => by simp [sumFinset]
  | _ + 1, C => by
      simp only [sumFinset]
      rw [← image_sumFinset φ (fun i ↦ C i.castSucc)]
      ext q
      simp only [mem_image, mem_add]
      constructor
      · rintro ⟨z, ⟨u, hu, v, hv, rfl⟩, rfl⟩
        exact ⟨φ u, ⟨u, hu, rfl⟩, φ v, ⟨v, hv, rfl⟩, (map_add φ u v).symm⟩
      · rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨u + v, ⟨u, hu, v, hv, rfl⟩, map_add φ u v⟩

private lemma mem_sumFinset_iff {G : Type} [AddCommMonoid G] [DecidableEq G] :
    ∀ {k : ℕ} (C : Fin k → Finset G) (x : G),
      x ∈ sumFinset C ↔ ∃ f : Fin k → G, (∀ i, f i ∈ C i) ∧ ∑ i, f i = x
  | 0, C, x => by
      rw [sumFinset, mem_singleton]
      constructor
      · intro hx; exact ⟨Fin.elim0, fun i ↦ Fin.elim0 i, by simp [hx]⟩
      · rintro ⟨_, _, rfl⟩; simp
  | k + 1, C, x => by
      simp only [sumFinset, mem_add]
      constructor
      · rintro ⟨u, hu, v, hv, rfl⟩
        obtain ⟨f0, hf0, rfl⟩ := (mem_sumFinset_iff (fun i ↦ C i.castSucc) u).mp hu
        refine ⟨Fin.snoc f0 v, fun i ↦ ?_, ?_⟩
        · refine Fin.lastCases ?_ ?_ i
          · simp [Fin.snoc_last, hv]
          · intro j; simp [Fin.snoc_castSucc, hf0 j]
        · rw [Fin.sum_univ_castSucc]
          simp [Fin.snoc_castSucc, Fin.snoc_last]
      · rintro ⟨f, hf, rfl⟩
        refine ⟨∑ i : Fin k, f i.castSucc, ?_, f (Fin.last k), hf (Fin.last k), ?_⟩
        · exact (mem_sumFinset_iff (fun i ↦ C i.castSucc) _).mpr
            ⟨fun i ↦ f i.castSucc, fun i ↦ hf _, rfl⟩
        · rw [Fin.sum_univ_castSucc]

private lemma kneser_multi_bot :
    ∀ k : ℕ, 1 ≤ k → ∀ {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
      (C : Fin k → Finset G), (∀ i, (C i).Nonempty) →
      addStab (sumFinset C) = ⊥ →
      ∑ i : Fin k, (C i).card ≤ (sumFinset C).card + (k - 1) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro G _ _ _ C _ _
    have heq : sumFinset C = {0} + C 0 := rfl
    have h0 : ({0} : Finset G) + C 0 = C 0 := by
      rw [singleton_add, zero_vadd]
    rw [heq, h0]
    simp
  | succ k hk ih =>
    intro G _ _ _ C hC hstab
    let Cprev : Fin k → Finset G := fun i ↦ C i.castSucc
    let Sprev := sumFinset Cprev
    let Clast := C (Fin.last k)
    have hS : sumFinset C = Sprev + Clast := rfl
    have hstab_prev : addStab Sprev = ⊥ := by
      have hle : addStab Sprev ≤ addStab (Sprev + Clast) := by
        rw [add_comm]
        exact addStab_mono_add_left Clast Sprev
      rw [← hS, hstab] at hle
      exact le_bot_iff.mp hle
    have ih' := ih Cprev (fun i ↦ hC i.castSucc) hstab_prev
    have hk2 := kneser_two Sprev Clast (sumFinset_nonempty Cprev (fun i ↦ hC i.castSucc)) (hC (Fin.last k))
    rw [← hS, hstab, card_addStab_bot, add_subFin_bot, add_subFin_bot] at hk2
    rw [Fin.sum_univ_castSucc]
    dsimp only [Cprev, Clast, Sprev] at ih' hk2 ⊢
    omega

private lemma kneser_multi (k : ℕ) (hk : 1 ≤ k) {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (C : Fin k → Finset G) (hC : ∀ i, (C i).Nonempty) :
    ∑ i : Fin k, (C i + subFin (G := G) (addStab (sumFinset C))).card ≤
      (sumFinset C).card + (k - 1) * (subFin (G := G) (addStab (sumFinset C))).card := by
  let S := sumFinset C
  let H := addStab S
  let φ := QuotientAddGroup.mk' H
  let C' : Fin k → Finset (G ⧸ H) := fun i ↦ (C i).image φ
  have hC' : ∀ i, (C' i).Nonempty := fun i ↦ (hC i).image φ
  have hS' : sumFinset C' = S.image φ := (image_sumFinset φ C).symm
  have hstab' : addStab (sumFinset C') = ⊥ := by
    rw [hS']
    exact addStab_image_quot S
  have hbot := kneser_multi_bot k hk C' hC' hstab'
  rw [hS'] at hbot
  have hS_card : S.card = (S.image φ).card * (subFin H).card := card_of_le_addStab (le_refl H)
  have hsum_card : ∑ i : Fin k, (C i + subFin H).card =
      (∑ i : Fin k, (C' i).card) * (subFin H).card := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact card_add_subFin (C i) H
  rw [hsum_card, hS_card]
  have hmul := Nat.mul_le_mul_right (subFin H).card hbot
  nlinarith

end Kneser

section LevThm5

open Finset Classical
open scoped Pointwise

private lemma nat_cauchy_davenport_multi (k : ℕ) (hk : 1 ≤ k) (A : Fin k → Finset ℕ)
    (hA : ∀ i, (A i).Nonempty) :
    ∑ i : Fin k, (A i).card ≤ (sumFinset A).card + (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base =>
    have heq : sumFinset A = {0} + A 0 := rfl
    have h0 : ({0} : Finset ℕ) + A 0 = A 0 := by rw [singleton_add, zero_vadd]
    rw [heq, h0]
    simp
  | succ k hk ih =>
    have ih' := ih (fun i ↦ A i.castSucc) (fun i ↦ hA i.castSucc)
    have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd
      (sumFinset_nonempty (fun i ↦ A i.castSucc) (fun i ↦ hA i.castSucc)) (hA (Fin.last k))
    have hS : sumFinset A = sumFinset (fun i ↦ A i.castSucc) + A (Fin.last k) := rfl
    rw [← hS] at hcd
    rw [Fin.sum_univ_castSucc]
    have hne : 1 ≤ (sumFinset A).card := card_pos.mpr (sumFinset_nonempty A hA)
    omega

private lemma zmod_subgroup_char (n : ℕ) [NeZero n] (H : AddSubgroup (ZMod n)) :
    let q := (subFin H).card
    let d := n / q
    0 < q ∧ q ∣ n ∧ 0 < d ∧ d * q = n ∧ (∀ x : ℕ, (x : ZMod n) ∈ H ↔ d ∣ x) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have htop : (subFin (⊤ : AddSubgroup (ZMod n))).card = n := by
    have heq : subFin (⊤ : AddSubgroup (ZMod n)) = (Finset.univ : Finset (ZMod n)) := by
      ext x; simp
    rw [heq, Finset.card_univ, ZMod.card n]
  have hq_pos : 0 < (subFin H).card := card_pos.mpr (subFin_nonempty H)
  have hq_dvd : (subFin H).card ∣ n := by
    simpa [htop] using card_subFin_dvd_of_le (le_top : H ≤ ⊤)
  have hd_pos : 0 < n / (subFin H).card := Nat.div_pos (Nat.le_of_dvd hn hq_dvd) hq_pos
  have hmul : (n / (subFin H).card) * (subFin H).card = n := Nat.div_mul_cancel hq_dvd
  let P : ℕ → Prop := fun k ↦ 0 < k ∧ (k : ZMod n) ∈ H
  have hex : ∃ k, P k := ⟨n, hn, by simp⟩
  let d' := Nat.find hex
  have hd' : P d' := Nat.find_spec hex
  have hd'_iff : ∀ x : ℕ, (x : ZMod n) ∈ H ↔ d' ∣ x := by
    intro x
    constructor
    · intro hx
      by_contra hnd
      have hr_pos : 0 < x % d' := Nat.pos_of_ne_zero fun h0 ↦ hnd (Nat.dvd_of_mod_eq_zero h0)
      have hr_lt : x % d' < d' := Nat.mod_lt x hd'.1
      have hcast : ((x % d' : ℕ) : ZMod n) = (x : ZMod n) - (x / d') • (d' : ZMod n) := by
        have hdiv : d' * (x / d') + x % d' = x := Nat.div_add_mod x d'
        have hc : ((d' * (x / d') + x % d' : ℕ) : ZMod n) = (x : ZMod n) := congrArg Nat.cast hdiv
        push_cast at hc
        rw [mul_comm, ← nsmul_eq_mul] at hc
        exact eq_sub_of_add_eq' hc
      have hmem : P (x % d') := ⟨hr_pos, hcast ▸ H.sub_mem hx (H.nsmul_mem hd'.2 (x / d'))⟩
      exact Nat.find_min hex hr_lt hmem
    · rintro ⟨c, rfl⟩
      push_cast
      rw [mul_comm, ← nsmul_eq_mul]
      exact H.nsmul_mem hd'.2 c
  have hd'_dvd : d' ∣ n := (hd'_iff n).mp (by simp)
  have hcard_eq : (subFin H).card = n / d' := by
    have hbij : (subFin H).card = (Finset.univ : Finset (Fin (n / d'))).card := by
      refine (Finset.card_bij (fun (j : Fin (n / d')) _ ↦ ((j.val * d' : ℕ) : ZMod n)) ?_ ?_ ?_).symm
      · intro j _
        rw [mem_subFin]
        exact (hd'_iff _).mpr ⟨j.val, mul_comm _ _⟩
      · intro a _ b _ hab
        have hmul' : n / d' * d' = n := Nat.div_mul_cancel hd'_dvd
        have ha_lt : a.val * d' < n := by have := a.isLt; nlinarith
        have hb_lt : b.val * d' < n := by have := b.isLt; nlinarith
        have hv := congrArg ZMod.val hab
        rw [ZMod.val_natCast_of_lt ha_lt, ZMod.val_natCast_of_lt hb_lt] at hv
        exact Fin.ext (Nat.eq_of_mul_eq_mul_right hd'.1 hv)
      · intro z hz
        rw [mem_subFin] at hz
        have hdz : d' ∣ z.val := (hd'_iff z.val).mp (by simpa [ZMod.natCast_zmod_val] using hz)
        have hm_lt : z.val / d' < n / d' := by
          have hmul' : n / d' * d' = n := Nat.div_mul_cancel hd'_dvd
          have hz_lt : z.val < n := ZMod.val_lt z
          have hdiv' : z.val / d' * d' = z.val := Nat.div_mul_cancel hdz
          nlinarith
        refine ⟨⟨z.val / d', hm_lt⟩, mem_univ _, ?_⟩
        dsimp
        rw [Nat.div_mul_cancel hdz, ZMod.natCast_zmod_val]
    simpa using hbij
  have hmul' : d' * (subFin H).card = n := by
    rw [hcard_eq]
    exact Nat.mul_div_cancel' hd'_dvd
  have hd_eq : d' = n / (subFin H).card :=
    Nat.eq_of_mul_eq_mul_right hq_pos (hmul'.trans hmul.symm)
  refine ⟨hq_pos, hq_dvd, hd_pos, hmul, fun x ↦ hd_eq ▸ hd'_iff x⟩

private lemma zmod_val_cast_nat {l d : ℕ} (hd_dvd : d ∣ l) (x : ℕ) :
    (((x : ZMod l).val : ℕ) : ZMod d) = (x : ZMod d) := by
  rw [ZMod.val_natCast]
  have h1 : (l * (x / l) + x % l : ℕ) = x := Nat.div_add_mod x l
  have h2 := congrArg (Nat.cast : ℕ → ZMod d) h1
  push_cast at h2
  have hl0 : (l : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff l d).mpr hd_dvd
  rw [hl0, zero_mul, zero_add] at h2
  exact h2

private lemma zmod_val_eq_iff_sub_mem {l d : ℕ} (hl : 0 < l) (_hd_dvd : d ∣ l)
    {H : AddSubgroup (ZMod l)} (hH : ∀ x : ℕ, (x : ZMod l) ∈ H ↔ d ∣ x)
    (z₁ z₂ : ZMod l) :
    ((z₁.val : ℕ) : ZMod d) = ((z₂.val : ℕ) : ZMod d) ↔ z₁ - z₂ ∈ H := by
  have : NeZero l := ⟨Nat.ne_of_gt hl⟩
  have hswap : ∀ a b : ZMod l, a.val ≤ b.val →
      ((((a.val : ℕ) : ZMod d) = ((b.val : ℕ) : ZMod d)) ↔ b - a ∈ H) := by
    intro a b hab
    have hsub_l : ((b.val - a.val : ℕ) : ZMod l) = b - a := by
      rw [Nat.cast_sub hab, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have hsub_d : ((b.val - a.val : ℕ) : ZMod d) = ((b.val : ℕ) : ZMod d) - ((a.val : ℕ) : ZMod d) :=
      Nat.cast_sub hab
    rw [← hsub_l, hH (b.val - a.val), ← ZMod.natCast_eq_zero_iff, hsub_d, sub_eq_zero]
    exact eq_comm
  rcases le_total z₁.val z₂.val with h | h
  · rw [hswap z₁ z₂ h]
    constructor
    · intro hm; simpa using H.neg_mem hm
    · intro hm; simpa using H.neg_mem hm
  · exact eq_comm.trans (hswap z₂ z₁ h)

private lemma zmod_card_image_erase {l : ℕ} (hl : 0 < l) {A : Finset ℕ}
    (h0 : 0 ∈ A) (hle : ∀ x ∈ A, x ≤ l) :
    (A.image (Nat.cast : ℕ → ZMod l)).card = (A.erase l).card := by
  have heq : A.image (Nat.cast : ℕ → ZMod l) = (A.erase l).image (Nat.cast : ℕ → ZMod l) := by
    ext z
    simp only [mem_image, mem_erase]
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases hxl : x = l
      · subst hxl
        exact ⟨0, ⟨hl.ne, h0⟩, by simp⟩
      · exact ⟨x, ⟨hxl, hx⟩, rfl⟩
    · rintro ⟨x, ⟨_, hx⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  have hinj : Set.InjOn (Nat.cast : ℕ → ZMod l) (A.erase l) := by
    intro x hx y hy hxy
    rw [mem_coe, mem_erase] at hx hy
    have hx_lt : x < l := lt_of_le_of_ne (hle x hx.2) hx.1
    have hy_lt : y < l := lt_of_le_of_ne (hle y hy.2) hy.1
    have hv := congrArg ZMod.val hxy
    rwa [ZMod.val_natCast_of_lt hx_lt, ZMod.val_natCast_of_lt hy_lt] at hv
  rw [heq, card_image_of_injOn hinj]

private lemma fiber_card_add_one_le {l : ℕ} (hl : 0 < l) (B Alast : Finset ℕ)
    (h0 : 0 ∈ Alast) (hl_mem : l ∈ Alast)
    (z : ZMod l) (hz : z ∈ (B + Alast).image (Nat.cast : ℕ → ZMod l)) :
    (B.filter (fun x : ℕ ↦ (x : ZMod l) = z)).card + 1 ≤
      ((B + Alast).filter (fun x : ℕ ↦ (x : ZMod l) = z)).card := by
  let Bz := B.filter (fun x : ℕ ↦ (x : ZMod l) = z)
  let Sz := (B + Alast).filter (fun x : ℕ ↦ (x : ZMod l) = z)
  have hsub : Bz ⊆ Sz := by
    intro x hx
    rw [mem_filter] at hx ⊢
    exact ⟨mem_add.mpr ⟨x, hx.1, 0, h0, add_zero x⟩, hx.2⟩
  by_cases hBz : Bz.Nonempty
  · let bm := Bz.max' hBz
    have hbm_mem : bm ∈ Bz := max'_mem Bz hBz
    have hbm_B : bm ∈ B := (mem_filter.mp hbm_mem).1
    have hbm_z : (bm : ZMod l) = z := (mem_filter.mp hbm_mem).2
    have hbm_Sz : bm + l ∈ Sz := by
      rw [mem_filter]
      refine ⟨mem_add.mpr ⟨bm, hbm_B, l, hl_mem, rfl⟩, ?_⟩
      simp [hbm_z]
    have hbm_nmem : bm + l ∉ Bz := by
      intro hmem
      have hle := le_max' Bz (bm + l) hmem
      omega
    have hins : insert (bm + l) Bz ⊆ Sz := insert_subset_iff.mpr ⟨hbm_Sz, hsub⟩
    have hle := card_le_card hins
    rw [card_insert_of_notMem hbm_nmem] at hle
    exact hle
  · rw [not_nonempty_iff_eq_empty] at hBz
    have hBz0 : Bz.card = 0 := by rw [hBz, card_empty]
    obtain ⟨s, hs, hsz⟩ := mem_image.mp hz
    have hpos : 0 < Sz.card := card_pos.mpr ⟨s, mem_filter.mpr ⟨hs, hsz⟩⟩
    change Bz.card + 1 ≤ Sz.card
    omega

private lemma card_image_quot_eq_card_image {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : α → γ) (hfg : ∀ a b, f a = f b ↔ g a = g b) (U : Finset α) :
    (U.image f).card = (U.image g).card := by
  induction U using Finset.induction with
  | empty => simp
  | @insert a s _ ih =>
    rw [image_insert, image_insert]
    have heq : f a ∈ s.image f ↔ g a ∈ s.image g := by
      simp only [mem_image]
      constructor
      · rintro ⟨b, hb, hab⟩; exact ⟨b, hb, (hfg b a).mp hab⟩
      · rintro ⟨b, hb, hab⟩; exact ⟨b, hb, (hfg b a).mpr hab⟩
    by_cases hf : f a ∈ s.image f
    · rw [insert_eq_of_mem hf, insert_eq_of_mem (heq.mp hf), ih]
    · rw [card_insert_of_notMem hf, card_insert_of_notMem (mt heq.mpr hf), ih]

private lemma lev_thm5 (k' : ℕ) (hk' : 1 ≤ k') (l : ℕ) (hl : 0 < l)
    (A : Fin (k' + 1) → Finset ℕ)
    (h0 : ∀ i, 0 ∈ A i)
    (hle : ∀ i, ∀ x ∈ A i, x ≤ l)
    (hl_mem : l ∈ A (Fin.last k'))
    (hcop : ∀ d : ℕ, 1 < d → ¬ ∀ x ∈ A (Fin.last k'), d ∣ x) :
    let B := sumFinset (fun i : Fin k' ↦ A i.castSucc)
    let S := sumFinset A
    B.card + min l (∑ i : Fin (k' + 1), ((A i).erase l).card - k') ≤ S.card := by
  intro B S
  have : NeZero l := ⟨Nat.ne_of_gt hl⟩
  let φl : ℕ →+ ZMod l := Nat.castAddMonoidHom (ZMod l)
  let C : Fin (k' + 1) → Finset (ZMod l) := fun i ↦ (A i).image φl
  have hC_ne : ∀ i, (C i).Nonempty := fun i ↦ ⟨0, mem_image.mpr ⟨0, h0 i, by simp⟩⟩
  have hC_card : ∀ i, (C i).card = ((A i).erase l).card :=
    fun i ↦ zmod_card_image_erase hl (h0 i) (hle i)
  have hS_eq : S = B + A (Fin.last k') := rfl
  have hCS : sumFinset C = S.image φl := (image_sumFinset φl A).symm
  have hfib_sum : B.card + (S.image φl).card ≤ S.card := by
    have hB_sub : B ⊆ S := by
      intro b hb
      rw [hS_eq]
      exact mem_add.mpr ⟨b, hb, 0, h0 (Fin.last k'), add_zero b⟩
    have hB_im : B.image φl ⊆ S.image φl := image_subset_image hB_sub
    rw [Finset.card_eq_sum_card_fiberwise (f := ⇑φl) (t := S.image φl)
      (fun x hx ↦ hB_im (mem_image_of_mem φl hx))]
    rw [Finset.card_eq_sum_card_fiberwise (f := ⇑φl) (t := S.image φl)
      (fun x hx ↦ mem_image_of_mem φl hx)]
    have hadd_sum :
        (∑ z ∈ S.image φl, (B.filter (fun x ↦ φl x = z)).card) + (S.image φl).card =
          ∑ z ∈ S.image φl, ((B.filter (fun x ↦ φl x = z)).card + 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    rw [hadd_sum]
    refine Finset.sum_le_sum fun z hz ↦ ?_
    exact fiber_card_add_one_le hl B (A (Fin.last k')) (h0 (Fin.last k')) hl_mem z hz
  let H := addStab (sumFinset C)
  obtain ⟨hq_pos, hq_dvd, hd_pos, hmul, hH_iff⟩ := zmod_subgroup_char l H
  let q := (subFin H).card
  let d := l / q
  change 0 < q at hq_pos
  change q ∣ l at hq_dvd
  change 0 < d at hd_pos
  change d * q = l at hmul
  change ∀ x : ℕ, (x : ZMod l) ∈ H ↔ d ∣ x at hH_iff
  by_cases hd1 : d = 1
  · have hq_eq : q = l := by rw [hd1, one_mul] at hmul; exact hmul
    obtain ⟨z0, hz0⟩ := sumFinset_nonempty C hC_ne
    have hcos_sub : z0 +ᵥ subFin H ⊆ sumFinset C := by
      intro y hy
      obtain ⟨h, hh, rfl⟩ := mem_vadd_finset.mp hy
      rw [mem_subFin] at hh
      have hst : h +ᵥ sumFinset C = sumFinset C := hh
      rw [← hst, mem_vadd_finset]
      exact ⟨z0, hz0, add_comm h z0⟩
    have hlen : l ≤ (sumFinset C).card := by
      have h1 := card_le_card hcos_sub
      rw [card_vadd_finset] at h1
      change q ≤ (sumFinset C).card at h1
      omega
    rw [hCS] at hlen
    have : min l (∑ i : Fin (k' + 1), ((A i).erase l).card - k') ≤ l := min_le_left _ _
    omega
  · by_cases hq1 : q = 1
    · have hH_eq : subFin H = {(0 : ZMod l)} := by
        refine eq_singleton_iff_unique_mem.mpr ⟨zero_mem_subFin H, fun x hx ↦ ?_⟩
        obtain ⟨a, ha⟩ := card_eq_one.mp hq1
        have hx0 := mem_singleton.mp (ha ▸ hx)
        have h00 := mem_singleton.mp (ha ▸ zero_mem_subFin H)
        exact hx0.trans h00.symm
      have hk_multi := kneser_multi (k' + 1) (by omega) C hC_ne
      change ∑ i : Fin (k' + 1), (C i + subFin H).card ≤ (sumFinset C).card + (k' + 1 - 1) * q at hk_multi
      have hadd0 : ∀ i, C i + subFin H = C i := fun i ↦ by
        rw [hH_eq]
        ext z; simp [mem_add]
      simp only [hadd0, hq1, mul_one, Nat.add_sub_cancel] at hk_multi
      have hsum_eq : ∑ i : Fin (k' + 1), (C i).card = ∑ i : Fin (k' + 1), ((A i).erase l).card :=
        Finset.sum_congr rfl fun i _ ↦ hC_card i
      rw [hsum_eq, hCS] at hk_multi
      have : min l (∑ i : Fin (k' + 1), ((A i).erase l).card - k') ≤
          ∑ i : Fin (k' + 1), ((A i).erase l).card - k' := min_le_right _ _
      omega
    · have hd_gt1 : 1 < d := by omega
      have hq_gt1 : 1 < q := by omega
      have : NeZero d := ⟨Nat.ne_of_gt hd_pos⟩
      let φd : ℕ →+ ZMod d := Nat.castAddMonoidHom (ZMod d)
      let πld : ZMod l → ZMod d := fun z ↦ (z.val : ZMod d)
      have hd_dvd : d ∣ l := ⟨q, mul_comm q d ▸ hmul.symm⟩
      have hπ_comp : ∀ x : ℕ, πld (φl x) = φd x := fun x ↦ zmod_val_cast_nat hd_dvd x
      have hπ_iff : ∀ z₁ z₂ : ZMod l,
          QuotientAddGroup.mk' H z₁ = QuotientAddGroup.mk' H z₂ ↔ πld z₁ = πld z₂ := by
        intro z₁ z₂
        rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_iff_sub_mem]
        exact (zmod_val_eq_iff_sub_mem hl hd_dvd hH_iff z₁ z₂).symm
      let R := S.image φd
      let R_B := B.image φd
      have hR_im : R = (sumFinset C).image πld := by
        rw [hCS, image_image]
        ext r
        simp [R, Function.comp_apply, hπ_comp]
      have hCS_card : (sumFinset C).card = R.card * q := by
        rw [card_of_le_addStab (le_refl H), hR_im]
        congr 1
        exact card_image_quot_eq_card_image (QuotientAddGroup.mk' H) πld hπ_iff (sumFinset C)
      have hR_ne_univ : R ≠ Finset.univ := by
        intro huniv
        have hRc : R.card = d := by rw [huniv, card_univ, ZMod.card d]
        have hCSc : (sumFinset C).card = l := by rw [hCS_card, hRc, hmul]
        have hCS_univ : sumFinset C = Finset.univ :=
          Finset.eq_univ_of_card (sumFinset C) (by rw [hCSc, ZMod.card l])
        have hH_top : H = ⊤ := by
          ext z
          simp only [AddSubgroup.mem_top, iff_true]
          rw [mem_addStab_iff, hCS_univ]
          ext w; simp
        have hql : q = l := by
          have := congrArg (fun K ↦ (subFin K).card) hH_top
          rw [show (subFin (⊤ : AddSubgroup (ZMod l))).card = l from by
            have : subFin (⊤ : AddSubgroup (ZMod l)) = Finset.univ := by ext x; simp
            rw [this, card_univ, ZMod.card l]] at this
          exact this
        rw [hql] at hmul
        have : d = 1 := by nlinarith
        exact hd1 this
      have hRB_sub : R_B ⊆ R := by
        intro r hr
        obtain ⟨b, hb, rfl⟩ := mem_image.mp hr
        refine mem_image.mpr ⟨b + 0, ?_, by simp⟩
        rw [hS_eq]
        exact mem_add.mpr ⟨b, hb, 0, h0 (Fin.last k'), rfl⟩
      have hRB_ne : R_B ≠ R := by
        intro hRB_eq
        let HR := addStab R_B
        have hlast_stab : ∀ x ∈ A (Fin.last k'), φd x ∈ HR := by
          intro x hx
          rw [mem_addStab_iff]
          refine eq_of_subset_of_card_le (fun y hy ↦ ?_) (card_vadd_finset _ _).ge
          obtain ⟨r, hr, rfl⟩ := mem_vadd_finset.mp hy
          obtain ⟨b, hb, rfl⟩ := mem_image.mp hr
          rw [hRB_eq]
          refine mem_image.mpr ⟨b + x, ?_, ?_⟩
          · rw [hS_eq]; exact mem_add.mpr ⟨b, hb, x, hx, rfl⟩
          · simp [φd, vadd_eq_add, add_comm]
        obtain ⟨hq'_pos, hq'_dvd, hd'_pos, hmul', hHR_iff⟩ := zmod_subgroup_char d HR
        have hd'_gt1 : 1 < d / (subFin HR).card := by
          by_contra hd'_le
          have hd'_eq1 : d / (subFin HR).card = 1 := by omega
          rw [hd'_eq1, one_mul] at hmul'
          have hHR_top : HR = ⊤ := by
            ext z
            simp only [AddSubgroup.mem_top, iff_true]
            have hz_sub : (subFin HR).card = d := hmul'
            have huniv : subFin HR = Finset.univ :=
              Finset.eq_univ_of_card (subFin HR) (by rw [hz_sub, ZMod.card d])
            have hz_mem : z ∈ subFin HR := huniv ▸ mem_univ z
            exact (mem_subFin HR z).mp hz_mem
          have hRB_univ : R_B = Finset.univ := by
            refine eq_univ_iff_forall.mpr fun z ↦ ?_
            have hz_stab : z ∈ HR := hHR_top ▸ AddSubgroup.mem_top z
            have h0_RB : (0 : ZMod d) ∈ R_B := mem_image.mpr ⟨(0 : ℕ), ?_, by simp⟩
            swap
            · exact (mem_sumFinset_iff (fun i ↦ A i.castSucc) (0 : ℕ)).mpr ⟨fun _ ↦ 0, fun i ↦ h0 i.castSucc, by simp⟩
            have hst : z +ᵥ R_B = R_B := hz_stab
            rw [← hst, mem_vadd_finset]
            exact ⟨0, h0_RB, add_zero z⟩
          exact hR_ne_univ (hRB_eq ▸ hRB_univ)
        apply hcop (d / (subFin HR).card) hd'_gt1
        intro x hx
        exact (hHR_iff x).mp (hlast_stab x hx)
      have hRB_ssub : R_B ⊂ R := Finset.ssubset_iff_subset_ne.mpr ⟨hRB_sub, hRB_ne⟩
      obtain ⟨r0, hr0_R, hr0_RB⟩ := Finset.exists_of_ssubset hRB_ssub
      obtain ⟨s0, hs0_S, hs0_eq⟩ := mem_image.mp hr0_R
      obtain ⟨f, hf_mem, hf_sum⟩ := (mem_sumFinset_iff A s0).mp hs0_S
      let A_sub : Fin (k' + 1) → Finset ℕ := fun i ↦ (A i).filter (fun x ↦ φd x = φd (f i))
      have hAsub_ne : ∀ i, (A_sub i).Nonempty :=
        fun i ↦ ⟨f i, mem_filter.mpr ⟨hf_mem i, rfl⟩⟩
      have hAsub_sub : sumFinset A_sub ⊆ S.filter (fun s ↦ φd s = r0) := by
        intro s hs
        obtain ⟨g, hg_mem, rfl⟩ := (mem_sumFinset_iff A_sub s).mp hs
        rw [mem_filter]
        refine ⟨(mem_sumFinset_iff A _).mpr ⟨g, fun i ↦ (mem_filter.mp (hg_mem i)).1, rfl⟩, ?_⟩
        rw [map_sum]
        have hcongr : ∑ i : Fin (k' + 1), φd (g i) = ∑ i : Fin (k' + 1), φd (f i) :=
          Finset.sum_congr rfl fun i _ ↦ (mem_filter.mp (hg_mem i)).2
        rw [hcongr, ← map_sum, hf_sum, hs0_eq]
      have hcd := nat_cauchy_davenport_multi (k' + 1) (by omega) A_sub hAsub_ne
      simp only [Nat.add_sub_cancel] at hcd
      have hr0_ineq : ∑ i : Fin (k' + 1), (A_sub i).card ≤
          (S.filter (fun s ↦ φd s = r0)).card + k' :=
        le_trans hcd (Nat.add_le_add_right (card_le_card hAsub_sub) k')
      have hr0_B : (B.filter (fun b ↦ φd b = r0)).card = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]
        intro b hb hbd
        apply hr0_RB
        exact mem_image.mpr ⟨b, hb, hbd⟩
      have hfib_diff : ∀ r ∈ R.erase r0,
          (B.filter (fun b ↦ φd b = r)).card + q ≤ (S.filter (fun s ↦ φd s = r)).card := by
        intro r hr
        have hr_R : r ∈ R := (mem_erase.mp hr).2
        let Zr := (sumFinset C).filter (fun z ↦ πld z = r)
        have hZr_card : Zr.card = q := by
          obtain ⟨z0, hz0_CS, hz0_eq⟩ := mem_image.mp (hR_im ▸ hr_R)
          have hZr_eq : Zr = z0 +ᵥ subFin H := by
            ext z
            simp only [Zr, mem_filter, mem_vadd_finset, mem_subFin]
            constructor
            · rintro ⟨_, hzr⟩
              have hd_mem : z - z0 ∈ H :=
                (zmod_val_eq_iff_sub_mem hl hd_dvd hH_iff z z0).mp (hzr.trans hz0_eq.symm)
              exact ⟨z - z0, hd_mem, by simp⟩
            · rintro ⟨h, hh, rfl⟩
              refine ⟨?_, ?_⟩
              · have hst : h +ᵥ sumFinset C = sumFinset C := hh
                rw [← hst, mem_vadd_finset]
                exact ⟨z0, hz0_CS, add_comm h z0⟩
              · have hm : (z0 +ᵥ h) - z0 ∈ H := by simpa [vadd_eq_add] using hh
                exact ((zmod_val_eq_iff_sub_mem hl hd_dvd hH_iff (z0 +ᵥ h) z0).mpr hm).trans hz0_eq
          rw [hZr_eq, card_vadd_finset]
        have hS_r : (S.filter (fun s ↦ φd s = r)).card =
            ∑ z ∈ Zr, (S.filter (fun s ↦ φl s = z)).card := by
          rw [Finset.card_eq_sum_card_fiberwise (f := fun s ↦ φl s) (t := Zr) ?_]
          · refine Finset.sum_congr rfl fun z hz ↦ ?_
            congr 1; ext s
            simp only [mem_filter]
            have hzr := (mem_filter.mp hz).2
            constructor
            · rintro ⟨⟨_, _⟩, hsz⟩; exact ⟨‹_›, hsz⟩
            · rintro ⟨hsS, hsz⟩
              refine ⟨⟨hsS, ?_⟩, hsz⟩
              rw [← hπ_comp, hsz, hzr]
          · intro s hs
            simp only [Zr, mem_coe, mem_filter] at hs ⊢
            refine ⟨hCS ▸ mem_image_of_mem φl hs.1, ?_⟩
            rw [hπ_comp]; exact hs.2
        have hB_r : (B.filter (fun b ↦ φd b = r)).card =
            ∑ z ∈ Zr, (B.filter (fun b ↦ φl b = z)).card := by
          have hB_maps : ∀ b ∈ B.filter (fun b ↦ φd b = r), φl b ∈ Zr := by
            intro b hb
            simp only [Zr, mem_filter] at hb ⊢
            have hbS : b ∈ S := by rw [hS_eq]; exact mem_add.mpr ⟨b, hb.1, 0, h0 (Fin.last k'), add_zero b⟩
            refine ⟨hCS ▸ mem_image_of_mem φl hbS, ?_⟩
            rw [hπ_comp]; exact hb.2
          rw [Finset.card_eq_sum_card_fiberwise (f := fun b ↦ φl b) (t := Zr) hB_maps]
          refine Finset.sum_congr rfl fun z hz ↦ ?_
          congr 1; ext b
          simp only [mem_filter]
          have hzr := (mem_filter.mp hz).2
          constructor
          · rintro ⟨⟨_, _⟩, hbz⟩; exact ⟨‹_›, hbz⟩
          · rintro ⟨hbB, hbz⟩
            refine ⟨⟨hbB, ?_⟩, hbz⟩
            rw [← hπ_comp, hbz, hzr]
        rw [hB_r, hS_r, ← hZr_card]
        have hsum_add : (∑ z ∈ Zr, (B.filter (fun b ↦ φl b = z)).card) + Zr.card =
            ∑ z ∈ Zr, ((B.filter (fun b ↦ φl b = z)).card + 1) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
        rw [hsum_add]
        refine Finset.sum_le_sum fun z hz ↦ ?_
        have hz_im : z ∈ S.image φl := hCS ▸ (mem_filter.mp hz).1
        exact fiber_card_add_one_le hl B (A (Fin.last k')) (h0 (Fin.last k')) hl_mem z hz_im
      have hS_decomp : S.card = ∑ r ∈ R, (S.filter (fun s ↦ φd s = r)).card :=
        Finset.card_eq_sum_card_fiberwise (f := ⇑φd) (t := R) (fun _ hx ↦ mem_image_of_mem φd hx)
      have hB_decomp : B.card = ∑ r ∈ R, (B.filter (fun b ↦ φd b = r)).card :=
        Finset.card_eq_sum_card_fiberwise (f := ⇑φd) (t := R) (fun _ hx ↦ hRB_sub (mem_image_of_mem φd hx))
      have hSB_sum : B.card + (R.card - 1) * q + ∑ i : Fin (k' + 1), (A_sub i).card ≤ S.card + k' := by
        rw [← Finset.add_sum_erase R _ hr0_R] at hS_decomp
        rw [← Finset.add_sum_erase R _ hr0_R, hr0_B, zero_add] at hB_decomp
        rw [hS_decomp, hB_decomp]
        have hrest : (∑ r ∈ R.erase r0, (B.filter (fun b ↦ φd b = r)).card) + (R.card - 1) * q ≤
            ∑ r ∈ R.erase r0, (S.filter (fun s ↦ φd s = r)).card := by
          have hcard_erase : (R.erase r0).card = R.card - 1 := card_erase_of_mem hr0_R
          have hsum_q : (∑ r ∈ R.erase r0, (B.filter (fun b ↦ φd b = r)).card) + (R.card - 1) * q =
              ∑ r ∈ R.erase r0, ((B.filter (fun b ↦ φd b = r)).card + q) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, hcard_erase]
          rw [hsum_q]
          exact Finset.sum_le_sum hfib_diff
        omega
      have hCi_bound : ∀ i : Fin (k' + 1),
          (C i).card + q ≤ (A_sub i).card + (C i + subFin H).card := by
        intro i
        let wi := φd (f i)
        let Wi := (C i).image πld
        have hwi_mem : wi ∈ Wi := mem_image.mpr ⟨φl (f i), mem_image_of_mem φl (hf_mem i), hπ_comp (f i)⟩
        have hWi_pos : 1 ≤ Wi.card := card_pos.mpr ⟨wi, hwi_mem⟩
        have hCiH_card : (C i + subFin H).card = Wi.card * q := by
          rw [card_add_subFin (C i) H]
          congr 1
          exact card_image_quot_eq_card_image (QuotientAddGroup.mk' H) πld hπ_iff (C i)
        have hCi_decomp : (C i).card = ∑ w ∈ Wi, ((C i).filter (fun z ↦ πld z = w)).card :=
          Finset.card_eq_sum_card_fiberwise (f := πld) (t := Wi) (fun _ hz ↦ mem_image_of_mem πld hz)
        have hfib_le_q : ∀ w ∈ Wi.erase wi, ((C i).filter (fun z ↦ πld z = w)).card ≤ q := by
          intro w hw
          obtain ⟨z0, hz0_Ci, hz0_eq⟩ := mem_image.mp (mem_erase.mp hw).2
          have hsub : (C i).filter (fun z ↦ πld z = w) ⊆ z0 +ᵥ subFin H := by
            intro z hz
            have hzw : πld z = w := (mem_filter.mp hz).2
            rw [mem_vadd_finset]
            simp only [mem_subFin]
            exact ⟨z - z0, (zmod_val_eq_iff_sub_mem hl hd_dvd hH_iff z z0).mp (hzw.trans hz0_eq.symm), by simp⟩
          simpa [card_vadd_finset] using card_le_card hsub
        have hfib_wi : ((C i).filter (fun z ↦ πld z = wi)).card ≤ (A_sub i).card := by
          have hsub : (C i).filter (fun z ↦ πld z = wi) ⊆ (A_sub i).image φl := by
            intro z hz
            rw [mem_filter] at hz
            obtain ⟨x, hxA, rfl⟩ := mem_image.mp hz.1
            refine mem_image.mpr ⟨x, mem_filter.mpr ⟨hxA, ?_⟩, rfl⟩
            rw [← hπ_comp]; exact hz.2
          exact le_trans (card_le_card hsub) card_image_le
        rw [← Finset.add_sum_erase Wi _ hwi_mem] at hCi_decomp
        have hrest_le : ∑ w ∈ Wi.erase wi, ((C i).filter (fun z ↦ πld z = w)).card ≤ (Wi.card - 1) * q := by
          calc ∑ w ∈ Wi.erase wi, ((C i).filter (fun z ↦ πld z = w)).card
              ≤ ∑ _w ∈ Wi.erase wi, q := Finset.sum_le_sum hfib_le_q
            _ = (Wi.erase wi).card * q := by rw [Finset.sum_const, smul_eq_mul]
            _ = (Wi.card - 1) * q := by rw [card_erase_of_mem hwi_mem]
        rw [hCiH_card]
        have hmul_sub : (Wi.card - 1) * q + q = Wi.card * q := by
          cases hW : Wi.card with
          | zero => omega
          | succ n => simp [Nat.succ_mul]
        omega
      have hCi_sum : ∑ i : Fin (k' + 1), (C i).card + (k' + 1) * q ≤
          ∑ i : Fin (k' + 1), (A_sub i).card + ∑ i : Fin (k' + 1), (C i + subFin H).card := by
        have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hCi_bound i
        simpa [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using hsum
      have hk_multi := kneser_multi (k' + 1) (by omega) C hC_ne
      change ∑ i : Fin (k' + 1), (C i + subFin H).card ≤ (sumFinset C).card + (k' + 1 - 1) * q at hk_multi
      rw [hCS_card, Nat.add_sub_cancel] at hk_multi
      have hR_pos : 1 ≤ R.card := by
        have hS0 : 0 ∈ S := (mem_sumFinset_iff A 0).mpr ⟨fun _ ↦ 0, fun i ↦ h0 i, by simp⟩
        exact card_pos.mpr ⟨φd 0, mem_image_of_mem φd hS0⟩
      have hR_mul : (R.card - 1) * q + q = R.card * q := by
        cases hRc : R.card with
        | zero => omega
        | succ n => simp [Nat.succ_mul]
      have hC_vs_Asub : ∑ i : Fin (k' + 1), (C i).card ≤
          ∑ i : Fin (k' + 1), (A_sub i).card + (R.card - 1) * q := by
        nlinarith
      have hsum_eq : ∑ i : Fin (k' + 1), (C i).card = ∑ i : Fin (k' + 1), ((A i).erase l).card :=
        Finset.sum_congr rfl fun i _ ↦ hC_card i
      have hBC : B.card + ∑ i : Fin (k' + 1), (C i).card ≤ S.card + k' := by linarith
      rw [hsum_eq] at hBC
      have : min l (∑ i : Fin (k' + 1), ((A i).erase l).card - k') ≤
          ∑ i : Fin (k' + 1), ((A i).erase l).card - k' := min_le_right _ _
      omega

end LevThm5

section Lev2010

open Finset Classical
open scoped Pointwise

private lemma sumFinset_perm {k : ℕ} (A : Fin k → Finset ℕ) (σ : Equiv.Perm (Fin k)) :
    sumFinset (fun i ↦ A (σ i)) = sumFinset A := by
  ext x
  rw [mem_sumFinset_iff, mem_sumFinset_iff]
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨fun j ↦ f (σ.symm j), fun j ↦ ?_, ?_⟩
    · simpa using hf (σ.symm j)
    · rw [← Equiv.sum_comp σ.symm f]
  · rintro ⟨g, hg, rfl⟩
    exact ⟨fun i ↦ g (σ i), fun i ↦ hg (σ i), Equiv.sum_comp σ g⟩

private lemma exists_perm_monotone : ∀ (k : ℕ) (f : Fin k → ℕ),
    ∃ σ : Equiv.Perm (Fin k), Monotone (fun i ↦ f (σ i))
  | 0, f => ⟨Equiv.refl _, fun a ↦ Fin.elim0 a⟩
  | k + 1, f => by
      obtain ⟨m, _, hm_max⟩ :=
        Finset.exists_max_image (Finset.univ : Finset (Fin (k + 1))) f Finset.univ_nonempty
      let τ : Equiv.Perm (Fin (k + 1)) := Equiv.swap m (Fin.last k)
      have hτ_last : ∀ i : Fin (k + 1), f (τ i) ≤ f (τ (Fin.last k)) := by
        intro i
        rw [Equiv.swap_apply_right]
        exact hm_max (τ i) (mem_univ _)
      let f' : Fin k → ℕ := fun i ↦ f (τ i.castSucc)
      obtain ⟨σ', hσ'⟩ := exists_perm_monotone k f'
      let σ0 : Equiv.Perm (Fin (k + 1)) :=
        { toFun := Fin.lastCases (Fin.last k) (fun i ↦ (σ' i).castSucc)
          invFun := Fin.lastCases (Fin.last k) (fun i ↦ (σ'.symm i).castSucc)
          left_inv := fun i ↦ by
            refine Fin.lastCases ?_ ?_ i
            · simp
            · intro j; simp
          right_inv := fun i ↦ by
            refine Fin.lastCases ?_ ?_ i
            · simp
            · intro j; simp }
      refine ⟨τ * σ0, fun a b hab ↦ ?_⟩
      dsimp only [Equiv.Perm.coe_mul, Function.comp_apply]
      rcases eq_or_lt_of_le (Fin.le_last b) with rfl | hb_lt
      · have hσ0_last : σ0 (Fin.last k) = Fin.last k := by
          dsimp only [σ0, Equiv.coe_fn_mk]
          exact Fin.lastCases_last
        rw [hσ0_last]
        exact hτ_last _
      · let jb : Fin k := ⟨b.val, hb_lt⟩
        let ja : Fin k := ⟨a.val, lt_of_le_of_lt hab hb_lt⟩
        have ha_eq : a = ja.castSucc := Fin.ext rfl
        have hb_eq : b = jb.castSucc := Fin.ext rfl
        have hjab : ja ≤ jb := hab
        rw [ha_eq, hb_eq]
        simp only [σ0, Equiv.coe_fn_mk, Fin.lastCases_castSucc]
        exact hσ' hjab

private lemma exists_perm_antitone (k : ℕ) (f : Fin k → ℕ) :
    ∃ σ : Equiv.Perm (Fin k), Antitone (fun i ↦ f (σ i)) := by
  obtain ⟨σ, hσ⟩ := exists_perm_monotone k f
  let rev : Equiv.Perm (Fin k) :=
    { toFun := Fin.rev
      invFun := Fin.rev
      left_inv := Fin.rev_rev
      right_inv := Fin.rev_rev }
  refine ⟨σ * rev, fun a b hab ↦ ?_⟩
  exact hσ (Fin.rev_le_rev.mpr hab)

private lemma sumFinset_max {k : ℕ} (A : Fin k → Finset ℕ) (hA : ∀ i, (A i).Nonempty) :
    (sumFinset A).max' (sumFinset_nonempty A hA) = ∑ i : Fin k, (A i).max' (hA i) := by
  induction k with
  | zero =>
    have heq : sumFinset A = {0} := rfl
    simp [heq]
  | succ k ih =>
    let Aprev : Fin k → Finset ℕ := fun i ↦ A i.castSucc
    have hprev : ∀ i, (Aprev i).Nonempty := fun i ↦ hA i.castSucc
    have ih' := ih Aprev hprev
    have hS : sumFinset A = sumFinset Aprev + A (Fin.last k) := rfl
    let m1 := (sumFinset Aprev).max' (sumFinset_nonempty Aprev hprev)
    let m2 := (A (Fin.last k)).max' (hA (Fin.last k))
    have hm_mem : m1 + m2 ∈ sumFinset A := by
      rw [hS]
      exact mem_add.mpr ⟨m1, max'_mem _ _, m2, max'_mem _ _, rfl⟩
    have hm_le : ∀ x ∈ sumFinset A, x ≤ m1 + m2 := by
      intro x hx
      rw [hS] at hx
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_add.mp hx
      exact Nat.add_le_add (le_max' _ _ hu) (le_max' _ _ hv)
    have hmax : (sumFinset A).max' (sumFinset_nonempty A hA) = m1 + m2 :=
      le_antisymm (max'_le _ _ _ hm_le) (le_max' _ _ hm_mem)
    rw [hmax, Fin.sum_univ_castSucc]
    dsimp [m1, m2] at ih' ⊢
    rw [ih']

private lemma lev_lemma1 {L₁ L₂ : ℕ} {S₁ S₂ : Finset ℕ}
    (hS1 : S₁ ⊆ Finset.Icc 0 L₁) (hS2 : S₂ ⊆ Finset.Icc 0 L₂)
    (hmax : max L₁ L₂ + 2 ≤ S₁.card + S₂.card) :
    ∀ g ∈ Finset.Icc (L₁ + L₂ + 2 - (S₁.card + S₂.card)) (S₁.card + S₂.card - 2),
      g ∈ S₁ + S₂ := by
  intro g hg
  rw [mem_Icc] at hg
  have hS1_le : S₁.card ≤ L₁ + 1 := by simpa [Nat.card_Icc] using card_le_card hS1
  have hS2_le : S₂.card ≤ L₂ + 1 := by simpa [Nat.card_Icc] using card_le_card hS2
  let I := Finset.Icc (g - L₂) (min g L₁)
  have hI_card : I.card = min g L₁ + 1 - (g - L₂) := by
    rw [Nat.card_Icc]
  let B1 := I.filter (· ∉ S₁)
  let B2 := I.filter (fun a ↦ g - a ∉ S₂)
  have hB1_sub : B1 ⊆ Finset.Icc 0 L₁ \ S₁ := by
    intro a ha
    rw [mem_filter, mem_Icc] at ha
    rw [mem_sdiff, mem_Icc]
    exact ⟨⟨Nat.zero_le a, le_trans ha.1.2 (min_le_right g L₁)⟩, ha.2⟩
  have hB1_le : B1.card ≤ L₁ + 1 - S₁.card := by
    have hle := card_le_card hB1_sub
    rwa [card_sdiff_of_subset hS1, Nat.card_Icc] at hle
  have hB2_im : B2.image (fun a ↦ g - a) ⊆ Finset.Icc 0 L₂ \ S₂ := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    rw [mem_filter, mem_Icc] at ha
    rw [mem_sdiff, mem_Icc]
    refine ⟨⟨Nat.zero_le _, ?_⟩, ha.2⟩
    omega
  have hB2_inj : Set.InjOn (fun a ↦ g - a) B2 := by
    intro a₁ ha₁ a₂ ha₂ h12
    rw [mem_coe, mem_filter, mem_Icc] at ha₁ ha₂
    dsimp only at h12
    have ha1_le : a₁ ≤ g := le_trans ha₁.1.2 (min_le_left g L₁)
    have ha2_le : a₂ ≤ g := le_trans ha₂.1.2 (min_le_left g L₁)
    omega
  have hB2_le : B2.card ≤ L₂ + 1 - S₂.card := by
    rw [← card_image_of_injOn hB2_inj]
    have hle := card_le_card hB2_im
    rwa [card_sdiff_of_subset hS2, Nat.card_Icc] at hle
  have hlt : (B1 ∪ B2).card < I.card := by
    have h1 := card_union_le B1 B2
    omega
  have hsub : B1 ∪ B2 ⊆ I := union_subset (filter_subset _ _) (filter_subset _ _)
  have hpos : 0 < (I \ (B1 ∪ B2)).card := by
    rw [card_sdiff_of_subset hsub]
    omega
  obtain ⟨a, ha⟩ := card_pos.mp hpos
  rw [mem_sdiff, mem_union, not_or, mem_filter, mem_filter, mem_Icc] at ha
  have ha1 : a ∈ S₁ := by
    by_contra h
    exact ha.2.1 ⟨ha.1, h⟩
  have ha2 : g - a ∈ S₂ := by
    by_contra h
    exact ha.2.2 ⟨ha.1, h⟩
  have ha_le : a ≤ g := le_trans ha.1.2 (min_le_left g L₁)
  exact mem_add.mpr ⟨a, ha1, g - a, ha2, Nat.add_sub_of_le ha_le⟩

private noncomputable def rbTerm (D x j : ℕ) : ℤ :=
  2 * min (x : ℤ) (((j : ℤ) + 1) * (D : ℤ)) - (x : ℤ)

private lemma sum_fin_succ_int (m : ℕ) :
    (∑ j : Fin m, ((j.val : ℤ) + 1)) * 2 = (m : ℤ) * ((m : ℤ) + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    push_cast
    rw [add_mul, ih]
    ring

private lemma red_blue_ineq : ∀ n : ℕ, 1 ≤ n →
    (∀ (D X : ℕ) (x : Fin n → ℕ), Monotone x → 1 ≤ D → (∀ j, D ≤ x j) → (∀ j, x j ≤ X) →
      X ≤ n * D → (n : ℤ) * D ≤ ∑ j : Fin n, rbTerm D (x j) j.val) ∧
    (∀ (D X : ℕ) (x : Fin n → ℕ), Monotone x → 1 ≤ D → (∀ j, D ≤ x j) → (∀ j, x j ≤ X) →
      X ≤ (n + 1) * D → ((n : ℤ) + 1) * D - X ≤ ∑ j : Fin n, rbTerm D (x j) j.val) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rcases n with _ | k
    · omega
    rcases k with _ | k'
    · constructor
      · intro D X x _ hD hlow hupp hX
        have hx0 : x 0 = D := le_antisymm (le_trans (hupp 0) (by simpa using hX)) (hlow 0)
        simp [rbTerm, hx0]
        linarith
      · intro D X x _ hD hlow hupp hX
        have hlow0 : (D : ℤ) ≤ x 0 := Nat.cast_le.mpr (hlow 0)
        have hupp0 : (x 0 : ℤ) ≤ X := Nat.cast_le.mpr (hupp 0)
        rw [show ∑ j : Fin (0 + 1), rbTerm D (x j) j.val = rbTerm D (x 0) 0 from Fin.sum_univ_one _]
        dsimp only [rbTerm]
        have h0d : (((0 : ℕ) : ℤ) + 1) * ↑D = ↑D := by ring
        rw [h0d, min_eq_right hlow0]
        push_cast
        linarith
    · let k := k' + 1
      have hk : 1 ≤ k := by omega
      have ih_k := ih k (by omega) hk
      have hP_succ : ∀ (D X : ℕ) (x : Fin (k + 1) → ℕ), Monotone x → 1 ≤ D →
          (∀ j, D ≤ x j) → (∀ j, x j ≤ X) → X ≤ (k + 1) * D →
          ((k + 1 : ℕ) : ℤ) * D ≤ ∑ j : Fin (k + 1), rbTerm D (x j) j.val := by
        intro D X x hmono hD hlow hupp hX
        rw [Fin.sum_univ_castSucc]
        let x' : Fin k → ℕ := fun i ↦ x i.castSucc
        have hmono' : Monotone x' := fun _ _ hab ↦ hmono hab
        have hlow' : ∀ i, D ≤ x' i := fun i ↦ hlow i.castSucc
        have hlast_le : x (Fin.last k) ≤ (k + 1) * D := le_trans (hupp (Fin.last k)) hX
        have hlast_min : min (x (Fin.last k) : ℤ) (((k : ℤ) + 1) * D) = x (Fin.last k) := by
          apply min_eq_left
          exact_mod_cast hlast_le
        have hterm : rbTerm D (x (Fin.last k)) (Fin.last k).val = (x (Fin.last k) : ℤ) := by
          simp only [rbTerm, Fin.val_last]
          rw [hlast_min]
          ring
        rw [hterm]
        by_cases hle_k : x (Fin.last k) ≤ k * D
        · have hupp' : ∀ i : Fin k, x' i ≤ k * D := fun i ↦
            le_trans (hmono (Fin.le_last i.castSucc)) hle_k
          have hpre := ih_k.1 D (k * D) x' hmono' hD hlow' hupp' le_rfl
          have hlow_last : (D : ℤ) ≤ x (Fin.last k) := Nat.cast_le.mpr (hlow (Fin.last k))
          change ((k : ℤ) + 1) * ↑D ≤ (∑ i : Fin k, rbTerm D (x' i) i.val) + ↑(x (Fin.last k))
          linarith
        · have hupp' : ∀ i : Fin k, x' i ≤ x (Fin.last k) := fun i ↦ hmono (Fin.le_last i.castSucc)
          have hpre := ih_k.2 D (x (Fin.last k)) x' hmono' hD hlow' hupp' hlast_le
          change ((k : ℤ) + 1) * ↑D ≤ (∑ i : Fin k, rbTerm D (x' i) i.val) + ↑(x (Fin.last k))
          linarith
      refine ⟨hP_succ, fun D X x hmono hD hlow hupp hX ↦ ?_⟩
      have hgoal_rw : (((k' + 1 + 1 : ℕ) : ℤ) + 1) * ↑D - ↑X = ((k : ℤ) + 2) * ↑D - ↑X := by
        dsimp [k]; ring
      rw [hgoal_rw]
      let blue := (Finset.univ : Finset (Fin (k + 1))).filter (fun j ↦ x j ≤ (j.val + 1) * D)
      by_cases hblue : blue.Nonempty
      · let s := blue.max' hblue
        have hs_mem : s ∈ blue := max'_mem blue hblue
        have hs_le : x s ≤ (s.val + 1) * D := (mem_filter.mp hs_mem).2
        by_cases hs_last : s = Fin.last k
        · rw [hs_last] at hs_le
          have hle_all : ∀ j : Fin (k + 1), x j ≤ (k + 1) * D := fun j ↦
            le_trans (hmono (Fin.le_last j)) (by simpa using hs_le)
          have hP := hP_succ D ((k + 1) * D) x hmono hD hlow hle_all le_rfl
          have hDX : (D : ℤ) ≤ X := Nat.cast_le.mpr (le_trans (hlow 0) (hupp 0))
          have hP' : ((k : ℤ) + 1) * ↑D ≤ ∑ j, rbTerm D (x j) ↑j := by
            push_cast at hP; exact hP
          linarith
        · have hs_lt : s.val < k := lt_of_le_of_ne (Fin.is_le s) (fun heq ↦ hs_last (Fin.ext heq))
          let s1 := s.val + 1
          have hs1_pos : 1 ≤ s1 := by omega
          have hs1_le : s1 ≤ k := by omega
          have hsplit : ∑ j : Fin (k + 1), rbTerm D (x j) j.val =
              (∑ j ∈ (Finset.univ : Finset (Fin (k + 1))).filter (fun j ↦ j.val < s1),
                rbTerm D (x j) j.val) +
              (∑ j ∈ (Finset.univ : Finset (Fin (k + 1))).filter (fun j ↦ ¬ j.val < s1),
                rbTerm D (x j) j.val) :=
            (Finset.sum_filter_add_sum_filter_not _ _ _).symm
          rw [hsplit]
          let x_pre : Fin s1 → ℕ := fun i ↦ x ⟨i.val, by omega⟩
          have hpre_eq : ∑ j ∈ (Finset.univ : Finset (Fin (k + 1))).filter (fun j ↦ j.val < s1),
              rbTerm D (x j) j.val = ∑ i : Fin s1, rbTerm D (x_pre i) i.val := by
            refine (Finset.sum_bij (fun (i : Fin s1) _ ↦ (⟨i.val, by omega⟩ : Fin (k + 1)))
              ?_ ?_ ?_ ?_).symm
            · intro i _; rw [mem_filter]; exact ⟨mem_univ _, i.isLt⟩
            · intro a _ b _ hab; exact Fin.ext (Fin.mk.inj hab)
            · intro j hj
              rw [mem_filter] at hj
              exact ⟨⟨j.val, hj.2⟩, mem_univ _, Fin.ext rfl⟩
            · intro i _; rfl
          have hpre_bound : (s1 : ℤ) * D ≤ ∑ i : Fin s1, rbTerm D (x_pre i) i.val := by
            refine (ih s1 (by omega) hs1_pos).1 D (s1 * D) x_pre
              (fun _ _ hab ↦ hmono hab) hD (fun i ↦ hlow _) ?_ le_rfl
            intro i
            have hi_le : (⟨i.val, by omega⟩ : Fin (k + 1)) ≤ s := by
              change i.val ≤ s.val; omega
            exact le_trans (hmono hi_le) hs_le
          let rest := (Finset.univ : Finset (Fin (k + 1))).filter (fun j ↦ ¬ j.val < s1)
          have hrest_lb : ∀ j ∈ rest, 2 * ((j.val : ℤ) + 1) * D - X ≤ rbTerm D (x j) j.val := by
            intro j hj
            rw [mem_filter] at hj
            have hjs : s < j := by change s.val < j.val; omega
            have hj_nmem : j ∉ blue := fun hmem ↦ (not_le_of_gt hjs) (le_max' blue j hmem)
            rw [mem_filter] at hj_nmem
            have hgt : (j.val + 1) * D < x j := by
              by_contra hle
              exact hj_nmem ⟨mem_univ _, not_lt.mp hle⟩
            have hmin : min (x j : ℤ) (((j.val : ℤ) + 1) * D) = ((j.val : ℤ) + 1) * D := by
              apply min_eq_right
              exact_mod_cast hgt.le
            have hx_le : (x j : ℤ) ≤ X := Nat.cast_le.mpr (hupp j)
            simp only [rbTerm]
            rw [hmin]
            linarith
          have hrest_sum : ∑ j ∈ rest, (2 * ((j.val : ℤ) + 1) * D - X) ≤
              ∑ j ∈ rest, rbTerm D (x j) j.val := Finset.sum_le_sum hrest_lb
          have hrest_card : rest.card = k + 1 - s1 := by
            have h1 : ((Finset.univ : Finset (Fin (k + 1))).filter (fun j ↦ j.val < s1)).card +
                rest.card = (Finset.univ : Finset (Fin (k + 1))).card :=
              Finset.card_filter_add_card_filter_not (fun j : Fin (k + 1) ↦ j.val < s1)
            have hpre_c : ((Finset.univ : Finset (Fin (k + 1))).filter (fun j ↦ j.val < s1)).card = s1 := by
              calc ((Finset.univ : Finset (Fin (k + 1))).filter (fun j ↦ j.val < s1)).card
                  = (Finset.univ : Finset (Fin s1)).card := by
                    refine (Finset.card_bij (fun (i : Fin s1) _ ↦ (⟨i.val, by omega⟩ : Fin (k + 1)))
                      ?_ ?_ ?_).symm
                    · intro i _; rw [mem_filter]; exact ⟨mem_univ _, i.isLt⟩
                    · intro a _ b _ hab; exact Fin.ext (Fin.mk.inj hab)
                    · intro j hj; rw [mem_filter] at hj; exact ⟨⟨j.val, hj.2⟩, mem_univ _, Fin.ext rfl⟩
                _ = s1 := by simp
            change ((Finset.univ : Finset (Fin (k + 1))).filter (fun j ↦ j.val < s1)).card + rest.card =
              (Finset.univ : Finset (Fin (k + 1))).card at h1
            rw [hpre_c, Finset.card_univ, Fintype.card_fin] at h1
            omega
          have hsum_j : ∑ j ∈ rest, ((j.val : ℤ) + 1) * 2 =
              ((k : ℤ) + 1) * ((k : ℤ) + 2) - (s1 : ℤ) * ((s1 : ℤ) + 1) := by
            have htot := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin (k + 1)))
              (fun j ↦ j.val < s1) (fun j ↦ ((j.val : ℤ) + 1) * 2)
            have htot_rhs : ∑ j : Fin (k + 1), ((j.val : ℤ) + 1) * 2 =
                ((k : ℤ) + 1) * ((k : ℤ) + 2) := by
              rw [← Finset.sum_mul, sum_fin_succ_int (k + 1)]
              push_cast
              ring
            have hpre_j : ∑ j ∈ (Finset.univ : Finset (Fin (k + 1))).filter (fun j ↦ j.val < s1),
                ((j.val : ℤ) + 1) * 2 = (s1 : ℤ) * ((s1 : ℤ) + 1) := by
              have hbij : ∑ j ∈ (Finset.univ : Finset (Fin (k + 1))).filter (fun j ↦ j.val < s1),
                  ((j.val : ℤ) + 1) * 2 = ∑ i : Fin s1, ((i.val : ℤ) + 1) * 2 := by
                refine (Finset.sum_bij (fun (i : Fin s1) _ ↦ (⟨i.val, by omega⟩ : Fin (k + 1)))
                  ?_ ?_ ?_ ?_).symm
                · intro i _; rw [mem_filter]; exact ⟨mem_univ _, i.isLt⟩
                · intro a _ b _ hab; exact Fin.ext (Fin.mk.inj hab)
                · intro j hj; rw [mem_filter] at hj; exact ⟨⟨j.val, hj.2⟩, mem_univ _, Fin.ext rfl⟩
                · intro i _; rfl
              rw [hbij, ← Finset.sum_mul, sum_fin_succ_int s1]
            change _ + ∑ j ∈ rest, ((j.val : ℤ) + 1) * 2 = _ at htot
            rw [hpre_j, htot_rhs] at htot
            linarith
          have hrest_eval : ∑ j ∈ rest, (2 * ((j.val : ℤ) + 1) * D - X) =
              (((k : ℤ) + 1) * ((k : ℤ) + 2) - (s1 : ℤ) * ((s1 : ℤ) + 1)) * D -
                ((k + 1 - s1 : ℕ) : ℤ) * X := by
            rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hrest_card]
            have hmul : ∑ j ∈ rest, 2 * ((j.val : ℤ) + 1) * D =
                (∑ j ∈ rest, ((j.val : ℤ) + 1) * 2) * D := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ ↦ ?_
              ring
            rw [hmul, hsum_j]
          have hX_le : (X : ℤ) ≤ ((k : ℤ) + 2) * D := by exact_mod_cast hX
          have hD_pos : (1 : ℤ) ≤ D := by exact_mod_cast hD
          have hk_pos : (1 : ℤ) ≤ k := by exact_mod_cast hk
          have hs1_ge : (1 : ℤ) ≤ s1 := by exact_mod_cast hs1_pos
          have hs1_le_z : (s1 : ℤ) ≤ k := by exact_mod_cast hs1_le
          have hr_eq : ((k + 1 - s1 : ℕ) : ℤ) = (k : ℤ) + 1 - s1 := by omega
          rw [hpre_eq]
          rw [hrest_eval, hr_eq] at hrest_sum
          change ((k : ℤ) + 2) * ↑D - ↑X ≤
            (∑ i : Fin s1, rbTerm D (x_pre i) i.val) + ∑ j ∈ rest, rbTerm D (x j) j.val
          have h_nonneg1 : (0 : ℤ) ≤ ((k : ℤ) - s1) * (((k : ℤ) + 2) * D - X) :=
            mul_nonneg (by linarith) (by linarith)
          have h_nonneg2 : (0 : ℤ) ≤ (s1 : ℤ) * ((k : ℤ) + 2 - s1) * D :=
            mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
          have hid : (s1 : ℤ) * D + (((k : ℤ) + 1) * ((k : ℤ) + 2) - (s1 : ℤ) * ((s1 : ℤ) + 1)) * D -
              ((k : ℤ) + 1 - s1) * X - (((k : ℤ) + 2) * D - X) =
              ((k : ℤ) - s1) * (((k : ℤ) + 2) * D - X) + (s1 : ℤ) * ((k : ℤ) + 2 - s1) * D := by ring
          linarith
      · have hall_gt : ∀ j : Fin (k + 1), (j.val + 1) * D < x j := by
          intro j
          by_contra hle
          exact hblue ⟨j, mem_filter.mpr ⟨mem_univ j, not_lt.mp hle⟩⟩
        have hlb : ∀ j : Fin (k + 1), 2 * ((j.val : ℤ) + 1) * D - X ≤ rbTerm D (x j) j.val := by
          intro j
          have hmin : min (x j : ℤ) (((j.val : ℤ) + 1) * D) = ((j.val : ℤ) + 1) * D := by
            apply min_eq_right
            exact_mod_cast (hall_gt j).le
          have hx_le : (x j : ℤ) ≤ X := Nat.cast_le.mpr (hupp j)
          simp only [rbTerm]
          rw [hmin]
          linarith
        have hsum_lb := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ hlb j
        have hsum_eval : ∑ j : Fin (k + 1), (2 * ((j.val : ℤ) + 1) * D - X) =
            ((k : ℤ) + 1) * ((k : ℤ) + 2) * D - ((k : ℤ) + 1) * X := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hmul : ∑ j : Fin (k + 1), 2 * ((j.val : ℤ) + 1) * D =
              (∑ j : Fin (k + 1), ((j.val : ℤ) + 1) * 2) * D := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            ring
          rw [hmul, ← Finset.sum_mul, sum_fin_succ_int (k + 1)]
          push_cast
          ring
        rw [hsum_eval] at hsum_lb
        have hX_le : (X : ℤ) ≤ ((k : ℤ) + 2) * D := by exact_mod_cast hX
        have hD_pos : (1 : ℤ) ≤ D := by exact_mod_cast hD
        have hk_pos : (1 : ℤ) ≤ k := by exact_mod_cast hk
        nlinarith

private lemma lev_prop1 (k l m : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) (hm : 3 ≤ m)
    (A : Fin k → Finset ℕ)
    (h0 : ∀ i, 0 ∈ A i)
    (hcard : ∀ i, m ≤ (A i).card)
    (hle : ∀ i, ∀ x ∈ A i, x ≤ l)
    (hcop : ∀ i, ∀ d : ℕ, 1 < d → ¬ ∀ x ∈ A i, d ∣ x)
    (hl_bound : l - 1 ≤ (k + 1) * (m - 2)) :
    let S := sumFinset A
    let lS := S.max' (sumFinset_nonempty A (fun i ↦ ⟨0, h0 i⟩))
    ((lS : ℤ) + (k + 1) * (m - 1) - l + 2 ≤ 2 * (S.card : ℤ)) ∧
    (l - 1 ≤ k * (m - 2) → (lS : ℤ) + k * (m - 1) + 2 ≤ 2 * (S.card : ℤ)) := by
  intro S lS
  let li0 : Fin k → ℕ := fun i ↦ (A i).max' ⟨0, h0 i⟩
  obtain ⟨σ, hσ⟩ := exists_perm_monotone k li0
  let B : Fin k → Finset ℕ := fun i ↦ A (σ i)
  have hB0 : ∀ i, 0 ∈ B i := fun i ↦ h0 (σ i)
  have hBcard : ∀ i, m ≤ (B i).card := fun i ↦ hcard (σ i)
  have hBle : ∀ i, ∀ x ∈ B i, x ≤ l := fun i x hx ↦ hle (σ i) x hx
  have hBcop : ∀ i, ∀ d : ℕ, 1 < d → ¬ ∀ x ∈ B i, d ∣ x := fun i ↦ hcop (σ i)
  have hBS : sumFinset B = S := sumFinset_perm A σ
  let li : Fin k → ℕ := fun i ↦ (B i).max' ⟨0, hB0 i⟩
  have hli_mono : Monotone li := hσ
  have hli_ge : ∀ i, m - 1 ≤ li i := fun i ↦ by
    have hsub : B i ⊆ Finset.Icc 0 (li i) := fun x hx ↦ mem_Icc.mpr ⟨Nat.zero_le _, le_max' _ _ hx⟩
    have hc := card_le_card hsub
    rw [Nat.card_Icc] at hc
    have hci := hBcard i
    omega
  have hli_le : ∀ i, li i ≤ l := fun i ↦ hBle i (li i) (max'_mem _ _)
  have hlS_eq : lS = ∑ i : Fin k, li i := by
    have hmax := sumFinset_max B (fun i ↦ ⟨0, hB0 i⟩)
    simp only [hBS] at hmax
    exact hmax
  have hpref : ∀ n : ℕ, 1 ≤ n → ∀ hn : n ≤ k,
      1 + ∑ j : Fin n, (min (li ⟨j.val, by omega⟩ - 1) ((j.val + 1) * (m - 2)) + 1) ≤
        (sumFinset (fun j : Fin n ↦ B ⟨j.val, by omega⟩)).card := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro hn1
      have hsum1 : sumFinset (fun j : Fin 1 ↦ B ⟨j.val, by omega⟩) = B ⟨0, by omega⟩ := by
        have heq : sumFinset (fun j : Fin 1 ↦ B ⟨j.val, by omega⟩) = {0} + B ⟨0, by omega⟩ := rfl
        rw [heq, singleton_add, zero_vadd]
      rw [hsum1, Fin.sum_univ_one]
      have hge0 := hli_ge ⟨0, by omega⟩
      have hcard0 := hBcard ⟨0, by omega⟩
      have h1 : (0 + 1) * (m - 2) = m - 2 := one_mul _
      have h2 : m - 2 ≤ li ⟨0, by omega⟩ - 1 := by omega
      simp only [Fin.val_zero]
      rw [h1, min_eq_right h2]
      omega
    | succ n hn ih =>
      intro hn1
      have ih' := ih (by omega)
      let Bi : Fin (n + 1) → Finset ℕ := fun j ↦ B ⟨j.val, by omega⟩
      let ln := li ⟨n, by omega⟩
      have hln_pos : 0 < ln := by have := hli_ge ⟨n, by omega⟩; omega
      have hBi_le : ∀ j, ∀ x ∈ Bi j, x ≤ ln := fun j x hx ↦
        le_trans (le_max' (Bi j) x hx) (hli_mono (by change j.val ≤ n; omega))
      have hthm := lev_thm5 n hn ln hln_pos Bi (fun j ↦ hB0 _) hBi_le
        (max'_mem (B ⟨n, by omega⟩) ⟨0, hB0 _⟩) (hBcop ⟨n, by omega⟩)
      dsimp only at hthm
      have hsum_er : (n + 1) * (m - 2) + 1 ≤ ∑ j : Fin (n + 1), ((Bi j).erase ln).card - n := by
        have h_each : ∀ j : Fin (n + 1), m - 1 ≤ ((Bi j).erase ln).card := fun j ↦ by
          have hle1 : (Bi j).card - 1 ≤ ((Bi j).erase ln).card := by
            by_cases hmem : ln ∈ Bi j
            · rw [card_erase_of_mem hmem]
            · rw [erase_eq_of_notMem hmem]; omega
          have hcj : m ≤ (Bi j).card := hBcard ⟨j.val, by omega⟩
          omega
        have hsum_ge := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ h_each j
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum_ge
        have hm_sub : m - 1 = (m - 2) + 1 := by omega
        have : (n + 1) * (m - 2) + 1 + n = (n + 1) * (m - 1) := by rw [hm_sub]; ring
        omega
      have hmin_le : min (ln - 1) ((n + 1) * (m - 2)) + 1 ≤
          min ln (∑ j : Fin (n + 1), ((Bi j).erase ln).card - n) := by
        omega
      rw [Fin.sum_univ_castSucc]
      have heq1 : ∑ j : Fin n, (min (li ⟨j.castSucc.val, by omega⟩ - 1) ((j.castSucc.val + 1) * (m - 2)) + 1) =
          ∑ j : Fin n, (min (li ⟨j.val, by omega⟩ - 1) ((j.val + 1) * (m - 2)) + 1) := rfl
      have heq2 : (li ⟨(Fin.last n).val, by omega⟩ - 1) = ln - 1 := rfl
      have heq3 : ((Fin.last n).val + 1) * (m - 2) = (n + 1) * (m - 2) := rfl
      change 1 + ((∑ j : Fin n, (min (li ⟨j.castSucc.val, by omega⟩ - 1) ((j.castSucc.val + 1) * (m - 2)) + 1)) +
        (min (li ⟨(Fin.last n).val, by omega⟩ - 1) (((Fin.last n).val + 1) * (m - 2)) + 1)) ≤ (sumFinset Bi).card
      rw [heq1, heq2, heq3]
      have hS_prev : sumFinset (fun j : Fin n ↦ Bi j.castSucc) =
          sumFinset (fun j : Fin n ↦ B ⟨j.val, by omega⟩) := rfl
      rw [hS_prev] at hthm
      omega
  have hS_lb := hpref k hk le_rfl
  have hS_eq : sumFinset (fun j : Fin k ↦ B ⟨j.val, by omega⟩) = S := by
    rw [← hBS]
  rw [hS_eq] at hS_lb
  let x : Fin k → ℕ := fun i ↦ li i - 1
  have hx_mono : Monotone x := fun _ _ hab ↦ Nat.sub_le_sub_right (hli_mono hab) 1
  have hm2 : 1 ≤ m - 2 := by omega
  have hx_low : ∀ i, m - 2 ≤ x i := fun i ↦ by have := hli_ge i; dsimp only [x]; omega
  have hx_upp : ∀ i, x i ≤ l - 1 := fun i ↦ by have := hli_le i; dsimp only [x]; omega
  have hS_int : (2 : ℤ) + (k : ℤ) + ∑ j : Fin k, rbTerm (m - 2) (x j) j.val ≤ 2 * (S.card : ℤ) - lS := by
    have h_nat : 2 + 2 * k + 2 * ∑ j : Fin k, min (x j) ((j.val + 1) * (m - 2)) ≤ 2 * S.card := by
      have h_eq : ∑ j : Fin k, (min (li ⟨j.val, j.isLt⟩ - 1) ((j.val + 1) * (m - 2)) + 1) =
          (∑ j : Fin k, min (x j) ((j.val + 1) * (m - 2))) + k := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      rw [h_eq] at hS_lb
      omega
    have h1' : (2 : ℤ) + 2 * (k : ℤ) + 2 * ∑ j : Fin k, min (x j : ℤ) (((j.val : ℤ) + 1) * ((m - 2 : ℕ) : ℤ)) ≤
        2 * (S.card : ℤ) := by
      have hz := Int.ofNat_le.mpr h_nat
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sum, Nat.cast_min, Nat.cast_ofNat, Nat.cast_one] at hz
      exact hz
    have hlS_int : (lS : ℤ) = (k : ℤ) + ∑ j : Fin k, (x j : ℤ) := by
      rw [hlS_eq]
      push_cast
      have hsum_1 : ∑ j : Fin k, (li j : ℤ) = ∑ j : Fin k, ((x j : ℤ) + 1) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        have hpos := hli_ge j
        dsimp only [x]
        omega
      rw [hsum_1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      ring
    rw [hlS_int]
    have hsum_rb : ∑ j : Fin k, rbTerm (m - 2) (x j) j.val =
        2 * ∑ j : Fin k, min (x j : ℤ) (((j.val : ℤ) + 1) * ((m - 2 : ℕ) : ℤ)) - ∑ j : Fin k, (x j : ℤ) := by
      simp only [rbTerm, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hsum_rb]
    linarith
  have hrb := red_blue_ineq k hk
  constructor
  · have hQ := hrb.2 (m - 2) (l - 1) x hx_mono hm2 hx_low hx_upp hl_bound
    have hm1 : ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 := by omega
    have hl1 : ((l - 1 : ℕ) : ℤ) = (l : ℤ) - 1 := by omega
    rw [hm1, hl1] at hQ
    linarith
  · intro hl_bound2
    have hP := hrb.1 (m - 2) (l - 1) x hx_mono hm2 hx_low hx_upp hl_bound2
    have hm1 : ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 := by omega
    rw [hm1] at hP
    linarith

private lemma extend_interval {B X : Finset ℕ} {a b lX : ℕ}
    (hab : a ≤ b) (hB : Finset.Icc a b ⊆ B)
    (h0 : 0 ∈ X) (hl : lX ∈ X) (hl_le : lX ≤ b - a + 1) :
    Finset.Icc a (b + lX) ⊆ B + X := by
  intro t ht
  rw [mem_Icc] at ht
  by_cases htb : t ≤ b
  · exact mem_add.mpr ⟨t, hB (mem_Icc.mpr ⟨ht.1, htb⟩), 0, h0, add_zero t⟩
  · have h_lo : a ≤ t - lX := by omega
    have h_hi : t - lX ≤ b := by omega
    exact mem_add.mpr ⟨t - lX, hB (mem_Icc.mpr ⟨h_lo, h_hi⟩), lX, hl, Nat.sub_add_cancel (by omega)⟩

private lemma even_odd_sumFinset : ∀ (κ : ℕ) (C : Fin (2 * κ + 1) → Finset ℕ),
    sumFinset C =
      sumFinset (fun i : Fin (κ + 1) ↦ C ⟨2 * i.val, by omega⟩) +
      sumFinset (fun i : Fin κ ↦ C ⟨2 * i.val + 1, by omega⟩)
  | 0, C => by
      have hL : sumFinset C = C 0 := by
        have h1 : sumFinset C = ({0} : Finset ℕ) + C 0 := rfl
        rw [h1, singleton_add, zero_vadd]
      have hR1 : sumFinset (fun i : Fin 1 ↦ C ⟨2 * i.val, by omega⟩) = C 0 := by
        have h1 : sumFinset (fun i : Fin 1 ↦ C ⟨2 * i.val, by omega⟩) =
            ({0} : Finset ℕ) + C ⟨0, by omega⟩ := rfl
        rw [h1, singleton_add, zero_vadd]; rfl
      have hR2 : sumFinset (fun i : Fin 0 ↦ C ⟨2 * i.val + 1, by omega⟩) = {0} := rfl
      rw [hL, hR1, hR2, add_comm (C 0) {0}, singleton_add, zero_vadd]
  | κ + 1, C => by
      let C0 : Fin (2 * κ + 1) → Finset ℕ := fun i ↦ C ⟨i.val, by omega⟩
      have hL1 : sumFinset C =
          sumFinset (fun i : Fin (2 * κ + 2) ↦ C ⟨i.val, by omega⟩) + C ⟨2 * κ + 2, by omega⟩ := rfl
      have hL2 : sumFinset (fun i : Fin (2 * κ + 2) ↦ C ⟨i.val, by omega⟩) =
          sumFinset C0 + C ⟨2 * κ + 1, by omega⟩ := rfl
      have hR1 : sumFinset (fun i : Fin (κ + 2) ↦ C ⟨2 * i.val, by omega⟩) =
          sumFinset (fun i : Fin (κ + 1) ↦ C0 ⟨2 * i.val, by omega⟩) + C ⟨2 * κ + 2, by omega⟩ := rfl
      have hR2 : sumFinset (fun i : Fin (κ + 1) ↦ C ⟨2 * i.val + 1, by omega⟩) =
          sumFinset (fun i : Fin κ ↦ C0 ⟨2 * i.val + 1, by omega⟩) + C ⟨2 * κ + 1, by omega⟩ := rfl
      rw [hL1, hL2, even_odd_sumFinset κ C0, hR1, hR2]
      let S1 := sumFinset (fun i : Fin (κ + 1) ↦ C0 ⟨2 * i.val, by omega⟩)
      let S2 := sumFinset (fun i : Fin κ ↦ C0 ⟨2 * i.val + 1, by omega⟩)
      let X := C ⟨2 * κ + 1, by omega⟩
      let Y := C ⟨2 * κ + 2, by omega⟩
      change ((S1 + S2) + X) + Y = (S1 + Y) + (S2 + X)
      rw [add_assoc (S1 + S2) X Y, add_comm X Y, ← add_assoc (S1 + S2) Y X,
        add_assoc S1 S2 Y, add_comm S2 Y, ← add_assoc S1 Y S2,
        add_assoc (S1 + Y) S2 X]

private lemma sumFinset_split_last {k : ℕ} (hk : 1 ≤ k) (A : Fin k → Finset ℕ) :
    sumFinset A = sumFinset (fun i : Fin (k - 1) ↦ A ⟨i.val, by omega⟩) + A ⟨k - 1, by omega⟩ := by
  cases k with
  | zero => omega
  | succ k' => rfl

private lemma lev_thm4 (κ lmax m : ℕ) (hm : 3 ≤ m)
    (C : Fin (2 * κ + 1) → Finset ℕ)
    (h0 : ∀ i, 0 ∈ C i)
    (hcard : ∀ i, m ≤ (C i).card)
    (hle : ∀ i, ∀ x ∈ C i, x ≤ lmax)
    (hcop : ∀ i, ∀ d : ℕ, 1 < d → ¬ ∀ x ∈ C i, d ∣ x)
    (hanti : ∀ i j : Fin (2 * κ + 1), i ≤ j →
      (C j).max' ⟨0, h0 j⟩ ≤ (C i).max' ⟨0, h0 i⟩)
    (hlmax_ge : m - 1 ≤ lmax)
    (hκ_upp : lmax - 1 ≤ (κ + 1) * (m - 2)) :
    ∃ a b : ℕ, a ≤ b ∧ Finset.Icc a b ⊆ sumFinset C ∧
      2 * (κ + 1) * (m - 1) + a ≤ b + lmax ∧ lmax ≤ b - a + 1 := by
  by_cases hκ0 : κ = 0
  · have hlmax_eq : lmax = m - 1 := by
      rw [hκ0, zero_add, one_mul] at hκ_upp
      omega
    have hC0_eq : C ⟨0, by omega⟩ = Finset.Icc 0 (m - 1) := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hlmax_eq ▸ hle _ x hx⟩
      · rw [Nat.card_Icc]
        have hc0 := hcard ⟨0, by omega⟩
        omega
    have hT_eq : sumFinset C = Finset.Icc 0 (m - 1) := by
      rw [← hC0_eq]
      ext x
      rw [mem_sumFinset_iff]
      constructor
      · rintro ⟨f, hf, rfl⟩
        have heq_f : ∑ i : Fin (2 * κ + 1), f i = f ⟨0, by omega⟩ := by
          have : ∀ i : Fin (2 * κ + 1), i = ⟨0, by omega⟩ := fun i ↦ Fin.ext (by omega)
          calc ∑ i : Fin (2 * κ + 1), f i = ∑ _i : Fin (2 * κ + 1), f ⟨0, by omega⟩ :=
                Finset.sum_congr rfl fun i _ ↦ by rw [this i]
            _ = f ⟨0, by omega⟩ := by simp [hκ0]
        rw [heq_f]
        exact hf _
      · intro hx
        refine ⟨fun _ ↦ x, fun i ↦ ?_, ?_⟩
        · have hi : i = ⟨0, by omega⟩ := Fin.ext (by omega)
          rw [hi]; exact hx
        · simp [hκ0]
    refine ⟨0, m - 1, Nat.zero_le _, hT_eq ▸ Subset.rfl, ?_, ?_⟩
    · rw [hκ0]; omega
    · omega
  · have hκ1 : 1 ≤ κ := by omega
    let G1 : Fin (κ + 1) → Finset ℕ := fun i ↦ C ⟨2 * i.val, by omega⟩
    let G2 : Fin κ → Finset ℕ := fun i ↦ C ⟨2 * i.val + 1, by omega⟩
    let S1 := sumFinset G1
    let S2 := sumFinset G2
    have hsum_eq : sumFinset C = S1 + S2 := even_odd_sumFinset κ C
    have hG1_0 : ∀ i, 0 ∈ G1 i := fun i ↦ h0 _
    have hG2_0 : ∀ i, 0 ∈ G2 i := fun i ↦ h0 _
    let L1 := S1.max' (sumFinset_nonempty G1 (fun i ↦ ⟨0, hG1_0 i⟩))
    let L2 := S2.max' (sumFinset_nonempty G2 (fun i ↦ ⟨0, hG2_0 i⟩))
    have hS1_sub : S1 ⊆ Finset.Icc 0 L1 := fun x hx ↦ Finset.mem_Icc.mpr ⟨Nat.zero_le _, Finset.le_max' _ _ hx⟩
    have hS2_sub : S2 ⊆ Finset.Icc 0 L2 := fun x hx ↦ Finset.mem_Icc.mpr ⟨Nat.zero_le _, Finset.le_max' _ _ hx⟩
    have hL1_sum : L1 = ∑ i : Fin (κ + 1), (G1 i).max' ⟨0, hG1_0 i⟩ := sumFinset_max G1 _
    have hL2_sum : L2 = ∑ i : Fin κ, (G2 i).max' ⟨0, hG2_0 i⟩ := sumFinset_max G2 _
    have hL2_le_L1 : L2 ≤ L1 := by
      rw [hL1_sum, hL2_sum, Fin.sum_univ_castSucc]
      have hstep : ∑ i : Fin κ, (G2 i).max' ⟨0, hG2_0 i⟩ ≤
          ∑ i : Fin κ, (G1 i.castSucc).max' ⟨0, hG1_0 i.castSucc⟩ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        exact hanti ⟨2 * i.val, by omega⟩ ⟨2 * i.val + 1, by omega⟩ (by change 2 * i.val ≤ 2 * i.val + 1; omega)
      omega
    have hL1_le_L2 : L1 ≤ L2 + lmax := by
      rw [hL1_sum, hL2_sum, Fin.sum_univ_succ]
      have hstep : ∑ i : Fin κ, (G1 i.succ).max' ⟨0, hG1_0 i.succ⟩ ≤
          ∑ i : Fin κ, (G2 i).max' ⟨0, hG2_0 i⟩ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        exact hanti ⟨2 * i.val + 1, by omega⟩ ⟨2 * (i.val + 1), by omega⟩
          (by change 2 * i.val + 1 ≤ 2 * (i.val + 1); omega)
      have h0_le : (G1 0).max' ⟨0, hG1_0 0⟩ ≤ lmax := hle _ _ (Finset.max'_mem _ _)
      omega
    have hlmax_pos : 1 ≤ lmax := by omega
    have hp1 := (lev_prop1 (κ + 1) lmax m (by omega) hlmax_pos hm G1 hG1_0
      (fun i ↦ hcard _) (fun i x hx ↦ hle _ x hx) (fun i ↦ hcop _)
      (le_trans hκ_upp (Nat.mul_le_mul_right (m - 2) (by omega)))).2 hκ_upp
    have hp2 := (lev_prop1 κ lmax m hκ1 hlmax_pos hm G2 hG2_0
      (fun i ↦ hcard _) (fun i x hx ↦ hle _ x hx) (fun i ↦ hcop _) hκ_upp).1
    have hp1' : (L1 : ℤ) + ((κ : ℤ) + 1) * ((m : ℤ) - 1) + 2 ≤ 2 * (S1.card : ℤ) := by
      change (L1 : ℤ) + ((κ + 1 : ℕ) : ℤ) * ((m : ℤ) - 1) + 2 ≤ 2 * (S1.card : ℤ) at hp1
      push_cast at hp1
      exact hp1
    have hp2' : (L2 : ℤ) + ((κ : ℤ) + 1) * ((m : ℤ) - 1) - (lmax : ℤ) + 2 ≤ 2 * (S2.card : ℤ) := hp2
    have hS1_le : S1.card ≤ L1 + 1 := by
      simpa [Nat.card_Icc] using Finset.card_le_card hS1_sub
    have hS2_le : S2.card ≤ L2 + 1 := by
      simpa [Nat.card_Icc] using Finset.card_le_card hS2_sub
    have hm1_nat : lmax + 1 ≤ (κ + 1) * (m - 1) := by
      have hm_sub : m - 1 = (m - 2) + 1 := by omega
      have hmul : (κ + 1) * (m - 1) = (κ + 1) * (m - 2) + (κ + 1) := by
        rw [hm_sub]; ring
      omega
    have hm1_z : (lmax : ℤ) + 1 ≤ ((κ : ℤ) + 1) * ((m : ℤ) - 1) := by
      have hz := Int.ofNat_le.mpr hm1_nat
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_sub (by omega : 1 ≤ m)] at hz
      exact hz
    have hL1L2_z : (L1 : ℤ) ≤ (L2 : ℤ) + (lmax : ℤ) := by exact_mod_cast hL1_le_L2
    have hmax_cond : max L1 L2 + 2 ≤ S1.card + S2.card := by
      have h1 : (L1 : ℤ) + 2 ≤ (S1.card : ℤ) + (S2.card : ℤ) := by linarith
      omega
    let a0_int := L1 + L2 + 2 - (S1.card + S2.card)
    let b0_int := S1.card + S2.card - 2
    have hIcc_int : Finset.Icc a0_int b0_int ⊆ sumFinset C := by
      rw [hsum_eq]
      exact fun g hg ↦ lev_lemma1 hS1_sub hS2_sub hmax_cond g hg
    have ha0_eq : (a0_int : ℤ) = (L1 : ℤ) + L2 + 2 - (S1.card + S2.card) := by omega
    have hb0_eq : (b0_int : ℤ) = (S1.card : ℤ) + S2.card - 2 := by omega
    have hineq_z : 2 * ((κ : ℤ) + 1) * ((m : ℤ) - 1) + (a0_int : ℤ) ≤ (b0_int : ℤ) + (lmax : ℤ) := by
      linarith
    have hlen_z : (lmax : ℤ) ≤ (b0_int : ℤ) - (a0_int : ℤ) + 1 := by linarith
    refine ⟨a0_int, b0_int, by omega, hIcc_int, ?_, ?_⟩
    · have hnat : ((2 * (κ + 1) * (m - 1) + a0_int : ℕ) : ℤ) ≤ ((b0_int + lmax : ℕ) : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_sub (by omega : 1 ≤ m)]
        exact hineq_z
      exact Int.ofNat_le.mp hnat
    · omega

private lemma extend_chain {k : ℕ} (k0 c0 m lmax : ℕ) (hm : 3 ≤ m)
    (A : Fin k → Finset ℕ) (hA0 : ∀ j, 0 ∈ A j) (hAcard : ∀ j, m ≤ (A j).card)
    (hAle : ∀ j, ∀ x ∈ A j, x ≤ lmax) (hk0 : k0 ≤ k)
    (a0 b0 : ℕ) (hab0 : a0 ≤ b0)
    (hsub0 : Finset.Icc a0 b0 ⊆ sumFinset (fun i : Fin k0 ↦ A ⟨i.val, by omega⟩))
    (hineq0 : c0 * (m - 1) + a0 ≤ b0 + lmax) (hlen0 : lmax ≤ b0 - a0 + 1) :
    ∀ n : ℕ, k0 ≤ n → ∀ hn : n ≤ k,
      ∃ a b : ℕ, a ≤ b ∧ Finset.Icc a b ⊆ sumFinset (fun i : Fin n ↦ A ⟨i.val, by omega⟩) ∧
        (c0 + (n - k0)) * (m - 1) + a ≤ b + lmax ∧ lmax ≤ b - a + 1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro _
    refine ⟨a0, b0, hab0, hsub0, ?_, hlen0⟩
    simpa using hineq0
  | succ n hn ih =>
    intro hn1
    obtain ⟨a, b, hab, hsub, hineq, hlen⟩ := ih (by omega)
    let X := A ⟨n, by omega⟩
    have hX0 : 0 ∈ X := hA0 ⟨n, by omega⟩
    let lX := X.max' ⟨0, hX0⟩
    have hlX_ge : m - 1 ≤ lX := by
      have hsubX : X ⊆ Finset.Icc 0 lX := fun x hx ↦ Finset.mem_Icc.mpr ⟨Nat.zero_le _, Finset.le_max' _ _ hx⟩
      have hc := Finset.card_le_card hsubX
      rw [Nat.card_Icc] at hc
      have hXc : m ≤ X.card := hAcard ⟨n, by omega⟩
      omega
    have hlX_le : lX ≤ lmax := hAle ⟨n, by omega⟩ lX (Finset.max'_mem _ _)
    have hext_sub := extend_interval hab hsub hX0 (Finset.max'_mem _ _) (le_trans hlX_le hlen)
    have hS_eq : sumFinset (fun i : Fin (n + 1) ↦ A ⟨i.val, by omega⟩) =
        sumFinset (fun i : Fin n ↦ A ⟨i.val, by omega⟩) + X := rfl
    refine ⟨a, b + lX, by omega, hS_eq ▸ hext_sub, ?_, by omega⟩
    have hmul : (c0 + (n + 1 - k0)) * (m - 1) = (c0 + (n - k0)) * (m - 1) + (m - 1) := by
      rw [show c0 + (n + 1 - k0) = (c0 + (n - k0)) + 1 by omega, Nat.add_mul, one_mul]
    nlinarith

end Lev2010

section Solution
open scoped Pointwise

theorem OMA.solution : OMA.R_Erdos360_erdos_360_R1_H4_R1.H3 := by
  intro ℓ q m hℓ hq hm hbound S hcard hIcc hcop
  have hne : ∀ i, (S i).Nonempty := fun i ↦ Finset.card_pos.mp (by have := hcard i; omega)
  let a0 : Fin ℓ → ℕ := fun i ↦ (S i).min' (hne i)
  let A0 : Fin ℓ → Finset ℕ := fun i ↦ (S i).image (· - a0 i)
  have hA0_0 : ∀ i, 0 ∈ A0 i := fun i ↦ Finset.mem_image.mpr ⟨a0 i, Finset.min'_mem _ _, Nat.sub_self _⟩
  have hA0_card : ∀ i, m ≤ (A0 i).card := fun i ↦ by
    have hinj : Set.InjOn (· - a0 i) (S i) := fun x hx y hy hxy ↦ by
      have hx' : a0 i ≤ x := Finset.min'_le _ _ hx
      have hy' : a0 i ≤ y := Finset.min'_le _ _ hy
      dsimp only at hxy
      omega
    rw [Finset.card_image_of_injOn hinj]
    exact hcard i
  have hA0_le : ∀ i, ∀ x ∈ A0 i, x ≤ q := fun i x hx ↦ by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c, hc⟩ := hIcc i
    have hc1 := Finset.mem_Icc.mp (hc (Finset.min'_mem (S i) (hne i)))
    change c ≤ a0 i ∧ a0 i ≤ c + q at hc1
    have hc2 := Finset.mem_Icc.mp (hc hy)
    omega
  have hA0_cop : ∀ i, ∀ d : ℕ, 1 < d → ¬ ∀ x ∈ A0 i, d ∣ x := by
    intro i d hd hall
    apply hcop i d hd
    intro x hx y hy
    have hx_le : a0 i ≤ x := Finset.min'_le _ _ hx
    have hy_le : a0 i ≤ y := Finset.min'_le _ _ hy
    have hdx : d ∣ x - a0 i := hall _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    have hdy : d ∣ y - a0 i := hall _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    have hxm : x % d = a0 i % d := by
      have : x = a0 i + (x - a0 i) := by omega
      rw [this, Nat.add_mod, Nat.dvd_iff_mod_eq_zero.mp hdx, add_zero, Nat.mod_mod]
    have hym : y % d = a0 i % d := by
      have : y = a0 i + (y - a0 i) := by omega
      rw [this, Nat.add_mod, Nat.dvd_iff_mod_eq_zero.mp hdy, add_zero, Nat.mod_mod]
    exact hxm.trans hym.symm
  let l0 : Fin ℓ → ℕ := fun i ↦ (A0 i).max' ⟨0, hA0_0 i⟩
  obtain ⟨imax, _, himax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin ℓ)) l0 ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  let lmax := l0 imax
  have hlmax_ge : m - 1 ≤ lmax := by
    have hsub : A0 imax ⊆ Finset.Icc 0 lmax := fun x hx ↦ Finset.mem_Icc.mpr ⟨Nat.zero_le _, Finset.le_max' _ _ hx⟩
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hc
    have := hA0_card imax
    omega
  have hlmax_le : lmax ≤ q := hA0_le imax lmax (Finset.max'_mem _ _)
  let κ := (lmax - 2) / (m - 2)
  have hκ_le : κ * (m - 2) ≤ lmax - 2 := by
    rw [mul_comm]; exact Nat.mul_div_le (lmax - 2) (m - 2)
  have hκ_upp : lmax - 1 ≤ (κ + 1) * (m - 2) := by
    have hm2 : 0 < m - 2 := by omega
    have hlt := Nat.lt_mul_div_succ (lmax - 2) hm2
    change lmax - 2 < (m - 2) * (κ + 1) at hlt
    have hcomm : (κ + 1) * (m - 2) = (m - 2) * (κ + 1) := mul_comm _ _
    omega
  have hκ_ell : 2 * κ + 2 ≤ ℓ := by
    have hκ_le2 : κ * (m - 2) + 2 ≤ q := by omega
    have h1 : 3 * κ * (m - 2) + 6 ≤ ℓ * (m - 2) := by linarith
    have h2 : 3 * κ < ℓ := by
      by_contra hge
      have : ℓ * (m - 2) ≤ 3 * κ * (m - 2) := Nat.mul_le_mul_right (m - 2) (not_lt.mp hge)
      omega
    omega
  let lastIdx : Fin ℓ := ⟨ℓ - 1, by omega⟩
  let τ : Equiv.Perm (Fin ℓ) := Equiv.swap imax lastIdx
  let A1 : Fin ℓ → Finset ℕ := fun i ↦ A0 (τ i)
  let A_rest : Fin (ℓ - 1) → Finset ℕ := fun i ↦ A1 ⟨i.val, by omega⟩
  let l_rest : Fin (ℓ - 1) → ℕ := fun i ↦ (A_rest i).max' ⟨0, hA0_0 (τ ⟨i.val, by omega⟩)⟩
  obtain ⟨σr, hσr⟩ := exists_perm_antitone (ℓ - 1) l_rest
  let A : Fin ℓ → Finset ℕ := fun j ↦
    if hj : j.val < ℓ - 1 then A_rest (σr ⟨j.val, hj⟩) else A1 lastIdx
  let σ : Equiv.Perm (Fin ℓ) :=
    { toFun := fun j ↦ if hj : j.val < ℓ - 1 then ⟨(σr ⟨j.val, hj⟩).val, by omega⟩ else lastIdx
      invFun := fun j ↦ if hj : j.val < ℓ - 1 then ⟨(σr.symm ⟨j.val, hj⟩).val, by omega⟩ else lastIdx
      left_inv := fun j ↦ by
        by_cases hj : j.val < ℓ - 1
        · simp [hj, (σr ⟨j.val, hj⟩).isLt]
        · simp [hj, lastIdx, Fin.ext_iff]; omega
      right_inv := fun j ↦ by
        by_cases hj : j.val < ℓ - 1
        · simp [hj, (σr.symm ⟨j.val, hj⟩).isLt]
        · simp [hj, lastIdx, Fin.ext_iff]; omega }
  have hA_perm_idx : ∀ j : Fin ℓ, A j = A0 (τ (σ j)) := fun j ↦ by
    by_cases hj : j.val < ℓ - 1 <;> simp [A, σ, A1, A_rest, hj]
  have hA_perm : sumFinset A = sumFinset A0 := by
    rw [show A = fun j ↦ A0 ((τ * σ) j) from funext hA_perm_idx]
    exact sumFinset_perm A0 (τ * σ)
  have hA_0 : ∀ j, 0 ∈ A j := fun j ↦ hA_perm_idx j ▸ hA0_0 _
  have hA_card : ∀ j, m ≤ (A j).card := fun j ↦ hA_perm_idx j ▸ hA0_card _
  have hA_le : ∀ j, ∀ x ∈ A j, x ≤ lmax := fun j x hx ↦ by
    rw [hA_perm_idx j] at hx
    exact le_trans (Finset.le_max' (A0 (τ (σ j))) x hx) (himax (τ (σ j)) (Finset.mem_univ _))
  have hA_cop : ∀ j, ∀ d : ℕ, 1 < d → ¬ ∀ x ∈ A j, d ∣ x := fun j ↦ hA_perm_idx j ▸ hA0_cop _
  have hA_last : (A lastIdx).max' ⟨0, hA_0 lastIdx⟩ = lmax := by
    have heq : A lastIdx = A0 imax := by
      dsimp only [A, A1]
      rw [dif_neg (by simp [lastIdx])]
      simp [τ]
    simp_rw [heq]
    rfl
  have hA_anti : ∀ i j : Fin (ℓ - 1), i ≤ j →
      (A ⟨j.val, by omega⟩).max' ⟨0, hA_0 _⟩ ≤ (A ⟨i.val, by omega⟩).max' ⟨0, hA_0 _⟩ := by
    intro i j hij
    have hi_lt : (⟨i.val, by omega⟩ : Fin ℓ).val < ℓ - 1 := i.isLt
    have hj_lt : (⟨j.val, by omega⟩ : Fin ℓ).val < ℓ - 1 := j.isLt
    have hi_eq : A ⟨i.val, by omega⟩ = A_rest (σr i) := by dsimp only [A]; rw [dif_pos hi_lt]
    have hj_eq : A ⟨j.val, by omega⟩ = A_rest (σr j) := by dsimp only [A]; rw [dif_pos hj_lt]
    have hm := hσr hij
    dsimp only [l_rest] at hm
    simp_rw [hj_eq, hi_eq]
    exact hm
  have hT0 : ∃ a0_int b0_int : ℕ, a0_int ≤ b0_int ∧
      Finset.Icc a0_int b0_int ⊆ sumFinset (fun i : Fin (2 * κ + 1) ↦ A ⟨i.val, by omega⟩) ∧
      2 * (κ + 1) * (m - 1) + a0_int ≤ b0_int + lmax ∧ lmax ≤ b0_int - a0_int + 1 := by
    refine lev_thm4 κ lmax m hm (fun i : Fin (2 * κ + 1) ↦ A ⟨i.val, by omega⟩)
      (fun i ↦ hA_0 _) (fun i ↦ hA_card _) (fun i x hx ↦ hA_le _ x hx) (fun i ↦ hA_cop _)
      (fun i j hij ↦ hA_anti ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ (by exact hij)) hlmax_ge hκ_upp
  obtain ⟨a0_i, b0_i, hab0, hsub0, hineq0, hlen0⟩ := hT0
  obtain ⟨a, b, hab, hsub_pre, hineq_pre, hlen_pre⟩ :=
    extend_chain (2 * κ + 1) (2 * (κ + 1)) m lmax hm A hA_0 hA_card hA_le (by omega)
      a0_i b0_i hab0 hsub0 hineq0 hlen0 (ℓ - 1) (by omega) (by omega)
  have hS_last : sumFinset A = sumFinset (fun i : Fin (ℓ - 1) ↦ A ⟨i.val, by omega⟩) + A lastIdx :=
    sumFinset_split_last (by omega) A
  have hext_last := extend_interval hab hsub_pre (hA_0 lastIdx)
    (hA_last ▸ Finset.max'_mem (A lastIdx) ⟨0, hA_0 lastIdx⟩) hlen_pre
  have hIcc_A0 : Finset.Icc a (b + lmax) ⊆ sumFinset A0 := by
    rw [← hA_perm, hS_last]
    exact hext_last
  have hlen_final : a + ℓ * (m - 1) ≤ b + lmax := by
    have hcoeff : 2 * (κ + 1) + (ℓ - 1 - (2 * κ + 1)) = ℓ := by omega
    rw [hcoeff] at hineq_pre
    linarith
  let shift := ∑ i : Fin ℓ, a0 i
  refine ⟨a + shift, b + lmax + shift, by omega, fun t ht ↦ ?_⟩
  rw [Finset.mem_Icc] at ht
  have ht_sub : t - shift ∈ Finset.Icc a (b + lmax) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  obtain ⟨g, hg_mem, hg_sum⟩ := (mem_sumFinset_iff A0 (t - shift)).mp (hIcc_A0 ht_sub)
  refine ⟨fun i ↦ g i + a0 i, fun i ↦ ?_, ?_⟩
  · obtain ⟨y, hy, hy_eq⟩ := Finset.mem_image.mp (hg_mem i)
    have hy_le : a0 i ≤ y := Finset.min'_le _ _ hy
    have hy_eq2 : g i + a0 i = y := by omega
    change g i + a0 i ∈ S i
    rw [hy_eq2]
    exact hy
  · rw [Finset.sum_add_distrib, hg_sum]
    change (t - shift) + shift = t
    omega

end Solution
