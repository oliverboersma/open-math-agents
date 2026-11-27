import FormalConjectures.Other.VCDimConvex

/-!
# Proof that every convex set in R^{n+1} has VC_n dimension at most 3^n (in fact <= 3)

We prove the exponential-bound conjecture with `c = 3`: for every `n >= 1`,
every convex set `C` in `Fin (n + 1) -> ℝ` has `HasAddVCNDimAtMost C n (3 ^ n)`.
In fact, we prove the stronger sharp bound `HasAddVCNDimAtMost C n 2` for all `n >= 2` and
`HasAddVCNDimAtMost C 1 3` for `n = 1`.

Architecture (100% homology-free and self-contained in Mathlib 4):
1. Plain Borsuk-Ulam theorem on the sup-norm sphere `cubeBdry m = ∂([-1, 1]^{m+1})`, proved from
   scratch via Ky Fan's mod-2 parity lemma on the antipodally reflected cubical triangulation
   `CubeSimplex k N` using a 5-case fixed-point-free facet-pairing involution.
2. Convex geometry core: strict convex position, two-subset forbidden cones, `S_3`-invariant cubic
   sign polynomials `α * β * (α + β)`, non-hitting of orthants, exact kernel dimension
   `finrank W = n - 1`, and surjectivity of the summation map `Φ`.
3. Base cases `n = 1, d = 3` (Radon's theorem + 4-sector covering) and `n = 2, d = 2` (1-dimensional
   kernel + forward/backward one-step cone covering).
4. Simultaneous Chamber Surgery for `n = m + 3 >= 3`: 4-band radial surgery inside every nonempty
   chamber `D_a` and `-D_a`, glued via finite closed pasting into a continuous odd map avoiding
   `± q_*`, followed by zero-inner-product equatorial projection contradicting Borsuk-Ulam.
-/

namespace VCDimAllNProof

noncomputable section

open scoped Classical

/- ## Section 1: Self-Contained Combinatorial Borsuk-Ulam via Ky Fan Parity -/

section BorsukUlam

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private def posSign (t : ℕ) (x : ℤ) : Prop :=
  if Even t then 0 < x else x < 0

private def IsPosAlt (r : ℕ) (S : Finset ℤ) : Prop :=
  S.card = r ∧ ∀ x ∈ S, posSign (S.filter (fun y => y.natAbs < x.natAbs)).card x

private def IsNegAlt (r : ℕ) (S : Finset ℤ) : Prop :=
  IsPosAlt r (S.image (fun x => -x))

private lemma neg_inj_int : Function.Injective (fun x : ℤ => -x) := neg_injective

private lemma isNegAlt_iff (r : ℕ) (S : Finset ℤ) :
    IsNegAlt r S ↔
      S.card = r ∧ ∀ x ∈ S, posSign ((S.filter (fun y => y.natAbs < x.natAbs)).card + 1) x := by
  unfold IsNegAlt IsPosAlt
  rw [Finset.card_image_of_injective _ neg_inj_int]
  have hfilt_eq : ∀ x : ℤ,
      ((S.image (fun y => -y)).filter (fun y => y.natAbs < (-x).natAbs)).card =
      (S.filter (fun y => y.natAbs < x.natAbs)).card := by
    intro x
    have heq : (S.image (fun y => -y)).filter (fun y => y.natAbs < (-x).natAbs) =
        (S.filter (fun y => y.natAbs < x.natAbs)).image (fun y => -y) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_image, Int.natAbs_neg]
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hlt⟩
        exact ⟨y, ⟨hy, by simpa using hlt⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hlt⟩, rfl⟩
        exact ⟨⟨y, hy, rfl⟩, by simpa using hlt⟩
    rw [heq, Finset.card_image_of_injective _ neg_inj_int]
  constructor
  · rintro ⟨hcard, h⟩
    refine ⟨hcard, fun x hx => ?_⟩
    have hx' := h (-x) (Finset.mem_image_of_mem _ hx)
    rw [hfilt_eq x] at hx'
    unfold posSign at hx' ⊢
    by_cases hev : Even (S.filter (fun y => y.natAbs < x.natAbs)).card
    · have hodd : ¬ Even ((S.filter (fun y => y.natAbs < x.natAbs)).card + 1) := by
        rw [Nat.even_add_one]; exact not_not.mpr hev
      rw [if_pos hev] at hx'
      rw [if_neg hodd]
      omega
    · have hev' : Even ((S.filter (fun y => y.natAbs < x.natAbs)).card + 1) := by
        rw [Nat.even_add_one]; exact hev
      rw [if_neg hev] at hx'
      rw [if_pos hev']
      omega
  · rintro ⟨hcard, h⟩
    refine ⟨hcard, fun z hz => ?_⟩
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    have hx' := h x hx
    rw [hfilt_eq x]
    unfold posSign at hx' ⊢
    by_cases hev : Even (S.filter (fun y => y.natAbs < x.natAbs)).card
    · have hodd : ¬ Even ((S.filter (fun y => y.natAbs < x.natAbs)).card + 1) := by
        rw [Nat.even_add_one]; exact not_not.mpr hev
      rw [if_neg hodd] at hx'
      rw [if_pos hev]
      omega
    · have hev' : Even ((S.filter (fun y => y.natAbs < x.natAbs)).card + 1) := by
        rw [Nat.even_add_one]; exact hev
      rw [if_pos hev'] at hx'
      rw [if_neg hev]
      omega

private lemma natAbs_inj_of_nocomp {S : Finset ℤ}
    (hnocomp : ∀ x ∈ S, -x ∉ S) {x y : ℤ} (hx : x ∈ S) (hy : y ∈ S)
    (habs : x.natAbs = y.natAbs) : x = y := by
  rcases Int.natAbs_eq_natAbs_iff.mp habs with h | h
  · exact h
  · exfalso
    exact hnocomp y hy (h ▸ hx)

private lemma kyFan_finset_parity : ∀ (k : ℕ) (S : Finset ℤ),
    S.card = k + 1 →
    (∀ x ∈ S, x ≠ 0) →
    (∀ x ∈ S, -x ∉ S) →
    (∑ x ∈ S, (if IsPosAlt k (S.erase x) then (1 : ZMod 2) else 0)) =
      (if IsPosAlt (k + 1) S ∨ IsNegAlt (k + 1) S then 1 else 0)
  | 0, S, hcard, hnz, _ => by
    rcases Finset.card_eq_one.mp hcard with ⟨m, rfl⟩
    have hm : m ≠ 0 := hnz m (Finset.mem_singleton_self m)
    have h0 : IsPosAlt 0 (({m} : Finset ℤ).erase m) := by simp [IsPosAlt]
    have h1 : IsPosAlt 1 {m} ∨ IsNegAlt 1 {m} := by
      rw [isNegAlt_iff]
      rcases lt_or_gt_of_ne hm with hlt | hgt
      · right
        refine ⟨Finset.card_singleton m, fun x hx => ?_⟩
        rcases Finset.mem_singleton.mp hx with rfl
        have hfilt : (({x} : Finset ℤ).filter (fun y => y.natAbs < x.natAbs)).card = 0 := by simp
        rw [hfilt]; simp [posSign, hlt]
      · left
        refine ⟨Finset.card_singleton m, fun x hx => ?_⟩
        rcases Finset.mem_singleton.mp hx with rfl
        have hfilt : (({x} : Finset ℤ).filter (fun y => y.natAbs < x.natAbs)).card = 0 := by simp
        rw [hfilt]; simp [posSign, hgt]
    rw [Finset.sum_singleton, if_pos h0, if_pos h1]
  | k + 1, S, hcard, hnz, hnocomp => by
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨m, hmS, hm_max⟩ := Finset.exists_max_image S Int.natAbs hne
    let T := S.erase m
    have hTcard : T.card = k + 1 := by rw [Finset.card_erase_of_mem hmS, hcard]; omega
    have hTnz : ∀ x ∈ T, x ≠ 0 := fun x hx => hnz x (Finset.mem_of_mem_erase hx)
    have hTnocomp : ∀ x ∈ T, -x ∉ T := fun x hx hneg =>
      hnocomp x (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hneg)
    have hlt_m : ∀ y ∈ T, y.natAbs < m.natAbs := by
      intro y hy
      have hyS := Finset.mem_of_mem_erase hy
      have hne_ym := Finset.ne_of_mem_erase hy
      exact lt_of_le_of_ne (hm_max y hyS) (fun heq => hne_ym (natAbs_inj_of_nocomp hnocomp hyS hmS heq))
    have hfilt_T_eq : ∀ y ∈ T,
        S.filter (fun z => z.natAbs < y.natAbs) = T.filter (fun z => z.natAbs < y.natAbs) := by
      intro y hy
      ext z
      simp only [Finset.mem_filter, T, Finset.mem_erase]
      constructor
      · rintro ⟨hzS, hlt⟩
        exact ⟨⟨by rintro rfl; have := hlt_m y hy; omega, hzS⟩, hlt⟩
      · rintro ⟨⟨_, hzS⟩, hlt⟩
        exact ⟨hzS, hlt⟩
    have hfilt_m : S.filter (fun z => z.natAbs < m.natAbs) = T := by
      ext z
      simp only [Finset.mem_filter, T, Finset.mem_erase]
      constructor
      · rintro ⟨hzS, hlt⟩; exact ⟨by rintro rfl; omega, hzS⟩
      · rintro ⟨hzm, hzS⟩; exact ⟨hzS, hlt_m z (Finset.mem_erase.mpr ⟨hzm, hzS⟩)⟩
    have hPos_iff : IsPosAlt (k + 2) S ↔ IsPosAlt (k + 1) T ∧ posSign (k + 1) m := by
      constructor
      · rintro ⟨_, hS⟩
        refine ⟨⟨hTcard, fun y hy => ?_⟩, ?_⟩
        · rw [← hfilt_T_eq y hy]; exact hS y (Finset.mem_of_mem_erase hy)
        · have hm' := hS m hmS; rwa [hfilt_m, hTcard] at hm'
      · rintro ⟨⟨_, hT⟩, hm'⟩
        refine ⟨hcard, fun y hy => ?_⟩
        by_cases hym : y = m
        · subst hym; rwa [hfilt_m, hTcard]
        · have hyT : y ∈ T := Finset.mem_erase.mpr ⟨hym, hy⟩
          rw [hfilt_T_eq y hyT]; exact hT y hyT
    have hNeg_iff : IsNegAlt (k + 2) S ↔ IsNegAlt (k + 1) T ∧ posSign k m := by
      rw [isNegAlt_iff, isNegAlt_iff]
      have hpar : posSign (k + 2) m ↔ posSign k m := by
        unfold posSign
        have : Even (k + 2) ↔ Even k := by rw [Nat.even_add]; simp
        simp [this]
      constructor
      · rintro ⟨_, hS⟩
        refine ⟨⟨hTcard, fun y hy => ?_⟩, ?_⟩
        · rw [← hfilt_T_eq y hy]; exact hS y (Finset.mem_of_mem_erase hy)
        · have hm' := hS m hmS; rw [hfilt_m, hTcard] at hm'; exact hpar.mp hm'
      · rintro ⟨⟨_, hT⟩, hm'⟩
        refine ⟨hcard, fun y hy => ?_⟩
        by_cases hym : y = m
        · subst hym; rw [hfilt_m, hTcard]; exact hpar.mpr hm'
        · have hyT : y ∈ T := Finset.mem_erase.mpr ⟨hym, hy⟩
          rw [hfilt_T_eq y hyT]; exact hT y hyT
    have hErase_iff : ∀ x ∈ T,
        IsPosAlt (k + 1) (S.erase x) ↔ IsPosAlt k (T.erase x) ∧ posSign k m := by
      intro x hxT
      have hxS := Finset.mem_of_mem_erase hxT
      have hxm := Finset.ne_of_mem_erase hxT
      have hSx_card : (S.erase x).card = k + 1 := by rw [Finset.card_erase_of_mem hxS, hcard]; omega
      have hTx_card : (T.erase x).card = k := by rw [Finset.card_erase_of_mem hxT, hTcard]; omega
      have hmSx : m ∈ S.erase x := Finset.mem_erase.mpr ⟨hxm.symm, hmS⟩
      have hfilt_m_x : (S.erase x).filter (fun z => z.natAbs < m.natAbs) = T.erase x := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_erase, T]
        constructor
        · rintro ⟨⟨hzx, hzS⟩, hlt⟩; exact ⟨hzx, by rintro rfl; omega, hzS⟩
        · rintro ⟨hzx, hzm, hzS⟩; exact ⟨⟨hzx, hzS⟩, hlt_m z (Finset.mem_erase.mpr ⟨hzm, hzS⟩)⟩
      have hfilt_y_x : ∀ y ∈ T.erase x,
          (S.erase x).filter (fun z => z.natAbs < y.natAbs) =
          (T.erase x).filter (fun z => z.natAbs < y.natAbs) := by
        intro y hy
        have hyT := Finset.mem_of_mem_erase hy
        ext z
        simp only [Finset.mem_filter, Finset.mem_erase, T]
        constructor
        · rintro ⟨⟨hzx, hzS⟩, hlt⟩
          exact ⟨⟨hzx, by rintro rfl; have := hlt_m y hyT; omega, hzS⟩, hlt⟩
        · rintro ⟨⟨hzx, _, hzS⟩, hlt⟩; exact ⟨⟨hzx, hzS⟩, hlt⟩
      constructor
      · rintro ⟨_, hSx⟩
        refine ⟨⟨hTx_card, fun y hy => ?_⟩, ?_⟩
        · rw [← hfilt_y_x y hy]
          exact hSx y (Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hy,
            Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)⟩)
        · have hm' := hSx m hmSx; rwa [hfilt_m_x, hTx_card] at hm'
      · rintro ⟨⟨_, hTx⟩, hm'⟩
        refine ⟨hSx_card, fun y hy => ?_⟩
        by_cases hym : y = m
        · subst hym; rwa [hfilt_m_x, hTx_card]
        · have hyTx : y ∈ T.erase x := Finset.mem_erase.mpr
            ⟨Finset.ne_of_mem_erase hy, Finset.mem_erase.mpr ⟨hym, Finset.mem_of_mem_erase hy⟩⟩
          rw [hfilt_y_x y hyTx]; exact hTx y hyTx
    have hsum_split :
        (∑ x ∈ S, (if IsPosAlt (k + 1) (S.erase x) then (1 : ZMod 2) else 0)) =
        (if IsPosAlt (k + 1) T then (1 : ZMod 2) else 0) +
        ∑ x ∈ T, (if IsPosAlt (k + 1) (S.erase x) then (1 : ZMod 2) else 0) :=
      (Finset.add_sum_erase S
        (fun x => if IsPosAlt (k + 1) (S.erase x) then (1 : ZMod 2) else 0) hmS).symm
    have hm_nz : m ≠ 0 := hnz m hmS
    have hpos_xor : posSign (k + 1) m ↔ ¬ posSign k m := by
      unfold posSign
      have hev : Even (k + 1) ↔ ¬ Even k := Nat.even_add_one
      by_cases h : Even k <;> simp [h, hev] <;> omega
    have hdisj_T : ¬ (IsPosAlt (k + 1) T ∧ IsNegAlt (k + 1) T) := by
      rintro ⟨hP, hN⟩
      rw [isNegAlt_iff] at hN
      obtain ⟨y, hyT⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
      have hp1 := hP.2 y hyT
      have hp2 := hN.2 y hyT
      unfold posSign at hp1 hp2
      by_cases hev : Even (T.filter (fun z => z.natAbs < y.natAbs)).card
      · have hodd : ¬ Even ((T.filter (fun z => z.natAbs < y.natAbs)).card + 1) := by
          rw [Nat.even_add_one]; exact not_not.mpr hev
        rw [if_pos hev] at hp1; rw [if_neg hodd] at hp2; omega
      · have hev' : Even ((T.filter (fun z => z.natAbs < y.natAbs)).card + 1) := by
          rw [Nat.even_add_one]; exact hev
        rw [if_neg hev] at hp1; rw [if_pos hev'] at hp2; omega
    rw [hsum_split, hPos_iff, hNeg_iff]
    by_cases hmk : posSign k m
    · have hmk1 : ¬ posSign (k + 1) m := fun h => hpos_xor.mp h hmk
      have hTsum : (∑ x ∈ T, (if IsPosAlt (k + 1) (S.erase x) then (1 : ZMod 2) else 0)) =
          ∑ x ∈ T, (if IsPosAlt k (T.erase x) then (1 : ZMod 2) else 0) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        simp [hErase_iff x hx, hmk]
      rw [hTsum, kyFan_finset_parity k T hTcard hTnz hTnocomp]
      by_cases hPT : IsPosAlt (k + 1) T
      · have hNT : ¬ IsNegAlt (k + 1) T := fun h => hdisj_T ⟨hPT, h⟩
        simp [hPT, hNT, hmk, hmk1, zmod2_add_self]
      · by_cases hNT : IsNegAlt (k + 1) T <;> simp [hPT, hNT, hmk, hmk1]
    · have hmk1 : posSign (k + 1) m := hpos_xor.mpr hmk
      have hTsum : (∑ x ∈ T, (if IsPosAlt (k + 1) (S.erase x) then (1 : ZMod 2) else 0)) = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        simp [hErase_iff x hx, hmk]
      rw [hTsum, add_zero]
      simp [hmk, hmk1]

private lemma kyFan_simplex_parity {k : ℕ} (f : Fin (k + 1) → ℤ)
    (hnz : ∀ i, f i ≠ 0) (hnocomp : ∀ i j, f i + f j ≠ 0) :
    (∑ r : Fin (k + 1),
      (if IsPosAlt k ((Finset.univ.erase r).image f) then (1 : ZMod 2) else 0)) =
      (if IsPosAlt (k + 1) (Finset.univ.image f) ∨ IsNegAlt (k + 1) (Finset.univ.image f)
       then 1 else 0) := by
  let S := Finset.univ.image f
  have hSnz : ∀ x ∈ S, x ≠ 0 := by
    intro x hx; rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩; exact hnz i
  have hSnocomp : ∀ x ∈ S, -x ∉ S := by
    intro x hx hnx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hnx with ⟨j, _, hj⟩
    exact hnocomp i j (by omega)
  by_cases hinj : Function.Injective f
  · have hScard : S.card = k + 1 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have hsum :
        (∑ r : Fin (k + 1),
          (if IsPosAlt k ((Finset.univ.erase r).image f) then (1 : ZMod 2) else 0)) =
        ∑ x ∈ S, (if IsPosAlt k (S.erase x) then (1 : ZMod 2) else 0) := by
      rw [Finset.sum_image (fun a _ b _ h => hinj h)]
      refine Finset.sum_congr rfl fun r _ => ?_
      have heq : (Finset.univ.erase r).image f = S.erase (f r) := by
        ext y
        simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, true_and, S]
        constructor
        · rintro ⟨i, hir, rfl⟩; exact ⟨fun h => hir (hinj h), ⟨i, rfl⟩⟩
        · rintro ⟨hy, ⟨i, rfl⟩⟩; exact ⟨i, fun h => hy (congr_arg f h), rfl⟩
      rw [heq]
    rw [hsum]
    exact kyFan_finset_parity k S hScard hSnz hSnocomp
  · have hScard_lt : S.card < k + 1 := by
      by_contra hge
      have hle : S.card ≤ k + 1 := Finset.card_image_le.trans (by simp)
      have heq : S.card = (Finset.univ : Finset (Fin (k + 1))).card := by simp; omega
      have hbij : Set.InjOn f (Finset.univ : Finset (Fin (k + 1))) :=
        Finset.injOn_of_card_image_eq heq
      exact hinj (fun a b h => hbij (Finset.mem_univ a) (Finset.mem_univ b) h)
    have hRHS : ¬ (IsPosAlt (k + 1) S ∨ IsNegAlt (k + 1) S) := by
      rintro (h | h)
      · exact absurd h.1 (by omega)
      · rw [isNegAlt_iff] at h; exact absurd h.1 (by omega)
    rw [if_neg hRHS]
    by_cases hSk : S.card < k
    · refine Finset.sum_eq_zero fun r _ => ?_
      rw [if_neg]
      intro hPA
      have hle : ((Finset.univ.erase r).image f).card ≤ S.card :=
        Finset.card_le_card (Finset.image_subset_image (Finset.erase_subset _ _))
      have := hPA.1; omega
    · have hScard : S.card = k := by omega
      have hnotinj : ∃ i j : Fin (k + 1), i ≠ j ∧ f i = f j := by
        unfold Function.Injective at hinj; push Not at hinj
        rcases hinj with ⟨i, j, hij, hne⟩; exact ⟨i, j, hne, hij⟩
      rcases hnotinj with ⟨i₁, i₂, hi12, hfi⟩
      have huniq : ∀ r : Fin (k + 1), r ≠ i₁ → r ≠ i₂ →
          ((Finset.univ.erase r).image f).card < k := by
        intro r hr1 hr2
        have hfr_not : f r ∉ (Finset.univ.erase r).image f := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨j, hj, hfj⟩
          have hjr : j ≠ r := Finset.ne_of_mem_erase hj
          have hsub : S ⊆ ((Finset.univ.erase i₁).erase r).image f := by
            intro y hy
            rcases Finset.mem_image.mp hy with ⟨t, _, rfl⟩
            by_cases ht1 : t = i₁
            · subst ht1
              exact Finset.mem_image.mpr ⟨i₂, Finset.mem_erase.mpr
                ⟨hr2.symm, Finset.mem_erase.mpr ⟨hi12.symm, Finset.mem_univ _⟩⟩, hfi.symm⟩
            · by_cases htr : t = r
              · subst htr
                by_cases hj1 : j = i₁
                · subst hj1
                  exact Finset.mem_image.mpr ⟨i₂, Finset.mem_erase.mpr
                    ⟨hr2.symm, Finset.mem_erase.mpr ⟨hi12.symm, Finset.mem_univ _⟩⟩, hfi.symm.trans hfj⟩
                · exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr
                    ⟨hjr, Finset.mem_erase.mpr ⟨hj1, Finset.mem_univ _⟩⟩, hfj⟩
              · exact Finset.mem_image.mpr ⟨t, Finset.mem_erase.mpr
                  ⟨htr, Finset.mem_erase.mpr ⟨ht1, Finset.mem_univ _⟩⟩, rfl⟩
          have hcard_le : S.card ≤ ((Finset.univ.erase i₁).erase r).card :=
            (Finset.card_le_card hsub).trans Finset.card_image_le
          have hr_in : r ∈ Finset.univ.erase i₁ := Finset.mem_erase.mpr ⟨hr1, Finset.mem_univ _⟩
          rw [Finset.card_erase_of_mem hr_in, Finset.card_erase_of_mem (Finset.mem_univ i₁),
            Finset.card_univ, Fintype.card_fin] at hcard_le
          omega
        have hss : (Finset.univ.erase r).image f ⊂ S :=
          Finset.ssubset_iff_subset_ne.mpr ⟨Finset.image_subset_image (Finset.erase_subset _ _),
            fun heq => hfr_not (heq ▸ Finset.mem_image_of_mem f (Finset.mem_univ r))⟩
        have := Finset.card_lt_card hss; omega
      have himg1 : (Finset.univ.erase i₁).image f = S := by
        apply Finset.Subset.antisymm (Finset.image_subset_image (Finset.erase_subset _ _))
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨t, _, rfl⟩
        by_cases ht : t = i₁
        · subst ht
          exact Finset.mem_image.mpr ⟨i₂, Finset.mem_erase.mpr ⟨hi12.symm, Finset.mem_univ _⟩, hfi.symm⟩
        · exact Finset.mem_image.mpr ⟨t, Finset.mem_erase.mpr ⟨ht, Finset.mem_univ _⟩, rfl⟩
      have himg2 : (Finset.univ.erase i₂).image f = S := by
        apply Finset.Subset.antisymm (Finset.image_subset_image (Finset.erase_subset _ _))
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨t, _, rfl⟩
        by_cases ht : t = i₂
        · subst ht
          exact Finset.mem_image.mpr ⟨i₁, Finset.mem_erase.mpr ⟨hi12, Finset.mem_univ _⟩, hfi⟩
        · exact Finset.mem_image.mpr ⟨t, Finset.mem_erase.mpr ⟨ht, Finset.mem_univ _⟩, rfl⟩
      let term : Fin (k + 1) → ZMod 2 :=
        fun r => if IsPosAlt k ((Finset.univ.erase r).image f) then (1 : ZMod 2) else 0
      have hsum_pair : ∑ r : Fin (k + 1), term r = term i₁ + term i₂ := by
        rw [← Finset.sum_pair hi12]
        symm
        refine Finset.sum_subset (Finset.subset_univ _) fun r _ hr => ?_
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
        simp only [term]
        rw [if_neg]
        intro hPA
        have := huniq r hr.1 hr.2; have := hPA.1; omega
      change ∑ r : Fin (k + 1), term r = 0
      rw [hsum_pair]
      simp only [term, himg1, himg2, zmod2_add_self]

private structure CubeSimplex (k N : ℕ) where
  a : Fin (k + 1)
  v : Fin (k + 1) → Fin (N + 1)
  s : Fin (k + 1) → Bool
  pi : Fin k → Fin (k + 1)
  hv_a : (v a).val = N
  hv_lt : ∀ i, i ≠ a → (v i).val < N
  hpi_inj : Function.Injective pi
  hpi_ne : ∀ j, pi j ≠ a

private def CubeSimplex.toRaw {k N : ℕ} (σ : CubeSimplex k N) :=
  (σ.a, σ.v, σ.s, σ.pi)

private lemma CubeSimplex.toRaw_inj {k N : ℕ} : Function.Injective (@CubeSimplex.toRaw k N) := by
  rintro ⟨a1, v1, s1, pi1, _, _, _, _⟩ ⟨a2, v2, s2, pi2, _, _, _, _⟩ h
  simp only [CubeSimplex.toRaw, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩; rfl

private instance (k N : ℕ) : Fintype (CubeSimplex k N) := by
  haveI : Finite (CubeSimplex k N) := Finite.of_injective CubeSimplex.toRaw CubeSimplex.toRaw_inj
  exact Fintype.ofFinite (CubeSimplex k N)

private lemma CubeSimplex.ext_raw {k N : ℕ} {σ₁ σ₂ : CubeSimplex k N}
    (ha : σ₁.a = σ₂.a) (hv : σ₁.v = σ₂.v) (hs : σ₁.s = σ₂.s) (hpi : σ₁.pi = σ₂.pi) :
    σ₁ = σ₂ :=
  CubeSimplex.toRaw_inj (by simp [CubeSimplex.toRaw, ha, hv, hs, hpi])

private def boolSign (b : Bool) : ℤ := if b then 1 else -1

private lemma boolSign_not (b : Bool) : boolSign (!b) = -boolSign b := by cases b <;> rfl

private def vert {k N : ℕ} (σ : CubeSimplex k N) (j : Fin (k + 1)) (i : Fin (k + 1)) : ℤ :=
  boolSign (σ.s i) * ((σ.v i).val + if ∃ t : Fin k, t.val < j.val ∧ σ.pi t = i then 1 else 0)

private def CubeSimplex.neg {k N : ℕ} (σ : CubeSimplex k N) : CubeSimplex k N where
  a := σ.a
  v := σ.v
  s := fun i => !σ.s i
  pi := σ.pi
  hv_a := σ.hv_a
  hv_lt := σ.hv_lt
  hpi_inj := σ.hpi_inj
  hpi_ne := σ.hpi_ne

private lemma CubeSimplex.neg_involutive {k N : ℕ} (σ : CubeSimplex k N) : σ.neg.neg = σ :=
  CubeSimplex.ext_raw rfl rfl (by funext i; simp [CubeSimplex.neg]) rfl

private lemma vert_neg {k N : ℕ} (σ : CubeSimplex k N) (j : Fin (k + 1)) :
    vert σ.neg j = -vert σ j := by
  funext i; simp only [vert, CubeSimplex.neg, Pi.neg_apply, boolSign_not, neg_mul]
  rfl

private lemma vert_abs_le {k N : ℕ} (σ : CubeSimplex k N) (j i : Fin (k + 1)) :
    |vert σ j i| ≤ N := by
  unfold vert
  have hs : |boolSign (σ.s i)| = 1 := by cases σ.s i <;> simp [boolSign]
  rw [abs_mul, hs, one_mul]
  by_cases hi : i = σ.a
  · subst hi
    have hno : ¬ ∃ t : Fin k, t.val < j.val ∧ σ.pi t = σ.a := by
      rintro ⟨t, _, ht⟩; exact σ.hpi_ne t ht
    rw [if_neg hno, add_zero, σ.hv_a]; simp
  · have hlt := σ.hv_lt i hi
    split_ifs <;> rw [abs_of_nonneg (by omega)] <;> omega

private lemma vert_abs_a {k N : ℕ} (σ : CubeSimplex k N) (j : Fin (k + 1)) :
    |vert σ j σ.a| = N := by
  unfold vert
  have hs : |boolSign (σ.s σ.a)| = 1 := by cases σ.s σ.a <;> simp [boolSign]
  have hno : ¬ ∃ t : Fin k, t.val < j.val ∧ σ.pi t = σ.a := by
    rintro ⟨t, _, ht⟩; exact σ.hpi_ne t ht
  rw [abs_mul, hs, one_mul, if_neg hno, add_zero, σ.hv_a]; simp

private lemma vert_diff_le_one {k N : ℕ} (σ : CubeSimplex k N) (j₁ j₂ i : Fin (k + 1)) :
    |vert σ j₁ i - vert σ j₂ i| ≤ 1 := by
  unfold vert
  rw [← mul_sub]
  have hs : |boolSign (σ.s i)| = 1 := by cases σ.s i <;> simp [boolSign]
  rw [abs_mul, hs, one_mul]
  split_ifs <;> simp

private abbrev UpperSimplex (k N : ℕ) :=
  {σ : CubeSimplex (k + 1) N // σ.s (Fin.last (k + 1)) = true}

private abbrev FacePair (k N : ℕ) := UpperSimplex k N × Fin (k + 2)

private def isEquator {k N : ℕ} (p : FacePair k N) : Prop :=
  p.2 = Fin.last (k + 1) ∧
  p.1.1.pi (Fin.last k) = Fin.last (k + 1) ∧
  (p.1.1.v (Fin.last (k + 1))).val = 0

private def pairSwapMid {k N : ℕ} (σ : UpperSimplex k N) (r : Fin (k + 2))
    (hr0 : 0 < r.val) (hrk : r.val < k + 1) : FacePair k N :=
  let t1 : Fin (k + 1) := ⟨r.val - 1, by omega⟩
  let t2 : Fin (k + 1) := ⟨r.val, hrk⟩
  let e := Equiv.swap t1 t2
  (⟨{ a := σ.1.a
      v := σ.1.v
      s := σ.1.s
      pi := σ.1.pi ∘ e
      hv_a := σ.1.hv_a
      hv_lt := σ.1.hv_lt
      hpi_inj := σ.1.hpi_inj.comp e.injective
      hpi_ne := fun j => σ.1.hpi_ne (e j) }, σ.2⟩, r)

private def pairZeroStep {k N : ℕ} (σ : UpperSimplex k N)
    (hvb : (σ.1.v (σ.1.pi 0)).val + 1 < N) : FacePair k N :=
  let b := σ.1.pi 0
  let v' : Fin (k + 2) → Fin (N + 1) := fun i =>
    if i = b then ⟨(σ.1.v b).val + 1, by dsimp [b]; omega⟩ else σ.1.v i
  let pi' : Fin (k + 1) → Fin (k + 2) := fun t =>
    if ht : t.val + 1 < k + 1 then σ.1.pi ⟨t.val + 1, ht⟩ else b
  (⟨{ a := σ.1.a
      v := v'
      s := σ.1.s
      pi := pi'
      hv_a := by
        have hba : σ.1.a ≠ b := (σ.1.hpi_ne 0).symm
        simp [v', hba, σ.1.hv_a]
      hv_lt := by
        intro i hi
        by_cases hib : i = b
        · rw [hib]; simpa [v', b] using hvb
        · simp [v', hib, σ.1.hv_lt i hi]
      hpi_inj := by
        intro t1 t2 h
        simp only [pi'] at h
        split_ifs at h with h1 h2 h2
        · have := σ.1.hpi_inj h; ext; have := congr_arg Fin.val this; dsimp at this; omega
        · have := σ.1.hpi_inj h; have := congr_arg Fin.val this; dsimp at this; omega
        · have := σ.1.hpi_inj h.symm; have := congr_arg Fin.val this; dsimp at this; omega
        · ext; omega
      hpi_ne := by
        intro t; simp only [pi']
        split_ifs with ht
        · exact σ.1.hpi_ne _
        · exact σ.1.hpi_ne 0 }, σ.2⟩, Fin.last (k + 1))

private def pairZeroCorner {k N : ℕ} (hN : 1 ≤ N) (σ : UpperSimplex k N)
    (hvb : (σ.1.v (σ.1.pi 0)).val + 1 = N) : FacePair k N :=
  let b := σ.1.pi 0
  let a0 := σ.1.a
  let v' : Fin (k + 2) → Fin (N + 1) := fun i =>
    if i = b then ⟨N, by omega⟩
    else if i = a0 then ⟨N - 1, by omega⟩
    else σ.1.v i
  let pi' : Fin (k + 1) → Fin (k + 2) := fun t =>
    if t.val = 0 then a0 else σ.1.pi t
  (⟨{ a := b
      v := v'
      s := σ.1.s
      pi := pi'
      hv_a := by simp [v']
      hv_lt := by
        intro i hi
        by_cases hia : i = a0
        · subst hia; simp [v', hi]; omega
        · simp [v', hi, hia, σ.1.hv_lt i hia]
      hpi_inj := by
        intro t1 t2 h
        simp only [pi'] at h
        split_ifs at h with h1 h2 h2
        · ext; omega
        · exact absurd h.symm (σ.1.hpi_ne t2)
        · exact absurd h (σ.1.hpi_ne t1)
        · exact σ.1.hpi_inj h
      hpi_ne := by
        intro t; simp only [pi']
        split_ifs with ht
        · exact (σ.1.hpi_ne 0).symm
        · intro heq
          have := σ.1.hpi_inj heq
          have := congr_arg Fin.val this; dsimp at this; omega }, σ.2⟩, 0)

private def pairLastStep {k N : ℕ} (σ : UpperSimplex k N)
    (hvb : 0 < (σ.1.v (σ.1.pi (Fin.last k))).val) : FacePair k N :=
  let b := σ.1.pi (Fin.last k)
  let v' : Fin (k + 2) → Fin (N + 1) := fun i =>
    if i = b then ⟨(σ.1.v b).val - 1, by have := (σ.1.v b).isLt; omega⟩ else σ.1.v i
  let pi' : Fin (k + 1) → Fin (k + 2) := fun t =>
    if ht : t.val = 0 then b else σ.1.pi ⟨t.val - 1, by omega⟩
  (⟨{ a := σ.1.a
      v := v'
      s := σ.1.s
      pi := pi'
      hv_a := by
        have hba : σ.1.a ≠ b := (σ.1.hpi_ne (Fin.last k)).symm
        simp [v', hba, σ.1.hv_a]
      hv_lt := by
        intro i hi
        by_cases hib : i = b
        · subst hib
          have hlt := σ.1.hv_lt b (σ.1.hpi_ne (Fin.last k))
          simp [v']; omega
        · simp [v', hib, σ.1.hv_lt i hi]
      hpi_inj := by
        intro t1 t2 h
        simp only [pi'] at h
        split_ifs at h with h1 h2 h2
        · ext; omega
        · have := σ.1.hpi_inj h.symm
          have := congr_arg Fin.val this; dsimp [Fin.last] at this; omega
        · have := σ.1.hpi_inj h
          have := congr_arg Fin.val this; dsimp [Fin.last] at this; omega
        · have := σ.1.hpi_inj h; ext; have := congr_arg Fin.val this; dsimp at this; omega
      hpi_ne := by
        intro t; simp only [pi']
        split_ifs with ht
        · exact σ.1.hpi_ne (Fin.last k)
        · exact σ.1.hpi_ne _ }, σ.2⟩, 0)

private def pairLastFlip {k N : ℕ} (σ : UpperSimplex k N)
    (hbne : σ.1.pi (Fin.last k) ≠ Fin.last (k + 1)) : FacePair k N :=
  let b := σ.1.pi (Fin.last k)
  (⟨{ a := σ.1.a
      v := σ.1.v
      s := fun i => if i = b then !σ.1.s i else σ.1.s i
      pi := σ.1.pi
      hv_a := σ.1.hv_a
      hv_lt := σ.1.hv_lt
      hpi_inj := σ.1.hpi_inj
      hpi_ne := σ.1.hpi_ne }, by simp [b, hbne.symm, σ.2]⟩, Fin.last (k + 1))

private def pairStep {k N : ℕ} (hN : 1 ≤ N) (p : FacePair k N) : FacePair k N :=
  let σ := p.1
  let r := p.2
  if hr0 : r.val = 0 then
    if hvb : (σ.1.v (σ.1.pi 0)).val + 1 < N then
      pairZeroStep σ hvb
    else
      pairZeroCorner hN σ (by have := σ.1.hv_lt (σ.1.pi 0) (σ.1.hpi_ne 0); omega)
  else if hrk : r.val < k + 1 then
    pairSwapMid σ r (by omega) hrk
  else
    if hvb : 0 < (σ.1.v (σ.1.pi (Fin.last k))).val then
      pairLastStep σ hvb
    else if hbne : σ.1.pi (Fin.last k) ≠ Fin.last (k + 1) then
      pairLastFlip σ hbne
    else
      p

private lemma pairStep_zeroStep {k N : ℕ} (hN : 1 ≤ N) (p : FacePair k N)
    (hr0 : p.2.val = 0) (hvb : (p.1.1.v (p.1.1.pi 0)).val + 1 < N) :
    pairStep hN p = pairZeroStep p.1 hvb := by
  unfold pairStep; rw [dif_pos hr0, dif_pos hvb]

private lemma pairStep_zeroCorner {k N : ℕ} (hN : 1 ≤ N) (p : FacePair k N)
    (hr0 : p.2.val = 0) (hvb : ¬ (p.1.1.v (p.1.1.pi 0)).val + 1 < N) :
    pairStep hN p = pairZeroCorner hN p.1 (by have := p.1.1.hv_lt (p.1.1.pi 0) (p.1.1.hpi_ne 0); omega) := by
  unfold pairStep; rw [dif_pos hr0, dif_neg hvb]

private lemma pairStep_swapMid {k N : ℕ} (hN : 1 ≤ N) (p : FacePair k N)
    (hr0 : p.2.val ≠ 0) (hrk : p.2.val < k + 1) :
    pairStep hN p = pairSwapMid p.1 p.2 (by omega) hrk := by
  unfold pairStep; rw [dif_neg hr0, dif_pos hrk]

private lemma pairStep_lastStep {k N : ℕ} (hN : 1 ≤ N) (p : FacePair k N)
    (hr0 : p.2.val ≠ 0) (hrk : ¬ p.2.val < k + 1)
    (hvb : 0 < (p.1.1.v (p.1.1.pi (Fin.last k))).val) :
    pairStep hN p = pairLastStep p.1 hvb := by
  unfold pairStep; rw [dif_neg hr0, dif_neg hrk, dif_pos hvb]

private lemma pairStep_lastFlip {k N : ℕ} (hN : 1 ≤ N) (p : FacePair k N)
    (hr0 : p.2.val ≠ 0) (hrk : ¬ p.2.val < k + 1)
    (hvb : ¬ 0 < (p.1.1.v (p.1.1.pi (Fin.last k))).val)
    (hbne : p.1.1.pi (Fin.last k) ≠ Fin.last (k + 1)) :
    pairStep hN p = pairLastFlip p.1 hbne := by
  unfold pairStep; rw [dif_neg hr0, dif_neg hrk, dif_neg hvb, dif_pos hbne]

private lemma pairStep_equator {k N : ℕ} (hN : 1 ≤ N) (p : FacePair k N) (hp : isEquator p) :
    pairStep hN p = p := by
  rcases hp with ⟨hr, hpi, hv⟩
  have hr0 : p.2.val ≠ 0 := by rw [hr]; simp
  have hrk : ¬ p.2.val < k + 1 := by rw [hr]; simp
  have hvb : ¬ 0 < (p.1.1.v (p.1.1.pi (Fin.last k))).val := by rw [hpi]; omega
  have hbne : ¬ p.1.1.pi (Fin.last k) ≠ Fin.last (k + 1) := not_not.mpr hpi
  unfold pairStep; rw [dif_neg hr0, dif_neg hrk, dif_neg hvb, dif_neg hbne]

private lemma pairStep_involutive {k N : ℕ} (hN : 1 ≤ N) (p : FacePair k N) :
    pairStep hN (pairStep hN p) = p := by
  rcases p with ⟨σ, r⟩
  by_cases hr0 : r.val = 0
  · have hr_eq : r = 0 := Fin.ext hr0
    by_cases hvb : (σ.1.v (σ.1.pi 0)).val + 1 < N
    · rw [pairStep_zeroStep hN (σ, r) hr0 hvb]
      set q := pairZeroStep σ hvb
      have hq_r : q.2.val ≠ 0 := by simp [q, pairZeroStep]
      have hq_rk : ¬ q.2.val < k + 1 := by simp [q, pairZeroStep]
      have hq_pilast : q.1.1.pi (Fin.last k) = σ.1.pi 0 := by simp [q, pairZeroStep]
      have hq_vb : 0 < (q.1.1.v (q.1.1.pi (Fin.last k))).val := by
        rw [hq_pilast]; simp [q, pairZeroStep]
      rw [pairStep_lastStep hN q hq_r hq_rk hq_vb]
      ext1
      · apply Subtype.ext
        refine CubeSimplex.ext_raw rfl ?_ rfl ?_
        · funext i; apply Fin.ext; dsimp only [pairLastStep]
          by_cases hib : i = σ.1.pi 0
          · rw [if_pos (by rw [hq_pilast]; exact hib)]
            dsimp only; rw [hq_pilast]; simp [q, pairZeroStep, hib]
          · rw [if_neg (by rw [hq_pilast]; exact hib)]
            simp [q, pairZeroStep, hib]
        · funext t
          dsimp only [pairLastStep]; rw [hq_pilast]
          split_ifs with ht
          · have : t = 0 := Fin.ext ht; subst this; rfl
          · simp only [q, pairZeroStep]
            have hlt : t.val - 1 + 1 < k + 1 := by omega
            simp only [hlt, ↓reduceDIte]
            congr 1; ext; dsimp; omega
      · exact hr_eq.symm
    · rw [pairStep_zeroCorner hN (σ, r) hr0 hvb]
      have hvb_eq : (σ.1.v (σ.1.pi 0)).val + 1 = N := by
        have := σ.1.hv_lt (σ.1.pi 0) (σ.1.hpi_ne 0); omega
      set q := pairZeroCorner hN σ hvb_eq
      have hq_r : q.2.val = 0 := by simp [q, pairZeroCorner]
      have hq_pi0 : q.1.1.pi 0 = σ.1.a := by simp [q, pairZeroCorner]
      have hq_a : q.1.1.a = σ.1.pi 0 := rfl
      have hq_vb : ¬ (q.1.1.v (q.1.1.pi 0)).val + 1 < N := by
        rw [hq_pi0]
        have hab : σ.1.a ≠ σ.1.pi 0 := (σ.1.hpi_ne 0).symm
        simp [q, pairZeroCorner, hab]; omega
      rw [pairStep_zeroCorner hN q hq_r hq_vb]
      ext1
      · apply Subtype.ext
        refine CubeSimplex.ext_raw (by simp [pairZeroCorner, hq_pi0]) ?_ rfl ?_
        · funext i; apply Fin.ext
          unfold pairZeroCorner; dsimp only
          by_cases hia : i = σ.1.a
          · rw [if_pos (by rw [hq_pi0]; exact hia)]
            dsimp only; simp [hia, σ.1.hv_a]
          · rw [if_neg (by rw [hq_pi0]; exact hia)]
            by_cases hib : i = σ.1.pi 0
            · rw [if_pos (by rw [hq_a]; exact hib)]
              dsimp only; rw [hib]; omega
            · rw [if_neg (by rw [hq_a]; exact hib)]
              simp [q, pairZeroCorner, hia, hib]
        · funext t
          unfold pairZeroCorner; dsimp only
          rw [hq_a]
          by_cases ht : t.val = 0
          · have ht0 : t = 0 := Fin.ext ht; subst ht0; simp
          · rw [if_neg ht]; dsimp only [q, pairZeroCorner]; rw [if_neg ht]
      · exact hr_eq.symm
  · by_cases hrk : r.val < k + 1
    · rw [pairStep_swapMid hN (σ, r) hr0 hrk]
      set q := pairSwapMid σ r (by omega) hrk
      have hq_r : q.2 = r := rfl
      rw [pairStep_swapMid hN q (by rwa [hq_r]) (by rwa [hq_r])]
      ext1
      · apply Subtype.ext
        dsimp only [pairSwapMid, q]
        refine CubeSimplex.ext_raw rfl rfl rfl ?_
        funext t; simp [Function.comp_apply]
      · rfl
    · have hr_last : r = Fin.last (k + 1) := by ext; simp [Fin.last]; omega
      by_cases hvb : 0 < (σ.1.v (σ.1.pi (Fin.last k))).val
      · rw [pairStep_lastStep hN (σ, r) hr0 hrk hvb]
        set q := pairLastStep σ hvb
        have hq_r : q.2.val = 0 := by simp [q, pairLastStep]
        have hq_pi0 : q.1.1.pi 0 = σ.1.pi (Fin.last k) := by simp [q, pairLastStep]
        have hq_vb : (q.1.1.v (q.1.1.pi 0)).val + 1 < N := by
          rw [hq_pi0]
          have hlt := σ.1.hv_lt (σ.1.pi (Fin.last k)) (σ.1.hpi_ne (Fin.last k))
          simp [q, pairLastStep]; omega
        rw [pairStep_zeroStep hN q hq_r hq_vb]
        ext1
        · apply Subtype.ext
          refine CubeSimplex.ext_raw rfl ?_ rfl ?_
          · funext i; apply Fin.ext; dsimp only [pairZeroStep]
            by_cases hib : i = σ.1.pi (Fin.last k)
            · rw [if_pos (by rw [hq_pi0]; exact hib)]
              dsimp only; rw [hq_pi0]; simp [q, pairLastStep, hib]; omega
            · rw [if_neg (by rw [hq_pi0]; exact hib)]
              simp [q, pairLastStep, hib]
          · funext t
            dsimp only [pairZeroStep]; rw [hq_pi0]
            split_ifs with ht
            · simp only [q, pairLastStep]
              have hne0 : (t.val + 1) ≠ 0 := by omega
              simp only [hne0, ↓reduceDIte]
              rfl
            · have : t = Fin.last k := by ext; simp [Fin.last]; omega
              rw [this]
        · exact hr_last.symm
      · by_cases hbne : σ.1.pi (Fin.last k) ≠ Fin.last (k + 1)
        · rw [pairStep_lastFlip hN (σ, r) hr0 hrk hvb hbne]
          set q := pairLastFlip σ hbne
          have hq_r : q.2.val ≠ 0 := by simp [q, pairLastFlip]
          have hq_rk : ¬ q.2.val < k + 1 := by simp [q, pairLastFlip]
          have hq_vb : ¬ 0 < (q.1.1.v (q.1.1.pi (Fin.last k))).val := hvb
          have hq_bne : q.1.1.pi (Fin.last k) ≠ Fin.last (k + 1) := hbne
          rw [pairStep_lastFlip hN q hq_r hq_rk hq_vb hq_bne]
          ext1
          · apply Subtype.ext
            refine CubeSimplex.ext_raw rfl rfl ?_ rfl
            funext i; simp only [pairLastFlip, q]; split_ifs <;> simp
          · exact hr_last.symm
        · push Not at hbne
          have heq : isEquator (σ, r) := ⟨hr_last, hbne, by dsimp only; rw [hbne] at hvb; omega⟩
          rw [pairStep_equator hN (σ, r) heq, pairStep_equator hN (σ, r) heq]

private lemma pairStep_ne_of_not_equator {k N : ℕ} (hN : 1 ≤ N) (p : FacePair k N)
    (hneq : ¬ isEquator p) : pairStep hN p ≠ p := by
  rcases p with ⟨σ, r⟩
  intro heq
  by_cases hr0 : r.val = 0
  · by_cases hvb : (σ.1.v (σ.1.pi 0)).val + 1 < N
    · rw [pairStep_zeroStep hN (σ, r) hr0 hvb] at heq
      have hr2 := congr_arg (fun q : FacePair k N => q.2.val) heq
      simp [pairZeroStep] at hr2; omega
    · rw [pairStep_zeroCorner hN (σ, r) hr0 hvb] at heq
      have ha := congr_arg (fun q : FacePair k N => q.1.1.a) heq
      simp [pairZeroCorner] at ha
      exact σ.1.hpi_ne 0 ha
  · by_cases hrk : r.val < k + 1
    · rw [pairStep_swapMid hN (σ, r) hr0 hrk] at heq
      have hpi := congr_arg (fun q : FacePair k N => q.1.1.pi ⟨r.val, hrk⟩) heq
      simp [pairSwapMid] at hpi
      have := congr_arg Fin.val (σ.1.hpi_inj hpi); dsimp at this; omega
    · by_cases hvb : 0 < (σ.1.v (σ.1.pi (Fin.last k))).val
      · rw [pairStep_lastStep hN (σ, r) hr0 hrk hvb] at heq
        have hr2 := congr_arg (fun q : FacePair k N => q.2.val) heq
        simp [pairLastStep] at hr2; omega
      · by_cases hbne : σ.1.pi (Fin.last k) ≠ Fin.last (k + 1)
        · rw [pairStep_lastFlip hN (σ, r) hr0 hrk hvb hbne] at heq
          have hs := congr_arg (fun q : FacePair k N => q.1.1.s (σ.1.pi (Fin.last k))) heq
          simp [pairLastFlip] at hs
        · push Not at hbne
          apply hneq
          refine ⟨by ext; simp [Fin.last]; omega, hbne, ?_⟩
          dsimp only; rw [hbne] at hvb; omega

private def faceVerts {k N : ℕ} (p : FacePair k N) : Finset (Fin (k + 2) → ℤ) :=
  (Finset.univ.erase p.2).image (vert p.1.1)

private lemma pairStep_preserves_faceVerts {k N : ℕ} (hN : 1 ≤ N) (p : FacePair k N) :
    faceVerts (pairStep hN p) = faceVerts p := by
  have hZeroStep : ∀ (σ : UpperSimplex k N) (hvb : (σ.1.v (σ.1.pi 0)).val + 1 < N),
      faceVerts (pairZeroStep σ hvb) = faceVerts (σ, 0) := by
    intro σ hvb
    set q := pairZeroStep σ hvb
    have hvert_shift : ∀ j : Fin (k + 1), vert q.1.1 j.castSucc = vert σ.1 j.succ := by
      intro j; funext i; unfold vert
      have hs : q.1.1.s i = σ.1.s i := rfl
      rw [hs]; congr 1
      by_cases hib : i = σ.1.pi 0
      · subst hib
        have hno : ¬ ∃ t : Fin (k + 1), t.val < j.castSucc.val ∧ q.1.1.pi t = σ.1.pi 0 := by
          rintro ⟨t, htj, ht⟩
          have hlt : t.val + 1 < k + 1 := by have := j.isLt; simp at htj; omega
          simp only [q, pairZeroStep, hlt, ↓reduceDIte] at ht
          have := congr_arg Fin.val (σ.1.hpi_inj ht); dsimp at this; omega
        have hyes : ∃ t : Fin (k + 1), t.val < j.succ.val ∧ σ.1.pi t = σ.1.pi 0 :=
          ⟨0, by simp, rfl⟩
        rw [if_neg hno, if_pos hyes]; simp [q, pairZeroStep]
      · have hv : (q.1.1.v i).val = (σ.1.v i).val := by simp [q, pairZeroStep, hib]
        rw [hv]; congr 1
        have heq : (∃ t : Fin (k + 1), t.val < j.castSucc.val ∧ q.1.1.pi t = i) ↔
            (∃ t : Fin (k + 1), t.val < j.succ.val ∧ σ.1.pi t = i) := by
          constructor
          · rintro ⟨t, htj, ht⟩
            have hlt : t.val + 1 < k + 1 := by have := j.isLt; simp at htj; omega
            simp only [q, pairZeroStep, hlt, ↓reduceDIte] at ht
            exact ⟨⟨t.val + 1, hlt⟩, by simp at htj ⊢; omega, ht⟩
          · rintro ⟨t, htj, ht⟩
            have ht0 : t.val ≠ 0 := by
              intro h0; have : t = 0 := Fin.ext h0; rw [this] at ht; exact hib ht.symm
            refine ⟨⟨t.val - 1, by omega⟩, by simp at htj ⊢; omega, ?_⟩
            have hlt : t.val - 1 + 1 < k + 1 := by have := t.isLt; omega
            simp only [q, pairZeroStep, hlt, ↓reduceDIte]
            convert ht using 2; ext; dsimp; omega
        rw [if_congr heq rfl rfl]
    ext x
    simp only [faceVerts, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hjlt : j.val < k + 1 := by
        have := j.isLt
        have hne : j.val ≠ k + 1 := fun h => hj (by ext; simp [q, pairZeroStep, Fin.last, h])
        omega
      let j0 : Fin (k + 1) := ⟨j.val, hjlt⟩
      exact ⟨j0.succ, Fin.succ_ne_zero _, (hvert_shift j0).symm⟩
    · rintro ⟨j, hj, rfl⟩
      have hjpos : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))
      let j0 : Fin (k + 1) := ⟨j.val - 1, by have := j.isLt; omega⟩
      refine ⟨j0.castSucc, ?_, ?_⟩
      · intro heq; have := congr_arg Fin.val heq; simp [q, pairZeroStep, Fin.last, j0] at this; omega
      · have hj_eq : j0.succ = j := by ext; simp [j0]; omega
        rw [hvert_shift j0, hj_eq]
  rcases p with ⟨σ, r⟩
  by_cases hr0 : r.val = 0
  · have hr_eq : r = 0 := Fin.ext hr0; subst hr_eq
    by_cases hvb : (σ.1.v (σ.1.pi 0)).val + 1 < N
    · rw [pairStep_zeroStep hN (σ, 0) rfl hvb]; exact hZeroStep σ hvb
    · rw [pairStep_zeroCorner hN (σ, 0) rfl hvb]
      have hvb_eq : (σ.1.v (σ.1.pi 0)).val + 1 = N := by
        have := σ.1.hv_lt (σ.1.pi 0) (σ.1.hpi_ne 0); omega
      set q := pairZeroCorner hN σ hvb_eq
      have hq_r : q.2 = 0 := rfl
      suffices h : ∀ j : Fin (k + 2), j ≠ 0 → vert q.1.1 j = vert σ.1 j by
        ext x
        simp only [faceVerts, hq_r, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
        exact ⟨fun ⟨j, hj, hx⟩ => ⟨j, hj, hx ▸ (h j hj).symm⟩,
               fun ⟨j, hj, hx⟩ => ⟨j, hj, hx ▸ h j hj⟩⟩
      intro j hj
      have hjpos : 0 < j.val := Nat.pos_of_ne_zero (fun h0 => hj (Fin.ext h0))
      funext i; unfold vert
      have hs : q.1.1.s i = σ.1.s i := rfl
      rw [hs]; congr 1
      by_cases hib : i = σ.1.pi 0
      · subst hib
        have hno : ¬ ∃ t : Fin (k + 1), t.val < j.val ∧ q.1.1.pi t = σ.1.pi 0 := by
          rintro ⟨t, _, ht⟩; exact q.1.1.hpi_ne t ht
        have hyes : ∃ t : Fin (k + 1), t.val < j.val ∧ σ.1.pi t = σ.1.pi 0 := ⟨0, hjpos, rfl⟩
        rw [if_neg hno, if_pos hyes]; simp [q, pairZeroCorner]; omega
      · by_cases hia : i = σ.1.a
        · subst hia
          have hyes : ∃ t : Fin (k + 1), t.val < j.val ∧ q.1.1.pi t = σ.1.a :=
            ⟨0, hjpos, by simp [q, pairZeroCorner]⟩
          have hno : ¬ ∃ t : Fin (k + 1), t.val < j.val ∧ σ.1.pi t = σ.1.a := by
            rintro ⟨t, _, ht⟩; exact σ.1.hpi_ne t ht
          rw [if_pos hyes, if_neg hno]; simp [q, pairZeroCorner, hib, σ.1.hv_a]; omega
        · have hv : (q.1.1.v i).val = (σ.1.v i).val := by simp [q, pairZeroCorner, hib, hia]
          rw [hv]; congr 1
          have heq : (∃ t : Fin (k + 1), t.val < j.val ∧ q.1.1.pi t = i) ↔
              (∃ t : Fin (k + 1), t.val < j.val ∧ σ.1.pi t = i) := by
            constructor
            · rintro ⟨t, htj, ht⟩
              simp only [q, pairZeroCorner] at ht
              split_ifs at ht with ht0
              · exact absurd ht.symm hia
              · exact ⟨t, htj, ht⟩
            · rintro ⟨t, htj, ht⟩
              have ht0 : t ≠ 0 := fun h0 => hib (h0 ▸ ht).symm
              exact ⟨t, htj, by simp [q, pairZeroCorner, ht0, ht]⟩
          rw [if_congr heq rfl rfl]
  · by_cases hrk : r.val < k + 1
    · rw [pairStep_swapMid hN (σ, r) hr0 hrk]
      set q := pairSwapMid σ r (by omega) hrk
      have hq_r : q.2 = r := rfl
      suffices h : ∀ j : Fin (k + 2), j ≠ r → vert q.1.1 j = vert σ.1 j by
        ext x
        simp only [faceVerts, hq_r, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
        exact ⟨fun ⟨j, hj, hx⟩ => ⟨j, hj, hx ▸ (h j hj).symm⟩,
               fun ⟨j, hj, hx⟩ => ⟨j, hj, hx ▸ h j hj⟩⟩
      intro j hj
      have hjr : j.val ≠ r.val := fun h => hj (Fin.ext h)
      let t1 : Fin (k + 1) := ⟨r.val - 1, by omega⟩
      let t2 : Fin (k + 1) := ⟨r.val, hrk⟩
      let e := Equiv.swap t1 t2
      funext i; unfold vert
      have hs : q.1.1.s i = σ.1.s i := rfl
      have hv : q.1.1.v i = σ.1.v i := rfl
      rw [hs, hv]; congr 2
      have heq : (∃ t : Fin (k + 1), t.val < j.val ∧ σ.1.pi (e t) = i) ↔
          (∃ t : Fin (k + 1), t.val < j.val ∧ σ.1.pi t = i) := by
        have hlt_inv : ∀ t : Fin (k + 1), (e t).val < j.val ↔ t.val < j.val := by
          intro t
          by_cases h1 : t = t1
          · subst h1; simp [e, t1, t2]; omega
          · by_cases h2 : t = t2
            · subst h2; simp [e, t1, t2]; omega
            · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
        exact ⟨fun ⟨t, htj, ht⟩ => ⟨e t, (hlt_inv t).mpr htj, ht⟩,
               fun ⟨t, htj, ht⟩ => ⟨e t, (hlt_inv t).mpr htj, by simpa [e] using ht⟩⟩
      simp only [q, pairSwapMid, Function.comp_apply]
      rw [if_congr heq rfl rfl]
    · have hr_last : r = Fin.last (k + 1) := by ext; simp [Fin.last]; omega
      subst hr_last
      by_cases hvb : 0 < (σ.1.v (σ.1.pi (Fin.last k))).val
      · rw [pairStep_lastStep hN (σ, Fin.last (k + 1)) hr0 hrk hvb]
        set q := pairLastStep σ hvb
        have hq_vb : (q.1.1.v (q.1.1.pi 0)).val + 1 < N := by
          have hlt := σ.1.hv_lt (σ.1.pi (Fin.last k)) (σ.1.hpi_ne (Fin.last k))
          simp [q, pairLastStep]; omega
        have hback : pairZeroStep q.1 hq_vb = (σ, Fin.last (k + 1)) := by
          have hinv := pairStep_involutive hN (σ, Fin.last (k + 1))
          have h1 : pairStep hN (σ, Fin.last (k + 1)) = q :=
            pairStep_lastStep hN (σ, Fin.last (k + 1)) hr0 hrk hvb
          rw [h1] at hinv
          have h2 : pairStep hN q = pairZeroStep q.1 hq_vb :=
            pairStep_zeroStep hN q rfl hq_vb
          rw [← h2]; exact hinv
        have hq0 : q = (q.1, 0) := rfl
        rw [hq0, ← hZeroStep q.1 hq_vb, hback]
      · by_cases hbne : σ.1.pi (Fin.last k) ≠ Fin.last (k + 1)
        · rw [pairStep_lastFlip hN (σ, Fin.last (k + 1)) hr0 hrk hvb hbne]
          set q := pairLastFlip σ hbne
          have hq_r : q.2 = Fin.last (k + 1) := rfl
          suffices h : ∀ j : Fin (k + 2), j ≠ Fin.last (k + 1) → vert q.1.1 j = vert σ.1 j by
            ext x
            simp only [faceVerts, hq_r, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
            exact ⟨fun ⟨j, hj, hx⟩ => ⟨j, hj, hx ▸ (h j hj).symm⟩,
                   fun ⟨j, hj, hx⟩ => ⟨j, hj, hx ▸ h j hj⟩⟩
          intro j hj
          have hjlt : j.val < k + 1 := by
            have := j.isLt; have : j.val ≠ k + 1 := fun h => hj (by ext; simp [Fin.last, h]); omega
          funext i; unfold vert
          by_cases hib : i = σ.1.pi (Fin.last k)
          · subst hib
            have hno : ¬ ∃ t : Fin (k + 1), t.val < j.val ∧ σ.1.pi t = σ.1.pi (Fin.last k) := by
              rintro ⟨t, htj, ht⟩
              have := congr_arg Fin.val (σ.1.hpi_inj ht); simp [Fin.last] at this; omega
            have hv0 : (σ.1.v (σ.1.pi (Fin.last k))).val = 0 := by omega
            simp [q, pairLastFlip, hno, hv0]
          · simp [q, pairLastFlip, hib]
        · push Not at hbne
          have heq : isEquator (σ, Fin.last (k + 1)) := ⟨rfl, hbne, by dsimp only; rw [hbne] at hvb; omega⟩
          rw [pairStep_equator hN (σ, Fin.last (k + 1)) heq]

private def embedEquator {k N : ℕ} (hN : 1 ≤ N) (τ : CubeSimplex k N) : FacePair k N :=
  (⟨{ a := τ.a.castSucc
      v := Fin.snoc τ.v ⟨0, by omega⟩
      s := Fin.snoc τ.s true
      pi := Fin.snoc (fun t => (τ.pi t).castSucc) (Fin.last (k + 1))
      hv_a := by simp [Fin.snoc_castSucc, τ.hv_a]
      hv_lt := by
        intro i
        refine Fin.lastCases ?_ (fun i' => ?_) i
        · intro _; simp [Fin.snoc_last]; omega
        · intro hi; simp only [Fin.snoc_castSucc]
          exact τ.hv_lt i' (fun h => hi (congr_arg Fin.castSucc h))
      hpi_inj := by
        intro t1 t2
        refine Fin.lastCases ?_ (fun t1' => ?_) t1 <;> refine Fin.lastCases ?_ (fun t2' => ?_) t2
        · intro _; rfl
        · intro h; simp only [Fin.snoc_last, Fin.snoc_castSucc] at h
          exact absurd h.symm (Fin.castSucc_ne_last _)
        · intro h; simp only [Fin.snoc_last, Fin.snoc_castSucc] at h
          exact absurd h (Fin.castSucc_ne_last _)
        · intro h; simp only [Fin.snoc_castSucc] at h
          exact congr_arg Fin.castSucc (τ.hpi_inj (Fin.castSucc_injective _ h))
      hpi_ne := by
        intro t
        refine Fin.lastCases ?_ (fun t' => ?_) t
        · simp only [Fin.snoc_last]; exact (Fin.castSucc_ne_last _).symm
        · simp only [Fin.snoc_castSucc]
          exact fun h => τ.hpi_ne t' (Fin.castSucc_injective _ h) }, by simp⟩, Fin.last (k + 1))

private lemma embedEquator_isEquator {k N : ℕ} (hN : 1 ≤ N) (τ : CubeSimplex k N) :
    isEquator (embedEquator hN τ) := ⟨rfl, by simp [embedEquator], by simp [embedEquator]⟩

private lemma embedEquator_inj {k N : ℕ} (hN : 1 ≤ N) :
    Function.Injective (@embedEquator k N hN) := by
  intro τ₁ τ₂ h
  have ha : τ₁.a = τ₂.a :=
    Fin.castSucc_injective _ (congr_arg (fun p : FacePair k N => p.1.1.a) h)
  have hv : τ₁.v = τ₂.v := by
    funext i; simpa [embedEquator] using congr_arg (fun p : FacePair k N => p.1.1.v i.castSucc) h
  have hs : τ₁.s = τ₂.s := by
    funext i; simpa [embedEquator] using congr_arg (fun p : FacePair k N => p.1.1.s i.castSucc) h
  have hpi : τ₁.pi = τ₂.pi := by
    funext t
    have ht := congr_arg (fun p : FacePair k N => p.1.1.pi t.castSucc) h
    simp only [embedEquator, Fin.snoc_castSucc] at ht
    exact Fin.castSucc_injective _ ht
  exact CubeSimplex.ext_raw ha hv hs hpi

private lemma embedEquator_surj {k N : ℕ} (hN : 1 ≤ N) (p : FacePair k N) (hp : isEquator p) :
    ∃ τ : CubeSimplex k N, embedEquator hN τ = p := by
  rcases p with ⟨⟨σ, hs_last⟩, r⟩
  rcases hp with ⟨rfl, hpi_last, hv_last⟩
  have ha_lt : σ.a.val < k + 1 := by
    have hne : σ.a ≠ Fin.last (k + 1) := by rw [← hpi_last]; exact (σ.hpi_ne (Fin.last k)).symm
    have := σ.a.isLt; have : σ.a.val ≠ k + 1 := fun h => hne (by ext; simp [Fin.last, h]); omega
  have hpi_lt : ∀ t : Fin k, (σ.pi t.castSucc).val < k + 1 := by
    intro t
    have hne : σ.pi t.castSucc ≠ Fin.last (k + 1) := by
      rw [← hpi_last]; intro h; exact Fin.castSucc_ne_last t (σ.hpi_inj h)
    have := (σ.pi t.castSucc).isLt
    have : (σ.pi t.castSucc).val ≠ k + 1 := fun h => hne (by ext; simp [Fin.last, h]); omega
  let τ : CubeSimplex k N :=
    { a := ⟨σ.a.val, ha_lt⟩
      v := fun i => σ.v i.castSucc
      s := fun i => σ.s i.castSucc
      pi := fun t => ⟨(σ.pi t.castSucc).val, hpi_lt t⟩
      hv_a := by
        have : (⟨σ.a.val, ha_lt⟩ : Fin (k + 1)).castSucc = σ.a := by ext; rfl
        rw [this]; exact σ.hv_a
      hv_lt := fun i hi => σ.hv_lt i.castSucc (fun h => hi (Fin.ext (by simpa using congr_arg Fin.val h)))
      hpi_inj := fun t1 t2 h => by
        have h1 : σ.pi t1.castSucc = σ.pi t2.castSucc := Fin.ext (by simpa using congr_arg Fin.val h)
        exact Fin.castSucc_injective _ (σ.hpi_inj h1)
      hpi_ne := fun t h => σ.hpi_ne t.castSucc (Fin.ext (by simpa using congr_arg Fin.val h)) }
  dsimp at hpi_last hv_last
  refine ⟨τ, ?_⟩
  ext1
  · apply Subtype.ext
    apply CubeSimplex.ext_raw (by ext; rfl)
    · funext i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · ext; simp [embedEquator, hv_last]
      · simp [embedEquator, τ]
    · funext i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · simp [embedEquator, hs_last]
      · simp [embedEquator, τ]
    · funext t
      refine Fin.lastCases ?_ (fun t' => ?_) t
      · simp [embedEquator, hpi_last]
      · ext; simp [embedEquator, τ]
  · rfl

private lemma embedEquator_faceVerts {k N : ℕ} (hN : 1 ≤ N) (τ : CubeSimplex k N) :
    faceVerts (embedEquator hN τ) =
      (Finset.univ.image (vert τ)).image (fun x => Fin.snoc x (0 : ℤ)) := by
  have hv_eq : ∀ j : Fin (k + 1),
      vert (embedEquator hN τ).1.1 j.castSucc = Fin.snoc (vert τ j) 0 := by
    intro j; funext i
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · simp only [Fin.snoc_last]; unfold vert
      have hno : ¬ ∃ t : Fin (k + 1), t.val < j.castSucc.val ∧
          (embedEquator hN τ).1.1.pi t = Fin.last (k + 1) := by
        rintro ⟨t, htj, ht⟩
        have hlt : t.val < k := by have := j.isLt; simp at htj; omega
        let t' : Fin k := ⟨t.val, hlt⟩
        have hteq : t = t'.castSucc := by ext; rfl
        rw [hteq] at ht; simp only [embedEquator, Fin.snoc_castSucc] at ht
        exact Fin.castSucc_ne_last _ ht
      rw [if_neg hno]; simp [embedEquator]
    · simp only [Fin.snoc_castSucc]; unfold vert
      have hs : (embedEquator hN τ).1.1.s i'.castSucc = τ.s i' := by simp [embedEquator]
      have hv : ((embedEquator hN τ).1.1.v i'.castSucc).val = (τ.v i').val := by simp [embedEquator]
      rw [hs, hv]; congr 2
      have heq : (∃ t : Fin (k + 1), t.val < j.castSucc.val ∧ (embedEquator hN τ).1.1.pi t = i'.castSucc) ↔
          (∃ t : Fin k, t.val < j.val ∧ τ.pi t = i') := by
        constructor
        · rintro ⟨t, htj, ht⟩
          have hlt : t.val < k := by have := j.isLt; simp at htj; omega
          let t' : Fin k := ⟨t.val, hlt⟩
          have hteq : t = t'.castSucc := by ext; rfl
          rw [hteq] at ht; simp only [embedEquator, Fin.snoc_castSucc] at ht
          exact ⟨t', by simpa [t'] using htj, Fin.castSucc_injective _ ht⟩
        · rintro ⟨t, htj, ht⟩; exact ⟨t.castSucc, by simpa using htj, by simp [embedEquator, ht]⟩
      rw [if_congr heq rfl rfl]
  ext x
  simp only [faceVerts, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hjlt : j.val < k + 1 := by
      have := j.isLt; have hne : j.val ≠ k + 1 := fun h => hj (by ext; simp [embedEquator, Fin.last, h]); omega
    let j0 : Fin (k + 1) := ⟨j.val, hjlt⟩
    exact ⟨vert τ j0, ⟨j0, rfl⟩, (hv_eq j0).symm⟩
  · rintro ⟨_, ⟨j0, rfl⟩, rfl⟩
    exact ⟨j0.castSucc, by simp [embedEquator, Fin.castSucc_ne_last], hv_eq j0⟩

private lemma sum_involution_zmod2 {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α) (g : α → ZMod 2) (S : Finset α)
    (hmem : ∀ a ∈ S, f a ∈ S) (hinv : ∀ a ∈ S, f (f a) = a)
    (hne : ∀ a ∈ S, f a ≠ a) (hg : ∀ a ∈ S, g (f a) = g a) :
    ∑ a ∈ S, g a = 0 := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hE : S = ∅
    · subst hE; simp
    · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hE
      have hfa : f a ∈ S := hmem a ha
      have hnea : f a ≠ a := hne a ha
      let S' := (S.erase a).erase (f a)
      have hS'_sub : S' ⊂ S := by
        refine Finset.ssubset_iff_subset_ne.mpr
          ⟨(Finset.erase_subset _ _).trans (Finset.erase_subset _ _), fun heq => ?_⟩
        have : a ∉ S' := fun h => (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase h)) rfl
        exact this (heq ▸ ha)
      have hS'_mem : ∀ x ∈ S', f x ∈ S' := by
        intro x hx
        have hx1 := Finset.ne_of_mem_erase hx
        have hx2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx)
        have hxS := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hmem x hxS⟩⟩
        · intro heq; have := congr_arg f heq; rw [hinv x hxS, hinv a ha] at this; exact hx2 this
        · intro heq; have := congr_arg f heq; rw [hinv x hxS] at this; exact hx1 this
      have hS'_sum : ∑ x ∈ S', g x = 0 :=
        ih S' hS'_sub hS'_mem
          (fun x hx => hinv x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)))
          (fun x hx => hne x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)))
          (fun x hx => hg x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)))
      have hfa_in : f a ∈ S.erase a := Finset.mem_erase.mpr ⟨hnea, hfa⟩
      rw [← Finset.add_sum_erase S g ha, ← Finset.add_sum_erase (S.erase a) g hfa_in]
      change g a + (g (f a) + ∑ x ∈ S', g x) = 0
      rw [hS'_sum, add_zero, hg a ha, zmod2_add_self]

private lemma kyFan_cube_parity (k N : ℕ) (hN : 1 ≤ N)
    (L : (Fin (k + 1) → ℤ) → ℤ)
    (hL_odd : ∀ x, L (-x) = -L x)
    (hL_nz : ∀ x, (∀ i, |x i| ≤ (N : ℤ)) → (∃ i, |x i| = (N : ℤ)) → L x ≠ 0)
    (hL_nocomp : ∀ (σ : CubeSimplex k N) (i j : Fin (k + 1)),
      L (vert σ i) + L (vert σ j) ≠ 0) :
    (∑ σ : CubeSimplex k N,
      (if IsPosAlt (k + 1) (Finset.univ.image (L ∘ vert σ)) then (1 : ZMod 2) else 0)) = 1 := by
  induction k with
  | zero =>
    have hfin1 : ∀ a b : Fin (0 + 1), a = b := fun a b => Fin.ext (by omega)
    let σpos : CubeSimplex 0 N :=
      { a := 0
        v := fun _ => ⟨N, by omega⟩
        s := fun _ => true
        pi := fun t => Fin.elim0 t
        hv_a := rfl
        hv_lt := fun i hi => absurd (hfin1 i 0) hi
        hpi_inj := fun t => Fin.elim0 t
        hpi_ne := fun t => Fin.elim0 t }
    let σneg : CubeSimplex 0 N := σpos.neg
    have hne : σpos ≠ σneg := by
      intro h; have := congr_arg (fun σ : CubeSimplex 0 N => σ.s 0) h
      simp [σpos, σneg, CubeSimplex.neg] at this
    have huniv : (Finset.univ : Finset (CubeSimplex 0 N)) = {σpos, σneg} := by
      ext σ; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      have ha : σ.a = 0 := hfin1 _ _
      have hv : σ.v = fun _ => ⟨N, by omega⟩ := by
        funext i; ext; rw [hfin1 i σ.a, σ.hv_a]
      have hpi : σ.pi = fun t => Fin.elim0 t := by funext t; exact Fin.elim0 t
      cases hs : σ.s 0
      · right; exact CubeSimplex.ext_raw ha hv (by funext i; rw [hfin1 i 0, hs]; rfl) hpi
      · left; exact CubeSimplex.ext_raw ha hv (by funext i; rw [hfin1 i 0, hs]) hpi
    rw [huniv, Finset.sum_pair hne]
    have hvn : vert σneg 0 = -vert σpos 0 := vert_neg σpos 0
    have hLp_nz : L (vert σpos 0) ≠ 0 :=
      hL_nz (vert σpos 0) (vert_abs_le σpos 0) ⟨0, vert_abs_a σpos 0⟩
    have hLn : L (vert σneg 0) = -L (vert σpos 0) := by rw [hvn, hL_odd]
    have himg : ∀ σ : CubeSimplex 0 N, Finset.univ.image (L ∘ vert σ) = {L (vert σ 0)} := by
      intro σ; ext y; simp
    have hPA1 : ∀ x : ℤ, IsPosAlt 1 {x} ↔ 0 < x := by
      intro x; constructor
      · intro h
        have hx := h.2 x (Finset.mem_singleton_self x)
        have hfilt : (({x} : Finset ℤ).filter (fun y => y.natAbs < x.natAbs)).card = 0 := by simp
        rw [hfilt] at hx; simpa [posSign] using hx
      · intro hx
        refine ⟨Finset.card_singleton x, fun y hy => ?_⟩
        rcases Finset.mem_singleton.mp hy with rfl
        have hfilt : (({y} : Finset ℤ).filter (fun z => z.natAbs < y.natAbs)).card = 0 := by simp
        rw [hfilt]; simpa [posSign] using hx
    rw [himg σpos, himg σneg, hPA1, hPA1, hLn]
    rcases lt_or_gt_of_ne hLp_nz with hlt | hgt
    · have h1 : ¬ (0 < L (vert σpos 0)) := by omega
      have h2 : 0 < -L (vert σpos 0) := by omega
      rw [if_neg h1, if_pos h2]; simp
    · have h1 : ¬ (0 < -L (vert σpos 0)) := by omega
      rw [if_pos hgt, if_neg h1]; simp
  | succ k ih =>
    have hUpper_eq :
        (∑ σ : UpperSimplex k N,
          ∑ r : Fin (k + 2),
            (if IsPosAlt (k + 1) ((Finset.univ.erase r).image (L ∘ vert σ.1))
             then (1 : ZMod 2) else 0)) =
        ∑ σ : UpperSimplex k N,
          (if IsPosAlt (k + 2) (Finset.univ.image (L ∘ vert σ.1)) ∨
              IsNegAlt (k + 2) (Finset.univ.image (L ∘ vert σ.1))
           then (1 : ZMod 2) else 0) := by
      refine Finset.sum_congr rfl fun σ _ => ?_
      exact kyFan_simplex_parity (L ∘ vert σ.1)
        (fun i => hL_nz (vert σ.1 i) (vert_abs_le σ.1 i) ⟨σ.1.a, vert_abs_a σ.1 i⟩)
        (fun i j => hL_nocomp σ.1 i j)
    have hLHS :
        (∑ σ : UpperSimplex k N,
          ∑ r : Fin (k + 2),
            (if IsPosAlt (k + 1) ((Finset.univ.erase r).image (L ∘ vert σ.1))
             then (1 : ZMod 2) else 0)) = 1 := by
      let g : FacePair k N → ZMod 2 :=
        fun p => if IsPosAlt (k + 1) ((faceVerts p).image L) then 1 else 0
      have hprod :
          (∑ σ : UpperSimplex k N,
            ∑ r : Fin (k + 2),
              (if IsPosAlt (k + 1) ((Finset.univ.erase r).image (L ∘ vert σ.1))
               then (1 : ZMod 2) else 0)) =
          ∑ p : FacePair k N, g p := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun r _ => ?_
        simp only [g, faceVerts, Finset.image_image]
      rw [hprod]
      let EqSet : Finset (FacePair k N) := Finset.univ.filter (fun p => isEquator p)
      let IntSet : Finset (FacePair k N) := Finset.univ.filter (fun p => ¬ isEquator p)
      have hsplit : ∑ p : FacePair k N, g p = (∑ p ∈ EqSet, g p) + ∑ p ∈ IntSet, g p := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => isEquator p) g]
      have hInt_zero : ∑ p ∈ IntSet, g p = 0 := by
        refine sum_involution_zmod2 (pairStep hN) g IntSet ?_ ?_ ?_ ?_
        · intro p hp
          simp only [IntSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          intro heq_p2
          have hfix : pairStep hN (pairStep hN p) = pairStep hN p :=
            pairStep_equator hN (pairStep hN p) heq_p2
          rw [pairStep_involutive hN p] at hfix
          exact pairStep_ne_of_not_equator hN p hp hfix.symm
        · intro p _; exact pairStep_involutive hN p
        · intro p hp
          simp only [IntSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          exact pairStep_ne_of_not_equator hN p hp
        · intro p _; simp only [g, pairStep_preserves_faceVerts hN p]
      have hEq_img : EqSet = Finset.univ.image (embedEquator hN) := by
        ext p
        simp only [EqSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        exact ⟨embedEquator_surj hN p, fun ⟨τ, hτ⟩ => hτ ▸ embedEquator_isEquator hN τ⟩
      have hEq_one : ∑ p ∈ EqSet, g p = 1 := by
        rw [hEq_img, Finset.sum_image (fun a _ b _ h => embedEquator_inj hN h)]
        let L' : (Fin (k + 1) → ℤ) → ℤ := fun x => L (Fin.snoc (α := fun _ => ℤ) x 0)
        have hL'_odd : ∀ x, L' (-x) = -L' x := by
          intro x
          have hsn : Fin.snoc (α := fun _ => ℤ) (-x) 0 = -Fin.snoc (α := fun _ => ℤ) x 0 := by
            funext i; refine Fin.lastCases ?_ (fun i' => ?_) i <;> simp
          simp only [L', hsn, hL_odd]
        have hL'_nz : ∀ x, (∀ i, |x i| ≤ (N : ℤ)) → (∃ i, |x i| = (N : ℤ)) → L' x ≠ 0 := by
          intro x hle ⟨i, hi⟩
          refine hL_nz (Fin.snoc (α := fun _ => ℤ) x 0) ?_ ⟨i.castSucc, by simpa using hi⟩
          intro j; refine Fin.lastCases ?_ (fun j' => ?_) j
          · simp
          · simpa using hle j'
        have hL'_nocomp : ∀ (τ : CubeSimplex k N) (i j : Fin (k + 1)),
            L' (vert τ i) + L' (vert τ j) ≠ 0 := by
          intro τ i j
          have hv : ∀ t : Fin (k + 1), Fin.snoc (vert τ t) 0 ∈ faceVerts (embedEquator hN τ) := by
            intro t; rw [embedEquator_faceVerts hN τ]
            exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ t))
          obtain ⟨i', _, hi'⟩ := Finset.mem_image.mp (hv i)
          obtain ⟨j', _, hj'⟩ := Finset.mem_image.mp (hv j)
          simp only [L', ← hi', ← hj']
          exact hL_nocomp (embedEquator hN τ).1.1 i' j'
        have hcongr : (∑ τ : CubeSimplex k N, g (embedEquator hN τ)) =
            ∑ τ : CubeSimplex k N,
              (if IsPosAlt (k + 1) (Finset.univ.image (L' ∘ vert τ)) then (1 : ZMod 2) else 0) := by
          refine Finset.sum_congr rfl fun τ _ => ?_
          simp only [g, embedEquator_faceVerts hN τ, Finset.image_image]; rfl
        rw [hcongr]; exact ih L' hL'_odd hL'_nz hL'_nocomp
      rw [hsplit, hEq_one, hInt_zero, add_zero]
    have hRHS :
        (∑ σ : UpperSimplex k N,
          (if IsPosAlt (k + 2) (Finset.univ.image (L ∘ vert σ.1)) ∨
              IsNegAlt (k + 2) (Finset.univ.image (L ∘ vert σ.1))
           then (1 : ZMod 2) else 0)) =
        ∑ σ : CubeSimplex (k + 1) N,
          (if IsPosAlt (k + 2) (Finset.univ.image (L ∘ vert σ)) then (1 : ZMod 2) else 0) := by
      have hdisj : ∀ σ : CubeSimplex (k + 1) N,
          ¬ (IsPosAlt (k + 2) (Finset.univ.image (L ∘ vert σ)) ∧
             IsNegAlt (k + 2) (Finset.univ.image (L ∘ vert σ))) := by
        intro σ ⟨hP, hN'⟩
        rw [isNegAlt_iff] at hN'
        have hmem : L (vert σ 0) ∈ Finset.univ.image (L ∘ vert σ) :=
          Finset.mem_image_of_mem _ (Finset.mem_univ 0)
        have h1 := hP.2 _ hmem; have h2 := hN'.2 _ hmem
        unfold posSign at h1 h2
        by_cases hev : Even (((Finset.univ.image (L ∘ vert σ)).filter
            (fun y => y.natAbs < (L (vert σ 0)).natAbs)).card)
        · have hodd : ¬ Even (((Finset.univ.image (L ∘ vert σ)).filter
              (fun y => y.natAbs < (L (vert σ 0)).natAbs)).card + 1) := by
            rw [Nat.even_add_one]; exact not_not.mpr hev
          rw [if_pos hev] at h1; rw [if_neg hodd] at h2; omega
        · have hev' : Even (((Finset.univ.image (L ∘ vert σ)).filter
              (fun y => y.natAbs < (L (vert σ 0)).natAbs)).card + 1) := by
            rw [Nat.even_add_one]; exact hev
          rw [if_neg hev] at h1; rw [if_pos hev'] at h2; omega
      have hneg_img : ∀ σ : CubeSimplex (k + 1) N,
          Finset.univ.image (L ∘ vert σ.neg) =
            (Finset.univ.image (L ∘ vert σ)).image (fun x => -x) := by
        intro σ; ext y
        simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply, vert_neg, hL_odd]
        exact ⟨fun ⟨i, hi⟩ => ⟨L (vert σ i), ⟨i, rfl⟩, hi⟩, fun ⟨_, ⟨i, hi⟩, hy⟩ => ⟨i, hi ▸ hy⟩⟩
      have hsplit_or :
          (∑ σ : UpperSimplex k N,
            (if IsPosAlt (k + 2) (Finset.univ.image (L ∘ vert σ.1)) ∨
                IsNegAlt (k + 2) (Finset.univ.image (L ∘ vert σ.1))
             then (1 : ZMod 2) else 0)) =
          (∑ σ : UpperSimplex k N,
            (if IsPosAlt (k + 2) (Finset.univ.image (L ∘ vert σ.1)) then (1 : ZMod 2) else 0)) +
          (∑ σ : UpperSimplex k N,
            (if IsPosAlt (k + 2) (Finset.univ.image (L ∘ vert σ.1.neg)) then (1 : ZMod 2) else 0)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun σ _ => ?_
        have hNA : IsNegAlt (k + 2) (Finset.univ.image (L ∘ vert σ.1)) ↔
            IsPosAlt (k + 2) (Finset.univ.image (L ∘ vert σ.1.neg)) := by
          unfold IsNegAlt; rw [hneg_img]
        rw [hNA]
        by_cases h1 : IsPosAlt (k + 2) (Finset.univ.image (L ∘ vert σ.1))
        · have h2 : ¬ IsPosAlt (k + 2) (Finset.univ.image (L ∘ vert σ.1.neg)) :=
            fun h => hdisj σ.1 ⟨h1, hNA.mpr h⟩
          simp [h1, h2]
        · by_cases h2 : IsPosAlt (k + 2) (Finset.univ.image (L ∘ vert σ.1.neg)) <;> simp [h1, h2]
      rw [hsplit_or]
      let P : CubeSimplex (k + 1) N → Prop := fun σ => σ.s (Fin.last (k + 1)) = true
      let hfun : CubeSimplex (k + 1) N → ZMod 2 :=
        fun σ => if IsPosAlt (k + 2) (Finset.univ.image (L ∘ vert σ)) then 1 else 0
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P hfun]
      congr 1
      · refine Finset.sum_bij (fun σ _ => σ.1)
          (fun σ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.2⟩)
          (fun _ _ _ _ h => Subtype.ext h)
          (fun σ hσ => ⟨⟨σ, (Finset.mem_filter.mp hσ).2⟩, Finset.mem_univ _, rfl⟩)
          (fun _ _ => rfl)
      · refine Finset.sum_bij (fun σ _ => σ.1.neg)
          (fun σ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [P, CubeSimplex.neg, σ.2]⟩)
          (fun _ _ _ _ h => Subtype.ext (by
            have := congr_arg CubeSimplex.neg h
            rwa [CubeSimplex.neg_involutive, CubeSimplex.neg_involutive] at this))
          (fun σ hσ => by
            have hfalse : σ.s (Fin.last (k + 1)) = false := by
              have := (Finset.mem_filter.mp hσ).2
              cases hs : σ.s (Fin.last (k + 1))
              · rfl
              · exact absurd hs this
            exact ⟨⟨σ.neg, by simp [CubeSimplex.neg, hfalse]⟩, Finset.mem_univ _,
              CubeSimplex.neg_involutive σ⟩)
          (fun _ _ => rfl)
    rw [← hRHS, ← hUpper_eq, hLHS]

private def cubeBdry (m : ℕ) : Set (Fin (m + 1) → ℝ) :=
  {x | (∀ i, |x i| ≤ 1) ∧ ∃ i, |x i| = 1}

private lemma mem_cubeBdry_iff_norm_eq_one {m : ℕ} (x : Fin (m + 1) → ℝ) :
    x ∈ cubeBdry m ↔ ‖x‖ = 1 := by
  have hne : (Finset.univ : Finset (Fin (m + 1))).Nonempty := ⟨0, Finset.mem_univ 0⟩
  constructor
  · rintro ⟨hle, i, hi⟩
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonneg (by norm_num)]
      intro j; simpa [Real.norm_eq_abs] using hle j
    · have h1 := norm_le_pi_norm x i
      simpa [Real.norm_eq_abs, hi] using h1
  · intro hn
    refine ⟨fun j => ?_, ?_⟩
    · have h1 := norm_le_pi_norm x j
      simpa [Real.norm_eq_abs, hn] using h1
    · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (fun j : Fin (m + 1) => ‖x j‖₊)
      refine ⟨i, ?_⟩
      have hsup : ‖x‖ = |x i| := by
        rw [Pi.norm_def, ← Finset.sup'_eq_sup hne, hi]
        simp [Real.norm_eq_abs]
      linarith

private lemma neg_mem_cubeBdry {m : ℕ} {x : Fin (m + 1) → ℝ} (hx : x ∈ cubeBdry m) :
    -x ∈ cubeBdry m := by
  rw [mem_cubeBdry_iff_norm_eq_one] at hx ⊢
  rwa [norm_neg]

private lemma cubeBdry_isCompact (m : ℕ) : IsCompact (cubeBdry m) := by
  have heq : cubeBdry m = Metric.sphere (0 : Fin (m + 1) → ℝ) 1 := by
    ext x; simp [mem_cubeBdry_iff_norm_eq_one]
  rw [heq]
  exact isCompact_sphere 0 1

private theorem borsuk_ulam (m : ℕ) (g : (Fin (m + 1) → ℝ) → (Fin m → ℝ))
    (hg_cont : ContinuousOn g (cubeBdry m)) (hg_odd : ∀ x ∈ cubeBdry m, g (-x) = -g x) :
    ∃ x ∈ cubeBdry m, g x = 0 := by
  by_contra hno
  push Not at hno
  have hBne : (cubeBdry m).Nonempty := ⟨fun _ => 1, fun _ => by simp, ⟨0, by simp⟩⟩
  have hBcomp : IsCompact (cubeBdry m) := cubeBdry_isCompact m
  obtain ⟨x₀, hx₀B, hx₀min⟩ :=
    hBcomp.exists_isMinOn hBne (continuous_norm.comp_continuousOn hg_cont)
  have hε : 0 < ‖g x₀‖ := norm_pos_iff.mpr (hno x₀ hx₀B)
  set ε := ‖g x₀‖
  have hge_ε : ∀ x ∈ cubeBdry m, ε ≤ ‖g x‖ := fun x hx => hx₀min hx
  have huc : UniformContinuousOn g (cubeBdry m) :=
    hBcomp.uniformContinuousOn_of_continuous hg_cont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδpos, hδ⟩ := huc ε hε
  obtain ⟨N, hN_gt⟩ := exists_nat_gt (1 / δ)
  have hN1 : 1 ≤ N := by
    have : (0 : ℝ) < N := lt_trans (div_pos zero_lt_one hδpos) hN_gt
    exact Nat.pos_of_ne_zero (fun h0 => by rw [h0] at this; simp at this)
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN1
  have hinv_lt : (1 : ℝ) / N < δ := by
    have h1 : 1 / δ * δ < N * δ := mul_lt_mul_of_pos_right hN_gt hδpos
    rw [div_mul_cancel₀ _ hδpos.ne'] at h1
    exact (div_lt_iff₀ hNpos).mpr (by linarith)
  let scale : (Fin (m + 1) → ℤ) → (Fin (m + 1) → ℝ) := fun p i => (p i : ℝ) / N
  have hscale_neg : ∀ p, scale (-p) = -scale p := by
    intro p; funext i; simp [scale, neg_div]
  have hscale_mem : ∀ p : Fin (m + 1) → ℤ,
      (∀ i, |p i| ≤ (N : ℤ)) → (∃ i, |p i| = (N : ℤ)) → scale p ∈ cubeBdry m := by
    intro p hle ⟨i, hi⟩
    refine ⟨fun j => ?_, ⟨i, ?_⟩⟩
    · simp only [scale, abs_div, abs_of_pos hNpos]
      rw [div_le_one hNpos]
      exact_mod_cast hle j
    · simp only [scale, abs_div, abs_of_pos hNpos]
      have : |(p i : ℝ)| = (N : ℝ) := by exact_mod_cast hi
      rw [this, div_self hNpos.ne']
  have hex_coord : ∀ p : Fin (m + 1) → ℤ,
      scale p ∈ cubeBdry m → ∃ i : Fin m, ε ≤ |g (scale p) i| := by
    intro p hpB
    have hnorm : ε ≤ ‖g (scale p)‖ := hge_ε (scale p) hpB
    by_cases hm0 : m = 0
    · subst hm0
      have hgz : g (scale p) = 0 := Subsingleton.elim _ _
      rw [hgz, norm_zero] at hnorm; linarith
    · have hne_fin : (Finset.univ : Finset (Fin m)).Nonempty :=
        Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero hm0⟩⟩
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne_fin (fun i => ‖g (scale p) i‖₊)
      have hsup : ‖g (scale p)‖ = |g (scale p) i| := by
        rw [Pi.norm_def, ← Finset.sup'_eq_sup hne_fin, hi]; simp [Real.norm_eq_abs]
      exact ⟨i, by linarith⟩
  let idxOf : ∀ (p : Fin (m + 1) → ℤ), scale p ∈ cubeBdry m → Fin m := fun p hB =>
    let hex_nat : ∃ k : ℕ, ∃ hk : k < m, ε ≤ |g (scale p) ⟨k, hk⟩| :=
      let ⟨j, hj⟩ := hex_coord p hB; ⟨j.val, j.isLt, hj⟩
    ⟨Nat.find hex_nat, (Nat.find_spec hex_nat).1⟩
  have hidxOf_ge : ∀ (p : Fin (m + 1) → ℤ) (hB : scale p ∈ cubeBdry m),
      ε ≤ |g (scale p) (idxOf p hB)| := fun p hB =>
    (Nat.find_spec (show ∃ k : ℕ, ∃ hk : k < m, ε ≤ |g (scale p) ⟨k, hk⟩| from
      let ⟨j, hj⟩ := hex_coord p hB; ⟨j.val, j.isLt, hj⟩)).2
  let L : (Fin (m + 1) → ℤ) → ℤ := fun p =>
    if hB : scale p ∈ cubeBdry m then
      let j := idxOf p hB
      if 0 < g (scale p) j then (j.val + 1 : ℤ) else -((j.val + 1 : ℤ))
    else 0
  have hL_odd : ∀ p, L (-p) = -L p := by
    intro p
    by_cases hB : scale p ∈ cubeBdry m
    · have hB' : scale (-p) ∈ cubeBdry m := by rw [hscale_neg]; exact neg_mem_cubeBdry hB
      have hval_eq : ∀ j : Fin m, g (scale (-p)) j = -g (scale p) j := by
        intro j; rw [hscale_neg, hg_odd _ hB, Pi.neg_apply]
      have habs_eq : ∀ j : Fin m, |g (scale (-p)) j| = |g (scale p) j| := by
        intro j; rw [hval_eq, abs_neg]
      have hidx : idxOf (-p) hB' = idxOf p hB := by
        apply Fin.ext
        dsimp only [idxOf]
        congr 1; funext k; simp only [habs_eq]
      simp only [L, hB, hB', ↓reduceDIte, hidx, hval_eq]
      have hge := hidxOf_ge p hB
      have hne0 : g (scale p) (idxOf p hB) ≠ 0 := fun hz => by rw [hz, abs_zero] at hge; linarith
      rcases lt_or_gt_of_ne hne0 with hlt | hgt
      · have hpos : 0 < -g (scale p) (idxOf p hB) := by linarith
        have hnot : ¬ (0 < g (scale p) (idxOf p hB)) := by linarith
        simp [hpos, hnot]
      · have hnot : ¬ (0 < -g (scale p) (idxOf p hB)) := by linarith
        simp [hgt, hnot]
    · have hB' : scale (-p) ∉ cubeBdry m := fun h =>
        hB (by have := neg_mem_cubeBdry h; rwa [hscale_neg, neg_neg] at this)
      simp [L, hB, hB']
  have hL_nz : ∀ p, (∀ i, |p i| ≤ (N : ℤ)) → (∃ i, |p i| = (N : ℤ)) → L p ≠ 0 := by
    intro p hle hex
    have hB := hscale_mem p hle hex
    simp only [L, hB, ↓reduceDIte]
    split_ifs <;> omega
  have hL_bound : ∀ p, (L p).natAbs ≤ m := by
    intro p
    by_cases hB : scale p ∈ cubeBdry m
    · simp only [L, hB, ↓reduceDIte]
      have hlt := (idxOf p hB).isLt
      split_ifs <;> omega
    · simp [L, hB]
  have hL_nocomp : ∀ (σ : CubeSimplex m N) (j₁ j₂ : Fin (m + 1)),
      L (vert σ j₁) + L (vert σ j₂) ≠ 0 := by
    intro σ j₁ j₂ hsum
    have hp1B : scale (vert σ j₁) ∈ cubeBdry m :=
      hscale_mem _ (vert_abs_le σ j₁) ⟨σ.a, vert_abs_a σ j₁⟩
    have hp2B : scale (vert σ j₂) ∈ cubeBdry m :=
      hscale_mem _ (vert_abs_le σ j₂) ⟨σ.a, vert_abs_a σ j₂⟩
    have hdist : dist (scale (vert σ j₁)) (scale (vert σ j₂)) < δ := by
      rw [dist_eq_norm]
      refine lt_of_le_of_lt ?_ hinv_lt
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      simp only [Pi.sub_apply, Real.norm_eq_abs, scale, ← sub_div, abs_div, abs_of_pos hNpos]
      rw [div_le_div_iff_of_pos_right hNpos]
      exact_mod_cast vert_diff_le_one σ j₁ j₂ i
    have hgdist : dist (g (scale (vert σ j₁))) (g (scale (vert σ j₂))) < ε :=
      hδ _ hp1B _ hp2B hdist
    simp only [L, hp1B, hp2B, ↓reduceDIte] at hsum
    set i1 := idxOf (vert σ j₁) hp1B
    set i2 := idxOf (vert σ j₂) hp2B
    have hge1' : ε ≤ |g (scale (vert σ j₁)) i1| := hidxOf_ge (vert σ j₁) hp1B
    have hge2' : ε ≤ |g (scale (vert σ j₂)) i2| := hidxOf_ge (vert σ j₂) hp2B
    split_ifs at hsum with hs1 hs2 hs2
    · omega
    · have hi_eq : i1 = i2 := Fin.ext (by omega)
      rw [hi_eq] at hs1 hge1'
      have hge1 : ε ≤ g (scale (vert σ j₁)) i2 := by rwa [abs_of_pos hs1] at hge1'
      have hge2 : g (scale (vert σ j₂)) i2 ≤ -ε := by
        rw [abs_of_nonpos (not_lt.mp hs2)] at hge2'; linarith
      have hcoord : |g (scale (vert σ j₁)) i2 - g (scale (vert σ j₂)) i2| < ε := by
        have hle := norm_le_pi_norm (g (scale (vert σ j₁)) - g (scale (vert σ j₂))) i2
        rw [dist_eq_norm] at hgdist
        simpa [Real.norm_eq_abs] using lt_of_le_of_lt hle hgdist
      rw [abs_of_pos (by linarith)] at hcoord; linarith
    · have hi_eq : i1 = i2 := Fin.ext (by omega)
      rw [hi_eq] at hs1 hge1'
      have hge1 : g (scale (vert σ j₁)) i2 ≤ -ε := by
        rw [abs_of_nonpos (not_lt.mp hs1)] at hge1'; linarith
      have hge2 : ε ≤ g (scale (vert σ j₂)) i2 := by rwa [abs_of_pos hs2] at hge2'
      have hcoord : |g (scale (vert σ j₁)) i2 - g (scale (vert σ j₂)) i2| < ε := by
        have hle := norm_le_pi_norm (g (scale (vert σ j₁)) - g (scale (vert σ j₂))) i2
        rw [dist_eq_norm] at hgdist
        simpa [Real.norm_eq_abs] using lt_of_le_of_lt hle hgdist
      rw [abs_of_neg (by linarith)] at hcoord; linarith
    · omega
  have hparity := kyFan_cube_parity m N hN1 L hL_odd hL_nz hL_nocomp
  have hzero : (∑ σ : CubeSimplex m N,
      (if IsPosAlt (m + 1) (Finset.univ.image (L ∘ vert σ)) then (1 : ZMod 2) else 0)) = 0 := by
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [if_neg]; intro hPA
    let S := Finset.univ.image (L ∘ vert σ)
    have hSsub : S.image Int.natAbs ⊆ Finset.Icc 1 m := by
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨x, hx, rfl⟩
      rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
      exact Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr
        (hL_nz (vert σ j) (vert_abs_le σ j) ⟨σ.a, vert_abs_a σ j⟩), hL_bound (vert σ j)⟩
    have hinj_abs : Set.InjOn Int.natAbs (S : Set ℤ) := by
      intro x hx y hy habs
      refine natAbs_inj_of_nocomp (fun z hz hnz' => ?_) hx hy habs
      rcases Finset.mem_image.mp hz with ⟨j₁, _, rfl⟩
      rcases Finset.mem_image.mp hnz' with ⟨j₂, _, hj₂⟩
      dsimp only [Function.comp_apply] at hj₂
      exact hL_nocomp σ j₁ j₂ (by omega)
    have hcard_eq : (S.image Int.natAbs).card = S.card := Finset.card_image_of_injOn hinj_abs
    have hle_m : (S.image Int.natAbs).card ≤ m :=
      (Finset.card_le_card hSsub).trans (by simp)
    have hSm : S.card = m + 1 := hPA.1
    omega
  rw [hzero] at hparity
  exact absurd hparity (by decide)

end BorsukUlam

/- ## Section 2: Convex Geometry Core (L1, L2, L3a-c, Avoidance) -/

section ConvexCore

private def gridPt {V : Type*} [AddCommGroup V] {n d : ℕ}
    (x : Fin n → Fin (d + 1) → V) (i : Fin n → Fin (d + 1)) : V :=
  ∑ k : Fin n, x k (i k)

private def ShattersN {V : Type*} [AddCommGroup V] (C : Set V) {n d : ℕ}
    (x : Fin n → Fin (d + 1) → V) (y : Set (Fin n → Fin (d + 1)) → V) : Prop :=
  ∀ (i : Fin n → Fin (d + 1)) (S : Set (Fin n → Fin (d + 1))),
    y S + gridPt x i ∈ C ↔ i ∈ S

private lemma strict_convex_pos {V : Type*} [AddCommGroup V] [Module ℝ V]
    {C : Set V} (hC : Convex ℝ C) {n d : ℕ}
    {x : Fin n → Fin (d + 1) → V} {y : Set (Fin n → Fin (d + 1)) → V}
    (hS : ShattersN C x y) (i₀ : Fin n → Fin (d + 1))
    (w : (Fin n → Fin (d + 1)) → ℝ)
    (hw0 : w i₀ = 0) (hw_nn : ∀ j, 0 ≤ w j) (hw_sum : ∑ j, w j = 1)
    (heq : ∑ j, w j • gridPt x j = gridPt x i₀) : False := by
  let S : Set (Fin n → Fin (d + 1)) := {j | j ≠ i₀}
  let T : Finset (Fin n → Fin (d + 1)) := Finset.univ.erase i₀
  have hTsum : ∑ j ∈ T, w j = 1 := by
    have := Finset.add_sum_erase Finset.univ w (Finset.mem_univ i₀)
    linarith
  have hTcomb : ∑ j ∈ T, w j • gridPt x j = gridPt x i₀ := by
    have := Finset.add_sum_erase Finset.univ (fun j => w j • gridPt x j) (Finset.mem_univ i₀)
    rw [hw0, zero_smul, zero_add] at this
    rw [this, heq]
  have hmem : ∑ j ∈ T, w j • (y S + gridPt x j) ∈ C := by
    refine hC.sum_mem (fun j _ => hw_nn j) hTsum fun j hj => ?_
    exact (hS j S).mpr (Finset.ne_of_mem_erase hj)
  have hrew : ∑ j ∈ T, w j • (y S + gridPt x j) = y S + gridPt x i₀ := by
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hTsum, one_smul, hTcomb]
  rw [hrew] at hmem
  exact (hS i₀ S).mp hmem rfl

private lemma forbidden_forward {V : Type*} [AddCommGroup V] [Module ℝ V]
    {C : Set V} (hC : Convex ℝ C) {n d : ℕ}
    {x : Fin n → Fin (d + 1) → V} {y : Set (Fin n → Fin (d + 1)) → V}
    (hS : ShattersN C x y) {Sa Sb : Set (Fin n → Fin (d + 1))}
    {q : Fin n → Fin (d + 1)} (hqb : q ∈ Sb) (hqa : q ∉ Sa)
    {ι : Type*} [Fintype ι] (pts : ι → (Fin n → Fin (d + 1)))
    (hpts : ∀ r, pts r ∈ Sa) (α : ι → ℝ) (hα : ∀ r, 0 ≤ α r)
    (hsum_pos : 0 < ∑ r, α r)
    (hw : y Sb - y Sa = ∑ r, α r • (gridPt x q - gridPt x (pts r))) : False := by
  set Λ := ∑ r, α r
  have hΛpos : 0 < Λ := hsum_pos
  have hΛ1 : 0 < Λ + 1 := by linarith
  have hz_mem : ∑ r, (α r / Λ) • (y Sa + gridPt x (pts r)) ∈ C := by
    refine hC.sum_mem (fun r _ => div_nonneg (hα r) hΛpos.le) ?_ fun r _ => (hS _ Sa).mpr (hpts r)
    rw [← Finset.sum_div, div_self hΛpos.ne']
  set z := ∑ r, (α r / Λ) • (y Sa + gridPt x (pts r))
  have hq_mem : y Sb + gridPt x q ∈ C := (hS q Sb).mpr hqb
  have hcomb : (Λ / (Λ + 1)) • z + (1 / (Λ + 1)) • (y Sb + gridPt x q) ∈ C := by
    refine hC hz_mem hq_mem (by positivity) (by positivity) ?_
    have : Λ + 1 ≠ 0 := hΛ1.ne'
    field_simp
  have hcomb_eq : (Λ / (Λ + 1)) • z + (1 / (Λ + 1)) • (y Sb + gridPt x q) = y Sa + gridPt x q := by
    apply smul_right_injective V hΛ1.ne'
    dsimp only
    have h1 : (Λ + 1) • ((Λ / (Λ + 1)) • z + (1 / (Λ + 1)) • (y Sb + gridPt x q)) =
        Λ • z + (y Sb + gridPt x q) := by
      simp only [smul_add, smul_smul, mul_div_cancel₀ _ hΛ1.ne', one_smul]
    have h2 : Λ • z = Λ • y Sa + ∑ r, α r • gridPt x (pts r) := by
      simp only [z, Finset.smul_sum, smul_add, smul_smul, mul_div_cancel₀ _ hΛpos.ne',
        Finset.sum_add_distrib, ← Finset.sum_smul]
      rw [← Finset.sum_div, mul_div_cancel₀ _ hΛpos.ne']
    have h3 : y Sb = y Sa + Λ • gridPt x q - ∑ r, α r • gridPt x (pts r) := by
      have hw' : y Sb - y Sa = Λ • gridPt x q - ∑ r, α r • gridPt x (pts r) := by
        simpa only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul] using hw
      calc y Sb = y Sa + (y Sb - y Sa) := by abel
        _ = y Sa + (Λ • gridPt x q - ∑ r, α r • gridPt x (pts r)) := by rw [hw']
        _ = y Sa + Λ • gridPt x q - ∑ r, α r • gridPt x (pts r) := by abel
    rw [h1, h2, h3]
    module
  rw [hcomb_eq] at hcomb
  exact hqa ((hS q Sa).mp hcomb)

private lemma forbidden_backward {V : Type*} [AddCommGroup V] [Module ℝ V]
    {C : Set V} (hC : Convex ℝ C) {n d : ℕ}
    {x : Fin n → Fin (d + 1) → V} {y : Set (Fin n → Fin (d + 1)) → V}
    (hS : ShattersN C x y) {Sa Sb : Set (Fin n → Fin (d + 1))}
    {p₀ : Fin n → Fin (d + 1)} (hpa : p₀ ∈ Sa) (hpb : p₀ ∉ Sb)
    {ι : Type*} [Fintype ι] (pts : ι → (Fin n → Fin (d + 1)))
    (hpts : ∀ r, pts r ∈ Sb) (β : ι → ℝ) (hβ : ∀ r, 0 ≤ β r)
    (hsum_pos : 0 < ∑ r, β r)
    (hw : y Sb - y Sa = ∑ r, β r • (gridPt x (pts r) - gridPt x p₀)) : False := by
  refine forbidden_forward hC hS (Sa := Sb) (Sb := Sa) hpa hpb pts hpts β hβ hsum_pos ?_
  calc y Sa - y Sb = -(y Sb - y Sa) := by abel
    _ = -(∑ r, β r • (gridPt x (pts r) - gridPt x p₀)) := by rw [hw]
    _ = ∑ r, β r • (gridPt x p₀ - gridPt x (pts r)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun r _ => by module

private lemma y_sub_ne_zero {V : Type*} [AddCommGroup V] {C : Set V} {n d : ℕ}
    {x : Fin n → Fin (d + 1) → V} {y : Set (Fin n → Fin (d + 1)) → V}
    (hS : ShattersN C x y) {Sa Sb : Set (Fin n → Fin (d + 1))}
    {q : Fin n → Fin (d + 1)} (hqb : q ∈ Sb) (hqa : q ∉ Sa) : y Sb - y Sa ≠ 0 := by
  intro h0
  have heq : y Sb = y Sa := sub_eq_zero.mp h0
  have hin : y Sb + gridPt x q ∈ C := (hS q Sb).mpr hqb
  rw [heq] at hin
  exact hqa ((hS q Sa).mp hin)

private def coneCoord (ak : Fin 3) (c : Fin 2 → ℝ) : Fin 2 → ℝ :=
  match ak with
  | 0 => ![c 0, c 1]
  | 1 => ![-(c 0 + c 1), c 1]
  | 2 => ![-(c 0 + c 1), c 0]

private def coneOther (ak : Fin 3) : Fin 2 → Fin 3 :=
  match ak with
  | 0 => ![1, 2]
  | 1 => ![0, 2]
  | 2 => ![0, 1]

private lemma coneOther_ne (ak : Fin 3) (r : Fin 2) : coneOther ak r ≠ ak := by
  fin_cases ak <;> fin_cases r <;> decide

private lemma coneOther_inj (ak : Fin 3) : Function.Injective (coneOther ak) := by
  intro r1 r2 h
  fin_cases ak <;> fin_cases r1 <;> fin_cases r2 <;> simp [coneOther] at h ⊢

private lemma coneCoord_vec {V : Type*} [AddCommGroup V] [Module ℝ V]
    (xk : Fin 3 → V) (ak : Fin 3) (c : Fin 2 → ℝ) :
    coneCoord ak c 0 • (xk (coneOther ak 0) - xk ak) +
    coneCoord ak c 1 • (xk (coneOther ak 1) - xk ak) =
    c 0 • (xk 1 - xk 0) + c 1 • (xk 2 - xk 0) := by
  fin_cases ak <;> simp [coneCoord, coneOther] <;> module

private lemma coneCoord_cubic (ak : Fin 3) (c : Fin 2 → ℝ) :
    coneCoord ak c 0 * coneCoord ak c 1 * (coneCoord ak c 0 + coneCoord ak c 1) =
    c 0 * c 1 * (c 0 + c 1) := by
  fin_cases ak <;> simp [coneCoord] <;> ring

private lemma coneCoord_add (ak : Fin 3) (c₁ c₂ : Fin 2 → ℝ) (r : Fin 2) :
    coneCoord ak (c₁ + c₂) r = coneCoord ak c₁ r + coneCoord ak c₂ r := by
  fin_cases ak <;> fin_cases r <;> simp [coneCoord] <;> ring

private lemma coneCoord_smul (ak : Fin 3) (t : ℝ) (c : Fin 2 → ℝ) (r : Fin 2) :
    coneCoord ak (t • c) r = t * coneCoord ak c r := by
  fin_cases ak <;> fin_cases r <;> simp [coneCoord] <;> ring

private lemma cubic_pos_iff (c : Fin 2 → ℝ) :
    0 < c 0 * c 1 * (c 0 + c 1) ↔
      ∃ ak : Fin 3, 0 < coneCoord ak c 0 ∧ 0 < coneCoord ak c 1 := by
  constructor
  · intro hpos
    by_cases h0 : 0 < c 0 <;> by_cases h1 : 0 < c 1
    · exact ⟨0, by simp [coneCoord, h0, h1]⟩
    · have h1lt : c 1 < 0 := lt_of_le_of_ne (not_lt.mp h1) (fun hz => by rw [hz] at hpos; simp at hpos)
      have hsum : c 0 + c 1 < 0 := by nlinarith [mul_neg_of_pos_of_neg h0 h1lt]
      exact ⟨2, by simp [coneCoord]; constructor <;> linarith⟩
    · have h0lt : c 0 < 0 := lt_of_le_of_ne (not_lt.mp h0) (fun hz => by rw [hz] at hpos; simp at hpos)
      have hsum : c 0 + c 1 < 0 := by nlinarith [mul_neg_of_neg_of_pos h0lt h1]
      exact ⟨1, by simp [coneCoord]; constructor <;> linarith⟩
    · have h0le : c 0 ≤ 0 := not_lt.mp h0
      have h1le : c 1 ≤ 0 := not_lt.mp h1
      nlinarith [mul_nonneg (neg_nonneg.mpr h0le) (neg_nonneg.mpr h1le)]
  · rintro ⟨ak, h0, h1⟩
    rw [← coneCoord_cubic ak c]
    positivity

private lemma cubic_nonneg_iff (c : Fin 2 → ℝ) :
    0 ≤ c 0 * c 1 * (c 0 + c 1) ↔
      ∃ ak : Fin 3, 0 ≤ coneCoord ak c 0 ∧ 0 ≤ coneCoord ak c 1 := by
  constructor
  · intro hnn
    rcases eq_or_lt_of_le hnn with h0 | hpos
    · have hmul : c 0 = 0 ∨ c 1 = 0 ∨ c 0 + c 1 = 0 := by
        rcases mul_eq_zero.mp h0.symm with h | h
        · rcases mul_eq_zero.mp h with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr h)
      rcases hmul with h | h | h
      · rcases le_total 0 (c 1) with h1 | h1
        · exact ⟨0, by simp [coneCoord, h, h1]⟩
        · exact ⟨2, by simp [coneCoord, h]; linarith⟩
      · rcases le_total 0 (c 0) with h1 | h1
        · exact ⟨0, by simp [coneCoord, h, h1]⟩
        · exact ⟨1, by simp [coneCoord, h]; linarith⟩
      · rcases le_total 0 (c 0) with h1 | h1
        · exact ⟨2, by simp [coneCoord, h, h1]⟩
        · exact ⟨1, by simp [coneCoord, h]; linarith⟩
    · rcases (cubic_pos_iff c).mp hpos with ⟨ak, h1, h2⟩
      exact ⟨ak, h1.le, h2.le⟩
  · rintro ⟨ak, h0, h1⟩
    rw [← coneCoord_cubic ak c]
    positivity

private lemma coneCoord_pos_unique {c : Fin 2 → ℝ} {a₁ a₂ : Fin 3}
    (h1 : 0 < coneCoord a₁ c 0 ∧ 0 < coneCoord a₁ c 1)
    (h2 : 0 < coneCoord a₂ c 0 ∧ 0 < coneCoord a₂ c 1) : a₁ = a₂ := by
  fin_cases a₁ <;> fin_cases a₂ <;> simp [coneCoord] at h1 h2 ⊢ <;> linarith

private def sumMap {n : ℕ} (x : Fin n → Fin 3 → (Fin (n + 1) → ℝ)) :
    (Fin n → Fin 2 → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun c := ∑ k : Fin n, (c k 0 • (x k 1 - x k 0) + c k 1 • (x k 2 - x k 0))
  map_add' c₁ c₂ := by
    simp only [Pi.add_apply, add_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => by module
  map_smul' t c := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_add, smul_smul]

private lemma no_pos_sum {n : ℕ} {C : Set (Fin (n + 1) → ℝ)} (hC : Convex ℝ C)
    {x : Fin n → Fin 3 → (Fin (n + 1) → ℝ)}
    {y : Set (Fin n → Fin 3) → (Fin (n + 1) → ℝ)}
    (hS : ShattersN C x y) {c : Fin n → Fin 2 → ℝ}
    (hker : sumMap x c = 0) (hne : c ≠ 0) (a : Fin n → Fin 3)
    (hnn : ∀ k r, 0 ≤ coneCoord (a k) (c k) r) : False := by
  let Sval : ℝ := ∑ k : Fin n, ∑ r : Fin 2, coneCoord (a k) (c k) r
  have hSpos : 0 < Sval := by
    by_contra hle
    push Not at hle
    have hall0 : ∀ k r, coneCoord (a k) (c k) r = 0 := by
      intro k r
      have hsum0 : Sval = 0 := le_antisymm hle
        (Finset.sum_nonneg fun k' _ => Finset.sum_nonneg fun r' _ => hnn k' r')
      have hk0 : ∑ r' : Fin 2, coneCoord (a k) (c k) r' = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun k' _ =>
          Finset.sum_nonneg fun r' _ => hnn k' r').mp hsum0 k (Finset.mem_univ k)
      exact (Finset.sum_eq_zero_iff_of_nonneg fun r' _ => hnn k r').mp hk0 r (Finset.mem_univ r)
    apply hne
    funext k r
    have h0 := hall0 k 0; have h1 := hall0 k 1
    generalize a k = ak at h0 h1
    fin_cases ak <;> fin_cases r <;> simp [coneCoord] at h0 h1 ⊢ <;> linarith
  let stepPt : Fin n × Fin 2 → (Fin n → Fin 3) :=
    fun p => Function.update a p.1 (coneOther (a p.1) p.2)
  have hstep_ne : ∀ p : Fin n × Fin 2, stepPt p ≠ a := by
    intro p heq
    have := congr_fun heq p.1
    simp only [stepPt, Function.update_self] at this
    exact coneOther_ne (a p.1) p.2 this
  have hstep_inj : Function.Injective stepPt := by
    intro p1 p2 h
    by_cases hk : p1.1 = p2.1
    · have hr := congr_fun h p1.1
      simp only [stepPt, hk, Function.update_self] at hr
      exact Prod.ext hk (coneOther_inj (a p2.1) hr)
    · have h1 := congr_fun h p1.1
      simp only [stepPt, Function.update_self, Function.update_of_ne hk] at h1
      exact absurd h1 (coneOther_ne (a p1.1) p1.2)
  let w : (Fin n → Fin 3) → ℝ := fun j =>
    if h : ∃ p : Fin n × Fin 2, stepPt p = j then
      coneCoord (a h.choose.1) (c h.choose.1) h.choose.2 / Sval
    else 0
  have hw_step : ∀ p : Fin n × Fin 2, w (stepPt p) = coneCoord (a p.1) (c p.1) p.2 / Sval := by
    intro p
    have hex : ∃ q : Fin n × Fin 2, stepPt q = stepPt p := ⟨p, rfl⟩
    simp only [w, hex, ↓reduceDIte]
    rw [hstep_inj hex.choose_spec]
  have hw0 : w a = 0 := by
    have hno : ¬ ∃ p : Fin n × Fin 2, stepPt p = a := fun ⟨p, hp⟩ => hstep_ne p hp
    simp only [w, hno, ↓reduceDIte]
  have hw_nn : ∀ j, 0 ≤ w j := by
    intro j
    by_cases h : ∃ p, stepPt p = j
    · simp only [w, h, ↓reduceDIte]; exact div_nonneg (hnn _ _) hSpos.le
    · simp only [w, h, ↓reduceDIte, le_rfl]
  have hsum_w : ∑ j, w j = 1 := by
    have hsub : ∑ j, w j = ∑ j ∈ Finset.univ.image stepPt, w j := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
      have hno : ¬ ∃ p, stepPt p = j := by
        rintro ⟨p, rfl⟩; exact hj (Finset.mem_image_of_mem _ (Finset.mem_univ p))
      simp only [w, hno, ↓reduceDIte]
    rw [hsub, Finset.sum_image (fun a _ b _ h => hstep_inj h)]
    simp only [hw_step, ← Finset.sum_div, Fintype.sum_prod_type]
    exact div_self hSpos.ne'
  have hsum_pt : ∑ j, w j • gridPt x j = gridPt x a := by
    have hsub : ∑ j, w j • gridPt x j = ∑ j ∈ Finset.univ.image stepPt, w j • gridPt x j := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
      have hno : ¬ ∃ p, stepPt p = j := by
        rintro ⟨p, rfl⟩; exact hj (Finset.mem_image_of_mem _ (Finset.mem_univ p))
      simp only [w, hno, ↓reduceDIte, zero_smul]
    rw [hsub, Finset.sum_image (fun a _ b _ h => hstep_inj h)]
    have hdiff : ∑ p : Fin n × Fin 2, (coneCoord (a p.1) (c p.1) p.2 / Sval) •
        (gridPt x (stepPt p) - gridPt x a) = 0 := by
      have hpt : ∀ p : Fin n × Fin 2,
          gridPt x (stepPt p) - gridPt x a = x p.1 (coneOther (a p.1) p.2) - x p.1 (a p.1) := by
        intro p; unfold gridPt stepPt
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single p.1]
        · simp
        · intro k _ hk; simp [Function.update_of_ne hk]
        · intro h; exact absurd (Finset.mem_univ p.1) h
      simp only [hpt, div_eq_inv_mul, ← smul_smul, ← Finset.smul_sum]
      have hinner : ∑ p : Fin n × Fin 2,
          coneCoord (a p.1) (c p.1) p.2 • (x p.1 (coneOther (a p.1) p.2) - x p.1 (a p.1)) = 0 := by
        rw [Fintype.sum_prod_type]
        calc ∑ k : Fin n, ∑ r : Fin 2,
              coneCoord (a k) (c k) r • (x k (coneOther (a k) r) - x k (a k))
            = ∑ k : Fin n, (c k 0 • (x k 1 - x k 0) + c k 1 • (x k 2 - x k 0)) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Fin.sum_univ_two]; exact coneCoord_vec (x k) (a k) (c k)
          _ = sumMap x c := rfl
          _ = 0 := hker
      rw [hinner, smul_zero]
    have hsplit : ∑ p : Fin n × Fin 2, w (stepPt p) • gridPt x (stepPt p) -
        (∑ p : Fin n × Fin 2, w (stepPt p)) • gridPt x a = 0 := by
      simpa only [hw_step, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul] using hdiff
    have hsum1 : ∑ p : Fin n × Fin 2, w (stepPt p) = 1 := by
      simp only [hw_step, ← Finset.sum_div, Fintype.sum_prod_type]
      exact div_self hSpos.ne'
    rw [hsum1, one_smul, sub_eq_zero] at hsplit
    exact hsplit
  exact strict_convex_pos hC hS a w hw0 hw_nn hsum_w hsum_pt

private def cubicF {n : ℕ} (c : Fin n → Fin 2 → ℝ) (k : Fin n) : ℝ :=
  c k 0 * c k 1 * (c k 0 + c k 1)

private lemma cubicF_neg {n : ℕ} (c : Fin n → Fin 2 → ℝ) : cubicF (-c) = -cubicF c := by
  funext k; simp [cubicF]; ring

private lemma cubicF_smul {n : ℕ} (t : ℝ) (c : Fin n → Fin 2 → ℝ) (k : Fin n) :
    cubicF (t • c) k = t ^ 3 * cubicF c k := by
  simp [cubicF]; ring

private lemma continuous_cubicF {n : ℕ} (k : Fin n) :
    Continuous (fun c : Fin n → Fin 2 → ℝ => cubicF c k) := by
  unfold cubicF; fun_prop

private lemma cubicF_not_nonneg {n : ℕ} {C : Set (Fin (n + 1) → ℝ)} (hC : Convex ℝ C)
    {x : Fin n → Fin 3 → (Fin (n + 1) → ℝ)}
    {y : Set (Fin n → Fin 3) → (Fin (n + 1) → ℝ)}
    (hS : ShattersN C x y) {c : Fin n → Fin 2 → ℝ}
    (hker : sumMap x c = 0) (hne : c ≠ 0) (hnn : ∀ k, 0 ≤ cubicF c k) : False := by
  have hex : ∀ k, ∃ ak : Fin 3, 0 ≤ coneCoord ak (c k) 0 ∧ 0 ≤ coneCoord ak (c k) 1 :=
    fun k => (cubic_nonneg_iff (c k)).mp (hnn k)
  let a : Fin n → Fin 3 := fun k => (hex k).choose
  refine no_pos_sum hC hS hker hne a fun k r => ?_
  fin_cases r
  · exact (hex k).choose_spec.1
  · exact (hex k).choose_spec.2

private lemma cubicF_not_nonpos {n : ℕ} {C : Set (Fin (n + 1) → ℝ)} (hC : Convex ℝ C)
    {x : Fin n → Fin 3 → (Fin (n + 1) → ℝ)}
    {y : Set (Fin n → Fin 3) → (Fin (n + 1) → ℝ)}
    (hS : ShattersN C x y) {c : Fin n → Fin 2 → ℝ}
    (hker : sumMap x c = 0) (hne : c ≠ 0) (hnp : ∀ k, cubicF c k ≤ 0) : False := by
  refine cubicF_not_nonneg hC hS (c := -c) (by rw [map_neg, hker, neg_zero])
    (neg_ne_zero.mpr hne) fun k => ?_
  have := hnp k; rw [cubicF_neg, Pi.neg_apply]; linarith

private lemma ker_finrank_and_surj {m : ℕ}
    {C : Set (Fin (m + 3) → ℝ)} (hC : Convex ℝ C)
    {x : Fin (m + 2) → Fin 3 → (Fin (m + 3) → ℝ)}
    {y : Set (Fin (m + 2) → Fin 3) → (Fin (m + 3) → ℝ)}
    (hS : ShattersN C x y) :
    Module.finrank ℝ (LinearMap.ker (sumMap x)) = m + 1 ∧
    Function.Surjective (sumMap x) := by
  have hdom : Module.finrank ℝ (Fin (m + 2) → Fin 2 → ℝ) = 2 * (m + 2) := by
    rw [Module.finrank_pi_fintype]
    simp [mul_comm]
  have hcod : Module.finrank ℝ (Fin (m + 3) → ℝ) = m + 3 := by simp
  have hrk := LinearMap.finrank_range_add_finrank_ker (sumMap x)
  have hle_cod : Module.finrank ℝ (LinearMap.range (sumMap x)) ≤ m + 3 :=
    (Submodule.finrank_le _).trans hcod.le
  have hge : m + 1 ≤ Module.finrank ℝ (LinearMap.ker (sumMap x)) := by omega
  have hlt : Module.finrank ℝ (LinearMap.ker (sumMap x)) < m + 2 := by
    by_contra hbig
    push Not at hbig
    have hex_ι : ∃ ι : (Fin (m + 2) → ℝ) →ₗ[ℝ] (Fin (m + 2) → Fin 2 → ℝ),
        (∀ v, sumMap x (ι v) = 0) ∧ (∀ v, ι v = 0 → v = 0) := by
      set W := LinearMap.ker (sumMap x)
      let bW := Module.finBasis ℝ W
      let ι : (Fin (m + 2) → ℝ) →ₗ[ℝ] (Fin (m + 2) → Fin 2 → ℝ) :=
        { toFun := fun v => ∑ j : Fin (m + 2), v j • (bW (Fin.castLE hbig j)).1
          map_add' := fun v₁ v₂ => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
          map_smul' := fun t v => by
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul] }
      refine ⟨ι, ?_, ?_⟩
      · intro v
        simp only [ι, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [(bW (Fin.castLE hbig j)).2, smul_zero]
      · intro v hv
        have hvW : (∑ j : Fin (m + 2), v j • bW (Fin.castLE hbig j) : W) = 0 := by
          apply Subtype.ext
          simpa only [ι, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum,
            Submodule.coe_smul_of_tower, ZeroMemClass.coe_zero] using hv
        let extv : Fin (Module.finrank ℝ W) → ℝ := fun i =>
          if hi : i.val < m + 2 then v ⟨i.val, hi⟩ else 0
        have hext : ∑ i : Fin (Module.finrank ℝ W), extv i • bW i = 0 := by
          rw [← hvW]
          have hsub : ∑ i : Fin (Module.finrank ℝ W), extv i • bW i =
              ∑ i ∈ Finset.univ.image (Fin.castLE hbig), extv i • bW i := by
            symm
            refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
            have hnot : ¬ i.val < m + 2 := fun hlt' =>
              hi (Finset.mem_image.mpr ⟨⟨i.val, hlt'⟩, Finset.mem_univ _, by ext; rfl⟩)
            simp [extv, hnot]
          rw [hsub, Finset.sum_image (fun a _ b _ h => Fin.castLE_injective hbig h)]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp [extv, j.isLt]
        have hall := Fintype.linearIndependent_iff.mp bW.linearIndependent extv hext
        funext j
        have hj := hall (Fin.castLE hbig j)
        simpa [extv, j.isLt] using hj
    obtain ⟨ι, hι_ker, hι_inj⟩ := hex_ι
    have hι_cont : Continuous (fun v => ι v) := LinearMap.continuous_of_finiteDimensional ι
    have hcomp_cont : ∀ k : Fin (m + 2), Continuous (fun v => cubicF (ι v) k) :=
      fun k => (continuous_cubicF k).comp hι_cont
    let g : (Fin (m + 2) → ℝ) → (Fin (m + 1) → ℝ) :=
      fun v k => cubicF (ι v) k.succ - cubicF (ι v) 0
    have hg_cont : ContinuousOn g (cubeBdry (m + 1)) :=
      (continuous_pi fun k : Fin (m + 1) => (hcomp_cont k.succ).sub (hcomp_cont 0)).continuousOn
    have hg_odd : ∀ v ∈ cubeBdry (m + 1), g (-v) = -g v := by
      intro v _
      funext k
      simp only [g, Pi.neg_apply, map_neg, cubicF_neg]; ring
    obtain ⟨v, hvB, hgv⟩ := borsuk_ulam (m + 1) g hg_cont hg_odd
    have hvne : v ≠ 0 := by
      intro hz; have := (mem_cubeBdry_iff_norm_eq_one v).mp hvB; rw [hz, norm_zero] at this; norm_num at this
    have hιv_ne : ι v ≠ 0 := fun h => hvne (hι_inj v h)
    have hconst : ∀ k : Fin (m + 2), cubicF (ι v) k = cubicF (ι v) 0 := by
      intro k
      refine Fin.cases rfl (fun k' => ?_) k
      have := congr_fun hgv k'
      simp only [g, Pi.zero_apply] at this
      linarith
    rcases le_total 0 (cubicF (ι v) 0) with hnn | hnp
    · exact cubicF_not_nonneg hC hS (hι_ker v) hιv_ne (fun k => by rw [hconst k]; exact hnn)
    · exact cubicF_not_nonpos hC hS (hι_ker v) hιv_ne (fun k => by rw [hconst k]; exact hnp)
  have hker_eq : Module.finrank ℝ (LinearMap.ker (sumMap x)) = m + 1 := by omega
  have hrng_eq : Module.finrank ℝ (LinearMap.range (sumMap x)) = m + 3 := by omega
  exact ⟨hker_eq, LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq (by rw [hrng_eq, hcod]))⟩

-- Shared one-step vectors u_{k, r} and kernel functionals μ_{k, r} for any n = m + 2 and apex a
private def uVec {m : ℕ} (x : Fin (m + 2) → Fin 3 → (Fin (m + 3) → ℝ))
    (a : Fin (m + 2) → Fin 3) (k : Fin (m + 2)) (r : Fin 2) : Fin (m + 3) → ℝ :=
  Fin.cases (x 0 (coneOther (a 0) r) - x 0 (a 0))
    (fun k' => x k'.succ (a k'.succ) - x k'.succ (coneOther (a k'.succ) r)) k

private def muCoord {m : ℕ} (a : Fin (m + 2) → Fin 3)
    (c : Fin (m + 2) → Fin 2 → ℝ) (k : Fin (m + 2)) (r : Fin 2) : ℝ :=
  Fin.cases (-coneCoord (a 0) (c 0) r) (fun k' => coneCoord (a k'.succ) (c k'.succ) r) k

private lemma muCoord_add {m : ℕ} (a : Fin (m + 2) → Fin 3)
    (c₁ c₂ : Fin (m + 2) → Fin 2 → ℝ) (k : Fin (m + 2)) (r : Fin 2) :
    muCoord a (c₁ + c₂) k r = muCoord a c₁ k r + muCoord a c₂ k r := by
  refine Fin.cases ?_ (fun k' => ?_) k
  · simp [muCoord, coneCoord_add]; ring
  · simp [muCoord, coneCoord_add]

private lemma muCoord_smul {m : ℕ} (a : Fin (m + 2) → Fin 3)
    (t : ℝ) (c : Fin (m + 2) → Fin 2 → ℝ) (k : Fin (m + 2)) (r : Fin 2) :
    muCoord a (t • c) k r = t * muCoord a c k r := by
  refine Fin.cases ?_ (fun k' => ?_) k
  · simp [muCoord, coneCoord_smul]
  · simp [muCoord, coneCoord_smul]

private lemma muCoord_cubic_zero {m : ℕ} (a : Fin (m + 2) → Fin 3)
    (c : Fin (m + 2) → Fin 2 → ℝ) :
    cubicF c 0 = -(muCoord a c 0 0 * muCoord a c 0 1 * (muCoord a c 0 0 + muCoord a c 0 1)) := by
  rw [cubicF, ← coneCoord_cubic (a 0) (c 0)]
  simp only [muCoord, Fin.cases_zero]
  ring

private lemma muCoord_cubic_succ {m : ℕ} (a : Fin (m + 2) → Fin 3)
    (c : Fin (m + 2) → Fin 2 → ℝ) (k : Fin (m + 1)) :
    cubicF c k.succ =
      muCoord a c k.succ 0 * muCoord a c k.succ 1 * (muCoord a c k.succ 0 + muCoord a c k.succ 1) := by
  rw [cubicF, ← coneCoord_cubic (a k.succ) (c k.succ)]
  simp [muCoord]

private lemma continuous_muCoord {m : ℕ} (a : Fin (m + 2) → Fin 3) (k : Fin (m + 2)) (r : Fin 2) :
    Continuous (fun c : Fin (m + 2) → Fin 2 → ℝ => muCoord a c k r) := by
  refine Fin.cases ?_ (fun k' => ?_) k
  · simp only [muCoord, Fin.cases_zero]
    generalize a 0 = ak
    fin_cases ak <;> fin_cases r <;> simp [coneCoord] <;> fun_prop
  · simp only [muCoord, Fin.cases_succ]
    generalize a k'.succ = ak
    fin_cases ak <;> fin_cases r <;> simp [coneCoord] <;> fun_prop

private lemma sum_muCoord_uVec {m : ℕ} (x : Fin (m + 2) → Fin 3 → (Fin (m + 3) → ℝ))
    (a : Fin (m + 2) → Fin 3) (c : Fin (m + 2) → Fin 2 → ℝ) :
    ∑ k : Fin (m + 2), ∑ r : Fin 2, muCoord a c k r • uVec x a k r = -sumMap x c := by
  rw [Fin.sum_univ_succ (f := fun k : Fin (m + 2) => ∑ r : Fin 2, muCoord a c k r • uVec x a k r)]
  unfold sumMap
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fin.sum_univ_succ (f := fun k : Fin (m + 2) => c k 0 • (x k 1 - x k 0) + c k 1 • (x k 2 - x k 0)),
    neg_add, ← Finset.sum_neg_distrib]
  congr 1
  · rw [Fin.sum_univ_two]
    simp only [muCoord, uVec, Fin.cases_zero, neg_smul, ← neg_add]
    rw [coneCoord_vec (x 0) (a 0) (c 0)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fin.sum_univ_two]
    simp only [muCoord, uVec, Fin.cases_succ]
    rw [← coneCoord_vec (x k.succ) (a k.succ) (c k.succ)]
    module

private lemma exists_uVec_repr {m : ℕ} {x : Fin (m + 2) → Fin 3 → (Fin (m + 3) → ℝ)}
    (hsurj : Function.Surjective (sumMap x)) (a : Fin (m + 2) → Fin 3) (w : Fin (m + 3) → ℝ) :
    ∃ coeff : Fin (m + 2) → Fin 2 → ℝ,
      ∑ k : Fin (m + 2), ∑ r : Fin 2, coeff k r • uVec x a k r = w := by
  obtain ⟨c, hc⟩ := hsurj (-w)
  refine ⟨muCoord a c, ?_⟩
  rw [sum_muCoord_uVec, hc, neg_neg]

private def MaSet {m : ℕ} (a : Fin (m + 2) → Fin 3) : Set (Fin (m + 2) → Fin 3) :=
  {i | i 0 ≠ a 0 ∧ ∀ k : Fin (m + 1), i k.succ = a k.succ}

private def MbSet {m : ℕ} (a : Fin (m + 2) → Fin 3) : Set (Fin (m + 2) → Fin 3) :=
  {i | i 0 = a 0 ∧ ∀ k : Fin (m + 1), i k.succ ≠ a k.succ}

private def wVec {m : ℕ} (y : Set (Fin (m + 2) → Fin 3) → (Fin (m + 3) → ℝ))
    (a : Fin (m + 2) → Fin 3) : Fin (m + 3) → ℝ :=
  y (MbSet a)ᶜ - y (MaSet a)ᶜ

private lemma wVec_ne_zero {m : ℕ} {C : Set (Fin (m + 3) → ℝ)}
    {x : Fin (m + 2) → Fin 3 → (Fin (m + 3) → ℝ)}
    {y : Set (Fin (m + 2) → Fin 3) → (Fin (m + 3) → ℝ)}
    (hS : ShattersN C x y) (a : Fin (m + 2) → Fin 3) : wVec y a ≠ 0 := by
  let q := Function.update a 0 (coneOther (a 0) 0)
  have hqb : q ∈ (MbSet a)ᶜ := by
    intro hmem
    have h0 : q 0 = a 0 := hmem.1
    simp only [q, Function.update_self] at h0
    exact coneOther_ne (a 0) 0 h0
  have hqa : q ∉ (MaSet a)ᶜ := by
    rw [Set.notMem_compl_iff]
    refine ⟨by simp [q, coneOther_ne], fun k => ?_⟩
    simp [q]
  exact y_sub_ne_zero hS hqb hqa

private lemma forward_avoidance {m : ℕ} {C : Set (Fin (m + 3) → ℝ)} (hC : Convex ℝ C)
    {x : Fin (m + 2) → Fin 3 → (Fin (m + 3) → ℝ)}
    {y : Set (Fin (m + 2) → Fin 3) → (Fin (m + 3) → ℝ)}
    (hS : ShattersN C x y) (a : Fin (m + 2) → Fin 3)
    (L : Fin (m + 2) → Fin 2 → ℝ) (hL_nn : ∀ k r, 0 ≤ L k r)
    (hL_eq : ∑ k : Fin (m + 2), ∑ r : Fin 2, L k r • uVec x a k r = wVec y a) :
    0 < L 0 0 ∧ 0 < L 0 1 := by
  have hstep : ∀ r₀ : Fin 2, L 0 r₀ ≠ 0 := by
    intro r₀ hzero
    let r₁ : Fin 2 := 1 - r₀
    have hr01 : r₀ ≠ r₁ := by fin_cases r₀ <;> decide
    let q := Function.update a 0 (coneOther (a 0) r₁)
    have hqb : q ∈ (MbSet a)ᶜ := by
      intro hmem; have h0 := hmem.1; simp only [q, Function.update_self] at h0
      exact coneOther_ne (a 0) r₁ h0
    have hqa : q ∉ (MaSet a)ᶜ := by
      rw [Set.notMem_compl_iff]
      exact ⟨by simp [q, coneOther_ne], fun k => by simp [q]⟩
    let pts : Option (Fin (m + 1) × Fin 2) → (Fin (m + 2) → Fin 3)
      | none => a
      | some (k, r) => Function.update q k.succ (coneOther (a k.succ) r)
    have hpts : ∀ p, pts p ∈ (MaSet a)ᶜ := by
      rintro (⟨⟩ | ⟨k, r⟩)
      · intro hmem; exact hmem.1 rfl
      · intro hmem
        have hk := hmem.2 k
        simp only [pts, Function.update_self] at hk
        exact coneOther_ne (a k.succ) r hk
    let α : Option (Fin (m + 1) × Fin 2) → ℝ
      | none => L 0 r₁
      | some (k, r) => L k.succ r
    have hα : ∀ p, 0 ≤ α p := by
      rintro (⟨⟩ | ⟨k, r⟩) <;> exact hL_nn _ _
    have hcomb : ∑ p, α p • (gridPt x q - gridPt x (pts p)) = wVec y a := by
      rw [Fintype.sum_option, Fintype.sum_prod_type]
      have hdiff0 : gridPt x q - gridPt x a = uVec x a 0 r₁ := by
        unfold gridPt q uVec
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single 0]
        · simp
        · intro k _ hk; simp [Function.update_of_ne hk]
        · intro h; exact absurd (Finset.mem_univ 0) h
      have hdiffk : ∀ (k : Fin (m + 1)) (r : Fin 2),
          gridPt x q - gridPt x (Function.update q k.succ (coneOther (a k.succ) r)) =
          uVec x a k.succ r := by
        intro k r
        unfold gridPt uVec
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single k.succ]
        · simp [q]
        · intro j _ hj; simp [Function.update_of_ne hj]
        · intro h; exact absurd (Finset.mem_univ k.succ) h
      simp only [α, pts, hdiff0, hdiffk]
      rw [← hL_eq, Fin.sum_univ_succ (f := fun k : Fin (m + 2) => ∑ r : Fin 2, L k r • uVec x a k r)]
      have h0sum : L 0 r₁ • uVec x a 0 r₁ = ∑ r : Fin 2, L 0 r • uVec x a 0 r := by
        have hr : r₀ = 0 ∨ r₀ = 1 := by fin_cases r₀ <;> simp
        rcases hr with rfl | rfl
        · simp [Fin.sum_univ_two, hzero, r₁]
        · simp [Fin.sum_univ_two, hzero, r₁]
      rw [h0sum]
    have hsum_pos : 0 < ∑ p, α p := by
      by_contra hle
      push Not at hle
      have hsum0 : ∑ p, α p = 0 := le_antisymm hle (Finset.sum_nonneg fun p _ => hα p)
      have hall0 : ∀ p, α p = 0 := fun p =>
        (Finset.sum_eq_zero_iff_of_nonneg fun p' _ => hα p').mp hsum0 p (Finset.mem_univ p)
      have hw0 : wVec y a = 0 := by rw [← hcomb]; simp [hall0]
      exact wVec_ne_zero hS a hw0
    exact forbidden_forward hC hS hqb hqa pts hpts α hα hsum_pos hcomb.symm
  exact ⟨lt_of_le_of_ne (hL_nn 0 0) (hstep 0).symm, lt_of_le_of_ne (hL_nn 0 1) (hstep 1).symm⟩

private lemma backward_avoidance {m : ℕ} {C : Set (Fin (m + 3) → ℝ)} (hC : Convex ℝ C)
    {x : Fin (m + 2) → Fin 3 → (Fin (m + 3) → ℝ)}
    {y : Set (Fin (m + 2) → Fin 3) → (Fin (m + 3) → ℝ)}
    (hS : ShattersN C x y) (a : Fin (m + 2) → Fin 3)
    (L : Fin (m + 2) → Fin 2 → ℝ) (hL_nn : ∀ k r, 0 ≤ L k r)
    (hL_eq : ∑ k : Fin (m + 2), ∑ r : Fin 2, L k r • uVec x a k r = wVec y a) :
    ∃ k : Fin (m + 1), 0 < L k.succ 0 ∧ 0 < L k.succ 1 := by
  by_contra hno
  push Not at hno
  have hzero_ex : ∀ k : Fin (m + 1), ∃ r : Fin 2, L k.succ (1 - r) = 0 := by
    intro k
    by_cases h0 : 0 < L k.succ 0
    · exact ⟨0, le_antisymm (hno k h0) (hL_nn k.succ 1)⟩
    · exact ⟨1, le_antisymm (not_lt.mp h0) (hL_nn k.succ 0)⟩
  let rkeep : Fin (m + 1) → Fin 2 := fun k => (hzero_ex k).choose
  have hrzero : ∀ k : Fin (m + 1), L k.succ (1 - rkeep k) = 0 := fun k => (hzero_ex k).choose_spec
  let p₀ : Fin (m + 2) → Fin 3 := Fin.cons (a 0) (fun k => coneOther (a k.succ) (rkeep k))
  have hpa : p₀ ∈ (MaSet a)ᶜ := by intro hmem; exact hmem.1 (by simp [p₀])
  have hpb : p₀ ∉ (MbSet a)ᶜ := by
    rw [Set.notMem_compl_iff]
    exact ⟨by simp [p₀], fun k => by simp [p₀, coneOther_ne]⟩
  let pts : Fin 2 ⊕ Fin (m + 1) → (Fin (m + 2) → Fin 3)
    | Sum.inl r => Function.update p₀ 0 (coneOther (a 0) r)
    | Sum.inr k => Function.update p₀ k.succ (a k.succ)
  have hpts : ∀ p, pts p ∈ (MbSet a)ᶜ := by
    rintro (r | k)
    · intro hmem; have h0 := hmem.1; simp only [pts, Function.update_self] at h0
      exact coneOther_ne (a 0) r h0
    · intro hmem; have hk := hmem.2 k; simp only [pts, Function.update_self] at hk; exact hk rfl
  let β : Fin 2 ⊕ Fin (m + 1) → ℝ
    | Sum.inl r => L 0 r
    | Sum.inr k => L k.succ (rkeep k)
  have hβ : ∀ p, 0 ≤ β p := by rintro (r | k) <;> exact hL_nn _ _
  have hcomb : ∑ p, β p • (gridPt x (pts p) - gridPt x p₀) = wVec y a := by
    rw [Fintype.sum_sum_type]
    have hdiff0 : ∀ r : Fin 2, gridPt x (Function.update p₀ 0 (coneOther (a 0) r)) - gridPt x p₀ =
        uVec x a 0 r := by
      intro r; unfold gridPt uVec
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single 0]
      · simp [p₀]
      · intro k _ hk; simp [Function.update_of_ne hk]
      · intro h; exact absurd (Finset.mem_univ 0) h
    have hdiffk : ∀ k : Fin (m + 1), gridPt x (Function.update p₀ k.succ (a k.succ)) - gridPt x p₀ =
        uVec x a k.succ (rkeep k) := by
      intro k; unfold gridPt uVec
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single k.succ]
      · simp [p₀]
      · intro j _ hj; simp [Function.update_of_ne hj]
      · intro h; exact absurd (Finset.mem_univ k.succ) h
    simp only [β, pts, hdiff0, hdiffk]
    rw [← hL_eq, Fin.sum_univ_succ (f := fun k : Fin (m + 2) => ∑ r : Fin 2, L k r • uVec x a k r)]
    apply congr_arg (fun v => (∑ r : Fin 2, L 0 r • uVec x a 0 r) + v)
    refine Finset.sum_congr rfl fun k _ => ?_
    have hz := hrzero k
    have hrk : rkeep k = 0 ∨ rkeep k = 1 := by
      generalize rkeep k = rv; fin_cases rv <;> simp
    have h10 : (1 : Fin 2) - 0 = 1 := rfl
    have h11 : (1 : Fin 2) - 1 = 0 := rfl
    rcases hrk with h0 | h1
    · rw [h0, h10] at hz; rw [h0]; simp [Fin.sum_univ_two, hz]
    · rw [h1, h11] at hz; rw [h1]; simp [Fin.sum_univ_two, hz]
  have hsum_pos : 0 < ∑ p, β p := by
    by_contra hle; push Not at hle
    have hsum0 : ∑ p, β p = 0 := le_antisymm hle (Finset.sum_nonneg fun p _ => hβ p)
    have hall0 : ∀ p, β p = 0 := fun p =>
      (Finset.sum_eq_zero_iff_of_nonneg fun p' _ => hβ p').mp hsum0 p (Finset.mem_univ p)
    have hw0 : wVec y a = 0 := by rw [← hcomb]; simp [hall0]
    exact wVec_ne_zero hS a hw0
  exact forbidden_backward hC hS hpa hpb pts hpts β hβ hsum_pos hcomb.symm

end ConvexCore


/- ## Section 3: Simultaneous Chamber Surgery for n >= 3 -/

section ChamberSurgery

private lemma continuous_finset_sup' {α ι : Type*} [TopologicalSpace α]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → α → ℝ) (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x => s.sup' hs (fun i => f i x)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
    simpa using hf i (Finset.mem_singleton_self i)
  | cons i t hi ht ih =>
    have hfun : (fun x => (t.cons i hi).sup' (Finset.cons_nonempty _) (fun j => f j x)) =
        fun x => f i x ⊔ t.sup' ht (fun j => f j x) := by
      funext x; exact Finset.sup'_cons ht (fun j => f j x)
    rw [hfun]
    exact (hf i (Finset.mem_cons_self i t)).sup
      (ih fun j hj => hf j (Finset.mem_cons.mpr (Or.inr hj)))

private lemma continuousOn_union_of_isClosed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    (hf1 : ContinuousOn f s) (hf2 : ContinuousOn f t) : ContinuousOn f (s ∪ t) := by
  intro x _
  rw [ContinuousWithinAt, nhdsWithin_union, Filter.tendsto_sup]
  refine ⟨?_, ?_⟩
  · by_cases hx : x ∈ s
    · exact hf1 x hx
    · have hbot : nhdsWithin x s = ⊥ :=
        Filter.empty_mem_iff_bot.mp
          (mem_nhdsWithin.mpr ⟨sᶜ, hs.isOpen_compl, hx, (Set.compl_inter_self s).subset⟩)
      rw [hbot]; exact Filter.tendsto_bot
  · by_cases hx : x ∈ t
    · exact hf2 x hx
    · have hbot : nhdsWithin x t = ⊥ :=
        Filter.empty_mem_iff_bot.mp
          (mem_nhdsWithin.mpr ⟨tᶜ, ht.isOpen_compl, hx, (Set.compl_inter_self t).subset⟩)
      rw [hbot]; exact Filter.tendsto_bot

private lemma continuousOn_biUnion_of_isClosed {X Y ι : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (S : Finset ι) (A : ι → Set X)
    (hclosed : ∀ i ∈ S, IsClosed (A i)) (hcont : ∀ i ∈ S, ContinuousOn f (A i)) :
    ContinuousOn f (⋃ i ∈ S, A i) := by
  classical
  induction S using Finset.induction with
  | empty => simp [continuousOn_empty]
  | insert i s _ ih =>
    have hunion : (⋃ j ∈ insert i s, A j) = A i ∪ ⋃ j ∈ s, A j := by ext x; simp
    rw [hunion]
    refine continuousOn_union_of_isClosed
      (hclosed i (Finset.mem_insert_self i s))
      (isClosed_biUnion_finset fun j hj => hclosed j (Finset.mem_insert_of_mem hj))
      (hcont i (Finset.mem_insert_self i s))
      (ih (fun j hj => hclosed j (Finset.mem_insert_of_mem hj))
          (fun j hj => hcont j (Finset.mem_insert_of_mem hj)))

private lemma abs_min_sub_min_le {a b c d ε : ℝ} (h1 : |a - c| ≤ ε) (h2 : |b - d| ≤ ε) :
    |min a b - min c d| ≤ ε := by
  rw [abs_le] at h1 h2 ⊢
  rcases h1 with ⟨h1l, h1r⟩
  rcases h2 with ⟨h2l, h2r⟩
  constructor
  · have : min c d ≤ min a b + ε := by
      rw [← min_add_add_right]
      exact le_min (by linarith [min_le_left c d]) (by linarith [min_le_right c d])
    linarith
  · have : min a b ≤ min c d + ε := by
      rw [← min_add_add_right]
      exact le_min (by linarith [min_le_left a b]) (by linarith [min_le_right a b])
    linarith

private def piE {m : ℕ} (v : Fin (m + 3) → ℝ) : Fin (m + 3) → ℝ :=
  fun k => v k - (∑ j, v j) / ((m + 3 : ℕ) : ℝ)

private lemma sum_piE {m : ℕ} (v : Fin (m + 3) → ℝ) : ∑ k, piE v k = 0 := by
  unfold piE
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hne : ((m + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private lemma piE_neg {m : ℕ} (v : Fin (m + 3) → ℝ) : piE (-v) = -piE v := by
  funext k; simp [piE, Finset.sum_neg_distrib]; ring

private lemma piE_smul {m : ℕ} (t : ℝ) (v : Fin (m + 3) → ℝ) : piE (t • v) = t • piE v := by
  funext k; simp only [piE, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]; ring

private lemma continuous_piE (m : ℕ) : Continuous (@piE m) := by
  unfold piE
  refine continuous_pi fun k => (continuous_apply k).sub ?_
  exact (continuous_finsetSum _ fun j _ => continuous_apply j).div_const _

private def qstar (m : ℕ) : Fin (m + 3) → ℝ :=
  Fin.cons (-1 : ℝ) (fun _ : Fin (m + 2) => (1 : ℝ) / ((m + 2 : ℕ) : ℝ))

private lemma sum_qstar (m : ℕ) : ∑ k, qstar m k = 0 := by
  unfold qstar
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hne : ((m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private lemma norm_qstar (m : ℕ) : ‖qstar m‖ = 1 := by
  rw [← mem_cubeBdry_iff_norm_eq_one]
  refine ⟨fun k => ?_, ⟨0, by simp [qstar]⟩⟩
  refine Fin.cases ?_ (fun k' => ?_) k
  · simp [qstar]
  · simp only [qstar, Fin.cons_succ]
    have hpos : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
    rw [abs_of_pos (div_pos one_pos hpos), div_le_one hpos]
    exact_mod_cast (show 1 ≤ m + 2 by omega)

private def bstar (m : ℕ) : Fin (m + 2) → ℝ :=
  fun _ => (1 : ℝ) / ((m + 2 : ℕ) : ℝ)

private lemma sum_bstar (m : ℕ) : ∑ k, bstar m k = 1 := by
  unfold bstar
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hne : ((m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

private def yraw {m : ℕ} (u : Fin (m + 2) → ℝ) : Fin (m + 3) → ℝ :=
  Fin.cons (-(1 : ℝ) / ((m + 3 : ℕ) : ℝ)) (fun k => u k - (1 : ℝ) / ((m + 3 : ℕ) : ℝ))

private lemma continuous_yraw (m : ℕ) : Continuous (@yraw m) := by
  refine continuous_pi fun j => ?_
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [yraw, Fin.cons_zero]; exact continuous_const
  · simp only [yraw, Fin.cons_succ]; exact (continuous_apply k).sub continuous_const

private lemma yraw_ne_zero {m : ℕ} (u : Fin (m + 2) → ℝ) : yraw u ≠ 0 := by
  intro hz
  have h0 := congr_fun hz 0
  simp only [yraw, Fin.cons_zero, Pi.zero_apply] at h0
  have hpos : (0 : ℝ) < ((m + 3 : ℕ) : ℝ) := by positivity
  have hneg : -(1 : ℝ) / ((m + 3 : ℕ) : ℝ) < 0 := by
    rw [neg_div]; exact neg_lt_zero.mpr (div_pos one_pos hpos)
  linarith

private lemma sum_yraw {m : ℕ} {u : Fin (m + 2) → ℝ} (hu : ∑ k, u k = 1) :
    ∑ j, yraw u j = 0 := by
  unfold yraw
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Finset.sum_sub_distrib, hu, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hne : ((m + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  have hcast : ((m + 3 : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hne ⊢
  field_simp
  ring

private def PsiInv {m : ℕ} (u : Fin (m + 2) → ℝ) : Fin (m + 3) → ℝ :=
  (‖yraw u‖)⁻¹ • yraw u

private lemma continuous_PsiInv (m : ℕ) : Continuous (@PsiInv m) := by
  unfold PsiInv
  exact ((continuous_norm.comp (continuous_yraw m)).inv₀ fun u =>
    norm_ne_zero_iff.mpr (yraw_ne_zero u)).smul (continuous_yraw m)

private lemma norm_PsiInv {m : ℕ} (u : Fin (m + 2) → ℝ) : ‖PsiInv u‖ = 1 := by
  unfold PsiInv
  have hpos : 0 < ‖yraw u‖ := norm_pos_iff.mpr (yraw_ne_zero u)
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']

private lemma sum_PsiInv {m : ℕ} {u : Fin (m + 2) → ℝ} (hu : ∑ k, u k = 1) :
    ∑ j, PsiInv u j = 0 := by
  unfold PsiInv
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, sum_yraw hu, mul_zero]

private lemma PsiInv_zero_neg {m : ℕ} (u : Fin (m + 2) → ℝ) : PsiInv u 0 < 0 := by
  unfold PsiInv
  simp only [Pi.smul_apply, smul_eq_mul, yraw, Fin.cons_zero]
  have h1 : 0 < (‖yraw u‖)⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (yraw_ne_zero u))
  have h2 : -(1 : ℝ) / ((m + 3 : ℕ) : ℝ) < 0 := by
    rw [neg_div]; exact neg_lt_zero.mpr (div_pos one_pos (by positivity))
  exact mul_neg_of_pos_of_neg h1 h2

private lemma PsiInv_ne_neg_qstar {m : ℕ} (u : Fin (m + 2) → ℝ) : PsiInv u ≠ -qstar m := by
  intro heq
  have h0 := congr_fun heq 0
  simp only [Pi.neg_apply, qstar, Fin.cons_zero, neg_neg] at h0
  linarith [PsiInv_zero_neg u]

private lemma PsiInv_ne_qstar {m : ℕ} {u : Fin (m + 2) → ℝ}
    (hu_ne : u ≠ bstar m) : PsiInv u ≠ qstar m := by
  intro heq
  apply hu_ne
  have h0 := congr_fun heq 0
  simp only [PsiInv, Pi.smul_apply, smul_eq_mul, qstar, Fin.cons_zero] at h0
  have hpos3 : (0 : ℝ) < ((m + 3 : ℕ) : ℝ) := by positivity
  have hpos2 : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  have hnorm_pos : 0 < ‖yraw u‖ := norm_pos_iff.mpr (yraw_ne_zero u)
  have hnorm_eq : ‖yraw u‖ = 1 / ((m + 3 : ℕ) : ℝ) := by
    have hmul := congr_arg (fun t => ‖yraw u‖ * t) h0
    rw [← mul_assoc, mul_inv_cancel₀ hnorm_pos.ne', one_mul] at hmul
    have hy0 : yraw u 0 = -1 / ((m + 3 : ℕ) : ℝ) := by simp [yraw]
    rw [hy0, neg_div] at hmul
    linarith
  funext k
  have hk := congr_fun heq k.succ
  simp only [PsiInv, Pi.smul_apply, smul_eq_mul, qstar, Fin.cons_succ] at hk
  have hmul := congr_arg (fun t => ‖yraw u‖ * t) hk
  rw [← mul_assoc, mul_inv_cancel₀ hnorm_pos.ne', one_mul, hnorm_eq] at hmul
  have hyk : yraw u k.succ = u k - 1 / ((m + 3 : ℕ) : ℝ) := by simp [yraw]
  rw [hyk] at hmul
  unfold bstar
  have hcast : ((m + 3 : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) + 1 := by push_cast; ring
  have hne2 : ((m + 2 : ℕ) : ℝ) ≠ 0 := hpos2.ne'
  have hne3 : ((m + 3 : ℕ) : ℝ) ≠ 0 := hpos3.ne'
  have h1 : u k = 1 / ((m + 3 : ℕ) : ℝ) + (1 / ((m + 3 : ℕ) : ℝ)) * (1 / ((m + 2 : ℕ) : ℝ)) := by
    linarith
  rw [h1]
  rw [hcast] at hne3 ⊢
  field_simp

private lemma PsiInv_H0_eq_Fbar {m : ℕ} {v : Fin (m + 3) → ℝ}
    (hv0 : v 0 < 0) (hvsucc : ∀ k : Fin (m + 2), 0 ≤ v k.succ) :
    let S := ∑ k : Fin (m + 2), (v k.succ - v 0)
    PsiInv (fun k => (v k.succ - v 0) / S) = (‖piE v‖)⁻¹ • piE v := by
  intro S
  have hSpos : 0 < S := by
    refine Finset.sum_pos (fun k _ => by linarith [hvsucc k]) ⟨0, Finset.mem_univ 0⟩
  let u : Fin (m + 2) → ℝ := fun k => (v k.succ - v 0) / S
  have hS_eq : S = (∑ j : Fin (m + 3), v j) - ((m + 3 : ℕ) : ℝ) * v 0 := by
    have hsum : ∑ j : Fin (m + 3), v j = v 0 + ∑ k : Fin (m + 2), v k.succ := Fin.sum_univ_succ v
    have hS' : S = (∑ k : Fin (m + 2), v k.succ) - ((m + 2 : ℕ) : ℝ) * v 0 := by
      simp only [S, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    have hcast : ((m + 3 : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hS', hsum, hcast]; ring
  have hpiE_eq : piE v = S • yraw u := by
    funext j
    have hne3 : ((m + 3 : ℕ) : ℝ) ≠ 0 := by positivity
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [piE, Pi.smul_apply, smul_eq_mul, yraw, Fin.cons_zero]
      rw [hS_eq]; field_simp; ring
    · simp only [piE, Pi.smul_apply, smul_eq_mul, yraw, Fin.cons_succ, u]
      have hSne : S ≠ 0 := hSpos.ne'
      rw [mul_sub, mul_div_cancel₀ _ hSne, hS_eq]
      field_simp; ring
  change (‖yraw u‖)⁻¹ • yraw u = (‖piE v‖)⁻¹ • piE v
  rw [hpiE_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hSpos, mul_inv, smul_smul]
  congr 1
  field_simp [hSpos.ne']

private lemma no_odd_map_avoiding_qstar (m : ℕ)
    (Ftilde : (Fin (m + 2) → ℝ) → (Fin (m + 3) → ℝ))
    (hcont : ContinuousOn Ftilde (cubeBdry (m + 1)))
    (hodd : ∀ z ∈ cubeBdry (m + 1), Ftilde (-z) = -Ftilde z)
    (hsum : ∀ z ∈ cubeBdry (m + 1), ∑ j, Ftilde z j = 0)
    (hnorm : ∀ z ∈ cubeBdry (m + 1), ‖Ftilde z‖ = 1)
    (havoid : ∀ z ∈ cubeBdry (m + 1), Ftilde z ≠ qstar m ∧ Ftilde z ≠ -qstar m) : False := by
  let g : (Fin (m + 2) → ℝ) → (Fin (m + 1) → ℝ) :=
    fun z j => Ftilde z j.castSucc.succ + Ftilde z 0 / ((m + 2 : ℕ) : ℝ)
  have hg_cont : ContinuousOn g (cubeBdry (m + 1)) := by
    refine continuousOn_pi.mpr fun j => ?_
    exact ((continuous_apply j.castSucc.succ).comp_continuousOn hcont).add
      (((continuous_apply (0 : Fin (m + 3))).comp_continuousOn hcont).div_const _)
  have hg_odd : ∀ z ∈ cubeBdry (m + 1), g (-z) = -g z := by
    intro z hz; funext j
    simp only [g, hodd z hz, Pi.neg_apply]; ring
  obtain ⟨z, hzB, hgz⟩ := borsuk_ulam (m + 1) g hg_cont hg_odd
  set c := -Ftilde z 0
  have hcast : ∀ j : Fin (m + 1), Ftilde z j.castSucc.succ = c / ((m + 2 : ℕ) : ℝ) := by
    intro j
    have hj := congr_fun hgz j
    simp only [g, Pi.zero_apply] at hj
    have h1 : Ftilde z j.castSucc.succ = -(Ftilde z 0 / ((m + 2 : ℕ) : ℝ)) := by linarith
    rw [h1, ← neg_div]
  have hlast : Ftilde z (Fin.last (m + 1)).succ = c / ((m + 2 : ℕ) : ℝ) := by
    have h0 := hsum z hzB
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at h0
    have hpart : ∑ j : Fin (m + 1), Ftilde z j.castSucc.succ =
        ((m + 1 : ℕ) : ℝ) * (c / ((m + 2 : ℕ) : ℝ)) := by
      rw [Finset.sum_congr rfl fun j _ => hcast j, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [hpart] at h0
    have hne2 : ((m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    have hc_eq : Ftilde z 0 = -c := by simp [c]
    rw [hc_eq] at h0
    have hnat : ((m + 2 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    have hlin : -c + ((m + 1 : ℕ) : ℝ) * (c / ((m + 2 : ℕ) : ℝ)) = -(c / ((m + 2 : ℕ) : ℝ)) := by
      rw [hnat] at hne2 ⊢; field_simp; ring
    linarith
  have hcol : Ftilde z = c • qstar m := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [qstar, c]
    · refine Fin.lastCases ?_ (fun j => ?_) k
      · simp only [Pi.smul_apply, smul_eq_mul, qstar, Fin.cons_succ, hlast]; ring
      · simp only [Pi.smul_apply, smul_eq_mul, qstar, Fin.cons_succ, hcast j]; ring
  have habs : |c| = 1 := by
    have h1 := hnorm z hzB
    rw [hcol, norm_smul, Real.norm_eq_abs, norm_qstar, mul_one] at h1
    exact h1
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with hc | hc
  · exact (havoid z hzB).1 (by rw [hc, one_smul] at hcol; exact hcol)
  · exact (havoid z hzB).2 (by rw [hc, neg_one_smul] at hcol; exact hcol)

private lemma chamber_surgery {m : ℕ}
    {C : Set (Fin (m + 4) → ℝ)} (hC : Convex ℝ C)
    {x : Fin (m + 3) → Fin 3 → (Fin (m + 4) → ℝ)}
    {y : Set (Fin (m + 3) → Fin 3) → (Fin (m + 4) → ℝ)}
    (hS : ShattersN C x y)
    (hsurj : Function.Surjective (sumMap x))
    (eW : (Fin (m + 2) → ℝ) ≃ₗ[ℝ] LinearMap.ker (sumMap x))
    (a : Fin (m + 3) → Fin 3)
    (hJa : ({z : Fin (m + 2) → ℝ | ∀ k r, 0 < muCoord a (eW z).1 k r}).Nonempty) :
    ∃ Fsur : (Fin (m + 2) → ℝ) → (Fin (m + 3) → ℝ),
      ContinuousOn Fsur ({z | ∀ k r, 0 ≤ muCoord a (eW z).1 k r} ∩ cubeBdry (m + 1)) ∧
      (∀ z ∈ ({z | ∀ k r, 0 ≤ muCoord a (eW z).1 k r} ∩ cubeBdry (m + 1)),
        ∑ j, Fsur z j = 0 ∧ ‖Fsur z‖ = 1 ∧ Fsur z ≠ qstar m ∧ Fsur z ≠ -qstar m) ∧
      (∀ z ∈ ({z | ∀ k r, 0 ≤ muCoord a (eW z).1 k r} ∩ cubeBdry (m + 1)),
        ¬ (∀ k r, 0 < muCoord a (eW z).1 k r) →
          Fsur z = (‖piE (cubicF (eW z).1)‖)⁻¹ • piE (cubicF (eW z).1)) := by
  let Z : (Fin (m + 2) → ℝ) →ₗ[ℝ] (Fin (m + 3) → Fin 2 → ℝ) :=
    (LinearMap.ker (sumMap x)).subtype.comp eW.toLinearMap
  have hZ_cont : Continuous Z := LinearMap.continuous_of_finiteDimensional Z
  have hZ_ker : ∀ z, sumMap x (Z z) = 0 := fun z => (eW z).2
  have hZ_inj : ∀ z, Z z = 0 → z = 0 := fun z hz =>
    eW.map_eq_zero_iff.mp (Subtype.ext hz)
  let μ : (Fin (m + 2) → ℝ) → Fin (m + 3) → Fin 2 → ℝ := fun z k r => muCoord a (Z z) k r
  have hμ_add : ∀ z₁ z₂ k r, μ (z₁ + z₂) k r = μ z₁ k r + μ z₂ k r := fun z₁ z₂ k r => by
    simp only [μ, map_add, muCoord_add]
  have hμ_smul : ∀ t z k r, μ (t • z) k r = t * μ z k r := fun t z k r => by
    simp only [μ, map_smul, muCoord_smul]
  have hμ_sub : ∀ z₁ z₂ k r, μ (z₁ - z₂) k r = μ z₁ k r - μ z₂ k r := fun z₁ z₂ k r => by
    have h1 : z₁ - z₂ = z₁ + (-1 : ℝ) • z₂ := by module
    rw [h1, hμ_add, hμ_smul]; ring
  have hμ_zero : ∀ k r, μ 0 k r = 0 := fun k r => by
    have := hμ_smul 0 0 k r; simpa using this
  have hμ_cont : ∀ k r, Continuous (fun z => μ z k r) := fun k r =>
    (continuous_muCoord a k r).comp hZ_cont
  let f : (Fin (m + 2) → ℝ) → Fin (m + 3) → ℝ := fun z => cubicF (Z z)
  have hf_cont : ∀ j, Continuous (fun z => f z j) := fun j => (continuous_cubicF j).comp hZ_cont
  have hf_smul : ∀ t z j, f (t • z) j = t ^ 3 * f z j := fun t z j => by
    simp only [f, map_smul, cubicF_smul]
  have hf0_eq : ∀ z, f z 0 = -(μ z 0 0 * μ z 0 1 * (μ z 0 0 + μ z 0 1)) :=
    fun z => muCoord_cubic_zero a (Z z)
  have hfsucc_eq : ∀ z (k : Fin (m + 2)),
      f z k.succ = μ z k.succ 0 * μ z k.succ 1 * (μ z k.succ 0 + μ z k.succ 1) :=
    fun z k => muCoord_cubic_succ a (Z z) k
  let Jbar : Set (Fin (m + 2) → ℝ) := {z | ∀ k r, 0 ≤ μ z k r}
  let Da : Set (Fin (m + 2) → ℝ) := Jbar ∩ cubeBdry (m + 1)
  have hJbar_props : ∀ z ∈ Jbar, z ≠ 0 →
      f z 0 < 0 ∧ (∀ k : Fin (m + 2), 0 ≤ f z k.succ) ∧
      0 < (∑ k : Fin (m + 2), f z k.succ) ∧ 0 < μ z 0 0 ∧ 0 < μ z 0 1 := by
    intro z hzJ hzne
    have hZne : Z z ≠ 0 := fun h => hzne (hZ_inj z h)
    have hf0_le : f z 0 ≤ 0 := by
      rw [hf0_eq]; have h0 := hzJ 0 0; have h1 := hzJ 0 1; nlinarith [mul_nonneg h0 h1]
    have hfsucc_nn : ∀ k : Fin (m + 2), 0 ≤ f z k.succ := fun k => by
      rw [hfsucc_eq]; have h0 := hzJ k.succ 0; have h1 := hzJ k.succ 1; positivity
    have hf0_lt : f z 0 < 0 := lt_of_le_of_ne hf0_le fun hf0 => by
      apply cubicF_not_nonneg hC hS (hZ_ker z) hZne
      intro j; refine Fin.cases (by change 0 ≤ f z 0; linarith) (fun k => hfsucc_nn k) j
    have hsum_pos : 0 < ∑ k : Fin (m + 2), f z k.succ := by
      by_contra hle; push Not at hle
      have hsum0 : ∑ k : Fin (m + 2), f z k.succ = 0 :=
        le_antisymm hle (Finset.sum_nonneg fun k _ => hfsucc_nn k)
      have hall0 : ∀ k : Fin (m + 2), f z k.succ = 0 := fun k =>
        (Finset.sum_eq_zero_iff_of_nonneg fun k' _ => hfsucc_nn k').mp hsum0 k (Finset.mem_univ k)
      apply cubicF_not_nonpos hC hS (hZ_ker z) hZne
      intro j; refine Fin.cases hf0_le (fun k => by change f z k.succ ≤ 0; rw [hall0 k]) j
    have hμ00 : 0 < μ z 0 0 := lt_of_le_of_ne (hzJ 0 0) fun h0 => by
      rw [hf0_eq, ← h0] at hf0_lt; simp at hf0_lt
    have hμ01 : 0 < μ z 0 1 := lt_of_le_of_ne (hzJ 0 1) fun h0 => by
      rw [hf0_eq, ← h0] at hf0_lt; simp at hf0_lt
    exact ⟨hf0_lt, hfsucc_nn, hsum_pos, hμ00, hμ01⟩
  -- Normalize interior point z₀ ∈ J a with μ z₀ 0 0 = 1 (opaque to prevent smul unfolding)
  obtain ⟨z₀, hz₀_pos, hz₀_00⟩ : ∃ z₀ : Fin (m + 2) → ℝ, (∀ k r, 0 < μ z₀ k r) ∧ μ z₀ 0 0 = 1 := by
    obtain ⟨z₀', hz₀'⟩ := hJa
    have hμz₀'_pos : ∀ k r, 0 < μ z₀' k r := hz₀'
    refine ⟨(μ z₀' 0 0)⁻¹ • z₀', fun k r => ?_, ?_⟩
    · rw [hμ_smul]; exact mul_pos (inv_pos.mpr (hμz₀'_pos 0 0)) (hμz₀'_pos k r)
    · rw [hμ_smul, inv_mul_cancel₀ (hμz₀'_pos 0 0).ne']
  -- Hyperplane H0 = {v | μ v 0 0 = 0} and Minkowski gauge M
  let H0 : Set (Fin (m + 2) → ℝ) := {v | μ v 0 0 = 0}
  have hH0_closed : IsClosed H0 := isClosed_eq (hμ_cont 0 0) continuous_const
  let SH0 : Set (Fin (m + 2) → ℝ) := H0 ∩ cubeBdry (m + 1)
  have hSH0_comp : IsCompact SH0 := (cubeBdry_isCompact (m + 1)).inter_left hH0_closed
  have hSH0_ne : SH0.Nonempty := by
    let e0 : Fin (m + 2) → ℝ := Pi.single 0 1
    let e1 : Fin (m + 2) → ℝ := Pi.single 1 1
    have hv_ex : ∃ v : Fin (m + 2) → ℝ, v ∈ H0 ∧ v ≠ 0 := by
      by_cases h0 : μ e0 0 0 = 0
      · refine ⟨e0, h0, fun hz => ?_⟩
        have := congr_fun hz 0; simp [e0] at this
      · refine ⟨μ e1 0 0 • e0 - μ e0 0 0 • e1, ?_, fun hz => ?_⟩
        · show μ (μ e1 0 0 • e0 - μ e0 0 0 • e1) 0 0 = 0
          rw [hμ_sub, hμ_smul, hμ_smul]; ring
        · have h1 := congr_fun hz 1
          have h01 : (1 : Fin (m + 2)) ≠ 0 := fun h => by
            have := congr_arg Fin.val h; simp at this
          simp [e0, e1, h01] at h1
          exact h0 h1
    obtain ⟨v, hvH, hvne⟩ := hv_ex
    refine ⟨(‖v‖)⁻¹ • v, ?_, ?_⟩
    · change μ ((‖v‖)⁻¹ • v) 0 0 = 0
      rw [hμ_smul, hvH, mul_zero]
    · rw [mem_cubeBdry_iff_norm_eq_one, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos (norm_pos_iff.mpr hvne), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvne)]
  have hne_kr : (Finset.univ : Finset (Fin (m + 2) × Fin 2)).Nonempty := ⟨(0, 0), Finset.mem_univ _⟩
  have hne_all : (Finset.univ : Finset (Fin (m + 3) × Fin 2)).Nonempty := ⟨(0, 0), Finset.mem_univ _⟩
  let M : (Fin (m + 2) → ℝ) → ℝ := fun v =>
    Finset.univ.sup' hne_kr (fun p : Fin (m + 2) × Fin 2 => -μ v p.1.succ p.2 / μ z₀ p.1.succ p.2)
  have hM_cont : Continuous M :=
    continuous_finset_sup' Finset.univ hne_kr _ fun p _ => ((hμ_cont p.1.succ p.2).neg).div_const _
  have hM_zero : M 0 = 0 := by
    unfold M
    apply le_antisymm
    · refine Finset.sup'_le hne_kr _ fun p _ => ?_; simp [hμ_zero]
    · refine le_trans ?_ (Finset.le_sup' (fun p : Fin (m + 2) × Fin 2 =>
        -μ 0 p.1.succ p.2 / μ z₀ p.1.succ p.2) (Finset.mem_univ (0, 0)))
      simp [hμ_zero]
  have hM_le_iff : ∀ v s, M v ≤ s ↔ ∀ (k : Fin (m + 2)) (r : Fin 2), 0 ≤ μ (v + s • z₀) k.succ r := by
    intro v s
    simp only [M, Finset.sup'_le_iff, Finset.mem_univ, true_implies, Prod.forall]
    refine forall₂_congr fun k r => ?_
    rw [div_le_iff₀ (hz₀_pos k.succ r), hμ_add, hμ_smul]
    constructor <;> intro h <;> linarith
  have hM_lt_iff : ∀ v s, M v < s ↔ ∀ (k : Fin (m + 2)) (r : Fin 2), 0 < μ (v + s • z₀) k.succ r := by
    intro v s
    simp only [M, Finset.sup'_lt_iff, Finset.mem_univ, true_implies, Prod.forall]
    refine forall₂_congr fun k r => ?_
    rw [div_lt_iff₀ (hz₀_pos k.succ r), hμ_add, hμ_smul]
    constructor <;> intro h <;> linarith
  have hM_pos : ∀ v ∈ H0, v ≠ 0 → 0 < M v := by
    intro v hvH hvne
    by_contra hle; push Not at hle
    have hnn := (hM_le_iff v 0).mp hle
    have hZne : Z v ≠ 0 := fun h => hvne (hZ_inj v h)
    apply cubicF_not_nonneg hC hS (hZ_ker v) hZne
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · change 0 ≤ f v 0; rw [hf0_eq, hvH]; simp
    · change 0 ≤ f v k.succ; rw [hfsucc_eq]
      have h0 : 0 ≤ μ v k.succ 0 := by simpa using hnn k 0
      have h1 : 0 ≤ μ v k.succ 1 := by simpa using hnn k 1
      positivity
  have hM_nonneg : ∀ v ∈ H0, 0 ≤ M v := by
    intro v hvH
    by_cases hv : v = 0
    · rw [hv, hM_zero]
    · exact (hM_pos v hvH hv).le
  have hM_smul : ∀ {t : ℝ}, 0 ≤ t → ∀ v, M (t • v) = t * M v := by
    intro t ht v
    rcases eq_or_lt_of_le ht with rfl | htpos
    · simp [hM_zero]
    · apply le_antisymm
      · unfold M
        refine Finset.sup'_le hne_kr _ fun p _ => ?_
        have hle := Finset.le_sup' (fun q : Fin (m + 2) × Fin 2 =>
          -μ v q.1.succ q.2 / μ z₀ q.1.succ q.2) (Finset.mem_univ p)
        have hmul := mul_le_mul_of_nonneg_left hle htpos.le
        have hrew : -μ (t • v) p.1.succ p.2 / μ z₀ p.1.succ p.2 =
            t * (-μ v p.1.succ p.2 / μ z₀ p.1.succ p.2) := by rw [hμ_smul]; ring
        rw [hrew]; exact hmul
      · rw [← le_div_iff₀' htpos]
        unfold M
        refine Finset.sup'_le hne_kr _ fun p _ => ?_
        have hle := Finset.le_sup' (fun q : Fin (m + 2) × Fin 2 =>
          -μ (t • v) q.1.succ q.2 / μ z₀ q.1.succ q.2) (Finset.mem_univ p)
        rw [le_div_iff₀' htpos]
        have hrew : -μ (t • v) p.1.succ p.2 / μ z₀ p.1.succ p.2 =
            t * (-μ v p.1.succ p.2 / μ z₀ p.1.succ p.2) := by rw [hμ_smul]; ring
        rw [← hrew]; exact hle
  have hM_le_one_Jbar : ∀ v ∈ H0, M v ≤ 1 → z₀ + v ∈ Jbar ∧ z₀ + v ≠ 0 := by
    intro v hvH hMle
    have h00 : μ (z₀ + v) 0 0 = 1 := by rw [hμ_add, hz₀_00, hvH, add_zero]
    have hne : z₀ + v ≠ 0 := fun h => by rw [h, hμ_zero] at h00; norm_num at h00
    have hsucc : ∀ (k : Fin (m + 2)) (r : Fin 2), 0 ≤ μ (z₀ + v) k.succ r := by
      intro k r
      have h := (hM_le_iff v 1).mp hMle k r
      simpa [add_comm] using h
    have h01 : 0 < μ (z₀ + v) 0 1 := by
      by_contra hle; push Not at hle
      set a1 := μ z₀ 0 1
      set b1 := μ (z₀ + v) 0 1
      have ha1 : 0 < a1 := hz₀_pos 0 1
      have hdiff : 0 < a1 - b1 := by linarith
      set t := a1 / (a1 - b1)
      have ht_pos : 0 < t := div_pos ha1 hdiff
      have ht_le : t ≤ 1 := (div_le_one hdiff).mpr (by linarith)
      let w := z₀ + t • v
      have hw00 : μ w 0 0 = 1 := by rw [hμ_add, hz₀_00, hμ_smul, hvH]; ring
      have hwne : w ≠ 0 := fun h => by rw [h, hμ_zero] at hw00; norm_num at hw00
      have hw01 : μ w 0 1 = 0 := by
        have hlin : μ w 0 1 = (1 - t) * a1 + t * b1 := by
          have hb1_eq : b1 = a1 + μ v 0 1 := hμ_add z₀ v 0 1
          rw [hμ_add, hμ_smul]
          change a1 + t * μ v 0 1 = (1 - t) * a1 + t * b1
          rw [hb1_eq]; ring
        rw [hlin]
        have : t * (a1 - b1) = a1 := div_mul_cancel₀ a1 hdiff.ne'
        linarith
      have hZne : Z w ≠ 0 := fun h => hwne (hZ_inj w h)
      apply cubicF_not_nonneg hC hS (hZ_ker w) hZne
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · change 0 ≤ f w 0; rw [hf0_eq, hw01]; simp
      · change 0 ≤ f w k.succ; rw [hfsucc_eq]
        have hkr : ∀ r : Fin 2, 0 ≤ μ w k.succ r := fun r => by
          have heq : μ w k.succ r = (1 - t) * μ z₀ k.succ r + t * μ (z₀ + v) k.succ r := by
            rw [hμ_add, hμ_smul, hμ_add]; ring
          rw [heq]
          have h1 : 0 ≤ (1 - t) * μ z₀ k.succ r := mul_nonneg (by linarith) (hz₀_pos k.succ r).le
          have h2 : 0 ≤ t * μ (z₀ + v) k.succ r := mul_nonneg ht_pos.le (hsucc k r)
          linarith
        have h0 := hkr 0; have h1 := hkr 1; positivity
    refine ⟨fun j r => ?_, hne⟩
    refine Fin.cases ?_ (fun k => hsucc k r) j
    have hr : r = 0 ∨ r = 1 := by fin_cases r <;> simp
    rcases hr with rfl | rfl
    · linarith
    · exact h01.le
  -- Ray uRay v = v + M v • z₀ on H0 \ {0}
  let uRay : (Fin (m + 2) → ℝ) → (Fin (m + 2) → ℝ) := fun v => v + M v • z₀
  have huRay_cont : Continuous uRay := continuous_id.add (hM_cont.smul continuous_const)
  have huRay_smul : ∀ {t : ℝ}, 0 ≤ t → ∀ v, uRay (t • v) = t • uRay v := by
    intro t ht v
    simp only [uRay, hM_smul ht, smul_add, smul_smul]
  have huRay_Jbar : ∀ v ∈ H0, v ≠ 0 → uRay v ∈ Jbar ∧ uRay v ≠ 0 ∧
      ∃ (k : Fin (m + 2)) (r : Fin 2), μ (uRay v) k.succ r = 0 := by
    intro v hvH hvne
    have hMv : 0 < M v := hM_pos v hvH hvne
    have hv'H : (M v)⁻¹ • v ∈ H0 := by change μ ((M v)⁻¹ • v) 0 0 = 0; rw [hμ_smul, hvH, mul_zero]
    have hMv' : M ((M v)⁻¹ • v) = 1 := by
      rw [hM_smul (inv_pos.mpr hMv).le, inv_mul_cancel₀ hMv.ne']
    obtain ⟨hJ', hne'⟩ := hM_le_one_Jbar _ hv'H hMv'.le
    have hu_eq : uRay v = M v • (z₀ + (M v)⁻¹ • v) := by
      simp only [uRay, smul_add, smul_smul, mul_inv_cancel₀ hMv.ne', one_smul]; abel
    have hJ : uRay v ∈ Jbar := fun k r => by
      rw [hu_eq, hμ_smul]; exact mul_nonneg hMv.le (hJ' k r)
    have hne : uRay v ≠ 0 := by
      rw [hu_eq]; exact smul_ne_zero hMv.ne' hne'
    obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' hne_kr
      (fun p : Fin (m + 2) × Fin 2 => -μ v p.1.succ p.2 / μ z₀ p.1.succ p.2)
    have hzero : μ (uRay v) p.1.succ p.2 = 0 := by
      simp only [uRay, hμ_add, hμ_smul]
      have hMp : M v = -μ v p.1.succ p.2 / μ z₀ p.1.succ p.2 := hp
      rw [hMp, div_mul_cancel₀ _ (hz₀_pos p.1.succ p.2).ne']; ring
    exact ⟨hJ, hne, p.1, p.2, hzero⟩
  -- Build PhiR globally on Fin (m + 2) → ℝ from (cval, tFun, psi, Lval, gFun)
  obtain ⟨cval, hcval⟩ := exists_uVec_repr hsurj a (wVec y a)
  let Lval : (Fin (m + 2) → ℝ) → Fin (m + 3) → Fin 2 → ℝ := fun z k r => cval k r + μ z k r
  have hLval_eq : ∀ z, ∑ k : Fin (m + 3), ∑ r : Fin 2, Lval z k r • uVec x a k r = wVec y a := by
    intro z
    calc ∑ k : Fin (m + 3), ∑ r : Fin 2, (cval k r + μ z k r) • uVec x a k r
        = (∑ k : Fin (m + 3), ∑ r : Fin 2, cval k r • uVec x a k r) +
          (∑ k : Fin (m + 3), ∑ r : Fin 2, μ z k r • uVec x a k r) := by
          simp only [add_smul, Finset.sum_add_distrib]
      _ = wVec y a + (-sumMap x (Z z)) := by rw [hcval, sum_muCoord_uVec]
      _ = wVec y a := by rw [hZ_ker z, neg_zero, add_zero]
  let tFun : (Fin (m + 2) → ℝ) → ℝ := fun v =>
    Finset.univ.sup' hne_all (fun p : Fin (m + 3) × Fin 2 =>
      (-cval p.1 p.2 - μ v p.1 p.2) / μ z₀ p.1 p.2)
  have htFun_cont : Continuous tFun :=
    continuous_finset_sup' Finset.univ hne_all _ fun p _ =>
      (continuous_const.sub (hμ_cont p.1 p.2)).div_const _
  let psi : (Fin (m + 2) → ℝ) → (Fin (m + 2) → ℝ) := fun v => v + tFun v • z₀
  have hpsi_cont : Continuous psi := continuous_id.add (htFun_cont.smul continuous_const)
  let gFun : (Fin (m + 2) → ℝ) → Fin (m + 2) → ℝ :=
    fun v k => min (Lval (psi v) k.succ 0) (Lval (psi v) k.succ 1)
  have hgFun_cont : ∀ k, Continuous (fun v => gFun v k) := fun k =>
    (continuous_const.add ((hμ_cont k.succ 0).comp hpsi_cont)).min
      (continuous_const.add ((hμ_cont k.succ 1).comp hpsi_cont))
  have hgFun_props : ∀ v, (∀ k, 0 ≤ gFun v k) ∧ (∃ k, gFun v k = 0) ∧
      0 < ∑ k : Fin (m + 2), gFun v k := by
    intro v
    have hLnn : ∀ k r, 0 ≤ Lval (psi v) k r := fun k r => by
      have hle := Finset.le_sup' (fun p : Fin (m + 3) × Fin 2 =>
        (-cval p.1 p.2 - μ v p.1 p.2) / μ z₀ p.1 p.2) (Finset.mem_univ (k, r))
      have hmul := (div_le_iff₀ (hz₀_pos k r)).mp hle
      simp only [Lval, psi, hμ_add, hμ_smul]; linarith
    have hfwd := forward_avoidance hC hS a (Lval (psi v)) hLnn (hLval_eq (psi v))
    have hbwd := backward_avoidance hC hS a (Lval (psi v)) hLnn (hLval_eq (psi v))
    obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' hne_all
      (fun p : Fin (m + 3) × Fin 2 => (-cval p.1 p.2 - μ v p.1 p.2) / μ z₀ p.1 p.2)
    have hpzero : Lval (psi v) p.1 p.2 = 0 := by
      simp only [Lval, psi, hμ_add, hμ_smul]
      have ht : tFun v = (-cval p.1 p.2 - μ v p.1 p.2) / μ z₀ p.1 p.2 := hp
      rw [ht, div_mul_cancel₀ _ (hz₀_pos p.1 p.2).ne']; ring
    have hg_nn : ∀ k, 0 ≤ gFun v k := fun k => le_min (hLnn k.succ 0) (hLnn k.succ 1)
    have hg_zero : ∃ k : Fin (m + 2), gFun v k = 0 := by
      rcases p with ⟨pj, pr⟩
      dsimp only at hpzero
      revert hpzero
      refine Fin.cases ?_ (fun k hpzero => ⟨k, ?_⟩) pj
      · intro hpzero; exfalso
        have hr : pr = 0 ∨ pr = 1 := by fin_cases pr <;> simp
        rcases hr with rfl | rfl
        · linarith [hfwd.1]
        · linarith [hfwd.2]
      · refine le_antisymm ?_ (hg_nn k)
        have hr : pr = 0 ∨ pr = 1 := by fin_cases pr <;> simp
        rcases hr with rfl | rfl
        · exact (min_le_left _ _).trans hpzero.le
        · exact (min_le_right _ _).trans hpzero.le
    obtain ⟨kpos, hkpos0, hkpos1⟩ := hbwd
    have hsum_pos : 0 < ∑ k : Fin (m + 2), gFun v k :=
      lt_of_lt_of_le (lt_min hkpos0 hkpos1)
        (Finset.single_le_sum (fun k _ => hg_nn k) (Finset.mem_univ kpos))
    exact ⟨hg_nn, hg_zero, hsum_pos⟩
  let PhiR : (Fin (m + 2) → ℝ) → Fin (m + 2) → ℝ :=
    fun v k => gFun v k / ∑ j : Fin (m + 2), gFun v j
  have hPhiR_cont : Continuous PhiR :=
    continuous_pi fun k =>
      (hgFun_cont k).div (continuous_finsetSum _ fun j _ => hgFun_cont j)
        fun v => (hgFun_props v).2.2.ne'
  have hPhiR_props : ∀ v, (∀ k, 0 ≤ PhiR v k) ∧ (∑ k, PhiR v k = 1) ∧ PhiR v ≠ bstar m := by
    intro v
    obtain ⟨hnn, ⟨kz, hkz⟩, hpos⟩ := hgFun_props v
    refine ⟨fun k => div_nonneg (hnn k) hpos.le, ?_, fun heq => ?_⟩
    · simp only [PhiR, ← Finset.sum_div, div_self hpos.ne']
    · have hk := congr_fun heq kz
      simp only [PhiR, hkz, zero_div, bstar] at hk
      have : (0 : ℝ) < 1 / ((m + 2 : ℕ) : ℝ) := by positivity
      linarith
  -- Build mFun and PhiInf on H0 \ {0}
  let mFun : (Fin (m + 2) → ℝ) → Fin (m + 2) → ℝ :=
    fun v k => min (μ (uRay v) k.succ 0) (μ (uRay v) k.succ 1)
  have hmFun_cont : ∀ k, Continuous (fun v => mFun v k) := fun k =>
    ((hμ_cont k.succ 0).comp huRay_cont).min ((hμ_cont k.succ 1).comp huRay_cont)
  have hmFun_props : ∀ v ∈ H0, v ≠ 0 →
      (∀ k, 0 ≤ mFun v k) ∧ (∀ k, mFun v k = 0 ↔ f (uRay v) k.succ = 0) ∧
      (∃ k, mFun v k = 0) ∧ 0 < ∑ k : Fin (m + 2), mFun v k := by
    intro v hvH hvne
    obtain ⟨hJ, hne, kz, rz, hkz⟩ := huRay_Jbar v hvH hvne
    obtain ⟨_, _, hfsum_pos, _, _⟩ := hJbar_props (uRay v) hJ hne
    have hnn : ∀ k, 0 ≤ mFun v k := fun k => le_min (hJ k.succ 0) (hJ k.succ 1)
    have hiff : ∀ k, mFun v k = 0 ↔ f (uRay v) k.succ = 0 := by
      intro k
      have h0 := hJ k.succ 0; have h1 := hJ k.succ 1
      rw [hfsucc_eq]
      constructor
      · intro hm0
        unfold mFun at hm0
        rcases min_choice (μ (uRay v) k.succ 0) (μ (uRay v) k.succ 1) with h | h
        · rw [h] at hm0; simp [hm0]
        · rw [h] at hm0; simp [hm0]
      · intro hf0
        rcases mul_eq_zero.mp hf0 with hmul | hadd
        · rcases mul_eq_zero.mp hmul with ha | hb
          · exact le_antisymm ((min_le_left _ _).trans ha.le) (hnn k)
          · exact le_antisymm ((min_le_right _ _).trans hb.le) (hnn k)
        · have ha : μ (uRay v) k.succ 0 = 0 := by linarith
          exact le_antisymm ((min_le_left _ _).trans ha.le) (hnn k)
    have hex0 : ∃ k, mFun v k = 0 := by
      refine ⟨kz, le_antisymm ?_ (hnn kz)⟩
      have hr : rz = 0 ∨ rz = 1 := by fin_cases rz <;> simp
      rcases hr with rfl | rfl
      · exact (min_le_left _ _).trans hkz.le
      · exact (min_le_right _ _).trans hkz.le
    have hpos : 0 < ∑ k : Fin (m + 2), mFun v k := by
      by_contra hle; push Not at hle
      have hsum0 : ∑ k : Fin (m + 2), mFun v k = 0 :=
        le_antisymm hle (Finset.sum_nonneg fun k _ => hnn k)
      have hall0 : ∀ k : Fin (m + 2), f (uRay v) k.succ = 0 := fun k =>
        (hiff k).mp ((Finset.sum_eq_zero_iff_of_nonneg fun k' _ => hnn k').mp hsum0 k (Finset.mem_univ k))
      have : ∑ k : Fin (m + 2), f (uRay v) k.succ = 0 := Finset.sum_eq_zero fun k _ => hall0 k
      linarith
    exact ⟨hnn, hiff, hex0, hpos⟩
  let PhiInf : (Fin (m + 2) → ℝ) → Fin (m + 2) → ℝ :=
    fun v k => mFun v k / ∑ j : Fin (m + 2), mFun v j
  have hPhiInf_smul : ∀ {t : ℝ}, 0 < t → ∀ v, PhiInf (t • v) = PhiInf v := by
    intro t ht v
    have hm_smul : ∀ k, mFun (t • v) k = t * mFun v k := fun k => by
      simp only [mFun, huRay_smul ht.le, hμ_smul, mul_min_of_nonneg _ _ ht.le]
    funext k
    simp only [PhiInf, hm_smul, ← Finset.mul_sum, mul_div_mul_left _ _ ht.ne']
  -- Compact infimum δ > 0 of ∑ mFun on SH0 and explicit R > 0
  obtain ⟨vδ, hvδS, hvδmin⟩ := hSH0_comp.exists_isMinOn hSH0_ne
    (continuous_finsetSum _ fun j _ => hmFun_cont j).continuousOn
  have hvδ_ne : vδ ≠ 0 := fun hz => by
    have := (mem_cubeBdry_iff_norm_eq_one vδ).mp hvδS.2; rw [hz, norm_zero] at this; norm_num at this
  set δ := ∑ j : Fin (m + 2), mFun vδ j
  have hδpos : 0 < δ := (hmFun_props vδ hvδS.1 hvδ_ne).2.2.2
  have hδle : ∀ v ∈ SH0, δ ≤ ∑ j : Fin (m + 2), mFun v j := fun v hv => hvδmin hv
  let M0 : ℝ := Finset.univ.sup' hne_all (fun p : Fin (m + 3) × Fin 2 => |cval p.1 p.2| / μ z₀ p.1 p.2)
  have hM0_nn : 0 ≤ M0 :=
    le_trans (div_nonneg (abs_nonneg _) (hz₀_pos 0 0).le)
      (Finset.le_sup' (fun p : Fin (m + 3) × Fin 2 => |cval p.1 p.2| / μ z₀ p.1 p.2) (Finset.mem_univ (0, 0)))
  let Cmax : ℝ := Finset.univ.sup' hne_kr (fun p : Fin (m + 2) × Fin 2 => |cval p.1.succ p.2|)
  have hCmax_nn : 0 ≤ Cmax :=
    le_trans (abs_nonneg _)
      (Finset.le_sup' (fun p : Fin (m + 2) × Fin 2 => |cval p.1.succ p.2|) (Finset.mem_univ (0, 0)))
  let Zmax : ℝ := Finset.univ.sup' hne_kr (fun p : Fin (m + 2) × Fin 2 => μ z₀ p.1.succ p.2)
  have hZmax_nn : 0 ≤ Zmax :=
    le_trans (hz₀_pos (0 : Fin (m + 2)).succ 0).le
      (Finset.le_sup' (fun p : Fin (m + 2) × Fin 2 => μ z₀ p.1.succ p.2) (Finset.mem_univ (0, 0)))
  let K : ℝ := Cmax + M0 * Zmax
  have hK_nn : 0 ≤ K := by positivity
  let R : ℝ := ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) * K / δ + 1
  have hR_pos : 0 < R := by positivity
  have hPhiR_close : ∀ v ∈ SH0, ∀ k : Fin (m + 2),
      |PhiR (R • v) k - PhiInf v k| < 1 / ((m + 2 : ℕ) : ℝ) := by
    intro v hvS k
    have hvne : v ≠ 0 := fun hz => by
      have := (mem_cubeBdry_iff_norm_eq_one v).mp hvS.2; rw [hz, norm_zero] at this; norm_num at this
    obtain ⟨huJ, hune, _⟩ := huRay_Jbar v hvS.1 hvne
    obtain ⟨_, _, _, hu00, hu01⟩ := hJbar_props (uRay v) huJ hune
    have ht_diff : |tFun (R • v) / R - M v| ≤ M0 / R := by
      rw [abs_le]
      constructor
      · obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' hne_kr
          (fun p : Fin (m + 2) × Fin 2 => -μ v p.1.succ p.2 / μ z₀ p.1.succ p.2)
        have hle := Finset.le_sup' (fun q : Fin (m + 3) × Fin 2 =>
          (-cval q.1 q.2 - μ (R • v) q.1 q.2) / μ z₀ q.1 q.2) (Finset.mem_univ (p.1.succ, p.2))
        have hdiv : (-cval p.1.succ p.2 - μ (R • v) p.1.succ p.2) / μ z₀ p.1.succ p.2 / R ≤
            tFun (R • v) / R := div_le_div_of_nonneg_right hle hR_pos.le
        have hMp : M v = -μ v p.1.succ p.2 / μ z₀ p.1.succ p.2 := hp
        have hrew : (-cval p.1.succ p.2 - μ (R • v) p.1.succ p.2) / μ z₀ p.1.succ p.2 / R =
            (-cval p.1.succ p.2 / μ z₀ p.1.succ p.2) / R + M v := by
          rw [hMp, hμ_smul]
          have hRne := hR_pos.ne'; have hz := (hz₀_pos p.1.succ p.2).ne'
          field_simp; ring
        have hc_le : -(M0 / R) ≤ (-cval p.1.succ p.2 / μ z₀ p.1.succ p.2) / R := by
          have h1 : |cval p.1.succ p.2| / μ z₀ p.1.succ p.2 ≤ M0 :=
            Finset.le_sup' (fun q : Fin (m + 3) × Fin 2 => |cval q.1 q.2| / μ z₀ q.1 q.2)
              (Finset.mem_univ (p.1.succ, p.2))
          have h2 : -cval p.1.succ p.2 ≥ -|cval p.1.succ p.2| := by linarith [le_abs_self (cval p.1.succ p.2)]
          have h3 : -|cval p.1.succ p.2| / μ z₀ p.1.succ p.2 ≤ -cval p.1.succ p.2 / μ z₀ p.1.succ p.2 :=
            div_le_div_of_nonneg_right h2 (hz₀_pos p.1.succ p.2).le
          have h4 : -M0 ≤ -cval p.1.succ p.2 / μ z₀ p.1.succ p.2 := by
            linarith [show -M0 ≤ -(|cval p.1.succ p.2| / μ z₀ p.1.succ p.2) by linarith,
              show -(|cval p.1.succ p.2| / μ z₀ p.1.succ p.2) = -|cval p.1.succ p.2| / μ z₀ p.1.succ p.2 by ring]
          have h5 : -M0 / R ≤ (-cval p.1.succ p.2 / μ z₀ p.1.succ p.2) / R :=
            div_le_div_of_nonneg_right h4 hR_pos.le
          rw [show -(M0 / R) = -M0 / R by ring]; exact h5
        linarith
      · have hle : tFun (R • v) / R ≤ M v + M0 / R := by
          rw [div_le_iff₀ hR_pos]
          refine Finset.sup'_le hne_all _ fun q _ => ?_
          rw [← div_le_iff₀ hR_pos]
          have hrew : (-cval q.1 q.2 - μ (R • v) q.1 q.2) / μ z₀ q.1 q.2 / R =
              (-cval q.1 q.2 / μ z₀ q.1 q.2) / R + (-μ v q.1 q.2 / μ z₀ q.1 q.2) := by
            rw [hμ_smul]
            have hRne := hR_pos.ne'; have hz := (hz₀_pos q.1 q.2).ne'
            field_simp; ring
          rw [hrew]
          have hc_le : (-cval q.1 q.2 / μ z₀ q.1 q.2) / R ≤ M0 / R := by
            have h1 : |cval q.1 q.2| / μ z₀ q.1 q.2 ≤ M0 :=
              Finset.le_sup' (fun p : Fin (m + 3) × Fin 2 => |cval p.1 p.2| / μ z₀ p.1 p.2)
                (Finset.mem_univ q)
            have h2 : -cval q.1 q.2 ≤ |cval q.1 q.2| := neg_le_abs _
            have h3 : -cval q.1 q.2 / μ z₀ q.1 q.2 ≤ M0 :=
              (div_le_div_of_nonneg_right h2 (hz₀_pos q.1 q.2).le).trans h1
            exact div_le_div_of_nonneg_right h3 hR_pos.le
          have hμ_le : -μ v q.1 q.2 / μ z₀ q.1 q.2 ≤ M v := by
            rcases q with ⟨j, r⟩
            refine Fin.cases ?_ (fun k' => ?_) j
            · have hu_pos : 0 < μ (uRay v) 0 r := by fin_cases r <;> assumption
              simp only [uRay, hμ_add, hμ_smul] at hu_pos
              rw [div_le_iff₀ (hz₀_pos 0 r)]; linarith
            · exact Finset.le_sup' (fun p : Fin (m + 2) × Fin 2 =>
                -μ v p.1.succ p.2 / μ z₀ p.1.succ p.2) (Finset.mem_univ (k', r))
          linarith
        linarith
    have hg_diff : ∀ j : Fin (m + 2), |gFun (R • v) j / R - mFun v j| ≤ K / R := by
      intro j
      have hL_diff : ∀ r : Fin 2, |Lval (psi (R • v)) j.succ r / R - μ (uRay v) j.succ r| ≤ K / R := by
        intro r
        have hrew : Lval (psi (R • v)) j.succ r / R - μ (uRay v) j.succ r =
            cval j.succ r / R + (tFun (R • v) / R - M v) * μ z₀ j.succ r := by
          simp only [Lval, psi, uRay, hμ_add, hμ_smul]
          have hRne := hR_pos.ne'
          field_simp; ring
        rw [hrew]
        have h1 : |cval j.succ r / R| ≤ Cmax / R := by
          rw [abs_div, abs_of_pos hR_pos]
          exact div_le_div_of_nonneg_right
            (Finset.le_sup' (fun p : Fin (m + 2) × Fin 2 => |cval p.1.succ p.2|) (Finset.mem_univ (j, r)))
            hR_pos.le
        have h2 : |(tFun (R • v) / R - M v) * μ z₀ j.succ r| ≤ (M0 / R) * Zmax := by
          rw [abs_mul, abs_of_pos (hz₀_pos j.succ r)]
          exact mul_le_mul ht_diff
            (Finset.le_sup' (fun p : Fin (m + 2) × Fin 2 => μ z₀ p.1.succ p.2) (Finset.mem_univ (j, r)))
            (hz₀_pos j.succ r).le (div_nonneg hM0_nn hR_pos.le)
        calc |cval j.succ r / R + (tFun (R • v) / R - M v) * μ z₀ j.succ r|
            ≤ |cval j.succ r / R| + |(tFun (R • v) / R - M v) * μ z₀ j.succ r| := abs_add_le _ _
          _ ≤ Cmax / R + (M0 / R) * Zmax := add_le_add h1 h2
          _ = K / R := by simp only [K]; ring
      have hmin : gFun (R • v) j / R =
          min (Lval (psi (R • v)) j.succ 0 / R) (Lval (psi (R • v)) j.succ 1 / R) := by
        unfold gFun
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
          min_mul_of_nonneg _ _ (inv_pos.mpr hR_pos).le]
      rw [hmin]
      exact abs_min_sub_min_le (hL_diff 0) (hL_diff 1)
    set A := gFun (R • v) k / R
    set SA := ∑ j : Fin (m + 2), gFun (R • v) j / R
    set B := mFun v k
    set SB := ∑ j : Fin (m + 2), mFun v j
    have hSA_pos : 0 < SA := by
      simp only [SA, ← Finset.sum_div]; exact div_pos (hgFun_props (R • v)).2.2 hR_pos
    have hSB_ge : δ ≤ SB := hδle v hvS
    have hSB_pos : 0 < SB := lt_of_lt_of_le hδpos hSB_ge
    have hPhiR_eq : PhiR (R • v) k = A / SA := by
      simp only [PhiR, A, SA, ← Finset.sum_div, div_div_div_cancel_right₀ hR_pos.ne']
    have hA_nn : 0 ≤ A := div_nonneg ((hgFun_props (R • v)).1 k) hR_pos.le
    have hA_le_SA : A ≤ SA :=
      Finset.single_le_sum (fun j _ => div_nonneg ((hgFun_props (R • v)).1 j) hR_pos.le) (Finset.mem_univ k)
    have hASA_le1 : |A / SA| ≤ 1 := by
      rw [abs_of_nonneg (div_nonneg hA_nn hSA_pos.le), div_le_one hSA_pos]; exact hA_le_SA
    have hsum_diff : |SB - SA| ≤ ((m + 2 : ℕ) : ℝ) * (K / R) := by
      have hrew : SB - SA = ∑ j : Fin (m + 2), (mFun v j - gFun (R • v) j / R) := by
        simp only [SB, SA, Finset.sum_sub_distrib]
      rw [hrew]
      calc |∑ j : Fin (m + 2), (mFun v j - gFun (R • v) j / R)|
          ≤ ∑ j : Fin (m + 2), |mFun v j - gFun (R • v) j / R| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin (m + 2), (K / R) := Finset.sum_le_sum fun j _ => by
            rw [abs_sub_comm]; exact hg_diff j
        _ = ((m + 2 : ℕ) : ℝ) * (K / R) := by simp
    have hid : A / SA - B / SB = ((A - B) + (A / SA) * (SB - SA)) / SB := by
      have hSAne := hSA_pos.ne'; have hSBne := hSB_pos.ne'
      field_simp; ring
    rw [hPhiR_eq, show PhiInf v k = B / SB from rfl, hid, abs_div, abs_of_pos hSB_pos]
    have hnum_le : |(A - B) + (A / SA) * (SB - SA)| ≤ ((m + 3 : ℕ) : ℝ) * (K / R) := by
      have hcast : ((m + 3 : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) + 1 := by push_cast; ring
      calc |(A - B) + (A / SA) * (SB - SA)|
          ≤ |A - B| + |(A / SA) * (SB - SA)| := abs_add_le _ _
        _ = |A - B| + |A / SA| * |SB - SA| := by rw [abs_mul]
        _ ≤ K / R + 1 * (((m + 2 : ℕ) : ℝ) * (K / R)) :=
            add_le_add (hg_diff k) (mul_le_mul hASA_le1 hsum_diff (abs_nonneg _) zero_le_one)
        _ = ((m + 3 : ℕ) : ℝ) * (K / R) := by rw [hcast]; ring
    have hquot_le : |(A - B) + (A / SA) * (SB - SA)| / SB ≤
        ((m + 3 : ℕ) : ℝ) * (K / R) / δ :=
      (div_le_div_of_nonneg_right hnum_le hSB_pos.le).trans
        (div_le_div_of_nonneg_left (mul_nonneg (by positivity) (div_nonneg hK_nn hR_pos.le)) hδpos hSB_ge)
    refine lt_of_le_of_lt hquot_le ?_
    have hlt_R : ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) * K / δ < R := by simp only [R]; linarith
    have hpos2 : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
    rw [div_lt_div_iff₀ hδpos hpos2]
    have h1 : ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) * K < R * δ := (div_lt_iff₀ hδpos).mp hlt_R
    have h2 : ((m + 3 : ℕ) : ℝ) * (K / R) * ((m + 2 : ℕ) : ℝ) =
        ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) * K / R := by ring
    rw [h2, div_lt_iff₀ hR_pos]
    linarith
  -- 4-band radial surgery N on KM = {v ∈ H0 | M v ≤ 1}
  let Hmap : ℝ → (Fin (m + 2) → ℝ) → Fin (m + 2) → ℝ := fun s z k =>
    (f z k.succ - (1 - s) * f z 0) / ∑ j : Fin (m + 2), (f z j.succ - (1 - s) * f z 0)
  have hHmap_denom_pos : ∀ {s : ℝ}, 0 ≤ s → s ≤ 1 → ∀ z ∈ Jbar, z ≠ 0 →
      0 < ∑ j : Fin (m + 2), (f z j.succ - (1 - s) * f z 0) := by
    intro s _ hs1 z hzJ hzne
    obtain ⟨hf0, hfsucc, hfsum, _, _⟩ := hJbar_props z hzJ hzne
    have hterm : ∀ j : Fin (m + 2), f z j.succ ≤ f z j.succ - (1 - s) * f z 0 := fun j => by
      have : (1 - s) * f z 0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hf0.le
      linarith
    exact lt_of_lt_of_le hfsum (Finset.sum_le_sum fun j _ => hterm j)
  have hHmap_smul : ∀ s {t : ℝ}, 0 < t → ∀ z, Hmap s (t • z) = Hmap s z := by
    intro s t ht z
    funext k
    simp only [Hmap, hf_smul]
    have ht3 : t ^ 3 ≠ 0 := (pow_pos ht 3).ne'
    have h1 : t ^ 3 * f z k.succ - (1 - s) * (t ^ 3 * f z 0) =
        t ^ 3 * (f z k.succ - (1 - s) * f z 0) := by ring
    have h2 : ∑ j : Fin (m + 2), (t ^ 3 * f z j.succ - (1 - s) * (t ^ 3 * f z 0)) =
        t ^ 3 * ∑ j : Fin (m + 2), (f z j.succ - (1 - s) * f z 0) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    rw [h1, h2, mul_div_mul_left _ _ ht3]
  let yBand : (Fin (m + 2) → ℝ) → (Fin (m + 2) → ℝ) := fun v =>
    if v = 0 then 0 else (4 * R * M v / ‖v‖) • v
  have hyBand_cont : Continuous yBand := by
    rw [continuous_iff_continuousAt]
    intro v₀
    by_cases hv₀ : v₀ = 0
    · subst hv₀
      rw [ContinuousAt, Metric.tendsto_nhds]
      intro ε hε
      have hM_tend : Filter.Tendsto (fun v => 4 * R * |M v|) (nhds (0 : Fin (m + 2) → ℝ)) (nhds 0) := by
        have h : ContinuousAt (fun v : Fin (m + 2) → ℝ => 4 * R * |M v|) 0 :=
          (continuous_const.mul (continuous_abs.comp hM_cont)).continuousAt
        simpa [hM_zero] using h.tendsto
      filter_upwards [Metric.tendsto_nhds.mp hM_tend ε hε] with v hv
      have hy0 : yBand 0 = 0 := if_pos rfl
      rw [hy0, dist_zero_right]
      have hnorm_y : ‖yBand v‖ = 4 * R * |M v| := by
        by_cases h : v = 0
        · simp [yBand, h, hM_zero]
        · simp only [yBand, h, ↓reduceIte, norm_smul, Real.norm_eq_abs, abs_div, abs_mul,
            abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hR_pos,
            abs_of_pos (norm_pos_iff.mpr h), div_mul_cancel₀ _ (norm_ne_zero_iff.mpr h)]
      rw [hnorm_y]
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hv
      exact hv
    · have hopen : IsOpen ({v : Fin (m + 2) → ℝ | v ≠ 0}) := isOpen_ne
      have hcont_fn : ContinuousOn (fun v : Fin (m + 2) → ℝ => (4 * R * M v / ‖v‖) • v) {v | v ≠ 0} :=
        (((continuous_const.mul hM_cont).continuousOn).div continuous_norm.continuousOn
          (fun v hv => norm_ne_zero_iff.mpr hv)).smul continuousOn_id
      have hagree : Set.EqOn yBand (fun v => (4 * R * M v / ‖v‖) • v) {v | v ≠ 0} :=
        fun v hv => if_neg hv
      exact (hcont_fn.congr hagree).continuousAt (hopen.mem_nhds hv₀)
  let N1 : (Fin (m + 2) → ℝ) → (Fin (m + 2) → ℝ) := fun v => Hmap (4 * (1 - M v)) (uRay v)
  let N2 : (Fin (m + 2) → ℝ) → (Fin (m + 2) → ℝ) := fun v =>
    (1 - 4 * ((3 : ℝ) / 4 - M v)) • Hmap 1 (uRay v) + (4 * ((3 : ℝ) / 4 - M v)) • PhiInf v
  let N3 : (Fin (m + 2) → ℝ) → (Fin (m + 2) → ℝ) := fun v =>
    (1 - 4 * ((1 : ℝ) / 2 - M v)) • PhiInf v + (4 * ((1 : ℝ) / 2 - M v)) • PhiR ((R / ‖v‖) • v)
  let N4 : (Fin (m + 2) → ℝ) → (Fin (m + 2) → ℝ) := fun v => PhiR (yBand v)
  let N : (Fin (m + 2) → ℝ) → (Fin (m + 2) → ℝ) := fun v =>
    if (3 : ℝ) / 4 ≤ M v then N1 v
    else if (1 : ℝ) / 2 ≤ M v then N2 v
    else if (1 : ℝ) / 4 ≤ M v then N3 v
    else N4 v
  let KM : Set (Fin (m + 2) → ℝ) := {v | v ∈ H0 ∧ M v ≤ 1}
  let C1 : Set (Fin (m + 2) → ℝ) := {v | v ∈ H0 ∧ (3 : ℝ) / 4 ≤ M v ∧ M v ≤ 1}
  let C2 : Set (Fin (m + 2) → ℝ) := {v | v ∈ H0 ∧ (1 : ℝ) / 2 ≤ M v ∧ M v ≤ (3 : ℝ) / 4}
  let C3 : Set (Fin (m + 2) → ℝ) := {v | v ∈ H0 ∧ (1 : ℝ) / 4 ≤ M v ∧ M v ≤ (1 : ℝ) / 2}
  let C4 : Set (Fin (m + 2) → ℝ) := {v | v ∈ H0 ∧ M v ≤ (1 : ℝ) / 4}
  have hC1_closed : IsClosed C1 :=
    hH0_closed.inter ((isClosed_le continuous_const hM_cont).inter (isClosed_le hM_cont continuous_const))
  have hC2_closed : IsClosed C2 :=
    hH0_closed.inter ((isClosed_le continuous_const hM_cont).inter (isClosed_le hM_cont continuous_const))
  have hC3_closed : IsClosed C3 :=
    hH0_closed.inter ((isClosed_le continuous_const hM_cont).inter (isClosed_le hM_cont continuous_const))
  have hC4_closed : IsClosed C4 := hH0_closed.inter (isClosed_le hM_cont continuous_const)
  have hKM_eq : KM = (C1 ∪ C2) ∪ (C3 ∪ C4) := by
    ext v; simp only [KM, C1, C2, C3, C4, Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨hvH, hle⟩
      by_cases h1 : (3 : ℝ) / 4 ≤ M v
      · exact Or.inl (Or.inl ⟨hvH, h1, hle⟩)
      · by_cases h2 : (1 : ℝ) / 2 ≤ M v
        · exact Or.inl (Or.inr ⟨hvH, h2, by linarith⟩)
        · by_cases h3 : (1 : ℝ) / 4 ≤ M v
          · exact Or.inr (Or.inl ⟨hvH, h3, by linarith⟩)
          · exact Or.inr (Or.inr ⟨hvH, by linarith⟩)
    · rintro ((⟨h, _, hle⟩ | ⟨h, _, hle⟩) | (⟨h, _, hle⟩ | ⟨h, hle⟩)) <;> exact ⟨h, by linarith⟩
  have hne_of_Mpos : ∀ {v}, 0 < M v → v ≠ 0 := fun hM hz => by rw [hz, hM_zero] at hM; linarith
  have hN1_cont : ContinuousOn N1 C1 := by
    refine continuousOn_pi.mpr fun k => ContinuousOn.div ?_ ?_ ?_
    · exact (((hf_cont k.succ).comp huRay_cont).sub
        ((continuous_const.sub (continuous_const.mul (continuous_const.sub hM_cont))).mul
          ((hf_cont 0).comp huRay_cont))).continuousOn
    · exact (continuous_finsetSum _ fun j _ =>
        ((hf_cont j.succ).comp huRay_cont).sub
          ((continuous_const.sub (continuous_const.mul (continuous_const.sub hM_cont))).mul
            ((hf_cont 0).comp huRay_cont))).continuousOn
    · rintro v ⟨hvH, hge, hle⟩
      obtain ⟨huJ, hune, _⟩ := huRay_Jbar v hvH (hne_of_Mpos (by linarith))
      exact (hHmap_denom_pos (by linarith) (by linarith) (uRay v) huJ hune).ne'
  have hH1_cont_on : ∀ S : Set (Fin (m + 2) → ℝ), (∀ v ∈ S, v ∈ H0 ∧ 0 < M v) →
      ContinuousOn (fun v => Hmap 1 (uRay v)) S := by
    intro S hS'
    refine continuousOn_pi.mpr fun k => ContinuousOn.div ?_ ?_ ?_
    · exact (((hf_cont k.succ).comp huRay_cont).sub
        (continuous_const.mul ((hf_cont 0).comp huRay_cont))).continuousOn
    · exact (continuous_finsetSum _ fun j _ =>
        ((hf_cont j.succ).comp huRay_cont).sub
          (continuous_const.mul ((hf_cont 0).comp huRay_cont))).continuousOn
    · intro v hv
      obtain ⟨hvH, hMv⟩ := hS' v hv
      obtain ⟨huJ, hune, _⟩ := huRay_Jbar v hvH (hne_of_Mpos hMv)
      exact (hHmap_denom_pos zero_le_one le_rfl (uRay v) huJ hune).ne'
  have hPhiInf_cont_on : ∀ S : Set (Fin (m + 2) → ℝ), (∀ v ∈ S, v ∈ H0 ∧ 0 < M v) →
      ContinuousOn PhiInf S := by
    intro S hS'
    refine continuousOn_pi.mpr fun k =>
      (hmFun_cont k).continuousOn.div (continuous_finsetSum _ fun j _ => hmFun_cont j).continuousOn ?_
    intro v hv
    obtain ⟨hvH, hMv⟩ := hS' v hv
    exact (hmFun_props v hvH (hne_of_Mpos hMv)).2.2.2.ne'
  have hN2_cont : ContinuousOn N2 C2 := by
    have hS2 : ∀ v ∈ C2, v ∈ H0 ∧ 0 < M v := fun v ⟨hvH, hge, _⟩ => ⟨hvH, by linarith⟩
    refine ((continuous_const.sub (continuous_const.mul (continuous_const.sub hM_cont))).continuousOn.smul
      (hH1_cont_on C2 hS2)).add
      ((continuous_const.mul (continuous_const.sub hM_cont)).continuousOn.smul (hPhiInf_cont_on C2 hS2))
  have hN3_cont : ContinuousOn N3 C3 := by
    have hS3 : ∀ v ∈ C3, v ∈ H0 ∧ 0 < M v := fun v ⟨hvH, hge, _⟩ => ⟨hvH, by linarith⟩
    have hRv : ContinuousOn (fun v : Fin (m + 2) → ℝ => (R / ‖v‖) • v) C3 :=
      (continuousOn_const.div continuous_norm.continuousOn
        fun v hv => norm_ne_zero_iff.mpr (hne_of_Mpos (hS3 v hv).2)).smul continuousOn_id
    refine ((continuous_const.sub (continuous_const.mul (continuous_const.sub hM_cont))).continuousOn.smul
      (hPhiInf_cont_on C3 hS3)).add
      ((continuous_const.mul (continuous_const.sub hM_cont)).continuousOn.smul
        (hPhiR_cont.comp_continuousOn hRv))
  have hN4_cont : ContinuousOn N4 C4 := (hPhiR_cont.comp hyBand_cont).continuousOn
  have hN_eq1 : Set.EqOn N N1 C1 := fun v ⟨_, hge, _⟩ => if_pos hge
  have hN_eq2 : Set.EqOn N N2 C2 := by
    rintro v ⟨_, hge, hle⟩
    by_cases h34 : (3 : ℝ) / 4 ≤ M v
    · have hM34 : M v = (3 : ℝ) / 4 := le_antisymm hle h34
      simp only [N, N1, N2, hM34]
      norm_num
    · simp only [N, h34, ↓reduceIte, hge]
  have hN_eq3 : Set.EqOn N N3 C3 := by
    rintro v ⟨_, hge, hle⟩
    have h34 : ¬ ((3 : ℝ) / 4 ≤ M v) := by linarith
    by_cases h12 : (1 : ℝ) / 2 ≤ M v
    · have hM12 : M v = (1 : ℝ) / 2 := le_antisymm hle h12
      simp only [N, N2, N3, hM12]
      norm_num
    · simp only [N, h34, h12, hge, ↓reduceIte]
  have hN_eq4 : Set.EqOn N N4 C4 := by
    rintro v ⟨_, hle⟩
    have h34 : ¬ ((3 : ℝ) / 4 ≤ M v) := by linarith
    have h12 : ¬ ((1 : ℝ) / 2 ≤ M v) := by linarith
    by_cases h14 : (1 : ℝ) / 4 ≤ M v
    · have hM14 : M v = (1 : ℝ) / 4 := le_antisymm hle h14
      have hvne : v ≠ 0 := hne_of_Mpos (by linarith)
      simp only [N, N3, N4, yBand, hvne, hM14]
      norm_num
      congr 2; ring
    · simp only [N, h34, h12, h14, ↓reduceIte]
  have hN_cont : ContinuousOn N KM := by
    rw [hKM_eq]
    exact continuousOn_union_of_isClosed (hC1_closed.union hC2_closed) (hC3_closed.union hC4_closed)
      (continuousOn_union_of_isClosed hC1_closed hC2_closed (hN1_cont.congr hN_eq1) (hN2_cont.congr hN_eq2))
      (continuousOn_union_of_isClosed hC3_closed hC4_closed (hN3_cont.congr hN_eq3) (hN4_cont.congr hN_eq4))
  -- Verify sum = 1 and avoidance of bstar on KM
  have hN_props : ∀ v ∈ KM, ∑ k, N v k = 1 ∧ N v ≠ bstar m := by
    rintro v ⟨hvH, hle1⟩
    by_cases h34 : (3 : ℝ) / 4 ≤ M v
    · simp only [N, h34, ↓reduceIte, N1]
      set s := 4 * (1 - M v)
      have hs0 : 0 ≤ s := by linarith
      have hs1 : s ≤ 1 := by linarith
      obtain ⟨huJ, hune, _⟩ := huRay_Jbar v hvH (hne_of_Mpos (by linarith))
      obtain ⟨_, hiff, ⟨kz, hkz⟩, _⟩ := hmFun_props v hvH (hne_of_Mpos (by linarith))
      obtain ⟨_, _, hfsum, _, _⟩ := hJbar_props (uRay v) huJ hune
      have hden := hHmap_denom_pos hs0 hs1 (uRay v) huJ hune
      refine ⟨?_, fun heq => ?_⟩
      · simp only [Hmap, ← Finset.sum_div, div_self hden.ne']
      · have hfkz : f (uRay v) kz.succ = 0 := (hiff kz).mp hkz
        have hall : ∀ k : Fin (m + 2), f (uRay v) k.succ = 0 := fun k => by
          have hk := congr_fun heq k
          have hkz' := congr_fun heq kz
          simp only [Hmap, bstar] at hk hkz'
          have h1 : f (uRay v) k.succ - (1 - s) * f (uRay v) 0 =
              f (uRay v) kz.succ - (1 - s) * f (uRay v) 0 := by
            have := hk.trans hkz'.symm
            exact (div_left_inj' hden.ne').mp this
          linarith
        have : ∑ k : Fin (m + 2), f (uRay v) k.succ = 0 := Finset.sum_eq_zero fun k _ => hall k
        linarith
    · by_cases h12 : (1 : ℝ) / 2 ≤ M v
      · simp only [N, h34, h12, ↓reduceIte, N2]
        set s := 4 * ((3 : ℝ) / 4 - M v)
        obtain ⟨huJ, hune, _⟩ := huRay_Jbar v hvH (hne_of_Mpos (by linarith))
        obtain ⟨_, hiff, ⟨kz, hkz⟩, hmsum⟩ := hmFun_props v hvH (hne_of_Mpos (by linarith))
        have hden := hHmap_denom_pos zero_le_one le_rfl (uRay v) huJ hune
        have hsum1 : ∑ k, Hmap 1 (uRay v) k = 1 := by
          simp only [Hmap, ← Finset.sum_div, div_self hden.ne']
        have hsum2 : ∑ k, PhiInf v k = 1 := by
          simp only [PhiInf, ← Finset.sum_div, div_self hmsum.ne']
        refine ⟨?_, fun heq => ?_⟩
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
            ← Finset.mul_sum, hsum1, hsum2]; ring
        · have hk := congr_fun heq kz
          have hfkz : f (uRay v) kz.succ = 0 := (hiff kz).mp hkz
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Hmap, PhiInf, hfkz, hkz,
            sub_self, zero_mul, sub_zero, zero_div, mul_zero, add_zero, bstar] at hk
          have : (0 : ℝ) < 1 / ((m + 2 : ℕ) : ℝ) := by positivity
          linarith
      · by_cases h14 : (1 : ℝ) / 4 ≤ M v
        · simp only [N, h34, h12, h14, ↓reduceIte, N3]
          have h12' : M v < (1 : ℝ) / 2 := not_le.mp h12
          set s := 4 * ((1 : ℝ) / 2 - M v)
          have hs0 : 0 ≤ s := by simp only [s]; linarith
          have hs1 : s ≤ 1 := by simp only [s]; linarith
          have hvne : v ≠ 0 := hne_of_Mpos (by linarith)
          have hvnpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
          let u : Fin (m + 2) → ℝ := (‖v‖)⁻¹ • v
          have huS : u ∈ SH0 := by
            refine ⟨?_, ?_⟩
            · change μ ((‖v‖)⁻¹ • v) 0 0 = 0; rw [hμ_smul, hvH, mul_zero]
            · rw [mem_cubeBdry_iff_norm_eq_one, norm_smul, Real.norm_eq_abs, abs_inv,
                abs_of_pos hvnpos, inv_mul_cancel₀ hvnpos.ne']
          have hRu : (R / ‖v‖) • v = R • u := by simp only [u, smul_smul]; ring_nf
          have hPhiInf_eq : PhiInf v = PhiInf u := by
            have hv_eq : v = ‖v‖ • u := by
              simp only [u, smul_smul, mul_inv_cancel₀ hvnpos.ne', one_smul]
            rw [hv_eq, hPhiInf_smul hvnpos]
          obtain ⟨_, _, ⟨kz, hkz⟩, hmsum⟩ := hmFun_props v hvH hvne
          have hsum1 : ∑ k, PhiInf v k = 1 := by
            simp only [PhiInf, ← Finset.sum_div, div_self hmsum.ne']
          have hsum2 : ∑ k, PhiR ((R / ‖v‖) • v) k = 1 := (hPhiR_props _).2.1
          refine ⟨?_, fun heq => ?_⟩
          · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
              ← Finset.mul_sum, hsum1, hsum2]; ring
          · have hk := congr_fun heq kz
            have hinf0 : PhiInf v kz = 0 := by simp [PhiInf, hkz]
            have hinfu0 : PhiInf u kz = 0 := by rw [← hPhiInf_eq]; exact hinf0
            have hclose := hPhiR_close u huS kz
            rw [hinfu0, sub_zero, abs_of_nonneg ((hPhiR_props (R • u)).1 kz)] at hclose
            have hnnR := (hPhiR_props (R • u)).1 kz
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hinf0, mul_zero, zero_add,
              hRu, bstar] at hk
            have hleR : s * PhiR (R • u) kz ≤ PhiR (R • u) kz :=
              mul_le_of_le_one_left hnnR hs1
            linarith
        · simp only [N, h34, h12, h14, ↓reduceIte, N4]
          exact ⟨(hPhiR_props _).2.1, (hPhiR_props _).2.2⟩
  -- Pull back along xOf z := (μ z 0 0)⁻¹ • z - z₀ and apply PsiInv
  let xOf : (Fin (m + 2) → ℝ) → (Fin (m + 2) → ℝ) := fun z => (μ z 0 0)⁻¹ • z - z₀
  have hxOf_cont : ContinuousOn xOf Da := by
    refine ContinuousOn.sub ?_ continuousOn_const
    exact ((hμ_cont 0 0).continuousOn.inv₀ fun z hz => by
      have hzne : z ≠ 0 := fun h0 => by
        have := (mem_cubeBdry_iff_norm_eq_one z).mp hz.2; rw [h0, norm_zero] at this; norm_num at this
      exact (hJbar_props z hz.1 hzne).2.2.2.1.ne').smul continuousOn_id
  have hxOf_maps : Set.MapsTo xOf Da KM := by
    intro z hz
    have hzne : z ≠ 0 := fun h0 => by
      have := (mem_cubeBdry_iff_norm_eq_one z).mp hz.2; rw [h0, norm_zero] at this; norm_num at this
    have h00 : 0 < μ z 0 0 := (hJbar_props z hz.1 hzne).2.2.2.1
    refine ⟨?_, ?_⟩
    · show μ ((μ z 0 0)⁻¹ • z - z₀) 0 0 = 0
      rw [hμ_sub, hμ_smul, hz₀_00, inv_mul_cancel₀ h00.ne', sub_self]
    · rw [hM_le_iff]
      intro k r
      have hrew : xOf z + (1 : ℝ) • z₀ = (μ z 0 0)⁻¹ • z := by simp [xOf]
      rw [hrew, hμ_smul]
      exact mul_nonneg (inv_pos.mpr h00).le (hz.1 k.succ r)
  let Fsur : (Fin (m + 2) → ℝ) → (Fin (m + 3) → ℝ) := fun z => PsiInv (N (xOf z))
  refine ⟨Fsur, ?_, ?_, ?_⟩
  · exact (continuous_PsiInv m).comp_continuousOn (hN_cont.comp hxOf_cont hxOf_maps)
  · intro z hz
    obtain ⟨hsumN, hneN⟩ := hN_props (xOf z) (hxOf_maps hz)
    exact ⟨sum_PsiInv hsumN, norm_PsiInv _, PsiInv_ne_qstar hneN, PsiInv_ne_neg_qstar _⟩
  · intro z hz hnotJ
    have hzne : z ≠ 0 := fun h0 => by
      have := (mem_cubeBdry_iff_norm_eq_one z).mp hz.2; rw [h0, norm_zero] at this; norm_num at this
    obtain ⟨hf0, hfsucc, _, h00, h01⟩ := hJbar_props z hz.1 hzne
    have hMle : M (xOf z) ≤ 1 := (hxOf_maps hz).2
    have hM1 : M (xOf z) = 1 := by
      refine le_antisymm hMle ?_
      by_contra hlt; push Not at hlt
      apply hnotJ
      have hpos_succ := (hM_lt_iff (xOf z) 1).mp hlt
      intro j r
      refine Fin.cases ?_ (fun k => ?_) j
      · fin_cases r <;> assumption
      · have hrew : xOf z + (1 : ℝ) • z₀ = (μ z 0 0)⁻¹ • z := by simp [xOf]
        have hpk := hpos_succ k r
        rw [hrew, hμ_smul] at hpk
        have := mul_pos h00 hpk
        rwa [← mul_assoc, mul_inv_cancel₀ h00.ne', one_mul] at this
    have huRay_eq : uRay (xOf z) = (μ z 0 0)⁻¹ • z := by
      simp only [uRay, hM1, one_smul, xOf]; abel
    have hN_eq : N (xOf z) = Hmap 0 z := by
      simp only [N, N1, hM1, sub_self, mul_zero, huRay_eq]
      rw [if_pos (by norm_num : (3 : ℝ) / 4 ≤ 1)]
      exact hHmap_smul 0 (inv_pos.mpr h00) z
    have hH0_eq : Hmap 0 z = fun k => (f z k.succ - f z 0) / ∑ j : Fin (m + 2), (f z j.succ - f z 0) := by
      funext k; simp [Hmap]
    simp only [Fsur, hN_eq, hH0_eq]
    exact PsiInv_H0_eq_Fbar hf0 hfsucc

private lemma no_shatters_d2_ge3 {m : ℕ}
    {C : Set (Fin (m + 4) → ℝ)} (hC : Convex ℝ C)
    {x : Fin (m + 3) → Fin 3 → (Fin (m + 4) → ℝ)}
    {y : Set (Fin (m + 3) → Fin 3) → (Fin (m + 4) → ℝ)}
    (hS : ShattersN C x y) : False := by
  obtain ⟨hker_rk, hsurj⟩ := ker_finrank_and_surj (m := m + 1) hC hS
  obtain ⟨eW⟩ : Nonempty ((Fin (m + 2) → ℝ) ≃ₗ[ℝ] LinearMap.ker (sumMap x)) :=
    ⟨(Module.finBasisOfFinrankEq ℝ (LinearMap.ker (sumMap x)) hker_rk).equivFun.symm⟩
  let Z : (Fin (m + 2) → ℝ) →ₗ[ℝ] (Fin (m + 3) → Fin 2 → ℝ) :=
    (LinearMap.ker (sumMap x)).subtype.comp eW.toLinearMap
  have hZ_cont : Continuous Z := LinearMap.continuous_of_finiteDimensional Z
  have hZ_ker : ∀ z, sumMap x (Z z) = 0 := fun z => (eW z).2
  have hZ_inj : ∀ z, Z z = 0 → z = 0 := fun z hz =>
    eW.map_eq_zero_iff.mp (Subtype.ext hz)
  let f : (Fin (m + 2) → ℝ) → Fin (m + 3) → ℝ := fun z => cubicF (Z z)
  have hf_cont : Continuous f := continuous_pi fun j => (continuous_cubicF j).comp hZ_cont
  have hf_neg : ∀ z, f (-z) = -f z := fun z => by simp only [f, map_neg, cubicF_neg]
  have hpiE_ne : ∀ z, z ≠ 0 → piE (f z) ≠ 0 := by
    intro z hzne h0
    have hZne : Z z ≠ 0 := fun h => hzne (hZ_inj z h)
    have hconst : ∀ j : Fin (m + 3), f z j = f z 0 := fun j => by
      have hj := congr_fun h0 j; have h0' := congr_fun h0 0
      simp only [piE, Pi.zero_apply] at hj h0'; linarith
    rcases le_total 0 (f z 0) with hnn | hnp
    · exact cubicF_not_nonneg hC hS (hZ_ker z) hZne fun j => by change 0 ≤ f z j; rw [hconst j]; exact hnn
    · exact cubicF_not_nonpos hC hS (hZ_ker z) hZne fun j => by change f z j ≤ 0; rw [hconst j]; exact hnp
  let Fbar : (Fin (m + 2) → ℝ) → (Fin (m + 3) → ℝ) := fun z => (‖piE (f z)‖)⁻¹ • piE (f z)
  have hFbar_cont : ContinuousOn Fbar (cubeBdry (m + 1)) := by
    have hpi : Continuous (fun z => piE (f z)) := (continuous_piE m).comp hf_cont
    exact ((continuous_norm.comp hpi).continuousOn.inv₀ fun z hz => by
      have hzne : z ≠ 0 := fun h0 => by
        have := (mem_cubeBdry_iff_norm_eq_one z).mp hz; rw [h0, norm_zero] at this; norm_num at this
      exact norm_ne_zero_iff.mpr (hpiE_ne z hzne)).smul hpi.continuousOn
  have hFbar_odd : ∀ z, Fbar (-z) = -Fbar z := fun z => by
    simp only [Fbar, hf_neg, piE_neg, norm_neg, smul_neg]
  have hFbar_norm : ∀ z ∈ cubeBdry (m + 1), ‖Fbar z‖ = 1 := fun z hz => by
    have hzne : z ≠ 0 := fun h0 => by
      have := (mem_cubeBdry_iff_norm_eq_one z).mp hz; rw [h0, norm_zero] at this; norm_num at this
    have hpos : 0 < ‖piE (f z)‖ := norm_pos_iff.mpr (hpiE_ne z hzne)
    simp only [Fbar, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
  have hFbar_sum : ∀ z, ∑ j, Fbar z j = 0 := fun z => by
    simp only [Fbar, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, sum_piE, mul_zero]
  let J : (Fin (m + 3) → Fin 3) → Set (Fin (m + 2) → ℝ) :=
    fun a => {z | ∀ k r, 0 < muCoord a (Z z) k r}
  let D : (Fin (m + 3) → Fin 3) → Set (Fin (m + 2) → ℝ) :=
    fun a => {z | ∀ k r, 0 ≤ muCoord a (Z z) k r} ∩ cubeBdry (m + 1)
  have hμ_cont : ∀ a k r, Continuous (fun z => muCoord a (Z z) k r) := fun a k r =>
    (continuous_muCoord a k r).comp hZ_cont
  have hJ_open : ∀ a, IsOpen (J a) := fun a => by
    have heq : J a = ⋂ k : Fin (m + 3), ⋂ r : Fin 2, {z | 0 < muCoord a (Z z) k r} := by
      ext z; simp [J]
    rw [heq]
    exact isOpen_iInter_of_finite fun k => isOpen_iInter_of_finite fun r =>
      isOpen_lt continuous_const (hμ_cont a k r)
  have hD_closed : ∀ a, IsClosed (D a) := fun a => by
    have h1 : IsClosed {z | ∀ k r, 0 ≤ muCoord a (Z z) k r} := by
      have heq : {z | ∀ k r, 0 ≤ muCoord a (Z z) k r} =
          ⋂ k : Fin (m + 3), ⋂ r : Fin 2, {z | 0 ≤ muCoord a (Z z) k r} := by ext z; simp
      rw [heq]
      exact isClosed_iInter fun k => isClosed_iInter fun r =>
        isClosed_le continuous_const (hμ_cont a k r)
    exact h1.inter (cubeBdry_isCompact (m + 1)).isClosed
  have hD_f0_neg : ∀ a z, z ∈ D a → f z 0 < 0 := by
    intro a z hz
    have hzne : z ≠ 0 := fun h0 => by
      have := (mem_cubeBdry_iff_norm_eq_one z).mp hz.2; rw [h0, norm_zero] at this; norm_num at this
    have hZne : Z z ≠ 0 := fun h => hzne (hZ_inj z h)
    have hf0_le : f z 0 ≤ 0 := by
      change cubicF (Z z) 0 ≤ 0; rw [muCoord_cubic_zero a]
      have h0 := hz.1 0 0; have h1 := hz.1 0 1; nlinarith [mul_nonneg h0 h1]
    exact lt_of_le_of_ne hf0_le fun hf0 => by
      apply cubicF_not_nonneg hC hS (hZ_ker z) hZne
      intro j; refine Fin.cases (by linarith) (fun k => ?_) j
      rw [muCoord_cubic_succ a]; have h0 := hz.1 k.succ 0; have h1 := hz.1 k.succ 1; positivity
  have hJ_f0_neg : ∀ a z, z ∈ J a → f z 0 < 0 := fun a z hz => by
    change cubicF (Z z) 0 < 0; rw [muCoord_cubic_zero a]
    have h0 := hz 0 0; have h1 := hz 0 1; nlinarith [mul_pos h0 h1]
  have hJ_disj : ∀ a b z, z ∈ D a → z ∈ J b → a = b := by
    intro a b z hza hzb
    have hf0 : f z 0 < 0 := hD_f0_neg a z hza
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · have ha0 : 0 < muCoord a (Z z) 0 0 := lt_of_le_of_ne (hza.1 0 0) fun h0 => by
        have : f z 0 = 0 := by change cubicF (Z z) 0 = 0; rw [muCoord_cubic_zero a, ← h0]; simp
        linarith
      have ha1 : 0 < muCoord a (Z z) 0 1 := lt_of_le_of_ne (hza.1 0 1) fun h0 => by
        have : f z 0 = 0 := by change cubicF (Z z) 0 = 0; rw [muCoord_cubic_zero a, ← h0]; simp
        linarith
      have hneg : ∀ ak r, coneCoord ak (-(Z z 0)) r = -coneCoord ak (Z z 0) r := fun ak r => by
        have := coneCoord_smul ak (-1) (Z z 0) r; simpa using this
      refine coneCoord_pos_unique (c := -(Z z 0)) ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · rw [hneg]; exact ha0
      · rw [hneg]; exact ha1
      · rw [hneg]; exact hzb 0 0
      · rw [hneg]; exact hzb 0 1
    · have hfk : 0 < f z k.succ := by
        change 0 < cubicF (Z z) k.succ; rw [muCoord_cubic_succ b]
        have h0 := hzb k.succ 0; have h1 := hzb k.succ 1; positivity
      have ha0 : 0 < muCoord a (Z z) k.succ 0 := lt_of_le_of_ne (hza.1 k.succ 0) fun h0 => by
        have : f z k.succ = 0 := by change cubicF (Z z) k.succ = 0; rw [muCoord_cubic_succ a, ← h0]; simp
        linarith
      have ha1 : 0 < muCoord a (Z z) k.succ 1 := lt_of_le_of_ne (hza.1 k.succ 1) fun h0 => by
        have : f z k.succ = 0 := by change cubicF (Z z) k.succ = 0; rw [muCoord_cubic_succ a, ← h0]; simp
        linarith
      exact coneCoord_pos_unique (c := Z z k.succ) ⟨ha0, ha1⟩ ⟨hzb k.succ 0, hzb k.succ 1⟩
  have hJ_unique : ∀ a b z, z ∈ J a → z ∈ J b → a = b := by
    intro a b z hza hzb
    have hzn : z ≠ 0 := fun h0 => by
      have := hza 0 0; rw [h0] at this
      have : muCoord a (Z 0) 0 0 = 0 := by
        have hsm := muCoord_smul a 0 (Z 0) 0 0; simpa using hsm
      linarith
    have hza' : (‖z‖)⁻¹ • z ∈ D a := by
      refine ⟨fun k r => ?_, ?_⟩
      · rw [map_smul, muCoord_smul]; exact mul_nonneg (inv_pos.mpr (norm_pos_iff.mpr hzn)).le (hza k r).le
      · rw [mem_cubeBdry_iff_norm_eq_one, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_pos (norm_pos_iff.mpr hzn), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hzn)]
    have hzb' : (‖z‖)⁻¹ • z ∈ J b := fun k r => by
      rw [map_smul, muCoord_smul]; exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hzn)) (hzb k r)
    exact hJ_disj a b _ hza' hzb'
  have hFbar_qstar_mem : ∀ z ∈ cubeBdry (m + 1), Fbar z = qstar m → ∃ a, z ∈ J a := by
    intro z hzB hq
    have hzne : z ≠ 0 := fun h0 => by
      have := (mem_cubeBdry_iff_norm_eq_one z).mp hzB; rw [h0, norm_zero] at this; norm_num at this
    have hZne : Z z ≠ 0 := fun h => hzne (hZ_inj z h)
    set lam := ‖piE (f z)‖
    have hlam : 0 < lam := norm_pos_iff.mpr (hpiE_ne z hzne)
    set c := (∑ j, f z j) / ((m + 3 : ℕ) : ℝ)
    have hf0_eq : f z 0 = c - lam := by
      have h0 := congr_fun hq 0
      simp only [Fbar, Pi.smul_apply, smul_eq_mul, piE, qstar, Fin.cons_zero] at h0
      have hmul := congr_arg (fun t => lam * t) h0
      rw [← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul] at hmul
      linarith
    have hfk_eq : ∀ k : Fin (m + 2), f z k.succ = c + lam / ((m + 2 : ℕ) : ℝ) := fun k => by
      have hk := congr_fun hq k.succ
      simp only [Fbar, Pi.smul_apply, smul_eq_mul, piE, qstar, Fin.cons_succ] at hk
      have hmul := congr_arg (fun t => lam * t) hk
      rw [← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul] at hmul
      have : lam * (1 / ((m + 2 : ℕ) : ℝ)) = lam / ((m + 2 : ℕ) : ℝ) := by ring
      linarith
    have hf0_neg : f z 0 < 0 := by
      by_contra hge; push Not at hge
      apply cubicF_not_nonneg hC hS (hZ_ker z) hZne
      intro j; refine Fin.cases hge (fun k => ?_) j
      change 0 ≤ f z k.succ
      rw [hfk_eq k]; have : 0 < lam / ((m + 2 : ℕ) : ℝ) := by positivity
      linarith
    have hfk_pos : ∀ k : Fin (m + 2), 0 < f z k.succ := fun k => by
      by_contra hle; push Not at hle
      apply cubicF_not_nonpos hC hS (hZ_ker z) hZne
      intro j; refine Fin.cases hf0_neg.le (fun k' => ?_) j
      change f z k'.succ ≤ 0
      rw [hfk_eq k']; rw [hfk_eq k] at hle; linarith
    have hex0 : ∃ a0 : Fin 3, 0 < coneCoord a0 (-(Z z 0)) 0 ∧ 0 < coneCoord a0 (-(Z z 0)) 1 := by
      rw [← cubic_pos_iff]
      have : (-Z z 0) 0 * (-Z z 0) 1 * ((-Z z 0) 0 + (-Z z 0) 1) = -f z 0 := by
        simp only [f, cubicF, Pi.neg_apply]; ring
      linarith
    have hexk : ∀ k : Fin (m + 2), ∃ ak : Fin 3,
        0 < coneCoord ak (Z z k.succ) 0 ∧ 0 < coneCoord ak (Z z k.succ) 1 := fun k =>
      (cubic_pos_iff (Z z k.succ)).mp (hfk_pos k)
    let a : Fin (m + 3) → Fin 3 := Fin.cons hex0.choose (fun k => (hexk k).choose)
    refine ⟨a, fun j r => ?_⟩
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [muCoord, Fin.cases_zero, a, Fin.cons_zero]
      have hneg : coneCoord hex0.choose (-(Z z 0)) r = -coneCoord hex0.choose (Z z 0) r := by
        have := coneCoord_smul hex0.choose (-1) (Z z 0) r; simpa using this
      rw [← hneg]; fin_cases r
      · exact hex0.choose_spec.1
      · exact hex0.choose_spec.2
    · simp only [muCoord, Fin.cases_succ, a, Fin.cons_succ]
      fin_cases r
      · exact (hexk k).choose_spec.1
      · exact (hexk k).choose_spec.2
  -- Extract surgery map for each nonempty chamber a
  have hsur_all : ∀ (a : Fin (m + 3) → Fin 3) (ha : (J a).Nonempty),
      ∃ Fsur : (Fin (m + 2) → ℝ) → (Fin (m + 3) → ℝ),
        ContinuousOn Fsur (D a) ∧
        (∀ z ∈ D a, ∑ j, Fsur z j = 0 ∧ ‖Fsur z‖ = 1 ∧ Fsur z ≠ qstar m ∧ Fsur z ≠ -qstar m) ∧
        (∀ z ∈ D a, z ∉ J a → Fsur z = Fbar z) := fun a ha =>
    chamber_surgery hC hS hsurj eW a ha
  obtain ⟨Fsur, hFsur_spec⟩ :
      ∃ Fsur : ∀ (a : Fin (m + 3) → Fin 3), (J a).Nonempty → (Fin (m + 2) → ℝ) → (Fin (m + 3) → ℝ),
        ∀ a ha,
          ContinuousOn (Fsur a ha) (D a) ∧
          (∀ z ∈ D a, ∑ j, Fsur a ha z j = 0 ∧ ‖Fsur a ha z‖ = 1 ∧
            Fsur a ha z ≠ qstar m ∧ Fsur a ha z ≠ -qstar m) ∧
          (∀ z ∈ D a, z ∉ J a → Fsur a ha z = Fbar z) :=
    ⟨fun a ha => (hsur_all a ha).choose, fun a ha => (hsur_all a ha).choose_spec⟩
  have hFsur_eq : ∀ {a₁ a₂} (h₁ : (J a₁).Nonempty) (h₂ : (J a₂).Nonempty) {z₁ z₂},
      a₁ = a₂ → z₁ = z₂ → Fsur a₁ h₁ z₁ = Fsur a₂ h₂ z₂ := by
    rintro a _ h₁ h₂ z _ rfl rfl; rfl
  -- Global pasted odd map Ftilde
  let Ftilde : (Fin (m + 2) → ℝ) → (Fin (m + 3) → ℝ) := fun z =>
    if h1 : ∃ a, z ∈ J a then
      Fsur h1.choose ⟨z, h1.choose_spec⟩ z
    else if h2 : ∃ a, -z ∈ J a then
      -Fsur h2.choose ⟨-z, h2.choose_spec⟩ (-z)
    else
      Fbar z
  have hFtilde_odd : ∀ z, Ftilde (-z) = -Ftilde z := by
    intro z
    by_cases h1 : ∃ a, z ∈ J a
    · obtain ⟨a, ha⟩ := h1
      have hno : ¬ ∃ b, -z ∈ J b := by
        rintro ⟨b, hb⟩
        have h1' := hJ_f0_neg a z ha
        have h2' := hJ_f0_neg b (-z) hb
        rw [hf_neg, Pi.neg_apply] at h2'; linarith
      have h1' : ∃ b, z ∈ J b := ⟨a, ha⟩
      have h2' : ∃ b, -(-z) ∈ J b := ⟨a, by simpa using ha⟩
      dsimp only [Ftilde]
      rw [dif_neg hno, dif_pos h2', dif_pos h1']
      congr 1
      exact hFsur_eq _ _ (hJ_unique _ _ z (by simpa using h2'.choose_spec) h1'.choose_spec) (neg_neg z)
    · by_cases h2 : ∃ a, -z ∈ J a
      · simp only [Ftilde, h1, h2, ↓reduceDIte, neg_neg]
      · have h2neg : ¬ ∃ b, -(-z) ∈ J b := by simpa using h1
        simp only [Ftilde, h1, h2, h2neg, ↓reduceDIte, hFbar_odd]
  have hFtilde_eq_D : ∀ a (ha : (J a).Nonempty), Set.EqOn Ftilde (Fsur a ha) (D a) := by
    intro a ha z hzD
    by_cases hzJ : z ∈ J a
    · have h1 : ∃ b, z ∈ J b := ⟨a, hzJ⟩
      simp only [Ftilde, h1, ↓reduceDIte]
      exact hFsur_eq _ _ (hJ_unique _ _ z h1.choose_spec hzJ) rfl
    · have hno1 : ¬ ∃ b, z ∈ J b := by
        rintro ⟨b, hb⟩
        have heq_ab : a = b := hJ_disj a b z hzD hb
        exact hzJ (heq_ab ▸ hb)
      have hno2 : ¬ ∃ b, -z ∈ J b := by
        rintro ⟨b, hb⟩
        have h1' := hD_f0_neg a z hzD
        have h2' := hJ_f0_neg b (-z) hb
        rw [hf_neg, Pi.neg_apply] at h2'; linarith
      simp only [Ftilde, hno1, hno2, ↓reduceDIte]
      exact ((hFsur_spec a ha).2.2 z hzD hzJ).symm
  let Uall : Set (Fin (m + 2) → ℝ) := (⋃ a, J a) ∪ (⋃ a, (fun z => -z) ⁻¹' J a)
  have hUall_open : IsOpen Uall :=
    (isOpen_iUnion hJ_open).union (isOpen_iUnion fun a => (hJ_open a).preimage continuous_neg)
  let K0 : Set (Fin (m + 2) → ℝ) := cubeBdry (m + 1) \ Uall
  have hK0_closed : IsClosed K0 := (cubeBdry_isCompact (m + 1)).isClosed.sdiff hUall_open
  have hFtilde_eq_K0 : Set.EqOn Ftilde Fbar K0 := by
    rintro z ⟨_, hnotU⟩
    have hno1 : ¬ ∃ a, z ∈ J a := fun ⟨a, ha⟩ => hnotU (Or.inl (Set.mem_iUnion.mpr ⟨a, ha⟩))
    have hno2 : ¬ ∃ a, -z ∈ J a := fun ⟨a, ha⟩ => hnotU (Or.inr (Set.mem_iUnion.mpr ⟨a, ha⟩))
    simp only [Ftilde, hno1, hno2, ↓reduceDIte]
  classical
  let Sne : Finset (Fin (m + 3) → Fin 3) := Finset.univ.filter (fun a => (J a).Nonempty)
  let PosU : Set (Fin (m + 2) → ℝ) := ⋃ a ∈ Sne, D a
  let NegU : Set (Fin (m + 2) → ℝ) := ⋃ a ∈ Sne, (fun z => -z) ⁻¹' D a
  have hcover : cubeBdry (m + 1) = K0 ∪ (PosU ∪ NegU) := by
    ext z
    constructor
    · intro hzB
      by_cases hU : z ∈ Uall
      · rcases hU with hpos | hneg
        · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hpos
          refine Or.inr (Or.inl (Set.mem_iUnion₂.mpr ⟨a, ?_, ⟨fun k r => (ha k r).le, hzB⟩⟩))
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ⟨z, ha⟩⟩
        · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hneg
          refine Or.inr (Or.inr (Set.mem_iUnion₂.mpr ⟨a, ?_, ⟨fun k r => (ha k r).le, neg_mem_cubeBdry hzB⟩⟩))
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ⟨-z, ha⟩⟩
      · exact Or.inl ⟨hzB, hU⟩
    · rintro (⟨hzB, _⟩ | hPos | hNeg)
      · exact hzB
      · obtain ⟨a, _, hzD⟩ := Set.mem_iUnion₂.mp hPos; exact hzD.2
      · obtain ⟨a, _, hzD⟩ := Set.mem_iUnion₂.mp hNeg
        simpa using neg_mem_cubeBdry hzD.2
  have hPos_closed : IsClosed PosU := isClosed_biUnion_finset fun a _ => hD_closed a
  have hNeg_closed : IsClosed NegU :=
    isClosed_biUnion_finset fun a _ => (hD_closed a).preimage continuous_neg
  have hPos_cont : ContinuousOn Ftilde PosU := by
    refine continuousOn_biUnion_of_isClosed Sne D (fun a _ => hD_closed a) fun a haS => ?_
    have ha : (J a).Nonempty := (Finset.mem_filter.mp haS).2
    exact (hFsur_spec a ha).1.congr (hFtilde_eq_D a ha)
  have hNeg_cont : ContinuousOn Ftilde NegU := by
    refine continuousOn_biUnion_of_isClosed Sne (fun a => (fun z => -z) ⁻¹' D a)
      (fun a _ => (hD_closed a).preimage continuous_neg) fun a haS => ?_
    have ha : (J a).Nonempty := (Finset.mem_filter.mp haS).2
    have hcomp : ContinuousOn (fun z => -Fsur a ha (-z)) ((fun z => -z) ⁻¹' D a) :=
      ((hFsur_spec a ha).1.comp continuous_neg.continuousOn (fun _ hz => hz)).neg
    refine hcomp.congr fun z hz => ?_
    have h1 := hFtilde_odd (-z)
    rw [neg_neg] at h1
    rw [h1, hFtilde_eq_D a ha hz]
  have hFtilde_cont : ContinuousOn Ftilde (cubeBdry (m + 1)) := by
    rw [hcover]
    exact continuousOn_union_of_isClosed hK0_closed (hPos_closed.union hNeg_closed)
      ((hFbar_cont.mono fun _ h => h.1).congr hFtilde_eq_K0)
      (continuousOn_union_of_isClosed hPos_closed hNeg_closed hPos_cont hNeg_cont)
  have hFtilde_vals : ∀ z ∈ cubeBdry (m + 1),
      ∑ j, Ftilde z j = 0 ∧ ‖Ftilde z‖ = 1 ∧ Ftilde z ≠ qstar m ∧ Ftilde z ≠ -qstar m := by
    intro z hzB
    rw [hcover] at hzB
    rcases hzB with ⟨hzB', hnotU⟩ | hPos | hNeg
    · rw [hFtilde_eq_K0 ⟨hzB', hnotU⟩]
      refine ⟨hFbar_sum z, hFbar_norm z hzB', ?_, ?_⟩
      · intro hq
        obtain ⟨a, ha⟩ := hFbar_qstar_mem z hzB' hq
        exact hnotU (Or.inl (Set.mem_iUnion.mpr ⟨a, ha⟩))
      · intro hnq
        have hq : Fbar (-z) = qstar m := by rw [hFbar_odd, hnq, neg_neg]
        obtain ⟨a, ha⟩ := hFbar_qstar_mem (-z) (neg_mem_cubeBdry hzB') hq
        exact hnotU (Or.inr (Set.mem_iUnion.mpr ⟨a, ha⟩))
    · obtain ⟨a, haS, hzD⟩ := Set.mem_iUnion₂.mp hPos
      have ha : (J a).Nonempty := (Finset.mem_filter.mp haS).2
      rw [hFtilde_eq_D a ha hzD]
      exact (hFsur_spec a ha).2.1 z hzD
    · obtain ⟨a, haS, hzD⟩ := Set.mem_iUnion₂.mp hNeg
      have ha : (J a).Nonempty := (Finset.mem_filter.mp haS).2
      have h1 := hFtilde_odd (-z)
      rw [neg_neg] at h1
      rw [h1, hFtilde_eq_D a ha hzD]
      obtain ⟨hs, hn, hq1, hq2⟩ := (hFsur_spec a ha).2.1 (-z) hzD
      refine ⟨by simp [Finset.sum_neg_distrib, hs], by rwa [norm_neg], ?_, ?_⟩
      · intro h; exact hq2 (by rw [← neg_neg (Fsur a ha (-z)), h])
      · intro h; exact hq1 (neg_injective h)
  exact no_odd_map_avoiding_qstar m Ftilde hFtilde_cont (fun z _ => hFtilde_odd z)
    (fun z hz => (hFtilde_vals z hz).1)
    (fun z hz => (hFtilde_vals z hz).2.1)
    (fun z hz => ⟨(hFtilde_vals z hz).2.2.1, (hFtilde_vals z hz).2.2.2⟩)

end ChamberSurgery

/- ## Section 4: Base Cases (n = 2, n = 1) and Master Theorems -/

section BaseCasesAndMain

private lemma no_shatters_d2_n2
    {C : Set (Fin 3 → ℝ)} (hC : Convex ℝ C)
    {x : Fin 2 → Fin 3 → (Fin 3 → ℝ)}
    {y : Set (Fin 2 → Fin 3) → (Fin 3 → ℝ)}
    (hS : ShattersN C x y) : False := by
  obtain ⟨hker_rk, hsurj⟩ := ker_finrank_and_surj (m := 0) hC hS
  have hpos : 0 < Module.finrank ℝ (LinearMap.ker (sumMap x)) := by rw [hker_rk]; omega
  have : Nontrivial (LinearMap.ker (sumMap x)) := Module.finrank_pos_iff.mp hpos
  obtain ⟨z', hz'ne⟩ := exists_ne (0 : LinearMap.ker (sumMap x))
  have hc'ne : z'.1 ≠ 0 := fun h => hz'ne (Subtype.ext h)
  have hex_c : ∃ c : Fin 2 → Fin 2 → ℝ, sumMap x c = 0 ∧ cubicF c 0 < 0 ∧ 0 < cubicF c 1 := by
    by_cases h0 : cubicF z'.1 0 < 0
    · refine ⟨z'.1, z'.2, h0, ?_⟩
      by_contra h1; push Not at h1
      apply cubicF_not_nonpos hC hS z'.2 hc'ne
      intro k
      rcases (by fin_cases k <;> simp : k = 0 ∨ k = 1) with rfl | rfl
      · exact h0.le
      · exact h1
    · push Not at h0
      have h1 : cubicF z'.1 1 < 0 := by
        by_contra h1'; push Not at h1'
        apply cubicF_not_nonneg hC hS z'.2 hc'ne
        intro k
        rcases (by fin_cases k <;> simp : k = 0 ∨ k = 1) with rfl | rfl
        · exact h0
        · exact h1'
      have h0pos : 0 < cubicF z'.1 0 := lt_of_le_of_ne h0 fun h0z => by
        apply cubicF_not_nonpos hC hS z'.2 hc'ne
        intro k
        rcases (by fin_cases k <;> simp : k = 0 ∨ k = 1) with rfl | rfl
        · linarith
        · exact h1.le
      refine ⟨-z'.1, by rw [map_neg, z'.2, neg_zero], ?_, ?_⟩
      · rw [cubicF_neg, Pi.neg_apply]; linarith
      · rw [cubicF_neg, Pi.neg_apply]; linarith
  obtain ⟨c, hcker, hc0, hc1⟩ := hex_c
  have hex0 : ∃ a0 : Fin 3, 0 < coneCoord a0 (-(c 0)) 0 ∧ 0 < coneCoord a0 (-(c 0)) 1 := by
    rw [← cubic_pos_iff]
    have : (-c 0) 0 * (-c 0) 1 * ((-c 0) 0 + (-c 0) 1) = -cubicF c 0 := by
      simp only [cubicF, Pi.neg_apply]; ring
    linarith
  obtain ⟨a0, ha00, ha01⟩ := hex0
  obtain ⟨a1, ha10, ha11⟩ := (cubic_pos_iff (c 1)).mp hc1
  let a : Fin 2 → Fin 3 := ![a0, a1]
  have hμpos : ∀ (k : Fin 2) (r : Fin 2), 0 < muCoord a c k r := by
    intro k r
    have hneg : coneCoord a0 (-(c 0)) r = -coneCoord a0 (c 0) r := by
      have := coneCoord_smul a0 (-1) (c 0) r; simpa using this
    rcases (by fin_cases k <;> simp : k = 0 ∨ k = 1) with rfl | rfl <;>
    rcases (by fin_cases r <;> simp : r = 0 ∨ r = 1) with rfl | rfl
    · simp only [muCoord, Fin.cases_zero, a, Matrix.cons_val_zero]; rw [← hneg]; exact ha00
    · simp only [muCoord, Fin.cases_zero, a, Matrix.cons_val_zero]; rw [← hneg]; exact ha01
    · change 0 < coneCoord (a 1) (c 1) 0; simpa [a] using ha10
    · change 0 < coneCoord (a 1) (c 1) 1; simpa [a] using ha11
  obtain ⟨cval, hcval⟩ := exists_uVec_repr hsurj a (wVec y a)
  have hne : (Finset.univ : Finset (Fin 2 × Fin 2)).Nonempty := ⟨(0, 0), Finset.mem_univ _⟩
  let tstar : ℝ := Finset.univ.sup' hne (fun p : Fin 2 × Fin 2 => -cval p.1 p.2 / muCoord a c p.1 p.2)
  let L : Fin 2 → Fin 2 → ℝ := fun k r => cval k r + tstar * muCoord a c k r
  have hLnn : ∀ k r, 0 ≤ L k r := fun k r => by
    have hle := Finset.le_sup' (fun p : Fin 2 × Fin 2 => -cval p.1 p.2 / muCoord a c p.1 p.2)
      (Finset.mem_univ (k, r))
    have hmul := (div_le_iff₀ (hμpos k r)).mp hle
    simp only [L]; linarith
  have hLeq : ∑ k : Fin 2, ∑ r : Fin 2, L k r • uVec x a k r = wVec y a := by
    calc ∑ k : Fin 2, ∑ r : Fin 2, (cval k r + tstar * muCoord a c k r) • uVec x a k r
        = (∑ k : Fin 2, ∑ r : Fin 2, cval k r • uVec x a k r) +
          tstar • (∑ k : Fin 2, ∑ r : Fin 2, muCoord a c k r • uVec x a k r) := by
          simp only [add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
      _ = wVec y a + tstar • (-sumMap x c) := by rw [hcval, sum_muCoord_uVec]
      _ = wVec y a := by rw [hcker, neg_zero, smul_zero, add_zero]
  have hfwd := forward_avoidance hC hS a L hLnn hLeq
  have hbwd := backward_avoidance hC hS a L hLnn hLeq
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' hne
    (fun p : Fin 2 × Fin 2 => -cval p.1 p.2 / muCoord a c p.1 p.2)
  have hpzero : L p.1 p.2 = 0 := by
    simp only [L]
    have ht : tstar = -cval p.1 p.2 / muCoord a c p.1 p.2 := hp
    rw [ht, div_mul_cancel₀ _ (hμpos p.1 p.2).ne']; ring
  obtain ⟨k1, hk10, hk11⟩ := hbwd
  have hk1_eq : k1 = 0 := Fin.ext (by omega)
  subst hk1_eq
  rcases p with ⟨k, r⟩
  dsimp only at hpzero
  have h10 : (0 : Fin 1).succ = (1 : Fin 2) := rfl
  rw [h10] at hk10 hk11
  rcases (by fin_cases k <;> simp : k = 0 ∨ k = 1) with rfl | rfl <;>
  rcases (by fin_cases r <;> simp : r = 0 ∨ r = 1) with rfl | rfl
  · linarith [hfwd.1]
  · linarith [hfwd.2]
  · linarith
  · linarith

private lemma d3_n1_four_sectors
    {C : Set (Fin 2 → ℝ)} (hC : Convex ℝ C)
    {x : Fin 1 → Fin 4 → (Fin 2 → ℝ)}
    {y : Set (Fin 1 → Fin 4) → (Fin 2 → ℝ)}
    (hS : ShattersN C x y)
    {Sa Sb : Set (Fin 1 → Fin 4)} {q0 q1 q2 q3 : Fin 1 → Fin 4}
    (hp1_in_Sb : q1 ∈ Sb) (hp1_not_Sa : q1 ∉ Sa)
    (hp3_in_Sb : q3 ∈ Sb) (hp3_not_Sa : q3 ∉ Sa)
    (hp0_in_Sa : q0 ∈ Sa) (hp0_not_Sb : q0 ∉ Sb)
    (hp2_in_Sa : q2 ∈ Sa) (hp2_not_Sb : q2 ∉ Sb)
    {e1 e2 : Fin 2 → ℝ} {ρ σ α β : ℝ}
    (hρ_pos : 0 < ρ) (hσ_pos : 0 < σ)
    (hab_ne : α ≠ 0 ∨ β ≠ 0)
    (hw_eq : y Sb - y Sa = α • e1 + β • e2)
    (hd10 : gridPt x q1 - gridPt x q0 = e1 + e2)
    (hd30 : gridPt x q3 - gridPt x q0 = (-ρ) • e1 + e2)
    (hd32 : gridPt x q3 - gridPt x q2 = (-ρ) • e1 + (-σ) • e2)
    (hd12 : gridPt x q1 - gridPt x q2 = e1 + (-σ) • e2) : False := by
  have hsec1 : 0 ≤ α → -σ * α ≤ β → β ≤ α → False := by
    intro hα hlo hhi
    have hαpos : 0 < α := lt_of_le_of_ne hα fun hz => by
      have hβ0 : β = 0 := by rw [← hz] at hlo hhi; simp only [mul_zero] at hlo; linarith only [hlo, hhi]
      rcases hab_ne with h | h <;> exact h (by linarith only [hz, hβ0])
    have h1s : 0 < 1 + σ := by linarith only [hσ_pos]
    set c1 := (σ * α + β) / (1 + σ)
    set c2 := (α - β) / (1 + σ)
    have hc1 : 0 ≤ c1 := div_nonneg (by rw [neg_mul] at hlo; linarith only [hlo]) h1s.le
    have hc2 : 0 ≤ c2 := div_nonneg (by linarith only [hhi]) h1s.le
    have hcsum : c1 + c2 = α := by simp only [c1, c2]; field_simp; ring
    have hcoeff2 : c1 - c2 * σ = β := by simp only [c1, c2]; field_simp; ring
    refine forbidden_forward hC hS hp1_in_Sb hp1_not_Sa ![q0, q2]
      (fun r => by fin_cases r <;> [exact hp0_in_Sa; exact hp2_in_Sa])
      ![c1, c2] (fun r => by fin_cases r <;> assumption)
      (by simp [Fin.sum_univ_two, hcsum, hαpos]) ?_
    rw [Fin.sum_univ_two]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hd10, hd12, hw_eq]
    calc α • e1 + β • e2 = (c1 + c2) • e1 + (c1 - c2 * σ) • e2 := by rw [hcsum, hcoeff2]
      _ = c1 • (e1 + e2) + c2 • (e1 + (-σ) • e2) := by module
  have hsec2 : 0 ≤ β → -ρ * β ≤ α → α ≤ β → False := by
    intro hβ hlo hhi
    have hβpos : 0 < β := lt_of_le_of_ne hβ fun hz => by
      have hα0 : α = 0 := by rw [← hz] at hlo hhi; simp only [mul_zero] at hlo; linarith only [hlo, hhi]
      rcases hab_ne with h | h <;> exact h (by linarith only [hz, hα0])
    have h1r : 0 < 1 + ρ := by linarith only [hρ_pos]
    set c1 := (α + ρ * β) / (1 + ρ)
    set c2 := (β - α) / (1 + ρ)
    have hc1 : 0 ≤ c1 := div_nonneg (by rw [neg_mul] at hlo; linarith only [hlo]) h1r.le
    have hc2 : 0 ≤ c2 := div_nonneg (by linarith only [hhi]) h1r.le
    have hcsum : c1 + c2 = β := by simp only [c1, c2]; field_simp; ring
    have hcoeff1 : c1 - c2 * ρ = α := by simp only [c1, c2]; field_simp; ring
    refine forbidden_backward hC hS hp0_in_Sa hp0_not_Sb ![q1, q3]
      (fun r => by fin_cases r <;> [exact hp1_in_Sb; exact hp3_in_Sb])
      ![c1, c2] (fun r => by fin_cases r <;> assumption)
      (by simp [Fin.sum_univ_two, hcsum, hβpos]) ?_
    rw [Fin.sum_univ_two]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hd10, hd30, hw_eq]
    calc α • e1 + β • e2 = (c1 - c2 * ρ) • e1 + (c1 + c2) • e2 := by rw [hcsum, hcoeff1]
      _ = c1 • (e1 + e2) + c2 • ((-ρ) • e1 + e2) := by module
  have hsec3 : α ≤ 0 → σ * α ≤ ρ * β → ρ * β ≤ -α → False := by
    intro hα hlo hhi
    have hαneg : α < 0 := lt_of_le_of_ne hα fun hz => by
      have hβ0 : β = 0 := by
        rw [hz] at hlo hhi; simp only [mul_zero, neg_zero] at hlo hhi
        have hρβ : ρ * β = 0 := by linarith only [hlo, hhi]
        exact (mul_eq_zero.mp hρβ).resolve_left hρ_pos.ne'
      rcases hab_ne with h | h <;> exact h (by linarith only [hz, hβ0])
    have hden : 0 < ρ * (1 + σ) := mul_pos hρ_pos (by linarith only [hσ_pos])
    set c1 := (-σ * α + ρ * β) / (ρ * (1 + σ))
    set c2 := (-α - ρ * β) / (ρ * (1 + σ))
    have hc1 : 0 ≤ c1 := div_nonneg (by rw [neg_mul]; linarith only [hlo]) hden.le
    have hc2 : 0 ≤ c2 := div_nonneg (by linarith only [hhi]) hden.le
    have hcsum : c1 + c2 = -α / ρ := by
      have hρne := hρ_pos.ne'; have h1s : (1 + σ) ≠ 0 := by linarith only [hσ_pos]
      simp only [c1, c2]; field_simp; ring
    have hcoeff1 : -(c1 + c2) * ρ = α := by rw [hcsum]; field_simp
    have hcoeff2 : c1 - c2 * σ = β := by
      have hρne := hρ_pos.ne'; have h1s : (1 + σ) ≠ 0 := by linarith only [hσ_pos]
      simp only [c1, c2]; field_simp; ring
    refine forbidden_forward hC hS hp3_in_Sb hp3_not_Sa ![q0, q2]
      (fun r => by fin_cases r <;> [exact hp0_in_Sa; exact hp2_in_Sa])
      ![c1, c2] (fun r => by fin_cases r <;> assumption)
      (by simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hcsum]
          exact div_pos (by linarith only [hαneg]) hρ_pos) ?_
    rw [Fin.sum_univ_two]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hd30, hd32, hw_eq]
    calc α • e1 + β • e2 = (-(c1 + c2) * ρ) • e1 + (c1 - c2 * σ) • e2 := by rw [hcoeff1, hcoeff2]
      _ = c1 • ((-ρ) • e1 + e2) + c2 • ((-ρ) • e1 + (-σ) • e2) := by module
  have hsec4 : β ≤ 0 → ρ * β ≤ σ * α → σ * α ≤ -β → False := by
    intro hβ hlo hhi
    have hβneg : β < 0 := lt_of_le_of_ne hβ fun hz => by
      have hα0 : α = 0 := by
        rw [hz] at hlo hhi; simp only [mul_zero, neg_zero] at hlo hhi
        have hσα : σ * α = 0 := by linarith only [hlo, hhi]
        exact (mul_eq_zero.mp hσα).resolve_left hσ_pos.ne'
      rcases hab_ne with h | h <;> exact h (by linarith only [hz, hα0])
    have hden : 0 < σ * (1 + ρ) := mul_pos hσ_pos (by linarith only [hρ_pos])
    set c1 := (-σ * α - β) / (σ * (1 + ρ))
    set c2 := (σ * α - ρ * β) / (σ * (1 + ρ))
    have hc1 : 0 ≤ c1 := div_nonneg (by rw [neg_mul]; linarith only [hhi]) hden.le
    have hc2 : 0 ≤ c2 := div_nonneg (by linarith only [hlo]) hden.le
    have hcsum : c1 + c2 = -β / σ := by
      have hσne := hσ_pos.ne'; have h1r : (1 + ρ) ≠ 0 := by linarith only [hρ_pos]
      simp only [c1, c2]; field_simp; ring
    have hcoeff1 : c2 - c1 * ρ = α := by
      have hσne := hσ_pos.ne'; have h1r : (1 + ρ) ≠ 0 := by linarith only [hρ_pos]
      simp only [c1, c2]; field_simp; ring
    have hcoeff2 : -(c1 + c2) * σ = β := by rw [hcsum]; field_simp
    refine forbidden_backward hC hS hp2_in_Sa hp2_not_Sb ![q3, q1]
      (fun r => by fin_cases r <;> [exact hp3_in_Sb; exact hp1_in_Sb])
      ![c1, c2] (fun r => by fin_cases r <;> assumption)
      (by simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hcsum]
          exact div_pos (by linarith only [hβneg]) hσ_pos) ?_
    rw [Fin.sum_univ_two]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hd32, hd12, hw_eq]
    calc α • e1 + β • e2 = (c2 - c1 * ρ) • e1 + (-(c1 + c2) * σ) • e2 := by rw [hcoeff1, hcoeff2]
      _ = c1 • ((-ρ) • e1 + (-σ) • e2) + c2 • (e1 + (-σ) • e2) := by module
  rcases le_total 0 α with hα | hα <;> rcases le_total 0 β with hβ | hβ
  · rcases le_total β α with h | h
    · exact hsec1 hα (by rw [neg_mul]; have h1 := mul_nonneg hσ_pos.le hα; linarith only [h1, hβ]) h
    · exact hsec2 hβ (by rw [neg_mul]; have h1 := mul_nonneg hρ_pos.le hβ; linarith only [h1, hα]) h
  · rcases le_total (-σ * α) β with h | h
    · exact hsec1 hα h (by linarith only [hα, hβ])
    · exact hsec4 hβ
        (by have h1 := mul_nonpos_of_nonneg_of_nonpos hρ_pos.le hβ
            have h2 := mul_nonneg hσ_pos.le hα; linarith only [h1, h2])
        (by rw [neg_mul] at h; linarith only [h])
  · rcases le_total (-ρ * β) α with h | h
    · exact hsec2 hβ h (by linarith only [hα, hβ])
    · exact hsec3 hα
        (by have h1 := mul_nonpos_of_nonneg_of_nonpos hσ_pos.le hα
            have h2 := mul_nonneg hρ_pos.le hβ; linarith only [h1, h2])
        (by rw [neg_mul] at h; linarith only [h])
  · rcases le_total (σ * α) (ρ * β) with h | h
    · exact hsec3 hα h (by have h1 := mul_nonpos_of_nonneg_of_nonpos hρ_pos.le hβ; linarith only [h1, hα])
    · exact hsec4 hβ h (by have h1 := mul_nonpos_of_nonneg_of_nonpos hσ_pos.le hα; linarith only [h1, hβ])

private lemma no_shatters_d3_n1
    {C : Set (Fin 2 → ℝ)} (hC : Convex ℝ C)
    {x : Fin 1 → Fin 4 → (Fin 2 → ℝ)}
    {y : Set (Fin 1 → Fin 4) → (Fin 2 → ℝ)}
    (hS : ShattersN C x y) : False := by
  let p : Fin 4 → (Fin 2 → ℝ) := x 0
  let pt : Fin 4 → (Fin 1 → Fin 4) := fun i _ => i
  have hgrid : ∀ i : Fin 4, gridPt x (pt i) = p i := fun i => by simp [gridPt, pt, p]
  have hpt_inj : Function.Injective pt := fun i j h => congr_fun h 0
  have hno_conv : ∀ (i₀ : Fin 4) (u : Fin 4 → ℝ), u i₀ = 0 → (∀ i, 0 ≤ u i) →
      ∑ i, u i = 1 → ∑ i, u i • p i = p i₀ → False := by
    intro i₀ u hu0 hunn husum hucomb
    let w : (Fin 1 → Fin 4) → ℝ := fun f => u (f 0)
    have hsum_w : ∑ f : Fin 1 → Fin 4, w f = 1 := by
      have heq : ∑ f : Fin 1 → Fin 4, w f = ∑ i : Fin 4, u i :=
        Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 4)) w u (fun _ => rfl)
      rw [heq, husum]
    have hsum_pt : ∑ f : Fin 1 → Fin 4, w f • gridPt x f = gridPt x (pt i₀) := by
      have heq : ∑ f : Fin 1 → Fin 4, w f • gridPt x f = ∑ i : Fin 4, u i • p i :=
        Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 4)) _ _ fun f => by
          simp [w, gridPt, p]
      rw [heq, hucomb, hgrid]
    exact strict_convex_pos hC hS (pt i₀) w hu0 (fun f => hunn (f 0)) hsum_w hsum_pt
  -- Radon dependence in ℝ²
  let A : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
    { toFun := fun γ => ![∑ i, γ i * p i 0, ∑ i, γ i * p i 1, ∑ i, γ i]
      map_add' := fun γ₁ γ₂ => by
        funext j; fin_cases j <;> simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun t γ => by
        funext j; fin_cases j <;> simp [mul_assoc, ← Finset.mul_sum] }
  have hker_pos : 0 < Module.finrank ℝ (LinearMap.ker A) := by
    have hrk := LinearMap.finrank_range_add_finrank_ker A
    have hdom : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by simp
    have hcod : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by simp
    have hle : Module.finrank ℝ (LinearMap.range A) ≤ 3 := (Submodule.finrank_le _).trans hcod.le
    omega
  have : Nontrivial (LinearMap.ker A) := Module.finrank_pos_iff.mp hker_pos
  obtain ⟨γK, hγKne⟩ := exists_ne (0 : LinearMap.ker A)
  let γ : Fin 4 → ℝ := γK.1
  have hγ_ne : γ ≠ 0 := fun h => hγKne (Subtype.ext h)
  have hAγ : A γ = 0 := LinearMap.mem_ker.mp γK.2
  have hγ_sum : ∑ i, γ i = 0 := by
    have := congr_fun hAγ 2; simpa [A] using this
  have hγ_pt : ∑ i, γ i • p i = 0 := by
    funext c; fin_cases c
    · have := congr_fun hAγ 0; simpa [A] using this
    · have := congr_fun hAγ 1; simpa [A] using this
  let Ipos : Finset (Fin 4) := Finset.univ.filter (fun i => 0 < γ i)
  let Ineg : Finset (Fin 4) := Finset.univ.filter (fun i => γ i < 0)
  have hdisj : Disjoint Ipos Ineg := Finset.disjoint_left.mpr fun i h1 h2 => by
    have hp1 := (Finset.mem_filter.mp h1).2
    have hn1 := (Finset.mem_filter.mp h2).2
    linarith
  have hsum_split : (∑ i ∈ Ipos, γ i) = ∑ i ∈ Ineg, (-γ i) := by
    have hsplit : ∑ i : Fin 4, γ i = (∑ i ∈ Ipos, γ i) + ∑ i ∈ Ineg, γ i := by
      rw [← Finset.sum_union hdisj]
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
      simp only [Finset.mem_union, Ipos, Ineg, Finset.mem_filter, Finset.mem_univ, true_and, not_or,
        not_lt] at hi
      linarith
    rw [hγ_sum] at hsplit
    rw [Finset.sum_neg_distrib]
    linarith
  have hpt_split : (∑ i ∈ Ipos, γ i • p i) = ∑ i ∈ Ineg, (-γ i) • p i := by
    have hsplit : ∑ i : Fin 4, γ i • p i = (∑ i ∈ Ipos, γ i • p i) + ∑ i ∈ Ineg, γ i • p i := by
      rw [← Finset.sum_union hdisj]
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
      simp only [Finset.mem_union, Ipos, Ineg, Finset.mem_filter, Finset.mem_univ, true_and, not_or,
        not_lt] at hi
      have h0 : γ i = 0 := by linarith
      simp [h0]
    rw [hγ_pt] at hsplit
    have hneg : ∑ i ∈ Ineg, (-γ i) • p i = -(∑ i ∈ Ineg, γ i • p i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => by rw [neg_smul]
    rw [hneg]
    exact eq_neg_of_add_eq_zero_left hsplit.symm
  have hIpos_ne : Ipos.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hall_le : ∀ i, γ i ≤ 0 := fun i => by
      by_contra hgt; push Not at hgt
      have : i ∈ Ipos := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hgt⟩
      rw [hemp] at this; exact Finset.notMem_empty i this
    have hall0 : ∀ i, γ i = 0 := fun i => by
      have hneg_sum : ∑ j : Fin 4, (-γ j) = 0 := by rw [Finset.sum_neg_distrib, hγ_sum, neg_zero]
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => neg_nonneg.mpr (hall_le j)).mp
        hneg_sum i (Finset.mem_univ i)
      linarith
    exact hγ_ne (funext hall0)
  set S := ∑ i ∈ Ipos, γ i
  have hSpos : 0 < S := Finset.sum_pos (fun i hi => (Finset.mem_filter.mp hi).2) hIpos_ne
  have hIneg_ne : Ineg.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sum_empty] at hsum_split
    linarith
  have hIpos_ne1 : Ipos.card ≠ 1 := by
    intro h1
    obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp h1
    have hγi₀ : γ i₀ = S := by simp only [S, hi₀, Finset.sum_singleton]
    have hi₀_not : i₀ ∉ Ineg := fun h => by
      have := (Finset.mem_filter.mp h).2; linarith
    let u : Fin 4 → ℝ := fun i => if i ∈ Ineg then (-γ i) / S else 0
    refine hno_conv i₀ u (by simp [u, hi₀_not]) (fun i => ?_) ?_ ?_
    · by_cases hi : i ∈ Ineg
      · simp only [u, hi, ↓reduceIte]
        have := (Finset.mem_filter.mp hi).2; exact div_nonneg (by linarith) hSpos.le
      · simp [u, hi]
    · have : ∑ i : Fin 4, u i = ∑ i ∈ Ineg, (-γ i) / S := by
        simp only [u, Finset.sum_ite_mem, Finset.univ_inter]
      rw [this, ← Finset.sum_div, ← hsum_split, div_self hSpos.ne']
    · have : ∑ i : Fin 4, u i • p i = ∑ i ∈ Ineg, ((-γ i) / S) • p i := by
        have hsub : ∑ i : Fin 4, u i • p i = ∑ i ∈ Ineg, u i • p i := by
          symm; refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by simp [u, hi]
        rw [hsub]; refine Finset.sum_congr rfl fun i hi => by simp [u, hi]
      rw [this]
      have hcomb : ∑ i ∈ Ineg, ((-γ i) / S) • p i = S⁻¹ • ∑ i ∈ Ineg, (-γ i) • p i := by
        rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun i _ => by rw [div_eq_inv_mul, smul_smul]
      rw [hcomb, ← hpt_split, hi₀, Finset.sum_singleton, hγi₀, smul_smul, inv_mul_cancel₀ hSpos.ne', one_smul]
  have hIneg_ne1 : Ineg.card ≠ 1 := by
    intro h1
    obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp h1
    have hγi₀ : -γ i₀ = S := by
      have := hsum_split; rw [hi₀, Finset.sum_singleton] at this; exact this.symm
    have hi₀_not : i₀ ∉ Ipos := fun h => by
      have := (Finset.mem_filter.mp h).2; linarith
    let u : Fin 4 → ℝ := fun i => if i ∈ Ipos then γ i / S else 0
    refine hno_conv i₀ u (by simp [u, hi₀_not]) (fun i => ?_) ?_ ?_
    · by_cases hi : i ∈ Ipos
      · simp only [u, hi, ↓reduceIte]
        have := (Finset.mem_filter.mp hi).2; exact div_nonneg this.le hSpos.le
      · simp [u, hi]
    · have : ∑ i : Fin 4, u i = ∑ i ∈ Ipos, γ i / S := by
        simp only [u, Finset.sum_ite_mem, Finset.univ_inter]
      rw [this, ← Finset.sum_div, div_self hSpos.ne']
    · have : ∑ i : Fin 4, u i • p i = ∑ i ∈ Ipos, (γ i / S) • p i := by
        have hsub : ∑ i : Fin 4, u i • p i = ∑ i ∈ Ipos, u i • p i := by
          symm; refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by simp [u, hi]
        rw [hsub]; refine Finset.sum_congr rfl fun i hi => by simp [u, hi]
      rw [this]
      have hcomb : ∑ i ∈ Ipos, (γ i / S) • p i = S⁻¹ • ∑ i ∈ Ipos, γ i • p i := by
        rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun i _ => by rw [div_eq_inv_mul, smul_smul]
      rw [hcomb, hpt_split, hi₀, Finset.sum_singleton, hγi₀, smul_smul, inv_mul_cancel₀ hSpos.ne', one_smul]
  have hcard_le : Ipos.card + Ineg.card ≤ 4 := by
    have := Finset.card_le_univ (Ipos ∪ Ineg)
    rw [Finset.card_union_of_disjoint hdisj, Fintype.card_fin] at this
    exact this
  have hpos_ge1 : 1 ≤ Ipos.card := Finset.Nonempty.card_pos hIpos_ne
  have hneg_ge1 : 1 ≤ Ineg.card := Finset.Nonempty.card_pos hIneg_ne
  have hIpos_card : Ipos.card = 2 := by omega
  have hIneg_card : Ineg.card = 2 := by omega
  obtain ⟨i0, i2, hi02, hIpos_eq⟩ := Finset.card_eq_two.mp hIpos_card
  obtain ⟨i1, i3, hi13, hIneg_eq⟩ := Finset.card_eq_two.mp hIneg_card
  have hi0_pos : i0 ∈ Ipos := by rw [hIpos_eq]; simp
  have hi2_pos : i2 ∈ Ipos := by rw [hIpos_eq]; simp
  have hi1_neg : i1 ∈ Ineg := by rw [hIneg_eq]; simp
  have hi3_neg : i3 ∈ Ineg := by rw [hIneg_eq]; simp
  have hne01 : i0 ≠ i1 := fun h => Finset.disjoint_left.mp hdisj hi0_pos (h ▸ hi1_neg)
  have hne03 : i0 ≠ i3 := fun h => Finset.disjoint_left.mp hdisj hi0_pos (h ▸ hi3_neg)
  have hne21 : i2 ≠ i1 := fun h => Finset.disjoint_left.mp hdisj hi2_pos (h ▸ hi1_neg)
  have hne23 : i2 ≠ i3 := fun h => Finset.disjoint_left.mp hdisj hi2_pos (h ▸ hi3_neg)
  have hγ0_pos : 0 < γ i0 := (Finset.mem_filter.mp (by rw [hIpos_eq]; simp : i0 ∈ Ipos)).2
  have hγ2_pos : 0 < γ i2 := (Finset.mem_filter.mp (by rw [hIpos_eq]; simp : i2 ∈ Ipos)).2
  have hγ1_neg : γ i1 < 0 := (Finset.mem_filter.mp (by rw [hIneg_eq]; simp : i1 ∈ Ineg)).2
  have hγ3_neg : γ i3 < 0 := (Finset.mem_filter.mp (by rw [hIneg_eq]; simp : i3 ∈ Ineg)).2
  have hS_pos_eq : S = γ i0 + γ i2 := by simp only [S, hIpos_eq, Finset.sum_pair hi02]
  have hS_neg_eq : S = -γ i1 + -γ i3 := by
    have := hsum_split; rw [hIneg_eq, Finset.sum_pair hi13] at this; exact this
  set θ := γ i2 / S
  set φ := (-γ i3) / S
  have hθ0 : 0 < θ := div_pos hγ2_pos hSpos
  have hθ1 : θ < 1 := (div_lt_one hSpos).mpr (by linarith)
  have hφ0 : 0 < φ := div_pos (by linarith) hSpos
  have hφ1 : φ < 1 := (div_lt_one hSpos).mpr (by linarith)
  have h1mθ : 1 - θ = γ i0 / S := by
    have hSne := hSpos.ne'; simp only [θ]; rw [hS_pos_eq] at hSne ⊢; field_simp; ring
  have h1mφ : 1 - φ = (-γ i1) / S := by
    have hSne := hSpos.ne'; simp only [φ]; rw [hS_neg_eq] at hSne ⊢; field_simp; ring
  set xstar := (1 - θ) • p i0 + θ • p i2
  have hxstar_eq : xstar = (1 - φ) • p i1 + φ • p i3 := by
    have h1 := congr_arg (fun v : Fin 2 → ℝ => S⁻¹ • v) hpt_split
    rw [hIpos_eq, hIneg_eq, Finset.sum_pair hi02, Finset.sum_pair hi13,
      smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul] at h1
    simp only [xstar]
    rw [h1mθ, h1mφ]
    simp only [θ, φ, div_eq_inv_mul]
    exact h1
  set e1 := p i1 - xstar
  set e2 := xstar - p i0
  set ρ := (1 - φ) / φ
  set σ := (1 - θ) / θ
  have hρ_pos : 0 < ρ := div_pos (by linarith) hφ0
  have hσ_pos : 0 < σ := div_pos (by linarith) hθ0
  have hp3_eq : p i3 - xstar = (-ρ) • e1 := by
    apply smul_right_injective (Fin 2 → ℝ) hφ0.ne'
    dsimp only
    have hrel : (1 - φ) • (p i1 - xstar) + φ • (p i3 - xstar) = 0 := by
      have h : (1 - φ) • p i1 + φ • p i3 - xstar = 0 := sub_eq_zero.mpr hxstar_eq.symm
      rw [← h]; module
    have hmul : φ * (-ρ) = -(1 - φ) := by simp only [ρ]; field_simp
    rw [smul_smul, hmul]
    have h2 : φ • (p i3 - xstar) = -(1 - φ) • e1 := by
      have h3 : φ • (p i3 - xstar) = -((1 - φ) • e1) := eq_neg_of_add_eq_zero_right hrel
      rw [← neg_smul] at h3
      exact h3
    exact h2
  have hp2_eq : xstar - p i2 = (-σ) • e2 := by
    apply smul_right_injective (Fin 2 → ℝ) hθ0.ne'
    dsimp only
    have hrel : (1 - θ) • (p i0 - xstar) + θ • (p i2 - xstar) = 0 := by
      have h : (1 - θ) • p i0 + θ • p i2 - xstar = 0 := sub_eq_zero.mpr rfl
      rw [← h]; module
    have hmul : θ * (-σ) = -(1 - θ) := by simp only [σ]; field_simp
    rw [smul_smul, hmul]
    have h2 : θ • (xstar - p i2) = (1 - θ) • (p i0 - xstar) := by
      have : θ • (p i2 - xstar) = -((1 - θ) • (p i0 - xstar)) := eq_neg_of_add_eq_zero_right hrel
      calc θ • (xstar - p i2) = -(θ • (p i2 - xstar)) := by module
        _ = (1 - θ) • (p i0 - xstar) := by rw [this, neg_neg]
    calc θ • (xstar - p i2) = (1 - θ) • (p i0 - xstar) := h2
      _ = (-(1 - θ)) • e2 := by simp only [e2]; module
  -- Helper: no three distinct points with one a convex combination of the other two
  have hno_seg : ∀ (j j1 j2 : Fin 4) (t1 t2 : ℝ), j ≠ j1 → j ≠ j2 → j1 ≠ j2 →
      0 ≤ t1 → 0 ≤ t2 → t1 + t2 = 1 → t1 • p j1 + t2 • p j2 = p j → False := by
    intro j j1 j2 t1 t2 hj1 hj2 h12 ht1 ht2 hsum hcomb
    let u : Fin 4 → ℝ := fun i => if i = j1 then t1 else if i = j2 then t2 else 0
    refine hno_conv j u (by simp [u, hj1, hj2]) (fun i => by simp only [u]; split_ifs <;> linarith) ?_ ?_
    · have hsub : ∑ i : Fin 4, u i = ∑ i ∈ ({j1, j2} : Finset (Fin 4)), u i := by
        symm; refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
        simp [u, hi.1, hi.2]
      rw [hsub, Finset.sum_pair h12]; simp [u, h12.symm, hsum]
    · have hsub : ∑ i : Fin 4, u i • p i = ∑ i ∈ ({j1, j2} : Finset (Fin 4)), u i • p i := by
        symm; refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
        simp [u, hi.1, hi.2]
      rw [hsub, Finset.sum_pair h12]; simp [u, h12.symm, hcomb]
  -- Show {e1, e2} is linearly independent
  have hlin_indep : ∀ c1 c2 : ℝ, c1 • e1 + c2 • e2 = 0 → c1 = 0 ∧ c2 = 0 := by
    intro c1 c2 hrel
    by_contra hne
    have hnot0 : c1 ≠ 0 ∨ c2 ≠ 0 := by tauto
    by_cases hc1 : c1 = 0
    · have hc2 : c2 ≠ 0 := hnot0.resolve_left (not_not.mpr hc1)
      rw [hc1, zero_smul, zero_add] at hrel
      have he2 : e2 = 0 := (smul_eq_zero.mp hrel).resolve_left hc2
      have hp0_eq : p i0 = (1 - φ) • p i1 + φ • p i3 := by
        have : p i0 = xstar := (sub_eq_zero.mp he2).symm
        rw [this, hxstar_eq]
      exact hno_seg i0 i1 i3 (1 - φ) φ hne01 hne03 hi13 (by linarith) hφ0.le (by ring) hp0_eq.symm
    · by_cases hc2 : c2 = 0
      · rw [hc2, zero_smul, add_zero] at hrel
        have he1 : e1 = 0 := (smul_eq_zero.mp hrel).resolve_left hc1
        have hp1_eq : p i1 = (1 - θ) • p i0 + θ • p i2 := sub_eq_zero.mp he1
        exact hno_seg i1 i0 i2 (1 - θ) θ hne01.symm hne21.symm hi02 (by linarith) hθ0.le (by ring) hp1_eq.symm
      · set t := -c2 / c1
        have ht_ne : t ≠ 0 := div_ne_zero (neg_ne_zero.mpr hc2) hc1
        have he1_eq : e1 = t • e2 := by
          apply smul_right_injective (Fin 2 → ℝ) hc1
          dsimp only
          have hmul : c1 * t = -c2 := mul_div_cancel₀ (-c2) hc1
          rw [smul_smul, hmul]
          have : c1 • e1 = -(c2 • e2) := eq_neg_of_add_eq_zero_left hrel
          simpa [neg_smul] using this
        have hpi0 : p i0 = xstar + (-1 : ℝ) • e2 := by simp only [e2]; module
        have hpi2 : p i2 = xstar + σ • e2 := by
          have : p i2 = xstar - (-σ) • e2 := by rw [← hp2_eq]; abel
          rw [this]; module
        have hpi1 : p i1 = xstar + t • e2 := by
          have : p i1 = xstar + e1 := by simp only [e1]; abel
          rw [this, he1_eq]
        have hpi3 : p i3 = xstar + (-ρ * t) • e2 := by
          have : p i3 = xstar + (-ρ) • e1 := by rw [← hp3_eq]; abel
          rw [this, he1_eq, smul_smul]
        have hpos_j : ∃ j : Fin 4, ∃ s : ℝ, j ≠ i0 ∧ j ≠ i2 ∧ 0 < s ∧ p j = xstar + s • e2 := by
          rcases lt_or_gt_of_ne ht_ne with htlt | htgt
          · exact ⟨i3, -ρ * t, hne03.symm, hne23.symm, by nlinarith, hpi3⟩
          · exact ⟨i1, t, hne01.symm, hne21.symm, htgt, hpi1⟩
        obtain ⟨j, s, hj0, hj2, hspos, hpj⟩ := hpos_j
        by_cases hle : s ≤ σ
        · have hden : 0 < 1 + σ := by linarith
          refine hno_seg j i0 i2 ((σ - s) / (1 + σ)) ((1 + s) / (1 + σ)) hj0 hj2 hi02
            (div_nonneg (by linarith) hden.le) (div_nonneg (by linarith) hden.le)
            (by field_simp; ring) ?_
          rw [hpi0, hpi2, hpj]
          have h1 : (σ - s) / (1 + σ) + (1 + s) / (1 + σ) = 1 := by field_simp; ring
          have h2 : (σ - s) / (1 + σ) * (-1) + (1 + s) / (1 + σ) * σ = s := by field_simp; ring
          calc ((σ - s) / (1 + σ)) • (xstar + (-1 : ℝ) • e2) + ((1 + s) / (1 + σ)) • (xstar + σ • e2)
              = (((σ - s) / (1 + σ)) + ((1 + s) / (1 + σ))) • xstar +
                (((σ - s) / (1 + σ)) * (-1) + ((1 + s) / (1 + σ)) * σ) • e2 := by module
            _ = xstar + s • e2 := by rw [h1, h2, one_smul]
        · push Not at hle
          have hden : 0 < 1 + s := by linarith
          refine hno_seg i2 i0 j ((s - σ) / (1 + s)) ((1 + σ) / (1 + s)) hi02.symm hj2.symm hj0.symm
            (div_nonneg (by linarith) hden.le) (div_nonneg (by linarith) hden.le)
            (by field_simp; ring) ?_
          rw [hpi0, hpj, hpi2]
          have h1 : (s - σ) / (1 + s) + (1 + σ) / (1 + s) = 1 := by field_simp; ring
          have h2 : (s - σ) / (1 + s) * (-1) + (1 + σ) / (1 + s) * s = σ := by field_simp; ring
          calc ((s - σ) / (1 + s)) • (xstar + (-1 : ℝ) • e2) + ((1 + σ) / (1 + s)) • (xstar + s • e2)
              = (((s - σ) / (1 + s)) + ((1 + σ) / (1 + s))) • xstar +
                (((s - σ) / (1 + s)) * (-1) + ((1 + σ) / (1 + s)) * s) • e2 := by module
            _ = xstar + σ • e2 := by rw [h1, h2, one_smul]
  -- Basis representation of w := y Sb - y Sa
  let B : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
    { toFun := fun v => v 0 • e1 + v 1 • e2
      map_add' := fun v₁ v₂ => by simp only [Pi.add_apply]; module
      map_smul' := fun t v => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; module }
  have hB_inj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨h0, h1⟩ := hlin_indep (v 0) (v 1) hv
    funext c; fin_cases c <;> assumption
  have hB_surj : Function.Surjective B := LinearMap.injective_iff_surjective.mp hB_inj
  let Sa : Set (Fin 1 → Fin 4) := {pt i0, pt i2}
  let Sb : Set (Fin 1 → Fin 4) := {pt i1, pt i3}
  have hp1_in_Sb : pt i1 ∈ Sb := Or.inl rfl
  have hp1_not_Sa : pt i1 ∉ Sa := by
    rintro (h | h)
    · exact hne01 (hpt_inj h).symm
    · exact hne21 (hpt_inj h).symm
  have hp3_in_Sb : pt i3 ∈ Sb := Or.inr rfl
  have hp3_not_Sa : pt i3 ∉ Sa := by
    rintro (h | h)
    · exact hne03 (hpt_inj h).symm
    · exact hne23 (hpt_inj h).symm
  have hp0_in_Sa : pt i0 ∈ Sa := Or.inl rfl
  have hp0_not_Sb : pt i0 ∉ Sb := by
    rintro (h | h)
    · exact hne01 (hpt_inj h)
    · exact hne03 (hpt_inj h)
  have hp2_in_Sa : pt i2 ∈ Sa := Or.inr rfl
  have hp2_not_Sb : pt i2 ∉ Sb := by
    rintro (h | h)
    · exact hne21 (hpt_inj h)
    · exact hne23 (hpt_inj h)
  have hw_ne : y Sb - y Sa ≠ 0 := y_sub_ne_zero hS hp1_in_Sb hp1_not_Sa
  obtain ⟨ab, hab⟩ := hB_surj (y Sb - y Sa)
  set α := ab 0
  set β := ab 1
  have hw_eq : y Sb - y Sa = α • e1 + β • e2 := hab.symm
  have hab_ne : α ≠ 0 ∨ β ≠ 0 := by
    by_contra h0; push Not at h0
    rw [h0.1, h0.2, zero_smul, zero_smul, add_zero] at hw_eq
    exact hw_ne hw_eq
  -- 4 difference vectors
  have hd10 : gridPt x (pt i1) - gridPt x (pt i0) = e1 + e2 := by
    rw [hgrid, hgrid]; simp only [e1, e2]; abel
  have hd30 : gridPt x (pt i3) - gridPt x (pt i0) = (-ρ) • e1 + e2 := by
    rw [hgrid, hgrid]
    calc p i3 - p i0 = (p i3 - xstar) + (xstar - p i0) := by abel
      _ = (-ρ) • e1 + e2 := by rw [hp3_eq]
  have hd32 : gridPt x (pt i3) - gridPt x (pt i2) = (-ρ) • e1 + (-σ) • e2 := by
    rw [hgrid, hgrid]
    calc p i3 - p i2 = (p i3 - xstar) + (xstar - p i2) := by abel
      _ = (-ρ) • e1 + (-σ) • e2 := by rw [hp3_eq, hp2_eq]
  have hd12 : gridPt x (pt i1) - gridPt x (pt i2) = e1 + (-σ) • e2 := by
    rw [hgrid, hgrid]
    calc p i1 - p i2 = (p i1 - xstar) + (xstar - p i2) := by abel
      _ = e1 + (-σ) • e2 := by rw [hp2_eq]
  exact d3_n1_four_sectors hC hS hp1_in_Sb hp1_not_Sa hp3_in_Sb hp3_not_Sa
    hp0_in_Sa hp0_not_Sb hp2_in_Sa hp2_not_Sb hρ_pos hσ_pos hab_ne hw_eq hd10 hd30 hd32 hd12

theorem hasAddVCNDimAtMost_three_of_convex_rn_add_one (n : ℕ) (hn : n ≠ 0)
    {C : Set (Fin (n + 1) → ℝ)} (hC : Convex ℝ C) : HasAddVCNDimAtMost C n 3 := by
  match n with
  | 0 => exact absurd rfl hn
  | 1 => exact fun x y hxy => no_shatters_d3_n1 hC hxy
  | 2 => exact HasAddVCNDimAtMost.mono (by omega : 2 ≤ 3) (fun x y hxy => no_shatters_d2_n2 hC hxy)
  | m + 3 => exact HasAddVCNDimAtMost.mono (by omega : 2 ≤ 3) (fun x y hxy => no_shatters_d2_ge3 hC hxy)

end BaseCasesAndMain

end

end VCDimAllNProof

theorem OMA.solution :
    type_of% @VCDimConvex.exists_exponential_bound_hasAddVCNDimAtMost_n_of_convex_rn_add_one := by
  refine ⟨3, by omega, fun n hn C hC => ?_⟩
  have h3 : HasAddVCNDimAtMost C n 3 :=
    VCDimAllNProof.hasAddVCNDimAtMost_three_of_convex_rn_add_one n (by omega) hC
  exact HasAddVCNDimAtMost.mono (by simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 3) hn) h3
