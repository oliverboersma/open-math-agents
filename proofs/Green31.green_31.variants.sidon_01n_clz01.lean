import FormalConjectures.GreensOpenProblems.«31»

/-!
# Binary Sidon sets in `{0, 1}^n`: Cohen--Litsyn--Zemor (2001) upper bound

Formalization of `Green31.green_31.variants.sidon_01n_clz01`, proving that any binary Sidon
subset `S` of `F_2^n` satisfies `|S| <= C * (2^n)^0.5753`, via slice counting, the
Johnson scheme Bose--Mesner algebra, Hadamard product positive semidefiniteness, and
binomial entropy bounds.
-/

namespace OMA

open Finset

section BinarySidonCounting

variable {n : ℕ}

/-- The support of a vector in `𝔽₂ n` as a `Finset (Fin n)`. -/
def f2Supp (a : 𝔽₂ n) : Finset (Fin n) :=
  Finset.univ.filter fun i => a i ≠ 0

lemma mem_f2Supp {a : 𝔽₂ n} {i : Fin n} : i ∈ f2Supp a ↔ a i ≠ 0 := by
  simp [f2Supp]

lemma zmod2_cases (u : ZMod 2) : u = 0 ∨ u = 1 := by
  fin_cases u <;> [exact Or.inl rfl; exact Or.inr rfl]

lemma zmod2_add_self (u : ZMod 2) : u + u = 0 := by
  rcases zmod2_cases u with rfl | rfl <;> decide

lemma zmod2_eq_of_add_eq_zero {u v : ZMod 2} (h : u + v = 0) : u = v := by
  rcases zmod2_cases u with rfl | rfl <;> rcases zmod2_cases v with rfl | rfl <;>
    simp_all

lemma zmod2_add_one_val (u : ZMod 2) : (u + 1).val = 1 - u.val := by
  rcases zmod2_cases u with rfl | rfl <;> decide

lemma f2_add_cancel_right (a b x : 𝔽₂ n) : (a + x) + (b + x) = a + b := by
  ext i
  calc (a + x) i + (b + x) i = (a i + b i) + (x i + x i) := by simp [Pi.add_apply]; ring
    _ = a i + b i := by rw [zmod2_add_self, add_zero]

lemma f2Supp_inj : Function.Injective (f2Supp (n := n)) := by
  intro a b hab
  ext i
  have hmem : i ∈ f2Supp a ↔ i ∈ f2Supp b := by rw [hab]
  simp only [mem_f2Supp, ne_eq] at hmem
  rcases zmod2_cases (a i) with ha | ha <;> rcases zmod2_cases (b i) with hb | hb <;>
    simp_all

lemma f2Supp_surj (A : Finset (Fin n)) :
    ∃ a : 𝔽₂ n, f2Supp a = A := by
  refine ⟨fun i => if i ∈ A then 1 else 0, ?_⟩
  ext i
  simp [mem_f2Supp]

noncomputable def f2EquivFinset : 𝔽₂ n ≃ Finset (Fin n) :=
  Equiv.ofBijective f2Supp ⟨f2Supp_inj, f2Supp_surj⟩

lemma f2Supp_add (a b : 𝔽₂ n) : f2Supp (a + b) = symmDiff (f2Supp a) (f2Supp b) := by
  ext i
  simp only [mem_f2Supp, Pi.add_apply, Finset.mem_symmDiff, ne_eq]
  rcases zmod2_cases (a i) with ha | ha <;> rcases zmod2_cases (b i) with hb | hb <;>
    (simp [ha, hb]; try decide)

lemma isBinarySidon_translate {S : Finset (𝔽₂ n)}
    (hS : Green31.IsBinarySidon (S : Set (𝔽₂ n))) (x : 𝔽₂ n) :
    Green31.IsBinarySidon ((S.image (· + x) : Finset (𝔽₂ n)) : Set (𝔽₂ n)) := by
  intro a' b' c' d' ha' hb' hc' hd' hsum
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha' hb' hc' hd'
  obtain ⟨a, ha, rfl⟩ := ha'
  obtain ⟨b, hb, rfl⟩ := hb'
  obtain ⟨c, hc, rfl⟩ := hc'
  obtain ⟨d, hd, rfl⟩ := hd'
  have hsum' : (fun i => (a i).val + (b i).val) = (fun i => (c i).val + (d i).val) := by
    ext i
    have hi := congr_fun hsum i
    simp only [Pi.add_apply] at hi
    rcases zmod2_cases (x i) with hx | hx
    · simpa [hx] using hi
    · rw [hx, zmod2_add_one_val, zmod2_add_one_val, zmod2_add_one_val, zmod2_add_one_val] at hi
      have ha1 : (a i).val ≤ 1 := Nat.lt_succ_iff.mp (ZMod.val_lt (a i))
      have hb1 : (b i).val ≤ 1 := Nat.lt_succ_iff.mp (ZMod.val_lt (b i))
      have hc1 : (c i).val ≤ 1 := Nat.lt_succ_iff.mp (ZMod.val_lt (c i))
      have hd1 : (d i).val ≤ 1 := Nat.lt_succ_iff.mp (ZMod.val_lt (d i))
      omega
  rcases hS ha hb hc hd hsum' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- For any nonzero `Δ : 𝔽₂ n`, the number of ordered pairs `(a, b) ∈ S ×ˢ S` with `a + b = Δ`
is at most `2 ^ (f2Supp Δ).card`. -/
lemma sidon_pair_count_le (S : Finset (𝔽₂ n))
    (hS : Green31.IsBinarySidon (S : Set (𝔽₂ n)))
    {Δ : 𝔽₂ n} (hΔ : Δ ≠ 0) :
    ((S ×ˢ S).filter fun p => p.1 + p.2 = Δ).card ≤ 2 ^ (f2Supp Δ).card := by
  let F := (S ×ˢ S).filter fun p => p.1 + p.2 = Δ
  let proj : 𝔽₂ n × 𝔽₂ n → (↥(f2Supp Δ) → ZMod 2) := fun p i => p.1 i.1
  have hinj : Set.InjOn proj (F : Set (𝔽₂ n × 𝔽₂ n)) := by
    rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    simp only [Finset.mem_coe, F, Finset.mem_filter, Finset.mem_product] at h₁ h₂
    rcases h₁ with ⟨⟨ha₁, hb₁⟩, hsum₁⟩
    rcases h₂ with ⟨⟨ha₂, hb₂⟩, hsum₂⟩
    have ha_eq : ∀ i ∈ f2Supp Δ, a₁ i = a₂ i := fun i hi =>
      congr_fun heq ⟨i, hi⟩
    have hcoord : (fun i => (a₁ i).val + (b₂ i).val) =
        (fun i => (a₂ i).val + (b₁ i).val) := by
      ext i
      by_cases hi : i ∈ f2Supp Δ
      · have h1 := ha_eq i hi
        have hsum_i1 : a₁ i + b₁ i = Δ i := congr_fun hsum₁ i
        have hsum_i2 : a₂ i + b₂ i = Δ i := congr_fun hsum₂ i
        rw [h1] at hsum_i1
        have hb_eq : b₁ i = b₂ i := add_left_cancel (hsum_i1.trans hsum_i2.symm)
        rw [h1, hb_eq]
      · rw [mem_f2Supp, not_not] at hi
        have hsum_i1 : a₁ i + b₁ i = 0 := by simpa [hi] using congr_fun hsum₁ i
        have hsum_i2 : a₂ i + b₂ i = 0 := by simpa [hi] using congr_fun hsum₂ i
        have hb1 : b₁ i = a₁ i := (zmod2_eq_of_add_eq_zero hsum_i1).symm
        have hb2 : b₂ i = a₂ i := (zmod2_eq_of_add_eq_zero hsum_i2).symm
        rw [hb1, hb2, add_comm]
    rcases hS ha₁ hb₂ ha₂ hb₁ hcoord with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exfalso
      apply hΔ
      rw [← hsum₁]
      ext i
      exact zmod2_add_self (a₁ i)
  have hcard : F.card ≤ (Finset.univ : Finset (↥(f2Supp Δ) → ZMod 2)).card :=
    Finset.card_le_card_of_injOn proj (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
  simpa [Fintype.card_fun, ZMod.card, Fintype.card_coe] using hcard

lemma sidon_dist_count_le (S : Finset (𝔽₂ n))
    (hS : Green31.IsBinarySidon (S : Set (𝔽₂ n))) {d : ℕ} (hd : 1 ≤ d) :
    ((S ×ˢ S).filter fun p => (f2Supp (p.1 + p.2)).card = d).card ≤
      Nat.choose n d * 2 ^ d := by
  let Ds : Finset (𝔽₂ n) := Finset.univ.filter fun Δ => (f2Supp Δ).card = d
  have hsub : ((S ×ˢ S).filter fun p => (f2Supp (p.1 + p.2)).card = d) =
      Ds.biUnion (fun Δ => (S ×ˢ S).filter fun p => p.1 + p.2 = Δ) := by
    ext ⟨a, b⟩
    simp only [Ds, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨hab, hd'⟩
      exact ⟨a + b, hd', hab, rfl⟩
    · rintro ⟨Δ, hΔ, hab, rfl⟩
      exact ⟨hab, hΔ⟩
  rw [hsub, Finset.card_biUnion]
  · calc ∑ Δ ∈ Ds, ((S ×ˢ S).filter fun p => p.1 + p.2 = Δ).card
        ≤ ∑ Δ ∈ Ds, 2 ^ d := by
          refine Finset.sum_le_sum fun Δ hΔ => ?_
          have hΔ' : (f2Supp Δ).card = d := (Finset.mem_filter.mp hΔ).2
          have hne : Δ ≠ 0 := by
            intro h0
            subst h0
            simp [f2Supp] at hΔ'
            omega
          simpa [hΔ'] using sidon_pair_count_le S hS hne
      _ = Ds.card * 2 ^ d := by simp
      _ = Nat.choose n d * 2 ^ d := by
          congr 1
          have hbij : Ds = Finset.image f2EquivFinset.symm
              (Finset.powersetCard d (Finset.univ : Finset (Fin n))) := by
            ext Δ
            simp only [Ds, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
              Finset.mem_powersetCard, Finset.subset_univ]
            constructor
            · intro h
              exact ⟨f2Supp Δ, h, f2EquivFinset.symm_apply_apply Δ⟩
            · rintro ⟨A, hA, rfl⟩
              have : f2Supp (f2EquivFinset.symm A) = A := f2EquivFinset.apply_symm_apply A
              rw [this]
              exact hA
          rw [hbij, Finset.card_image_of_injective _ f2EquivFinset.symm.injective,
            Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  · intro Δ₁ _ Δ₂ _ hne
    refine Finset.disjoint_left.mpr ?_
    intro p hp₁ hp₂
    simp only [Finset.mem_filter] at hp₁ hp₂
    exact hne (hp₁.2.symm.trans hp₂.2)

/-- Fixed-weight subset type `WSub n w`. -/
abbrev WSub (n w : ℕ) := { A : Finset (Fin n) // A.card = w }

lemma card_wsub (n w : ℕ) : Fintype.card (WSub n w) = Nat.choose n w := by
  have heq : Fintype.card (WSub n w) =
      Fintype.card ↥(Finset.powersetCard w (Finset.univ : Finset (Fin n))) := by
    refine Fintype.card_congr
      { toFun := fun A => ⟨A.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, A.2⟩⟩
        invFun := fun A => ⟨A.1, (Finset.mem_powersetCard.mp A.2).2⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
  rw [heq, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- Translate `S` by `x` and restrict to weight `w`. -/
noncomputable def sliceW (S : Finset (𝔽₂ n)) (w : ℕ) (x : 𝔽₂ n) : Finset (WSub n w) :=
  Finset.univ.filter fun A => ∃ a ∈ S, f2Supp (a + x) = A.1

lemma mem_sliceW {S : Finset (𝔽₂ n)} {w : ℕ} {x : 𝔽₂ n} {A : WSub n w} :
    A ∈ sliceW S w x ↔ ∃ a ∈ S, f2Supp (a + x) = A.1 := by
  simp [sliceW]

lemma sum_card_sliceW (S : Finset (𝔽₂ n)) (w : ℕ) :
    ∑ x : 𝔽₂ n, (sliceW S w x).card = S.card * Nat.choose n w := by
  classical
  have h1 : ∀ x : 𝔽₂ n, (S.filter fun a => (f2Supp (a + x)).card = w).card =
      (sliceW S w x).card := by
    intro x
    refine Finset.card_bij (fun a ha => ⟨f2Supp (a + x), (Finset.mem_filter.mp ha).2⟩) ?_ ?_ ?_
    · intro a ha
      exact mem_sliceW.mpr ⟨a, (Finset.mem_filter.mp ha).1, rfl⟩
    · intro a₁ _ a₂ _ heq
      have h' : f2Supp (a₁ + x) = f2Supp (a₂ + x) := congr_arg Subtype.val heq
      exact add_right_cancel (f2Supp_inj h')
    · intro A hA
      obtain ⟨a, ha, hfa⟩ := mem_sliceW.mp hA
      refine ⟨a, Finset.mem_filter.mpr ⟨ha, by rw [hfa]; exact A.2⟩, ?_⟩
      ext1; exact hfa
  simp_rw [← h1, Finset.card_filter]
  rw [Finset.sum_comm]
  have hinner : ∀ a ∈ S, (∑ x : 𝔽₂ n, if (f2Supp (a + x)).card = w then 1 else 0) = Nat.choose n w := by
    intro a _
    let e : 𝔽₂ n ≃ Finset (Fin n) := (Equiv.addLeft a).trans f2EquivFinset
    have he_apply : ∀ x, e x = f2Supp (a + x) := fun x => rfl
    have hsum : (∑ x : 𝔽₂ n, if (f2Supp (a + x)).card = w then 1 else 0) =
        ∑ A : Finset (Fin n), if A.card = w then 1 else 0 :=
      Fintype.sum_equiv e _ (fun A => if A.card = w then 1 else 0) fun x => by
        rw [he_apply]
    rw [hsum, ← Finset.card_filter]
    have hfilt : (Finset.univ.filter fun A : Finset (Fin n) => A.card = w) =
        Finset.powersetCard w (Finset.univ : Finset (Fin n)) := by
      ext A; simp [Finset.mem_powersetCard]
    rw [hfilt, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  calc ∑ a ∈ S, ∑ x : 𝔽₂ n, (if (f2Supp (a + x)).card = w then 1 else 0)
      = ∑ _a ∈ S, Nat.choose n w := Finset.sum_congr rfl hinner
    _ = S.card * Nat.choose n w := by simp

lemma sum_sq_card_sliceW_ge (S : Finset (𝔽₂ n)) (w : ℕ) :
    ((S.card : ℝ) * Nat.choose n w) ^ 2 ≤
      (2 : ℝ) ^ n * ∑ x : 𝔽₂ n, ((sliceW S w x).card : ℝ) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (𝔽₂ n)))
    (f := fun x => ((sliceW S w x).card : ℝ))
  have hsum : ∑ x : 𝔽₂ n, ((sliceW S w x).card : ℝ) = (S.card : ℝ) * Nat.choose n w := by
    exact_mod_cast sum_card_sliceW S w
  have hcard : ((Finset.univ : Finset (𝔽₂ n)).card : ℝ) = (2 : ℝ) ^ n := by
    simp [ZMod.card]
  rw [hsum, hcard] at h
  exact h

/-- Number of `x : 𝔽₂ n` placing both `a + x` and `b + x` in weight `w`, when `|(f2Supp (a + b))| = 2 * j`. -/
lemma count_x_both_weight (a b : 𝔽₂ n) {w j : ℕ}
    (hd : (f2Supp (a + b)).card = 2 * j) (hj : j ≤ w) :
    ((Finset.univ : Finset (𝔽₂ n)).filter fun x =>
      (f2Supp (a + x)).card = w ∧ (f2Supp (b + x)).card = w).card =
      Nat.choose (2 * j) j * Nat.choose (n - 2 * j) (w - j) := by
  let D := f2Supp (a + b)
  let Dc := (Finset.univ : Finset (Fin n)) \ D
  have hD_card : D.card = 2 * j := hd
  have hDc_card : Dc.card = n - 2 * j := by
    simp [Dc, Finset.card_sdiff, hD_card]
  have hdisj : Disjoint D Dc := disjoint_sdiff_self_right
  have hunion : D ∪ Dc = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ _)
  let Fy : Finset (Finset (Fin n)) :=
    Finset.univ.filter fun Y => Y.card = w ∧ (symmDiff D Y).card = w
  have hcard_Fy : ((Finset.univ : Finset (𝔽₂ n)).filter fun x =>
      (f2Supp (a + x)).card = w ∧ (f2Supp (b + x)).card = w).card = Fy.card := by
    refine Finset.card_bij (fun x _ => f2Supp (a + x)) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Fy, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hx.1, ?_⟩
      have hbx : symmDiff D (f2Supp (a + x)) = f2Supp (b + x) := by
        rw [← f2Supp_add (a + b) (a + x)]
        congr 1
        rw [add_comm a b, add_comm a x]
        exact f2_add_cancel_right b x a
      rw [hbx]
      exact hx.2
    · intro x₁ _ x₂ _ heq
      exact add_left_cancel (f2Supp_inj heq)
    · intro Y hY
      simp only [Fy, Finset.mem_filter, Finset.mem_univ, true_and] at hY
      obtain ⟨y, hy⟩ := f2Supp_surj Y
      have hya : a + (y + a) = y := by
        ext i
        calc a i + (y i + a i) = y i + (a i + a i) := by ring
          _ = y i := by rw [zmod2_add_self, add_zero]
      refine ⟨y + a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · refine ⟨by rw [hya, hy]; exact hY.1, ?_⟩
        have hbx : b + (y + a) = (a + b) + y := by
          ext i
          simp only [Pi.add_apply]
          ring
        rw [hbx, f2Supp_add, hy]
        exact hY.2
      · rw [hya, hy]
  rw [hcard_Fy]
  have hbij : Fy.card = (Finset.powersetCard j D ×ˢ Finset.powersetCard (w - j) Dc).card := by
    refine Finset.card_bij (fun Y _ => (Y ∩ D, Y ∩ Dc)) ?_ ?_ ?_
    · intro Y hY
      simp only [Fy, Finset.mem_filter, Finset.mem_univ, true_and] at hY
      have hY_split : Y.card = (Y ∩ D).card + (Y ∩ Dc).card := by
        rw [← Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right hdisj))]
        congr 1
        rw [← Finset.inter_union_distrib_left, hunion, Finset.inter_univ]
      have hsym_split : (symmDiff D Y).card = (D \ Y).card + (Y ∩ Dc).card := by
        have hsd : symmDiff D Y = (D \ Y) ∪ (Y ∩ Dc) := by
          ext i
          simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, Dc,
            Finset.mem_univ, true_and]
        rw [hsd, Finset.card_union_of_disjoint]
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hi2).2).2 (Finset.mem_sdiff.mp hi1).1
      have hD_split : (D \ Y).card + (Y ∩ D).card = 2 * j := by
        rw [← hD_card, ← Finset.card_sdiff_add_card_inter D Y, Finset.inter_comm]
      have h1 : (Y ∩ D).card = j := by omega
      have h2 : (Y ∩ Dc).card = w - j := by omega
      simp only [Finset.mem_product, Finset.mem_powersetCard]
      exact ⟨⟨Finset.inter_subset_right, h1⟩, ⟨Finset.inter_subset_right, h2⟩⟩
    · intro Y₁ _ Y₂ _ heq
      have h1 : Y₁ ∩ D = Y₂ ∩ D := congr_arg Prod.fst heq
      have h2 : Y₁ ∩ Dc = Y₂ ∩ Dc := congr_arg Prod.snd heq
      calc Y₁ = Y₁ ∩ (D ∪ Dc) := by rw [hunion, Finset.inter_univ]
        _ = (Y₁ ∩ D) ∪ (Y₁ ∩ Dc) := Finset.inter_union_distrib_left Y₁ D Dc
        _ = (Y₂ ∩ D) ∪ (Y₂ ∩ Dc) := by rw [h1, h2]
        _ = Y₂ ∩ (D ∪ Dc) := (Finset.inter_union_distrib_left Y₂ D Dc).symm
        _ = Y₂ := by rw [hunion, Finset.inter_univ]
    · rintro ⟨U, V⟩ hUV
      simp only [Finset.mem_product, Finset.mem_powersetCard] at hUV
      rcases hUV with ⟨⟨hUD, hUcard⟩, ⟨hVDc, hVcard⟩⟩
      have hUVdisj : Disjoint U V :=
        Finset.disjoint_of_subset_left hUD (Finset.disjoint_of_subset_right hVDc hdisj)
      refine ⟨U ∪ V, ?_, ?_⟩
      · simp only [Fy, Finset.mem_filter, Finset.mem_univ, true_and]
        have hcardUV : (U ∪ V).card = w := by
          rw [Finset.card_union_of_disjoint hUVdisj, hUcard, hVcard]
          omega
        refine ⟨hcardUV, ?_⟩
        have hsd : symmDiff D (U ∪ V) = (D \ U) ∪ V := by
          ext i
          simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
          have hiU : i ∈ U → i ∈ D := fun h => hUD h
          have hiV : i ∈ V → i ∉ D := fun h => (Finset.mem_sdiff.mp (hVDc h)).2
          tauto
        rw [hsd, Finset.card_union_of_disjoint]
        · rw [Finset.card_sdiff_of_subset hUD, hD_card, hUcard, hVcard]
          omega
        · exact Finset.disjoint_of_subset_left Finset.sdiff_subset
            (Finset.disjoint_of_subset_right hVDc hdisj)
      · ext1
        · ext i
          simp only [Finset.mem_inter, Finset.mem_union]
          constructor
          · rintro ⟨hiU | hiV, hiD⟩
            · exact hiU
            · exact False.elim ((Finset.mem_sdiff.mp (hVDc hiV)).2 hiD)
          · intro hiU
            exact ⟨Or.inl hiU, hUD hiU⟩
        · ext i
          simp only [Finset.mem_inter, Finset.mem_union]
          constructor
          · rintro ⟨hiU | hiV, hiDc⟩
            · exact False.elim ((Finset.mem_sdiff.mp hiDc).2 (hUD hiU))
            · exact hiV
          · intro hiV
            exact ⟨Or.inr hiV, hVDc hiV⟩
  rw [hbij, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
    hD_card, hDc_card]

lemma pair_both_weight_sum (S : Finset (𝔽₂ n))
    (hS : Green31.IsBinarySidon (S : Set (𝔽₂ n))) {w j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ w) :
    ∑ x : 𝔽₂ n, (((sliceW S w x) ×ˢ (sliceW S w x)).filter fun p =>
      (symmDiff p.1.1 p.2.1).card = 2 * j).card ≤
      Nat.choose n (2 * j) * 2 ^ (2 * j) *
        (Nat.choose (2 * j) j * Nat.choose (n - 2 * j) (w - j)) := by
  classical
  have h1 : ∀ x : 𝔽₂ n,
      ((S ×ˢ S).filter fun p =>
        (f2Supp (p.1 + x)).card = w ∧ (f2Supp (p.2 + x)).card = w ∧
          (f2Supp (p.1 + p.2)).card = 2 * j).card =
      (((sliceW S w x) ×ˢ (sliceW S w x)).filter fun p => (symmDiff p.1.1 p.2.1).card = 2 * j).card := by
    intro x
    refine Finset.card_bij
      (fun p hp => (⟨f2Supp (p.1 + x), (Finset.mem_filter.mp hp).2.1⟩,
        ⟨f2Supp (p.2 + x), (Finset.mem_filter.mp hp).2.2.1⟩))
      ?_ ?_ ?_
    · rintro ⟨a, b⟩ hab
      simp only [Finset.mem_filter, Finset.mem_product] at hab
      rcases hab with ⟨⟨ha, hb⟩, hwa, hwb, hdist⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨mem_sliceW.mpr ⟨a, ha, rfl⟩,
        mem_sliceW.mpr ⟨b, hb, rfl⟩⟩, ?_⟩
      dsimp only
      rw [← f2Supp_add (a + x) (b + x), f2_add_cancel_right]
      exact hdist
    · rintro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ heq
      have h1' : f2Supp (a₁ + x) = f2Supp (a₂ + x) := congr_arg (fun p => p.1.1) heq
      have h2' : f2Supp (b₁ + x) = f2Supp (b₂ + x) := congr_arg (fun p => p.2.1) heq
      exact Prod.ext (add_right_cancel (f2Supp_inj h1')) (add_right_cancel (f2Supp_inj h2'))
    · rintro ⟨A, B⟩ hAB
      simp only [Finset.mem_filter, Finset.mem_product] at hAB
      rcases hAB with ⟨⟨hA, hB⟩, hdiff⟩
      obtain ⟨a, ha, hfa⟩ := mem_sliceW.mp hA
      obtain ⟨b, hb, hfb⟩ := mem_sliceW.mp hB
      refine ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩,
        by rw [hfa]; exact A.2, by rw [hfb]; exact B.2, ?_⟩, ?_⟩
      · rw [← f2_add_cancel_right a b x, f2Supp_add, hfa, hfb]
        exact hdiff
      · ext1
        · ext1; exact hfa
        · ext1; exact hfb
  simp_rw [← h1, Finset.card_filter]
  rw [Finset.sum_comm]
  have hswap : ∀ p ∈ S ×ˢ S,
      (∑ x : 𝔽₂ n, if (f2Supp (p.1 + x)).card = w ∧ (f2Supp (p.2 + x)).card = w ∧
        (f2Supp (p.1 + p.2)).card = 2 * j then 1 else 0) =
      if (f2Supp (p.1 + p.2)).card = 2 * j then
        Nat.choose (2 * j) j * Nat.choose (n - 2 * j) (w - j) else 0 := by
    rintro ⟨a, b⟩ _
    by_cases hd : (f2Supp (a + b)).card = 2 * j
    · simp only [hd, and_true, ↓reduceIte]
      rw [← Finset.card_filter]
      exact count_x_both_weight a b hd hj
    · simp [hd]
  calc ∑ p ∈ S ×ˢ S, ∑ x : 𝔽₂ n, (if (f2Supp (p.1 + x)).card = w ∧
          (f2Supp (p.2 + x)).card = w ∧ (f2Supp (p.1 + p.2)).card = 2 * j then 1 else 0)
      = ∑ p ∈ S ×ˢ S, (if (f2Supp (p.1 + p.2)).card = 2 * j then
          Nat.choose (2 * j) j * Nat.choose (n - 2 * j) (w - j) else 0) :=
        Finset.sum_congr rfl hswap
    _ = ((S ×ˢ S).filter fun p => (f2Supp (p.1 + p.2)).card = 2 * j).card *
          (Nat.choose (2 * j) j * Nat.choose (n - 2 * j) (w - j)) := by
        simp [Finset.sum_ite]
    _ ≤ Nat.choose n (2 * j) * 2 ^ (2 * j) *
          (Nat.choose (2 * j) j * Nat.choose (n - 2 * j) (w - j)) := by
        exact Nat.mul_le_mul_right _ (sidon_dist_count_le S hS (by omega))

/-- Binomial identity: `C(n, 2j) * C(2j, j) * C(n - 2j, w - j) = C(n, w) * C(w, j) * C(n - w, j)`. -/
lemma choose_johnson_identity {n w j : ℕ} (hj : j ≤ w) (hw : w + j ≤ n) :
    Nat.choose n (2 * j) * (Nat.choose (2 * j) j * Nat.choose (n - 2 * j) (w - j)) =
      Nat.choose n w * (Nat.choose w j * Nat.choose (n - w) j) := by
  have h2j : 2 * j ≤ n := by omega
  have h1 := Nat.choose_mul_factorial_mul_factorial h2j
  have h2 := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
  have h3 := Nat.choose_mul_factorial_mul_factorial (show w - j ≤ n - 2 * j by omega)
  have h4 := Nat.choose_mul_factorial_mul_factorial (show w ≤ n by omega)
  have h5 := Nat.choose_mul_factorial_mul_factorial hj
  have h6 := Nat.choose_mul_factorial_mul_factorial (show j ≤ n - w by omega)
  have hfac_pos : 0 < Nat.factorial (2 * j) * Nat.factorial (n - 2 * j) *
      (Nat.factorial j * Nat.factorial j) *
      (Nat.factorial (w - j) * Nat.factorial (n - w - j)) *
      (Nat.factorial w * Nat.factorial (n - w)) := by
    positivity
  have hsub1 : (n - 2 * j) - (w - j) = n - w - j := by omega
  have hsub2 : (2 * j) - j = j := by omega
  have hsub3 : (n - w) - j = n - w - j := by omega
  rw [hsub1] at h3
  rw [hsub2] at h2
  rw [hsub3] at h6
  apply Nat.eq_of_mul_eq_mul_right hfac_pos
  calc Nat.choose n (2 * j) * (Nat.choose (2 * j) j * Nat.choose (n - 2 * j) (w - j)) *
        (Nat.factorial (2 * j) * Nat.factorial (n - 2 * j) *
          (Nat.factorial j * Nat.factorial j) *
          (Nat.factorial (w - j) * Nat.factorial (n - w - j)) *
          (Nat.factorial w * Nat.factorial (n - w)))
      = (Nat.choose n (2 * j) * Nat.factorial (2 * j) * Nat.factorial (n - 2 * j)) *
          (Nat.choose (2 * j) j * Nat.factorial j * Nat.factorial j) *
          (Nat.choose (n - 2 * j) (w - j) * Nat.factorial (w - j) * Nat.factorial (n - w - j)) *
          (Nat.factorial w * Nat.factorial (n - w)) := by ring
    _ = Nat.factorial n * Nat.factorial (2 * j) * Nat.factorial (n - 2 * j) *
          (Nat.factorial w * Nat.factorial (n - w)) := by rw [h1, h2, h3]
    _ = (Nat.choose n w * Nat.factorial w * Nat.factorial (n - w)) *
          (Nat.choose w j * Nat.factorial j * Nat.factorial (w - j)) *
          (Nat.choose (n - w) j * Nat.factorial j * Nat.factorial (n - w - j)) *
          (Nat.factorial (2 * j) * Nat.factorial (n - 2 * j)) := by
        rw [h4, h5, h6]; ring
    _ = Nat.choose n w * (Nat.choose w j * Nat.choose (n - w) j) *
          (Nat.factorial (2 * j) * Nat.factorial (n - 2 * j) *
            (Nat.factorial j * Nat.factorial j) *
            (Nat.factorial (w - j) * Nat.factorial (n - w - j)) *
            (Nat.factorial w * Nat.factorial (n - w))) := by ring

end BinarySidonCounting

section JohnsonScheme

open Matrix

/-- Johnson distance `|A \ B|` between two `w`-subsets. -/
def jDist {n w : ℕ} (A B : WSub n w) : ℕ :=
  (A.1 \ B.1).card

lemma jDist_symm {n w : ℕ} (A B : WSub n w) : jDist A B = jDist B A := by
  have h1 := Finset.card_sdiff_add_card_inter A.1 B.1
  have h2 := Finset.card_sdiff_add_card_inter B.1 A.1
  rw [A.2] at h1
  rw [B.2, Finset.inter_comm] at h2
  dsimp [jDist]
  omega

lemma card_symmDiff_wsub {n w : ℕ} (A B : WSub n w) :
    (symmDiff A.1 B.1).card = 2 * jDist A B := by
  have hsd : symmDiff A.1 B.1 = (A.1 \ B.1) ∪ (B.1 \ A.1) := by
    ext i
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
  rw [hsd, Finset.card_union_of_disjoint]
  · have hsym := jDist_symm A B
    dsimp [jDist] at hsym ⊢
    omega
  · rw [Finset.disjoint_left]
    intro i hi1 hi2
    exact (Finset.mem_sdiff.mp hi2).2 (Finset.mem_sdiff.mp hi1).1

lemma jDist_le {n w : ℕ} (A B : WSub n w) : jDist A B ≤ w := by
  calc jDist A B = (A.1 \ B.1).card := rfl
    _ ≤ A.1.card := Finset.card_le_card Finset.sdiff_subset
    _ = w := A.2

lemma jDist_add_le {n w : ℕ} (A B : WSub n w) : w + jDist A B ≤ n := by
  have hsub : A.1 ∪ B.1 ⊆ Finset.univ := Finset.subset_univ _
  have hcard : (A.1 ∪ B.1).card ≤ n := by
    simpa [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card hsub
  have hu : (A.1 ∪ B.1).card = w + jDist A B := by
    have hdisj : Disjoint A.1 (B.1 \ A.1) := disjoint_sdiff_self_right
    have heq : A.1 ∪ B.1 = A.1 ∪ (B.1 \ A.1) := by
      ext i; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
    have hsym := jDist_symm A B
    rw [heq, Finset.card_union_of_disjoint hdisj, A.2]
    dsimp [jDist] at hsym ⊢
    omega
  omega

lemma card_inter_wsub {n w : ℕ} (A B : WSub n w) :
    (A.1 ∩ B.1).card = w - jDist A B := by
  have h := Finset.card_sdiff_add_card_inter A.1 B.1
  rw [A.2] at h
  dsimp [jDist]
  omega

lemma jDist_eq_zero_iff {n w : ℕ} {A B : WSub n w} :
    jDist A B = 0 ↔ A = B := by
  constructor
  · intro h
    have hsub : A.1 \ B.1 = ∅ := Finset.card_eq_zero.mp h
    have hAB : A.1 ⊆ B.1 := Finset.sdiff_eq_empty_iff_subset.mp hsub
    exact Subtype.ext (Finset.eq_of_subset_of_card_le hAB (by rw [A.2, B.2]))
  · rintro rfl
    simp [jDist]

/-- Adjacency matrix of the Johnson graph `J(n, w)`. -/
noncomputable def jAdjMatrix (n w : ℕ) : Matrix (WSub n w) (WSub n w) ℝ :=
  fun A B => if jDist A B = 1 then 1 else 0

lemma jAdjMatrix_symm (n w : ℕ) (A B : WSub n w) :
    jAdjMatrix n w A B = jAdjMatrix n w B A := by
  simp only [jAdjMatrix, jDist_symm A B]

lemma eucl_sum_apply {α ι : Type*} [Fintype α] [DecidableEq α] (s : Finset ι)
    (f : ι → EuclideanSpace ℝ α) (A : α) :
    (∑ i ∈ s, f i) A = ∑ i ∈ s, (f i) A := by
  simp_rw [← EuclideanSpace.basisFun_inner, inner_sum]

/-- Matrix representation of a linear operator on `EuclideanSpace ℝ α` in the standard basis. -/
noncomputable def opToMatrix {α : Type*} [Fintype α] [DecidableEq α]
    (T : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ α) : Matrix α α ℝ :=
  fun A B => (T (EuclideanSpace.basisFun α ℝ B)) A

lemma opToMatrix_mulVec {α : Type*} [Fintype α] [DecidableEq α]
    (T : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ α) (v : EuclideanSpace ℝ α) (A : α) :
    (opToMatrix T *ᵥ v) A = (T v) A := by
  have hv : v = ∑ B : α, v B • EuclideanSpace.basisFun α ℝ B := by
    have h := (EuclideanSpace.basisFun α ℝ).sum_repr v
    simpa [EuclideanSpace.basisFun_repr] using h.symm
  conv_rhs => rw [hv, map_sum]
  rw [eucl_sum_apply]
  simp only [Matrix.mulVec, dotProduct, opToMatrix]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [map_smul, PiLp.smul_apply, smul_eq_mul, mul_comm]

lemma opToMatrix_mul {α : Type*} [Fintype α] [DecidableEq α]
    (S T : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ α) :
    opToMatrix (S ∘L T) = opToMatrix S * opToMatrix T := by
  ext A B
  simp only [opToMatrix, ContinuousLinearMap.comp_apply, Matrix.mul_apply]
  exact (opToMatrix_mulVec S (T (EuclideanSpace.basisFun α ℝ B)) A).symm

lemma opToMatrix_id {α : Type*} [Fintype α] [DecidableEq α] :
    opToMatrix (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ α)) = 1 := by
  ext A B
  simp [opToMatrix, ContinuousLinearMap.id_apply, EuclideanSpace.basisFun_apply,
    Matrix.one_apply, PiLp.single_apply]

lemma opToMatrix_starProjection_symm {α : Type*} [Fintype α] [DecidableEq α]
    (K : Submodule ℝ (EuclideanSpace ℝ α)) (A B : α) :
    opToMatrix K.starProjection A B = opToMatrix K.starProjection B A := by
  calc opToMatrix K.starProjection A B
      = inner ℝ (EuclideanSpace.basisFun α ℝ A)
          (K.starProjection (EuclideanSpace.basisFun α ℝ B)) := by
        rw [EuclideanSpace.basisFun_inner]; rfl
    _ = inner ℝ (K.starProjection (EuclideanSpace.basisFun α ℝ A))
          (EuclideanSpace.basisFun α ℝ B) :=
        (K.inner_starProjection_left_eq_right _ _).symm
    _ = inner ℝ (EuclideanSpace.basisFun α ℝ B)
          (K.starProjection (EuclideanSpace.basisFun α ℝ A)) := real_inner_comm _ _
    _ = opToMatrix K.starProjection B A := by
        rw [EuclideanSpace.basisFun_inner]; rfl

lemma opToMatrix_starProjection_posSemidef {α : Type*} [Fintype α] [DecidableEq α]
    (K : Submodule ℝ (EuclideanSpace ℝ α)) :
    (opToMatrix K.starProjection).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · ext A B
    simp [opToMatrix_starProjection_symm K A B]
  · intro x
    let v : EuclideanSpace ℝ α := WithLp.toLp 2 x
    have hv : ∀ A, (opToMatrix K.starProjection *ᵥ x) A = (K.starProjection v) A := by
      intro A
      simpa [v] using opToMatrix_mulVec K.starProjection v A
    have hdot : star x ⬝ᵥ (opToMatrix K.starProjection *ᵥ x) =
        inner ℝ v (K.starProjection v) := by
      simp only [dotProduct, star_trivial, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      refine Finset.sum_congr rfl fun A _ => ?_
      rw [hv A]
      ring
    rw [hdot, real_inner_comm]
    simpa using K.re_inner_starProjection_nonneg v

lemma posSemidef_sum_nonneg_smul {α ι : Type*} [Fintype α] [DecidableEq α]
    (s : Finset ι) (c : ι → ℝ) (M : ι → Matrix α α ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hM : ∀ i ∈ s, (M i).PosSemidef) :
    (∑ i ∈ s, c i • M i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.PosSemidef.zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ((hM a (Finset.mem_insert_self a s)).smul (hc a (Finset.mem_insert_self a s))).add
      (ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))
          (fun i hi => hM i (Finset.mem_insert_of_mem hi)))

lemma opToMatrix_starProjection_trace {α : Type*} [Fintype α] [DecidableEq α]
    (K : Submodule ℝ (EuclideanSpace ℝ α)) :
    ∑ A : α, opToMatrix K.starProjection A A = (Module.finrank ℝ K : ℝ) := by
  let b := stdOrthonormalBasis ℝ K
  have hproj : ∀ x : EuclideanSpace ℝ α,
      K.starProjection x = ∑ i, inner ℝ ((b i : K) : EuclideanSpace ℝ α) x •
        ((b i : K) : EuclideanSpace ℝ α) := by
    intro x
    refine K.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
    · exact K.sum_mem fun i _ => K.smul_mem _ (b i).2
    · intro u hu
      have hu_eq : (⟨u, hu⟩ : K) = ∑ i, inner ℝ (b i) ⟨u, hu⟩ • b i := by
        have h := b.sum_repr ⟨u, hu⟩
        simpa [OrthonormalBasis.repr_apply_apply] using h.symm
      have hu' : u = ∑ i, inner ℝ ((b i : K) : EuclideanSpace ℝ α) u •
          ((b i : K) : EuclideanSpace ℝ α) := by
        simpa using congr_arg Subtype.val hu_eq
      rw [inner_sub_left]
      have hx_eq : inner ℝ x u = ∑ i, inner ℝ ((b i : K) : EuclideanSpace ℝ α) u *
          inner ℝ x ((b i : K) : EuclideanSpace ℝ α) := by
        conv_lhs => rw [hu']
        rw [inner_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [real_inner_smul_right]
      have hy_eq : inner ℝ (∑ i, inner ℝ ((b i : K) : EuclideanSpace ℝ α) x •
          ((b i : K) : EuclideanSpace ℝ α)) u =
          ∑ i, inner ℝ ((b i : K) : EuclideanSpace ℝ α) x *
            inner ℝ ((b i : K) : EuclideanSpace ℝ α) u := by
        rw [sum_inner]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [real_inner_smul_left]
      rw [hx_eq, hy_eq, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_comm x _, mul_comm]
  calc ∑ A : α, opToMatrix K.starProjection A A
      = ∑ A : α, (K.starProjection (EuclideanSpace.basisFun α ℝ A)) A := rfl
    _ = ∑ A : α, ∑ i, ((b i : K) : EuclideanSpace ℝ α) A *
          ((b i : K) : EuclideanSpace ℝ α) A := by
        refine Finset.sum_congr rfl fun A _ => ?_
        rw [hproj, eucl_sum_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [PiLp.smul_apply, smul_eq_mul, EuclideanSpace.inner_basisFun_real]
    _ = ∑ i, ∑ A : α, ((b i : K) : EuclideanSpace ℝ α) A *
          ((b i : K) : EuclideanSpace ℝ α) A := Finset.sum_comm
    _ = ∑ i, inner ℝ ((b i : K) : EuclideanSpace ℝ α) ((b i : K) : EuclideanSpace ℝ α) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [PiLp.inner_apply]
        simp only [RCLike.inner_apply, conj_trivial]
    _ = ∑ i, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [real_inner_self_eq_norm_sq]
        have hn : ‖((b i : K) : EuclideanSpace ℝ α)‖ = 1 := b.orthonormal.1 i
        rw [hn, one_pow]
    _ = (Fintype.card (Fin (Module.finrank ℝ K)) : ℝ) := by simp
    _ = (Module.finrank ℝ K : ℝ) := by simp

/-- Indicator vector of supersets of `U` in `EuclideanSpace ℝ (WSub n w)`. -/
noncomputable def indVec (n w : ℕ) (U : Finset (Fin n)) : EuclideanSpace ℝ (WSub n w) :=
  WithLp.toLp 2 (fun A : WSub n w => if U ⊆ A.1 then (1 : ℝ) else 0)

/-- Span of `k`-set indicator vectors in `WSub n w`. -/
noncomputable def HSub (n w k : ℕ) : Submodule ℝ (EuclideanSpace ℝ (WSub n w)) :=
  Submodule.span ℝ { v | ∃ U : Finset (Fin n), U.card = k ∧ v = indVec n w U }

/-- `k`-th Johnson eigenspace `V_k = H_k ∩ H_{k-1}ᗮ`. -/
noncomputable def VSub (n w : ℕ) : ℕ → Submodule ℝ (EuclideanSpace ℝ (WSub n w))
  | 0 => HSub n w 0
  | k + 1 => HSub n w (k + 1) ⊓ (HSub n w k)ᗮ

/-- Orthogonal projection matrix onto `VSub n w k`. -/
noncomputable def projMat (n w k : ℕ) : Matrix (WSub n w) (WSub n w) ℝ :=
  opToMatrix (VSub n w k).starProjection

lemma indVec_mem_HSub {n w k : ℕ} {U : Finset (Fin n)} (hU : U.card = k) :
    indVec n w U ∈ HSub n w k :=
  Submodule.subset_span ⟨U, hU, rfl⟩

lemma HSub_step {n w k : ℕ} (hk : k + 1 ≤ w) : HSub n w k ≤ HSub n w (k + 1) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨U, hU, rfl⟩
  have hsum : ∑ i ∈ Finset.univ \ U, indVec n w (insert i U) = ((w - k : ℕ) : ℝ) • indVec n w U := by
    ext A
    rw [eucl_sum_apply]
    simp only [PiLp.smul_apply, smul_eq_mul, indVec, PiLp.toLp_apply]
    by_cases hUA : U ⊆ A.1
    · have hfilter : (Finset.univ \ U).filter (fun i => insert i U ⊆ A.1) = A.1 \ U := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
          Finset.insert_subset_iff, hUA, and_true]
        tauto
      rw [if_pos hUA, mul_one]
      have hconst : ∀ i ∈ (Finset.univ \ U).filter (fun i => insert i U ⊆ A.1),
          (if insert i U ⊆ A.1 then (1 : ℝ) else 0) = 1 := fun i hi =>
        if_pos (Finset.mem_filter.mp hi).2
      calc ∑ i ∈ Finset.univ \ U, (if insert i U ⊆ A.1 then (1 : ℝ) else 0)
          = ∑ i ∈ (Finset.univ \ U).filter (fun i => insert i U ⊆ A.1),
              (if insert i U ⊆ A.1 then (1 : ℝ) else 0) := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun i _ => ?_
            split_ifs <;> rfl
        _ = ∑ _ ∈ A.1 \ U, (1 : ℝ) := by
            rw [Finset.sum_congr rfl hconst, hfilter]
        _ = ((A.1 \ U).card : ℝ) := by simp
        _ = ((w - k : ℕ) : ℝ) := by
            rw [Finset.card_sdiff_of_subset hUA, A.2, hU]
    · rw [if_neg hUA, mul_zero]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg]
      intro hsub
      exact hUA (Finset.Subset.trans (Finset.subset_insert i U) hsub)
  have hmem : ((w - k : ℕ) : ℝ) • indVec n w U ∈ HSub n w (k + 1) := by
    rw [← hsum]
    refine Submodule.sum_mem _ fun i hi => indVec_mem_HSub ?_
    rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hi).2, hU]
  have hpos : ((w - k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : w - k ≠ 0)
  have heq : indVec n w U = (((w - k : ℕ) : ℝ)⁻¹) • (((w - k : ℕ) : ℝ) • indVec n w U) := by
    rw [smul_smul, inv_mul_cancel₀ hpos, one_smul]
  rw [heq]
  exact Submodule.smul_mem _ _ hmem

lemma HSub_mono {n w k l : ℕ} (hkl : k ≤ l) (hl : l ≤ w) :
    HSub n w k ≤ HSub n w l := by
  induction l with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    exact le_rfl
  | succ l ih =>
    rcases Nat.eq_or_lt_of_le hkl with rfl | hlt
    · exact le_rfl
    · exact le_trans (ih (by omega) (by omega)) (HSub_step hl)

lemma HSub_top (n w : ℕ) : HSub n w w = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : v = ∑ A : WSub n w, v A • EuclideanSpace.basisFun (WSub n w) ℝ A := by
    have h := (EuclideanSpace.basisFun (WSub n w) ℝ).sum_repr v
    simpa [EuclideanSpace.basisFun_repr] using h.symm
  rw [hv]
  refine Submodule.sum_mem _ fun A _ => Submodule.smul_mem _ _ ?_
  have heq : EuclideanSpace.basisFun (WSub n w) ℝ A = indVec n w A.1 := by
    ext B
    simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply, indVec, PiLp.toLp_apply]
    by_cases hAB : A = B
    · subst hAB; simp
    · rw [if_neg (Ne.symm hAB), if_neg]
      intro hsub
      exact hAB (Subtype.ext (Finset.eq_of_subset_of_card_le hsub (by rw [A.2, B.2])))
  rw [heq]
  exact indVec_mem_HSub A.2

lemma VSub_le_HSub (n w k : ℕ) : VSub n w k ≤ HSub n w k := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact inf_le_left

lemma VSub_orthogonal {n w k l : ℕ} (hkl : k ≠ l) (hk : k ≤ w) (hl : l ≤ w)
    {u v : EuclideanSpace ℝ (WSub n w)} (hu : u ∈ VSub n w k) (hv : v ∈ VSub n w l) :
    inner ℝ u v = 0 := by
  wlog hlt : k < l
  · rw [real_inner_comm]
    exact this hkl.symm hl hk hv hu (lt_of_le_of_ne (not_lt.mp hlt) hkl.symm)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
  have huH : u ∈ HSub n w m := HSub_mono (by omega) (by omega) (VSub_le_HSub n w k hu)
  have hvO : v ∈ (HSub n w m)ᗮ := (Submodule.mem_inf.mp hv).2
  exact (Submodule.mem_orthogonal _ _).mp hvO u huH

lemma projMat_mul_eq_zero {n w k l : ℕ} (hkl : k ≠ l) (hk : k ≤ w) (hl : l ≤ w) :
    projMat n w k * projMat n w l = 0 := by
  rw [projMat, projMat, ← opToMatrix_mul]
  ext A B
  simp only [opToMatrix, ContinuousLinearMap.comp_apply, Matrix.zero_apply]
  have hmemA : (VSub n w k).starProjection (EuclideanSpace.basisFun (WSub n w) ℝ A) ∈ VSub n w k :=
    Submodule.starProjection_apply_mem _ _
  have hmemB : (VSub n w l).starProjection (EuclideanSpace.basisFun (WSub n w) ℝ B) ∈ VSub n w l :=
    Submodule.starProjection_apply_mem _ _
  have horth : inner ℝ ((VSub n w k).starProjection (EuclideanSpace.basisFun (WSub n w) ℝ A))
      ((VSub n w l).starProjection (EuclideanSpace.basisFun (WSub n w) ℝ B)) = 0 :=
    VSub_orthogonal hkl hk hl hmemA hmemB
  have hidem : ((VSub n w k).starProjection ((VSub n w l).starProjection
      (EuclideanSpace.basisFun (WSub n w) ℝ B))) A =
      inner ℝ (EuclideanSpace.basisFun (WSub n w) ℝ A)
        ((VSub n w k).starProjection ((VSub n w l).starProjection
          (EuclideanSpace.basisFun (WSub n w) ℝ B))) := by
    rw [EuclideanSpace.basisFun_inner]
  rw [hidem, ← (VSub n w k).inner_starProjection_left_eq_right]
  exact horth

lemma projMat_mul_self (n w k : ℕ) : projMat n w k * projMat n w k = projMat n w k := by
  rw [projMat, ← opToMatrix_mul]
  congr 1
  exact (VSub n w k).isIdempotentElem_starProjection

lemma sum_projMat_eq_one (n w : ℕ) :
    ∑ k ∈ Finset.range (w + 1), projMat n w k = 1 := by
  have hsum : ∀ m ≤ w, ∀ x : EuclideanSpace ℝ (WSub n w), x ∈ HSub n w m →
      ∑ k ∈ Finset.range (m + 1), (VSub n w k).starProjection x = x := by
    intro m
    induction m with
    | zero =>
      intro _ x hx
      simpa [VSub] using (HSub n w 0).starProjection_eq_self_iff.mpr hx
    | succ m ih =>
      intro hm x hx
      have hdecomp : x = (HSub n w m).starProjection x +
          (x - (HSub n w m).starProjection x) := by abel
      have h1 : (HSub n w m).starProjection x ∈ HSub n w m := Submodule.starProjection_apply_mem _ _
      have h2 : x - (HSub n w m).starProjection x ∈ VSub n w (m + 1) := by
        refine ⟨sub_mem hx (HSub_step hm h1), ?_⟩
        exact (HSub n w m).sub_starProjection_mem_orthogonal x
      have hsum1 : ∑ k ∈ Finset.range (m + 1), (VSub n w k).starProjection x =
          (HSub n w m).starProjection x := by
        have hp : ∀ k ≤ m, (VSub n w k).starProjection x =
            (VSub n w k).starProjection ((HSub n w m).starProjection x) := by
          intro k hk
          have hVk : VSub n w k ≤ HSub n w m :=
            le_trans (VSub_le_HSub n w k) (HSub_mono hk (by omega))
          have hsub : x - (HSub n w m).starProjection x ∈ (HSub n w m)ᗮ :=
            (HSub n w m).sub_starProjection_mem_orthogonal x
          have hsubVk : x - (HSub n w m).starProjection x ∈ (VSub n w k)ᗮ :=
            Submodule.orthogonal_le hVk hsub
          have hz : (VSub n w k).starProjection (x - (HSub n w m).starProjection x) = 0 :=
            (Submodule.starProjection_apply_eq_zero_iff (VSub n w k)).mpr hsubVk
          rw [map_sub, sub_eq_zero] at hz
          exact hz
        calc ∑ k ∈ Finset.range (m + 1), (VSub n w k).starProjection x
            = ∑ k ∈ Finset.range (m + 1),
                (VSub n w k).starProjection ((HSub n w m).starProjection x) := by
              refine Finset.sum_congr rfl fun k hk => hp k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
          _ = (HSub n w m).starProjection x := ih (by omega) _ h1
      have hlast : (VSub n w (m + 1)).starProjection x = x - (HSub n w m).starProjection x := by
        nth_rw 1 [hdecomp]
        rw [map_add, (VSub n w (m + 1)).starProjection_eq_self_iff.mpr h2]
        have hz : (VSub n w (m + 1)).starProjection ((HSub n w m).starProjection x) = 0 := by
          rw [Submodule.starProjection_apply_eq_zero_iff]
          intro y hy
          rw [real_inner_comm]
          exact (Submodule.mem_orthogonal _ _).mp (Submodule.mem_inf.mp hy).2 _ h1
        rw [hz, zero_add]
      rw [Finset.sum_range_succ, hsum1, hlast]
      abel
  ext A B
  rw [← opToMatrix_id, Matrix.sum_apply]
  have hB : EuclideanSpace.basisFun (WSub n w) ℝ B ∈ HSub n w w := by
    rw [HSub_top]; trivial
  have heq := hsum w le_rfl (EuclideanSpace.basisFun (WSub n w) ℝ B) hB
  simp only [projMat, opToMatrix, ContinuousLinearMap.id_apply]
  rw [← eucl_sum_apply]
  exact congr_arg (fun v => v A) heq

/-- Up incidence operator `U_r : (WSub n r → ℝ) → (WSub n (r + 1) → ℝ)`. -/
def upOp (n r : ℕ) (c : WSub n r → ℝ) : WSub n (r + 1) → ℝ :=
  fun V => ∑ U : WSub n r, if U.1 ⊆ V.1 then c U else 0

/-- Down incidence operator `D_{r+1} : (WSub n (r + 1) → ℝ) → (WSub n r → ℝ)`. -/
def downOp (n r : ℕ) (g : WSub n (r + 1) → ℝ) : WSub n r → ℝ :=
  fun U => ∑ V : WSub n (r + 1), if U.1 ⊆ V.1 then g V else 0

lemma upOp_adjoint_downOp (n r : ℕ) (c : WSub n r → ℝ) (g : WSub n (r + 1) → ℝ) :
    ∑ V : WSub n (r + 1), g V * upOp n r c V = ∑ U : WSub n r, downOp n r g U * c U := by
  simp only [upOp, downOp, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun U _ => Finset.sum_congr rfl fun V _ => ?_
  split_ifs <;> ring

lemma downOp_upOp_identity {n m : ℕ} (hm : m + 1 ≤ n) (c : WSub n (m + 1) → ℝ)
    (U : WSub n (m + 1)) :
    downOp n (m + 1) (upOp n (m + 1) c) U - upOp n m (downOp n m c) U =
      ((n : ℝ) - 2 * ((m + 1 : ℕ) : ℝ)) * c U := by
  have hdown_up : downOp n (m + 1) (upOp n (m + 1) c) U =
      ((n - (m + 1) : ℕ) : ℝ) * c U +
      ∑ V : WSub n (m + 1), if (U.1 ∩ V.1).card = m then c V else 0 := by
    simp only [downOp, upOp]
    have hswap : (∑ W : WSub n (m + 2), if U.1 ⊆ W.1 then
          ∑ V : WSub n (m + 1), if V.1 ⊆ W.1 then c V else 0 else 0) =
        ∑ V : WSub n (m + 1),
          ((Finset.univ.filter fun W : WSub n (m + 2) => U.1 ⊆ W.1 ∧ V.1 ⊆ W.1).card : ℝ) *
            c V := by
      have hpull : ∀ W : WSub n (m + 2),
          (if U.1 ⊆ W.1 then ∑ V : WSub n (m + 1), if V.1 ⊆ W.1 then c V else 0 else 0) =
          ∑ V : WSub n (m + 1), if U.1 ⊆ W.1 ∧ V.1 ⊆ W.1 then c V else 0 := by
        intro W
        by_cases hU : U.1 ⊆ W.1
        · simp [hU]
        · simp [hU]
      simp_rw [hpull]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun V _ => ?_
      rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun W _ => ?_
      by_cases hUW : U.1 ⊆ W.1 ∧ V.1 ⊆ W.1 <;> simp [hUW]
    rw [hswap]
    have hcount : ∀ V : WSub n (m + 1),
        ((Finset.univ.filter fun W : WSub n (m + 2) => U.1 ⊆ W.1 ∧ V.1 ⊆ W.1).card : ℝ) * c V =
          (if V = U then ((n - (m + 1) : ℕ) : ℝ) * c V else 0) +
          (if (U.1 ∩ V.1).card = m then c V else 0) := by
      intro V
      by_cases hVU : V = U
      · subst V
        have hnot : (U.1 ∩ U.1).card ≠ m := by rw [Finset.inter_self, U.2]; omega
        rw [if_pos rfl, if_neg hnot, add_zero]
        congr 1
        norm_cast
        have hbij : (Finset.univ.filter fun W : WSub n (m + 2) => U.1 ⊆ W.1 ∧ U.1 ⊆ W.1).card =
            (Finset.powersetCard 1 (Finset.univ \ U.1)).card := by
          refine Finset.card_bij (fun W _ => W.1 \ U.1) ?_ ?_ ?_
          · intro W hW
            have hUW : U.1 ⊆ W.1 := (Finset.mem_filter.mp hW).2.1
            refine Finset.mem_powersetCard.mpr ⟨fun x hx => ?_, ?_⟩
            · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
            · rw [Finset.card_sdiff_of_subset hUW, W.2, U.2]; omega
          · intro W₁ hW₁ W₂ hW₂ heq
            have h1 : U.1 ⊆ W₁.1 := (Finset.mem_filter.mp hW₁).2.1
            have h2 : U.1 ⊆ W₂.1 := (Finset.mem_filter.mp hW₂).2.1
            ext1
            rw [← Finset.union_sdiff_of_subset h1, ← Finset.union_sdiff_of_subset h2, heq]
          · intro D hD
            rcases Finset.mem_powersetCard.mp hD with ⟨hDsub, hDcard⟩
            have hdisj : Disjoint U.1 D := by
              rw [Finset.disjoint_left]
              intro x hxU hxD
              exact (Finset.mem_sdiff.mp (hDsub hxD)).2 hxU
            have hWcard : (U.1 ∪ D).card = m + 2 := by
              rw [Finset.card_union_of_disjoint hdisj, U.2, hDcard]
            refine ⟨⟨U.1 ∪ D, hWcard⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              ⟨Finset.subset_union_left, Finset.subset_union_left⟩⟩, ?_⟩
            exact Finset.union_sdiff_cancel_left hdisj
        rw [hbij, Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ _),
          Finset.card_univ, Fintype.card_fin, U.2, Nat.choose_one_right]
      · by_cases hinter : (U.1 ∩ V.1).card = m
        · rw [if_neg hVU, if_pos hinter, zero_add]
          have hcardUV : (U.1 ∪ V.1).card = m + 2 := by
            have h := Finset.card_union_add_card_inter U.1 V.1
            rw [U.2, V.2, hinter] at h
            omega
          have hfilt : (Finset.univ.filter fun W : WSub n (m + 2) => U.1 ⊆ W.1 ∧ V.1 ⊆ W.1) =
              {⟨U.1 ∪ V.1, hcardUV⟩} := by
            ext W
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · rintro ⟨hUW, hVW⟩
              exact Subtype.ext (Finset.eq_of_subset_of_card_le (Finset.union_subset hUW hVW)
                (by rw [W.2, hcardUV])).symm
            · rintro rfl
              exact ⟨Finset.subset_union_left, Finset.subset_union_right⟩
          rw [hfilt, Finset.card_singleton]
          simp
        · rw [if_neg hVU, if_neg hinter, zero_add]
          have hlt : (U.1 ∩ V.1).card < m := by
            have hle : (U.1 ∩ V.1).card ≤ m + 1 :=
              (Finset.card_le_card Finset.inter_subset_left).trans_eq U.2
            have hne : (U.1 ∩ V.1).card ≠ m + 1 := by
              intro heq
              have hUV : U.1 ⊆ V.1 := by
                have heq1 : U.1 ∩ V.1 = U.1 :=
                  Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [heq, U.2])
                intro x hx
                rw [← heq1] at hx
                exact (Finset.mem_inter.mp hx).2
              exact hVU (Subtype.ext (Finset.eq_of_subset_of_card_le hUV (by rw [U.2, V.2])).symm)
            omega
          have hfilt : (Finset.univ.filter fun W : WSub n (m + 2) => U.1 ⊆ W.1 ∧ V.1 ⊆ W.1) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro W _ ⟨hUW, hVW⟩
            have hle : (U.1 ∪ V.1).card ≤ W.1.card := Finset.card_le_card (Finset.union_subset hUW hVW)
            have h := Finset.card_union_add_card_inter U.1 V.1
            rw [U.2, V.2] at h
            rw [W.2] at hle
            omega
          rw [hfilt]
          simp
    simp_rw [hcount, Finset.sum_add_distrib]
    simp [Finset.sum_ite_eq']
  have hup_down : upOp n m (downOp n m c) U =
      ((m + 1 : ℕ) : ℝ) * c U +
      ∑ V : WSub n (m + 1), if (U.1 ∩ V.1).card = m then c V else 0 := by
    simp only [upOp, downOp]
    have hswap : (∑ T : WSub n m, if T.1 ⊆ U.1 then
          ∑ V : WSub n (m + 1), if T.1 ⊆ V.1 then c V else 0 else 0) =
        ∑ V : WSub n (m + 1),
          ((Finset.univ.filter fun T : WSub n m => T.1 ⊆ U.1 ∧ T.1 ⊆ V.1).card : ℝ) * c V := by
      have hpull : ∀ T : WSub n m,
          (if T.1 ⊆ U.1 then ∑ V : WSub n (m + 1), if T.1 ⊆ V.1 then c V else 0 else 0) =
          ∑ V : WSub n (m + 1), if T.1 ⊆ U.1 ∧ T.1 ⊆ V.1 then c V else 0 := by
        intro T
        by_cases hU : T.1 ⊆ U.1
        · simp [hU]
        · simp [hU]
      simp_rw [hpull]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun V _ => ?_
      rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun T _ => ?_
      by_cases hT : T.1 ⊆ U.1 ∧ T.1 ⊆ V.1 <;> simp [hT]
    rw [hswap]
    have hcount : ∀ V : WSub n (m + 1),
        ((Finset.univ.filter fun T : WSub n m => T.1 ⊆ U.1 ∧ T.1 ⊆ V.1).card : ℝ) * c V =
          (if V = U then ((m + 1 : ℕ) : ℝ) * c V else 0) +
          (if (U.1 ∩ V.1).card = m then c V else 0) := by
      intro V
      by_cases hVU : V = U
      · subst V
        have hnot : (U.1 ∩ U.1).card ≠ m := by rw [Finset.inter_self, U.2]; omega
        rw [if_pos rfl, if_neg hnot, add_zero]
        congr 1
        norm_cast
        have hbij : (Finset.univ.filter fun T : WSub n m => T.1 ⊆ U.1 ∧ T.1 ⊆ U.1).card =
            (Finset.powersetCard m U.1).card := by
          refine Finset.card_bij (fun T _ => T.1) ?_ ?_ ?_
          · intro T hT
            exact Finset.mem_powersetCard.mpr ⟨(Finset.mem_filter.mp hT).2.1, T.2⟩
          · intro T₁ _ T₂ _ heq
            exact Subtype.ext heq
          · intro T hT
            rcases Finset.mem_powersetCard.mp hT with ⟨hTU, hTcard⟩
            exact ⟨⟨T, hTcard⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTU, hTU⟩, rfl⟩
        rw [hbij, Finset.card_powersetCard, U.2, Nat.choose_succ_self_right]
      · by_cases hinter : (U.1 ∩ V.1).card = m
        · rw [if_neg hVU, if_pos hinter, zero_add]
          have hfilt : (Finset.univ.filter fun T : WSub n m => T.1 ⊆ U.1 ∧ T.1 ⊆ V.1) =
              {⟨U.1 ∩ V.1, hinter⟩} := by
            ext T
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · rintro ⟨hTU, hTV⟩
              exact Subtype.ext (Finset.eq_of_subset_of_card_le (Finset.subset_inter hTU hTV)
                (by rw [hinter, T.2]))
            · rintro rfl
              exact ⟨Finset.inter_subset_left, Finset.inter_subset_right⟩
          rw [hfilt, Finset.card_singleton]
          simp
        · rw [if_neg hVU, if_neg hinter, zero_add]
          have hlt : (U.1 ∩ V.1).card < m := by
            have hle : (U.1 ∩ V.1).card ≤ m + 1 :=
              (Finset.card_le_card Finset.inter_subset_left).trans_eq U.2
            have hne : (U.1 ∩ V.1).card ≠ m + 1 := by
              intro heq
              have hUV : U.1 ⊆ V.1 := by
                have heq1 : U.1 ∩ V.1 = U.1 :=
                  Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [heq, U.2])
                intro x hx
                rw [← heq1] at hx
                exact (Finset.mem_inter.mp hx).2
              exact hVU (Subtype.ext (Finset.eq_of_subset_of_card_le hUV (by rw [U.2, V.2])).symm)
            omega
          have hfilt : (Finset.univ.filter fun T : WSub n m => T.1 ⊆ U.1 ∧ T.1 ⊆ V.1) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro T _ ⟨hTU, hTV⟩
            have hle := Finset.card_le_card (Finset.subset_inter hTU hTV)
            rw [T.2] at hle
            omega
          rw [hfilt]
          simp
    simp_rw [hcount, Finset.sum_add_distrib]
    simp [Finset.sum_ite_eq']
  rw [hdown_up, hup_down]
  have hcast : ((n - (m + 1) : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ) =
      (n : ℝ) - 2 * ((m + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hm]
    push_cast
    ring
  rw [← hcast]
  ring

lemma upOp_injective {n r : ℕ} (hr : 2 * r < n) :
    Function.Injective (upOp n r) := by
  have hlin : ∀ c, upOp n r c = 0 → c = 0 := by
    intro c hc
    cases r with
    | zero =>
      ext U
      have hU : U.1 = ∅ := Finset.card_eq_zero.mp U.2
      have hex : ∃ i : Fin n, True := ⟨⟨0, by omega⟩, trivial⟩
      obtain ⟨i, _⟩ := hex
      have hV : ({i} : Finset (Fin n)).card = 1 := Finset.card_singleton i
      have h0 := congr_fun hc ⟨{i}, hV⟩
      simp only [upOp, Pi.zero_apply] at h0
      have hsum : (∑ T : WSub n 0, if T.1 ⊆ {i} then c T else 0) = c U := by
        rw [Finset.sum_eq_single U]
        · rw [if_pos (by rw [hU]; exact Finset.empty_subset _)]
        · intro T _ hTU
          exfalso
          apply hTU
          ext1
          rw [hU, Finset.card_eq_zero.mp T.2]
        · intro h
          exact False.elim (h (Finset.mem_univ U))
      rw [hsum] at h0
      exact h0
    | succ m =>
      have hsum1 : ∑ U : WSub n (m + 1), c U * (downOp n (m + 1) (upOp n (m + 1) c) U -
          upOp n m (downOp n m c) U) =
          ((n : ℝ) - 2 * ((m + 1 : ℕ) : ℝ)) * ∑ U : WSub n (m + 1), (c U) ^ 2 := by
        calc ∑ U : WSub n (m + 1), c U * (downOp n (m + 1) (upOp n (m + 1) c) U -
              upOp n m (downOp n m c) U)
            = ∑ U : WSub n (m + 1), c U * (((n : ℝ) - 2 * ((m + 1 : ℕ) : ℝ)) * c U) := by
              refine Finset.sum_congr rfl fun U _ => ?_
              rw [downOp_upOp_identity (by omega) c U]
          _ = ((n : ℝ) - 2 * ((m + 1 : ℕ) : ℝ)) * ∑ U : WSub n (m + 1), (c U) ^ 2 := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun U _ => by ring
      have h0_left : ∑ U : WSub n (m + 1), c U * downOp n (m + 1) (upOp n (m + 1) c) U = 0 := by
        have hadj := upOp_adjoint_downOp n (m + 1) c (upOp n (m + 1) c)
        conv_lhs at hadj => rw [hc]
        simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hadj
        calc ∑ U : WSub n (m + 1), c U * downOp n (m + 1) (upOp n (m + 1) c) U
            = ∑ U : WSub n (m + 1), downOp n (m + 1) (upOp n (m + 1) c) U * c U := by
              refine Finset.sum_congr rfl fun U _ => mul_comm _ _
          _ = 0 := hadj.symm
      have hnonneg : 0 ≤ ∑ U : WSub n (m + 1), c U * upOp n m (downOp n m c) U := by
        have hadj := upOp_adjoint_downOp n m (downOp n m c) c
        calc (0 : ℝ) ≤ ∑ T : WSub n m, (downOp n m c T) ^ 2 :=
              Finset.sum_nonneg fun T _ => sq_nonneg _
          _ = ∑ T : WSub n m, downOp n m c T * downOp n m c T := by
              refine Finset.sum_congr rfl fun T _ => sq _
          _ = ∑ U : WSub n (m + 1), c U * upOp n m (downOp n m c) U := hadj.symm
      simp_rw [mul_sub, Finset.sum_sub_distrib, h0_left, zero_sub] at hsum1
      have hle : ((n : ℝ) - 2 * ((m + 1 : ℕ) : ℝ)) * ∑ U : WSub n (m + 1), (c U) ^ 2 ≤ 0 := by
        linarith
      have hpos : 0 < (n : ℝ) - 2 * ((m + 1 : ℕ) : ℝ) := by
        have hlt_nat : 2 * (m + 1) < n := hr
        have hlt_real : ((2 * (m + 1) : ℕ) : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hlt_nat
        rw [Nat.cast_mul, Nat.cast_ofNat] at hlt_real
        linarith
      have hsq_le : ∑ U : WSub n (m + 1), (c U) ^ 2 ≤ 0 := by nlinarith
      have hsq_eq : ∑ U : WSub n (m + 1), (c U) ^ 2 = 0 :=
        le_antisymm hsq_le (Finset.sum_nonneg fun U _ => sq_nonneg _)
      rw [Finset.sum_eq_zero_iff_of_nonneg fun U _ => sq_nonneg (c U)] at hsq_eq
      ext U
      exact sq_eq_zero_iff.mp (hsq_eq U (Finset.mem_univ U))
  intro c₁ c₂ heq
  rw [← sub_eq_zero]
  apply hlin
  ext V
  have hdiff : upOp n r (c₁ - c₂) V = upOp n r c₁ V - upOp n r c₂ V := by
    simp only [upOp]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun U _ => ?_
    split_ifs <;> simp [Pi.sub_apply]
  rw [hdiff, heq, sub_self, Pi.zero_apply]

/-- Iterated up-incidence operator from level `k` to level `k + d`. -/
def iterUp (n k : ℕ) : (d : ℕ) → (WSub n k → ℝ) → (WSub n (k + d) → ℝ)
  | 0, c => c
  | d + 1, c => upOp n (k + d) (iterUp n k d c)

lemma iterUp_injective {n k d : ℕ} (hd : 2 * (k + d) ≤ n) :
    Function.Injective (iterUp n k d) := by
  induction d with
  | zero => exact Function.injective_id
  | succ d ih =>
    intro c₁ c₂ heq
    apply ih (by omega)
    exact upOp_injective (by omega) heq

lemma iterUp_eq {n k d : ℕ} (c : WSub n k → ℝ) (V : WSub n (k + d)) :
    iterUp n k d c V = (Nat.factorial d : ℝ) * ∑ U : WSub n k, if U.1 ⊆ V.1 then c U else 0 := by
  induction d with
  | zero =>
    simp only [iterUp, Nat.factorial_zero, Nat.cast_one, one_mul]
    let V' : WSub n k := ⟨V.1, by simpa using V.2⟩
    rw [Finset.sum_eq_single V']
    · simp [V']
    · intro U _ hUV
      rw [if_neg]
      intro hsub
      apply hUV
      exact Subtype.ext (Finset.eq_of_subset_of_card_le hsub (by rw [U.2, V'.2]))
    · intro h
      exact False.elim (h (Finset.mem_univ V'))
  | succ d ih =>
    simp only [iterUp, upOp]
    have h1 : (∑ T : WSub n (k + d), if T.1 ⊆ V.1 then iterUp n k d c T else 0) =
        ∑ T : WSub n (k + d), if T.1 ⊆ V.1 then
          (Nat.factorial d : ℝ) * ∑ U : WSub n k, if U.1 ⊆ T.1 then c U else 0 else 0 := by
      refine Finset.sum_congr rfl fun T _ => ?_
      split_ifs with hT
      · exact ih T
      · rfl
    rw [h1]
    have hswap : (∑ T : WSub n (k + d), if T.1 ⊆ V.1 then
          (Nat.factorial d : ℝ) * ∑ U : WSub n k, if U.1 ⊆ T.1 then c U else 0 else 0) =
        (Nat.factorial d : ℝ) * ∑ U : WSub n k,
          ((Finset.univ.filter fun T : WSub n (k + d) => U.1 ⊆ T.1 ∧ T.1 ⊆ V.1).card : ℝ) *
            c U := by
      have hpull : ∀ T : WSub n (k + d),
          (if T.1 ⊆ V.1 then (Nat.factorial d : ℝ) * ∑ U : WSub n k,
            if U.1 ⊆ T.1 then c U else 0 else 0) =
          (Nat.factorial d : ℝ) * ∑ U : WSub n k,
            if U.1 ⊆ T.1 ∧ T.1 ⊆ V.1 then c U else 0 := by
        intro T
        by_cases hT : T.1 ⊆ V.1
        · simp [hT]
        · simp [hT]
      simp_rw [hpull, ← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun U _ => ?_
      rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun T _ => ?_
      by_cases hUT : U.1 ⊆ T.1 ∧ T.1 ⊆ V.1 <;> simp [hUT]
    rw [hswap]
    have hcount : ∀ U : WSub n k,
        ((Finset.univ.filter fun T : WSub n (k + d) => U.1 ⊆ T.1 ∧ T.1 ⊆ V.1).card : ℝ) * c U =
          if U.1 ⊆ V.1 then ((d + 1 : ℕ) : ℝ) * c U else 0 := by
      intro U
      by_cases hUV : U.1 ⊆ V.1
      · rw [if_pos hUV]
        congr 1
        norm_cast
        have hbij : (Finset.univ.filter fun T : WSub n (k + d) => U.1 ⊆ T.1 ∧ T.1 ⊆ V.1).card =
            (Finset.powersetCard 1 (V.1 \ U.1)).card := by
          refine Finset.card_bij (fun T _ => V.1 \ T.1) ?_ ?_ ?_
          · intro T hT
            have hTV : T.1 ⊆ V.1 := (Finset.mem_filter.mp hT).2.2
            have hUT : U.1 ⊆ T.1 := (Finset.mem_filter.mp hT).2.1
            refine Finset.mem_powersetCard.mpr ⟨fun x hx => ?_, ?_⟩
            · exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,
                fun hxU => (Finset.mem_sdiff.mp hx).2 (hUT hxU)⟩
            · rw [Finset.card_sdiff_of_subset hTV, V.2, T.2]; omega
          · intro T₁ hT₁ T₂ hT₂ heq
            have h1 : T₁.1 ⊆ V.1 := (Finset.mem_filter.mp hT₁).2.2
            have h2 : T₂.1 ⊆ V.1 := (Finset.mem_filter.mp hT₂).2.2
            ext1
            have hs1 : V.1 \ (V.1 \ T₁.1) = T₁.1 := by
              ext x; simp only [Finset.mem_sdiff]; exact ⟨fun ⟨hxV, h⟩ => by_contra fun hx1 => h ⟨hxV, hx1⟩, fun hx1 => ⟨h1 hx1, fun ⟨_, h⟩ => h hx1⟩⟩
            have hs2 : V.1 \ (V.1 \ T₂.1) = T₂.1 := by
              ext x; simp only [Finset.mem_sdiff]; exact ⟨fun ⟨hxV, h⟩ => by_contra fun hx2 => h ⟨hxV, hx2⟩, fun hx2 => ⟨h2 hx2, fun ⟨_, h⟩ => h hx2⟩⟩
            rw [← hs1, ← hs2, heq]
          · intro D hD
            rcases Finset.mem_powersetCard.mp hD with ⟨hDsub, hDcard⟩
            have hDV : D ⊆ V.1 := fun x hx => (Finset.mem_sdiff.mp (hDsub hx)).1
            have hdisj : Disjoint D U.1 := by
              rw [Finset.disjoint_left]
              intro x hxD hxU
              exact (Finset.mem_sdiff.mp (hDsub hxD)).2 hxU
            have hTcard : (V.1 \ D).card = k + d := by
              rw [Finset.card_sdiff_of_subset hDV, V.2, hDcard]; omega
            refine ⟨⟨V.1 \ D, hTcard⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              ⟨fun x hxU => Finset.mem_sdiff.mpr ⟨hUV hxU, fun hxD => Finset.disjoint_left.mp hdisj hxD hxU⟩,
               Finset.sdiff_subset⟩⟩, ?_⟩
            ext x; simp only [Finset.mem_sdiff]; exact ⟨fun ⟨hxV, h⟩ => by_contra fun hxD => h ⟨hxV, hxD⟩, fun hxD => ⟨hDV hxD, fun ⟨_, h⟩ => h hxD⟩⟩
        rw [hbij, Finset.card_powersetCard, Finset.card_sdiff_of_subset hUV, V.2, U.2,
          Nat.choose_one_right]
        omega
      · rw [if_neg hUV]
        have hfilt : (Finset.univ.filter fun T : WSub n (k + d) => U.1 ⊆ T.1 ∧ T.1 ⊆ V.1) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro T _ ⟨hUT, hTV⟩
          exact hUV (Finset.Subset.trans hUT hTV)
        rw [hfilt]
        simp
    simp_rw [hcount]
    have hpull : (∑ U : WSub n k, if U.1 ⊆ V.1 then ((d + 1 : ℕ) : ℝ) * c U else 0) =
        ((d + 1 : ℕ) : ℝ) * ∑ U : WSub n k, if U.1 ⊆ V.1 then c U else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun U _ => ?_
      split_ifs <;> ring
    rw [hpull, ← mul_assoc, ← Nat.cast_mul, mul_comm (Nat.factorial d) (d + 1),
      ← Nat.factorial_succ]

lemma indVec_linearIndependent {n w k : ℕ} (hk : k ≤ w) (hwn : 2 * w ≤ n) :
    LinearIndependent ℝ (fun U : WSub n k => indVec n w U.1) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let d := w - k
  have hd : k + d = w := Nat.add_sub_cancel' hk
  have hzero_up : iterUp n k d c = 0 := by
    ext V
    rw [iterUp_eq, Pi.zero_apply]
    let A : WSub n w := ⟨V.1, by rw [V.2, hd]⟩
    have hA : (∑ U : WSub n k, c U • indVec n w U.1) A = 0 := by
      rw [hc]; rfl
    rw [eucl_sum_apply] at hA
    simp only [PiLp.smul_apply, smul_eq_mul, indVec] at hA
    have hsum : (∑ U : WSub n k, if U.1 ⊆ V.1 then c U else 0) = 0 := by
      have hcongr : (∑ U : WSub n k, if U.1 ⊆ V.1 then c U else 0) =
          ∑ U : WSub n k, c U * if U.1 ⊆ A.1 then 1 else 0 := by
        refine Finset.sum_congr rfl fun U _ => ?_
        by_cases hUV : U.1 ⊆ V.1 <;> simp [A, hUV]
      rw [hcongr, hA]
    rw [hsum, mul_zero]
  have hzero_id : iterUp n k d (0 : WSub n k → ℝ) = 0 := by
    ext V
    rw [iterUp_eq]
    simp
  have hcd : c = 0 := iterUp_injective (by omega : 2 * (k + d) ≤ n) (hzero_up.trans hzero_id.symm)
  intro U
  exact congr_fun hcd U

lemma HSub_finrank {n w k : ℕ} (hk : k ≤ w) (hwn : 2 * w ≤ n) :
    Module.finrank ℝ (HSub n w k) = Nat.choose n k := by
  have hset : { v | ∃ U : Finset (Fin n), U.card = k ∧ v = indVec n w U } =
      Set.range (fun U : WSub n k => indVec n w U.1) := by
    ext v
    constructor
    · rintro ⟨U, hU, rfl⟩
      exact ⟨⟨U, hU⟩, rfl⟩
    · rintro ⟨⟨U, hU⟩, rfl⟩
      exact ⟨U, hU, rfl⟩
  have hspan : HSub n w k = Submodule.span ℝ (Set.range fun U : WSub n k => indVec n w U.1) := by
    simp only [HSub, hset]
  rw [hspan, finrank_span_eq_card (indVec_linearIndependent hk hwn), card_wsub]

lemma VSub_finrank {n w k : ℕ} (hk : k ≤ w) (hwn : 2 * w ≤ n) :
    Module.finrank ℝ (VSub n w k) =
      Nat.choose n k - if k = 0 then 0 else Nat.choose n (k - 1) := by
  cases k with
  | zero =>
    change Module.finrank ℝ (HSub n w 0) = Nat.choose n 0 - 0
    rw [HSub_finrank hk hwn, Nat.sub_zero]
  | succ m =>
    have hadd := Submodule.finrank_add_inf_finrank_orthogonal (HSub_step (n := n) hk)
    have hH1 := HSub_finrank (by omega : m ≤ w) hwn
    have hH2 := HSub_finrank hk hwn
    change Module.finrank ℝ (HSub n w m) + Module.finrank ℝ ↥((HSub n w m)ᗮ ⊓ HSub n w (m + 1)) =
      Module.finrank ℝ (HSub n w (m + 1)) at hadd
    rw [inf_comm] at hadd
    change Module.finrank ℝ (HSub n w m) + Module.finrank ℝ (VSub n w (m + 1)) =
      Module.finrank ℝ (HSub n w (m + 1)) at hadd
    rw [hH1, hH2] at hadd
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    omega

/-- Eigenvalue of `jAdjMatrix n w` on `VSub n w k`. -/
def jTheta (n w k : ℕ) : ℝ :=
  ((w : ℝ) - k) * ((n : ℝ) - w - k) - k

lemma jAdjMatrix_mulVec_indVec {n w k : ℕ} {U : Finset (Fin n)}
    (hU : U.card = k) (hk : k ≤ w) (hw : w ≤ n) :
    WithLp.toLp 2 (jAdjMatrix n w *ᵥ indVec n w U) =
      jTheta n w k • indVec n w U +
        ((w - k + 1 : ℕ) : ℝ) • ∑ u ∈ U, indVec n w (U.erase u) := by
  ext A
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, indVec, PiLp.toLp_apply,
    Matrix.mulVec, dotProduct, jAdjMatrix]
  rw [eucl_sum_apply]
  have hlhs : (∑ B : WSub n w, (if jDist A B = 1 then (1 : ℝ) else 0) *
      if U ⊆ B.1 then 1 else 0) =
      ((Finset.univ.filter fun B : WSub n w => jDist A B = 1 ∧ U ⊆ B.1).card : ℝ) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun B _ => ?_
    by_cases h1 : jDist A B = 1 <;> by_cases h2 : U ⊆ B.1 <;> simp [h1, h2]
  rw [hlhs]
  have h1s : (Finset.univ.filter fun B : WSub n w => jDist A B = 1 ∧ U ⊆ B.1) =
      Finset.univ.filter fun B : WSub n w =>
        (∃ a ∈ A.1, ∃ b ∈ Finset.univ \ A.1, B.1 = insert b (A.1.erase a)) ∧ U ⊆ B.1 := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine and_congr_left fun _ => ?_
    constructor
    · intro h1
      have hsym : (B.1 \ A.1).card = 1 := by
        change jDist B A = 1
        rw [jDist_symm]
        exact h1
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
      obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hsym
      have haA : a ∈ A.1 := (Finset.mem_sdiff.mp (ha ▸ Finset.mem_singleton_self a)).1
      have haB : a ∉ B.1 := (Finset.mem_sdiff.mp (ha ▸ Finset.mem_singleton_self a)).2
      have hbB : b ∈ B.1 := (Finset.mem_sdiff.mp (hb ▸ Finset.mem_singleton_self b)).1
      have hbA : b ∉ A.1 := (Finset.mem_sdiff.mp (hb ▸ Finset.mem_singleton_self b)).2
      refine ⟨a, haA, b, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hbA⟩, ?_⟩
      ext x
      simp only [Finset.mem_insert, Finset.mem_erase]
      constructor
      · intro hx
        by_cases hxb : x = b
        · exact Or.inl hxb
        · right
          have hxA : x ∈ A.1 := by
            by_contra hxnA
            have hx_in : x ∈ B.1 \ A.1 := Finset.mem_sdiff.mpr ⟨hx, hxnA⟩
            rw [hb, Finset.mem_singleton] at hx_in
            exact hxb hx_in
          have hxa : x ≠ a := fun h => haB (h ▸ hx)
          exact ⟨hxa, hxA⟩
      · rintro (rfl | ⟨hxa, hxA⟩)
        · exact hbB
        · by_contra hxnB
          have hx_in : x ∈ A.1 \ B.1 := Finset.mem_sdiff.mpr ⟨hxA, hxnB⟩
          rw [ha, Finset.mem_singleton] at hx_in
          exact hxa hx_in
    · rintro ⟨a, haA, b, hbA, hB⟩
      have hbnotA : b ∉ A.1 := (Finset.mem_sdiff.mp hbA).2
      have hAB : A.1 \ B.1 = {a} := by
        ext x
        rw [hB, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
        constructor
        · rintro ⟨hxA, hnx⟩
          by_contra hxa
          exact hnx (Or.inr ⟨hxa, hxA⟩)
        · rintro rfl
          refine ⟨haA, fun h => ?_⟩
          rcases h with rfl | ⟨h, _⟩
          · exact hbnotA haA
          · exact h rfl
      dsimp [jDist]
      rw [hAB, Finset.card_singleton]
  rw [h1s]
  by_cases hUA : U ⊆ A.1
  · have hbij : ((A.1 \ U) ×ˢ (Finset.univ \ A.1)).card =
        (Finset.univ.filter fun B : WSub n w =>
          (∃ a ∈ A.1, ∃ b ∈ Finset.univ \ A.1, B.1 = insert b (A.1.erase a)) ∧ U ⊆ B.1).card := by
      refine Finset.card_bij (fun p hp => ⟨insert p.2 (A.1.erase p.1), by
        have haA : p.1 ∈ A.1 := (Finset.mem_sdiff.mp (Finset.mem_product.mp hp).1).1
        have hbA : p.2 ∉ A.1 := (Finset.mem_sdiff.mp (Finset.mem_product.mp hp).2).2
        have hbne : p.2 ∉ A.1.erase p.1 := fun h => hbA (Finset.erase_subset _ _ h)
        rw [Finset.card_insert_of_notMem hbne, Finset.card_erase_of_mem haA, A.2]
        have hw1 : 1 ≤ w := by rw [← A.2]; exact Finset.card_pos.mpr ⟨p.1, haA⟩
        omega⟩) ?_ ?_ ?_
      · intro p hp
        rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
        have haA : p.1 ∈ A.1 := (Finset.mem_sdiff.mp hp1).1
        have haU : p.1 ∉ U := (Finset.mem_sdiff.mp hp1).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p.1, haA, p.2, hp2, rfl⟩, ?_⟩
        intro u hu
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun h => haU (h ▸ hu), hUA hu⟩)
      · intro p₁ hp₁ p₂ hp₂ heq
        have hp1A : p₁.1 ∈ A.1 := (Finset.mem_sdiff.mp (Finset.mem_product.mp hp₁).1).1
        have hp1B : p₁.2 ∉ A.1 := (Finset.mem_sdiff.mp (Finset.mem_product.mp hp₁).2).2
        have hp2A : p₂.1 ∈ A.1 := (Finset.mem_sdiff.mp (Finset.mem_product.mp hp₂).1).1
        have hp2B : p₂.2 ∉ A.1 := (Finset.mem_sdiff.mp (Finset.mem_product.mp hp₂).2).2
        have hval : insert p₁.2 (A.1.erase p₁.1) = insert p₂.2 (A.1.erase p₂.1) :=
          congr_arg Subtype.val heq
        have hb_eq : p₁.2 = p₂.2 := by
          have hmem : p₁.2 ∈ insert p₂.2 (A.1.erase p₂.1) := by
            rw [← hval]; exact Finset.mem_insert_self _ _
          rcases Finset.mem_insert.mp hmem with h | h
          · exact h
          · exact False.elim (hp1B (Finset.erase_subset _ _ h))
        have ha_eq : p₁.1 = p₂.1 := by
          by_contra hne
          have hmem : p₁.1 ∈ insert p₂.2 (A.1.erase p₂.1) :=
            Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, hp1A⟩)
          rw [← hval] at hmem
          rcases Finset.mem_insert.mp hmem with h | h
          · exact hp1B (h ▸ hp1A)
          · exact (Finset.mem_erase.mp h).1 rfl
        exact Prod.ext ha_eq hb_eq
      · intro B hB
        rcases (Finset.mem_filter.mp hB).2 with ⟨⟨a, haA, b, hbA, hBeq⟩, hUB⟩
        have haU : a ∉ U := by
          intro haU
          have haB : a ∈ B.1 := hUB haU
          rw [hBeq] at haB
          rcases Finset.mem_insert.mp haB with rfl | h
          · exact (Finset.mem_sdiff.mp hbA).2 haA
          · exact (Finset.mem_erase.mp h).1 rfl
        refine ⟨(a, b), Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨haA, haU⟩, hbA⟩, ?_⟩
        exact Subtype.ext hBeq.symm
    rw [← hbij, Finset.card_product, Finset.card_sdiff_of_subset hUA,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      A.2, hU]
    have hrhs_sum : (∑ u ∈ U, if U.erase u ⊆ A.1 then (1 : ℝ) else 0) = (k : ℝ) := by
      calc ∑ u ∈ U, (if U.erase u ⊆ A.1 then (1 : ℝ) else 0)
          = ∑ _ ∈ U, (1 : ℝ) :=
            Finset.sum_congr rfl fun u _ => if_pos (Finset.Subset.trans (Finset.erase_subset u U) hUA)
        _ = (k : ℝ) := by simp [hU]
    rw [if_pos hUA, hrhs_sum, jTheta, Nat.cast_mul, Nat.cast_sub hk, Nat.cast_sub hw,
      Nat.cast_add, Nat.cast_sub hk, Nat.cast_one]
    ring
  · by_cases h1 : (U \ A.1).card = 1
    · obtain ⟨u₀, hu₀⟩ := Finset.card_eq_one.mp h1
      have hu₀U : u₀ ∈ U := (Finset.mem_sdiff.mp (hu₀ ▸ Finset.mem_singleton_self u₀)).1
      have hu₀A : u₀ ∉ A.1 := (Finset.mem_sdiff.mp (hu₀ ▸ Finset.mem_singleton_self u₀)).2
      have hU_erase_sub : U.erase u₀ ⊆ A.1 := by
        intro u hu
        rcases Finset.mem_erase.mp hu with ⟨hune, huU⟩
        by_contra hunA
        have hmem : u ∈ U \ A.1 := Finset.mem_sdiff.mpr ⟨huU, hunA⟩
        rw [hu₀, Finset.mem_singleton] at hmem
        exact hune hmem
      have hinter_card : (A.1 ∩ U).card = k - 1 := by
        have hs := Finset.card_sdiff_add_card_inter U A.1
        rw [U.card_sdiff_add_card_inter] at *
        have hs2 : (U \ A.1).card + (U ∩ A.1).card = U.card := Finset.card_sdiff_add_card_inter U A.1
        rw [h1, hU, Finset.inter_comm] at hs2
        omega
      have hbij : (A.1 \ U).card =
          (Finset.univ.filter fun B : WSub n w =>
            (∃ a ∈ A.1, ∃ b ∈ Finset.univ \ A.1, B.1 = insert b (A.1.erase a)) ∧ U ⊆ B.1).card := by
        refine Finset.card_bij (fun a ha => ⟨insert u₀ (A.1.erase a), by
          have haA : a ∈ A.1 := (Finset.mem_sdiff.mp ha).1
          have hne : u₀ ∉ A.1.erase a := fun h => hu₀A (Finset.erase_subset _ _ h)
          rw [Finset.card_insert_of_notMem hne, Finset.card_erase_of_mem haA, A.2]
          have hw1 : 1 ≤ w := by rw [← A.2]; exact Finset.card_pos.mpr ⟨a, haA⟩
          omega⟩) ?_ ?_ ?_
        · intro a ha
          have haA : a ∈ A.1 := (Finset.mem_sdiff.mp ha).1
          have haU : a ∉ U := (Finset.mem_sdiff.mp ha).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            ⟨a, haA, u₀, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu₀A⟩, rfl⟩, ?_⟩
          intro u hu
          by_cases hu0 : u = u₀
          · subst hu0; exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
              ⟨fun h => haU (h ▸ hu), hU_erase_sub (Finset.mem_erase.mpr ⟨hu0, hu⟩)⟩)
        · intro a₁ ha₁ a₂ ha₂ heq
          have hval : insert u₀ (A.1.erase a₁) = insert u₀ (A.1.erase a₂) :=
            congr_arg Subtype.val heq
          have ha1A : a₁ ∈ A.1 := (Finset.mem_sdiff.mp ha₁).1
          by_contra hne
          have hmem : a₁ ∈ insert u₀ (A.1.erase a₂) :=
            Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, ha1A⟩)
          rw [← hval] at hmem
          rcases Finset.mem_insert.mp hmem with h | h
          · exact hu₀A (h ▸ ha1A)
          · exact (Finset.mem_erase.mp h).1 rfl
        · intro B hB
          rcases (Finset.mem_filter.mp hB).2 with ⟨⟨a, haA, b, hbA, hBeq⟩, hUB⟩
          have hb_eq : b = u₀ := by
            have hu0B : u₀ ∈ B.1 := hUB hu₀U
            rw [hBeq] at hu0B
            rcases Finset.mem_insert.mp hu0B with h | h
            · exact h.symm
            · exact False.elim (hu₀A (Finset.erase_subset _ _ h))
          have haU : a ∉ U := by
            intro haU
            have haB : a ∈ B.1 := hUB haU
            rw [hBeq] at haB
            rcases Finset.mem_insert.mp haB with rfl | h
            · exact (Finset.mem_sdiff.mp hbA).2 haA
            · exact (Finset.mem_erase.mp h).1 rfl
          refine ⟨a, Finset.mem_sdiff.mpr ⟨haA, haU⟩, ?_⟩
          exact Subtype.ext (by rw [hBeq, hb_eq])
      rw [← hbij]
      have hcard_AU : (A.1 \ U).card = w - k + 1 := by
        have h := Finset.card_sdiff_add_card_inter A.1 U
        rw [A.2, hinter_card] at h
        have hk1 : 1 ≤ k := by
          rw [← hU]
          exact Finset.card_pos.mpr ⟨u₀, hu₀U⟩
        omega
      have hrhs_sum : (∑ u ∈ U, if U.erase u ⊆ A.1 then (1 : ℝ) else 0) = 1 := by
        rw [Finset.sum_eq_single u₀]
        · exact if_pos hU_erase_sub
        · intro u hu hune
          rw [if_neg]
          intro hsub
          exact hu₀A (hsub (Finset.mem_erase.mpr ⟨hune.symm, hu₀U⟩))
        · intro h; exact False.elim (h hu₀U)
      rw [hcard_AU, if_neg hUA, hrhs_sum]
      simp
    · have hge2 : 2 ≤ (U \ A.1).card := by
        have hpos : 0 < (U \ A.1).card := by
          rw [Finset.card_pos]
          obtain ⟨u, huU, huA⟩ := Finset.not_subset.mp hUA
          exact ⟨u, Finset.mem_sdiff.mpr ⟨huU, huA⟩⟩
        omega
      have hfilt : (Finset.univ.filter fun B : WSub n w =>
          (∃ a ∈ A.1, ∃ b ∈ Finset.univ \ A.1, B.1 = insert b (A.1.erase a)) ∧ U ⊆ B.1) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro B _ ⟨⟨a, _, b, _, hBeq⟩, hUB⟩
        have hsub : U \ A.1 ⊆ {b} := by
          intro x hx
          rcases Finset.mem_sdiff.mp hx with ⟨hxU, hxA⟩
          have hxB : x ∈ B.1 := hUB hxU
          rw [hBeq] at hxB
          rcases Finset.mem_insert.mp hxB with rfl | h
          · exact Finset.mem_singleton_self _
          · exact False.elim (hxA (Finset.erase_subset _ _ h))
        have hle := Finset.card_le_card hsub
        rw [Finset.card_singleton] at hle
        omega
      have hrhs_sum : (∑ u ∈ U, if U.erase u ⊆ A.1 then (1 : ℝ) else 0) = 0 := by
        refine Finset.sum_eq_zero fun u _ => ?_
        rw [if_neg]
        intro hsub
        have hsub' : U \ A.1 ⊆ {u} := by
          intro x hx
          rcases Finset.mem_sdiff.mp hx with ⟨hxU, hxA⟩
          by_contra hxu
          exact hxA (hsub (Finset.mem_erase.mpr ⟨fun h => hxu (Finset.mem_singleton.mpr h), hxU⟩))
        have hle := Finset.card_le_card hsub'
        rw [Finset.card_singleton] at hle
        omega
      rw [hfilt, Finset.card_empty, Nat.cast_zero, if_neg hUA, hrhs_sum]
      simp

lemma jAdjMatrix_mulVec_HSub {n w k : ℕ} (hk : k ≤ w) (hw : w ≤ n)
    {v : EuclideanSpace ℝ (WSub n w)} (hv : v ∈ HSub n w k) :
    WithLp.toLp 2 (jAdjMatrix n w *ᵥ v) ∈ HSub n w k ∧
      WithLp.toLp 2 (jAdjMatrix n w *ᵥ v) - jTheta n w k • v ∈
        (if k = 0 then (⊥ : Submodule ℝ (EuclideanSpace ℝ (WSub n w))) else HSub n w (k - 1)) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨U, hU, rfl⟩
    have hmul := jAdjMatrix_mulVec_indVec hU hk hw
    rw [hmul]
    cases k with
    | zero =>
      have hU0 : U = ∅ := Finset.card_eq_zero.mp hU
      subst hU0
      simp only [Finset.sum_empty, smul_zero, add_zero, ↓reduceIte]
      refine ⟨Submodule.smul_mem _ _ (indVec_mem_HSub rfl), ?_⟩
      simp
    | succ m =>
      have hsum_mem : ∑ u ∈ U, indVec n w (U.erase u) ∈ HSub n w m := by
        refine Submodule.sum_mem _ fun u hu => indVec_mem_HSub ?_
        rw [Finset.card_erase_of_mem hu, hU]
        omega
      have h1 : jTheta n w (m + 1) • indVec n w U +
          ((w - (m + 1) + 1 : ℕ) : ℝ) • ∑ u ∈ U, indVec n w (U.erase u) ∈ HSub n w (m + 1) :=
        Submodule.add_mem _ (Submodule.smul_mem _ _ (indVec_mem_HSub hU))
          (Submodule.smul_mem _ _ (HSub_step hk hsum_mem))
      refine ⟨h1, ?_⟩
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      have hsub : jTheta n w (m + 1) • indVec n w U +
          ((w - (m + 1) + 1 : ℕ) : ℝ) • ∑ u ∈ U, indVec n w (U.erase u) -
          jTheta n w (m + 1) • indVec n w U =
          ((w - (m + 1) + 1 : ℕ) : ℝ) • ∑ u ∈ U, indVec n w (U.erase u) := by abel
      rw [hsub]
      exact Submodule.smul_mem _ _ hsum_mem
  | zero =>
    simp
  | add x y _ _ ihx ihy =>
    have hlin : WithLp.toLp 2 (jAdjMatrix n w *ᵥ (x + y).ofLp) =
        WithLp.toLp 2 (jAdjMatrix n w *ᵥ x.ofLp) + WithLp.toLp 2 (jAdjMatrix n w *ᵥ y.ofLp) := by
      ext A
      change (jAdjMatrix n w *ᵥ (x.ofLp + y.ofLp)) A = _
      simp [Matrix.mulVec_add]
    rw [hlin]
    refine ⟨Submodule.add_mem _ ihx.1 ihy.1, ?_⟩
    have hsub : (WithLp.toLp 2 (jAdjMatrix n w *ᵥ x.ofLp) + WithLp.toLp 2 (jAdjMatrix n w *ᵥ y.ofLp)) -
        jTheta n w k • (x + y) =
        (WithLp.toLp 2 (jAdjMatrix n w *ᵥ x.ofLp) - jTheta n w k • x) +
        (WithLp.toLp 2 (jAdjMatrix n w *ᵥ y.ofLp) - jTheta n w k • y) := by
      rw [smul_add]; abel
    rw [hsub]
    exact Submodule.add_mem _ ihx.2 ihy.2
  | smul c x _ ih =>
    have hlin : WithLp.toLp 2 (jAdjMatrix n w *ᵥ (c • x).ofLp) =
        c • WithLp.toLp 2 (jAdjMatrix n w *ᵥ x.ofLp) := by
      ext A
      change (jAdjMatrix n w *ᵥ (c • x.ofLp)) A = _
      simp [Matrix.mulVec_smul]
    rw [hlin]
    refine ⟨Submodule.smul_mem _ _ ih.1, ?_⟩
    have hsub : c • WithLp.toLp 2 (jAdjMatrix n w *ᵥ x.ofLp) - jTheta n w k • (c • x) =
        c • (WithLp.toLp 2 (jAdjMatrix n w *ᵥ x.ofLp) - jTheta n w k • x) := by
      rw [smul_sub, smul_comm]
    rw [hsub]
    exact Submodule.smul_mem _ _ ih.2

lemma jAdjMatrix_mulVec_VSub {n w k : ℕ} (hk : k ≤ w) (hw : w ≤ n)
    {v : EuclideanSpace ℝ (WSub n w)} (hv : v ∈ VSub n w k) :
    WithLp.toLp 2 (jAdjMatrix n w *ᵥ v) = jTheta n w k • v := by
  have hvH : v ∈ HSub n w k := VSub_le_HSub n w k hv
  have hmem := (jAdjMatrix_mulVec_HSub hk hw hvH).2
  cases k with
  | zero =>
    simp only [↓reduceIte, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  | succ m =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel] at hmem
    have horth : WithLp.toLp 2 (jAdjMatrix n w *ᵥ v) - jTheta n w (m + 1) • v ∈ (HSub n w m)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro h hh
      have hvO : v ∈ (HSub n w m)ᗮ := (Submodule.mem_inf.mp hv).2
      have h1 : inner ℝ h v = 0 := (Submodule.mem_orthogonal _ _).mp hvO h hh
      have hh' : WithLp.toLp 2 (jAdjMatrix n w *ᵥ h) ∈ HSub n w m :=
        (jAdjMatrix_mulVec_HSub (by omega) hw hh).1
      have h2 : inner ℝ (WithLp.toLp 2 (jAdjMatrix n w *ᵥ h)) v = 0 :=
        (Submodule.mem_orthogonal _ _).mp hvO _ hh'
      have hsym : inner ℝ h (WithLp.toLp 2 (jAdjMatrix n w *ᵥ v)) =
          inner ℝ (WithLp.toLp 2 (jAdjMatrix n w *ᵥ h)) v := by
        simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Matrix.mulVec, dotProduct]
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
        rw [jAdjMatrix_symm n w A B]
        ring
      rw [inner_sub_right, inner_smul_right, hsym, h2, h1, mul_zero, sub_zero]
    have hinner0 : inner ℝ (WithLp.toLp 2 (jAdjMatrix n w *ᵥ v) - jTheta n w (m + 1) • v)
        (WithLp.toLp 2 (jAdjMatrix n w *ᵥ v) - jTheta n w (m + 1) • v) = 0 :=
      (Submodule.mem_orthogonal _ _).mp horth _ hmem
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hinner0)

lemma jAdjMatrix_mul_projMat {n w k : ℕ} (hk : k ≤ w) (hw : w ≤ n) :
    jAdjMatrix n w * projMat n w k = jTheta n w k • projMat n w k := by
  ext A B
  simp only [Matrix.mul_apply, projMat, opToMatrix, Matrix.smul_apply, smul_eq_mul]
  have hcol : (VSub n w k).starProjection (EuclideanSpace.basisFun (WSub n w) ℝ B) ∈ VSub n w k :=
    Submodule.starProjection_apply_mem _ _
  have heq := congr_arg (fun v : EuclideanSpace ℝ (WSub n w) => v A)
    (jAdjMatrix_mulVec_VSub hk hw hcol)
  simpa [Matrix.mulVec, dotProduct] using heq

/-- Permutation action of `S_n` on `WSub n w`. -/
def permWSub (n w : ℕ) (σ : Equiv.Perm (Fin n)) : WSub n w ≃ WSub n w where
  toFun A := ⟨A.1.map σ.toEmbedding, by simp [A.2]⟩
  invFun A := ⟨A.1.map σ.symm.toEmbedding, by simp [A.2]⟩
  left_inv A := by
    ext x
    simp only [Finset.mem_map, Equiv.coe_toEmbedding]
    exact ⟨by rintro ⟨y, ⟨z, hz, rfl⟩, hy⟩; simpa [← hy] using hz,
      fun hx => ⟨σ x, ⟨x, hx, rfl⟩, σ.symm_apply_apply x⟩⟩
  right_inv A := by
    ext x
    simp only [Finset.mem_map, Equiv.coe_toEmbedding]
    exact ⟨by rintro ⟨y, ⟨z, hz, rfl⟩, hy⟩; simpa [← hy] using hz,
      fun hx => ⟨σ.symm x, ⟨x, hx, rfl⟩, σ.apply_symm_apply x⟩⟩

/-- Linear isometry of `EuclideanSpace ℝ (WSub n w)` induced by `σ : Equiv.Perm (Fin n)`. -/
noncomputable def permIso (n w : ℕ) (σ : Equiv.Perm (Fin n)) :
    EuclideanSpace ℝ (WSub n w) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (WSub n w) :=
  (EuclideanSpace.basisFun (WSub n w) ℝ).equiv
    (EuclideanSpace.basisFun (WSub n w) ℝ) (permWSub n w σ)

lemma permIso_apply {n w : ℕ} (σ : Equiv.Perm (Fin n)) (v : EuclideanSpace ℝ (WSub n w))
    (A : WSub n w) :
    permIso n w σ v (permWSub n w σ A) = v A := by
  dsimp [permIso]
  rw [OrthonormalBasis.equiv_apply, eucl_sum_apply]
  simp only [PiLp.smul_apply, smul_eq_mul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, PiLp.single_apply]
  rw [Finset.sum_eq_single A]
  · simp
  · intro B _ hBA
    rw [if_neg (fun h => hBA ((permWSub n w σ).injective h.symm)), mul_zero]
  · intro h; exact False.elim (h (Finset.mem_univ A))

lemma permIso_indVec {n w : ℕ} (σ : Equiv.Perm (Fin n)) (U : Finset (Fin n)) :
    permIso n w σ (indVec n w U) = indVec n w (U.map σ.toEmbedding) := by
  ext B
  obtain ⟨A, rfl⟩ := (permWSub n w σ).surjective B
  rw [permIso_apply]
  simp only [indVec, PiLp.toLp_apply]
  have hiff : U ⊆ A.1 ↔ U.map σ.toEmbedding ⊆ (permWSub n w σ A).1 :=
    Finset.map_subset_map.symm
  by_cases h : U ⊆ A.1
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (mt hiff.mpr h)]

lemma permIso_mem_HSub {n w k : ℕ} (σ : Equiv.Perm (Fin n)) {v : EuclideanSpace ℝ (WSub n w)}
    (hv : v ∈ HSub n w k) : permIso n w σ v ∈ HSub n w k := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨U, hU, rfl⟩
    rw [permIso_indVec]
    exact indVec_mem_HSub (by simp [hU])
  | zero => simp
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x _ ih => rw [map_smul]; exact Submodule.smul_mem _ _ ih

lemma permIso_mem_VSub {n w k : ℕ} (σ : Equiv.Perm (Fin n)) {v : EuclideanSpace ℝ (WSub n w)}
    (hv : v ∈ VSub n w k) : permIso n w σ v ∈ VSub n w k := by
  cases k with
  | zero => exact permIso_mem_HSub σ hv
  | succ m =>
    refine Submodule.mem_inf.mpr ⟨permIso_mem_HSub σ (Submodule.mem_inf.mp hv).1, ?_⟩
    rw [Submodule.mem_orthogonal]
    intro u hu
    have hsymm : (permIso n w σ).symm u ∈ HSub n w m := by
      have heq : (permIso n w σ).symm = permIso n w σ.symm := by
        apply (EuclideanSpace.basisFun (WSub n w) ℝ).toBasis.ext_linearIsometryEquiv
        intro A
        simp [permIso, permWSub]
      rw [heq]
      exact permIso_mem_HSub σ.symm hu
    have hinner : inner ℝ u (permIso n w σ v) =
        inner ℝ ((permIso n w σ).symm u) v := by
      calc inner ℝ u (permIso n w σ v)
          = inner ℝ (permIso n w σ ((permIso n w σ).symm u)) (permIso n w σ v) := by
            rw [LinearIsometryEquiv.apply_symm_apply]
        _ = inner ℝ ((permIso n w σ).symm u) v := (permIso n w σ).inner_map_map _ _
    rw [hinner]
    exact (Submodule.mem_orthogonal _ _).mp (Submodule.mem_inf.mp hv).2 _ hsymm

lemma permIso_starProjection {n w k : ℕ} (σ : Equiv.Perm (Fin n))
    (v : EuclideanSpace ℝ (WSub n w)) :
    (VSub n w k).starProjection (permIso n w σ v) =
      permIso n w σ ((VSub n w k).starProjection v) := by
  refine (VSub n w k).eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · exact permIso_mem_VSub σ (Submodule.starProjection_apply_mem _ _)
  · intro u hu
    have hsymm : (permIso n w σ).symm u ∈ VSub n w k := by
      have heq : (permIso n w σ).symm = permIso n w σ.symm := by
        apply (EuclideanSpace.basisFun (WSub n w) ℝ).toBasis.ext_linearIsometryEquiv
        intro A
        simp [permIso, permWSub]
      rw [heq]
      exact permIso_mem_VSub σ.symm hu
    have hsub : permIso n w σ v - permIso n w σ ((VSub n w k).starProjection v) =
        permIso n w σ (v - (VSub n w k).starProjection v) := (map_sub _ _ _).symm
    rw [hsub]
    calc inner ℝ (permIso n w σ (v - (VSub n w k).starProjection v)) u
        = inner ℝ (permIso n w σ (v - (VSub n w k).starProjection v))
            (permIso n w σ ((permIso n w σ).symm u)) := by
          rw [LinearIsometryEquiv.apply_symm_apply]
      _ = inner ℝ (v - (VSub n w k).starProjection v) ((permIso n w σ).symm u) :=
          (permIso n w σ).inner_map_map _ _
      _ = 0 := (VSub n w k).starProjection_inner_eq_zero _ _ hsymm

lemma projMat_perm {n w k : ℕ} (σ : Equiv.Perm (Fin n)) (A B : WSub n w) :
    projMat n w k (permWSub n w σ A) (permWSub n w σ B) = projMat n w k A B := by
  simp only [projMat, opToMatrix]
  have hB : EuclideanSpace.basisFun (WSub n w) ℝ (permWSub n w σ B) =
      permIso n w σ (EuclideanSpace.basisFun (WSub n w) ℝ B) := by
    dsimp [permIso]
    exact (OrthonormalBasis.equiv_apply_basis _ _ _ B).symm
  rw [hB, permIso_starProjection, permIso_apply]

/-- Four-part partition of `Fin n` relative to `(A, B)`. -/
def fourPartEquiv {n w : ℕ} (A B : WSub n w) :
    Fin n ≃
      ({ x : Fin n // x ∈ A.1 ∩ B.1 } ⊕ { x : Fin n // x ∈ A.1 \ B.1 }) ⊕
      ({ x : Fin n // x ∈ B.1 \ A.1 } ⊕ { x : Fin n // x ∈ Finset.univ \ (A.1 ∪ B.1) }) where
  toFun x :=
    if hxA : x ∈ A.1 then
      if hxB : x ∈ B.1 then
        Sum.inl (Sum.inl ⟨x, Finset.mem_inter.mpr ⟨hxA, hxB⟩⟩)
      else
        Sum.inl (Sum.inr ⟨x, Finset.mem_sdiff.mpr ⟨hxA, hxB⟩⟩)
    else
      if hxB : x ∈ B.1 then
        Sum.inr (Sum.inl ⟨x, Finset.mem_sdiff.mpr ⟨hxB, hxA⟩⟩)
      else
        Sum.inr (Sum.inr ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
          fun h => (Finset.mem_union.mp h).elim hxA hxB⟩⟩)
  invFun y :=
    match y with
    | Sum.inl (Sum.inl x) => x.1
    | Sum.inl (Sum.inr x) => x.1
    | Sum.inr (Sum.inl x) => x.1
    | Sum.inr (Sum.inr x) => x.1
  left_inv x := by
    by_cases hxA : x ∈ A.1 <;> by_cases hxB : x ∈ B.1 <;> simp [hxA, hxB]
  right_inv y := by
    rcases y with (⟨x, hx⟩ | ⟨x, hx⟩) | (⟨x, hx⟩ | ⟨x, hx⟩)
    · simp only [Finset.mem_inter] at hx
      simp [hx.1, hx.2]
    · simp only [Finset.mem_sdiff] at hx
      simp [hx.1, hx.2]
    · simp only [Finset.mem_sdiff] at hx
      simp [hx.1, hx.2]
    · simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or] at hx
      simp [hx.1, hx.2]

lemma perm_pair_exists {n w : ℕ} {A₁ B₁ A₂ B₂ : WSub n w}
    (hdist : jDist A₁ B₁ = jDist A₂ B₂) :
    ∃ σ : Equiv.Perm (Fin n), permWSub n w σ A₁ = A₂ ∧ permWSub n w σ B₁ = B₂ := by
  have hc1 : Fintype.card { x : Fin n // x ∈ A₁.1 ∩ B₁.1 } =
      Fintype.card { x : Fin n // x ∈ A₂.1 ∩ B₂.1 } := by
    simp only [Fintype.card_coe, card_inter_wsub, hdist]
  have hc2 : Fintype.card { x : Fin n // x ∈ A₁.1 \ B₁.1 } =
      Fintype.card { x : Fin n // x ∈ A₂.1 \ B₂.1 } := by
    simp only [Fintype.card_coe]
    exact hdist
  have hc3 : Fintype.card { x : Fin n // x ∈ B₁.1 \ A₁.1 } =
      Fintype.card { x : Fin n // x ∈ B₂.1 \ A₂.1 } := by
    simp only [Fintype.card_coe]
    change jDist B₁ A₁ = jDist B₂ A₂
    rw [jDist_symm B₁ A₁, jDist_symm B₂ A₂, hdist]
  have hc4 : Fintype.card { x : Fin n // x ∈ Finset.univ \ (A₁.1 ∪ B₁.1) } =
      Fintype.card { x : Fin n // x ∈ Finset.univ \ (A₂.1 ∪ B₂.1) } := by
    simp only [Fintype.card_coe]
    have hs1 : (Finset.univ \ (A₁.1 ∪ B₁.1)).card = n - (A₁.1 ∪ B₁.1).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have hs2 : (Finset.univ \ (A₂.1 ∪ B₂.1)).card = n - (A₂.1 ∪ B₂.1).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have hu1 := Finset.card_union_add_card_inter A₁.1 B₁.1
    have hu2 := Finset.card_union_add_card_inter A₂.1 B₂.1
    rw [A₁.2, B₁.2, card_inter_wsub] at hu1
    rw [A₂.2, B₂.2, card_inter_wsub, ← hdist] at hu2
    omega
  let e1 : { x : Fin n // x ∈ A₁.1 ∩ B₁.1 } ≃ { x : Fin n // x ∈ A₂.1 ∩ B₂.1 } :=
    Fintype.equivOfCardEq (by convert hc1)
  let e2 : { x : Fin n // x ∈ A₁.1 \ B₁.1 } ≃ { x : Fin n // x ∈ A₂.1 \ B₂.1 } :=
    Fintype.equivOfCardEq (by convert hc2)
  let e3 : { x : Fin n // x ∈ B₁.1 \ A₁.1 } ≃ { x : Fin n // x ∈ B₂.1 \ A₂.1 } :=
    Fintype.equivOfCardEq (by convert hc3)
  let e4 : { x : Fin n // x ∈ Finset.univ \ (A₁.1 ∪ B₁.1) } ≃
      { x : Fin n // x ∈ Finset.univ \ (A₂.1 ∪ B₂.1) } :=
    Fintype.equivOfCardEq (by convert hc4)
  let σ : Equiv.Perm (Fin n) :=
    (fourPartEquiv A₁ B₁).trans (((e1.sumCongr e2).sumCongr (e3.sumCongr e4)).trans
      (fourPartEquiv A₂ B₂).symm)
  refine ⟨σ, ?_, ?_⟩
  · ext y
    simp only [permWSub, Equiv.coe_fn_mk, Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨x, hxA₁, rfl⟩
      by_cases hxB₁ : x ∈ B₁.1
      · have hmem := (e1 ⟨x, Finset.mem_inter.mpr ⟨hxA₁, hxB₁⟩⟩).2
        have hval : σ x = (e1 ⟨x, Finset.mem_inter.mpr ⟨hxA₁, hxB₁⟩⟩).1 := by
          simp [σ, fourPartEquiv, hxA₁, hxB₁]
        rw [hval]
        exact (Finset.mem_inter.mp hmem).1
      · have hmem := (e2 ⟨x, Finset.mem_sdiff.mpr ⟨hxA₁, hxB₁⟩⟩).2
        have hval : σ x = (e2 ⟨x, Finset.mem_sdiff.mpr ⟨hxA₁, hxB₁⟩⟩).1 := by
          simp [σ, fourPartEquiv, hxA₁, hxB₁]
        rw [hval]
        exact (Finset.mem_sdiff.mp hmem).1
    · intro hyA₂
      refine ⟨σ.symm y, ?_, σ.apply_symm_apply y⟩
      by_cases hyB₂ : y ∈ B₂.1
      · have hmem := (e1.symm ⟨y, Finset.mem_inter.mpr ⟨hyA₂, hyB₂⟩⟩).2
        have hval : σ.symm y = (e1.symm ⟨y, Finset.mem_inter.mpr ⟨hyA₂, hyB₂⟩⟩).1 := by
          simp [σ, fourPartEquiv, hyA₂, hyB₂]
        rw [hval]
        exact (Finset.mem_inter.mp hmem).1
      · have hmem := (e2.symm ⟨y, Finset.mem_sdiff.mpr ⟨hyA₂, hyB₂⟩⟩).2
        have hval : σ.symm y = (e2.symm ⟨y, Finset.mem_sdiff.mpr ⟨hyA₂, hyB₂⟩⟩).1 := by
          simp [σ, fourPartEquiv, hyA₂, hyB₂]
        rw [hval]
        exact (Finset.mem_sdiff.mp hmem).1
  · ext y
    simp only [permWSub, Equiv.coe_fn_mk, Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨x, hxB₁, rfl⟩
      by_cases hxA₁ : x ∈ A₁.1
      · have hmem := (e1 ⟨x, Finset.mem_inter.mpr ⟨hxA₁, hxB₁⟩⟩).2
        have hval : σ x = (e1 ⟨x, Finset.mem_inter.mpr ⟨hxA₁, hxB₁⟩⟩).1 := by
          simp [σ, fourPartEquiv, hxA₁, hxB₁]
        rw [hval]
        exact (Finset.mem_inter.mp hmem).2
      · have hmem := (e3 ⟨x, Finset.mem_sdiff.mpr ⟨hxB₁, hxA₁⟩⟩).2
        have hval : σ x = (e3 ⟨x, Finset.mem_sdiff.mpr ⟨hxB₁, hxA₁⟩⟩).1 := by
          simp [σ, fourPartEquiv, hxA₁, hxB₁]
        rw [hval]
        exact (Finset.mem_sdiff.mp hmem).1
    · intro hyB₂
      refine ⟨σ.symm y, ?_, σ.apply_symm_apply y⟩
      by_cases hyA₂ : y ∈ A₂.1
      · have hmem := (e1.symm ⟨y, Finset.mem_inter.mpr ⟨hyA₂, hyB₂⟩⟩).2
        have hval : σ.symm y = (e1.symm ⟨y, Finset.mem_inter.mpr ⟨hyA₂, hyB₂⟩⟩).1 := by
          simp [σ, fourPartEquiv, hyA₂, hyB₂]
        rw [hval]
        exact (Finset.mem_inter.mp hmem).2
      · have hmem := (e3.symm ⟨y, Finset.mem_sdiff.mpr ⟨hyB₂, hyA₂⟩⟩).2
        have hval : σ.symm y = (e3.symm ⟨y, Finset.mem_sdiff.mpr ⟨hyB₂, hyA₂⟩⟩).1 := by
          simp [σ, fourPartEquiv, hyA₂, hyB₂]
        rw [hval]
        exact (Finset.mem_sdiff.mp hmem).1

/-- Canonical `w`-subset `{0, ..., w-1}` in `Fin n`. -/
def canonA (n w : ℕ) (hw : w ≤ n) : WSub n w :=
  ⟨Finset.univ.filter fun i : Fin n => i.val < w, by
    have hbij : (Finset.univ.filter fun i : Fin n => i.val < w).card = (Finset.univ : Finset (Fin w)).card := by
      refine Finset.card_bij (fun i hi => ⟨i.val, (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_
      · intro i _; exact Finset.mem_univ _
      · intro i₁ _ i₂ _ h; exact Fin.ext (congr_arg (Fin.val : Fin w → ℕ) h)
      · intro j _
        refine ⟨⟨j.val, lt_of_lt_of_le j.isLt hw⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩, rfl⟩
    rw [hbij, Finset.card_univ, Fintype.card_fin]⟩

/-- Canonical shifted `w`-subset `{j, ..., w+j-1}` in `Fin n`. -/
def canonB (n w j : ℕ) (hwj : w + j ≤ n) : WSub n w :=
  ⟨Finset.univ.filter fun i : Fin n => j ≤ i.val ∧ i.val < w + j, by
    have hbij : (Finset.univ.filter fun i : Fin n => j ≤ i.val ∧ i.val < w + j).card =
        (Finset.univ : Finset (Fin w)).card := by
      refine Finset.card_bij (fun i hi => ⟨i.val - j, by
        have h := (Finset.mem_filter.mp hi).2
        omega⟩) ?_ ?_ ?_
      · intro i _; exact Finset.mem_univ _
      · intro i₁ hi₁ i₂ hi₂ h
        have h1 := (Finset.mem_filter.mp hi₁).2.1
        have h2 := (Finset.mem_filter.mp hi₂).2.1
        have hv : i₁.val - j = i₂.val - j := congr_arg (Fin.val : Fin w → ℕ) h
        exact Fin.ext (by omega)
      · intro k _
        refine ⟨⟨j + k.val, by have hk := k.isLt; omega⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            change j ≤ j + k.val ∧ j + k.val < w + j
            have hk := k.isLt
            omega⟩, ?_⟩
        apply Fin.ext
        change (j + k.val) - j = k.val
        exact Nat.add_sub_cancel_left j k.val
    rw [hbij, Finset.card_univ, Fintype.card_fin]⟩

lemma jDist_canon {n w j : ℕ} (hj : j ≤ w) (hwj : w + j ≤ n) :
    jDist (canonA n w (by omega)) (canonB n w j hwj) = j := by
  have hbij : (Finset.univ : Finset (Fin j)).card =
      ((canonA n w (by omega)).1 \ (canonB n w j hwj).1).card := by
    refine Finset.card_bij (fun k _ => ⟨k.val, by have hk := k.isLt; omega⟩) ?_ ?_ ?_
    · intro k _
      have hk := k.isLt
      simp only [canonA, canonB, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro k₁ _ k₂ _ h; exact Fin.ext (congr_arg (Fin.val : Fin n → ℕ) h)
    · intro i hi
      simp only [canonA, canonB, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      refine ⟨⟨i.val, by omega⟩, Finset.mem_univ _, rfl⟩
  change ((canonA n w (by omega)).1 \ (canonB n w j hwj).1).card = j
  rw [← hbij, Finset.card_univ, Fintype.card_fin]

/-- Common entry value `E_k(A, B)` when `jDist A B = j`. -/
noncomputable def eVal (n w k j : ℕ) : ℝ :=
  if h : j ≤ w ∧ w + j ≤ n then
    projMat n w k (canonA n w (by omega)) (canonB n w j h.2)
  else 0

lemma projMat_eq_eVal {n w k : ℕ} (A B : WSub n w) :
    projMat n w k A B = eVal n w k (jDist A B) := by
  have hj : jDist A B ≤ w := jDist_le A B
  have hwj : w + jDist A B ≤ n := jDist_add_le A B
  have hw : w ≤ n := by omega
  have hev : eVal n w k (jDist A B) =
      projMat n w k (canonA n w hw) (canonB n w (jDist A B) hwj) := by
    dsimp [eVal]
    exact dif_pos ⟨hj, hwj⟩
  rw [hev]
  have hdist : jDist (canonA n w hw) (canonB n w (jDist A B) hwj) = jDist A B :=
    jDist_canon hj hwj
  obtain ⟨σ, hσ1, hσ2⟩ := perm_pair_exists hdist
  have hlhs : projMat n w k A B =
      projMat n w k (permWSub n w σ (canonA n w hw))
        (permWSub n w σ (canonB n w (jDist A B) hwj)) := by
    rw [hσ1, hσ2]
  rw [hlhs]
  exact projMat_perm σ _ _

lemma eVal_zero {n w k : ℕ} (hk : k ≤ w) (hwn : 2 * w ≤ n) :
    eVal n w k 0 =
      ((Nat.choose n k - if k = 0 then 0 else Nat.choose n (k - 1) : ℕ) : ℝ) /
        (Nat.choose n w : ℝ) := by
  have htr := opToMatrix_starProjection_trace (VSub n w k)
  change ∑ A : WSub n w, projMat n w k A A = (Module.finrank ℝ (VSub n w k) : ℝ) at htr
  have hdiag : ∑ A : WSub n w, projMat n w k A A =
      (Nat.choose n w : ℝ) * eVal n w k 0 := by
    calc ∑ A : WSub n w, projMat n w k A A
        = ∑ A : WSub n w, eVal n w k 0 := by
          refine Finset.sum_congr rfl fun A _ => ?_
          rw [projMat_eq_eVal A A, jDist_eq_zero_iff.mpr rfl]
      _ = (Fintype.card (WSub n w) : ℝ) * eVal n w k 0 := by simp
      _ = (Nat.choose n w : ℝ) * eVal n w k 0 := by rw [card_wsub]
  rw [hdiag, VSub_finrank hk hwn] at htr
  have hpos : (0 : ℝ) < Nat.choose n w := by
    exact_mod_cast Nat.choose_pos (by omega : w ≤ n)
  exact (eq_div_iff (ne_of_gt hpos)).mpr (by rw [mul_comm]; exact htr)

lemma vj_mul_eVal_sq_le {n w k j : ℕ} (_hk : k ≤ w) (hwn : 2 * w ≤ n)
    (hj : j ≤ w) (_hwj : w + j ≤ n) :
    ((Nat.choose w j * Nat.choose (n - w) j : ℕ) : ℝ) * (eVal n w k j) ^ 2 ≤ eVal n w k 0 := by
  let A := canonA n w (by omega)
  have hidem := congr_fun (congr_fun (projMat_mul_self n w k) A) A
  simp only [Matrix.mul_apply] at hidem
  have hlhs : ∑ B : WSub n w, projMat n w k A B * projMat n w k B A =
      ∑ B : WSub n w, (eVal n w k (jDist A B)) ^ 2 := by
    refine Finset.sum_congr rfl fun B _ => ?_
    have hsym : projMat n w k B A = projMat n w k A B :=
      opToMatrix_starProjection_symm (VSub n w k) B A
    rw [hsym, projMat_eq_eVal A B, sq]
  have hrhs : projMat n w k A A = eVal n w k 0 := by
    rw [projMat_eq_eVal A A, jDist_eq_zero_iff.mpr rfl]
  rw [hlhs, hrhs] at hidem
  have hge : ∑ B ∈ Finset.univ.filter (fun B : WSub n w => jDist A B = j),
      (eVal n w k (jDist A B)) ^ 2 ≤ ∑ B : WSub n w, (eVal n w k (jDist A B)) ^ 2 :=
    Finset.sum_le_univ_sum_of_nonneg fun B => sq_nonneg _
  rw [hidem] at hge
  have hconst : ∑ B ∈ Finset.univ.filter (fun B : WSub n w => jDist A B = j),
      (eVal n w k (jDist A B)) ^ 2 =
      ((Finset.univ.filter (fun B : WSub n w => jDist A B = j)).card : ℝ) *
        (eVal n w k j) ^ 2 := by
    calc ∑ B ∈ Finset.univ.filter (fun B : WSub n w => jDist A B = j),
          (eVal n w k (jDist A B)) ^ 2
        = ∑ _ ∈ Finset.univ.filter (fun B : WSub n w => jDist A B = j), (eVal n w k j) ^ 2 :=
          Finset.sum_congr rfl fun B hB => by rw [(Finset.mem_filter.mp hB).2]
      _ = ((Finset.univ.filter (fun B : WSub n w => jDist A B = j)).card : ℝ) *
            (eVal n w k j) ^ 2 := by simp
  have hcard : (Finset.univ.filter (fun B : WSub n w => jDist A B = j)).card =
      Nat.choose w j * Nat.choose (n - w) j := by
    have hbij : (Finset.univ.filter (fun B : WSub n w => jDist A B = j)).card =
        (Finset.powersetCard (w - j) A.1 ×ˢ Finset.powersetCard j (Finset.univ \ A.1)).card := by
      refine Finset.card_bij (fun B _ => (A.1 ∩ B.1, B.1 \ A.1)) ?_ ?_ ?_
      · intro B hB
        have hjB : jDist A B = j := (Finset.mem_filter.mp hB).2
        refine Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_left, ?_⟩,
          Finset.mem_powersetCard.mpr ⟨?_, ?_⟩⟩
        · rw [card_inter_wsub, hjB]
        · intro x hx
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
        · change jDist B A = j
          rw [jDist_symm B A]
          exact hjB
      · intro B₁ _ B₂ _ heq
        have h1 : A.1 ∩ B₁.1 = A.1 ∩ B₂.1 := congr_arg Prod.fst heq
        have h2 : B₁.1 \ A.1 = B₂.1 \ A.1 := congr_arg Prod.snd heq
        ext1
        have hs1 : B₁.1 = (A.1 ∩ B₁.1) ∪ (B₁.1 \ A.1) := by
          ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
        have hs2 : B₂.1 = (A.1 ∩ B₂.1) ∪ (B₂.1 \ A.1) := by
          ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
        rw [hs1, hs2, h1, h2]
      · rintro ⟨U, V⟩ hUV
        rcases Finset.mem_product.mp hUV with ⟨hU, hV⟩
        rcases Finset.mem_powersetCard.mp hU with ⟨hUA, hUcard⟩
        rcases Finset.mem_powersetCard.mp hV with ⟨hVA, hVcard⟩
        have hdisj : Disjoint U V := by
          rw [Finset.disjoint_left]
          intro x hxU hxV
          exact (Finset.mem_sdiff.mp (hVA hxV)).2 (hUA hxU)
        have hBcard : (U ∪ V).card = w := by
          rw [Finset.card_union_of_disjoint hdisj, hUcard, hVcard]; omega
        refine ⟨⟨U ∪ V, hBcard⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · have hinter : A.1 ∩ (U ∪ V) = U := by
            ext x; simp only [Finset.mem_inter, Finset.mem_union]
            exact ⟨fun ⟨hxA, h⟩ => h.elim id fun hxV => False.elim ((Finset.mem_sdiff.mp (hVA hxV)).2 hxA),
              fun hxU => ⟨hUA hxU, Or.inl hxU⟩⟩
          have hcard_i := card_inter_wsub A ⟨U ∪ V, hBcard⟩
          rw [hinter, hUcard] at hcard_i
          have hle := jDist_le A ⟨U ∪ V, hBcard⟩
          omega
        · ext1
          · ext x; simp only [Finset.mem_inter, Finset.mem_union]
            exact ⟨fun ⟨hxA, h⟩ => h.elim id fun hxV => False.elim ((Finset.mem_sdiff.mp (hVA hxV)).2 hxA),
              fun hxU => ⟨hUA hxU, Or.inl hxU⟩⟩
          · ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
            exact ⟨fun ⟨h, hxA⟩ => h.elim (fun hxU => False.elim (hxA (hUA hxU))) id,
              fun hxV => ⟨Or.inr hxV, (Finset.mem_sdiff.mp (hVA hxV)).2⟩⟩
    rw [hbij, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      A.2, Nat.choose_symm hj]
  rw [hconst, hcard] at hge
  exact hge

/-- Distance indicator matrix `D_r` of the Johnson scheme. -/
noncomputable def distMat (n w r : ℕ) : Matrix (WSub n w) (WSub n w) ℝ :=
  fun A B => if jDist A B = r then 1 else 0

lemma invariant_eq_sum_distMat (n w : ℕ) (M : Matrix (WSub n w) (WSub n w) ℝ)
    (f : ℕ → ℝ) (hf : ∀ A B, M A B = f (jDist A B)) :
    M = ∑ r : Fin (w + 1), f r.1 • distMat n w r.1 := by
  ext A B
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, distMat]
  let r₀ : Fin (w + 1) := ⟨jDist A B, Nat.lt_succ_of_le (jDist_le A B)⟩
  rw [Finset.sum_eq_single r₀]
  · simp [r₀, hf A B]
  · intro r _ hne
    rw [if_neg (fun h => hne (Fin.ext h.symm)), mul_zero]
  · intro h; exact False.elim (h (Finset.mem_univ r₀))

lemma choose_pred_lt {n k : ℕ} (hk1 : 1 ≤ k) (hkn : 2 * k ≤ n) :
    Nat.choose n (k - 1) < Nat.choose n k := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show k ≤ n by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show k - 1 ≤ n by omega)
  have hfac : Nat.factorial k = k * Nat.factorial (k - 1) := by
    calc Nat.factorial k = Nat.factorial ((k - 1) + 1) := by rw [Nat.sub_add_cancel hk1]
      _ = (k - 1 + 1) * Nat.factorial (k - 1) := Nat.factorial_succ _
      _ = k * Nat.factorial (k - 1) := by rw [Nat.sub_add_cancel hk1]
  have hfac2 : Nat.factorial (n - (k - 1)) = (n - (k - 1)) * Nat.factorial (n - k) := by
    calc Nat.factorial (n - (k - 1)) = Nat.factorial ((n - k) + 1) := by
          rw [show n - (k - 1) = (n - k) + 1 by omega]
      _ = ((n - k) + 1) * Nat.factorial (n - k) := Nat.factorial_succ _
      _ = (n - (k - 1)) * Nat.factorial (n - k) := by
          rw [show (n - k) + 1 = n - (k - 1) by omega]
  have hpos : 0 < Nat.factorial (k - 1) * Nat.factorial (n - k) := by positivity
  have heq : k * Nat.choose n k * (Nat.factorial (k - 1) * Nat.factorial (n - k)) =
      (n - (k - 1)) * Nat.choose n (k - 1) * (Nat.factorial (k - 1) * Nat.factorial (n - k)) := by
    calc k * Nat.choose n k * (Nat.factorial (k - 1) * Nat.factorial (n - k))
        = Nat.choose n k * (k * Nat.factorial (k - 1)) * Nat.factorial (n - k) := by ring
      _ = Nat.factorial n := by rw [← hfac]; exact h1
      _ = Nat.choose n (k - 1) * Nat.factorial (k - 1) *
            ((n - (k - 1)) * Nat.factorial (n - k)) := by rw [← hfac2]; exact h2.symm
      _ = (n - (k - 1)) * Nat.choose n (k - 1) * (Nat.factorial (k - 1) * Nat.factorial (n - k)) := by ring
  have hmul_eq : k * Nat.choose n k = (n - (k - 1)) * Nat.choose n (k - 1) :=
    Nat.eq_of_mul_eq_mul_right hpos heq
  have hcpos : 0 < Nat.choose n (k - 1) := Nat.choose_pos (by omega)
  have hlt : k < n - (k - 1) := by omega
  nlinarith

lemma eVal_zero_pos {n w k : ℕ} (hk : k ≤ w) (hwn : 2 * w ≤ n) :
    0 < eVal n w k 0 := by
  rw [eVal_zero hk hwn]
  apply div_pos
  · exact_mod_cast by
      cases k with
      | zero => simp
      | succ m =>
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
          Nat.add_sub_cancel]
        have hlt := choose_pred_lt (n := n) (k := m + 1) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at hlt
        omega
  · exact_mod_cast Nat.choose_pos (by omega : w ≤ n)

lemma projMat_ne_zero {n w k : ℕ} (hk : k ≤ w) (hwn : 2 * w ≤ n) :
    projMat n w k ≠ 0 := by
  intro h0
  let A := canonA n w (by omega)
  have hA : projMat n w k A A = 0 := by rw [h0]; rfl
  rw [projMat_eq_eVal A A, jDist_eq_zero_iff.mpr rfl] at hA
  exact ne_of_gt (eVal_zero_pos hk hwn) hA

lemma projMat_linearIndependent {n w : ℕ} (hwn : 2 * w ≤ n) :
    LinearIndependent ℝ (fun k : Fin (w + 1) => projMat n w k.1) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc m
  have hmul : projMat n w m.1 * ∑ k : Fin (w + 1), c k • projMat n w k.1 = 0 := by
    rw [hc, Matrix.mul_zero]
  rw [Matrix.mul_sum] at hmul
  have hsingle : (∑ k : Fin (w + 1), projMat n w m.1 * (c k • projMat n w k.1)) =
      c m • projMat n w m.1 := by
    rw [Finset.sum_eq_single m]
    · rw [Matrix.mul_smul, projMat_mul_self]
    · intro k _ hkm
      rw [Matrix.mul_smul, projMat_mul_eq_zero (fun h => hkm (Fin.ext h).symm)
        (Nat.le_of_lt_succ m.isLt) (Nat.le_of_lt_succ k.isLt), smul_zero]
    · intro h; exact False.elim (h (Finset.mem_univ m))
  rw [hsingle, smul_eq_zero] at hmul
  exact hmul.resolve_right (projMat_ne_zero (Nat.le_of_lt_succ m.isLt) hwn)

lemma invariant_mem_span_projMat {n w : ℕ} (hwn : 2 * w ≤ n)
    (M : Matrix (WSub n w) (WSub n w) ℝ) (f : ℕ → ℝ) (hf : ∀ A B, M A B = f (jDist A B)) :
    ∃ c : Fin (w + 1) → ℝ, M = ∑ k : Fin (w + 1), c k • projMat n w k.1 := by
  let Sproj : Submodule ℝ (Matrix (WSub n w) (WSub n w) ℝ) :=
    Submodule.span ℝ (Set.range fun k : Fin (w + 1) => projMat n w k.1)
  let Sdist : Submodule ℝ (Matrix (WSub n w) (WSub n w) ℝ) :=
    Submodule.span ℝ (Set.range fun r : Fin (w + 1) => distMat n w r.1)
  have hle : Sproj ≤ Sdist := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    dsimp only
    rw [invariant_eq_sum_distMat n w (projMat n w k.1) (eVal n w k.1)
      (fun A B => projMat_eq_eVal A B)]
    exact Submodule.sum_mem _ fun r _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
  have hfin_proj : Module.finrank ℝ Sproj = w + 1 := by
    rw [finrank_span_eq_card (projMat_linearIndependent hwn), Fintype.card_fin]
  have hfin_dist : Module.finrank ℝ Sdist ≤ w + 1 := by
    have hle_card := finrank_span_le_card (R := ℝ) (Set.range fun r : Fin (w + 1) => distMat n w r.1)
    have hle_fin : (Set.range fun r : Fin (w + 1) => distMat n w r.1).toFinset.card ≤ w + 1 := by
      rw [Set.toFinset_range]
      exact (Finset.card_image_le).trans (by simp)
    exact le_trans hle_card hle_fin
  have heq : Sproj = Sdist := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hM : M ∈ Sproj := by
    rw [heq, invariant_eq_sum_distMat n w M f hf]
    exact Submodule.sum_mem _ fun r _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.mp hM
  exact ⟨c, hc.symm⟩

/-- Diagonal coordinate indicator matrix `D_i`. -/
def diagCoordMat (n w : ℕ) (i : Fin n) : Matrix (WSub n w) (WSub n w) ℝ :=
  fun A B => if A = B ∧ i ∈ A.1 then 1 else 0

lemma jDist_mul_projMat_eq (n w k : ℕ) :
    (fun A B : WSub n w => (jDist A B : ℝ) * projMat n w k A B) =
      (w : ℝ) • projMat n w k -
        ∑ i : Fin n, diagCoordMat n w i * projMat n w k * diagCoordMat n w i := by
  ext A B
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
    Matrix.mul_apply, diagCoordMat]
  have hsum : (∑ i : Fin n, ∑ x : WSub n w,
      (∑ x_1 : WSub n w, (if A = x_1 ∧ i ∈ A.1 then (1 : ℝ) else 0) * projMat n w k x_1 x) *
        (if x = B ∧ i ∈ x.1 then 1 else 0)) =
      ((A.1 ∩ B.1).card : ℝ) * projMat n w k A B := by
    have hinner : ∀ i : Fin n, (∑ x : WSub n w,
        (∑ x_1 : WSub n w, (if A = x_1 ∧ i ∈ A.1 then (1 : ℝ) else 0) * projMat n w k x_1 x) *
          (if x = B ∧ i ∈ x.1 then 1 else 0)) =
        if i ∈ A.1 ∩ B.1 then projMat n w k A B else 0 := by
      intro i
      rw [Finset.sum_eq_single B]
      · rw [Finset.sum_eq_single A]
        · by_cases hA : i ∈ A.1 <;> by_cases hB : i ∈ B.1 <;> simp [hA, hB]
        · intro C _ hCA
          rw [if_neg (fun h => hCA h.1.symm), zero_mul]
        · intro h; exact False.elim (h (Finset.mem_univ A))
      · intro x _ hxB
        rw [if_neg (fun h => hxB h.1), mul_zero]
      · intro h; exact False.elim (h (Finset.mem_univ B))
    simp_rw [hinner]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [hsum, card_inter_wsub]
  have hle : jDist A B ≤ w := jDist_le A B
  rw [Nat.cast_sub hle]
  ring

lemma diagCoordMat_mulVec_HSub {n w m : ℕ} (i : Fin n) (hm : m + 1 ≤ w)
    {v : EuclideanSpace ℝ (WSub n w)} (hv : v ∈ HSub n w m) :
    WithLp.toLp 2 (diagCoordMat n w i *ᵥ v) ∈ HSub n w (m + 1) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨U, hU, rfl⟩
    have heq : WithLp.toLp 2 (diagCoordMat n w i *ᵥ indVec n w U) =
        indVec n w (insert i U) := by
      ext A
      simp only [Matrix.mulVec, dotProduct, diagCoordMat, indVec, PiLp.toLp_apply]
      rw [Finset.sum_eq_single A]
      · by_cases hiA : i ∈ A.1 <;> by_cases hUA : U ⊆ A.1
        · simp [hiA, hUA, Finset.insert_subset_iff]
        · simp [hiA, hUA, Finset.insert_subset_iff]
        · simp [hiA, hUA, Finset.insert_subset_iff]
        · simp [hiA, hUA, Finset.insert_subset_iff]
      · intro B _ hBA
        rw [if_neg (fun h => hBA h.1.symm), zero_mul]
      · intro h; exact False.elim (h (Finset.mem_univ A))
    rw [heq]
    by_cases hiU : i ∈ U
    · rw [Finset.insert_eq_of_mem hiU]
      exact HSub_step hm (indVec_mem_HSub hU)
    · exact indVec_mem_HSub (by rw [Finset.card_insert_of_notMem hiU, hU])
  | zero => simp
  | add x y _ _ ihx ihy =>
    have hlin : WithLp.toLp 2 (diagCoordMat n w i *ᵥ (x.ofLp + y.ofLp)) =
        WithLp.toLp 2 (diagCoordMat n w i *ᵥ x.ofLp) +
          WithLp.toLp 2 (diagCoordMat n w i *ᵥ y.ofLp) := by
      ext A; change (diagCoordMat n w i *ᵥ (x.ofLp + y.ofLp)) A = _; simp [Matrix.mulVec_add]
    rw [show (x + y : EuclideanSpace ℝ (WSub n w)).ofLp = x.ofLp + y.ofLp from rfl, hlin]
    exact Submodule.add_mem _ ihx ihy
  | smul c x _ ih =>
    have hlin : WithLp.toLp 2 (diagCoordMat n w i *ᵥ (c • x.ofLp)) =
        c • WithLp.toLp 2 (diagCoordMat n w i *ᵥ x.ofLp) := by
      ext A; change (diagCoordMat n w i *ᵥ (c • x.ofLp)) A = _; simp [Matrix.mulVec_smul]
    rw [show (c • x : EuclideanSpace ℝ (WSub n w)).ofLp = c • x.ofLp from rfl, hlin]
    exact Submodule.smul_mem _ _ ih

lemma projMat_mul_diag_mul_projMat_eq_zero {n w k m : ℕ} (i : Fin n)
    (hk : k ≤ w) (hm : m ≤ w) (hfar : k + 2 ≤ m ∨ m + 2 ≤ k) :
    projMat n w m * diagCoordMat n w i * projMat n w k = 0 := by
  have hcase : ∀ a b : ℕ, a ≤ w → b ≤ w → a + 2 ≤ b →
      projMat n w b * diagCoordMat n w i * projMat n w a = 0 := by
    intro a b ha hb hab
    ext A B
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    let v : EuclideanSpace ℝ (WSub n w) :=
      (VSub n w a).starProjection (EuclideanSpace.basisFun (WSub n w) ℝ B)
    have hv : v ∈ HSub n w a := VSub_le_HSub n w a (Submodule.starProjection_apply_mem _ _)
    let u : EuclideanSpace ℝ (WSub n w) := WithLp.toLp 2 (diagCoordMat n w i *ᵥ v)
    have hu : u ∈ HSub n w (a + 1) := diagCoordMat_mulVec_HSub i (by omega) hv
    have hu_prev : u ∈ HSub n w (b - 1) := HSub_mono (by omega) (by omega) hu
    have hproj_u : (VSub n w b).starProjection u = 0 := by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
      rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
      intro y hy
      rw [real_inner_comm]
      exact (Submodule.mem_orthogonal _ _).mp (Submodule.mem_inf.mp hy).2 u
        (by simpa using hu_prev)
    have hmul_u : (∑ x : WSub n w, (∑ x_1 : WSub n w, projMat n w b A x_1 * diagCoordMat n w i x_1 x) *
        projMat n w a x B) = ((VSub n w b).starProjection u) A := by
      have hlhs : (∑ x : WSub n w, (∑ x_1 : WSub n w, projMat n w b A x_1 * diagCoordMat n w i x_1 x) *
          projMat n w a x B) = (projMat n w b *ᵥ u) A := by
        simp only [Matrix.mulVec, dotProduct, u, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun x _ => ?_
        change projMat n w b A x₁ * diagCoordMat n w i x₁ x * v x = _
        ring
      rw [hlhs, projMat, opToMatrix_mulVec]
    rw [hmul_u, hproj_u]
    rfl
  rcases hfar with h1 | h2
  · exact hcase k m hk hm h1
  · have hsym := hcase m k hm hk h2
    have htr : (projMat n w k * diagCoordMat n w i * projMat n w m)ᵀ =
        projMat n w m * diagCoordMat n w i * projMat n w k := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      have hEm : (projMat n w m)ᵀ = projMat n w m := by
        ext A B; exact opToMatrix_starProjection_symm (VSub n w m) B A
      have hEk : (projMat n w k)ᵀ = projMat n w k := by
        ext A B; exact opToMatrix_starProjection_symm (VSub n w k) B A
      have hDi : (diagCoordMat n w i)ᵀ = diagCoordMat n w i := by
        ext A B
        simp only [Matrix.transpose_apply, diagCoordMat]
        by_cases h : A = B <;> simp [h, eq_comm]
      rw [hEm, hEk, hDi]
    rw [← htr, hsym, Matrix.transpose_zero]

lemma jDist_mul_projMat_three_terms {n w k : ℕ} (hk : k ≤ w) (hwn : 2 * w ≤ n) :
    ∃ c : Fin (w + 1) → ℝ,
      (fun A B : WSub n w => (jDist A B : ℝ) * projMat n w k A B) =
        ∑ m : Fin (w + 1), c m • projMat n w m.1 ∧
      ∀ m : Fin (w + 1), (k + 2 ≤ m.1 ∨ m.1 + 2 ≤ k) → c m = 0 := by
  let M : Matrix (WSub n w) (WSub n w) ℝ :=
    fun A B => (jDist A B : ℝ) * projMat n w k A B
  obtain ⟨c, hc⟩ := invariant_mem_span_projMat hwn M
    (fun j => (j : ℝ) * eVal n w k j) (fun A B => by dsimp [M]; rw [projMat_eq_eVal A B])
  refine ⟨c, hc, fun m hm => ?_⟩
  have hmul : projMat n w m.1 * M = 0 := by
    dsimp only [M]
    rw [jDist_mul_projMat_eq, Matrix.mul_sub, Matrix.mul_smul,
      projMat_mul_eq_zero (by omega) (Nat.le_of_lt_succ m.isLt) hk, smul_zero, zero_sub,
      Matrix.mul_sum]
    have hzero : ∑ i : Fin n, projMat n w m.1 *
        (diagCoordMat n w i * projMat n w k * diagCoordMat n w i) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
        projMat_mul_diag_mul_projMat_eq_zero i hk (Nat.le_of_lt_succ m.isLt)
          hm, Matrix.zero_mul]
    rw [hzero, neg_zero]
  have hmul2 : projMat n w m.1 * ∑ r : Fin (w + 1), c r • projMat n w r.1 =
      c m • projMat n w m.1 := by
    rw [Matrix.mul_sum, Finset.sum_eq_single m]
    · rw [Matrix.mul_smul, projMat_mul_self]
    · intro r _ hrm
      rw [Matrix.mul_smul, projMat_mul_eq_zero (fun h => hrm (Fin.ext h).symm)
        (Nat.le_of_lt_succ m.isLt) (Nat.le_of_lt_succ r.isLt), smul_zero]
    · intro h; exact False.elim (h (Finset.mem_univ m))
  rw [← hc, hmul] at hmul2
  exact (smul_eq_zero.mp hmul2.symm).resolve_right
    (projMat_ne_zero (Nat.le_of_lt_succ m.isLt) hwn)

/-- Johnson recurrence coefficient `A_k`. -/
noncomputable def jA (n w k : ℕ) : ℝ :=
  ((n - k + 1 : ℕ) : ℝ) * ((w - k : ℕ) : ℝ) * ((n - w - k : ℕ) : ℝ) /
    (((n - 2 * k + 1 : ℕ) : ℝ) * ((n - 2 * k : ℕ) : ℝ))

/-- Johnson recurrence coefficient `C_k`. -/
noncomputable def jC (n w k : ℕ) : ℝ :=
  if k = 0 then 0 else
    ((k : ℝ) * ((w - k + 1 : ℕ) : ℝ) * ((n - w - k + 1 : ℕ) : ℝ)) /
      (((n - 2 * k + 2 : ℕ) : ℝ) * ((n - 2 * k + 1 : ℕ) : ℝ))

lemma jA_mul_eVal_zero {n w k : ℕ} (hk : k + 1 ≤ w) (hwn : 2 * w ≤ n) :
    jA n w k * eVal n w k 0 = jC n w (k + 1) * eVal n w (k + 1) 0 := by
  rw [eVal_zero (by omega) hwn, eVal_zero hk hwn]
  have hk_mul : ((n - k + 1 : ℕ) : ℝ) *
      ((Nat.choose n k - if k = 0 then 0 else Nat.choose n (k - 1) : ℕ) : ℝ) =
      ((n - 2 * k + 1 : ℕ) : ℝ) * (Nat.choose n k : ℝ) := by
    cases k with
    | zero => simp
    | succ m =>
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel]
      have hlt := choose_pred_lt (n := n) (k := m + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hlt
      have h1 := Nat.choose_mul_factorial_mul_factorial (show m + 1 ≤ n by omega)
      have h2 := Nat.choose_mul_factorial_mul_factorial (show m ≤ n by omega)
      have hfac1 : Nat.factorial (m + 1) = (m + 1) * Nat.factorial m := Nat.factorial_succ m
      have hfac2 : Nat.factorial (n - m) = (n - m) * Nat.factorial (n - (m + 1)) := by
        calc Nat.factorial (n - m) = Nat.factorial ((n - (m + 1)) + 1) := by
              rw [show n - m = (n - (m + 1)) + 1 by omega]
          _ = (n - (m + 1) + 1) * Nat.factorial (n - (m + 1)) := Nat.factorial_succ _
          _ = (n - m) * Nat.factorial (n - (m + 1)) := by
              rw [show n - (m + 1) + 1 = n - m by omega]
      have hpos : 0 < Nat.factorial m * Nat.factorial (n - (m + 1)) := by positivity
      have heq_fac : (m + 1) * Nat.choose n (m + 1) * (Nat.factorial m * Nat.factorial (n - (m + 1))) =
          (n - m) * Nat.choose n m * (Nat.factorial m * Nat.factorial (n - (m + 1))) := by
        calc (m + 1) * Nat.choose n (m + 1) * (Nat.factorial m * Nat.factorial (n - (m + 1)))
            = Nat.choose n (m + 1) * ((m + 1) * Nat.factorial m) * Nat.factorial (n - (m + 1)) := by ring
          _ = Nat.factorial n := by rw [← hfac1]; exact h1
          _ = Nat.choose n m * Nat.factorial m * ((n - m) * Nat.factorial (n - (m + 1))) := by
              rw [← hfac2]; exact h2.symm
          _ = (n - m) * Nat.choose n m * (Nat.factorial m * Nat.factorial (n - (m + 1))) := by ring
      have hrel : (m + 1) * Nat.choose n (m + 1) = (n - m) * Nat.choose n m :=
        Nat.eq_of_mul_eq_mul_right hpos heq_fac
      have hrelR : ((m + 1 : ℕ) : ℝ) * (Nat.choose n (m + 1) : ℝ) =
          ((n - m : ℕ) : ℝ) * (Nat.choose n m : ℝ) := by exact_mod_cast hrel
      rw [Nat.cast_sub (le_of_lt hlt)]
      have hc1 : ((n - (m + 1) + 1 : ℕ) : ℝ) = (n : ℝ) - m := by
        rw [Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring
      have hc2 : ((n - 2 * (m + 1) + 1 : ℕ) : ℝ) = (n : ℝ) - 2 * m - 1 := by
        rw [Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring
      have hc3 : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := by rw [Nat.cast_sub (by omega)]
      rw [hc1, hc2]
      rw [hc3] at hrelR
      have : ((m : ℝ) + 1) * (Nat.choose n (m + 1) : ℝ) = ((n : ℝ) - m) * (Nat.choose n m : ℝ) := by
        push_cast at hrelR; exact hrelR
      nlinarith
  have hk1_mul : ((k + 1 : ℕ) : ℝ) *
      ((Nat.choose n (k + 1) - Nat.choose n k : ℕ) : ℝ) =
      ((n - 2 * k - 1 : ℕ) : ℝ) * (Nat.choose n k : ℝ) := by
    have hlt := choose_pred_lt (n := n) (k := k + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at hlt
    have h1 := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ n by omega)
    have h2 := Nat.choose_mul_factorial_mul_factorial (show k ≤ n by omega)
    have hfac1 : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := Nat.factorial_succ k
    have hfac2 : Nat.factorial (n - k) = (n - k) * Nat.factorial (n - (k + 1)) := by
      calc Nat.factorial (n - k) = Nat.factorial ((n - (k + 1)) + 1) := by
            rw [show n - k = (n - (k + 1)) + 1 by omega]
        _ = (n - (k + 1) + 1) * Nat.factorial (n - (k + 1)) := Nat.factorial_succ _
        _ = (n - k) * Nat.factorial (n - (k + 1)) := by
            rw [show n - (k + 1) + 1 = n - k by omega]
    have hpos : 0 < Nat.factorial k * Nat.factorial (n - (k + 1)) := by positivity
    have heq_fac : (k + 1) * Nat.choose n (k + 1) * (Nat.factorial k * Nat.factorial (n - (k + 1))) =
        (n - k) * Nat.choose n k * (Nat.factorial k * Nat.factorial (n - (k + 1))) := by
      calc (k + 1) * Nat.choose n (k + 1) * (Nat.factorial k * Nat.factorial (n - (k + 1)))
          = Nat.choose n (k + 1) * ((k + 1) * Nat.factorial k) * Nat.factorial (n - (k + 1)) := by ring
        _ = Nat.factorial n := by rw [← hfac1]; exact h1
        _ = Nat.choose n k * Nat.factorial k * ((n - k) * Nat.factorial (n - (k + 1))) := by
            rw [← hfac2]; exact h2.symm
        _ = (n - k) * Nat.choose n k * (Nat.factorial k * Nat.factorial (n - (k + 1))) := by ring
    have hrel : (k + 1) * Nat.choose n (k + 1) = (n - k) * Nat.choose n k :=
      Nat.eq_of_mul_eq_mul_right hpos heq_fac
    have hrelR : ((k + 1 : ℕ) : ℝ) * (Nat.choose n (k + 1) : ℝ) =
        ((n - k : ℕ) : ℝ) * (Nat.choose n k : ℝ) := by exact_mod_cast hrel
    rw [Nat.cast_sub (le_of_lt hlt), Nat.cast_sub (by omega : 1 ≤ n - 2 * k),
      Nat.cast_sub (by omega : 2 * k ≤ n)]
    rw [Nat.cast_sub (by omega : k ≤ n)] at hrelR
    push_cast at hrelR ⊢
    nlinarith
  have hd1 : ((n - 2 * k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hd2 : ((n - 2 * k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : n - 2 * k ≠ 0)
  have hcw : (Nat.choose n w : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Nat.choose_pos (by omega : w ≤ n))
  have hne1 : ((n - k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hne2 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hsub1 : ((n - 2 * (k + 1) + 2 : ℕ) : ℝ) = ((n - 2 * k : ℕ) : ℝ) := by
    exact_mod_cast (by omega : n - 2 * (k + 1) + 2 = n - 2 * k)
  have hsub2 : ((n - 2 * (k + 1) + 1 : ℕ) : ℝ) = ((n - 2 * k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : n - 2 * (k + 1) + 1 = n - 2 * k - 1)
  have hsub3 : ((w - (k + 1) + 1 : ℕ) : ℝ) = ((w - k : ℕ) : ℝ) := by
    exact_mod_cast (by omega : w - (k + 1) + 1 = w - k)
  have hsub4 : ((n - w - (k + 1) + 1 : ℕ) : ℝ) = ((n - w - k : ℕ) : ℝ) := by
    exact_mod_cast (by omega : (n - w) - (k + 1) + 1 = (n - w) - k)
  dsimp only [jA, jC]
  rw [if_neg (Nat.succ_ne_zero k), hsub1, hsub2, hsub3, hsub4]
  have hk_mul' : ((Nat.choose n k - if k = 0 then 0 else Nat.choose n (k - 1) : ℕ) : ℝ) =
      ((n - 2 * k + 1 : ℕ) : ℝ) * (Nat.choose n k : ℝ) / ((n - k + 1 : ℕ) : ℝ) :=
    (eq_div_iff hne1).mpr (by rw [mul_comm]; exact hk_mul)
  have hk1_mul' : ((Nat.choose n (k + 1) - Nat.choose n k : ℕ) : ℝ) =
      ((n - 2 * k - 1 : ℕ) : ℝ) * (Nat.choose n k : ℝ) / ((k + 1 : ℕ) : ℝ) :=
    (eq_div_iff hne2).mpr (by rw [mul_comm]; exact hk1_mul)
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel] at *
  rw [hk_mul', hk1_mul']
  have hd_sub : ((n - 2 * k - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : n - 2 * k - 1 ≠ 0)
  push_cast
  field_simp [hd1, hd2, hd_sub, hcw, hne1, hne2]

lemma jAdjMatrix_sq_apply {n w : ℕ} (hw1 : 1 ≤ w) (hw : w + 1 ≤ n) (A B : WSub n w) :
    (jAdjMatrix n w * jAdjMatrix n w) A B =
      if jDist A B = 0 then (w : ℝ) * ((n : ℝ) - w)
      else if jDist A B = 1 then (n : ℝ) - 2
      else if jDist A B = 2 then 4
      else 0 := by
  have hsum_card : (jAdjMatrix n w * jAdjMatrix n w) A B =
      ((Finset.univ.filter fun C : WSub n w => jDist A C = 1 ∧ jDist B C = 1).card : ℝ) := by
    simp only [Matrix.mul_apply, jAdjMatrix]
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [jDist_symm C B]
    by_cases h1 : jDist A C = 1 <;> by_cases h2 : jDist B C = 1 <;> simp [h1, h2]
  rw [hsum_card]
  by_cases hd0 : jDist A B = 0
  · rw [if_pos hd0]
    obtain rfl : A = B := jDist_eq_zero_iff.mp hd0
    have hfilt : (Finset.univ.filter fun C : WSub n w => jDist A C = 1 ∧ jDist A C = 1) =
        Finset.univ.filter fun C : WSub n w => jDist A C = 1 := by
      ext C; simp [and_self]
    rw [hfilt]
    have hbij : (Finset.univ.filter fun C : WSub n w => jDist A C = 1).card =
        (A.1 ×ˢ (Finset.univ \ A.1)).card := by
      refine Eq.symm (Finset.card_bij (fun p hp => ⟨insert p.2 (A.1.erase p.1), by
        have ha : p.1 ∈ A.1 := (Finset.mem_product.mp hp).1
        have hb : p.2 ∉ A.1 := (Finset.mem_sdiff.mp (Finset.mem_product.mp hp).2).2
        have hne : p.2 ∉ A.1.erase p.1 := fun h => hb (Finset.erase_subset _ _ h)
        rw [Finset.card_insert_of_notMem hne, Finset.card_erase_of_mem ha, A.2]; omega⟩) ?_ ?_ ?_)
      · intro p hp
        have ha : p.1 ∈ A.1 := (Finset.mem_product.mp hp).1
        have hb : p.2 ∉ A.1 := (Finset.mem_sdiff.mp (Finset.mem_product.mp hp).2).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        dsimp [jDist]
        have hs : A.1 \ insert p.2 (A.1.erase p.1) = {p.1} := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
          exact ⟨fun ⟨hxA, hnx⟩ => by_contra fun hxp => hnx (Or.inr ⟨hxp, hxA⟩),
            by rintro rfl; exact ⟨ha, fun h' => h'.elim (fun h'' => hb (h'' ▸ ha)) fun h'' => h''.1 rfl⟩⟩
        rw [hs, Finset.card_singleton]
      · intro p₁ hp₁ p₂ hp₂ heq
        have hp1A := (Finset.mem_product.mp hp₁).1
        have hp1B := (Finset.mem_sdiff.mp (Finset.mem_product.mp hp₁).2).2
        have hp2A := (Finset.mem_product.mp hp₂).1
        have hp2B := (Finset.mem_sdiff.mp (Finset.mem_product.mp hp₂).2).2
        have hval : insert p₁.2 (A.1.erase p₁.1) = insert p₂.2 (A.1.erase p₂.1) :=
          congr_arg Subtype.val heq
        have hb : p₁.2 = p₂.2 := by
          have hm : p₁.2 ∈ insert p₂.2 (A.1.erase p₂.1) := by rw [← hval]; exact Finset.mem_insert_self _ _
          exact (Finset.mem_insert.mp hm).elim id fun h => False.elim (hp1B (Finset.erase_subset _ _ h))
        have ha : p₁.1 = p₂.1 := by
          by_contra hne
          have hm : p₁.1 ∈ insert p₂.2 (A.1.erase p₂.1) := Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, hp1A⟩)
          rw [← hval] at hm
          exact (Finset.mem_insert.mp hm).elim (fun h => hp1B (h ▸ hp1A)) fun h => (Finset.mem_erase.mp h).1 rfl
        exact Prod.ext ha hb
      · intro C hC
        have hj1 : jDist A C = 1 := (Finset.mem_filter.mp hC).2
        have hj2 : jDist C A = 1 := by rw [jDist_symm]; exact hj1
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hj1
        obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hj2
        have haA : a ∈ A.1 := (Finset.mem_sdiff.mp (ha ▸ Finset.mem_singleton_self a)).1
        have haC : a ∉ C.1 := (Finset.mem_sdiff.mp (ha ▸ Finset.mem_singleton_self a)).2
        have hbC : b ∈ C.1 := (Finset.mem_sdiff.mp (hb ▸ Finset.mem_singleton_self b)).1
        have hbA : b ∉ A.1 := (Finset.mem_sdiff.mp (hb ▸ Finset.mem_singleton_self b)).2
        refine ⟨(a, b), Finset.mem_product.mpr ⟨haA, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hbA⟩⟩, ?_⟩
        ext x; simp only [Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro (rfl | ⟨hxa, hxA⟩)
          · exact hbC
          · by_contra hxnC
            have hm : x ∈ A.1 \ C.1 := Finset.mem_sdiff.mpr ⟨hxA, hxnC⟩
            rw [ha, Finset.mem_singleton] at hm
            exact hxa hm
        · intro hxC
          by_cases hxb : x = b
          · exact Or.inl hxb
          · right
            have hxA : x ∈ A.1 := by
              by_contra hxnA
              have hm : x ∈ C.1 \ A.1 := Finset.mem_sdiff.mpr ⟨hxC, hxnA⟩
              rw [hb, Finset.mem_singleton] at hm
              exact hxb hm
            exact ⟨fun h => haC (h ▸ hxC), hxA⟩
    rw [hbij, Finset.card_product, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, A.2, Nat.cast_mul, Nat.cast_sub (by omega)]
  · rw [if_neg hd0]
    by_cases hd1 : jDist A B = 1
    · rw [if_pos hd1]
      have hd1' : jDist B A = 1 := by rw [jDist_symm]; exact hd1
      obtain ⟨a₀, ha₀⟩ := Finset.card_eq_one.mp hd1
      obtain ⟨b₀, hb₀⟩ := Finset.card_eq_one.mp hd1'
      have ha₀A : a₀ ∈ A.1 := (Finset.mem_sdiff.mp (ha₀ ▸ Finset.mem_singleton_self a₀)).1
      have ha₀B : a₀ ∉ B.1 := (Finset.mem_sdiff.mp (ha₀ ▸ Finset.mem_singleton_self a₀)).2
      have hb₀B : b₀ ∈ B.1 := (Finset.mem_sdiff.mp (hb₀ ▸ Finset.mem_singleton_self b₀)).1
      have hb₀A : b₀ ∉ A.1 := (Finset.mem_sdiff.mp (hb₀ ▸ Finset.mem_singleton_self b₀)).2
      have hab_ne : a₀ ≠ b₀ := fun h => hb₀A (h ▸ ha₀A)
      have hbij : (Finset.univ.filter fun C : WSub n w => jDist A C = 1 ∧ jDist B C = 1).card =
          ((A.1 ∩ B.1) ∪ (Finset.univ \ (A.1 ∪ B.1))).card := by
        refine Eq.symm (Finset.card_bij (fun z hz =>
          if hzI : z ∈ A.1 ∩ B.1 then ⟨insert b₀ (A.1.erase z), by
            have hzA := (Finset.mem_inter.mp hzI).1
            have hne : b₀ ∉ A.1.erase z := fun h => hb₀A (Finset.erase_subset _ _ h)
            rw [Finset.card_insert_of_notMem hne, Finset.card_erase_of_mem hzA, A.2]; omega⟩
          else ⟨insert z (A.1.erase a₀), by
            have hzS := (Finset.mem_union.mp hz).resolve_left hzI
            have hzA : z ∉ A.1 := fun h => (Finset.mem_sdiff.mp hzS).2 (Finset.mem_union_left _ h)
            have hne : z ∉ A.1.erase a₀ := fun h => hzA (Finset.erase_subset _ _ h)
            rw [Finset.card_insert_of_notMem hne, Finset.card_erase_of_mem ha₀A, A.2]; omega⟩) ?_ ?_ ?_)
        · intro z hz
          by_cases hzI : z ∈ A.1 ∩ B.1
          · simp only [dif_pos hzI, Finset.mem_filter, Finset.mem_univ, true_and]
            have hzA := (Finset.mem_inter.mp hzI).1
            have hzB := (Finset.mem_inter.mp hzI).2
            have hza : z ≠ a₀ := fun h => ha₀B (h ▸ hzB)
            have hjA : (A.1 \ insert b₀ (A.1.erase z)).card = 1 := by
              have hs : A.1 \ insert b₀ (A.1.erase z) = {z} := by
                ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
                exact ⟨fun ⟨hxA, hnx⟩ => by_contra fun hxz => hnx (Or.inr ⟨hxz, hxA⟩),
                  by rintro rfl; exact ⟨hzA, fun h' => h'.elim (fun h'' => hb₀A (h'' ▸ hzA)) fun h'' => h''.1 rfl⟩⟩
              rw [hs, Finset.card_singleton]
            have hjB : (B.1 \ insert b₀ (A.1.erase z)).card = 1 := by
              have hs : B.1 \ insert b₀ (A.1.erase z) = {z} := by
                ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
                constructor
                · rintro ⟨hxB, hnx⟩
                  by_contra hxz
                  by_cases hxb : x = b₀
                  · exact hnx (Or.inl hxb)
                  · have hxA : x ∈ A.1 := by
                      by_contra hxnA
                      have hm : x ∈ B.1 \ A.1 := Finset.mem_sdiff.mpr ⟨hxB, hxnA⟩
                      rw [hb₀, Finset.mem_singleton] at hm
                      exact hxb hm
                    exact hnx (Or.inr ⟨hxz, hxA⟩)
                · rintro rfl
                  refine ⟨hzB, fun h' => ?_⟩
                  rcases h' with h'' | h''
                  · exact hb₀A (h'' ▸ hzA)
                  · exact h''.1 rfl
              rw [hs, Finset.card_singleton]
            exact ⟨hjA, hjB⟩
          · simp only [dif_neg hzI, Finset.mem_filter, Finset.mem_univ, true_and]
            have hzS := (Finset.mem_union.mp hz).resolve_left hzI
            have hzA : z ∉ A.1 := fun h => (Finset.mem_sdiff.mp hzS).2 (Finset.mem_union_left _ h)
            have hzB : z ∉ B.1 := fun h => (Finset.mem_sdiff.mp hzS).2 (Finset.mem_union_right _ h)
            have hjA : (A.1 \ insert z (A.1.erase a₀)).card = 1 := by
              have hs : A.1 \ insert z (A.1.erase a₀) = {a₀} := by
                ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
                exact ⟨fun ⟨hxA, hnx⟩ => by_contra fun hxa => hnx (Or.inr ⟨hxa, hxA⟩),
                  by rintro rfl; exact ⟨ha₀A, fun h' => h'.elim (fun h'' => hzA (h'' ▸ ha₀A)) fun h'' => h''.1 rfl⟩⟩
              rw [hs, Finset.card_singleton]
            have hjB : (B.1 \ insert z (A.1.erase a₀)).card = 1 := by
              have hs : B.1 \ insert z (A.1.erase a₀) = {b₀} := by
                ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
                constructor
                · rintro ⟨hxB, hnx⟩
                  by_contra hxb
                  have hxA : x ∈ A.1 := by
                    by_contra hxnA
                    have hm : x ∈ B.1 \ A.1 := Finset.mem_sdiff.mpr ⟨hxB, hxnA⟩
                    rw [hb₀, Finset.mem_singleton] at hm
                    exact hxb hm
                  have hxa : x ≠ a₀ := fun h => ha₀B (h ▸ hxB)
                  exact hnx (Or.inr ⟨hxa, hxA⟩)
                · rintro rfl
                  refine ⟨hb₀B, fun h' => ?_⟩
                  rcases h' with h'' | ⟨_, h''⟩
                  · exact hzB (h'' ▸ hb₀B)
                  · exact hb₀A h''
              rw [hs, Finset.card_singleton]
            exact ⟨hjA, hjB⟩
        · intro z₁ hz₁ z₂ hz₂ heq
          by_cases hz₁I : z₁ ∈ A.1 ∩ B.1 <;> by_cases hz₂I : z₂ ∈ A.1 ∩ B.1
          · simp only [dif_pos hz₁I, dif_pos hz₂I] at heq
            have hval : insert b₀ (A.1.erase z₁) = insert b₀ (A.1.erase z₂) :=
              congr_arg Subtype.val heq
            have hz1A := (Finset.mem_inter.mp hz₁I).1
            by_contra hne
            have hm : z₁ ∈ insert b₀ (A.1.erase z₂) := Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, hz1A⟩)
            rw [← hval] at hm
            exact (Finset.mem_insert.mp hm).elim (fun h => hb₀A (h ▸ hz1A)) fun h => (Finset.mem_erase.mp h).1 rfl
          · simp only [dif_pos hz₁I, dif_neg hz₂I] at heq
            have hval : insert b₀ (A.1.erase z₁) = insert z₂ (A.1.erase a₀) :=
              congr_arg Subtype.val heq
            have hz₂S := (Finset.mem_union.mp hz₂).resolve_left hz₂I
            have hz₂A : z₂ ∉ A.1 := fun h => (Finset.mem_sdiff.mp hz₂S).2 (Finset.mem_union_left _ h)
            have hz₂B' : z₂ ∉ B.1 := fun hb => (Finset.mem_sdiff.mp hz₂S).2 (Finset.mem_union_right _ hb)
            have hm : b₀ ∈ insert z₂ (A.1.erase a₀) := by rw [← hval]; exact Finset.mem_insert_self _ _
            rcases Finset.mem_insert.mp hm with h | h
            · have hm2 : z₂ ∈ insert b₀ (A.1.erase z₁) := by rw [hval]; exact Finset.mem_insert_self _ _
              rcases Finset.mem_insert.mp hm2 with h2 | h2
              · exact False.elim (hz₂B' (h2 ▸ hb₀B))
              · exact False.elim (hz₂A (Finset.erase_subset _ _ h2))
            · exact False.elim (hb₀A (Finset.erase_subset _ _ h))
          · simp only [dif_neg hz₁I, dif_pos hz₂I] at heq
            have hval : insert z₁ (A.1.erase a₀) = insert b₀ (A.1.erase z₂) :=
              congr_arg Subtype.val heq
            have hz₁S := (Finset.mem_union.mp hz₁).resolve_left hz₁I
            have hz₁A : z₁ ∉ A.1 := fun h => (Finset.mem_sdiff.mp hz₁S).2 (Finset.mem_union_left _ h)
            have hz₁B : z₁ ∉ B.1 := fun h => (Finset.mem_sdiff.mp hz₁S).2 (Finset.mem_union_right _ h)
            have hm : z₁ ∈ insert b₀ (A.1.erase z₂) := by rw [← hval]; exact Finset.mem_insert_self _ _
            rcases Finset.mem_insert.mp hm with h | h
            · exact False.elim (hz₁B (h ▸ hb₀B))
            · exact False.elim (hz₁A (Finset.erase_subset _ _ h))
          · simp only [dif_neg hz₁I, dif_neg hz₂I] at heq
            have hval : insert z₁ (A.1.erase a₀) = insert z₂ (A.1.erase a₀) :=
              congr_arg Subtype.val heq
            have hz₁S := (Finset.mem_union.mp hz₁).resolve_left hz₁I
            have hz₁A : z₁ ∉ A.1 := fun h => (Finset.mem_sdiff.mp hz₁S).2 (Finset.mem_union_left _ h)
            have hm : z₁ ∈ insert z₂ (A.1.erase a₀) := by rw [← hval]; exact Finset.mem_insert_self _ _
            rcases Finset.mem_insert.mp hm with h | h
            · exact h
            · exact False.elim (hz₁A (Finset.erase_subset _ _ h))
        · intro C hC
          rcases (Finset.mem_filter.mp hC).2 with ⟨hAC, hBC⟩
          have hCA : jDist C A = 1 := by rw [jDist_symm]; exact hAC
          have hCB : jDist C B = 1 := by rw [jDist_symm]; exact hBC
          obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hAC
          obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hCA
          have haA : a ∈ A.1 := (Finset.mem_sdiff.mp (ha ▸ Finset.mem_singleton_self a)).1
          have haC : a ∉ C.1 := (Finset.mem_sdiff.mp (ha ▸ Finset.mem_singleton_self a)).2
          have hbC : b ∈ C.1 := (Finset.mem_sdiff.mp (hb ▸ Finset.mem_singleton_self b)).1
          have hbA : b ∉ A.1 := (Finset.mem_sdiff.mp (hb ▸ Finset.mem_singleton_self b)).2
          have hC_eq : C.1 = insert b (A.1.erase a) := by
            ext x; simp only [Finset.mem_insert, Finset.mem_erase]
            constructor
            · intro hxC
              by_cases hxb : x = b
              · exact Or.inl hxb
              · right
                have hxA : x ∈ A.1 := by
                  by_contra hxnA
                  have hm : x ∈ C.1 \ A.1 := Finset.mem_sdiff.mpr ⟨hxC, hxnA⟩
                  rw [hb, Finset.mem_singleton] at hm
                  exact hxb hm
                exact ⟨fun h => haC (h ▸ hxC), hxA⟩
            · rintro (rfl | ⟨hxa, hxA⟩)
              · exact hbC
              · by_contra hxnC
                have hm : x ∈ A.1 \ C.1 := Finset.mem_sdiff.mpr ⟨hxA, hxnC⟩
                rw [ha, Finset.mem_singleton] at hm
                exact hxa hm
          by_cases ha_eq : a = a₀
          · rw [ha_eq] at ha haA haC hC_eq
            have hb_ne : b ≠ b₀ := by
              intro hbb
              rw [hbb] at hb hbC hbA hC_eq
              have hCB0 : B = C := by
                ext1
                ext x
                by_cases hxa : x = a₀
                · subst hxa; simp [ha₀B, haC]
                · by_cases hxb : x = b₀
                  · subst hxb; simp [hb₀B, hbC]
                  · rw [hC_eq, Finset.mem_insert, Finset.mem_erase]
                    simp only [hxb, false_or, hxa, ne_eq, not_false_eq_true, true_and]
                    constructor
                    · intro hxB
                      by_contra hxnA
                      have hm : x ∈ B.1 \ A.1 := Finset.mem_sdiff.mpr ⟨hxB, hxnA⟩
                      rw [hb₀, Finset.mem_singleton] at hm
                      exact hxb hm
                    · intro hxA
                      by_contra hxnB
                      have hm : x ∈ A.1 \ B.1 := Finset.mem_sdiff.mpr ⟨hxA, hxnB⟩
                      rw [ha₀, Finset.mem_singleton] at hm
                      exact hxa hm
              rw [← hCB0, jDist_eq_zero_iff.mpr rfl] at hBC
              omega
            have hbnotB : b ∉ B.1 := by
              intro hbB
              have hm : b ∈ B.1 \ A.1 := Finset.mem_sdiff.mpr ⟨hbB, hbA⟩
              rw [hb₀, Finset.mem_singleton] at hm
              exact hb_ne hm
            have hbS : b ∈ (A.1 ∩ B.1) ∪ (Finset.univ \ (A.1 ∪ B.1)) :=
              Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
                fun h => (Finset.mem_union.mp h).elim hbA hbnotB⟩)
            have hbI : b ∉ A.1 ∩ B.1 := fun h => hbA (Finset.mem_inter.mp h).1
            refine ⟨b, hbS, ?_⟩
            simp only [dif_neg hbI]
            exact Subtype.ext hC_eq.symm
          · have haB : a ∈ B.1 := by
              by_contra hnaB
              have hm : a ∈ A.1 \ B.1 := Finset.mem_sdiff.mpr ⟨haA, hnaB⟩
              rw [ha₀, Finset.mem_singleton] at hm
              exact ha_eq hm
            have hb_eq : b = b₀ := by
              by_contra hnb
              have ha₀C : a₀ ∈ C.1 := by rw [hC_eq]; exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨Ne.symm ha_eq, ha₀A⟩)
              have hb₀nC : b₀ ∉ C.1 := by
                rw [hC_eq, Finset.mem_insert, Finset.mem_erase]
                rintro (h | ⟨_, h⟩)
                · exact hnb h.symm
                · exact hb₀A h
              have hsub : {a₀, b} ⊆ C.1 \ B.1 := by
                intro x hx
                rcases Finset.mem_insert.mp hx with rfl | hx
                · exact Finset.mem_sdiff.mpr ⟨ha₀C, ha₀B⟩
                · rw [Finset.mem_singleton.mp hx]
                  refine Finset.mem_sdiff.mpr ⟨hbC, fun h => hnb ?_⟩
                  have hm : b ∈ B.1 \ A.1 := Finset.mem_sdiff.mpr ⟨h, hbA⟩
                  rw [hb₀, Finset.mem_singleton] at hm
                  exact hm
              have hle := Finset.card_le_card hsub
              rw [Finset.card_pair (by rintro rfl; exact hbA ha₀A)] at hle
              change (C.1 \ B.1).card = 1 at hCB
              omega
            rw [hb_eq] at hC_eq
            have haI : a ∈ A.1 ∩ B.1 := Finset.mem_inter.mpr ⟨haA, haB⟩
            refine ⟨a, Finset.mem_union_left _ haI, ?_⟩
            simp only [dif_pos haI]
            exact Subtype.ext hC_eq.symm
      rw [hbij, Finset.card_union_of_disjoint]
      · have hc1 : (A.1 ∩ B.1).card = w - 1 := by rw [card_inter_wsub, hd1]
        have hc2 : (Finset.univ \ (A.1 ∪ B.1)).card = n - (w + 1) := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
          have hu := Finset.card_union_add_card_inter A.1 B.1
          rw [A.2, B.2, hc1] at hu
          omega
        rw [hc1, hc2, Nat.cast_add, Nat.cast_sub hw1, Nat.cast_sub hw]
        push_cast
        ring
      · rw [Finset.disjoint_left]
        intro x hx1 hx2
        exact (Finset.mem_sdiff.mp hx2).2 (Finset.mem_union_left _ (Finset.mem_inter.mp hx1).1)
    · rw [if_neg hd1]
      by_cases hd2 : jDist A B = 2
      · rw [if_pos hd2]
        have hd2' : jDist B A = 2 := by rw [jDist_symm]; exact hd2
        have hbij : (Finset.univ.filter fun C : WSub n w => jDist A C = 1 ∧ jDist B C = 1).card =
            ((A.1 \ B.1) ×ˢ (B.1 \ A.1)).card := by
          refine Eq.symm (Finset.card_bij (fun p hp => ⟨insert p.2 (A.1.erase p.1), by
            have haA := (Finset.mem_sdiff.mp (Finset.mem_product.mp hp).1).1
            have hbA := (Finset.mem_sdiff.mp (Finset.mem_product.mp hp).2).2
            have hne : p.2 ∉ A.1.erase p.1 := fun h => hbA (Finset.erase_subset _ _ h)
            rw [Finset.card_insert_of_notMem hne, Finset.card_erase_of_mem haA, A.2]; omega⟩) ?_ ?_ ?_)
          · intro p hp
            rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
            have haA := (Finset.mem_sdiff.mp hp1).1
            have haB := (Finset.mem_sdiff.mp hp1).2
            have hbB := (Finset.mem_sdiff.mp hp2).1
            have hbA := (Finset.mem_sdiff.mp hp2).2
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
            · dsimp [jDist]
              have hs : A.1 \ insert p.2 (A.1.erase p.1) = {p.1} := by
                ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
                exact ⟨fun ⟨hxA, hnx⟩ => by_contra fun hxp => hnx (Or.inr ⟨hxp, hxA⟩),
                  by rintro rfl; exact ⟨haA, fun h' => h'.elim (fun h'' => hbA (h'' ▸ haA)) fun h'' => h''.1 rfl⟩⟩
              rw [hs, Finset.card_singleton]
            · change (B.1 \ insert p.2 (A.1.erase p.1)).card = 1
              have hcard_BA : (B.1 \ A.1).card = 2 := hd2'
              have hs_sub : (B.1 \ A.1).erase p.2 ⊆ B.1 \ insert p.2 (A.1.erase p.1) := by
                intro x hx
                rcases Finset.mem_erase.mp hx with ⟨hxp2, hxBA⟩
                have hxB := (Finset.mem_sdiff.mp hxBA).1
                have hxA := (Finset.mem_sdiff.mp hxBA).2
                exact Finset.mem_sdiff.mpr ⟨hxB, fun h => (Finset.mem_insert.mp h).elim hxp2 fun h' => hxA (Finset.erase_subset _ _ h')⟩
              have hs_sup : B.1 \ insert p.2 (A.1.erase p.1) ⊆ (B.1 \ A.1).erase p.2 := by
                intro x hx
                rcases Finset.mem_sdiff.mp hx with ⟨hxB, hnx⟩
                have hxp2 : x ≠ p.2 := fun h => hnx (h ▸ Finset.mem_insert_self _ _)
                have hxA : x ∉ A.1 := by
                  intro hxA
                  have hxp1 : x = p.1 := by
                    by_contra hne
                    exact hnx (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, hxA⟩))
                  exact haB (hxp1 ▸ hxB)
                exact Finset.mem_erase.mpr ⟨hxp2, Finset.mem_sdiff.mpr ⟨hxB, hxA⟩⟩
              rw [Finset.Subset.antisymm hs_sup hs_sub, Finset.card_erase_of_mem hp2, hcard_BA]
          · intro p₁ hp₁ p₂ hp₂ heq
            have hp1A := (Finset.mem_sdiff.mp (Finset.mem_product.mp hp₁).1).1
            have hp1B := (Finset.mem_sdiff.mp (Finset.mem_product.mp hp₁).2).2
            have hp2A := (Finset.mem_sdiff.mp (Finset.mem_product.mp hp₂).1).1
            have hp2B := (Finset.mem_sdiff.mp (Finset.mem_product.mp hp₂).2).2
            have hval : insert p₁.2 (A.1.erase p₁.1) = insert p₂.2 (A.1.erase p₂.1) :=
              congr_arg Subtype.val heq
            have hb : p₁.2 = p₂.2 := by
              have hm : p₁.2 ∈ insert p₂.2 (A.1.erase p₂.1) := by rw [← hval]; exact Finset.mem_insert_self _ _
              exact (Finset.mem_insert.mp hm).elim id fun h => False.elim (hp1B (Finset.erase_subset _ _ h))
            have ha : p₁.1 = p₂.1 := by
              by_contra hne
              have hm : p₁.1 ∈ insert p₂.2 (A.1.erase p₂.1) := Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, hp1A⟩)
              rw [← hval] at hm
              exact (Finset.mem_insert.mp hm).elim (fun h => hp1B (h ▸ hp1A)) fun h => (Finset.mem_erase.mp h).1 rfl
            exact Prod.ext ha hb
          · intro C hC
            rcases (Finset.mem_filter.mp hC).2 with ⟨hAC, hBC⟩
            have hCA : jDist C A = 1 := by rw [jDist_symm]; exact hAC
            have hCB : jDist C B = 1 := by rw [jDist_symm]; exact hBC
            obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hAC
            obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hCA
            have haA : a ∈ A.1 := (Finset.mem_sdiff.mp (ha ▸ Finset.mem_singleton_self a)).1
            have haC : a ∉ C.1 := (Finset.mem_sdiff.mp (ha ▸ Finset.mem_singleton_self a)).2
            have hbC : b ∈ C.1 := (Finset.mem_sdiff.mp (hb ▸ Finset.mem_singleton_self b)).1
            have hbA : b ∉ A.1 := (Finset.mem_sdiff.mp (hb ▸ Finset.mem_singleton_self b)).2
            have hC_eq : C.1 = insert b (A.1.erase a) := by
              ext x; simp only [Finset.mem_insert, Finset.mem_erase]
              constructor
              · intro hxC
                by_cases hxb : x = b
                · exact Or.inl hxb
                · right
                  have hxA : x ∈ A.1 := by
                    by_contra hxnA
                    have hm : x ∈ C.1 \ A.1 := Finset.mem_sdiff.mpr ⟨hxC, hxnA⟩
                    rw [hb, Finset.mem_singleton] at hm
                    exact hxb hm
                  exact ⟨fun h => haC (h ▸ hxC), hxA⟩
              · rintro (rfl | ⟨hxa, hxA⟩)
                · exact hbC
                · by_contra hxnC
                  have hm : x ∈ A.1 \ C.1 := Finset.mem_sdiff.mpr ⟨hxA, hxnC⟩
                  rw [ha, Finset.mem_singleton] at hm
                  exact hxa hm
            have haB : a ∉ B.1 := by
              intro haB
              have hsub : B.1 \ A.1 ⊆ (B.1 \ C.1) ∪ {b} := by
                intro x hx
                rcases Finset.mem_sdiff.mp hx with ⟨hxB, hxA⟩
                by_cases hxb : x = b
                · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hxb)
                · refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxB, ?_⟩)
                  rw [hC_eq, Finset.mem_insert, Finset.mem_erase]
                  rintro (rfl | ⟨_, h⟩)
                  · exact hxb rfl
                  · exact hxA h
              -- Better: a ∈ A ∩ B, a ∉ C => a ∈ B \ C => (B \ C) = {a} => B \ A ⊆ {b} (impossible!)
              have hBC1 : (B.1 \ C.1).card = 1 := hBC
              have haBC : B.1 \ C.1 = {a} := by
                have hmem : a ∈ B.1 \ C.1 := Finset.mem_sdiff.mpr ⟨haB, haC⟩
                obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hBC1
                have haz : a = z := Finset.mem_singleton.mp (hz ▸ hmem)
                rw [hz, haz]
              have hBA_sub : B.1 \ A.1 ⊆ {b} := by
                intro x hx
                rcases Finset.mem_sdiff.mp hx with ⟨hxB, hxA⟩
                by_contra hxb
                have hxnC : x ∉ C.1 := by
                  rw [hC_eq, Finset.mem_insert, Finset.mem_erase]
                  rintro (h | ⟨_, h⟩)
                  · exact hxb (Finset.mem_singleton.mpr h)
                  · exact hxA h
                have hxa : x = a := Finset.mem_singleton.mp (haBC ▸ Finset.mem_sdiff.mpr ⟨hxB, hxnC⟩)
                exact hxA (hxa ▸ haA)
              have hle := Finset.card_le_card hBA_sub
              rw [Finset.card_singleton] at hle
              change (B.1 \ A.1).card = 2 at hd2'
              omega
            have hbB : b ∈ B.1 := by
              by_contra hnbB
              have hCB1 : (C.1 \ B.1).card = 1 := hCB
              have hbCB : C.1 \ B.1 = {b} := by
                have hmem : b ∈ C.1 \ B.1 := Finset.mem_sdiff.mpr ⟨hbC, hnbB⟩
                obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hCB1
                have hbz : b = z := Finset.mem_singleton.mp (hz ▸ hmem)
                rw [hz, hbz]
              have hAB_sub : A.1 \ B.1 ⊆ {a} := by
                intro x hx
                rcases Finset.mem_sdiff.mp hx with ⟨hxA, hxB⟩
                by_contra hxa
                have hxC : x ∈ C.1 := by
                  rw [hC_eq]; exact Finset.mem_insert_of_mem
                    (Finset.mem_erase.mpr ⟨fun h => hxa (Finset.mem_singleton.mpr h), hxA⟩)
                have hxb : x = b := Finset.mem_singleton.mp (hbCB ▸ Finset.mem_sdiff.mpr ⟨hxC, hxB⟩)
                exact hbA (hxb ▸ hxA)
              have hle := Finset.card_le_card hAB_sub
              rw [Finset.card_singleton] at hle
              change (A.1 \ B.1).card = 2 at hd2
              omega
            refine ⟨(a, b), Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨haA, haB⟩,
              Finset.mem_sdiff.mpr ⟨hbB, hbA⟩⟩, Subtype.ext hC_eq.symm⟩
        rw [hbij, Finset.card_product, Nat.cast_mul]
        rw [show (A.1 \ B.1).card = 2 from hd2, show (B.1 \ A.1).card = 2 from hd2']
        norm_num
      · rw [if_neg hd2]
        have hfilt : (Finset.univ.filter fun C : WSub n w => jDist A C = 1 ∧ jDist B C = 1) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro C _ ⟨hAC, hBC⟩
          have hsub : A.1 \ B.1 ⊆ (A.1 \ C.1) ∪ (C.1 \ B.1) := by
            intro x hx
            rcases Finset.mem_sdiff.mp hx with ⟨hxA, hxB⟩
            by_cases hxC : x ∈ C.1
            · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxC, hxB⟩)
            · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxA, hxC⟩)
          have hle := Finset.card_le_card hsub
          have hle2 : ((A.1 \ C.1) ∪ (C.1 \ B.1)).card ≤ (A.1 \ C.1).card + (C.1 \ B.1).card :=
            Finset.card_union_le _ _
          have hCB : (C.1 \ B.1).card = 1 := by change jDist C B = 1; rw [jDist_symm]; exact hBC
          dsimp [jDist] at hd0 hd1 hd2 hAC
          omega
        rw [hfilt, Finset.card_empty, Nat.cast_zero]

lemma jDist_mul_projMat_formula_zero {n w : ℕ} (hw1 : 1 ≤ w) (hwn : 2 * w ≤ n) :
    (fun A B : WSub n w => (jDist A B : ℝ) * projMat n w 0 A B) =
      jA n w 0 • projMat n w 0 - jC n w 1 • projMat n w 1 := by
  obtain ⟨c, hc, hzero⟩ := jDist_mul_projMat_three_terms (n := n) (w := w) (k := 0) (by omega) hwn
  let M : Matrix (WSub n w) (WSub n w) ℝ := fun A B => (jDist A B : ℝ) * projMat n w 0 A B
  have hc_sum : M = c ⟨0, by omega⟩ • projMat n w 0 + c ⟨1, by omega⟩ • projMat n w 1 := by
    change M = ∑ m : Fin (w + 1), c m • projMat n w m.1 at hc
    rw [hc]
    have hsplit : ∑ m : Fin (w + 1), c m • projMat n w m.1 =
        c ⟨0, by omega⟩ • projMat n w 0 + c ⟨1, by omega⟩ • projMat n w 1 := by
      have h01 : (⟨0, by omega⟩ : Fin (w + 1)) ≠ ⟨1, by omega⟩ := by simp
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, by omega⟩ : Fin (w + 1)))]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ _⟩)]
      have hrest : ∑ m ∈ (Finset.univ.erase (⟨0, by omega⟩ : Fin (w + 1))).erase ⟨1, by omega⟩,
          c m • projMat n w m.1 = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        have hne1 : m.1 ≠ 1 := fun h => (Finset.mem_erase.mp hm).1 (Fin.ext h)
        have hne0 : m.1 ≠ 0 := fun h =>
          (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1 (Fin.ext h)
        have hm2 : 2 ≤ m.1 := by omega
        rw [hzero m (Or.inl hm2), zero_smul]
      rw [hrest, add_zero]
    exact hsplit
  let A₀ := canonA n w (by omega)
  have heq0 : c ⟨0, by omega⟩ * eVal n w 0 0 + c ⟨1, by omega⟩ * eVal n w 1 0 = 0 := by
    have hAA := congr_fun (congr_fun hc_sum A₀) A₀
    have hM0 : M A₀ A₀ = 0 := by simp [M, jDist_eq_zero_iff.mpr rfl]
    have hE0 : projMat n w 0 A₀ A₀ = eVal n w 0 0 := by rw [projMat_eq_eVal A₀ A₀, jDist_eq_zero_iff.mpr rfl]
    have hE1 : projMat n w 1 A₀ A₀ = eVal n w 1 0 := by rw [projMat_eq_eVal A₀ A₀, jDist_eq_zero_iff.mpr rfl]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hM0, hE0, hE1] at hAA
    exact hAA.symm
  have heq1 : c ⟨0, by omega⟩ * jTheta n w 0 * eVal n w 0 0 +
      c ⟨1, by omega⟩ * jTheta n w 1 * eVal n w 1 0 = jTheta n w 0 * eVal n w 0 0 := by
    have hmul : jAdjMatrix n w * M =
        (c ⟨0, by omega⟩ * jTheta n w 0) • projMat n w 0 +
        (c ⟨1, by omega⟩ * jTheta n w 1) • projMat n w 1 := by
      conv_lhs => rw [hc_sum]
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
        jAdjMatrix_mul_projMat (by omega) (by omega),
        jAdjMatrix_mul_projMat (by omega) (by omega), smul_smul, smul_smul]
    have hlhs : (jAdjMatrix n w * M) A₀ A₀ = jTheta n w 0 * eVal n w 0 0 := by
      have he : (jAdjMatrix n w * M) A₀ A₀ = (jAdjMatrix n w * projMat n w 0) A₀ A₀ := by
        simp only [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun B _ => ?_
        dsimp [jAdjMatrix, M]
        by_cases h1 : jDist A₀ B = 1
        · have hsym : jDist B A₀ = 1 := by rw [jDist_symm]; exact h1
          simp [h1, hsym]
        · simp [h1]
      rw [he, jAdjMatrix_mul_projMat (by omega) (by omega), Matrix.smul_apply, smul_eq_mul,
        projMat_eq_eVal A₀ A₀, jDist_eq_zero_iff.mpr rfl]
    have hAA := congr_fun (congr_fun hmul A₀) A₀
    have hE0 : projMat n w 0 A₀ A₀ = eVal n w 0 0 := by rw [projMat_eq_eVal A₀ A₀, jDist_eq_zero_iff.mpr rfl]
    have hE1 : projMat n w 1 A₀ A₀ = eVal n w 1 0 := by rw [projMat_eq_eVal A₀ A₀, jDist_eq_zero_iff.mpr rfl]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hE0, hE1] at hAA
    rw [hlhs] at hAA
    exact hAA.symm
  have hrel := jA_mul_eVal_zero (n := n) (w := w) (k := 0) (by omega) hwn
  rw [zero_add] at hrel
  have hdiff : jTheta n w 0 - jTheta n w 1 = (n : ℝ) := by
    simp only [jTheta, Nat.cast_zero, sub_zero, Nat.cast_one]
    ring
  have h_eq0 : jA n w 0 * eVal n w 0 0 + (-jC n w 1) * eVal n w 1 0 = 0 := by
    linear_combination hrel
  have h_eq1 : jA n w 0 * jTheta n w 0 * eVal n w 0 0 +
      (-jC n w 1) * jTheta n w 1 * eVal n w 1 0 = jTheta n w 0 * eVal n w 0 0 := by
    have hjA0 : jA n w 0 = (w : ℝ) * ((n : ℝ) - w) / (n : ℝ) := by
      simp only [jA, Nat.sub_zero, Nat.cast_add, Nat.cast_one, mul_zero]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      rw [Nat.cast_sub (by omega : w ≤ n)]
      field_simp [hn0, hn1]
    have hth0 : jTheta n w 0 = (w : ℝ) * ((n : ℝ) - w) := by
      simp [jTheta]
    have h_th_eq : jA n w 0 * (jTheta n w 0 - jTheta n w 1) = jTheta n w 0 := by
      rw [hdiff, hjA0, hth0]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      field_simp [hn0]
    linear_combination h_th_eq * eVal n w 0 0 + jTheta n w 1 * hrel
  have he0_pos : 0 < eVal n w 0 0 := eVal_zero_pos (by omega) hwn
  have he1_pos : 0 < eVal n w 1 0 := eVal_zero_pos (by omega) hwn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc1 : c ⟨1, by omega⟩ = -jC n w 1 := by
    have hd : (c ⟨1, by omega⟩ - (-jC n w 1)) * (eVal n w 1 0 * (jTheta n w 1 - jTheta n w 0)) = 0 := by
      linear_combination heq1 - h_eq1 - jTheta n w 0 * (heq0 - h_eq0)
    have hne : eVal n w 1 0 * (jTheta n w 1 - jTheta n w 0) ≠ 0 := by
      rw [show jTheta n w 1 - jTheta n w 0 = -(n : ℝ) by linarith]
      exact mul_ne_zero (ne_of_gt he1_pos) (neg_ne_zero.mpr (ne_of_gt hn_pos))
    have hsub0 : c ⟨1, by omega⟩ - (-jC n w 1) = 0 := (mul_eq_zero.mp hd).resolve_right hne
    linarith
  have hc0 : c ⟨0, by omega⟩ = jA n w 0 := by
    have hsub0 : (c ⟨0, by omega⟩ - jA n w 0) * eVal n w 0 0 = 0 := by
      rw [hc1] at heq0
      linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hsub0).resolve_right (ne_of_gt he0_pos))
  rw [hc0, hc1, neg_smul, ← sub_eq_add_neg] at hc_sum
  exact hc_sum

lemma vandermonde_3x3 {a b c x y z : ℝ} (hab : b < a) (hbc : c < b)
    (h0 : x + y + z = 0) (h1 : a * x + b * y + c * z = 0)
    (h2 : a ^ 2 * x + b ^ 2 * y + c ^ 2 * z = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have hc1 : (a - c) * x + (b - c) * y = 0 := by linear_combination h1 - c * h0
  have hc2 : (a ^ 2 - c ^ 2) * x + (b ^ 2 - c ^ 2) * y = 0 := by
    linear_combination h2 - c ^ 2 * h0
  have hx_mul : (a - b) * (a - c) * x = 0 := by
    linear_combination hc2 - (b + c) * hc1
  have hx : x = 0 := (mul_eq_zero.mp hx_mul).resolve_left
    (mul_ne_zero (by linarith) (by linarith))
  have hy_mul : (b - c) * y = 0 := by linear_combination hc1 - (a - c) * hx
  have hy : y = 0 := (mul_eq_zero.mp hy_mul).resolve_left (by linarith)
  have hz : z = 0 := by linarith
  exact ⟨hx, hy, hz⟩

lemma jDist_mul_projMat_formula {n w k : ℕ} (hk1 : 1 ≤ k) (hkw : k + 1 ≤ w) (hwn : 2 * w ≤ n) :
    (fun A B : WSub n w => (jDist A B : ℝ) * projMat n w k A B) =
      (-jA n w (k - 1)) • projMat n w (k - 1) +
        (jA n w k + jC n w k) • projMat n w k -
        jC n w (k + 1) • projMat n w (k + 1) := by
  obtain ⟨c, hc, hzero⟩ := jDist_mul_projMat_three_terms (n := n) (w := w) (k := k) (by omega) hwn
  let M : Matrix (WSub n w) (WSub n w) ℝ := fun A B => (jDist A B : ℝ) * projMat n w k A B
  let fm : Fin (w + 1) := ⟨k - 1, by omega⟩
  let f0 : Fin (w + 1) := ⟨k, by omega⟩
  let fp : Fin (w + 1) := ⟨k + 1, by omega⟩
  have hfm0 : fm ≠ f0 := by simp [fm, f0, Fin.ext_iff]; omega
  have hfmp : fm ≠ fp := by simp [fm, fp, Fin.ext_iff]
  have hf0p : f0 ≠ fp := by simp [f0, fp, Fin.ext_iff]
  have hc_sum : M = c fm • projMat n w (k - 1) + c f0 • projMat n w k +
      c fp • projMat n w (k + 1) := by
    change M = ∑ m : Fin (w + 1), c m • projMat n w m.1 at hc
    rw [hc]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ fm)]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hfm0.symm, Finset.mem_univ _⟩)]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hf0p.symm,
      Finset.mem_erase.mpr ⟨hfmp.symm, Finset.mem_univ _⟩⟩)]
    have hrest : ∑ m ∈ ((Finset.univ.erase fm).erase f0).erase fp,
        c m • projMat n w m.1 = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      have h1 : m.1 ≠ fp.1 := fun h => (Finset.mem_erase.mp hm).1 (Fin.ext h)
      have h2 : m.1 ≠ f0.1 := fun h =>
        (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1 (Fin.ext h)
      have h3 : m.1 ≠ fm.1 := fun h =>
        (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).2).1 (Fin.ext h)
      have hfar : k + 2 ≤ m.1 ∨ m.1 + 2 ≤ k := by
        dsimp [fm, f0, fp] at h1 h2 h3
        omega
      rw [hzero m hfar, zero_smul]
    rw [hrest, add_zero]
    dsimp [fm, f0, fp]
    abel
  let A₀ := canonA n w (by omega)
  have hE_m : projMat n w (k - 1) A₀ A₀ = eVal n w (k - 1) 0 := by
    rw [projMat_eq_eVal A₀ A₀, jDist_eq_zero_iff.mpr rfl]
  have hE_0 : projMat n w k A₀ A₀ = eVal n w k 0 := by
    rw [projMat_eq_eVal A₀ A₀, jDist_eq_zero_iff.mpr rfl]
  have hE_p : projMat n w (k + 1) A₀ A₀ = eVal n w (k + 1) 0 := by
    rw [projMat_eq_eVal A₀ A₀, jDist_eq_zero_iff.mpr rfl]
  have heq0 : c fm * eVal n w (k - 1) 0 + c f0 * eVal n w k 0 + c fp * eVal n w (k + 1) 0 = 0 := by
    have hAA := congr_fun (congr_fun hc_sum A₀) A₀
    have hM0 : M A₀ A₀ = 0 := by simp [M, jDist_eq_zero_iff.mpr rfl]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hM0, hE_m, hE_0, hE_p] at hAA
    exact hAA.symm
  have hAM_eq : (jAdjMatrix n w * M) A₀ A₀ = jTheta n w k * eVal n w k 0 := by
    have he : (jAdjMatrix n w * M) A₀ A₀ = (jAdjMatrix n w * projMat n w k) A₀ A₀ := by
      simp only [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun B _ => ?_
      dsimp [jAdjMatrix, M]
      by_cases h1 : jDist A₀ B = 1
      · have hsym : jDist B A₀ = 1 := by rw [jDist_symm]; exact h1
        simp [h1, hsym]
      · simp [h1]
    rw [he, jAdjMatrix_mul_projMat (by omega) (by omega), Matrix.smul_apply, smul_eq_mul, hE_0]
  have heq1 : c fm * jTheta n w (k - 1) * eVal n w (k - 1) 0 +
      c f0 * jTheta n w k * eVal n w k 0 +
      c fp * jTheta n w (k + 1) * eVal n w (k + 1) 0 = jTheta n w k * eVal n w k 0 := by
    have hmul : jAdjMatrix n w * M =
        (c fm * jTheta n w (k - 1)) • projMat n w (k - 1) +
        (c f0 * jTheta n w k) • projMat n w k +
        (c fp * jTheta n w (k + 1)) • projMat n w (k + 1) := by
      conv_lhs => rw [hc_sum]
      rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
        jAdjMatrix_mul_projMat (by omega) (by omega),
        jAdjMatrix_mul_projMat (by omega) (by omega),
        jAdjMatrix_mul_projMat (by omega) (by omega), smul_smul, smul_smul, smul_smul]
    have hAA := congr_fun (congr_fun hmul A₀) A₀
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hE_m, hE_0, hE_p] at hAA
    rw [hAM_eq] at hAA
    exact hAA.symm
  have hA2M_eq : (jAdjMatrix n w * (jAdjMatrix n w * M)) A₀ A₀ =
      (2 * (jTheta n w k) ^ 2 - ((n : ℝ) - 2) * jTheta n w k - 2 * (w : ℝ) * ((n : ℝ) - w)) *
        eVal n w k 0 := by
    have hA2_E : (jAdjMatrix n w * (jAdjMatrix n w * projMat n w k)) A₀ A₀ =
        (jTheta n w k) ^ 2 * eVal n w k 0 := by
      rw [jAdjMatrix_mul_projMat (by omega) (by omega), Matrix.mul_smul,
        jAdjMatrix_mul_projMat (by omega) (by omega), smul_smul, Matrix.smul_apply, smul_eq_mul,
        hE_0, sq]
    have hA2_E_expand : (jAdjMatrix n w * (jAdjMatrix n w * projMat n w k)) A₀ A₀ =
        (w : ℝ) * ((n : ℝ) - w) * eVal n w k 0 +
          ((n : ℝ) - 2) * (∑ B ∈ Finset.univ.filter (fun B : WSub n w => jDist A₀ B = 1),
            projMat n w k B A₀) +
          4 * (∑ B ∈ Finset.univ.filter (fun B : WSub n w => jDist A₀ B = 2),
            projMat n w k B A₀) := by
      rw [← Matrix.mul_assoc, Matrix.mul_apply]
      have hterm : ∀ B : WSub n w, (jAdjMatrix n w * jAdjMatrix n w) A₀ B * projMat n w k B A₀ =
          (if jDist A₀ B = 0 then (w : ℝ) * ((n : ℝ) - w) * projMat n w k B A₀ else 0) +
          (if jDist A₀ B = 1 then ((n : ℝ) - 2) * projMat n w k B A₀ else 0) +
          (if jDist A₀ B = 2 then 4 * projMat n w k B A₀ else 0) := by
        intro B
        rw [jAdjMatrix_sq_apply (by omega) (by omega) A₀ B]
        by_cases h0 : jDist A₀ B = 0
        · rw [if_pos h0, if_pos h0, if_neg (by omega), if_neg (by omega)]; ring
        · by_cases h1 : jDist A₀ B = 1
          · rw [if_neg h0, if_pos h1, if_neg h0, if_pos h1, if_neg (by omega)]; ring
          · by_cases h2 : jDist A₀ B = 2
            · rw [if_neg h0, if_neg h1, if_pos h2, if_neg h0, if_neg h1, if_pos h2]; ring
            · rw [if_neg h0, if_neg h1, if_neg h2, if_neg h0, if_neg h1, if_neg h2]; ring
      simp_rw [hterm, Finset.sum_add_distrib]
      have hs0 : (∑ B : WSub n w, if jDist A₀ B = 0 then (w : ℝ) * ((n : ℝ) - w) * projMat n w k B A₀ else 0) =
          (w : ℝ) * ((n : ℝ) - w) * eVal n w k 0 := by
        rw [Finset.sum_eq_single A₀]
        · rw [if_pos (jDist_eq_zero_iff.mpr rfl), hE_0]
        · intro B _ hBA
          rw [if_neg (fun h => hBA (jDist_eq_zero_iff.mp h).symm)]
        · intro h; exact False.elim (h (Finset.mem_univ A₀))
      have hs1 : (∑ B : WSub n w, if jDist A₀ B = 1 then ((n : ℝ) - 2) * projMat n w k B A₀ else 0) =
          ((n : ℝ) - 2) * ∑ B ∈ Finset.univ.filter (fun B : WSub n w => jDist A₀ B = 1),
            projMat n w k B A₀ := by
        rw [Finset.mul_sum, Finset.sum_filter]
      have hs2 : (∑ B : WSub n w, if jDist A₀ B = 2 then 4 * projMat n w k B A₀ else 0) =
          4 * ∑ B ∈ Finset.univ.filter (fun B : WSub n w => jDist A₀ B = 2),
            projMat n w k B A₀ := by
        rw [Finset.mul_sum, Finset.sum_filter]
      rw [hs0, hs1, hs2]
    have hsum1_eq : (∑ B ∈ Finset.univ.filter (fun B : WSub n w => jDist A₀ B = 1),
        projMat n w k B A₀) = jTheta n w k * eVal n w k 0 := by
      have h1 : (jAdjMatrix n w * projMat n w k) A₀ A₀ =
          ∑ B ∈ Finset.univ.filter (fun B : WSub n w => jDist A₀ B = 1),
            projMat n w k B A₀ := by
        simp only [Matrix.mul_apply, jAdjMatrix]
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun B _ => ?_
        split_ifs <;> simp
      rw [← h1, jAdjMatrix_mul_projMat (by omega) (by omega), Matrix.smul_apply, smul_eq_mul, hE_0]
    have hA2_M_expand : (jAdjMatrix n w * (jAdjMatrix n w * M)) A₀ A₀ =
        ((n : ℝ) - 2) * (∑ B ∈ Finset.univ.filter (fun B : WSub n w => jDist A₀ B = 1),
            projMat n w k B A₀) +
          8 * (∑ B ∈ Finset.univ.filter (fun B : WSub n w => jDist A₀ B = 2),
            projMat n w k B A₀) := by
      rw [← Matrix.mul_assoc, Matrix.mul_apply]
      have hterm : ∀ B : WSub n w, (jAdjMatrix n w * jAdjMatrix n w) A₀ B * M B A₀ =
          (if jDist A₀ B = 1 then ((n : ℝ) - 2) * projMat n w k B A₀ else 0) +
          (if jDist A₀ B = 2 then 8 * projMat n w k B A₀ else 0) := by
        intro B
        rw [jAdjMatrix_sq_apply (by omega) (by omega) A₀ B]
        dsimp [M]
        rw [jDist_symm B A₀]
        by_cases h0 : jDist A₀ B = 0
        · rw [if_pos h0, if_neg (by omega), if_neg (by omega), h0]; simp
        · by_cases h1 : jDist A₀ B = 1
          · rw [if_neg h0, if_pos h1, if_pos h1, if_neg (by omega), h1]; simp
          · by_cases h2 : jDist A₀ B = 2
            · rw [if_neg h0, if_neg h1, if_pos h2, if_neg h1, if_pos h2, h2]; ring
            · rw [if_neg h0, if_neg h1, if_neg h2, if_neg h1, if_neg h2]; ring
      simp_rw [hterm, Finset.sum_add_distrib]
      have hs1 : (∑ B : WSub n w, if jDist A₀ B = 1 then ((n : ℝ) - 2) * projMat n w k B A₀ else 0) =
          ((n : ℝ) - 2) * ∑ B ∈ Finset.univ.filter (fun B : WSub n w => jDist A₀ B = 1),
            projMat n w k B A₀ := by
        rw [Finset.mul_sum, Finset.sum_filter]
      have hs2 : (∑ B : WSub n w, if jDist A₀ B = 2 then 8 * projMat n w k B A₀ else 0) =
          8 * ∑ B ∈ Finset.univ.filter (fun B : WSub n w => jDist A₀ B = 2),
            projMat n w k B A₀ := by
        rw [Finset.mul_sum, Finset.sum_filter]
      rw [hs1, hs2]
    rw [hA2_E, hsum1_eq] at hA2_E_expand
    rw [hsum1_eq] at hA2_M_expand
    linarith
  have heq2 : c fm * (jTheta n w (k - 1)) ^ 2 * eVal n w (k - 1) 0 +
      c f0 * (jTheta n w k) ^ 2 * eVal n w k 0 +
      c fp * (jTheta n w (k + 1)) ^ 2 * eVal n w (k + 1) 0 =
      (2 * (jTheta n w k) ^ 2 - ((n : ℝ) - 2) * jTheta n w k - 2 * (w : ℝ) * ((n : ℝ) - w)) *
        eVal n w k 0 := by
    have hmul : jAdjMatrix n w * (jAdjMatrix n w * M) =
        (c fm * (jTheta n w (k - 1)) ^ 2) • projMat n w (k - 1) +
        (c f0 * (jTheta n w k) ^ 2) • projMat n w k +
        (c fp * (jTheta n w (k + 1)) ^ 2) • projMat n w (k + 1) := by
      conv_lhs => rw [hc_sum]
      simp only [Matrix.mul_add, Matrix.mul_smul,
        jAdjMatrix_mul_projMat (n := n) (w := w) (k := k - 1) (by omega) (by omega),
        jAdjMatrix_mul_projMat (n := n) (w := w) (k := k) (by omega) (by omega),
        jAdjMatrix_mul_projMat (n := n) (w := w) (k := k + 1) (by omega) (by omega),
        smul_smul, sq]
      simp only [mul_assoc]
    have hAA := congr_fun (congr_fun hmul A₀) A₀
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hE_m, hE_0, hE_p] at hAA
    rw [hA2M_eq] at hAA
    exact hAA.symm
  have hrel1 := jA_mul_eVal_zero (n := n) (w := w) (k := k - 1) (by omega) hwn
  have hrel1' : jA n w (k - 1) * eVal n w (k - 1) 0 = jC n w k * eVal n w k 0 := by
    simpa [Nat.sub_add_cancel hk1] using hrel1
  have hrel2 := jA_mul_eVal_zero (n := n) (w := w) (k := k) (by omega) hwn
  have hne1 : ((n : ℝ) - 2 * k + 2) ≠ 0 := by
    have : (2 * k : ℝ) ≤ n := by exact_mod_cast (by omega : 2 * k ≤ n)
    linarith
  have hne2 : ((n : ℝ) - 2 * k + 1) ≠ 0 := by
    have : (2 * k : ℝ) ≤ n := by exact_mod_cast (by omega : 2 * k ≤ n)
    linarith
  have hne3 : ((n : ℝ) - 2 * k) ≠ 0 := by
    have : (2 * k + 1 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 * k + 1 ≤ n)
    linarith
  have hjA_cast : jA n w k =
      ((n : ℝ) - k + 1) * ((w : ℝ) - k) * ((n : ℝ) - w - k) /
        (((n : ℝ) - 2 * k + 1) * ((n : ℝ) - 2 * k)) := by
    dsimp [jA]
    simp only [Nat.cast_add, Nat.cast_sub (by omega : k ≤ n),
      Nat.cast_sub (by omega : k ≤ w), Nat.cast_sub (by omega : k ≤ n - w),
      Nat.cast_sub (by omega : w ≤ n), Nat.cast_sub (by omega : 2 * k ≤ n),
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have hjC_cast : jC n w k =
      ((k : ℝ) * ((w : ℝ) - k + 1) * ((n : ℝ) - w - k + 1)) /
        (((n : ℝ) - 2 * k + 2) * ((n : ℝ) - 2 * k + 1)) := by
    dsimp [jC]
    rw [if_neg (by omega)]
    simp only [Nat.cast_add, Nat.cast_sub (by omega : k ≤ w),
      Nat.cast_sub (by omega : k ≤ n - w), Nat.cast_sub (by omega : w ≤ n),
      Nat.cast_sub (by omega : 2 * k ≤ n), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have hth_m : jTheta n w (k - 1) = ((w : ℝ) - k + 1) * ((n : ℝ) - w - k + 1) - (k - 1) := by
    dsimp [jTheta]
    rw [Nat.cast_sub hk1]
    push_cast; ring
  have hth_0 : jTheta n w k = ((w : ℝ) - k) * ((n : ℝ) - w - k) - k := rfl
  have hth_p : jTheta n w (k + 1) = ((w : ℝ) - k - 1) * ((n : ℝ) - w - k - 1) - (k + 1) := by
    dsimp [jTheta]
    push_cast; ring
  have hdA : ((n : ℝ) - 2 * k + 1) * ((n : ℝ) - 2 * k) ≠ 0 := mul_ne_zero hne2 hne3
  have hdC : ((n : ℝ) - 2 * k + 2) * ((n : ℝ) - 2 * k + 1) ≠ 0 := mul_ne_zero hne1 hne2
  have h123 : ((n : ℝ) - 2 * k + 2) * (((n : ℝ) - 2 * k + 1) * ((n : ℝ) - 2 * k)) ≠ 0 :=
    mul_ne_zero hne1 hdA
  have hA_mul : jA n w k * (((n : ℝ) - 2 * k + 1) * ((n : ℝ) - 2 * k)) =
      ((n : ℝ) - k + 1) * ((w : ℝ) - k) * ((n : ℝ) - w - k) := by
    rw [hjA_cast, div_mul_cancel₀ _ hdA]
  have hC_mul : jC n w k * (((n : ℝ) - 2 * k + 2) * ((n : ℝ) - 2 * k + 1)) =
      (k : ℝ) * ((w : ℝ) - k + 1) * ((n : ℝ) - w - k + 1) := by
    rw [hjC_cast, div_mul_cancel₀ _ hdC]
  have hp1 : (-jC n w k) * jTheta n w (k - 1) + (jA n w k + jC n w k) * jTheta n w k +
      (-jA n w k) * jTheta n w (k + 1) = jTheta n w k := by
    apply mul_right_cancel₀ h123
    have hmul_lhs : ((-jC n w k) * jTheta n w (k - 1) + (jA n w k + jC n w k) * jTheta n w k +
        (-jA n w k) * jTheta n w (k + 1)) *
        (((n : ℝ) - 2 * k + 2) * (((n : ℝ) - 2 * k + 1) * ((n : ℝ) - 2 * k))) =
        (jC n w k * (((n : ℝ) - 2 * k + 2) * ((n : ℝ) - 2 * k + 1))) *
          ((jTheta n w k - jTheta n w (k - 1)) * ((n : ℝ) - 2 * k)) +
        (jA n w k * (((n : ℝ) - 2 * k + 1) * ((n : ℝ) - 2 * k))) *
          ((jTheta n w k - jTheta n w (k + 1)) * ((n : ℝ) - 2 * k + 2)) := by ring
    rw [hmul_lhs, hA_mul, hC_mul, hth_m, hth_0, hth_p]
    ring
  have hp2 : (-jC n w k) * (jTheta n w (k - 1)) ^ 2 +
      (jA n w k + jC n w k) * (jTheta n w k) ^ 2 +
      (-jA n w k) * (jTheta n w (k + 1)) ^ 2 =
      2 * (jTheta n w k) ^ 2 - ((n : ℝ) - 2) * jTheta n w k - 2 * (w : ℝ) * ((n : ℝ) - w) := by
    apply mul_right_cancel₀ h123
    have hmul_lhs : ((-jC n w k) * (jTheta n w (k - 1)) ^ 2 +
        (jA n w k + jC n w k) * (jTheta n w k) ^ 2 +
        (-jA n w k) * (jTheta n w (k + 1)) ^ 2) *
        (((n : ℝ) - 2 * k + 2) * (((n : ℝ) - 2 * k + 1) * ((n : ℝ) - 2 * k))) =
        (jC n w k * (((n : ℝ) - 2 * k + 2) * ((n : ℝ) - 2 * k + 1))) *
          (((jTheta n w k) ^ 2 - (jTheta n w (k - 1)) ^ 2) * ((n : ℝ) - 2 * k)) +
        (jA n w k * (((n : ℝ) - 2 * k + 1) * ((n : ℝ) - 2 * k))) *
          (((jTheta n w k) ^ 2 - (jTheta n w (k + 1)) ^ 2) * ((n : ℝ) - 2 * k + 2)) := by ring
    rw [hmul_lhs, hA_mul, hC_mul, hth_m, hth_0, hth_p]
    ring
  let dX := (c fm - (-jA n w (k - 1))) * eVal n w (k - 1) 0
  let dY := (c f0 - (jA n w k + jC n w k)) * eVal n w k 0
  let dZ := (c fp - (-jC n w (k + 1))) * eVal n w (k + 1) 0
  have hd0 : dX + dY + dZ = 0 := by
    dsimp [dX, dY, dZ]
    linear_combination heq0 + hrel1' - hrel2
  have hd1 : jTheta n w (k - 1) * dX + jTheta n w k * dY + jTheta n w (k + 1) * dZ = 0 := by
    dsimp [dX, dY, dZ]
    have hsum_t : (-jA n w (k - 1)) * jTheta n w (k - 1) * eVal n w (k - 1) 0 +
        (jA n w k + jC n w k) * jTheta n w k * eVal n w k 0 +
        (-jC n w (k + 1)) * jTheta n w (k + 1) * eVal n w (k + 1) 0 =
        jTheta n w k * eVal n w k 0 := by
      have hh : (-jA n w (k - 1)) * jTheta n w (k - 1) * eVal n w (k - 1) 0 =
          (-jC n w k) * jTheta n w (k - 1) * eVal n w k 0 := by
        linear_combination (-jTheta n w (k - 1)) * hrel1'
      have hh2 : (-jC n w (k + 1)) * jTheta n w (k + 1) * eVal n w (k + 1) 0 =
          (-jA n w k) * jTheta n w (k + 1) * eVal n w k 0 := by
        linear_combination jTheta n w (k + 1) * hrel2
      rw [hh, hh2]
      calc (-jC n w k) * jTheta n w (k - 1) * eVal n w k 0 +
            (jA n w k + jC n w k) * jTheta n w k * eVal n w k 0 +
            (-jA n w k) * jTheta n w (k + 1) * eVal n w k 0
          = ((-jC n w k) * jTheta n w (k - 1) + (jA n w k + jC n w k) * jTheta n w k +
              (-jA n w k) * jTheta n w (k + 1)) * eVal n w k 0 := by ring
        _ = jTheta n w k * eVal n w k 0 := by rw [hp1]
    linear_combination heq1 - hsum_t
  have hd2 : (jTheta n w (k - 1)) ^ 2 * dX + (jTheta n w k) ^ 2 * dY +
      (jTheta n w (k + 1)) ^ 2 * dZ = 0 := by
    dsimp [dX, dY, dZ]
    have hsum_t : (-jA n w (k - 1)) * (jTheta n w (k - 1)) ^ 2 * eVal n w (k - 1) 0 +
        (jA n w k + jC n w k) * (jTheta n w k) ^ 2 * eVal n w k 0 +
        (-jC n w (k + 1)) * (jTheta n w (k + 1)) ^ 2 * eVal n w (k + 1) 0 =
        (2 * (jTheta n w k) ^ 2 - ((n : ℝ) - 2) * jTheta n w k -
          2 * (w : ℝ) * ((n : ℝ) - w)) * eVal n w k 0 := by
      have hh : (-jA n w (k - 1)) * (jTheta n w (k - 1)) ^ 2 * eVal n w (k - 1) 0 =
          (-jC n w k) * (jTheta n w (k - 1)) ^ 2 * eVal n w k 0 := by
        linear_combination (-(jTheta n w (k - 1)) ^ 2) * hrel1'
      have hh2 : (-jC n w (k + 1)) * (jTheta n w (k + 1)) ^ 2 * eVal n w (k + 1) 0 =
          (-jA n w k) * (jTheta n w (k + 1)) ^ 2 * eVal n w k 0 := by
        linear_combination (jTheta n w (k + 1)) ^ 2 * hrel2
      rw [hh, hh2]
      calc (-jC n w k) * (jTheta n w (k - 1)) ^ 2 * eVal n w k 0 +
            (jA n w k + jC n w k) * (jTheta n w k) ^ 2 * eVal n w k 0 +
            (-jA n w k) * (jTheta n w (k + 1)) ^ 2 * eVal n w k 0
          = ((-jC n w k) * (jTheta n w (k - 1)) ^ 2 +
              (jA n w k + jC n w k) * (jTheta n w k) ^ 2 +
              (-jA n w k) * (jTheta n w (k + 1)) ^ 2) * eVal n w k 0 := by ring
        _ = (2 * (jTheta n w k) ^ 2 - ((n : ℝ) - 2) * jTheta n w k -
              2 * (w : ℝ) * ((n : ℝ) - w)) * eVal n w k 0 := by rw [hp2]
    linear_combination heq2 - hsum_t
  have hgt1 : jTheta n w k < jTheta n w (k - 1) := by
    rw [hth_m, hth_0]
    have : (2 * k : ℝ) ≤ n := by exact_mod_cast (by omega : 2 * k ≤ n)
    linarith
  have hgt2 : jTheta n w (k + 1) < jTheta n w k := by
    rw [hth_0, hth_p]
    have : (2 * k + 2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 * k + 2 ≤ n)
    linarith
  obtain ⟨hdX0, hdY0, hdZ0⟩ := vandermonde_3x3 hgt1 hgt2 hd0 hd1 hd2
  have hem_pos : 0 < eVal n w (k - 1) 0 := eVal_zero_pos (by omega) hwn
  have he0_pos : 0 < eVal n w k 0 := eVal_zero_pos (by omega) hwn
  have hep_pos : 0 < eVal n w (k + 1) 0 := eVal_zero_pos (by omega) hwn
  have hcm : c fm = -jA n w (k - 1) := by
    have : c fm - (-jA n w (k - 1)) = 0 := (mul_eq_zero.mp hdX0).resolve_right (ne_of_gt hem_pos)
    linarith
  have hc0 : c f0 = jA n w k + jC n w k := by
    have : c f0 - (jA n w k + jC n w k) = 0 := (mul_eq_zero.mp hdY0).resolve_right (ne_of_gt he0_pos)
    linarith
  have hcp : c fp = -jC n w (k + 1) := by
    have : c fp - (-jC n w (k + 1)) = 0 := (mul_eq_zero.mp hdZ0).resolve_right (ne_of_gt hep_pos)
    linarith
  rw [hcm, hc0, hcp] at hc_sum
  rw [neg_smul (jC n w (k + 1)), ← sub_eq_add_neg] at hc_sum
  exact hc_sum

end JohnsonScheme

section HadamardBound

/-- Test vector supported on `k ∈ [t - 100, t]` with `t = 9n / 1000` and geometric weight `(19 / 200)^j`. -/
noncomputable def testVec (n k : ℕ) : ℝ :=
  let t := 9 * n / 1000
  if t - 100 ≤ k ∧ k ≤ t then
    ((19 : ℝ) / 200) ^ (k - (t - 100)) *
      Real.sin (((k - (t - 100) + 1 : ℕ) : ℝ) * Real.pi / 102)
  else 0

lemma testVec_nonneg (n k : ℕ) : 0 ≤ testVec n k := by
  dsimp only [testVec]
  split_ifs with h
  · refine mul_nonneg (by positivity) (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) ?_)
    have hle : ((k - (9 * n / 1000 - 100) + 1 : ℕ) : ℝ) ≤ 102 := by exact_mod_cast (by omega : k - (9 * n / 1000 - 100) + 1 ≤ 102)
    have hpi : 0 ≤ Real.pi := le_of_lt Real.pi_pos
    nlinarith
  · exact le_refl 0

lemma testVec_pos {n k : ℕ} (hk1 : 9 * n / 1000 - 100 ≤ k) (hk2 : k ≤ 9 * n / 1000) :
    0 < testVec n k := by
  dsimp only [testVec]
  rw [if_pos ⟨hk1, hk2⟩]
  refine mul_pos (by positivity) (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
  · have h1 : (1 : ℝ) ≤ ((k - (9 * n / 1000 - 100) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ k - (9 * n / 1000 - 100) + 1)
    have hpi := Real.pi_pos
    positivity
  · have hlt : ((k - (9 * n / 1000 - 100) + 1 : ℕ) : ℝ) ≤ 101 := by
      exact_mod_cast (by omega : k - (9 * n / 1000 - 100) + 1 ≤ 101)
    have hpi := Real.pi_pos
    nlinarith

lemma testVec_eq_zero {n k : ℕ} (hk : k < 9 * n / 1000 - 100 ∨ 9 * n / 1000 < k) :
    testVec n k = 0 := by
  dsimp only [testVec]
  rw [if_neg (by omega)]

/-- Eigenvalue coefficient of `(j_p - jDist) ⊙ Q` in eigenspace `m`. -/
noncomputable def clzLam (n m : ℕ) : ℝ :=
  let w := 11 * n / 100
  let jp := (751 : ℝ) / 10000 * n
  (if m + 1 ≤ w then jA n w m * testVec n (m + 1) else 0) +
    (jp - jA n w m - jC n w m) * testVec n m +
    (if 1 ≤ m then jC n w m * testVec n (m - 1) else 0)

lemma jA_nonneg (n w m : ℕ) : 0 ≤ jA n w m := by
  unfold jA; positivity

lemma jC_nonneg (n w m : ℕ) : 0 ≤ jC n w m := by
  unfold jC; split_ifs <;> positivity

lemma jA_bounds {n m : ℕ} (hn : 10 ^ 7 ≤ n)
    (hm1 : 9 * n / 1000 - 100 ≤ m) (hm2 : m ≤ 9 * n / 1000) :
    (914 : ℝ) / 10000 * n ≤ jA n (11 * n / 100) m ∧
      jA n (11 * n / 100) m ≤ (915 : ℝ) / 10000 * n := by
  set w := 11 * n / 100
  have hnR : (10000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hwR_lo : (11 : ℝ) / 100 * n - 1 ≤ w := by
    have hnat : (11 * n : ℝ) ≤ 100 * (w : ℝ) + 99 := by
      exact_mod_cast (by omega : 11 * n ≤ 100 * w + 99)
    linarith
  have hwR_hi : (w : ℝ) ≤ (11 : ℝ) / 100 * n := by
    have hnat : (100 * w : ℝ) ≤ 11 * (n : ℝ) := by exact_mod_cast (by omega : 100 * w ≤ 11 * n)
    linarith
  have hmR_lo : (9 : ℝ) / 1000 * n - 101 ≤ m := by
    have hnat : (9 * n : ℝ) ≤ 1000 * (m : ℝ) + 100999 := by
      exact_mod_cast (by omega : 9 * n ≤ 1000 * m + 100999)
    linarith
  have hmR_hi : (m : ℝ) ≤ (9 : ℝ) / 1000 * n := by
    have hnat : (1000 * m : ℝ) ≤ 9 * (n : ℝ) := by exact_mod_cast (by omega : 1000 * m ≤ 9 * n)
    linarith
  have h1 : m ≤ n := by omega
  have h2 : m ≤ w := by omega
  have h3 : m ≤ n - w := by omega
  have h4 : 2 * m ≤ n := by omega
  have hw_le : w ≤ n := by omega
  have hc1 : ((n - m + 1 : ℕ) : ℝ) = (n : ℝ) - m + 1 := by rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub h1]
  have hc2 : ((w - m : ℕ) : ℝ) = (w : ℝ) - m := Nat.cast_sub h2
  have hc3 : ((n - w - m : ℕ) : ℝ) = (n : ℝ) - w - m := by
    rw [Nat.cast_sub h3, Nat.cast_sub hw_le]
  have hc4 : ((n - 2 * m + 1 : ℕ) : ℝ) = (n : ℝ) - 2 * m + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub h4, Nat.cast_mul, Nat.cast_ofNat]
  have hc5 : ((n - 2 * m : ℕ) : ℝ) = (n : ℝ) - 2 * m := by
    rw [Nat.cast_sub h4, Nat.cast_mul, Nat.cast_ofNat]
  unfold jA
  rw [hc1, hc2, hc3, hc4, hc5]
  have hden_pos : 0 < ((n : ℝ) - 2 * m + 1) * ((n : ℝ) - 2 * m) := by
    have ha : 0 < (n : ℝ) - 2 * m + 1 := by linarith
    have hb : 0 < (n : ℝ) - 2 * m := by linarith
    exact mul_pos ha hb
  have hnum_lo : (0.991 * 0.101 * 0.881 : ℝ) * (n : ℝ) ^ 3 - (n : ℝ) ^ 2 ≤
      ((n : ℝ) - m + 1) * ((w : ℝ) - m) * ((n : ℝ) - w - m) := by
    have h1 : (0.991 : ℝ) * n ≤ (n : ℝ) - m + 1 := by linarith
    have h2' : (0.101 : ℝ) * n - 1 ≤ (w : ℝ) - m := by linarith
    have h3' : (0.881 : ℝ) * n ≤ (n : ℝ) - w - m := by linarith
    have h1_nn : 0 ≤ (0.991 : ℝ) * n := by positivity
    have h2_nn : 0 ≤ (0.101 : ℝ) * n - 1 := by linarith
    have h12 : (0.991 * (n : ℝ)) * (0.101 * (n : ℝ) - 1) ≤ ((n : ℝ) - m + 1) * ((w : ℝ) - m) := by
      nlinarith only [h1, h2', h1_nn, h2_nn]
    have h12_nn : 0 ≤ (0.991 * (n : ℝ)) * (0.101 * (n : ℝ) - 1) := mul_nonneg h1_nn h2_nn
    have h123 : (0.991 * (n : ℝ)) * (0.101 * (n : ℝ) - 1) * (0.881 * (n : ℝ)) ≤
        ((n : ℝ) - m + 1) * ((w : ℝ) - m) * ((n : ℝ) - w - m) := by
      nlinarith only [h12, h3', h12_nn, hnR]
    nlinarith only [h123, hnR]
  have hnum_hi : ((n : ℝ) - m + 1) * ((w : ℝ) - m) * ((n : ℝ) - w - m) ≤
      (0.991 * 0.101 * 0.881 : ℝ) * (n : ℝ) ^ 3 + 250 * (n : ℝ) ^ 2 := by
    have h1 : (n : ℝ) - m + 1 ≤ 0.991 * n + 102 := by linarith
    have h2' : (w : ℝ) - m ≤ 0.101 * n + 101 := by linarith
    have h3' : (n : ℝ) - w - m ≤ 0.881 * n + 102 := by linarith
    have h1_nn : 0 ≤ (n : ℝ) - m + 1 := by linarith
    have h2_nn : 0 ≤ (w : ℝ) - m := by linarith
    have h3_nn : 0 ≤ (n : ℝ) - w - m := by linarith
    have h12 : ((n : ℝ) - m + 1) * ((w : ℝ) - m) ≤ (0.991 * (n : ℝ) + 102) * (0.101 * (n : ℝ) + 101) := by
      nlinarith only [h1, h2', h1_nn, h2_nn]
    have h12_nn : 0 ≤ ((n : ℝ) - m + 1) * ((w : ℝ) - m) := mul_nonneg h1_nn h2_nn
    have h123 : ((n : ℝ) - m + 1) * ((w : ℝ) - m) * ((n : ℝ) - w - m) ≤
        (0.991 * (n : ℝ) + 102) * (0.101 * (n : ℝ) + 101) * (0.881 * (n : ℝ) + 102) := by
      nlinarith only [h12, h3', h12_nn, h3_nn, hnR]
    nlinarith only [h123, hnR]
  have hden_lo : (0.982 * (n : ℝ)) ^ 2 ≤ ((n : ℝ) - 2 * m + 1) * ((n : ℝ) - 2 * m) := by
    have ha : (0.982 : ℝ) * n ≤ (n : ℝ) - 2 * m + 1 := by linarith
    have hb : (0.982 : ℝ) * n ≤ (n : ℝ) - 2 * m := by linarith
    nlinarith only [ha, hb, hnR]
  have hden_hi : ((n : ℝ) - 2 * m + 1) * ((n : ℝ) - 2 * m) ≤ (0.982 * (n : ℝ)) ^ 2 + 405 * (n : ℝ) := by
    have ha : (n : ℝ) - 2 * m + 1 ≤ 0.982 * n + 203 := by linarith
    have hb : (n : ℝ) - 2 * m ≤ 0.982 * n + 202 := by linarith
    have ha_nn : 0 ≤ (n : ℝ) - 2 * m + 1 := by linarith
    have hb_nn : 0 ≤ (n : ℝ) - 2 * m := by linarith
    have hmul : ((n : ℝ) - 2 * m + 1) * ((n : ℝ) - 2 * m) ≤ (0.982 * n + 203) * (0.982 * n + 202) := by
      nlinarith only [ha, hb, ha_nn, hb_nn]
    nlinarith only [hmul, hnR]
  constructor
  · rw [le_div_iff₀ hden_pos]
    have hmul : (914 : ℝ) / 10000 * n * (((n : ℝ) - 2 * m + 1) * ((n : ℝ) - 2 * m)) ≤
        (914 : ℝ) / 10000 * n * ((0.982 * (n : ℝ)) ^ 2 + 405 * (n : ℝ)) := by
      nlinarith only [hden_hi, hnR]
    have hcubic : (914 : ℝ) / 10000 * n * ((0.982 * (n : ℝ)) ^ 2 + 405 * (n : ℝ)) ≤
        (0.991 * 0.101 * 0.881 : ℝ) * (n : ℝ) ^ 3 - (n : ℝ) ^ 2 := by
      have hsq : (39 : ℝ) * (n : ℝ) ≤ (0.991 * 0.101 * 0.881 - 0.0914 * 0.982 ^ 2) * (n : ℝ) ^ 2 := by
        nlinarith only [hnR]
      nlinarith only [hsq, hnR]
    linarith only [hmul, hcubic, hnum_lo]
  · rw [div_le_iff₀ hden_pos]
    have hmul : (915 : ℝ) / 10000 * n * ((0.982 * (n : ℝ)) ^ 2) ≤
        (915 : ℝ) / 10000 * n * (((n : ℝ) - 2 * m + 1) * ((n : ℝ) - 2 * m)) := by
      nlinarith only [hden_lo, hnR]
    have hcubic : (0.991 * 0.101 * 0.881 : ℝ) * (n : ℝ) ^ 3 + 250 * (n : ℝ) ^ 2 ≤
        (915 : ℝ) / 10000 * n * ((0.982 * (n : ℝ)) ^ 2) := by
      have hsq : 250 * (n : ℝ) ≤ (0.0915 * 0.982 ^ 2 - 0.991 * 0.101 * 0.881) * (n : ℝ) ^ 2 := by
        nlinarith only [hnR]
      nlinarith only [hsq, hnR]
    linarith only [hmul, hcubic, hnum_hi]

lemma jC_bounds {n m : ℕ} (hn : 10 ^ 7 ≤ n)
    (hm1 : 9 * n / 1000 - 100 ≤ m) (hm2 : m ≤ 9 * n / 1000) :
    (828 : ℝ) / 1000000 * n ≤ jC n (11 * n / 100) m ∧
      jC n (11 * n / 100) m ≤ (831 : ℝ) / 1000000 * n := by
  set w := 11 * n / 100
  have hnR : (10000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hwR_lo : (11 : ℝ) / 100 * n - 1 ≤ w := by
    have hnat : (11 * n : ℝ) ≤ 100 * (w : ℝ) + 99 := by
      exact_mod_cast (by omega : 11 * n ≤ 100 * w + 99)
    linarith
  have hwR_hi : (w : ℝ) ≤ (11 : ℝ) / 100 * n := by
    have hnat : (100 * w : ℝ) ≤ 11 * (n : ℝ) := by exact_mod_cast (by omega : 100 * w ≤ 11 * n)
    linarith
  have hmR_lo : (9 : ℝ) / 1000 * n - 101 ≤ m := by
    have hnat : (9 * n : ℝ) ≤ 1000 * (m : ℝ) + 100999 := by
      exact_mod_cast (by omega : 9 * n ≤ 1000 * m + 100999)
    linarith
  have hmR_hi : (m : ℝ) ≤ (9 : ℝ) / 1000 * n := by
    have hnat : (1000 * m : ℝ) ≤ 9 * (n : ℝ) := by exact_mod_cast (by omega : 1000 * m ≤ 9 * n)
    linarith
  have hm_ne : m ≠ 0 := by omega
  have h2 : m ≤ w := by omega
  have h3 : m ≤ n - w := by omega
  have h4 : 2 * m ≤ n := by omega
  have hw_le : w ≤ n := by omega
  have hc1 : ((w - m + 1 : ℕ) : ℝ) = (w : ℝ) - m + 1 := by rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub h2]
  have hc2 : ((n - w - m + 1 : ℕ) : ℝ) = (n : ℝ) - w - m + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub h3, Nat.cast_sub hw_le]
  have hc3 : ((n - 2 * m + 2 : ℕ) : ℝ) = (n : ℝ) - 2 * m + 2 := by
    rw [Nat.cast_add, Nat.cast_ofNat, Nat.cast_sub h4, Nat.cast_mul, Nat.cast_ofNat]
  have hc4 : ((n - 2 * m + 1 : ℕ) : ℝ) = (n : ℝ) - 2 * m + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub h4, Nat.cast_mul, Nat.cast_ofNat]
  unfold jC
  rw [if_neg hm_ne, hc1, hc2, hc3, hc4]
  have hden_pos : 0 < ((n : ℝ) - 2 * m + 2) * ((n : ℝ) - 2 * m + 1) := by
    have ha : 0 < (n : ℝ) - 2 * m + 2 := by linarith
    have hb : 0 < (n : ℝ) - 2 * m + 1 := by linarith
    exact mul_pos ha hb
  have hnum_lo : (0.009 * 0.101 * 0.881 : ℝ) * (n : ℝ) ^ 3 - 10 * (n : ℝ) ^ 2 ≤
      (m : ℝ) * ((w : ℝ) - m + 1) * ((n : ℝ) - w - m + 1) := by
    have h1 : (0.009 : ℝ) * n - 101 ≤ m := by linarith
    have h2' : (0.101 : ℝ) * n ≤ (w : ℝ) - m + 1 := by linarith
    have h3' : (0.881 : ℝ) * n ≤ (n : ℝ) - w - m + 1 := by linarith
    have h1_nn : 0 ≤ (0.009 : ℝ) * n - 101 := by linarith
    have h2_nn : 0 ≤ (0.101 : ℝ) * n := by positivity
    have h12 : (0.009 * (n : ℝ) - 101) * (0.101 * (n : ℝ)) ≤ (m : ℝ) * ((w : ℝ) - m + 1) := by
      nlinarith only [h1, h2', h1_nn, h2_nn]
    have h12_nn : 0 ≤ (0.009 * (n : ℝ) - 101) * (0.101 * (n : ℝ)) := mul_nonneg h1_nn h2_nn
    have h123 : (0.009 * (n : ℝ) - 101) * (0.101 * (n : ℝ)) * (0.881 * (n : ℝ)) ≤
        (m : ℝ) * ((w : ℝ) - m + 1) * ((n : ℝ) - w - m + 1) := by
      nlinarith only [h12, h3', h12_nn, hnR]
    nlinarith only [h123, hnR]
  have hnum_hi : (m : ℝ) * ((w : ℝ) - m + 1) * ((n : ℝ) - w - m + 1) ≤
      (0.009 * 0.101 * 0.881 : ℝ) * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 := by
    have h1 : (m : ℝ) ≤ 0.009 * n := by linarith
    have h2' : (w : ℝ) - m + 1 ≤ 0.101 * n + 102 := by linarith
    have h3' : (n : ℝ) - w - m + 1 ≤ 0.881 * n + 103 := by linarith
    have h1_nn : 0 ≤ (m : ℝ) := by positivity
    have h2_nn : 0 ≤ (w : ℝ) - m + 1 := by linarith
    have h3_nn : 0 ≤ (n : ℝ) - w - m + 1 := by linarith
    have h12 : (m : ℝ) * ((w : ℝ) - m + 1) ≤ (0.009 * (n : ℝ)) * (0.101 * (n : ℝ) + 102) := by
      nlinarith only [h1, h2', h1_nn, h2_nn]
    have h12_nn : 0 ≤ (m : ℝ) * ((w : ℝ) - m + 1) := mul_nonneg h1_nn h2_nn
    have h123 : (m : ℝ) * ((w : ℝ) - m + 1) * ((n : ℝ) - w - m + 1) ≤
        (0.009 * (n : ℝ)) * (0.101 * (n : ℝ) + 102) * (0.881 * (n : ℝ) + 103) := by
      nlinarith only [h12, h3', h12_nn, h3_nn, hnR]
    nlinarith only [h123, hnR]
  have hden_lo : (0.982 * (n : ℝ)) ^ 2 ≤ ((n : ℝ) - 2 * m + 2) * ((n : ℝ) - 2 * m + 1) := by
    have ha : (0.982 : ℝ) * n ≤ (n : ℝ) - 2 * m + 2 := by linarith
    have hb : (0.982 : ℝ) * n ≤ (n : ℝ) - 2 * m + 1 := by linarith
    nlinarith only [ha, hb, hnR]
  have hden_hi : ((n : ℝ) - 2 * m + 2) * ((n : ℝ) - 2 * m + 1) ≤ (0.982 * (n : ℝ)) ^ 2 + 410 * (n : ℝ) := by
    have ha : (n : ℝ) - 2 * m + 2 ≤ 0.982 * n + 204 := by linarith
    have hb : (n : ℝ) - 2 * m + 1 ≤ 0.982 * n + 203 := by linarith
    have ha_nn : 0 ≤ (n : ℝ) - 2 * m + 2 := by linarith
    have hb_nn : 0 ≤ (n : ℝ) - 2 * m + 1 := by linarith
    have hmul : ((n : ℝ) - 2 * m + 2) * ((n : ℝ) - 2 * m + 1) ≤ (0.982 * n + 204) * (0.982 * n + 203) := by
      nlinarith only [ha, hb, ha_nn, hb_nn]
    nlinarith only [hmul, hnR]
  constructor
  · rw [le_div_iff₀ hden_pos]
    have hmul : (828 : ℝ) / 1000000 * n * (((n : ℝ) - 2 * m + 2) * ((n : ℝ) - 2 * m + 1)) ≤
        (828 : ℝ) / 1000000 * n * ((0.982 * (n : ℝ)) ^ 2 + 410 * (n : ℝ)) := by
      nlinarith only [hden_hi, hnR]
    have hcubic : (828 : ℝ) / 1000000 * n * ((0.982 * (n : ℝ)) ^ 2 + 410 * (n : ℝ)) ≤
        (0.009 * 0.101 * 0.881 : ℝ) * (n : ℝ) ^ 3 - 10 * (n : ℝ) ^ 2 := by
      have hsq : 11 * (n : ℝ) ≤ (0.009 * 0.101 * 0.881 - 0.000828 * 0.982 ^ 2) * (n : ℝ) ^ 2 := by
        nlinarith only [hnR]
      nlinarith only [hsq, hnR]
    linarith only [hmul, hcubic, hnum_lo]
  · rw [div_le_iff₀ hden_pos]
    have hmul : (831 : ℝ) / 1000000 * n * ((0.982 * (n : ℝ)) ^ 2) ≤
        (831 : ℝ) / 1000000 * n * (((n : ℝ) - 2 * m + 2) * ((n : ℝ) - 2 * m + 1)) := by
      nlinarith only [hden_lo, hnR]
    have hcubic : (0.009 * 0.101 * 0.881 : ℝ) * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 ≤
        (831 : ℝ) / 1000000 * n * ((0.982 * (n : ℝ)) ^ 2) := by
      have hsq : 2 * (n : ℝ) ≤ (0.000831 * 0.982 ^ 2 - 0.009 * 0.101 * 0.881) * (n : ℝ) ^ 2 := by
        nlinarith only [hnR]
      nlinarith only [hsq, hnR]
    linarith only [hmul, hcubic, hnum_hi]

lemma clzLam_lower {n m : ℕ} (hn : 10 ^ 7 ≤ n)
    (hm1 : 9 * n / 1000 - 100 ≤ m) (hm2 : m ≤ 9 * n / 1000) :
    ((1 : ℝ) / 10000) * n * testVec n m ≤ clzLam n m := by
  set t := 9 * n / 1000
  set w := 11 * n / 100
  set j := m - (t - 100)
  have ht_ge : 101 ≤ t := by omega
  have htw : t + 1 ≤ w := by omega
  have hj_le : j ≤ 100 := by omega
  have hm_eq : m = t - 100 + j := by omega
  have hm_add1 : m + 1 ≤ w := by omega
  have hm_ge1 : 1 ≤ m := by omega
  dsimp only [clzLam]
  rw [if_pos hm_add1, if_pos hm_ge1]
  set θ := Real.pi / 102
  have hv_m : testVec n m = ((19 : ℝ) / 200) ^ j * Real.sin (((j + 1 : ℕ) : ℝ) * θ) := by
    dsimp only [testVec]
    rw [if_pos ⟨hm1, hm2⟩]
    have hj_def : m - (9 * n / 1000 - 100) = j := rfl
    rw [hj_def, show ((j + 1 : ℕ) : ℝ) * Real.pi / 102 = ((j + 1 : ℕ) : ℝ) * θ by dsimp [θ]; ring]
  have hv_p : testVec n (m + 1) =
      ((19 : ℝ) / 200) ^ j * ((19 : ℝ) / 200) * Real.sin (((j + 2 : ℕ) : ℝ) * θ) := by
    dsimp only [testVec]
    by_cases hmp : m + 1 ≤ t
    · rw [if_pos ⟨by omega, hmp⟩]
      have hsub : m + 1 - (9 * n / 1000 - 100) = j + 1 := by omega
      rw [hsub, pow_succ, show ((j + 1 + 1 : ℕ) : ℝ) * Real.pi / 102 = ((j + 2 : ℕ) : ℝ) * θ by
        dsimp [θ]; push_cast; ring]
    · have hj100 : j = 100 := by omega
      rw [if_neg (by omega), hj100]
      have hsin0 : Real.sin (((100 + 2 : ℕ) : ℝ) * θ) = 0 := by
        have hpi_eq : ((100 + 2 : ℕ) : ℝ) * θ = Real.pi := by dsimp [θ]; ring
        rw [hpi_eq, Real.sin_pi]
      rw [hsin0, mul_zero]
  have hv_m1 : testVec n (m - 1) =
      ((19 : ℝ) / 200) ^ j * ((200 : ℝ) / 19) * Real.sin ((j : ℝ) * θ) := by
    dsimp only [testVec]
    by_cases hmm : t - 100 ≤ m - 1
    · rw [if_pos ⟨hmm, by omega⟩]
      have hsub : m - 1 - (9 * n / 1000 - 100) + 1 = j := by omega
      have hpow : ((19 : ℝ) / 200) ^ (m - 1 - (9 * n / 1000 - 100)) =
          ((19 : ℝ) / 200) ^ j * ((200 : ℝ) / 19) := by
        have hsub0 : m - 1 - (9 * n / 1000 - 100) = j - 1 := by omega
        rw [hsub0]
        obtain ⟨j', hj'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
        rw [hj', Nat.succ_sub_one, pow_succ]
        ring
      rw [hpow, hsub, show (j : ℝ) * Real.pi / 102 = (j : ℝ) * θ by dsimp [θ]; ring]
    · have hj0 : j = 0 := by omega
      rw [if_neg (by omega), hj0]
      simp
  rw [hv_m, hv_p, hv_m1]
  have hsin_sum : Real.sin ((j : ℝ) * θ) + Real.sin (((j + 2 : ℕ) : ℝ) * θ) =
      2 * Real.cos θ * Real.sin (((j + 1 : ℕ) : ℝ) * θ) := by
    have ha : (j : ℝ) * θ = ((j + 1 : ℕ) : ℝ) * θ - θ := by push_cast; ring
    have hb : ((j + 2 : ℕ) : ℝ) * θ = ((j + 1 : ℕ) : ℝ) * θ + θ := by push_cast; ring
    rw [ha, hb, Real.sin_sub, Real.sin_add]
    ring
  have hsin_m_nn : 0 ≤ Real.sin ((j : ℝ) * θ) := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) ?_
    have hjR : (j : ℝ) ≤ 102 := by exact_mod_cast (by omega : j ≤ 102)
    rw [show (j : ℝ) * θ = (j : ℝ) / 102 * Real.pi by dsimp [θ]; ring]
    nlinarith [Real.pi_pos]
  have hsin_p_nn : 0 ≤ Real.sin (((j + 2 : ℕ) : ℝ) * θ) := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) ?_
    have hjR : ((j + 2 : ℕ) : ℝ) ≤ 102 := by exact_mod_cast (by omega : j + 2 ≤ 102)
    rw [show ((j + 2 : ℕ) : ℝ) * θ = ((j + 2 : ℕ) : ℝ) / 102 * Real.pi by dsimp [θ]; ring]
    nlinarith [Real.pi_pos]
  have hsin_c_pos : 0 < Real.sin (((j + 1 : ℕ) : ℝ) * θ) := by
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · have h1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j + 1)
      have hpi := Real.pi_pos
      positivity
    · have hjR : ((j + 1 : ℕ) : ℝ) ≤ 101 := by exact_mod_cast (by omega : j + 1 ≤ 101)
      rw [show ((j + 1 : ℕ) : ℝ) * θ = ((j + 1 : ℕ) : ℝ) / 102 * Real.pi by dsimp [θ]; ring]
      nlinarith [Real.pi_pos]
  have hcos_lb : (1 - (3.1416 : ℝ) ^ 2 / (2 * 102 ^ 2)) ≤ Real.cos θ := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := θ)
    have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
    have hth_nn : 0 ≤ θ := by positivity
    have hth_ub : θ ≤ 3.1416 / 102 := by simp only [θ]; linarith
    have hsq : θ ^ 2 ≤ (3.1416 / 102) ^ 2 := by nlinarith
    linarith
  obtain ⟨hjA_lo, hjA_hi⟩ := jA_bounds hn hm1 hm2
  obtain ⟨hjC_lo, hjC_hi⟩ := jC_bounds hn hm1 hm2
  have hn_nn : (0 : ℝ) ≤ n := by positivity
  have hpow_nn : (0 : ℝ) ≤ ((19 : ℝ) / 200) ^ j := by positivity
  have hcA : ((19 : ℝ) / 200) * ((914 : ℝ) / 10000 * n) ≥ (8683 : ℝ) / 1000000 * n := by linarith
  have hcC : ((200 : ℝ) / 19) * ((828 : ℝ) / 1000000 * n) ≥ (8683 : ℝ) / 1000000 * n := by linarith
  have hterm1 : (8683 : ℝ) / 1000000 * n * Real.sin (((j + 2 : ℕ) : ℝ) * θ) ≤
      jA n w m * ((19 : ℝ) / 200) * Real.sin (((j + 2 : ℕ) : ℝ) * θ) := by
    refine mul_le_mul_of_nonneg_right (by linarith) hsin_p_nn
  have hterm2 : (8683 : ℝ) / 1000000 * n * Real.sin ((j : ℝ) * θ) ≤
      jC n w m * ((200 : ℝ) / 19) * Real.sin ((j : ℝ) * θ) := by
    refine mul_le_mul_of_nonneg_right (by linarith) hsin_m_nn
  have hcomb : (8683 : ℝ) / 1000000 * n *
        (2 * Real.cos θ * Real.sin (((j + 1 : ℕ) : ℝ) * θ)) ≤
      jA n w m * ((19 : ℝ) / 200) * Real.sin (((j + 2 : ℕ) : ℝ) * θ) +
        jC n w m * ((200 : ℝ) / 19) * Real.sin ((j : ℝ) * θ) := by
    rw [← hsin_sum]
    linarith
  have hcos_mul : (8683 : ℝ) / 1000000 * n * (2 * (1 - (3.1416 : ℝ) ^ 2 / (2 * 102 ^ 2))) *
        Real.sin (((j + 1 : ℕ) : ℝ) * θ) ≤
      (8683 : ℝ) / 1000000 * n * (2 * Real.cos θ * Real.sin (((j + 1 : ℕ) : ℝ) * θ)) := by
    have hnn : 0 ≤ (8683 : ℝ) / 1000000 * n * Real.sin (((j + 1 : ℕ) : ℝ) * θ) :=
      mul_nonneg (by positivity) (le_of_lt hsin_c_pos)
    nlinarith
  have hmid : ((751 : ℝ) / 10000 * n - (915 : ℝ) / 10000 * n - (831 : ℝ) / 1000000 * n) *
        Real.sin (((j + 1 : ℕ) : ℝ) * θ) ≤
      ((751 : ℝ) / 10000 * n - jA n w m - jC n w m) * Real.sin (((j + 1 : ℕ) : ℝ) * θ) := by
    refine mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hsin_c_pos)
  have hnum_margin : (1 : ℝ) / 10000 * n * Real.sin (((j + 1 : ℕ) : ℝ) * θ) ≤
      ((751 : ℝ) / 10000 * n - (915 : ℝ) / 10000 * n - (831 : ℝ) / 1000000 * n +
        (8683 : ℝ) / 1000000 * n * (2 * (1 - (3.1416 : ℝ) ^ 2 / (2 * 102 ^ 2)))) *
          Real.sin (((j + 1 : ℕ) : ℝ) * θ) := by
    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hsin_c_pos)
    nlinarith
  have hfactor : jA n w m * (((19 : ℝ) / 200) ^ j * ((19 : ℝ) / 200) * Real.sin (((j + 2 : ℕ) : ℝ) * θ)) +
        ((751 : ℝ) / 10000 * n - jA n w m - jC n w m) *
          (((19 : ℝ) / 200) ^ j * Real.sin (((j + 1 : ℕ) : ℝ) * θ)) +
        jC n w m * (((19 : ℝ) / 200) ^ j * ((200 : ℝ) / 19) * Real.sin ((j : ℝ) * θ)) =
      ((19 : ℝ) / 200) ^ j *
        (jA n w m * ((19 : ℝ) / 200) * Real.sin (((j + 2 : ℕ) : ℝ) * θ) +
          ((751 : ℝ) / 10000 * n - jA n w m - jC n w m) * Real.sin (((j + 1 : ℕ) : ℝ) * θ) +
          jC n w m * ((200 : ℝ) / 19) * Real.sin ((j : ℝ) * θ)) := by
    ring
  rw [hfactor]
  have hrhs_mul : ((19 : ℝ) / 200) ^ j * ((1 : ℝ) / 10000 * n * Real.sin (((j + 1 : ℕ) : ℝ) * θ)) ≤
      ((19 : ℝ) / 200) ^ j *
        (jA n w m * ((19 : ℝ) / 200) * Real.sin (((j + 2 : ℕ) : ℝ) * θ) +
          ((751 : ℝ) / 10000 * n - jA n w m - jC n w m) * Real.sin (((j + 1 : ℕ) : ℝ) * θ) +
          jC n w m * ((200 : ℝ) / 19) * Real.sin ((j : ℝ) * θ)) := by
    refine mul_le_mul_of_nonneg_left ?_ hpow_nn
    linarith
  linarith

lemma clzLam_nonneg {n m : ℕ} (hn : 10 ^ 7 ≤ n) : 0 ≤ clzLam n m := by
  by_cases hm : 9 * n / 1000 - 100 ≤ m ∧ m ≤ 9 * n / 1000
  · exact le_trans (mul_nonneg (by positivity) (testVec_nonneg n m)) (clzLam_lower hn hm.1 hm.2)
  · dsimp only [clzLam]
    have hm_out : m < 9 * n / 1000 - 100 ∨ 9 * n / 1000 < m := by
      rcases not_and_or.mp hm with h | h
      · exact Or.inl (Nat.lt_of_not_ge h)
      · exact Or.inr (Nat.lt_of_not_ge h)
    rw [testVec_eq_zero hm_out, mul_zero, add_zero]
    refine add_nonneg ?_ ?_
    · split_ifs
      · exact mul_nonneg (jA_nonneg _ _ _) (testVec_nonneg _ _)
      · exact le_refl 0
    · split_ifs
      · exact mul_nonneg (jC_nonneg _ _ _) (testVec_nonneg _ _)
      · exact le_refl 0

lemma clz_R_expansion {n : ℕ} (hn : 10 ^ 7 ≤ n) :
    (fun A B : WSub n (11 * n / 100) =>
      ((751 : ℝ) / 10000 * n - (jDist A B : ℝ)) *
        (∑ k ∈ Finset.range (11 * n / 100 + 1),
          testVec n k • projMat n (11 * n / 100) k) A B) =
    ∑ m ∈ Finset.range (11 * n / 100 + 1),
      clzLam n m • projMat n (11 * n / 100) m := by
  set w := 11 * n / 100
  set t := 9 * n / 1000
  set jp : ℝ := (751 : ℝ) / 10000 * n
  have ht_ge : 101 ≤ t := by omega
  have htw : t + 1 ≤ w := by omega
  have hwn : 2 * w ≤ n := by omega
  have hQ_supp : ∑ k ∈ Finset.range (w + 1), testVec n k • projMat n w k =
      ∑ k ∈ Finset.Icc (t - 100) t, testVec n k • projMat n w k := by
    symm
    refine Finset.sum_subset (fun k hk => Finset.mem_range.mpr (by rw [Finset.mem_Icc] at hk; omega)) ?_
    intro k hk hnk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hnk
    rw [testVec_eq_zero hnk, zero_smul]
  have hJ_sum : (fun A B : WSub n w => (jDist A B : ℝ) *
        (∑ k ∈ Finset.Icc (t - 100) t, testVec n k • projMat n w k) A B) =
      ∑ k ∈ Finset.Icc (t - 100) t,
        testVec n k • ((-jA n w (k - 1)) • projMat n w (k - 1) +
          (jA n w k + jC n w k) • projMat n w k -
          jC n w (k + 1) • projMat n w (k + 1)) := by
    ext A B
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    have hform := congr_fun (congr_fun
      (jDist_mul_projMat_formula (n := n) (w := w) (k := k) (by omega) (by omega) hwn) A) B
    rw [mul_left_comm, hform]
  have hJ_split :
      (∑ k ∈ Finset.Icc (t - 100) t,
        testVec n k • ((-jA n w (k - 1)) • projMat n w (k - 1) +
          (jA n w k + jC n w k) • projMat n w k -
          jC n w (k + 1) • projMat n w (k + 1))) =
      -(∑ m ∈ Finset.range (w + 1),
          (if m + 1 ≤ w then jA n w m * testVec n (m + 1) else 0) • projMat n w m) +
        (∑ m ∈ Finset.range (w + 1),
          ((jA n w m + jC n w m) * testVec n m) • projMat n w m) -
        (∑ m ∈ Finset.range (w + 1),
          (if 1 ≤ m then jC n w m * testVec n (m - 1) else 0) • projMat n w m) := by
    have hsplit : ∀ k ∈ Finset.Icc (t - 100) t,
        testVec n k • ((-jA n w (k - 1)) • projMat n w (k - 1) +
          (jA n w k + jC n w k) • projMat n w k -
          jC n w (k + 1) • projMat n w (k + 1)) =
        -((jA n w (k - 1) * testVec n k) • projMat n w (k - 1)) +
          ((jA n w k + jC n w k) * testVec n k) • projMat n w k -
          (jC n w (k + 1) * testVec n k) • projMat n w (k + 1) := by
      intro k _
      ext A B
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have h1 : (∑ k ∈ Finset.Icc (t - 100) t,
          -((jA n w (k - 1) * testVec n k) • projMat n w (k - 1))) =
        -(∑ m ∈ Finset.range (w + 1),
          (if m + 1 ≤ w then jA n w m * testVec n (m + 1) else 0) • projMat n w m) := by
      rw [Finset.sum_neg_distrib]
      congr 1
      calc ∑ k ∈ Finset.Icc (t - 100) t, (jA n w (k - 1) * testVec n k) • projMat n w (k - 1)
          = ∑ m ∈ Finset.Icc (t - 101) (t - 1),
              (if m + 1 ≤ w then jA n w m * testVec n (m + 1) else 0) • projMat n w m := by
            refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
            · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
            · intro k1 hk1 k2 hk2 h; rw [Finset.mem_Icc] at hk1 hk2; omega
            · intro m hm; rw [Finset.mem_Icc] at hm; exact ⟨m + 1, Finset.mem_Icc.mpr (by omega), by omega⟩
            · intro k hk
              rw [Finset.mem_Icc] at hk
              rw [if_pos (by omega), show k - 1 + 1 = k by omega]
        _ = ∑ m ∈ Finset.range (w + 1),
              (if m + 1 ≤ w then jA n w m * testVec n (m + 1) else 0) • projMat n w m := by
            refine Finset.sum_subset (fun m hm => Finset.mem_range.mpr (by rw [Finset.mem_Icc] at hm; omega)) ?_
            intro m _ hnm
            rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hnm
            have h0 : testVec n (m + 1) = 0 := testVec_eq_zero (by omega)
            split_ifs <;> simp [h0]
    have h2 : (∑ k ∈ Finset.Icc (t - 100) t,
          ((jA n w k + jC n w k) * testVec n k) • projMat n w k) =
        ∑ m ∈ Finset.range (w + 1),
          ((jA n w m + jC n w m) * testVec n m) • projMat n w m := by
      refine Finset.sum_subset (fun m hm => Finset.mem_range.mpr (by rw [Finset.mem_Icc] at hm; omega)) ?_
      intro m _ hnm
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hnm
      rw [testVec_eq_zero hnm, mul_zero, zero_smul]
    have h3 : (∑ k ∈ Finset.Icc (t - 100) t,
          (jC n w (k + 1) * testVec n k) • projMat n w (k + 1)) =
        ∑ m ∈ Finset.range (w + 1),
          (if 1 ≤ m then jC n w m * testVec n (m - 1) else 0) • projMat n w m := by
      calc ∑ k ∈ Finset.Icc (t - 100) t, (jC n w (k + 1) * testVec n k) • projMat n w (k + 1)
          = ∑ m ∈ Finset.Icc (t - 99) (t + 1),
              (if 1 ≤ m then jC n w m * testVec n (m - 1) else 0) • projMat n w m := by
            refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
            · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
            · intro _ _ _ _ h; omega
            · intro m hm; rw [Finset.mem_Icc] at hm; exact ⟨m - 1, Finset.mem_Icc.mpr (by omega), by omega⟩
            · intro k hk
              rw [Finset.mem_Icc] at hk
              rw [if_pos (by omega), Nat.add_sub_cancel]
        _ = ∑ m ∈ Finset.range (w + 1),
              (if 1 ≤ m then jC n w m * testVec n (m - 1) else 0) • projMat n w m := by
            refine Finset.sum_subset (fun m hm => Finset.mem_range.mpr (by rw [Finset.mem_Icc] at hm; omega)) ?_
            intro m _ hnm
            rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hnm
            split_ifs with hm1
            · have h0 : testVec n (m - 1) = 0 := testVec_eq_zero (by omega)
              simp [h0]
            · simp
    rw [h1, h2, h3]
  ext A B
  have hQ_AB : (∑ k ∈ Finset.range (w + 1), testVec n k • projMat n w k) A B =
      (∑ k ∈ Finset.Icc (t - 100) t, testVec n k • projMat n w k) A B := by
    rw [hQ_supp]
  have hJ_AB := congr_fun (congr_fun hJ_sum A) B
  rw [hJ_split] at hJ_AB
  calc (jp - (jDist A B : ℝ)) * (∑ k ∈ Finset.range (w + 1), testVec n k • projMat n w k) A B
      = jp * (∑ k ∈ Finset.range (w + 1), testVec n k • projMat n w k) A B -
          (jDist A B : ℝ) * (∑ k ∈ Finset.Icc (t - 100) t, testVec n k • projMat n w k) A B := by
        rw [hQ_AB]; ring
    _ = (∑ m ∈ Finset.range (w + 1),
          ((if m + 1 ≤ w then jA n w m * testVec n (m + 1) else 0) +
            (jp - jA n w m - jC n w m) * testVec n m +
            (if 1 ≤ m then jC n w m * testVec n (m - 1) else 0)) * projMat n w m A B) := by
        rw [hJ_AB]
        simp only [Matrix.sum_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply,
          Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
          ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        ring
    _ = (∑ m ∈ Finset.range (w + 1), clzLam n m • projMat n w m) A B := by
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, w, jp, clzLam]

lemma psd_rowsum_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosSemidef) (hM_symm : M.transpose = M)
    (mu0 : ℝ) (hrow : ∀ A : ι, ∑ B : ι, M A B = mu0)
    (y : ι → ℝ) :
    mu0 * (∑ A : ι, y A) ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ A : ι, ∑ B : ι, y A * M A B * y B := by
  by_cases h0 : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp h0
    simp
  have hN_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
  set N : ℝ := (Fintype.card ι : ℝ)
  set S : ℝ := ∑ A : ι, y A
  set c : ℝ := S / N
  let z : ι → ℝ := fun A => y A - c
  have hz_psd : 0 ≤ dotProduct z (Matrix.mulVec M z) := by
    have hre := hM.re_dotProduct_nonneg z
    simpa only [star_trivial, RCLike.re_to_real] using hre
  have hquad : dotProduct z (Matrix.mulVec M z) =
      (∑ A : ι, ∑ B : ι, y A * M A B * y B) - mu0 * S ^ 2 / N := by
    simp only [dotProduct, Matrix.mulVec, z]
    have hexp : ∀ A : ι, (y A - c) * (∑ B : ι, M A B * (y B - c)) =
        (∑ B : ι, y A * M A B * y B) - c * (∑ B : ι, y A * M A B) -
          c * (∑ B : ι, M A B * y B) + c ^ 2 * (∑ B : ι, M A B) := by
      intro A
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun B _ => ?_
      ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h1 : ∑ A : ι, c * ∑ B : ι, y A * M A B = c * mu0 * S := by
      have hA : ∀ A : ι, ∑ B : ι, y A * M A B = y A * mu0 := by
        intro A; rw [← Finset.mul_sum, hrow A]
      simp_rw [hA]
      rw [← Finset.mul_sum, ← Finset.sum_mul]
      change c * (S * mu0) = c * mu0 * S
      ring
    have h2 : ∑ A : ι, c * ∑ B : ι, M A B * y B = c * mu0 * S := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      have hB : ∀ B : ι, ∑ A : ι, M A B * y B = mu0 * y B := by
        intro B
        have hcol : ∑ A : ι, M A B = mu0 := by
          have := hrow B
          rw [← hM_symm] at this
          simpa [Matrix.transpose_apply] using this
        rw [← Finset.sum_mul, hcol]
      simp_rw [hB, ← Finset.mul_sum]
      ring
    have h3 : ∑ A : ι, c ^ 2 * ∑ B : ι, M A B = c ^ 2 * mu0 * N := by
      simp_rw [hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change (Fintype.card ι : ℝ) * (c ^ 2 * mu0) = c ^ 2 * mu0 * N
      ring
    rw [h1, h2, h3]
    have hNc : N * c = S := mul_div_cancel₀ S (ne_of_gt hN_pos)
    calc (∑ A : ι, ∑ B : ι, y A * M A B * y B) - c * mu0 * S - c * mu0 * S + c ^ 2 * mu0 * N
        = (∑ A : ι, ∑ B : ι, y A * M A B * y B) - mu0 * c * (2 * S - (N * c)) := by ring
      _ = (∑ A : ι, ∑ B : ι, y A * M A B * y B) - mu0 * (S / N) * S := by
          rw [hNc]; ring
      _ = (∑ A : ι, ∑ B : ι, y A * M A B * y B) - mu0 * S ^ 2 / N := by ring
  rw [hquad] at hz_psd
  have hdiv : mu0 * S ^ 2 / N ≤ ∑ A : ι, ∑ B : ι, y A * M A B * y B := sub_nonneg.mp hz_psd
  rwa [div_le_iff₀ hN_pos, mul_comm _ N] at hdiv

/-- Main CLZ01 Hadamard / Johnson-scheme quadratic bound on `S.card`. -/
lemma hadamard_sidon_bound {n : ℕ} (hn : 10 ^ 7 ≤ n)
    (S : Finset (𝔽₂ n)) (hS : Green31.IsBinarySidon (S : Set (𝔽₂ n))) :
    let w := 11 * n / 100
    let t := 9 * n / 1000
    let jp : ℝ := (751 : ℝ) / 10000 * n
    (S.card : ℝ) ^ 2 ≤
      (751 * 101 * (2 : ℝ) ^ n * (Nat.choose n t : ℝ) / (Nat.choose n w : ℝ)) * (S.card : ℝ) +
        (751 * 101 * (2 : ℝ) ^ n * ((Nat.floor jp : ℝ) + 1) * (2 : ℝ) ^ (2 * Nat.floor jp)) := by
  set w := 11 * n / 100
  set t := 9 * n / 1000
  set jp : ℝ := (751 : ℝ) / 10000 * n
  have ht_ge : 101 ≤ t := by omega
  have htw : t + 1 ≤ w := by omega
  have hwn : 2 * w ≤ n := by omega
  let Q : Matrix (WSub n w) (WSub n w) ℝ :=
    ∑ k ∈ Finset.range (w + 1), testVec n k • projMat n w k
  let R : Matrix (WSub n w) (WSub n w) ℝ :=
    ∑ m ∈ Finset.range (w + 1), clzLam n m • projMat n w m
  have hQ_psd : Q.PosSemidef :=
    posSemidef_sum_nonneg_smul (Finset.range (w + 1)) (testVec n) (fun k => projMat n w k)
      (fun k _ => testVec_nonneg n k) (fun k _ => opToMatrix_starProjection_posSemidef _)
  have hR_psd : R.PosSemidef :=
    posSemidef_sum_nonneg_smul (Finset.range (w + 1)) (clzLam n) (fun m => projMat n w m)
      (fun m _ => clzLam_nonneg hn) (fun m _ => opToMatrix_starProjection_posSemidef _)
  let M : Matrix (WSub n w) (WSub n w) ℝ := Matrix.hadamard R Q
  have hM_psd : M.PosSemidef := hR_psd.hadamard hQ_psd
  have hR_eq : R = (fun A B : WSub n w => (jp - (jDist A B : ℝ)) * Q A B) :=
    (clz_R_expansion hn).symm
  have hM_entry : ∀ A B : WSub n w, M A B = (jp - (jDist A B : ℝ)) * (Q A B) ^ 2 := by
    intro A B
    simp only [M, Matrix.hadamard_apply]
    rw [hR_eq]
    ring
  have hQ_symm : Q.transpose = Q := by
    ext A B
    simp only [Q, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hsym : projMat n w k B A = projMat n w k A B := opToMatrix_starProjection_symm (VSub n w k) B A
    rw [hsym]
  have hR_symm : R.transpose = R := by
    ext A B
    simp only [R, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hsym : projMat n w m B A = projMat n w m A B := opToMatrix_starProjection_symm (VSub n w m) B A
    rw [hsym]
  have hM_symm : M.transpose = M := by
    ext A B
    simp only [M, Matrix.transpose_apply, Matrix.hadamard_apply]
    have h1 := congr_fun (congr_fun hR_symm A) B
    have h2 := congr_fun (congr_fun hQ_symm A) B
    simp only [Matrix.transpose_apply] at h1 h2
    rw [h1, h2]
  let mu0 : ℝ := ∑ k ∈ Finset.range (w + 1), testVec n k * clzLam n k * eVal n w k 0
  have hrow : ∀ A : WSub n w, ∑ B : WSub n w, M A B = mu0 := by
    intro A
    have hmul : ∑ B : WSub n w, M A B = (R * Q) A A := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun B _ => ?_
      have h2 := congr_fun (congr_fun hQ_symm A) B
      simp only [Matrix.transpose_apply] at h2
      simp only [M, Matrix.hadamard_apply, h2]
    have hRQ : R * Q = ∑ k ∈ Finset.range (w + 1),
        (testVec n k * clzLam n k) • projMat n w k := by
      simp only [R, Q, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkw : k ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [Finset.sum_eq_single k]
      · rw [projMat_mul_self]
      · intro m hm hmk
        have hmw : m ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
        rw [projMat_mul_eq_zero hmk.symm hkw hmw, smul_zero]
      · intro h; exact False.elim (h hk)
    rw [hmul, hRQ]
    simp only [mu0, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [projMat_eq_eVal A A, jDist_eq_zero_iff.mpr rfl]
  have hcardW : (Fintype.card (WSub n w) : ℝ) = (Nat.choose n w : ℝ) := by
    rw [card_wsub n w]
  -- For each x : 𝔽₂ n, apply psd_rowsum_bound to indicator of sliceW S w x
  have hx_bound : ∀ x : 𝔽₂ n,
      mu0 * ((sliceW S w x).card : ℝ) ^ 2 ≤
        (Nat.choose n w : ℝ) * ∑ A ∈ sliceW S w x, ∑ B ∈ sliceW S w x, M A B := by
    intro x
    let y : WSub n w → ℝ := fun A => if A ∈ sliceW S w x then 1 else 0
    have hy_sum : ∑ A : WSub n w, y A = ((sliceW S w x).card : ℝ) := by
      simp [y]
    have hy_quad : ∑ A : WSub n w, ∑ B : WSub n w, y A * M A B * y B =
        ∑ A ∈ sliceW S w x, ∑ B ∈ sliceW S w x, M A B := by
      simp only [y, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_mem, Finset.univ_inter]
      have hinner : ∀ a : WSub n w,
          (∑ b ∈ sliceW S w x, if a ∈ sliceW S w x then M a b else 0) =
          if a ∈ sliceW S w x then ∑ b ∈ sliceW S w x, M a b else 0 := by
        intro a; split_ifs <;> simp
      simp_rw [hinner, Finset.sum_ite_mem, Finset.univ_inter]
    have hpsd := psd_rowsum_bound M hM_psd hM_symm mu0 hrow y
    rwa [hy_sum, hy_quad, hcardW] at hpsd
  have hsum_x : mu0 * ∑ x : 𝔽₂ n, ((sliceW S w x).card : ℝ) ^ 2 ≤
      (Nat.choose n w : ℝ) * ∑ x : 𝔽₂ n, ∑ A ∈ sliceW S w x, ∑ B ∈ sliceW S w x, M A B := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => hx_bound x
  -- Lower bound mu0 in terms of ∑_{k ∈ Icc (t-100) t} testVec^2 * eVal
  let E_sum : ℝ := ∑ k ∈ Finset.Icc (t - 100) t, (testVec n k) ^ 2 * eVal n w k 0
  have hE_sum_pos : 0 < E_sum := by
    refine Finset.sum_pos' (fun k hk => mul_nonneg (sq_nonneg _)
      (le_of_lt (eVal_zero_pos (by rw [Finset.mem_Icc] at hk; omega) hwn)))
      ⟨t, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩,
        mul_pos (sq_pos_of_pos (testVec_pos (by omega) le_rfl)) (eVal_zero_pos (by omega) hwn)⟩
  have hmu0_lb : ((1 : ℝ) / 10000) * n * E_sum ≤ mu0 := by
    have hmu0_sub : ∑ k ∈ Finset.Icc (t - 100) t, testVec n k * clzLam n k * eVal n w k 0 ≤ mu0 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
      · intro k hk _
        rw [Finset.mem_range] at hk
        exact mul_nonneg (mul_nonneg (testVec_nonneg _ _) (clzLam_nonneg hn))
          (le_of_lt (eVal_zero_pos (by omega) hwn))
    have hsum_le : ((1 : ℝ) / 10000) * n * E_sum ≤
        ∑ k ∈ Finset.Icc (t - 100) t, testVec n k * clzLam n k * eVal n w k 0 := by
      simp only [E_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      rw [Finset.mem_Icc] at hk
      have hlam := clzLam_lower hn hk.1 hk.2
      have htv := testVec_nonneg n k
      have hev := le_of_lt (eVal_zero_pos (by omega : k ≤ w) hwn)
      have h1 : testVec n k * (((1 : ℝ) / 10000) * n * testVec n k) * eVal n w k 0 ≤
          testVec n k * clzLam n k * eVal n w k 0 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlam htv) hev
      nlinarith
    exact le_trans hsum_le hmu0_sub
  -- Express Q A B via Q_val (jDist A B)
  let Q_val : ℕ → ℝ := fun j => ∑ k ∈ Finset.Icc (t - 100) t, testVec n k * eVal n w k j
  have hQ_eq : ∀ A B : WSub n w, Q A B = Q_val (jDist A B) := by
    intro A B
    simp only [Q, Q_val, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    have hsub : Finset.Icc (t - 100) t ⊆ Finset.range (w + 1) := by
      intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [projMat_eq_eVal A B]
    · intro k _ hnk
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hnk
      rw [testVec_eq_zero hnk, zero_mul]
  -- Bound Q_val 0 ^ 2
  have hchoose_mono : ∀ k, k ≤ t → Nat.choose n k ≤ Nat.choose n t := by
    intro k hkt
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hkt
    induction d generalizing k with
    | zero =>
      rw [Nat.add_zero] at hd
      subst hd
      exact le_rfl
    | succ d ih =>
      have hk_step : Nat.choose n k ≤ Nat.choose n (k + 1) := by
        have hm1 : 0 < k + 1 := Nat.succ_pos k
        have hrel : (k + 1) * Nat.choose n (k + 1) = (n - k) * Nat.choose n k := by
          have h1 := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ n by omega)
          have h2 := Nat.choose_mul_factorial_mul_factorial (show k ≤ n by omega)
          have hf1 : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := Nat.factorial_succ k
          have hf2 : Nat.factorial (n - k) = (n - k) * Nat.factorial (n - (k + 1)) := by
            rw [show n - k = (n - (k + 1)) + 1 by omega, Nat.factorial_succ,
              show n - (k + 1) + 1 = n - k by omega]
          have hpos : 0 < Nat.factorial k * Nat.factorial (n - (k + 1)) := by positivity
          apply Nat.eq_of_mul_eq_mul_right hpos
          calc (k + 1) * Nat.choose n (k + 1) * (Nat.factorial k * Nat.factorial (n - (k + 1)))
              = Nat.choose n (k + 1) * ((k + 1) * Nat.factorial k) * Nat.factorial (n - (k + 1)) := by ring
            _ = Nat.factorial n := by rw [← hf1]; exact h1
            _ = Nat.choose n k * Nat.factorial k * ((n - k) * Nat.factorial (n - (k + 1))) := by
                rw [← hf2]; exact h2.symm
            _ = (n - k) * Nat.choose n k * (Nat.factorial k * Nat.factorial (n - (k + 1))) := by ring
        have hcmp : k + 1 ≤ n - k := by omega
        have hstep : (k + 1) * Nat.choose n k ≤ (k + 1) * Nat.choose n (k + 1) := by
          rw [hrel]
          exact Nat.mul_le_mul_right _ hcmp
        exact Nat.le_of_mul_le_mul_left hstep hm1
      exact le_trans hk_step (ih (k + 1) (by omega) (by omega))
  have hcw_pos : (0 : ℝ) < (Nat.choose n w : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : w ≤ n)
  have hQ0_ub : Q_val 0 ^ 2 ≤ E_sum * (101 * (Nat.choose n t : ℝ) / (Nat.choose n w : ℝ)) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc (t - 100) t)
      (fun k => testVec n k * Real.sqrt (eVal n w k 0))
      (fun k => Real.sqrt (eVal n w k 0))
    have hL : (∑ k ∈ Finset.Icc (t - 100) t,
          (testVec n k * Real.sqrt (eVal n w k 0)) * Real.sqrt (eVal n w k 0)) = Q_val 0 := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_Icc] at hk
      have hev := le_of_lt (eVal_zero_pos (by omega : k ≤ w) hwn)
      rw [mul_assoc, Real.mul_self_sqrt hev]
    have hR1 : (∑ k ∈ Finset.Icc (t - 100) t, (testVec n k * Real.sqrt (eVal n w k 0)) ^ 2) = E_sum := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_Icc] at hk
      have hev := le_of_lt (eVal_zero_pos (by omega : k ≤ w) hwn)
      rw [mul_pow, Real.sq_sqrt hev]
    have hR2 : (∑ k ∈ Finset.Icc (t - 100) t, (Real.sqrt (eVal n w k 0)) ^ 2) ≤
        101 * (Nat.choose n t : ℝ) / (Nat.choose n w : ℝ) := by
      have hterm : ∀ k ∈ Finset.Icc (t - 100) t,
          (Real.sqrt (eVal n w k 0)) ^ 2 ≤ (Nat.choose n t : ℝ) / (Nat.choose n w : ℝ) := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        have hev := le_of_lt (eVal_zero_pos (by omega : k ≤ w) hwn)
        rw [Real.sq_sqrt hev, eVal_zero (by omega : k ≤ w) hwn]
        refine div_le_div_of_nonneg_right ?_ (le_of_lt hcw_pos)
        have hnat : Nat.choose n k - (if k = 0 then 0 else Nat.choose n (k - 1)) ≤ Nat.choose n t :=
          le_trans (Nat.sub_le _ _) (hchoose_mono k hk.2)
        exact_mod_cast hnat
      have hsum := Finset.sum_le_sum hterm
      rw [Finset.sum_const, Nat.card_Icc, show t + 1 - (t - 100) = 101 by omega, nsmul_eq_mul] at hsum
      push_cast at hsum
      rw [← mul_div_assoc] at hsum
      exact hsum
    rw [hL, hR1] at hcs
    exact le_trans hcs (mul_le_mul_of_nonneg_left hR2 (le_of_lt hE_sum_pos))
  -- Bound Q_val j ^ 2 for 1 ≤ j ≤ floor jp
  have hQj_ub : ∀ j : ℕ, 1 ≤ j → j ≤ Nat.floor jp →
      ((Nat.choose w j * Nat.choose (n - w) j : ℕ) : ℝ) * Q_val j ^ 2 ≤ 101 * E_sum := by
    intro j hj1 hjf
    have hjR : (j : ℝ) ≤ jp := by
      have := Nat.floor_le (by positivity : 0 ≤ jp)
      exact le_trans (by exact_mod_cast hjf) this
    have hj_lt : j < w := by
      have hjR' : (j : ℝ) ≤ (751 : ℝ) / 10000 * n := hjR
      have hwR : (11 : ℝ) / 100 * n - 1 ≤ w := by
        have hnat : (11 * n : ℝ) ≤ 100 * (w : ℝ) + 99 := by
          exact_mod_cast (by omega : 11 * n ≤ 100 * w + 99)
        linarith
      have hnR : (10000000 : ℝ) ≤ n := by exact_mod_cast hn
      have hjwR : (j : ℝ) < w := by linarith
      exact_mod_cast hjwR
    have hjw : j ≤ w := le_of_lt hj_lt
    have hwj : w + j ≤ n := by omega
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc (t - 100) t)
      (fun k => testVec n k * eVal n w k j) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Nat.card_Icc,
      show t + 1 - (t - 100) = 101 by omega, nsmul_eq_mul] at hcs
    have hmul : ((Nat.choose w j * Nat.choose (n - w) j : ℕ) : ℝ) * Q_val j ^ 2 ≤
        ((Nat.choose w j * Nat.choose (n - w) j : ℕ) : ℝ) *
          ((∑ k ∈ Finset.Icc (t - 100) t, (testVec n k * eVal n w k j) ^ 2) * 101) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    have hswap : ((Nat.choose w j * Nat.choose (n - w) j : ℕ) : ℝ) *
          ((∑ k ∈ Finset.Icc (t - 100) t, (testVec n k * eVal n w k j) ^ 2) * 101) =
        101 * ∑ k ∈ Finset.Icc (t - 100) t,
          (testVec n k) ^ 2 * (((Nat.choose w j * Nat.choose (n - w) j : ℕ) : ℝ) * (eVal n w k j) ^ 2) := by
      rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hswap] at hmul
    refine le_trans hmul ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Finset.sum_le_sum fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    refine mul_le_mul_of_nonneg_left (vj_mul_eVal_sq_le (by omega : k ≤ w) hwn hjw hwj) (sq_nonneg _)
  -- Upper bound ∑_x ∑_{A,B ∈ sliceW S w x} M A B
  let J := Nat.floor jp
  have hRHS_x : ∀ x : 𝔽₂ n,
      ∑ A ∈ sliceW S w x, ∑ B ∈ sliceW S w x, M A B ≤
        ((sliceW S w x).card : ℝ) * jp * Q_val 0 ^ 2 +
          ∑ j ∈ Finset.Icc 1 J,
            (((sliceW S w x ×ˢ sliceW S w x).filter (fun p => jDist p.1 p.2 = j)).card : ℝ) *
              jp * Q_val j ^ 2 := by
    intro x
    rw [← Finset.sum_product' (f := fun A B => M A B)]
    have hsplit : ∀ p ∈ sliceW S w x ×ˢ sliceW S w x,
        M p.1 p.2 ≤
          (if jDist p.1 p.2 = 0 then jp * Q_val 0 ^ 2 else 0) +
          ∑ j ∈ Finset.Icc 1 J,
            (if jDist p.1 p.2 = j then jp * Q_val j ^ 2 else 0) := by
      intro p _
      rw [hM_entry p.1 p.2, hQ_eq p.1 p.2]
      set d := jDist p.1 p.2
      by_cases hd0 : d = 0
      · have hsum0 : ∑ j ∈ Finset.Icc 1 J, (if d = j then jp * Q_val j ^ 2 else 0) = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          rw [Finset.mem_Icc] at hj
          rw [if_neg (by omega)]
        rw [if_pos hd0, hsum0, add_zero, hd0]
        simp
      · by_cases hdJ : d ≤ J
        · have hmem : d ∈ Finset.Icc 1 J := Finset.mem_Icc.mpr ⟨by omega, hdJ⟩
          have hsumd : ∑ j ∈ Finset.Icc 1 J, (if d = j then jp * Q_val j ^ 2 else 0) =
              jp * Q_val d ^ 2 := by
            rw [Finset.sum_eq_single d]
            · rw [if_pos rfl]
            · intro j _ hjd; rw [if_neg hjd.symm]
            · intro h; exact False.elim (h hmem)
          rw [if_neg hd0, zero_add, hsumd]
          have hd_nn : (0 : ℝ) ≤ d := by positivity
          exact mul_le_mul_of_nonneg_right (sub_le_self jp hd_nn) (sq_nonneg _)
        · have hsum0 : ∑ j ∈ Finset.Icc 1 J, (if d = j then jp * Q_val j ^ 2 else 0) = 0 := by
            refine Finset.sum_eq_zero fun j hj => ?_
            rw [Finset.mem_Icc] at hj
            rw [if_neg (by omega)]
          rw [if_neg hd0, hsum0, add_zero]
          have hd_gt : jp < (d : ℝ) := by
            have h1 : jp < (J : ℝ) + 1 := Nat.lt_floor_add_one jp
            have h2 : (J : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast (by omega : J + 1 ≤ d)
            linarith
          exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_lt hd_gt)) (sq_nonneg _)
    calc ∑ p ∈ sliceW S w x ×ˢ sliceW S w x, M p.1 p.2
        ≤ ∑ p ∈ sliceW S w x ×ˢ sliceW S w x,
            ((if jDist p.1 p.2 = 0 then jp * Q_val 0 ^ 2 else 0) +
              ∑ j ∈ Finset.Icc 1 J, (if jDist p.1 p.2 = j then jp * Q_val j ^ 2 else 0)) :=
          Finset.sum_le_sum hsplit
      _ = (∑ p ∈ sliceW S w x ×ˢ sliceW S w x, if jDist p.1 p.2 = 0 then jp * Q_val 0 ^ 2 else 0) +
            ∑ j ∈ Finset.Icc 1 J,
              ∑ p ∈ sliceW S w x ×ˢ sliceW S w x, if jDist p.1 p.2 = j then jp * Q_val j ^ 2 else 0 := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
      _ = ((sliceW S w x).card : ℝ) * jp * Q_val 0 ^ 2 +
            ∑ j ∈ Finset.Icc 1 J,
              (((sliceW S w x ×ˢ sliceW S w x).filter (fun p => jDist p.1 p.2 = j)).card : ℝ) *
                jp * Q_val j ^ 2 := by
          congr 1
          · have hfilt : (sliceW S w x ×ˢ sliceW S w x).filter (fun p => jDist p.1 p.2 = 0) =
                (sliceW S w x).image (fun A => (A, A)) := by
              ext ⟨A, B⟩
              simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, jDist_eq_zero_iff]
              constructor
              · rintro ⟨⟨hA, _⟩, rfl⟩; exact ⟨A, hA, rfl⟩
              · rintro ⟨C, hC, hEq⟩
                obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hEq
                exact ⟨⟨hC, hC⟩, rfl⟩
            have hinj : Function.Injective (fun A : WSub n w => (A, A)) :=
              fun _ _ h => (Prod.ext_iff.mp h).1
            have h0_eq : (∑ p ∈ sliceW S w x ×ˢ sliceW S w x,
                  if jDist p.1 p.2 = 0 then jp * Q_val 0 ^ 2 else 0) =
                ((sliceW S w x).card : ℝ) * jp * Q_val 0 ^ 2 := by
              rw [← Finset.sum_filter, hfilt, Finset.sum_const,
                Finset.card_image_of_injective _ hinj, nsmul_eq_mul]
              dsimp only [jp]; ring
            exact h0_eq
          · refine Finset.sum_congr rfl fun j _ => ?_
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
            dsimp only [jp]; ring
  -- Wait: check Finset.sum_ite_eq' usage above!
  have hRHS_sum : ∑ x : 𝔽₂ n, ∑ A ∈ sliceW S w x, ∑ B ∈ sliceW S w x, M A B ≤
      (S.card : ℝ) * (Nat.choose n w : ℝ) * jp * Q_val 0 ^ 2 +
        ∑ j ∈ Finset.Icc 1 J,
          ((Nat.choose n w * (Nat.choose w j * Nat.choose (n - w) j) * 2 ^ (2 * j) : ℕ) : ℝ) *
            jp * Q_val j ^ 2 := by
    calc ∑ x : 𝔽₂ n, ∑ A ∈ sliceW S w x, ∑ B ∈ sliceW S w x, M A B
        ≤ ∑ x : 𝔽₂ n, (((sliceW S w x).card : ℝ) * jp * Q_val 0 ^ 2 +
            ∑ j ∈ Finset.Icc 1 J,
              (((sliceW S w x ×ˢ sliceW S w x).filter (fun p => jDist p.1 p.2 = j)).card : ℝ) *
                jp * Q_val j ^ 2) :=
          Finset.sum_le_sum fun x _ => hRHS_x x
      _ = (∑ x : 𝔽₂ n, ((sliceW S w x).card : ℝ)) * jp * Q_val 0 ^ 2 +
            ∑ j ∈ Finset.Icc 1 J,
              (∑ x : 𝔽₂ n, (((sliceW S w x ×ˢ sliceW S w x).filter
                (fun p => jDist p.1 p.2 = j)).card : ℝ)) * jp * Q_val j ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
          congr 1
          · rw [Finset.sum_mul, Finset.sum_mul]
          · refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ (S.card : ℝ) * (Nat.choose n w : ℝ) * jp * Q_val 0 ^ 2 +
            ∑ j ∈ Finset.Icc 1 J,
              ((Nat.choose n w * (Nat.choose w j * Nat.choose (n - w) j) * 2 ^ (2 * j) : ℕ) : ℝ) *
                jp * Q_val j ^ 2 := by
          refine add_le_add ?_ (Finset.sum_le_sum fun j hj => ?_)
          · have hsw := sum_card_sliceW S w
            have hswR : (∑ x : 𝔽₂ n, ((sliceW S w x).card : ℝ)) =
                (S.card : ℝ) * (Nat.choose n w : ℝ) := by exact_mod_cast hsw
            rw [hswR]
          · rw [Finset.mem_Icc] at hj
            have hjR : (j : ℝ) ≤ jp := le_trans (by exact_mod_cast hj.2)
              (Nat.floor_le (by positivity : 0 ≤ jp))
            have hjw : j ≤ w := by
              have hjR' : (j : ℝ) ≤ (751 : ℝ) / 10000 * n := hjR
              have hwR : (11 : ℝ) / 100 * n - 1 ≤ w := by
                have hnat : (11 * n : ℝ) ≤ 100 * (w : ℝ) + 99 := by
                  exact_mod_cast (by omega : 11 * n ≤ 100 * w + 99)
                linarith
              have hnR : (10000000 : ℝ) ≤ n := by exact_mod_cast hn
              exact_mod_cast (by linarith : (j : ℝ) ≤ w)
            have hwj : w + j ≤ n := by omega
            have heq_f : ∀ x : 𝔽₂ n,
                ((sliceW S w x ×ˢ sliceW S w x).filter (fun p => jDist p.1 p.2 = j)).card =
                ((sliceW S w x ×ˢ sliceW S w x).filter (fun p => (symmDiff p.1.1 p.2.1).card = 2 * j)).card := by
              intro x
              congr 1
              ext p
              simp only [Finset.mem_filter, and_congr_right_iff]
              intro _
              rw [card_symmDiff_wsub p.1 p.2]
              omega
            simp_rw [heq_f]
            have hp_nat := pair_both_weight_sum S hS hj.1 hjw
            have hid_nat := choose_johnson_identity hjw hwj
            have hcomb_nat : ∑ x : 𝔽₂ n, ((sliceW S w x ×ˢ sliceW S w x).filter
                  (fun p => (symmDiff p.1.1 p.2.1).card = 2 * j)).card ≤
                Nat.choose n w * (Nat.choose w j * Nat.choose (n - w) j) * 2 ^ (2 * j) := by
              calc ∑ x : 𝔽₂ n, ((sliceW S w x ×ˢ sliceW S w x).filter
                      (fun p => (symmDiff p.1.1 p.2.1).card = 2 * j)).card
                  ≤ Nat.choose n (2 * j) * 2 ^ (2 * j) *
                      (Nat.choose (2 * j) j * Nat.choose (n - 2 * j) (w - j)) := hp_nat
                _ = Nat.choose n (2 * j) * (Nat.choose (2 * j) j * Nat.choose (n - 2 * j) (w - j)) *
                      2 ^ (2 * j) := by ring
                _ = Nat.choose n w * (Nat.choose w j * Nat.choose (n - w) j) * 2 ^ (2 * j) := by
                    rw [hid_nat]
            have hcombR : (∑ x : 𝔽₂ n, (((sliceW S w x ×ˢ sliceW S w x).filter
                  (fun p => (symmDiff p.1.1 p.2.1).card = 2 * j)).card : ℝ)) ≤
                ((Nat.choose n w * (Nat.choose w j * Nat.choose (n - w) j) * 2 ^ (2 * j) : ℕ) : ℝ) := by
              exact_mod_cast hcomb_nat
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcombR (by positivity))
              (sq_nonneg _)
  -- Bound the off-diagonal sum using hQj_ub and ∑_{j=1}^J 2^{2j} ≤ (J + 1) * 2^{2J}
  have hpow_sum : ∑ j ∈ Finset.Icc 1 J, (2 : ℝ) ^ (2 * j) ≤ ((J : ℝ) + 1) * (2 : ℝ) ^ (2 * J) := by
    have hterm : ∀ j ∈ Finset.Icc 1 J, (2 : ℝ) ^ (2 * j) ≤ (2 : ℝ) ^ (2 * J) := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    calc ∑ j ∈ Finset.Icc 1 J, (2 : ℝ) ^ (2 * j)
        ≤ ∑ _j ∈ Finset.Icc 1 J, (2 : ℝ) ^ (2 * J) := Finset.sum_le_sum hterm
      _ = ((Finset.Icc 1 J).card : ℝ) * (2 : ℝ) ^ (2 * J) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((J : ℝ) + 1) * (2 : ℝ) ^ (2 * J) := by
          rw [Nat.card_Icc]
          have hcard : (J + 1 - 1 : ℕ) ≤ J + 1 := by omega
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  have hRHS_all : (Nat.choose n w : ℝ) * ∑ x : 𝔽₂ n, ∑ A ∈ sliceW S w x, ∑ B ∈ sliceW S w x, M A B ≤
      (Nat.choose n w : ℝ) ^ 2 * E_sum * jp *
        ((101 * (Nat.choose n t : ℝ) / (Nat.choose n w : ℝ)) * (S.card : ℝ) +
          101 * ((J : ℝ) + 1) * (2 : ℝ) ^ (2 * J)) := by
    have h1 := mul_le_mul_of_nonneg_left hRHS_sum (le_of_lt hcw_pos)
    refine le_trans h1 ?_
    rw [mul_add, mul_add]
    refine add_le_add ?_ ?_
    · have hmul : (Nat.choose n w : ℝ) * ((S.card : ℝ) * (Nat.choose n w : ℝ) * jp * Q_val 0 ^ 2) ≤
          (Nat.choose n w : ℝ) * ((S.card : ℝ) * (Nat.choose n w : ℝ) * jp *
            (E_sum * (101 * (Nat.choose n t : ℝ) / (Nat.choose n w : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ0_ub (by positivity)) (le_of_lt hcw_pos)
      refine le_trans hmul ?_
      exact le_of_eq (by ring)
    · have hsum_j : ∑ j ∈ Finset.Icc 1 J,
            ((Nat.choose n w * (Nat.choose w j * Nat.choose (n - w) j) * 2 ^ (2 * j) : ℕ) : ℝ) *
              jp * Q_val j ^ 2 ≤
          (Nat.choose n w : ℝ) * E_sum * jp * 101 * ∑ j ∈ Finset.Icc 1 J, (2 : ℝ) ^ (2 * j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j hj => ?_
        rw [Finset.mem_Icc] at hj
        have hq := hQj_ub j hj.1 hj.2
        have heq : ((Nat.choose n w * (Nat.choose w j * Nat.choose (n - w) j) * 2 ^ (2 * j) : ℕ) : ℝ) *
              jp * Q_val j ^ 2 =
            (Nat.choose n w : ℝ) * jp * (2 : ℝ) ^ (2 * j) *
              (((Nat.choose w j * Nat.choose (n - w) j : ℕ) : ℝ) * Q_val j ^ 2) := by
          push_cast; ring
        rw [heq]
        have hmul := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ (Nat.choose n w : ℝ) * jp * (2 : ℝ) ^ (2 * j))
        refine le_trans hmul ?_
        exact le_of_eq (by ring)
      have h2 := mul_le_mul_of_nonneg_left hsum_j (le_of_lt hcw_pos)
      refine le_trans h2 ?_
      have hjp_nn : 0 ≤ jp := by dsimp only [jp]; positivity
      have h3 := mul_le_mul_of_nonneg_left
        (a := (Nat.choose n w : ℝ) * ((Nat.choose n w : ℝ) * E_sum * jp * 101)) hpow_sum
        (mul_nonneg (le_of_lt hcw_pos)
          (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hcw_pos) (le_of_lt hE_sum_pos))
            hjp_nn) (by norm_num)))
      rw [← mul_assoc]
      refine le_trans h3 ?_
      exact le_of_eq (by ring)
  -- Combine with LHS lower bound from sum_sq_card_sliceW_ge
  have hLHS_ge : ((1 : ℝ) / 10000) * n * E_sum *
        ((S.card : ℝ) ^ 2 * (Nat.choose n w : ℝ) ^ 2 / (2 : ℝ) ^ n) ≤
      (Nat.choose n w : ℝ) ^ 2 * E_sum * jp *
        ((101 * (Nat.choose n t : ℝ) / (Nat.choose n w : ℝ)) * (S.card : ℝ) +
          101 * ((J : ℝ) + 1) * (2 : ℝ) ^ (2 * J)) := by
    have hsq := sum_sq_card_sliceW_ge S w
    have hsqR : (S.card : ℝ) ^ 2 * (Nat.choose n w : ℝ) ^ 2 / (2 : ℝ) ^ n ≤
        ∑ x : 𝔽₂ n, ((sliceW S w x).card : ℝ) ^ 2 := by
      have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
      have hsq_cast : ((S.card * Nat.choose n w : ℕ) : ℝ) ^ 2 ≤
          ((2 ^ n * ∑ x : 𝔽₂ n, (sliceW S w x).card ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast hsq
      have hsq_alg : (S.card : ℝ) ^ 2 * (Nat.choose n w : ℝ) ^ 2 ≤
          (∑ x : 𝔽₂ n, ((sliceW S w x).card : ℝ) ^ 2) * (2 : ℝ) ^ n := by
        push_cast at hsq_cast
        linarith
      rwa [div_le_iff₀ h2n]
    have hmu0_nn : 0 ≤ mu0 := le_trans (mul_nonneg (by positivity) (le_of_lt hE_sum_pos)) hmu0_lb
    have hL1 := mul_le_mul_of_nonneg_left hsqR hmu0_nn
    have hL2 := mul_le_mul_of_nonneg_right hmu0_lb (by positivity :
      0 ≤ (S.card : ℝ) ^ 2 * (Nat.choose n w : ℝ) ^ 2 / (2 : ℝ) ^ n)
    exact le_trans hL2 (le_trans hL1 (le_trans hsum_x hRHS_all))
  have hpos_cancel : 0 < ((1 : ℝ) / 10000) * n * E_sum * (Nat.choose n w : ℝ) ^ 2 / (2 : ℝ) ^ n := by
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hn_pos) hE_sum_pos) (sq_pos_of_pos hcw_pos))
      (by positivity)
  have hdiv := div_le_div_of_nonneg_right hLHS_ge (le_of_lt hpos_cancel)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hcw0 : (Nat.choose n w : ℝ) ≠ 0 := ne_of_gt hcw_pos
  have hE0 : E_sum ≠ 0 := ne_of_gt hE_sum_pos
  have h2n0 : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hcancel_R : ∀ (nR cw E p2 s ct Jp1 : ℝ),
      nR ≠ 0 → cw ≠ 0 → E ≠ 0 → p2 ≠ 0 →
      (cw ^ 2 * E * (751 / 10000 * nR) * ((101 * ct / cw) * s + 101 * Jp1)) /
        (1 / 10000 * nR * E * cw ^ 2 / p2) =
      (751 * 101 * p2 * ct / cw) * s + (751 * 101 * p2 * Jp1) := by
    intro nR cw E p2 s ct Jp1 hn' hcw' hE' hp2'
    field_simp [hn', hcw', hE', hp2']
  have hpos_ne : ((1 : ℝ) / 10000 * n * E_sum * (Nat.choose n w : ℝ) ^ 2 / (2 : ℝ) ^ n) ≠ 0 :=
    ne_of_gt hpos_cancel
  have hL_eq : ((1 : ℝ) / 10000 * n * E_sum * ((S.card : ℝ) ^ 2 * (Nat.choose n w : ℝ) ^ 2 / (2 : ℝ) ^ n)) /
      ((1 : ℝ) / 10000 * n * E_sum * (Nat.choose n w : ℝ) ^ 2 / (2 : ℝ) ^ n) = (S.card : ℝ) ^ 2 := by
    rw [show ((1 : ℝ) / 10000 * n * E_sum * ((S.card : ℝ) ^ 2 * (Nat.choose n w : ℝ) ^ 2 / (2 : ℝ) ^ n)) =
      (S.card : ℝ) ^ 2 * ((1 : ℝ) / 10000 * n * E_sum * (Nat.choose n w : ℝ) ^ 2 / (2 : ℝ) ^ n) by ring]
    exact mul_div_cancel_right₀ _ hpos_ne
  have hR_eq : ((Nat.choose n w : ℝ) ^ 2 * E_sum * jp *
        ((101 * (Nat.choose n t : ℝ) / (Nat.choose n w : ℝ)) * (S.card : ℝ) +
          101 * ((J : ℝ) + 1) * (2 : ℝ) ^ (2 * J))) /
      ((1 : ℝ) / 10000 * n * E_sum * (Nat.choose n w : ℝ) ^ 2 / (2 : ℝ) ^ n) =
      (751 * 101 * (2 : ℝ) ^ n * (Nat.choose n t : ℝ) / (Nat.choose n w : ℝ)) * (S.card : ℝ) +
        (751 * 101 * (2 : ℝ) ^ n * ((J : ℝ) + 1) * (2 : ℝ) ^ (2 * J)) := by
    have hjp_def : jp = (751 : ℝ) / 10000 * n := rfl
    rw [hjp_def]
    have hcr := hcancel_R (n : ℝ) (Nat.choose n w : ℝ) E_sum ((2 : ℝ) ^ n) (S.card : ℝ)
      (Nat.choose n t : ℝ) (((J : ℝ) + 1) * (2 : ℝ) ^ (2 * J)) hn0 hcw0 hE0 h2n0
    rw [show (101 * ((J : ℝ) + 1) * (2 : ℝ) ^ (2 * J)) = 101 * (((J : ℝ) + 1) * (2 : ℝ) ^ (2 * J)) by ring,
      show (751 * 101 * (2 : ℝ) ^ n * ((J : ℝ) + 1) * (2 : ℝ) ^ (2 * J)) =
        751 * 101 * (2 : ℝ) ^ n * (((J : ℝ) + 1) * (2 : ℝ) ^ (2 * J)) by ring]
    exact hcr
  rw [hL_eq, hR_eq] at hdiv
  exact hdiv

end HadamardBound

section EntropyBound

lemma quadratic_bound {x a b : ℝ} (_hx : 0 ≤ x) (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : x ^ 2 ≤ a * x + b) : x ≤ a + Real.sqrt b := by
  by_contra hlt
  rw [not_le] at hlt
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have hsr := Real.sqrt_nonneg b
  nlinarith

lemma poly_le_exp_0001 {n : ℕ} (hn : 10 ^ 7 ≤ n) :
    2 * 751 * 101 * ((n : ℝ) + 1) * (89 / 11) ≤ Real.exp (0.0001 * (n : ℝ)) := by
  have hnR : (10000000 : ℝ) ≤ n := by exact_mod_cast hn
  set y : ℝ := 0.0001 * (n : ℝ)
  have hy_ge : 1000 ≤ y := by dsimp [y]; linarith
  have h1 : 1 + y / 6 ≤ Real.exp (y / 6) := by linarith [Real.add_one_le_exp (y / 6)]
  have hy6_nn : 0 ≤ y / 6 := by linarith
  have hpow1 : (y / 6) ^ 6 ≤ (1 + y / 6) ^ 6 := pow_le_pow_left₀ hy6_nn (by linarith) 6
  have hpow2 : (1 + y / 6) ^ 6 ≤ Real.exp (y / 6) ^ 6 := pow_le_pow_left₀ (by linarith) h1 6
  have hexp : Real.exp (y / 6) ^ 6 = Real.exp y := by
    rw [← Real.exp_nat_mul]
    congr 1; push_cast; ring
  have h5 : (1000 / 6 : ℝ) ^ 5 ≤ (y / 6) ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5
  have h6 : (1000 / 6 : ℝ) ^ 5 * (y / 6) ≤ (y / 6) ^ 6 := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right h5 hy6_nn
  have hcoeff : (1000 / 6 : ℝ) ^ 5 * (y / 6) = (31250000000000 / 14580000 : ℝ) * (n : ℝ) := by
    dsimp [y]; ring
  have hlin : 2 * 751 * 101 * ((n : ℝ) + 1) * (89 / 11) ≤ (1000 / 6 : ℝ) ^ 5 * (y / 6) := by
    rw [hcoeff]; linarith
  linarith [le_trans hlin (le_trans h6 (le_trans hpow1 (hexp ▸ hpow2)))]

lemma succ_mul_choose_eq' (n m : ℕ) (hm : m + 1 ≤ n) :
    (m + 1) * Nat.choose n (m + 1) = (n - m) * Nat.choose n m := by
  have h1 := Nat.choose_mul_factorial_mul_factorial hm
  have h2 := Nat.choose_mul_factorial_mul_factorial (show m ≤ n by omega)
  have hf1 : Nat.factorial (m + 1) = (m + 1) * Nat.factorial m := Nat.factorial_succ m
  have hf2 : Nat.factorial (n - m) = (n - m) * Nat.factorial (n - (m + 1)) := by
    rw [show n - m = (n - (m + 1)) + 1 by omega, Nat.factorial_succ,
      show n - (m + 1) + 1 = n - m by omega]
  have hpos : 0 < Nat.factorial m * Nat.factorial (n - (m + 1)) := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc (m + 1) * Nat.choose n (m + 1) * (Nat.factorial m * Nat.factorial (n - (m + 1)))
      = Nat.choose n (m + 1) * ((m + 1) * Nat.factorial m) * Nat.factorial (n - (m + 1)) := by ring
    _ = Nat.factorial n := by rw [← hf1]; exact h1
    _ = Nat.choose n m * Nat.factorial m * ((n - m) * Nat.factorial (n - (m + 1))) := by
        rw [← hf2]; exact h2.symm
    _ = (n - m) * Nat.choose n m * (Nat.factorial m * Nat.factorial (n - (m + 1))) := by ring

lemma choose_t_upper {n : ℕ} (hn : 10 ^ 7 ≤ n) :
    (Nat.choose n (9 * n / 1000) : ℝ) ≤
      Real.exp ((n : ℝ) * (-((9 : ℝ) / 1000 * Real.log (9 / 1000) +
        (991 : ℝ) / 1000 * Real.log (991 / 1000)))) := by
  set t := 9 * n / 1000
  have htn : t ≤ n := by omega
  have hbin := add_pow ((9 : ℝ) / 1000) ((991 : ℝ) / 1000) n
  have h1 : (1 : ℝ) = ∑ k ∈ Finset.range (n + 1),
      ((9 : ℝ) / 1000) ^ k * ((991 : ℝ) / 1000) ^ (n - k) * (Nat.choose n k : ℝ) := by
    have hsum : ((9 : ℝ) / 1000 + 991 / 1000) ^ n = 1 := by norm_num
    rw [← hsum, hbin]
  have hsingle : (Nat.choose n t : ℝ) * (((9 : ℝ) / 1000) ^ t * ((991 : ℝ) / 1000) ^ (n - t)) ≤ 1 := by
    have hle := Finset.single_le_sum (f := fun k =>
        ((9 : ℝ) / 1000) ^ k * ((991 : ℝ) / 1000) ^ (n - k) * (Nat.choose n k : ℝ))
      (fun k _ => by positivity) (Finset.mem_range.mpr (by omega : t < n + 1))
    linarith
  have hpow_eq : ((9 : ℝ) / 1000) ^ t * ((991 : ℝ) / 1000) ^ (n - t) =
      ((9 : ℝ) / 991) ^ (t : ℝ) * ((991 : ℝ) / 1000) ^ (n : ℝ) := by
    rw [Real.rpow_natCast, Real.rpow_natCast]
    have hsplit : ((9 : ℝ) / 1000) ^ t = ((9 : ℝ) / 991) ^ t * ((991 : ℝ) / 1000) ^ t := by
      rw [← mul_pow]; congr 1; norm_num
    rw [hsplit, mul_assoc, ← pow_add, Nat.add_sub_of_le htn]
  have ht_le_R : (t : ℝ) ≤ (9 : ℝ) / 1000 * n := by
    have hnat : (1000 * t : ℝ) ≤ 9 * (n : ℝ) := by exact_mod_cast (by omega : 1000 * t ≤ 9 * n)
    linarith
  have hrpow_ge : ((9 : ℝ) / 991) ^ ((9 : ℝ) / 1000 * n) ≤ ((9 : ℝ) / 991) ^ (t : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ht_le_R
  have hexp_eq : ((9 : ℝ) / 991) ^ ((9 : ℝ) / 1000 * n) * ((991 : ℝ) / 1000) ^ (n : ℝ) =
      Real.exp ((n : ℝ) * ((9 : ℝ) / 1000 * Real.log (9 / 1000) +
        (991 : ℝ) / 1000 * Real.log (991 / 1000))) := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos (by norm_num), ← Real.exp_add]
    congr 1
    have hdiv : (9 : ℝ) / 991 = (9 / 1000) / (991 / 1000) := by norm_num
    rw [hdiv, Real.log_div (by norm_num) (by norm_num)]
    ring
  have hprod : (Nat.choose n t : ℝ) * Real.exp ((n : ℝ) * ((9 : ℝ) / 1000 * Real.log (9 / 1000) +
      (991 : ℝ) / 1000 * Real.log (991 / 1000))) ≤ 1 := by
    rw [← hexp_eq]
    have hmul : (Nat.choose n t : ℝ) * (((9 : ℝ) / 991) ^ ((9 : ℝ) / 1000 * n) * ((991 : ℝ) / 1000) ^ (n : ℝ)) ≤
        (Nat.choose n t : ℝ) * (((9 : ℝ) / 991) ^ (t : ℝ) * ((991 : ℝ) / 1000) ^ (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrpow_ge (by positivity)) (by positivity)
    rw [← hpow_eq] at hmul
    exact le_trans hmul hsingle
  have hexp_pos : 0 < Real.exp ((n : ℝ) * ((9 : ℝ) / 1000 * Real.log (9 / 1000) +
      (991 : ℝ) / 1000 * Real.log (991 / 1000))) := Real.exp_pos _
  have hmul_pos := mul_le_mul_of_nonneg_right hprod (le_of_lt (Real.exp_pos ((n : ℝ) *
    (-((9 : ℝ) / 1000 * Real.log (9 / 1000) + (991 : ℝ) / 1000 * Real.log (991 / 1000))))))
  have hcancel : Real.exp ((n : ℝ) * ((9 : ℝ) / 1000 * Real.log (9 / 1000) +
        (991 : ℝ) / 1000 * Real.log (991 / 1000))) *
      Real.exp ((n : ℝ) * (-((9 : ℝ) / 1000 * Real.log (9 / 1000) +
        (991 : ℝ) / 1000 * Real.log (991 / 1000)))) = 1 := by
    rw [← Real.exp_add]
    have h0 : (n : ℝ) * ((9 : ℝ) / 1000 * Real.log (9 / 1000) +
        (991 : ℝ) / 1000 * Real.log (991 / 1000)) +
      (n : ℝ) * (-((9 : ℝ) / 1000 * Real.log (9 / 1000) +
        (991 : ℝ) / 1000 * Real.log (991 / 1000))) = 0 := by ring
    rw [h0, Real.exp_zero]
  rw [mul_assoc, hcancel, mul_one] at hmul_pos
  linarith

lemma choose_w_lower {n : ℕ} (hn : 10 ^ 7 ≤ n) :
    1 / (2 * ((n : ℝ) + 1) * (89 / 11)) *
      Real.exp ((n : ℝ) * (-((11 : ℝ) / 100 * Real.log (11 / 100) +
        (89 : ℝ) / 100 * Real.log (89 / 100)))) ≤
      (Nat.choose n (11 * n / 100) : ℝ) := by
  set w := 11 * n / 100
  have hwn : w ≤ n := by omega
  have hwn1 : w + 1 ≤ n := by omega
  let term : ℕ → ℝ := fun k =>
    ((11 : ℝ) / 100) ^ k * ((89 : ℝ) / 100) ^ (n - k) * (Nat.choose n k : ℝ)
  have hup : ∀ m, m + 1 ≤ w → term m ≤ term (m + 1) := by
    intro m hm
    have hmn : m + 1 ≤ n := by omega
    have hm_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    apply le_of_mul_le_mul_left _ hm_pos
    have hrelR : ((m + 1 : ℕ) : ℝ) * (Nat.choose n (m + 1) : ℝ) =
        ((n - m : ℕ) : ℝ) * (Nat.choose n m : ℝ) := by exact_mod_cast succ_mul_choose_eq' n m hmn
    have hL : ((m + 1 : ℕ) : ℝ) * term m =
        ((11 : ℝ) / 100) ^ m * ((89 : ℝ) / 100) ^ (n - (m + 1)) * (Nat.choose n m : ℝ) *
          (((m + 1 : ℕ) : ℝ) * (89 / 100)) := by
      dsimp [term]
      rw [show n - m = (n - (m + 1)) + 1 by omega, pow_succ]
      ring
    have hR : ((m + 1 : ℕ) : ℝ) * term (m + 1) =
        ((11 : ℝ) / 100) ^ m * ((89 : ℝ) / 100) ^ (n - (m + 1)) * (Nat.choose n m : ℝ) *
          (((n - m : ℕ) : ℝ) * (11 / 100)) := by
      dsimp [term]
      calc ((m + 1 : ℕ) : ℝ) * (((11 : ℝ) / 100) ^ (m + 1) * ((89 : ℝ) / 100) ^ (n - (m + 1)) *
              (Nat.choose n (m + 1) : ℝ))
          = ((11 : ℝ) / 100) ^ (m + 1) * ((89 : ℝ) / 100) ^ (n - (m + 1)) *
              (((m + 1 : ℕ) : ℝ) * (Nat.choose n (m + 1) : ℝ)) := by ring
        _ = ((11 : ℝ) / 100) ^ (m + 1) * ((89 : ℝ) / 100) ^ (n - (m + 1)) *
              (((n - m : ℕ) : ℝ) * (Nat.choose n m : ℝ)) := by rw [hrelR]
        _ = ((11 : ℝ) / 100) ^ m * ((89 : ℝ) / 100) ^ (n - (m + 1)) * (Nat.choose n m : ℝ) *
              (((n - m : ℕ) : ℝ) * (11 / 100)) := by rw [pow_succ]; ring
    rw [hL, hR]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hnat : 89 * (m + 1) ≤ 11 * (n - m) := by omega
    have hR' : (89 * (m + 1 : ℕ) : ℝ) ≤ 11 * ((n - m : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  have hstep_w : term (w + 1) ≤ 2 * term w := by
    have hm_pos : (0 : ℝ) < ((w + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos w
    apply le_of_mul_le_mul_left _ hm_pos
    have hrelR : ((w + 1 : ℕ) : ℝ) * (Nat.choose n (w + 1) : ℝ) =
        ((n - w : ℕ) : ℝ) * (Nat.choose n w : ℝ) := by exact_mod_cast succ_mul_choose_eq' n w hwn1
    have hL : ((w + 1 : ℕ) : ℝ) * term (w + 1) =
        ((11 : ℝ) / 100) ^ w * ((89 : ℝ) / 100) ^ (n - (w + 1)) * (Nat.choose n w : ℝ) *
          (((n - w : ℕ) : ℝ) * (11 / 100)) := by
      dsimp [term]
      calc ((w + 1 : ℕ) : ℝ) * (((11 : ℝ) / 100) ^ (w + 1) * ((89 : ℝ) / 100) ^ (n - (w + 1)) *
              (Nat.choose n (w + 1) : ℝ))
          = ((11 : ℝ) / 100) ^ (w + 1) * ((89 : ℝ) / 100) ^ (n - (w + 1)) *
              (((w + 1 : ℕ) : ℝ) * (Nat.choose n (w + 1) : ℝ)) := by ring
        _ = ((11 : ℝ) / 100) ^ (w + 1) * ((89 : ℝ) / 100) ^ (n - (w + 1)) *
              (((n - w : ℕ) : ℝ) * (Nat.choose n w : ℝ)) := by rw [hrelR]
        _ = ((11 : ℝ) / 100) ^ w * ((89 : ℝ) / 100) ^ (n - (w + 1)) * (Nat.choose n w : ℝ) *
              (((n - w : ℕ) : ℝ) * (11 / 100)) := by rw [pow_succ]; ring
    have hR : ((w + 1 : ℕ) : ℝ) * (2 * term w) =
        ((11 : ℝ) / 100) ^ w * ((89 : ℝ) / 100) ^ (n - (w + 1)) * (Nat.choose n w : ℝ) *
          (2 * ((w + 1 : ℕ) : ℝ) * (89 / 100)) := by
      dsimp [term]
      rw [show n - w = (n - (w + 1)) + 1 by omega, pow_succ]
      ring
    rw [hL, hR]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hnat : 11 * (n - w) ≤ 2 * 89 * (w + 1) := by omega
    have hR' : (11 * ((n - w : ℕ) : ℝ)) ≤ 2 * 89 * ((w + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  have hdown : ∀ m, w + 1 ≤ m → m + 1 ≤ n → term (m + 1) ≤ term m := by
    intro m hmw hmn
    have hm_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    apply le_of_mul_le_mul_left _ hm_pos
    have hrelR : ((m + 1 : ℕ) : ℝ) * (Nat.choose n (m + 1) : ℝ) =
        ((n - m : ℕ) : ℝ) * (Nat.choose n m : ℝ) := by exact_mod_cast succ_mul_choose_eq' n m hmn
    have hL : ((m + 1 : ℕ) : ℝ) * term (m + 1) =
        ((11 : ℝ) / 100) ^ m * ((89 : ℝ) / 100) ^ (n - (m + 1)) * (Nat.choose n m : ℝ) *
          (((n - m : ℕ) : ℝ) * (11 / 100)) := by
      dsimp [term]
      calc ((m + 1 : ℕ) : ℝ) * (((11 : ℝ) / 100) ^ (m + 1) * ((89 : ℝ) / 100) ^ (n - (m + 1)) *
              (Nat.choose n (m + 1) : ℝ))
          = ((11 : ℝ) / 100) ^ (m + 1) * ((89 : ℝ) / 100) ^ (n - (m + 1)) *
              (((m + 1 : ℕ) : ℝ) * (Nat.choose n (m + 1) : ℝ)) := by ring
        _ = ((11 : ℝ) / 100) ^ (m + 1) * ((89 : ℝ) / 100) ^ (n - (m + 1)) *
              (((n - m : ℕ) : ℝ) * (Nat.choose n m : ℝ)) := by rw [hrelR]
        _ = ((11 : ℝ) / 100) ^ m * ((89 : ℝ) / 100) ^ (n - (m + 1)) * (Nat.choose n m : ℝ) *
              (((n - m : ℕ) : ℝ) * (11 / 100)) := by rw [pow_succ]; ring
    have hR : ((m + 1 : ℕ) : ℝ) * term m =
        ((11 : ℝ) / 100) ^ m * ((89 : ℝ) / 100) ^ (n - (m + 1)) * (Nat.choose n m : ℝ) *
          (((m + 1 : ℕ) : ℝ) * (89 / 100)) := by
      dsimp [term]
      rw [show n - m = (n - (m + 1)) + 1 by omega, pow_succ]
      ring
    rw [hL, hR]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hnat : 11 * (n - m) ≤ 89 * (m + 1) := by omega
    have hR' : (11 * ((n - m : ℕ) : ℝ)) ≤ 89 * ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  have hmax : ∀ k, k ≤ n → term k ≤ 2 * term w := by
    intro k hk
    by_cases hkw : k ≤ w
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hkw
      have h1 : term k ≤ term w := by
        induction d generalizing k with
        | zero => rw [Nat.add_zero] at hd; subst hd; exact le_rfl
        | succ d ih => exact le_trans (hup k (by omega)) (ih (k + 1) (by omega) (by omega) (by omega))
      have htw_nn : 0 ≤ term w := by dsimp [term]; positivity
      linarith
    · have hwk : w + 1 ≤ k := by omega
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hwk
      have h1 : ∀ d', w + 1 + d' ≤ n → term (w + 1 + d') ≤ term (w + 1) := by
        intro d'
        induction d' with
        | zero => intro _; exact le_rfl
        | succ d' ih =>
          intro hd'
          rw [show w + 1 + (d' + 1) = (w + 1 + d') + 1 by omega] at hd' ⊢
          exact le_trans (hdown (w + 1 + d') (by omega) hd') (ih (by omega))
      rw [hd]
      exact le_trans (h1 d (by omega)) hstep_w
  have hsum_eq_one : ∑ k ∈ Finset.range (n + 1), term k = 1 := by
    have hbin := add_pow ((11 : ℝ) / 100) ((89 : ℝ) / 100) n
    have h1 : ((11 : ℝ) / 100 + 89 / 100) ^ n = 1 := by norm_num
    rw [← h1, hbin]
  have hsum_le : 1 ≤ 2 * ((n : ℝ) + 1) * term w := by
    calc (1 : ℝ) = ∑ k ∈ Finset.range (n + 1), term k := hsum_eq_one.symm
      _ ≤ ∑ _k ∈ Finset.range (n + 1), (2 * term w) :=
          Finset.sum_le_sum fun k hk => hmax k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
      _ = ((n + 1 : ℕ) : ℝ) * (2 * term w) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = 2 * ((n : ℝ) + 1) * term w := by push_cast; ring
  have hpow_eq : ((11 : ℝ) / 100) ^ w * ((89 : ℝ) / 100) ^ (n - w) =
      ((11 : ℝ) / 89) ^ (w : ℝ) * ((89 : ℝ) / 100) ^ (n : ℝ) := by
    rw [Real.rpow_natCast, Real.rpow_natCast]
    have hsplit : ((11 : ℝ) / 100) ^ w = ((11 : ℝ) / 89) ^ w * ((89 : ℝ) / 100) ^ w := by
      rw [← mul_pow]; congr 1; norm_num
    rw [hsplit, mul_assoc, ← pow_add, Nat.add_sub_of_le hwn]
  have hw_ge_R : (11 : ℝ) / 100 * n - 1 ≤ w := by
    have hnat : (11 * n : ℝ) ≤ 100 * (w : ℝ) + 99 := by
      exact_mod_cast (by omega : 11 * n ≤ 100 * w + 99)
    linarith
  have hrpow_le : ((11 : ℝ) / 89) ^ (w : ℝ) ≤ ((11 : ℝ) / 89) ^ ((11 : ℝ) / 100 * n - 1) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hw_ge_R
  have hrpow_sub : ((11 : ℝ) / 89) ^ ((11 : ℝ) / 100 * n - 1) =
      (89 / 11) * ((11 : ℝ) / 89) ^ ((11 : ℝ) / 100 * n) := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_neg (by norm_num), Real.rpow_one]
    ring
  have hexp_eq : ((11 : ℝ) / 89) ^ ((11 : ℝ) / 100 * n) * ((89 : ℝ) / 100) ^ (n : ℝ) =
      Real.exp ((n : ℝ) * ((11 : ℝ) / 100 * Real.log (11 / 100) +
        (89 : ℝ) / 100 * Real.log (89 / 100))) := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos (by norm_num), ← Real.exp_add]
    congr 1
    have hdiv : (11 : ℝ) / 89 = (11 / 100) / (89 / 100) := by norm_num
    rw [hdiv, Real.log_div (by norm_num) (by norm_num)]
    ring
  have hterm_ub : term w ≤ (Nat.choose n w : ℝ) * (89 / 11) *
      Real.exp ((n : ℝ) * ((11 : ℝ) / 100 * Real.log (11 / 100) +
        (89 : ℝ) / 100 * Real.log (89 / 100))) := by
    dsimp [term]
    rw [hpow_eq, ← hexp_eq]
    have hmul : ((11 : ℝ) / 89) ^ (w : ℝ) * ((89 : ℝ) / 100) ^ (n : ℝ) * (Nat.choose n w : ℝ) ≤
        ((89 / 11) * ((11 : ℝ) / 89) ^ ((11 : ℝ) / 100 * n)) * ((89 : ℝ) / 100) ^ (n : ℝ) *
          (Nat.choose n w : ℝ) := by
      rw [← hrpow_sub]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hrpow_le (by positivity)) (by positivity)
    refine le_trans hmul ?_
    exact le_of_eq (by ring)
  have h1_le := le_trans hsum_le (mul_le_mul_of_nonneg_left hterm_ub (by positivity))
  have hpos_div : 0 < 2 * ((n : ℝ) + 1) * (89 / 11) := by positivity
  have hexp_pos : 0 < Real.exp ((n : ℝ) * (-((11 : ℝ) / 100 * Real.log (11 / 100) +
      (89 : ℝ) / 100 * Real.log (89 / 100)))) := Real.exp_pos _
  have hmul_exp := mul_le_mul_of_nonneg_right h1_le (le_of_lt hexp_pos)
  have hcancel : Real.exp ((n : ℝ) * ((11 : ℝ) / 100 * Real.log (11 / 100) +
        (89 : ℝ) / 100 * Real.log (89 / 100))) *
      Real.exp ((n : ℝ) * (-((11 : ℝ) / 100 * Real.log (11 / 100) +
        (89 : ℝ) / 100 * Real.log (89 / 100)))) = 1 := by
    rw [← Real.exp_add]
    have h0 : (n : ℝ) * ((11 : ℝ) / 100 * Real.log (11 / 100) +
        (89 : ℝ) / 100 * Real.log (89 / 100)) +
      (n : ℝ) * (-((11 : ℝ) / 100 * Real.log (11 / 100) +
        (89 : ℝ) / 100 * Real.log (89 / 100))) = 0 := by ring
    rw [h0, Real.exp_zero]
  have hrearr : (2 * ((n : ℝ) + 1)) * ((Nat.choose n w : ℝ) * (89 / 11) *
        Real.exp ((n : ℝ) * ((11 : ℝ) / 100 * Real.log (11 / 100) +
          (89 : ℝ) / 100 * Real.log (89 / 100)))) *
      Real.exp ((n : ℝ) * (-((11 : ℝ) / 100 * Real.log (11 / 100) +
        (89 : ℝ) / 100 * Real.log (89 / 100)))) =
      (2 * ((n : ℝ) + 1) * (89 / 11)) * (Nat.choose n w : ℝ) := by
    calc _ = (2 * ((n : ℝ) + 1) * (89 / 11)) * (Nat.choose n w : ℝ) *
          (Real.exp ((n : ℝ) * ((11 : ℝ) / 100 * Real.log (11 / 100) +
              (89 : ℝ) / 100 * Real.log (89 / 100))) *
            Real.exp ((n : ℝ) * (-((11 : ℝ) / 100 * Real.log (11 / 100) +
              (89 : ℝ) / 100 * Real.log (89 / 100))))) := by ring
      _ = (2 * ((n : ℝ) + 1) * (89 / 11)) * (Nat.choose n w : ℝ) := by rw [hcancel, mul_one]
  rw [hrearr, one_mul] at hmul_exp
  rw [one_div, inv_mul_le_iff₀ hpos_div]
  exact hmul_exp

lemma clz_entropy_gap :
    Real.log 2 +
      (-((9 : ℝ) / 1000 * Real.log (9 / 1000) + (991 : ℝ) / 1000 * Real.log (991 / 1000))) -
      (-((11 : ℝ) / 100 * Real.log (11 / 100) + (89 : ℝ) / 100 * Real.log (89 / 100))) +
      0.0001 ≤ 0.5753 * Real.log 2 - 0.0003 := by
  have hlog_inv : ∀ x : ℝ, 0 < x → -Real.log x = Real.log (1 / x) := fun x hx => by
    rw [Real.log_div one_ne_zero (ne_of_gt hx), Real.log_one, zero_sub]
  have hL1 : -Real.log ((9 : ℝ) / 1000) ≤ 7 * Real.log 2 - 19 / 144 := by
    rw [hlog_inv _ (by norm_num)]
    have hsplit : (1 : ℝ) / (9 / 1000) = (2 : ℝ) ^ 7 * (125 / 144) := by norm_num
    rw [hsplit, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
    have hle := Real.log_le_sub_one_of_pos (x := (125 : ℝ) / 144) (by norm_num)
    push_cast; linarith
  have hL2 : -Real.log ((991 : ℝ) / 1000) ≤ 9 / 991 := by
    rw [hlog_inv _ (by norm_num)]
    have hsplit : (1 : ℝ) / (991 / 1000) = (1000 : ℝ) / 991 := by norm_num
    rw [hsplit]
    have hle := Real.log_le_sub_one_of_pos (x := (1000 : ℝ) / 991) (by norm_num)
    linarith
  have hL3 : 3 * Real.log 2 + 6 / 47 ≤ -Real.log ((11 : ℝ) / 100) := by
    rw [hlog_inv _ (by norm_num)]
    have hsplit : (1 : ℝ) / (11 / 100) = (2 : ℝ) ^ 3 * (1 + 3 / 22) := by norm_num
    rw [hsplit, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
    have hle := Real.le_log_one_add_of_nonneg (x := (3 : ℝ) / 22) (by norm_num)
    push_cast; linarith
  have hL4 : (22 : ℝ) / 189 ≤ -Real.log ((89 : ℝ) / 100) := by
    rw [hlog_inv _ (by norm_num)]
    have hsplit : (1 : ℝ) / (89 / 100) = 1 + 11 / 89 := by norm_num
    rw [hsplit]
    have hle := Real.le_log_one_add_of_nonneg (x := (11 : ℝ) / 89) (by norm_num)
    linarith
  have h2_lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h2_hi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  linarith

lemma clz_large_n {n : ℕ} (hn : 10 ^ 7 ≤ n)
    (S : Finset (𝔽₂ n)) (hS : Green31.IsBinarySidon (S : Set (𝔽₂ n))) :
    (S.card : ℝ) ≤ ((2 : ℝ) ^ n) ^ (0.5753 : ℝ) := by
  set w := 11 * n / 100
  set t := 9 * n / 1000
  set jp : ℝ := (751 : ℝ) / 10000 * n
  set J := Nat.floor jp
  set A : ℝ := 751 * 101 * (2 : ℝ) ^ n * (Nat.choose n t : ℝ) / (Nat.choose n w : ℝ)
  set B : ℝ := 751 * 101 * (2 : ℝ) ^ n * ((J : ℝ) + 1) * (2 : ℝ) ^ (2 * J)
  have hquad : (S.card : ℝ) ^ 2 ≤ A * (S.card : ℝ) + B := hadamard_sidon_bound hn S hS
  have hS_le : (S.card : ℝ) ≤ A + Real.sqrt B :=
    quadratic_bound (by positivity) (by positivity) (by positivity) hquad
  have hnR : (10000000 : ℝ) ≤ n := by exact_mod_cast hn
  -- Bound 2 * A ≤ ((2 : ℝ) ^ n) ^ (0.5753 : ℝ)
  have ht_ub := choose_t_upper hn
  have hw_lb := choose_w_lower hn
  have hcw_pos : 0 < (Nat.choose n w : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : w ≤ n)
  have hpoly := poly_le_exp_0001 hn
  have h2_exp : (2 : ℝ) ≤ Real.exp (0.0003 * (n : ℝ)) := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    exact le_trans h1 (Real.exp_le_exp.mpr (by linarith))
  have hrpow_target : ((2 : ℝ) ^ n) ^ (0.5753 : ℝ) = Real.exp ((n : ℝ) * (0.5753 * Real.log 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num)]
    congr 1; ring
  have h2n_exp : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
  have hA_bound : 2 * A ≤ ((2 : ℝ) ^ n) ^ (0.5753 : ℝ) := by
    have hdiv : (Nat.choose n t : ℝ) / (Nat.choose n w : ℝ) ≤
        2 * ((n : ℝ) + 1) * (89 / 11) *
          Real.exp ((n : ℝ) * (-((9 : ℝ) / 1000 * Real.log (9 / 1000) +
            (991 : ℝ) / 1000 * Real.log (991 / 1000)))) /
          Real.exp ((n : ℝ) * (-((11 : ℝ) / 100 * Real.log (11 / 100) +
            (89 : ℝ) / 100 * Real.log (89 / 100)))) := by
      have hpos_d : 0 < 1 / (2 * ((n : ℝ) + 1) * (89 / 11)) *
          Real.exp ((n : ℝ) * (-((11 : ℝ) / 100 * Real.log (11 / 100) +
            (89 : ℝ) / 100 * Real.log (89 / 100)))) := by positivity
      have h1 := div_le_div₀ (by positivity) ht_ub hpos_d hw_lb
      refine le_trans h1 (le_of_eq ?_)
      have hne1 : (2 * ((n : ℝ) + 1) * (89 / 11)) ≠ 0 := by positivity
      field_simp [hne1]
    have hA_le : 2 * A ≤ 2 * (2 * 751 * 101 * ((n : ℝ) + 1) * (89 / 11)) *
        Real.exp ((n : ℝ) * (Real.log 2 +
          (-((9 : ℝ) / 1000 * Real.log (9 / 1000) + (991 : ℝ) / 1000 * Real.log (991 / 1000))) -
          (-((11 : ℝ) / 100 * Real.log (11 / 100) + (89 : ℝ) / 100 * Real.log (89 / 100))))) := by
      dsimp only [A]
      have hmul := mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ 2 * (751 * 101 * (2 : ℝ) ^ n))
      refine le_trans (le_of_eq (by ring)) (le_trans hmul ?_)
      rw [h2n_exp]
      have hexp_comb : Real.exp ((n : ℝ) * Real.log 2) *
            Real.exp ((n : ℝ) * (-((9 : ℝ) / 1000 * Real.log (9 / 1000) +
              (991 : ℝ) / 1000 * Real.log (991 / 1000)))) /
            Real.exp ((n : ℝ) * (-((11 : ℝ) / 100 * Real.log (11 / 100) +
              (89 : ℝ) / 100 * Real.log (89 / 100)))) =
          Real.exp ((n : ℝ) * (Real.log 2 +
            (-((9 : ℝ) / 1000 * Real.log (9 / 1000) + (991 : ℝ) / 1000 * Real.log (991 / 1000))) -
            (-((11 : ℝ) / 100 * Real.log (11 / 100) + (89 : ℝ) / 100 * Real.log (89 / 100))))) := by
        rw [← Real.exp_add, ← Real.exp_sub]
        congr 1; ring
      refine le_of_eq ?_
      calc 2 * (751 * 101 * Real.exp ((n : ℝ) * Real.log 2)) *
            (2 * ((n : ℝ) + 1) * (89 / 11) *
              Real.exp ((n : ℝ) * (-((9 : ℝ) / 1000 * Real.log (9 / 1000) +
                (991 : ℝ) / 1000 * Real.log (991 / 1000)))) /
              Real.exp ((n : ℝ) * (-((11 : ℝ) / 100 * Real.log (11 / 100) +
                (89 : ℝ) / 100 * Real.log (89 / 100)))))
          = 2 * (2 * 751 * 101 * ((n : ℝ) + 1) * (89 / 11)) *
              (Real.exp ((n : ℝ) * Real.log 2) *
                Real.exp ((n : ℝ) * (-((9 : ℝ) / 1000 * Real.log (9 / 1000) +
                  (991 : ℝ) / 1000 * Real.log (991 / 1000)))) /
                Real.exp ((n : ℝ) * (-((11 : ℝ) / 100 * Real.log (11 / 100) +
                  (89 : ℝ) / 100 * Real.log (89 / 100))))) := by ring
        _ = 2 * (2 * 751 * 101 * ((n : ℝ) + 1) * (89 / 11)) *
              Real.exp ((n : ℝ) * (Real.log 2 +
                (-((9 : ℝ) / 1000 * Real.log (9 / 1000) + (991 : ℝ) / 1000 * Real.log (991 / 1000))) -
                (-((11 : ℝ) / 100 * Real.log (11 / 100) + (89 : ℝ) / 100 * Real.log (89 / 100))))) := by
              rw [hexp_comb]
    have hprod_le : 2 * (2 * 751 * 101 * ((n : ℝ) + 1) * (89 / 11)) ≤
        Real.exp (0.0003 * (n : ℝ)) * Real.exp (0.0001 * (n : ℝ)) :=
      mul_le_mul h2_exp hpoly (by positivity) (by positivity)
    refine le_trans hA_le ?_
    have hexp_nn : 0 ≤ Real.exp ((n : ℝ) * (Real.log 2 +
        (-((9 : ℝ) / 1000 * Real.log (9 / 1000) + (991 : ℝ) / 1000 * Real.log (991 / 1000))) -
        (-((11 : ℝ) / 100 * Real.log (11 / 100) + (89 : ℝ) / 100 * Real.log (89 / 100))))) :=
      le_of_lt (Real.exp_pos _)
    have hmul2 := mul_le_mul_of_nonneg_right hprod_le hexp_nn
    refine le_trans hmul2 ?_
    rw [← Real.exp_add, ← Real.exp_add, hrpow_target]
    refine Real.exp_le_exp.mpr ?_
    have hgap := clz_entropy_gap
    nlinarith only [hgap, hnR]
  -- Bound 2 * Real.sqrt B ≤ ((2 : ℝ) ^ n) ^ (0.5753 : ℝ)
  have hB_bound : 2 * Real.sqrt B ≤ ((2 : ℝ) ^ n) ^ (0.5753 : ℝ) := by
    have hJ_le : (J : ℝ) ≤ jp := Nat.floor_le (by dsimp [jp]; positivity)
    have h2J_le : (2 : ℝ) ^ (2 * J) ≤ Real.exp ((n : ℝ) * ((1502 : ℝ) / 10000 * Real.log 2)) := by
      have hpow_rpow : (2 : ℝ) ^ (2 * J) = (2 : ℝ) ^ ((2 * J : ℕ) : ℝ) := (Real.rpow_natCast 2 _).symm
      rw [hpow_rpow, Real.rpow_def_of_pos (by norm_num)]
      refine Real.exp_le_exp.mpr ?_
      have h2J_R : ((2 * J : ℕ) : ℝ) ≤ (n : ℝ) * ((1502 : ℝ) / 10000) := by
        push_cast; dsimp [jp] at hJ_le; linarith
      rw [mul_comm (Real.log 2), ← mul_assoc]
      exact mul_le_mul_of_nonneg_right h2J_R (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
    have hJ1_le : 4 * (751 * 101 * ((J : ℝ) + 1)) ≤ Real.exp (0.0001 * (n : ℝ)) := by
      have hJ_n : (J : ℝ) + 1 ≤ (n : ℝ) + 1 := by dsimp [jp] at hJ_le; linarith
      have h4_le : 4 * (751 * 101 * ((J : ℝ) + 1)) ≤ 2 * 751 * 101 * ((n : ℝ) + 1) * (89 / 11) := by
        nlinarith only [hJ_n, hnR]
      exact le_trans h4_le hpoly
    have h4B_le : 4 * B ≤ Real.exp ((n : ℝ) * (0.0001 + (1 + 1502 / 10000) * Real.log 2)) := by
      dsimp only [B]
      have h4B_eq : 4 * (751 * 101 * (2 : ℝ) ^ n * ((J : ℝ) + 1) * (2 : ℝ) ^ (2 * J)) =
          (4 * (751 * 101 * ((J : ℝ) + 1))) * ((2 : ℝ) ^ n * (2 : ℝ) ^ (2 * J)) := by ring
      rw [h4B_eq]
      have hprod1 : (4 * (751 * 101 * ((J : ℝ) + 1))) * ((2 : ℝ) ^ n * (2 : ℝ) ^ (2 * J)) ≤
          Real.exp (0.0001 * (n : ℝ)) *
            (Real.exp ((n : ℝ) * Real.log 2) * Real.exp ((n : ℝ) * ((1502 : ℝ) / 10000 * Real.log 2))) :=
        mul_le_mul hJ1_le (mul_le_mul (le_of_eq h2n_exp) h2J_le (by positivity) (by positivity))
          (by positivity) (by positivity)
      refine le_trans hprod1 ?_
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (le_of_eq (by ring))
    have hsqrt_le : 2 * Real.sqrt B = Real.sqrt (4 * B) := by
      symm
      rw [show (4 * B : ℝ) = (2 : ℝ) ^ 2 * B by ring, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]
    have hsqrt_exp : Real.sqrt (Real.exp ((n : ℝ) * (0.0001 + (1 + 1502 / 10000) * Real.log 2))) =
        Real.exp ((n : ℝ) * ((0.0001 + (1 + 1502 / 10000) * Real.log 2) / 2)) := by
      rw [show (n : ℝ) * (0.0001 + (1 + 1502 / 10000) * Real.log 2) =
        ((n : ℝ) * ((0.0001 + (1 + 1502 / 10000) * Real.log 2) / 2)) * ((2 : ℕ) : ℝ) by
          push_cast; ring,
        Real.exp_mul, Real.rpow_natCast, Real.sqrt_sq (by positivity)]
    refine le_trans (le_of_eq hsqrt_le) (le_trans (Real.sqrt_le_sqrt h4B_le) ?_)
    rw [hsqrt_exp, hrpow_target]
    refine Real.exp_le_exp.mpr ?_
    have h2_lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h2_hi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
    have hlin : (0.0001 + (1 + 1502 / 10000) * Real.log 2) / 2 ≤ 0.5753 * Real.log 2 := by linarith
    exact mul_le_mul_of_nonneg_left hlin (by positivity)
  linarith

end EntropyBound

end OMA

theorem OMA.solution : type_of% @Green31.green_31.variants.sidon_01n_clz01 := by
  refine ⟨(2 : ℝ) ^ (10 ^ 7), fun n S hS => ?_⟩
  by_cases hn : 10 ^ 7 ≤ n
  · have h1 := OMA.clz_large_n hn S hS
    have hC : (1 : ℝ) ≤ (2 : ℝ) ^ (10 ^ 7) := one_le_pow₀ (by norm_num)
    exact le_trans h1 (le_mul_of_one_le_left (by positivity) hC)
  · have hlt : n ≤ 10 ^ 7 := by omega
    have hcard : S.card ≤ Fintype.card (𝔽₂ n) := Finset.card_le_univ S
    have h2n : Fintype.card (𝔽₂ n) = 2 ^ n := by
      simp [ZMod.card]
    have hS_le : (S.card : ℝ) ≤ (2 : ℝ) ^ (10 ^ 7) := by
      have hnat : S.card ≤ 2 ^ (10 ^ 7) := le_trans (h2n ▸ hcard) (Nat.pow_le_pow_right (by norm_num) hlt)
      exact_mod_cast hnat
    have hrpow : (1 : ℝ) ≤ ((2 : ℝ) ^ n) ^ (0.5753 : ℝ) :=
      Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by norm_num)
    exact le_trans hS_le (le_mul_of_one_le_right (by positivity) hrpow)
