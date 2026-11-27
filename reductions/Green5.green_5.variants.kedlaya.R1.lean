import FormalConjectures.GreensOpenProblems.«5»
import Mathlib.Data.Fintype.Powerset
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Order.Preorder.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
Kedlaya's bound using the small-index theorem for nonabelian simple groups
and the product-free coset construction. An abelian simple quotient uses a
linear-size product-free set, as in the cyclic case of Kedlaya's argument.

Source: https://arxiv.org/abs/0708.2295, Sections 2 and 3.
Credit: @justusklocke-cloud
-/

namespace OMA.R_Green5_green_5_variants_kedlaya_R1

private theorem abelian_simple (Q : Type) [Group Q] [Fintype Q] (hs : IsSimpleGroup Q)
    (hc : ∀ x y : Q, x * y = y * x) :
    ∃ T : Finset Q, IsProductFree (T : Set Q) ∧
      (1 / 4 : ℝ) * Fintype.card Q ≤ (T.card : ℝ) := by
  classical
  let : CommGroup Q := { ‹Group Q› with mul_comm := hc }
  obtain ⟨p, hp, ⟨e⟩⟩ := exists_prime_addEquiv_ZMod (G := Q)
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : 2 ≤ p := hp.two_le
  let I := Finset.Icc (p / 3 + 1) (2 * p / 3)
  let f : Q ≃ ZMod p := Additive.ofMul.trans e.toEquiv
  have f_mul (x y : Q) : f (x * y) = f x + f y :=
    e.map_add (Additive.ofMul x) (Additive.ofMul y)
  let g (m : ℕ) : Q := f.symm (m : ZMod p)
  have fg (m : ℕ) : f (g m) = (m : ZMod p) := f.apply_symm_apply _
  have mlt {m : ℕ} (hm : m ∈ I) : m < p := by
    have hr := (Finset.mem_Icc.mp hm).2
    omega
  have val (m : ℕ) (hm : m ∈ I) : (f (g m)).val = m := by
    rw [fg, ZMod.val_natCast_of_lt (mlt hm)]
  let T := I.image g
  refine ⟨T, ?_, ?_⟩
  · rw [isProductFree_iff]
    intro x hx y hy hxy
    change x ∈ I.image g at hx
    change y ∈ I.image g at hy
    change x * y ∈ I.image g at hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨c, hc, heq⟩ := Finset.mem_image.mp hxy
    have hsum : f (g c) = f (g a) + f (g b) := (congrArg f heq).trans (f_mul _ _)
    have hbounda := Finset.mem_Icc.mp ha
    have hboundb := Finset.mem_Icc.mp hb
    have hboundc := Finset.mem_Icc.mp hc
    have he := congrArg ZMod.val hsum
    rw [val c hc] at he
    by_cases hab : a + b < p
    · rw [ZMod.val_add_of_lt (by rwa [val a ha, val b hb]), val a ha, val b hb] at he
      omega
    · rw [ZMod.val_add_of_le (by rw [val a ha, val b hb]; omega), val a ha, val b hb] at he
      omega
  · have hT : T.card = I.card := Finset.card_image_of_injOn fun a ha b hb hab => by
      have he := congrArg (fun q : Q => (f q).val) hab
      rwa [val a ha, val b hb] at he
    have hQ : Fintype.card Q = p := (Fintype.card_congr f).trans (ZMod.card p)
    have hN : p ≤ 4 * I.card := by
      rw [Nat.card_Icc]
      rcases (show p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 from by omega) with h | h | h <;>
        omega
    have hR : (p : ℝ) ≤ 4 * (I.card : ℝ) := by exact_mod_cast hN
    rw [hQ, hT]
    linarith

private theorem combine_index {a b n m s : ℝ} (ha : 0 < a) (hn : 0 < n) (hm : 0 < m)
    (hindex : m ≤ a * n ^ ((3 : ℝ) / 7))
    (hsize : b * n / m ^ ((1 : ℝ) / 2) ≤ s) (hs : 0 ≤ s) :
    (b / a ^ ((1 : ℝ) / 2)) * n ^ ((11 : ℝ) / 14) ≤ s := by
  have hmroot := Real.rpow_pos_of_pos hm ((1 : ℝ) / 2)
  have haroot := Real.rpow_pos_of_pos ha ((1 : ℝ) / 2)
  have hnpow := Real.rpow_pos_of_pos hn ((3 : ℝ) / 14)
  have hroot : m ^ ((1 : ℝ) / 2) ≤ a ^ ((1 : ℝ) / 2) * n ^ ((3 : ℝ) / 14) := by
    calc
      _ ≤ (a * n ^ ((3 : ℝ) / 7)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow hm.le hindex (by norm_num)
      _ = _ := by
        rw [Real.mul_rpow ha.le (Real.rpow_nonneg hn.le _), ← Real.rpow_mul hn.le]
        norm_num
  apply le_of_mul_le_mul_right _ (mul_pos haroot hnpow)
  calc
    (b / a ^ ((1 : ℝ) / 2) * n ^ ((11 : ℝ) / 14)) *
        (a ^ ((1 : ℝ) / 2) * n ^ ((3 : ℝ) / 14)) =
        b * (n ^ ((11 : ℝ) / 14) * n ^ ((3 : ℝ) / 14)) := by
      field_simp
    _ = b * n := by rw [← Real.rpow_add hn]; norm_num
    _ ≤ s * m ^ ((1 : ℝ) / 2) := (div_le_iff₀ hmroot).mp hsize
    _ ≤ s * (a ^ ((1 : ℝ) / 2) * n ^ ((3 : ℝ) / 14)) :=
      mul_le_mul_of_nonneg_left hroot hs

private theorem pullback_product_free {G Q : Type} [Group G] [Fintype G] [Group Q] [Fintype Q]
    (f : G →* Q) (hf : Function.Surjective f) {c : ℝ} (hc : 0 ≤ c)
    (T : Finset Q) (hT : IsProductFree (T : Set Q))
    (hcard : c * (Fintype.card Q : ℝ) ^ ((11 : ℝ) / 14) ≤ (T.card : ℝ)) :
    ∃ S : Finset G, IsProductFree (S : Set G) ∧
      c * (Fintype.card G : ℝ) ^ ((11 : ℝ) / 14) ≤ (S.card : ℝ) := by
  classical
  let S : Finset G := Finset.univ.filter (fun g => f g ∈ T)
  let k := (Finset.univ.filter (fun g : G => f g = 1)).card
  have hk : 1 ≤ k := by
    exact Finset.card_pos.mpr ⟨1, by simp⟩
  have hcount (U : Finset Q) :
      (Finset.univ.filter (fun g : G => f g ∈ U)).card = U.card * k := by
    rw [← Finset.sum_card_fiberwise_eq_card_filter Finset.univ U (fun g : G => f g)]
    apply Finset.sum_const_nat
    intro u _
    exact MonoidHom.card_fiber_eq_of_mem_range f (hf u) (hf 1)
  have hS : S.card = T.card * k := hcount T
  have hG : Fintype.card G = Fintype.card Q * k := by
    simpa using hcount Finset.univ
  refine ⟨S, isProductFree_iff.mpr ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_univ, true_and, map_mul] at hx hy hxy
    exact isProductFree_iff.mp hT (f x) hx (f y) hy hxy
  · have hkpow : (k : ℝ) ^ ((11 : ℝ) / 14) ≤ (k : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hk) (by norm_num : (11 : ℝ) / 14 ≤ 1)
    rw [hG, hS, Nat.cast_mul, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity), ← mul_assoc]
    exact (mul_le_mul_of_nonneg_left hkpow (by positivity)).trans
      (mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg _))

private theorem simple_quotient (G : Type) [Group G] [Fintype G] (hG : Nontrivial G) :
    ∃ (N : Subgroup G) (_ : N.Normal), IsSimpleGroup (G ⧸ N) := by
  classical
  let : Nontrivial G := hG
  let : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  let S : Set (Subgroup G) := {H | H.Normal ∧ H ≠ ⊤}
  have hb : (⊥ : Subgroup G) ∈ S := ⟨inferInstance, bot_ne_top⟩
  obtain ⟨N, -, hN⟩ := S.toFinite.exists_le_maximal hb
  have hn : N.Normal := hN.prop.1
  let f := QuotientGroup.mk' N
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective N
  have : Nontrivial (G ⧸ N) := not_subsingleton_iff_nontrivial.mp fun h =>
    hN.prop.2 (QuotientGroup.subgroup_eq_top_of_subsingleton N h)
  refine ⟨N, hn, ⟨?_⟩⟩
  intro H hH
  by_cases htop : H = ⊤
  · exact Or.inr htop
  left
  have hproper : H.comap f ≠ ⊤ := by
    intro heq
    exact htop ((Subgroup.comap_injective hf) (heq.trans (Subgroup.comap_top f).symm))
  have hcomap : H.comap f = N := (hN.eq_of_le ⟨hH.comap f, hproper⟩
    (QuotientGroup.le_comap_mk' N H)).symm
  apply Subgroup.comap_injective hf
  simpa [f] using hcomap

/-- The classification-based estimate for proper subgroup indices. -/
def H1 : Prop :=
  ∃ a > (0 : ℝ), ∀ (Q : Type) [Group Q] [Fintype Q], IsSimpleGroup Q →
    (¬ ∀ x y : Q, x * y = y * x) →
    ∃ H : Subgroup Q, H ≠ ⊤ ∧ (H.index : ℝ) ≤ a * (Fintype.card Q : ℝ) ^ ((3 : ℝ) / 7)

/-- Kedlaya's product-free set bound from a proper subgroup of given index. -/
def H2 : Prop :=
  ∃ b > (0 : ℝ), ∀ (Q : Type) [Group Q] [Fintype Q] (H : Subgroup Q), H ≠ ⊤ →
    ∃ T : Finset Q, IsProductFree (T : Set Q) ∧
      b * Fintype.card Q / (H.index : ℝ) ^ ((1 : ℝ) / 2) ≤ (T.card : ℝ)

theorem main : H1 → H2 → type_of% @Green5.green_5.variants.kedlaya := by
  classical
  rintro ⟨a, ha, hindex⟩ ⟨b, hb, hcoset⟩
  let c := min (b / a ^ ((1 : ℝ) / 2)) (1 / 4)
  have hc : 0 < c := lt_min (div_pos hb (Real.rpow_pos_of_pos ha _)) (by norm_num)
  refine ⟨c, hc, ?_⟩
  intro G _ _ hG
  obtain ⟨N, hN, hsimple⟩ := simple_quotient G hG
  let : N.Normal := hN
  let : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hq : (0 : ℝ) < Fintype.card (G ⧸ N) := by exact_mod_cast Fintype.card_pos
  have hq1 : (1 : ℝ) ≤ Fintype.card (G ⧸ N) := by
    exact_mod_cast Fintype.card_pos
  obtain ⟨T, hT, hTc⟩ : ∃ T : Finset (G ⧸ N), IsProductFree (T : Set (G ⧸ N)) ∧
      c * (Fintype.card (G ⧸ N) : ℝ) ^ ((11 : ℝ) / 14) ≤ (T.card : ℝ) := by
    by_cases hcomm : ∀ x y : G ⧸ N, x * y = y * x
    · obtain ⟨T, hT, hsize⟩ := abelian_simple (G ⧸ N) hsimple hcomm
      have hpow : (Fintype.card (G ⧸ N) : ℝ) ^ ((11 : ℝ) / 14) ≤
          (Fintype.card (G ⧸ N) : ℝ) := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num : (11 : ℝ) / 14 ≤ 1)
      exact ⟨T, hT, (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans
        ((mul_le_mul_of_nonneg_left hpow (by norm_num)).trans hsize)⟩
    · obtain ⟨H, hH, hm⟩ := hindex (G ⧸ N) hsimple hcomm
      obtain ⟨T, hT, hsize⟩ := hcoset (G ⧸ N) H hH
      have hmpos : (0 : ℝ) < (H.index : ℝ) := by
        exact_mod_cast (zero_lt_one.trans (H.one_lt_index_of_ne_top hH))
      have hbound := combine_index ha hq hmpos hm hsize (Nat.cast_nonneg _)
      exact ⟨T, hT, (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans hbound⟩
  exact pullback_product_free (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    hc.le T hT hTc

end OMA.R_Green5_green_5_variants_kedlaya_R1
