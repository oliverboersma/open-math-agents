import OMAReductions.R_Erdos604_erdos_604_variants_average_R2

/-!
# Circle incidences and bisector-sparse pinned distances

Reduction and adaptation by Hanan Beer (@hananzlt).
The incidence input is the positive-circle case of László A. Székely,
Crossing Numbers and Hard Erdős Problems in Discrete Geometry (1997), Theorem 8.
The parent reduction and its geometric strategy are due to @NicholasWierenga.
The small-pin argument follows the two-point fiber method; the arithmetic
organization builds on Hanan Beer's earlier CircleIncidenceArithmetic development
and @JaviSoto's crossing-number arguments. The `all_distances` lemma is adapted
from @JaviSoto's warning-free PR5124, commit
de6c4ce9e89bbb1b745e0516730e36292db1fe66, preserving attribution.
-/

namespace OMA.R_Erdos604_erdos_604_variants_average_R2_H2_R1

open Finset
open scoped EuclideanGeometry
open scoped Classical

/-- Székely's bounded-multiplicity circle-incidence theorem, in its equivalent
linear-or-cubic form. The constant is uniform in both finite sets. -/
def H1 : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ (A : Finset ℝ²) (L : Finset (ℝ² × ℝ)),
    (∀ c ∈ L, 0 < c.2) →
    (∀ y ∈ A, ∀ z ∈ A, y ≠ z →
      (L.filter fun c => dist y c.1 = c.2 ∧ dist z c.1 = c.2).card ≤ 2) →
    let I := ((L ×ˢ A).filter fun cp => dist cp.2 cp.1.1 = cp.1.2).card
    I ≤ C * (A.card + L.card) ∨ I ^ 3 ≤ C * A.card ^ 2 * L.card ^ 2

/-- Two distinct centers determine a planar point up to at most two choices. -/
def H2 : Prop :=
  ∀ (A : Finset ℝ²) (u v : ℝ²), u ≠ v →
    A.card ≤ 2 * (A.image fun p => (dist p u, dist p v)).card

lemma incidence_arithmetic (C n b D I l : ℕ)
    (hb : 2 ≤ b) (hbn : b ≤ n) (htwo : n ≤ 8 * D ^ 2)
    (hl : l ≤ b * D) (hi : n * b ≤ 2 * I)
    (hc : I ≤ C * (n + l) ∨ I ^ 3 ≤ C * n ^ 2 * l ^ 2) :
    n * b ≤ (8 * (C + 1) * D) ^ 2 := by
  have hn : 0 < n := by omega
  have hb0 : 0 < b := by omega
  by_cases hsmall : b ≤ 4 * C
  · have h := Nat.mul_le_mul htwo hsmall
    nlinarith only [h, sq_nonneg (C : ℤ)]
  rcases hc with hc | hc
  · have hbound : n * b ≤ 2 * C * (n + b * D) := by
      calc
        n * b ≤ 2 * I := hi
        _ ≤ 2 * (C * (n + l)) := Nat.mul_le_mul_left 2 hc
        _ ≤ 2 * (C * (n + b * D)) := by gcongr
        _ = _ := by ring
    have hnD : n ≤ 4 * C * D := by
      apply Nat.le_of_mul_le_mul_right _ hb0
      have hlarge := Nat.mul_le_mul_left n (show 4 * C ≤ b by omega)
      nlinarith only [hbound, hlarge]
    have h := Nat.mul_le_mul hnD (hbn.trans hnD)
    nlinarith only [h, sq_nonneg (C : ℤ)]
  · have cube : (n * b) ^ 3 ≤ 8 * C * n ^ 2 * b ^ 2 * D ^ 2 := by
      calc
        (n * b) ^ 3 ≤ (2 * I) ^ 3 := by gcongr
        _ = 8 * I ^ 3 := by ring
        _ ≤ 8 * (C * n ^ 2 * l ^ 2) := Nat.mul_le_mul_left 8 hc
        _ ≤ 8 * (C * n ^ 2 * (b * D) ^ 2) := by gcongr
        _ = _ := by ring
    have bound : n * b ≤ 8 * C * D ^ 2 := by
      apply Nat.le_of_mul_le_mul_left (c := n ^ 2 * b ^ 2) _ (by positivity)
      nlinarith only [cube]
    nlinarith only [bound, sq_nonneg (C : ℤ)]

lemma all_distances (A : Finset ℝ²) (hn : 2 ≤ A.card) {x : ℝ²} (hx : x ∈ A) :
    (A.image (fun a => dist a x)).card ≤ 2 * distinctDistancesFrom A x := by
  let D := (A.erase x).image fun a => dist a x
  have hd : distinctDistancesFrom A x = D.card := by
    unfold distinctDistancesFrom
    apply congrArg Finset.card
    ext d
    simp only [D, mem_image, mem_erase]
  have hpos : 0 < D.card := card_pos.mpr
    (((erase_nonempty hx).mpr (one_lt_card_iff_nontrivial.mp hn)).image _)
  have all_eq : A.image (fun a => dist a x) = insert 0 D := by
    calc
      _ = (insert x (A.erase x)).image (fun a => dist a x) := by rw [insert_erase hx]
      _ = _ := by rw [image_insert, dist_self]
  rw [hd, all_eq]
  have := card_insert_le 0 D
  omega

lemma two_pin_bound (h : H2) (A B : Finset ℝ²) (hBA : B ⊆ A) (hb : 2 ≤ B.card) :
    A.card ≤ 8 * (B.sup (distinctDistancesFrom A)) ^ 2 := by
  obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp hb
  have hn : 2 ≤ A.card := hb.trans (card_le_card hBA)
  have sub : A.image (fun p => (dist p u, dist p v)) ⊆
      (A.image fun p => dist p u) ×ˢ (A.image fun p => dist p v) := by
    rintro p hp
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hp
    exact mem_product.mpr ⟨mem_image_of_mem _ ha, mem_image_of_mem _ ha⟩
  have hh := (h A u v huv).trans (Nat.mul_le_mul_left 2 (card_le_card sub))
  rw [card_product] at hh
  have huD := (all_distances A hn (hBA hu)).trans
    (Nat.mul_le_mul_left 2 (le_sup hu))
  have hvD := (all_distances A hn (hBA hv)).trans
    (Nat.mul_le_mul_left 2 (le_sup hv))
  calc
    A.card ≤ 2 * ((A.image fun p => dist p u).card *
        (A.image fun p => dist p v).card) := hh
    _ ≤ 2 * ((2 * B.sup (distinctDistancesFrom A)) *
        (2 * B.sup (distinctDistancesFrom A))) := by gcongr
    _ = _ := by ring

lemma circle_family (A B : Finset ℝ²) (hBA : B ⊆ A) (hb : 2 ≤ B.card)
    (hsparse : ∀ y ∈ A, ∀ z ∈ A, y ≠ z →
      (B.filter fun x => dist x y = dist x z).card ≤ 2) :
    ∃ L : Finset (ℝ² × ℝ),
      (∀ c ∈ L, 0 < c.2) ∧
      (∀ y ∈ A, ∀ z ∈ A, y ≠ z →
        (L.filter fun c => dist y c.1 = c.2 ∧ dist z c.1 = c.2).card ≤ 2) ∧
      L.card ≤ B.card * B.sup (distinctDistancesFrom A) ∧
      A.card * B.card ≤ 2 * ((L ×ˢ A).filter fun cp => dist cp.2 cp.1.1 = cp.1.2).card := by
  let L := B.biUnion fun x => (A.erase x).image fun y => (x, dist y x)
  have memL (c : ℝ² × ℝ) : c ∈ L ↔
      c.1 ∈ B ∧ ∃ y ∈ A, y ≠ c.1 ∧ dist y c.1 = c.2 := by
    rcases c with ⟨x, r⟩
    simp only [L, mem_biUnion, mem_image, mem_erase, Prod.mk.injEq]
    aesop
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨_, y, _, hy, hd⟩ := (memL c).mp hc
    rw [← hd]
    exact dist_pos.mpr hy
  · intro y hy z hz hyz
    have maps : ∀ c ∈ L.filter (fun c => dist y c.1 = c.2 ∧ dist z c.1 = c.2),
        c.1 ∈ B.filter (fun x => dist x y = dist x z) := by
      intro c hc
      obtain ⟨hcL, hcy, hcz⟩ := mem_filter.mp hc
      refine mem_filter.mpr ⟨((memL c).mp hcL).1, ?_⟩
      rw [dist_comm _ y, dist_comm _ z, hcy, hcz]
    have inj : Set.InjOn Prod.fst
        (↑(L.filter fun c => dist y c.1 = c.2 ∧ dist z c.1 = c.2) : Set (ℝ² × ℝ)) := by
      intro c hc d hd hcd
      apply Prod.ext hcd
      have hc' := (mem_filter.mp hc).2.1
      have hd' := (mem_filter.mp hd).2.1
      rw [← hc', ← hd', hcd]
    exact (card_le_card_of_injOn Prod.fst maps inj).trans (hsparse y hy z hz hyz)
  · calc
      L.card ≤ ∑ x ∈ B, ((A.erase x).image fun y => (x, dist y x)).card := card_biUnion_le
      _ ≤ ∑ x ∈ B, distinctDistancesFrom A x := by
        apply sum_le_sum
        intro x hx
        have he : (A.erase x).image (fun y => (x, dist y x)) =
            ((A.erase x).image fun y => dist y x).image (fun r => (x, r)) := by
          rw [image_image]
          rfl
        rw [he]
        have hd : distinctDistancesFrom A x = ((A.erase x).image fun y => dist y x).card := by
          unfold distinctDistancesFrom
          apply congrArg Finset.card
          ext d
          simp only [mem_image, mem_erase]
        rw [hd]
        exact card_image_le
      _ ≤ ∑ _x ∈ B, B.sup (distinctDistancesFrom A) := sum_le_sum fun x hx => le_sup hx
      _ = _ := by simp
  · let N := (B ×ˢ A) \ B.diag
    let f (p : ℝ² × ℝ²) := ((p.1, dist p.2 p.1), p.2)
    have inj : Function.Injective f := by
      intro p q h
      exact Prod.ext (congrArg (fun t : (ℝ² × ℝ) × ℝ² => t.1.1) h)
        (congrArg (fun t : (ℝ² × ℝ) × ℝ² => t.2) h)
    have maps : ∀ p ∈ N,
        f p ∈ (L ×ˢ A).filter (fun cp => dist cp.2 cp.1.1 = cp.1.2) := by
      intro p hp
      obtain ⟨hp, hdiag⟩ := mem_sdiff.mp hp
      obtain ⟨hB, hA⟩ := mem_product.mp hp
      have hne : p.2 ≠ p.1 := by
        intro he
        exact hdiag (mem_diag.mpr ⟨hB, he.symm⟩)
      exact mem_filter.mpr ⟨mem_product.mpr
        ⟨(memL _).mpr ⟨hB, p.2, hA, hne, rfl⟩, hA⟩, rfl⟩
    have hcard := card_le_card_of_injOn f maps inj.injOn
    have diag_sub : B.diag ⊆ B ×ˢ A := by
      intro p hp
      obtain ⟨hB, he⟩ := mem_diag.mp hp
      exact mem_product.mpr ⟨hB, he ▸ hBA hB⟩
    have count : N.card = B.card * (A.card - 1) := by
      dsimp only [N]
      rw [card_sdiff_of_subset diag_sub, card_product, diag_card, Nat.mul_sub_left_distrib]
      simp
    have hn : 2 ≤ A.card := hb.trans (card_le_card hBA)
    have hhalf : A.card ≤ 2 * (A.card - 1) := by omega
    calc
      A.card * B.card ≤ (2 * (A.card - 1)) * B.card := Nat.mul_le_mul_right _ hhalf
      _ = 2 * N.card := by rw [count]; ring
      _ ≤ _ := Nat.mul_le_mul_left 2 hcard

theorem main : H1 → H2 →
    OMA.R_Erdos604_erdos_604_variants_average_R2.H2 := by
  rintro ⟨C, hC, hinc⟩ htwo
  let K : ℕ := 8 * (C + 1)
  have hK : (0 : ℝ) < K := by dsimp [K]; positivity
  refine ⟨1 / (K : ℝ), by positivity, ?_⟩
  intro A B hBA hb hsparse
  let D := B.sup (distinctDistancesFrom A)
  obtain ⟨L, hpos, hpair, hl, hi⟩ := circle_family A B hBA hb hsparse
  have hbound := incidence_arithmetic C A.card B.card D
    (((L ×ˢ A).filter fun cp => dist cp.2 cp.1.1 = cp.1.2).card) L.card
    hb (card_le_card hBA) (two_pin_bound htwo A B hBA hb) hl hi
    (hinc A L hpos hpair)
  obtain ⟨x, hx, hDx⟩ := B.exists_mem_eq_sup (card_pos.mp (by omega : 0 < B.card))
    (distinctDistancesFrom A)
  refine ⟨x, hx, ?_⟩
  have hreal : (A.card : ℝ) * B.card ≤ ((K : ℝ) * D) ^ 2 := by
    exact_mod_cast hbound
  have hroot : Real.sqrt ((A.card : ℝ) * B.card) ≤ (K : ℝ) * D :=
    (Real.sqrt_le_left (by positivity)).mpr hreal
  have hf : Real.sqrt ((A.card : ℝ) * B.card) / K ≤ D :=
    (div_le_iff₀ hK).mpr (by simpa [mul_comm] using hroot)
  change D = _ at hDx
  rw [← hDx]
  simpa [div_eq_mul_inv, mul_comm] using hf

end OMA.R_Erdos604_erdos_604_variants_average_R2_H2_R1
