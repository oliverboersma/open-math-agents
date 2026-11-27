import OMAStatements.S_oeis_a039799
import Mathlib

namespace OMA.A039799Proof

open OMA.S_oeis_a039799

theorem mem_ps {s : Finset ℕ} {t : ℕ} :
    t ∈ pairSums s ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a < b ∧ a + b = t := by
  unfold pairSums
  simp only [Finset.mem_image, Finset.mem_filter, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨hp, hab⟩, rfl⟩
    have hp' := Finset.mem_product.1 hp
    exact ⟨a, b, hp'.1, hp'.2, hab, rfl⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    exact ⟨a, b, ⟨Finset.mem_product.2 ⟨ha, hb⟩, hab⟩, rfl⟩

theorem wit {X : Finset ℕ} {t : ℕ} (a b : ℕ) (ha : a ∈ X) (hb : b ∈ X) (h1 : a < b)
    (h2 : a + b = t) : t ∈ pairSums X :=
  mem_ps.2 ⟨a, b, ha, hb, h1, h2⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem fin8 : ∀ u ∈ (Finset.Icc 1 8).powerset,
    4 ≤ ((Finset.Icc 3 9).filter
      (fun t => t ∉ pairSums u ∩ pairSums (Finset.Icc 1 8 \ u))).card := by
  decide

theorem fin8' (u : Finset ℕ) (hu : u ⊆ Finset.Icc 1 8) :
    4 ≤ ((Finset.Icc 3 9).filter
      (fun t => t ∉ pairSums u ∩ pairSums (Finset.Icc 1 8 \ u))).card :=
  fin8 u (Finset.mem_powerset.2 hu)

theorem low (n : ℕ) (_hn : 8 ≤ n) (X : Finset ℕ) (hX : X ⊆ Finset.Icc 1 n) (t : ℕ)
    (ht : t ≤ 9) :
    t ∈ pairSums X ↔ t ∈ pairSums ((Finset.Icc 1 8).filter (· ∈ X)) := by
  rw [mem_ps, mem_ps]
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    have h1 := Finset.mem_Icc.1 (hX ha)
    have h2 := Finset.mem_Icc.1 (hX hb)
    refine ⟨a, b, ?_, ?_, hab, rfl⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]; exact ⟨by omega, ha⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]; exact ⟨by omega, hb⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    exact ⟨a, b, (Finset.mem_filter.1 ha).2, (Finset.mem_filter.1 hb).2, hab, rfl⟩

theorem high (n : ℕ) (hn : 8 ≤ n) (X : Finset ℕ) (hX : X ⊆ Finset.Icc 1 n) (k : ℕ)
    (hk : k ≤ 9) :
    2 * n + 2 - k ∈ pairSums X ↔
      k ∈ pairSums ((Finset.Icc 1 8).filter (fun y => n + 1 - y ∈ X)) := by
  rw [mem_ps, mem_ps]
  constructor
  · rintro ⟨a, b, ha, hb, hab, hs⟩
    have h1 := Finset.mem_Icc.1 (hX ha)
    have h2 := Finset.mem_Icc.1 (hX hb)
    refine ⟨n + 1 - b, n + 1 - a, ?_, ?_, by omega, by omega⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨by omega, ?_⟩
      have : n + 1 - (n + 1 - b) = b := by omega
      rw [this]; exact hb
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨by omega, ?_⟩
      have : n + 1 - (n + 1 - a) = a := by omega
      rw [this]; exact ha
  · rintro ⟨a, b, ha, hb, hab, hs⟩
    have h1 := (Finset.mem_filter.1 ha)
    have h2 := (Finset.mem_filter.1 hb)
    have h1' := Finset.mem_Icc.1 h1.1
    have h2' := Finset.mem_Icc.1 h2.1
    exact ⟨n + 1 - b, n + 1 - a, h2.2, h1.2, by omega, by omega⟩

theorem upper (n : ℕ) (hn : 14 ≤ n) (s : Finset ℕ) (hs : s ⊆ Finset.Icc 1 n) :
    (pairSums s ∩ pairSums (Finset.Icc 1 n \ s)).card ≤ 2 * n - 11 := by
  have hc : Finset.Icc 1 n \ s ⊆ Finset.Icc 1 n := Finset.sdiff_subset
  set C := pairSums s ∩ pairSums (Finset.Icc 1 n \ s) with hC
  set u := (Finset.Icc 1 8).filter (· ∈ s) with hu
  set v := (Finset.Icc 1 8).filter (fun y => n + 1 - y ∈ s) with hv
  have hu' : Finset.Icc 1 8 \ u = (Finset.Icc 1 8).filter (· ∈ Finset.Icc 1 n \ s) := by
    ext x
    simp only [hu, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, ⟨by omega, fun h => h2 ⟨h1, h⟩⟩⟩
    · rintro ⟨h1, ⟨_, h2⟩⟩; exact ⟨h1, fun h => h2 h.2⟩
  have hv' : Finset.Icc 1 8 \ v =
      (Finset.Icc 1 8).filter (fun y => n + 1 - y ∈ Finset.Icc 1 n \ s) := by
    ext x
    simp only [hv, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, ⟨by omega, fun h => h2 ⟨h1, h⟩⟩⟩
    · rintro ⟨h1, ⟨_, h2⟩⟩; exact ⟨h1, fun h => h2 h.2⟩
  set L := (Finset.Icc 3 9).filter (fun t => t ∉ pairSums u ∩ pairSums (Finset.Icc 1 8 \ u))
    with hL
  set L' := (Finset.Icc 3 9).filter (fun t => t ∉ pairSums v ∩ pairSums (Finset.Icc 1 8 \ v))
    with hL'
  have hL4 : 4 ≤ L.card := fin8' u (Finset.filter_subset _ _)
  have hL'4 : 4 ≤ L'.card := fin8' v (Finset.filter_subset _ _)
  set H := L'.image (fun k => 2 * n + 2 - k) with hH
  have hHc : H.card = L'.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hx' := Finset.mem_Icc.1 (Finset.mem_filter.1 hx).1
    have hy' := Finset.mem_Icc.1 (Finset.mem_filter.1 hy).1
    simp only at hxy
    omega
  have hCsub : C ⊆ Finset.Icc 3 (2 * n - 1) := by
    intro t ht
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := mem_ps.1 (Finset.mem_inter.1 ht).1
    have h1 := Finset.mem_Icc.1 (hs ha)
    have h2 := Finset.mem_Icc.1 (hs hb)
    rw [Finset.mem_Icc]; omega
  have hLsub : L ⊆ Finset.Icc 3 (2 * n - 1) := by
    intro t ht
    have := Finset.mem_Icc.1 (Finset.mem_filter.1 ht).1
    rw [Finset.mem_Icc]; omega
  have hHsub : H ⊆ Finset.Icc 3 (2 * n - 1) := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 ht
    have := Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1
    rw [Finset.mem_Icc]; omega
  have dCL : Disjoint C L := by
    rw [Finset.disjoint_left]
    intro t ht htL
    have h3 := Finset.mem_filter.1 htL
    have h4 := Finset.mem_Icc.1 h3.1
    apply h3.2
    have h5 := Finset.mem_inter.1 ht
    rw [Finset.mem_inter, hu']
    exact ⟨(low n (by omega) s hs t (by omega)).1 h5.1,
      (low n (by omega) _ hc t (by omega)).1 h5.2⟩
  have dCH : Disjoint C H := by
    rw [Finset.disjoint_left]
    intro t ht htH
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 htH
    have h3 := Finset.mem_filter.1 hk
    have h4 := Finset.mem_Icc.1 h3.1
    apply h3.2
    have h5 := Finset.mem_inter.1 ht
    rw [Finset.mem_inter, hv']
    exact ⟨(high n (by omega) s hs k (by omega)).1 h5.1,
      (high n (by omega) _ hc k (by omega)).1 h5.2⟩
  have dLH : Disjoint L H := by
    rw [Finset.disjoint_left]
    intro t htL htH
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 htH
    have h3 := Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1
    have h4 := Finset.mem_Icc.1 (Finset.mem_filter.1 htL).1
    omega
  have hunion : C ∪ L ∪ H ⊆ Finset.Icc 3 (2 * n - 1) :=
    Finset.union_subset (Finset.union_subset hCsub hLsub) hHsub
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨dCH, dLH⟩),
    Finset.card_union_of_disjoint dCL, Nat.card_Icc] at hcard
  omega

def sE (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun x => (x % 2 = 0 ∧ x ≠ 4 ∧ x ≠ n) ∨ x = 3 ∨ x = n - 3)

def sO (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun x => (x % 2 = 0 ∧ x ≠ 4 ∧ x ≠ n - 3) ∨ x = 3 ∨ x = n - 2)

theorem even_case (n : ℕ) (hn : 14 ≤ n) (hp : n % 2 = 0) :
    insert 5 (Finset.Icc 8 (2 * n - 5)) ⊆
      pairSums (sE n) ∩ pairSums (Finset.Icc 1 n \ sE n) := by
  have hm : ∀ x, x ∈ sE n ↔ (1 ≤ x ∧ x ≤ n) ∧
      ((x % 2 = 0 ∧ x ≠ 4 ∧ x ≠ n) ∨ x = 3 ∨ x = n - 3) := by
    intro x; simp only [sE, Finset.mem_filter, Finset.mem_Icc]
  have hcm : ∀ x, x ∈ Finset.Icc 1 n \ sE n ↔ (1 ≤ x ∧ x ≤ n) ∧
      ¬ ((x % 2 = 0 ∧ x ≠ 4 ∧ x ≠ n) ∨ x = 3 ∨ x = n - 3) := by
    intro x; simp only [sE, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]; tauto
  intro t ht
  rw [Finset.mem_insert, Finset.mem_Icc] at ht
  rw [Finset.mem_inter]
  constructor
  · rcases ht with rfl | ⟨h1, h2⟩
    · exact wit 2 3 ((hm _).2 (by omega)) ((hm _).2 (by omega)) (by omega) (by omega)
    rcases (by omega : (t % 2 = 0 ∧ t ≤ n) ∨ t = n + 2 ∨ (t % 2 = 0 ∧ n + 4 ≤ t) ∨
        (t % 2 = 1 ∧ t ≤ n + 1) ∨ (t % 2 = 1 ∧ n + 3 ≤ t ∧ t ≤ 2 * n - 7) ∨ t = 2 * n - 5)
      with h | h | h | h | h | h
    · exact wit 2 (t - 2) ((hm _).2 (by omega)) ((hm _).2 (by omega)) (by omega) (by omega)
    · exact wit 6 (n - 4) ((hm _).2 (by omega)) ((hm _).2 (by omega)) (by omega) (by omega)
    · exact wit (t - n + 2) (n - 2) ((hm _).2 (by omega)) ((hm _).2 (by omega)) (by omega)
        (by omega)
    · exact wit 3 (t - 3) ((hm _).2 (by omega)) ((hm _).2 (by omega)) (by omega) (by omega)
    · exact wit (t - n + 3) (n - 3) ((hm _).2 (by omega)) ((hm _).2 (by omega)) (by omega)
        (by omega)
    · exact wit (n - 3) (n - 2) ((hm _).2 (by omega)) ((hm _).2 (by omega)) (by omega)
        (by omega)
  · rcases ht with rfl | ⟨h1, h2⟩
    · exact wit 1 4 ((hcm _).2 (by omega)) ((hcm _).2 (by omega)) (by omega) (by omega)
    rcases (by omega : (t % 2 = 0 ∧ t ≤ n ∧ t ≠ n - 2) ∨ t = n - 2 ∨ t = n + 2 ∨
        (t % 2 = 0 ∧ n + 4 ≤ t) ∨ (t % 2 = 1 ∧ t ≤ n + 3 ∧ t ≠ n + 1) ∨ t = n + 1 ∨
        (t % 2 = 1 ∧ n + 5 ≤ t))
      with h | h | h | h | h | h | h
    · exact wit 1 (t - 1) ((hcm _).2 (by omega)) ((hcm _).2 (by omega)) (by omega) (by omega)
    · exact wit 5 (n - 7) ((hcm _).2 (by omega)) ((hcm _).2 (by omega)) (by omega) (by omega)
    · exact wit 7 (n - 5) ((hcm _).2 (by omega)) ((hcm _).2 (by omega)) (by omega) (by omega)
    · exact wit (t - n + 1) (n - 1) ((hcm _).2 (by omega)) ((hcm _).2 (by omega)) (by omega)
        (by omega)
    · exact wit 4 (t - 4) ((hcm _).2 (by omega)) ((hcm _).2 (by omega)) (by omega) (by omega)
    · exact wit 1 n ((hcm _).2 (by omega)) ((hcm _).2 (by omega)) (by omega) (by omega)
    · exact wit (t - n) n ((hcm _).2 (by omega)) ((hcm _).2 (by omega)) (by omega) (by omega)

theorem odd_case (n : ℕ) (hn : 14 ≤ n) (hp : n % 2 = 1) :
    insert 5 (insert (2 * n - 3) (Finset.Icc 8 (2 * n - 6))) ⊆
      pairSums (sO n) ∩ pairSums (Finset.Icc 1 n \ sO n) := by
  have hm : ∀ x, x ∈ sO n ↔ (1 ≤ x ∧ x ≤ n) ∧
      ((x % 2 = 0 ∧ x ≠ 4 ∧ x ≠ n - 3) ∨ x = 3 ∨ x = n - 2) := by
    intro x; simp only [sO, Finset.mem_filter, Finset.mem_Icc]
  have hcm : ∀ x, x ∈ Finset.Icc 1 n \ sO n ↔ (1 ≤ x ∧ x ≤ n) ∧
      ¬ ((x % 2 = 0 ∧ x ≠ 4 ∧ x ≠ n - 3) ∨ x = 3 ∨ x = n - 2) := by
    intro x; simp only [sO, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]; tauto
  intro t ht
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_Icc] at ht
  rw [Finset.mem_inter]
  constructor
  · rcases ht with rfl | rfl | ⟨h1, h2⟩
    · exact wit 2 3 ((hm _).2 (by omega)) ((hm _).2 (by omega)) (by omega) (by omega)
    · exact wit (n - 2) (n - 1) ((hm _).2 (by omega)) ((hm _).2 (by omega)) (by omega)
        (by omega)
    rcases (by omega : (t % 2 = 0 ∧ t ≤ n + 1 ∧ t ≠ n - 1) ∨ t = n - 1 ∨
        (t % 2 = 0 ∧ n + 5 ≤ t) ∨ t = n + 3 ∨
        (t % 2 = 1 ∧ t ≤ n + 2 ∧ t ≠ n) ∨ t = n ∨ (t % 2 = 1 ∧ n + 4 ≤ t))
      with h | h | h | h | h | h | h
    · exact wit 2 (t - 2) ((hm _).2 (by omega)) ((hm _).2 (by omega)) (by omega) (by omega)
    · exact wit 6 (n - 7) ((hm _).2 (by omega)) ((hm _).2 (by omega)) (by omega) (by omega)
    · exact wit (t - n + 1) (n - 1) ((hm _).2 (by omega)) ((hm _).2 (by omega)) (by omega)
        (by omega)
    · exact wit 8 (n - 5) ((hm _).2 (by omega)) ((hm _).2 (by omega)) (by omega) (by omega)
    · exact wit 3 (t - 3) ((hm _).2 (by omega)) ((hm _).2 (by omega)) (by omega) (by omega)
    · exact wit 2 (n - 2) ((hm _).2 (by omega)) ((hm _).2 (by omega)) (by omega) (by omega)
    · exact wit (t - n + 2) (n - 2) ((hm _).2 (by omega)) ((hm _).2 (by omega)) (by omega)
        (by omega)
  · rcases ht with rfl | rfl | ⟨h1, h2⟩
    · exact wit 1 4 ((hcm _).2 (by omega)) ((hcm _).2 (by omega)) (by omega) (by omega)
    · exact wit (n - 3) n ((hcm _).2 (by omega)) ((hcm _).2 (by omega)) (by omega) (by omega)
    rcases (by omega : (t % 2 = 0 ∧ t ≤ n + 1 ∧ t ≠ n - 1) ∨ t = n - 1 ∨
        (t % 2 = 0 ∧ n + 5 ≤ t) ∨ t = n + 3 ∨
        (t % 2 = 1 ∧ t ≤ n + 4 ∧ t ≠ n + 2) ∨ t = n + 2 ∨ (t % 2 = 1 ∧ n + 6 ≤ t))
      with h | h | h | h | h | h | h
    · exact wit 1 (t - 1) ((hcm _).2 (by omega)) ((hcm _).2 (by omega)) (by omega) (by omega)
    · exact wit 5 (n - 6) ((hcm _).2 (by omega)) ((hcm _).2 (by omega)) (by omega) (by omega)
    · exact wit (t - n) n ((hcm _).2 (by omega)) ((hcm _).2 (by omega)) (by omega) (by omega)
    · exact wit 7 (n - 4) ((hcm _).2 (by omega)) ((hcm _).2 (by omega)) (by omega) (by omega)
    · exact wit 4 (t - 4) ((hcm _).2 (by omega)) ((hcm _).2 (by omega)) (by omega) (by omega)
    · exact wit 5 (n - 3) ((hcm _).2 (by omega)) ((hcm _).2 (by omega)) (by omega) (by omega)
    · exact wit (t - n + 3) (n - 3) ((hcm _).2 (by omega)) ((hcm _).2 (by omega)) (by omega)
        (by omega)

end OMA.A039799Proof

open OMA.S_oeis_a039799 OMA.A039799Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a039799.main := by
  intro n hn
  refine ⟨?_, ?_⟩
  · rcases Nat.mod_two_eq_zero_or_one n with hp | hp
    · refine ⟨sE n, Finset.filter_subset _ _, ?_⟩
      show (pairSums (sE n) ∩ pairSums (Finset.Icc 1 n \ sE n)).card = 2 * n - 11
      apply le_antisymm (upper n hn _ (Finset.filter_subset _ _))
      have h := Finset.card_le_card (even_case n hn hp)
      have hD : (insert 5 (Finset.Icc 8 (2 * n - 5))).card = 2 * n - 11 := by
        rw [Finset.card_insert_of_notMem (by rw [Finset.mem_Icc]; omega), Nat.card_Icc]
        omega
      rw [hD] at h
      exact h
    · refine ⟨sO n, Finset.filter_subset _ _, ?_⟩
      show (pairSums (sO n) ∩ pairSums (Finset.Icc 1 n \ sO n)).card = 2 * n - 11
      apply le_antisymm (upper n hn _ (Finset.filter_subset _ _))
      have h := Finset.card_le_card (odd_case n hn hp)
      have hD : (insert 5 (insert (2 * n - 3) (Finset.Icc 8 (2 * n - 6)))).card = 2 * n - 11 := by
        rw [Finset.card_insert_of_notMem (by rw [Finset.mem_insert, Finset.mem_Icc]; omega),
          Finset.card_insert_of_notMem (by rw [Finset.mem_Icc]; omega), Nat.card_Icc]
        omega
      rw [hD] at h
      exact h
  · rintro m ⟨s, hs, rfl⟩
    exact upper n hn s hs
