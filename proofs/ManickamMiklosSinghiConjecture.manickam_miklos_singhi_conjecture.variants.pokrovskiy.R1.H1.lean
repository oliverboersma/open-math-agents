import OMAReductions.R_ManickamMiklosSinghiConjecture_manickam_miklos_singhi_conjecture_variants_pokrovskiy_R1
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.EquivFin

/-! The large-n case is exactly the quadratic bound from the merged
Manickam–Miklós–Singhi proof by @drobison00 (PR 3213). -/

open Finset
open ManickamMiklosSinghiConjecture

namespace OMA.MMSQuadratic

private def bsum {n : ℕ} (x : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, x i

private lemma nonnegSubsetCount_comp_perm {n k : ℕ} (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    nonnegSubsetCount n k (x ∘ σ) = nonnegSubsetCount n k x := by
  unfold nonnegSubsetCount
  refine Finset.card_bij (fun S _ => S.map σ.toEmbedding) ?_ ?_ ?_
  · intro S hS
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at hS ⊢
    refine ⟨by simp [hS.1], ?_⟩
    rw [Finset.sum_map]
    simpa [Function.comp_apply] using hS.2
  · intro S₁ _ S₂ _ h
    exact Finset.map_injective σ.toEmbedding h
  · intro T hT
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at hT
    refine ⟨T.map σ.symm.toEmbedding, ?_, ?_⟩
    · simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
      refine ⟨by simp [hT.1], ?_⟩
      rw [Finset.sum_map]
      have hsum : ∑ i ∈ T, (x ∘ σ) (σ.symm.toEmbedding i) = ∑ i ∈ T, x i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp
      rw [hsum]
      exact hT.2
    · ext i
      simp

private lemma exists_antitone_perm {n : ℕ} (x : Fin n → ℝ) :
    ∃ σ : Equiv.Perm (Fin n), Antitone (x ∘ σ) := by
  let f : Fin n → OrderDual ℝ := fun i => OrderDual.toDual (x i)
  refine ⟨Tuple.sort f, ?_⟩
  intro i j hij
  exact Tuple.monotone_sort f hij

private lemma orderEmb_ge_id {n k : ℕ} {S : Finset (Fin n)} (hS : S.card = k) (j : Fin k) :
    j.val ≤ (S.orderEmbOfFin hS j).val := by
  rcases j with ⟨m, hm⟩
  induction m with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    have hm' : m < k := Nat.lt_of_succ_lt hm
    have hlt : S.orderEmbOfFin hS ⟨m, hm'⟩ < S.orderEmbOfFin hS ⟨m + 1, hm⟩ :=
      (S.orderEmbOfFin hS).strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self m))
    have ih' := ih hm'
    change m ≤ (S.orderEmbOfFin hS ⟨m, hm'⟩).val at ih'
    have hval : (S.orderEmbOfFin hS ⟨m, hm'⟩).val < (S.orderEmbOfFin hS ⟨m + 1, hm⟩).val := hlt
    change m + 1 ≤ (S.orderEmbOfFin hS ⟨m + 1, hm⟩).val
    omega

private lemma bsum_le_A {n k : ℕ} {x : Fin n → ℝ} (hx : Antitone x)
    (A : Finset (Fin n)) (hA_def : ∀ hn : k ≤ n, A = (Finset.univ : Finset (Fin k)).map
      ⟨fun j : Fin k => ⟨j.val, by omega⟩, fun a b h => Fin.ext (Fin.mk.inj h)⟩)
    (hn : k ≤ n) {S : Finset (Fin n)} (hS : S.card = k) :
    bsum x S ≤ bsum x A := by
  let e := S.orderEmbOfFin hS
  have hSmap : S = (Finset.univ : Finset (Fin k)).map e.toEmbedding :=
    (S.map_orderEmbOfFin_univ hS).symm
  rw [bsum, hSmap, Finset.sum_map, bsum, hA_def hn, Finset.sum_map]
  refine Finset.sum_le_sum fun j _ => ?_
  apply hx
  change j.val ≤ (e j).val
  exact orderEmb_ge_id hS j

private lemma bsum_le_C {n k : ℕ} (hk : 2 ≤ k) (hn : 2 * k - 1 ≤ n) {x : Fin n → ℝ}
    (hx : Antitone x) (A C : Finset (Fin n))
    (hA_mem : ∀ v : Fin n, v ∈ A ↔ v.val < k)
    (gC : Fin k → Fin n)
    (hgC : ∀ j : Fin k, gC j = if j.val = 0 then ⟨0, by omega⟩ else ⟨k - 1 + j.val, by omega⟩)
    (hgC_inj : Function.Injective gC)
    (hC_def : C = (Finset.univ : Finset (Fin k)).map ⟨gC, hgC_inj⟩)
    {S : Finset (Fin n)} (hS : S.card = k) (hSA : (S ∩ A).card = 1) :
    bsum x S ≤ bsum x C := by
  let e := S.orderEmbOfFin hS
  have hSmap : S = (Finset.univ : Finset (Fin k)).map e.toEmbedding :=
    (S.map_orderEmbOfFin_univ hS).symm
  have he_mem : ∀ j : Fin k, e j ∈ S := fun j => S.orderEmbOfFin_mem hS j
  have h0A : e ⟨0, by omega⟩ ∈ A := by
    by_contra hnot
    have hge : k ≤ (e ⟨0, by omega⟩).val := by
      have := (hA_mem (e ⟨0, by omega⟩)).not.mp hnot
      omega
    have hempty : S ∩ A = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro v hv
      obtain ⟨hvS, hvA⟩ := Finset.mem_inter.mp hv
      rw [hSmap] at hvS
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hvS
      have h0j : e ⟨0, by omega⟩ ≤ e j := e.monotone (Nat.zero_le j.val)
      have hvlt := (hA_mem (e j)).mp hvA
      have : (e ⟨0, by omega⟩).val ≤ (e j).val := h0j
      omega
    rw [hempty] at hSA
    simp at hSA
  have hnotA : ∀ j : Fin k, 1 ≤ j.val → e j ∉ A := by
    intro j hj hmem
    have h0in : e ⟨0, by omega⟩ ∈ S ∩ A := Finset.mem_inter.mpr ⟨he_mem _, h0A⟩
    have hjin : e j ∈ S ∩ A := Finset.mem_inter.mpr ⟨he_mem _, hmem⟩
    have heq : e ⟨0, by omega⟩ = e j := Finset.card_le_one.mp hSA.le _ h0in _ hjin
    have : (⟨0, by omega⟩ : Fin k) = j := e.injective heq
    have : (0 : ℕ) = j.val := congrArg Fin.val this
    omega
  have hge_gC : ∀ j : Fin k, (gC j).val ≤ (e j).val := by
    intro j
    rw [hgC j]
    split_ifs with h0
    · exact Nat.zero_le _
    · rcases j with ⟨m, hm⟩
      dsimp only at h0 ⊢
      have hm1 : 1 ≤ m := Nat.pos_of_ne_zero h0
      induction m with
      | zero => omega
      | succ m ih =>
        by_cases hm0 : m = 0
        · subst hm0
          have hk1 : e ⟨1, hm⟩ ∉ A := hnotA ⟨1, hm⟩ (by omega)
          have := (hA_mem (e ⟨1, hm⟩)).not.mp hk1
          change k - 1 + 1 ≤ (e ⟨1, hm⟩).val
          omega
        · have hm' : m < k := Nat.lt_of_succ_lt hm
          have ih' := ih hm' hm0 (by omega)
          have hlt : e ⟨m, hm'⟩ < e ⟨m + 1, hm⟩ :=
            e.strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self m))
          have hval : (e ⟨m, hm'⟩).val < (e ⟨m + 1, hm⟩).val := hlt
          omega
  rw [bsum, hSmap, Finset.sum_map, bsum, hC_def, Finset.sum_map]
  refine Finset.sum_le_sum fun j _ => ?_
  apply hx
  exact hge_gC j

private lemma sum_powersetCard_bsum {n k : ℕ} (hk : 1 ≤ k) (_hn : k ≤ n) (x : Fin n → ℝ) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, bsum x S =
      ((n - 1).choose (k - 1) : ℝ) * ∑ i, x i := by
  let F := (Finset.univ : Finset (Fin n)).powersetCard k
  have h1 : ∑ S ∈ F, bsum x S =
      ∑ i : Fin n, ((F.filter (fun S => i ∈ S)).card : ℝ) * x i := by
    simp only [bsum]
    calc ∑ S ∈ F, ∑ i ∈ S, x i
      _ = ∑ S ∈ F, ∑ i : Fin n, (if i ∈ S then x i else 0) := by
          refine Finset.sum_congr rfl fun S _ => ?_
          simp [Finset.sum_ite_mem, Finset.univ_inter]
      _ = ∑ i : Fin n, ∑ S ∈ F, (if i ∈ S then x i else 0) := Finset.sum_comm
      _ = ∑ i : Fin n, ((F.filter (fun S => i ∈ S)).card : ℝ) * x i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [h1]
  have hcard : ∀ i : Fin n, (F.filter (fun S => i ∈ S)).card = (n - 1).choose (k - 1) := by
    intro i
    have hbij : (F.filter (fun S => i ∈ S)).card =
        ((Finset.univ.erase i).powersetCard (k - 1)).card := by
      refine Finset.card_bij (fun S _ => S.erase i) ?_ ?_ ?_
      · intro S hS
        simp only [F, mem_filter, mem_powersetCard, subset_univ, true_and] at hS ⊢
        exact ⟨fun y hy => Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hy).1, Finset.mem_univ _⟩,
          by rw [Finset.card_erase_of_mem hS.2, hS.1]⟩
      · intro S₁ h₁ S₂ h₂ heq
        simp only [mem_filter] at h₁ h₂
        have : insert i (S₁.erase i) = insert i (S₂.erase i) := congrArg (insert i) heq
        simpa [Finset.insert_erase h₁.2, Finset.insert_erase h₂.2] using this
      · intro T hT
        simp only [mem_powersetCard, subset_erase] at hT
        refine ⟨insert i T, ?_, Finset.erase_insert hT.1.2⟩
        simp only [F, mem_filter, mem_powersetCard, subset_univ, true_and, mem_insert,
          true_or, and_true]
        rw [Finset.card_insert_of_notMem hT.1.2, hT.2]
        omega
    rw [hbij, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
  simp_rw [hcard, ← Finset.mul_sum]

private lemma sum_disjoint_bsum {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n) (x : Fin n → ℝ)
    (hx0 : ∑ i, x i = 0) {U : Finset (Fin n)} (hU : U.card = k) :
    ∑ S ∈ ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => Disjoint S U),
        bsum x S =
      - ((n - k - 1).choose (k - 1) : ℝ) * bsum x U := by
  let F := ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => Disjoint S U)
  have h1 : ∑ S ∈ F, bsum x S =
      ∑ i : Fin n, ((F.filter (fun S => i ∈ S)).card : ℝ) * x i := by
    simp only [bsum]
    calc ∑ S ∈ F, ∑ i ∈ S, x i
      _ = ∑ S ∈ F, ∑ i : Fin n, (if i ∈ S then x i else 0) := by
          refine Finset.sum_congr rfl fun S _ => ?_
          simp [Finset.sum_ite_mem, Finset.univ_inter]
      _ = ∑ i : Fin n, ∑ S ∈ F, (if i ∈ S then x i else 0) := Finset.sum_comm
      _ = ∑ i : Fin n, ((F.filter (fun S => i ∈ S)).card : ℝ) * x i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [h1]
  have hcard : ∀ i : Fin n, (F.filter (fun S => i ∈ S)).card =
      if i ∈ U then 0 else (n - k - 1).choose (k - 1) := by
    intro i
    split_ifs with hiU
    · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro S hS
      simp only [F, mem_filter] at hS
      exact Finset.disjoint_left.mp hS.1.2 hS.2 hiU
    · have hbij : (F.filter (fun S => i ∈ S)).card =
          (((Finset.univ \ U).erase i).powersetCard (k - 1)).card := by
        refine Finset.card_bij (fun S _ => S.erase i) ?_ ?_ ?_
        · intro S hS
          simp only [F, mem_filter, mem_powersetCard, subset_univ, true_and] at hS
          simp only [mem_powersetCard]
          refine ⟨?_, by rw [Finset.card_erase_of_mem hS.2, hS.1.1]⟩
          intro y hy
          rw [Finset.mem_erase, Finset.mem_sdiff]
          obtain ⟨hne, hyS⟩ := Finset.mem_erase.mp hy
          exact ⟨hne, Finset.mem_univ _, Finset.disjoint_left.mp hS.1.2 hyS⟩
        · intro S₁ h₁ S₂ h₂ heq
          simp only [mem_filter] at h₁ h₂
          have : insert i (S₁.erase i) = insert i (S₂.erase i) := congrArg (insert i) heq
          simpa [Finset.insert_erase h₁.2, Finset.insert_erase h₂.2] using this
        · intro T hT
          simp only [mem_powersetCard, subset_erase] at hT
          refine ⟨insert i T, ?_, Finset.erase_insert hT.1.2⟩
          simp only [F, mem_filter, mem_powersetCard, subset_univ, true_and, mem_insert,
            true_or, and_true]
          refine ⟨?_, ?_⟩
          · rw [Finset.card_insert_of_notMem hT.1.2, hT.2]; omega
          · rw [Finset.disjoint_insert_left]
            refine ⟨hiU, Finset.disjoint_left.mpr fun y hy => ?_⟩
            have hy' := hT.1.1 hy
            exact (Finset.mem_sdiff.mp hy').2
      rw [hbij, Finset.card_powersetCard,
        Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiU⟩),
        Finset.card_sdiff_of_subset (Finset.subset_univ U), Finset.card_univ, Fintype.card_fin, hU]
  simp_rw [hcard]
  have hsplit : ∑ i : Fin n, ((if i ∈ U then 0 else (n - k - 1).choose (k - 1) : ℕ) : ℝ) * x i =
      ((n - k - 1).choose (k - 1) : ℝ) * ∑ i ∈ Finset.univ \ U, x i := by
    rw [Finset.mul_sum, ← Finset.sum_sdiff (Finset.subset_univ U)]
    have hU0 : ∑ i ∈ U, ((if i ∈ U then 0 else (n - k - 1).choose (k - 1) : ℕ) : ℝ) * x i = 0 :=
      Finset.sum_eq_zero fun i hi => by simp [hi]
    rw [hU0, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiU : i ∉ U := (Finset.mem_sdiff.mp hi).2
    simp [hiU]
  rw [hsplit]
  have hcomp : ∑ i ∈ Finset.univ \ U, x i = - bsum x U := by
    have := Finset.sum_sdiff (Finset.subset_univ U) (f := x)
    rw [hx0] at this
    change (∑ i ∈ Finset.univ \ U, x i) + bsum x U = 0 at this
    linarith
  rw [hcomp]
  ring

private lemma sum_nondisjoint_bsum {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n) (x : Fin n → ℝ)
    (hx0 : ∑ i, x i = 0) {U : Finset (Fin n)} (hU : U.card = k) :
    ∑ S ∈ ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => ¬ Disjoint S U),
        bsum x S =
      ((n - k - 1).choose (k - 1) : ℝ) * bsum x U := by
  have htot := sum_powersetCard_bsum hk (by omega) x
  rw [hx0, mul_zero] at htot
  have hpart := Finset.sum_filter_add_sum_filter_not
    ((Finset.univ : Finset (Fin n)).powersetCard k) (fun S => Disjoint S U) (bsum x)
  rw [htot, sum_disjoint_bsum hk hn x hx0 hU] at hpart
  linarith

private lemma sum_inter_card_one_bsum {n k : ℕ} (hk : 2 ≤ k) (hn : 2 * k ≤ n) (x : Fin n → ℝ)
    (hx0 : ∑ i, x i = 0) {A : Finset (Fin n)} (hA : A.card = k) :
    ∑ S ∈ ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => (S ∩ A).card = 1),
        bsum x S =
      (((n - k - 1).choose (k - 1) : ℝ) - ((k - 1 : ℕ) : ℝ) * ((n - k - 1).choose (k - 2) : ℝ)) *
        bsum x A := by
  let F := ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => (S ∩ A).card = 1)
  have h1 : ∑ S ∈ F, bsum x S =
      ∑ i : Fin n, ((F.filter (fun S => i ∈ S)).card : ℝ) * x i := by
    simp only [bsum]
    calc ∑ S ∈ F, ∑ i ∈ S, x i
      _ = ∑ S ∈ F, ∑ i : Fin n, (if i ∈ S then x i else 0) := by
          refine Finset.sum_congr rfl fun S _ => ?_
          simp [Finset.sum_ite_mem, Finset.univ_inter]
      _ = ∑ i : Fin n, ∑ S ∈ F, (if i ∈ S then x i else 0) := Finset.sum_comm
      _ = ∑ i : Fin n, ((F.filter (fun S => i ∈ S)).card : ℝ) * x i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [h1]
  have hcardA : ∀ i ∈ A, (F.filter (fun S => i ∈ S)).card = (n - k).choose (k - 1) := by
    intro i hiA
    have hbij : (F.filter (fun S => i ∈ S)).card =
        ((Finset.univ \ A).powersetCard (k - 1)).card := by
      refine Finset.card_bij (fun S _ => S.erase i) ?_ ?_ ?_
      · intro S hS
        simp only [F, mem_filter, mem_powersetCard, subset_univ, true_and] at hS
        simp only [mem_powersetCard]
        refine ⟨?_, by rw [Finset.card_erase_of_mem hS.2, hS.1.1]⟩
        intro y hy
        obtain ⟨hyne, hyS⟩ := Finset.mem_erase.mp hy
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_univ _, fun hyA => ?_⟩
        have hyi : y = i := Finset.card_le_one.mp hS.1.2.le y
          (Finset.mem_inter.mpr ⟨hyS, hyA⟩) i (Finset.mem_inter.mpr ⟨hS.2, hiA⟩)
        exact hyne hyi
      · intro S₁ h₁ S₂ h₂ heq
        simp only [mem_filter] at h₁ h₂
        have : insert i (S₁.erase i) = insert i (S₂.erase i) := congrArg (insert i) heq
        simpa [Finset.insert_erase h₁.2, Finset.insert_erase h₂.2] using this
      · intro T hT
        simp only [mem_powersetCard] at hT
        have hiT : i ∉ T := fun h => (Finset.mem_sdiff.mp (hT.1 h)).2 hiA
        refine ⟨insert i T, ?_, Finset.erase_insert hiT⟩
        simp only [F, mem_filter, mem_powersetCard, subset_univ, true_and, mem_insert,
          true_or, and_true]
        refine ⟨by rw [Finset.card_insert_of_notMem hiT, hT.2]; omega, ?_⟩
        have hinter : insert i T ∩ A = {i} := by
          ext y
          simp only [mem_inter, mem_insert, mem_singleton]
          constructor
          · rintro ⟨rfl | hyT, hyA⟩
            · rfl
            · exact absurd hyA (Finset.mem_sdiff.mp (hT.1 hyT)).2
          · rintro rfl; exact ⟨Or.inl rfl, hiA⟩
        rw [hinter, Finset.card_singleton]
    rw [hbij, Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ A),
      Finset.card_univ, Fintype.card_fin, hA]
  have hcardNA : ∀ i ∉ A, (F.filter (fun S => i ∈ S)).card = k * (n - k - 1).choose (k - 2) := by
    intro i hiA
    have hbij : (A ×ˢ ((Finset.univ \ A).erase i).powersetCard (k - 2)).card =
        (F.filter (fun S => i ∈ S)).card := by
      refine Finset.card_bij (fun p _ => insert p.1 (insert i p.2)) ?_ ?_ ?_
      · intro p hp
        obtain ⟨hpA, hp2⟩ := Finset.mem_product.mp hp
        simp only [mem_powersetCard, subset_erase] at hp2
        have hip2 : i ∉ p.2 := hp2.1.2
        have hp1notin : p.1 ∉ insert i p.2 := by
          simp only [mem_insert, not_or]
          refine ⟨fun h => hiA (h ▸ hpA), fun h => ?_⟩
          exact (Finset.mem_sdiff.mp (hp2.1.1 h)).2 hpA
        have hinter : insert p.1 (insert i p.2) ∩ A = {p.1} := by
          ext y
          simp only [mem_inter, mem_insert, mem_singleton]
          constructor
          · rintro ⟨rfl | rfl | hy2, hyA⟩
            · rfl
            · exact absurd hyA hiA
            · exact absurd hyA (Finset.mem_sdiff.mp (hp2.1.1 hy2)).2
          · rintro rfl; exact ⟨Or.inl rfl, hpA⟩
        simp only [F, mem_filter, mem_powersetCard, subset_univ, true_and, mem_insert,
          true_or, or_true, and_true]
        refine ⟨?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hp1notin, Finset.card_insert_of_notMem hip2, hp2.2]
          omega
        · rw [hinter, Finset.card_singleton]
      · intro p₁ hp₁ p₂ hp₂ heq
        obtain ⟨hp₁A, hp₁2⟩ := Finset.mem_product.mp hp₁
        obtain ⟨hp₂A, hp₂2⟩ := Finset.mem_product.mp hp₂
        simp only [mem_powersetCard, subset_erase] at hp₁2 hp₂2
        have hinter1 : insert p₁.1 (insert i p₁.2) ∩ A = {p₁.1} := by
          ext y
          simp only [mem_inter, mem_insert, mem_singleton]
          constructor
          · rintro ⟨rfl | rfl | hy2, hyA⟩
            · rfl
            · exact absurd hyA hiA
            · exact absurd hyA (Finset.mem_sdiff.mp (hp₁2.1.1 hy2)).2
          · rintro rfl; exact ⟨Or.inl rfl, hp₁A⟩
        have hinter2 : insert p₂.1 (insert i p₂.2) ∩ A = {p₂.1} := by
          ext y
          simp only [mem_inter, mem_insert, mem_singleton]
          constructor
          · rintro ⟨rfl | rfl | hy2, hyA⟩
            · rfl
            · exact absurd hyA hiA
            · exact absurd hyA (Finset.mem_sdiff.mp (hp₂2.1.1 hy2)).2
          · rintro rfl; exact ⟨Or.inl rfl, hp₂A⟩
        have ha : p₁.1 = p₂.1 := by
          have := congrArg (· ∩ A) heq
          rw [hinter1, hinter2] at this
          exact Finset.singleton_injective this
        have hip₁ : p₁.1 ∉ insert i p₁.2 := by
          simp only [mem_insert, not_or]
          exact ⟨fun h => hiA (h ▸ hp₁A), fun h => (Finset.mem_sdiff.mp (hp₁2.1.1 h)).2 hp₁A⟩
        have hip₂ : p₂.1 ∉ insert i p₂.2 := by
          simp only [mem_insert, not_or]
          exact ⟨fun h => hiA (h ▸ hp₂A), fun h => (Finset.mem_sdiff.mp (hp₂2.1.1 h)).2 hp₂A⟩
        have heq2 : insert i p₁.2 = insert i p₂.2 := by
          have := congrArg (fun T => T.erase p₁.1) heq
          rw [Finset.erase_insert hip₁, ha, Finset.erase_insert hip₂] at this
          exact this
        have hp2eq : p₁.2 = p₂.2 := by
          have := congrArg (fun T => T.erase i) heq2
          rw [Finset.erase_insert hp₁2.1.2, Finset.erase_insert hp₂2.1.2] at this
          exact this
        exact Prod.ext ha hp2eq
      · intro S hS
        simp only [F, mem_filter, mem_powersetCard, subset_univ, true_and] at hS
        obtain ⟨a, ha_eq⟩ := Finset.card_eq_one.mp hS.1.2
        have ha_mem : a ∈ S ∩ A := by rw [ha_eq]; exact Finset.mem_singleton_self a
        have haS : a ∈ S := (Finset.mem_inter.mp ha_mem).1
        have haA : a ∈ A := (Finset.mem_inter.mp ha_mem).2
        have hane : a ≠ i := fun h => hiA (h ▸ haA)
        refine ⟨(a, (S.erase a).erase i), ?_, ?_⟩
        · simp only [mem_product, mem_powersetCard, subset_erase]
          refine ⟨haA, ⟨⟨?_, Finset.notMem_erase _ _⟩, ?_⟩⟩
          · intro y hy
            obtain ⟨hyi, hya⟩ := Finset.mem_erase.mp hy
            obtain ⟨hyne, hyS⟩ := Finset.mem_erase.mp hya
            rw [Finset.mem_sdiff]
            refine ⟨Finset.mem_univ _, fun hyA => ?_⟩
            have : y ∈ ({a} : Finset (Fin n)) := ha_eq ▸ Finset.mem_inter.mpr ⟨hyS, hyA⟩
            exact hyne (Finset.mem_singleton.mp this)
          · rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hane.symm, hS.2⟩),
              Finset.card_erase_of_mem haS, hS.1.1]
            omega
        · rw [Finset.insert_erase (Finset.mem_erase.mpr ⟨hane.symm, hS.2⟩),
            Finset.insert_erase haS]
    rw [← hbij, Finset.card_product, hA, Finset.card_powersetCard,
      Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiA⟩),
      Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ, Fintype.card_fin, hA]
  have hsplit : ∑ i : Fin n, ((F.filter (fun S => i ∈ S)).card : ℝ) * x i =
      (((n - k).choose (k - 1) : ℝ) - (k : ℝ) * ((n - k - 1).choose (k - 2) : ℝ)) * bsum x A := by
    rw [← Finset.sum_sdiff (Finset.subset_univ A)]
    have hA_sum : ∑ i ∈ A, ((F.filter (fun S => i ∈ S)).card : ℝ) * x i =
        ((n - k).choose (k - 1) : ℝ) * bsum x A := by
      rw [bsum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => by rw [hcardA i hi]
    have hNA_sum : ∑ i ∈ Finset.univ \ A, ((F.filter (fun S => i ∈ S)).card : ℝ) * x i =
        ((k : ℝ) * ((n - k - 1).choose (k - 2) : ℝ)) * ∑ i ∈ Finset.univ \ A, x i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiA : i ∉ A := (Finset.mem_sdiff.mp hi).2
      rw [hcardNA i hiA]
      push_cast
      rfl
    have hcomp : ∑ i ∈ Finset.univ \ A, x i = - bsum x A := by
      have := Finset.sum_sdiff (Finset.subset_univ A) (f := x)
      rw [hx0] at this
      change (∑ i ∈ Finset.univ \ A, x i) + bsum x A = 0 at this
      linarith
    rw [hNA_sum, hA_sum, hcomp]
    ring
  rw [hsplit]
  have hpascal : (n - k).choose (k - 1) = (n - k - 1).choose (k - 1) + (n - k - 1).choose (k - 2) := by
    have h := Nat.choose_succ_succ (n - k - 1) (k - 2)
    have h1 : n - k - 1 + 1 = n - k := by omega
    have h2 : k - 2 + 1 = k - 1 := by omega
    simp only [Nat.succ_eq_add_one] at h
    rw [h1, h2] at h
    omega
  have hpascalR : ((n - k).choose (k - 1) : ℝ) =
      ((n - k - 1).choose (k - 1) : ℝ) + ((n - k - 1).choose (k - 2) : ℝ) := by
    exact_mod_cast hpascal
  have hkR : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
    have : k = (k - 1) + 1 := by omega
    exact_mod_cast this
  rw [hpascalR, hkR]
  ring

private lemma choose_sub_ge {n k d : ℕ} (hk : 2 ≤ k) (hnd : d ≤ n - k) (hn : 2 * k ≤ n) :
    (1 - ((d : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
        ((n - 1).choose (k - 1) : ℝ) ≤
      ((n - 1 - d).choose (k - 1) : ℝ) := by
  set m := k - 1
  have hdenom_pos : (0 : ℝ) < ((n - 2 * k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - 2 * k + 1 by omega)
  have hnk1_pos : (0 : ℝ) < ((n - k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - k + 1 by omega)
  have hch_pos : (0 : ℝ) < ((n - 1).choose m : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : m ≤ n - 1)
  have hratio : ((n - 1 - d).choose m : ℝ) / ((n - 1).choose m : ℝ) =
      ∏ i ∈ Finset.range m, (((n - 1 - d - i : ℕ) : ℝ) / ((n - 1 - i : ℕ) : ℝ)) := by
    have hfac : ((Nat.factorial m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    have h1 : ((n - 1 - d).choose m : ℝ) * ((Nat.factorial m : ℕ) : ℝ) = ((n - 1 - d).descFactorial m : ℝ) := by
      exact_mod_cast (Nat.mul_comm _ _ ▸ Nat.descFactorial_eq_factorial_mul_choose (n - 1 - d) m).symm
    have h2 : ((n - 1).choose m : ℝ) * ((Nat.factorial m : ℕ) : ℝ) = ((n - 1).descFactorial m : ℝ) := by
      exact_mod_cast (Nat.mul_comm _ _ ▸ Nat.descFactorial_eq_factorial_mul_choose (n - 1) m).symm
    have hdesc1 : ((n - 1 - d).descFactorial m : ℝ) =
        ∏ i ∈ Finset.range m, ((n - 1 - d - i : ℕ) : ℝ) := by
      rw [Nat.descFactorial_eq_prod_range]
      push_cast
      rfl
    have hdesc2 : ((n - 1).descFactorial m : ℝ) =
        ∏ i ∈ Finset.range m, ((n - 1 - i : ℕ) : ℝ) := by
      rw [Nat.descFactorial_eq_prod_range]
      push_cast
      rfl
    rw [← mul_div_mul_right _ _ hfac, h1, h2, hdesc1, hdesc2, ← Finset.prod_div_distrib]
  have hterm : ∀ i ∈ Finset.range m,
      (1 - (d : ℝ) / ((n - k + 1 : ℕ) : ℝ)) ≤
        ((n - 1 - d - i : ℕ) : ℝ) / ((n - 1 - i : ℕ) : ℝ) := by
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    have hni_ge : n - k + 1 ≤ n - 1 - i := by omega
    have hni_pos : (0 : ℝ) < ((n - 1 - i : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < n - 1 - i by omega)
    have hnum_eq : ((n - 1 - d - i : ℕ) : ℝ) = ((n - 1 - i : ℕ) : ℝ) - (d : ℝ) := by
      have : n - 1 - d - i + d = n - 1 - i := by omega
      have hcast : ((n - 1 - d - i : ℕ) : ℝ) + (d : ℝ) = ((n - 1 - i : ℕ) : ℝ) := by
        exact_mod_cast this
      linarith
    rw [hnum_eq, sub_div, div_self hni_pos.ne']
    have hleR : ((n - k + 1 : ℕ) : ℝ) ≤ ((n - 1 - i : ℕ) : ℝ) := by exact_mod_cast hni_ge
    have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have := div_le_div_of_nonneg_left hd_nonneg hnk1_pos hleR
    linarith
  have hbase_nonneg : 0 ≤ 1 - (d : ℝ) / ((n - k + 1 : ℕ) : ℝ) := by
    have hdle : (d : ℝ) ≤ ((n - k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : d ≤ n - k + 1)
    rw [sub_nonneg, div_le_one hnk1_pos]
    exact hdle
  have hprod : (1 - (d : ℝ) / ((n - k + 1 : ℕ) : ℝ)) ^ m ≤
      ((n - 1 - d).choose m : ℝ) / ((n - 1).choose m : ℝ) := by
    rw [hratio]
    calc (1 - (d : ℝ) / ((n - k + 1 : ℕ) : ℝ)) ^ m
      _ = ∏ _i ∈ Finset.range m, (1 - (d : ℝ) / ((n - k + 1 : ℕ) : ℝ)) := by
          rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ i ∈ Finset.range m, (((n - 1 - d - i : ℕ) : ℝ) / ((n - 1 - i : ℕ) : ℝ)) := by
          refine Finset.prod_le_prod (fun _ _ => hbase_nonneg) hterm
  have hbern : 1 - (m : ℝ) * ((d : ℝ) / ((n - k + 1 : ℕ) : ℝ)) ≤
      (1 - (d : ℝ) / ((n - k + 1 : ℕ) : ℝ)) ^ m := by
    have ha : -2 ≤ -((d : ℝ) / ((n - k + 1 : ℕ) : ℝ)) := by linarith
    have := one_add_mul_le_pow ha m
    simpa [sub_eq_add_neg, mul_neg] using this
  have hmono : 1 - ((d : ℝ) * (m : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) ≤
      1 - (m : ℝ) * ((d : ℝ) / ((n - k + 1 : ℕ) : ℝ)) := by
    have hle_den : ((n - 2 * k + 1 : ℕ) : ℝ) ≤ ((n - k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : n - 2 * k + 1 ≤ n - k + 1)
    have hdm_nonneg : 0 ≤ (d : ℝ) * (m : ℝ) := by positivity
    have hdiv := div_le_div_of_nonneg_left hdm_nonneg hdenom_pos hle_den
    linarith [show (m : ℝ) * ((d : ℝ) / ((n - k + 1 : ℕ) : ℝ)) =
      ((d : ℝ) * (m : ℝ)) / ((n - k + 1 : ℕ) : ℝ) by ring]
  have hcomb : 1 - ((d : ℝ) * (m : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) ≤
      ((n - 1 - d).choose m : ℝ) / ((n - 1).choose m : ℝ) :=
    le_trans hmono (le_trans hbern hprod)
  have hmul := mul_le_mul_of_nonneg_right hcomb hch_pos.le
  rw [div_mul_cancel₀ _ hch_pos.ne'] at hmul
  exact hmul

private lemma bsum_C_ge {n k : ℕ} (hk : 2 ≤ k) (hn : 4 * k ^ 2 ≤ n) (x : Fin n → ℝ)
    (hx0 : ∑ i, x i = 0)
    (A C : Finset (Fin n)) (hA : A.card = k) (hC : C.card = k) (hCA : (C ∩ A).card = 1)
    (hbA : 0 < bsum x A)
    (hmaxC : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (S ∩ A).card = 1 → bsum x S ≤ bsum x C)
    (hle : nonnegSubsetCount n k x ≤ (n - 1).choose (k - 1)) :
    (1 - (((2 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) * bsum x A ≤
      bsum x C := by
  have hk2 : k ^ 2 ≤ n := by nlinarith
  have h2k : 2 * k ≤ n := by nlinarith
  have hsum1 := sum_inter_card_one_bsum hk h2k x hx0 hA
  let F1 := ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => (S ∩ A).card = 1)
  have hC_in : C ∈ F1 := by
    simp only [F1, mem_filter, mem_powersetCard, subset_univ, true_and]
    exact ⟨hC, hCA⟩
  have heq_choose : (n - 2 * k + 1) * (n - k - 1).choose (k - 2) =
      (k - 1) * (n - k - 1).choose (k - 1) := by
    have hsucc := Nat.choose_succ_right_eq (n - k - 1) (k - 2)
    have h1 : (k - 2) + 1 = k - 1 := by omega
    have h2 : (n - k - 1) - (k - 2) = n - 2 * k + 1 := by omega
    rw [h1, h2] at hsucc
    linarith
  have hpos_coef : 0 ≤ (((n - k - 1).choose (k - 1) : ℝ) -
      ((k - 1 : ℕ) : ℝ) * ((n - k - 1).choose (k - 2) : ℝ)) := by
    have hmul : (k - 1) * (n - k - 1).choose (k - 2) ≤ (n - k - 1).choose (k - 1) := by
      have hkm : (k - 1) * (k - 1) ≤ n - 2 * k + 1 := by
        have hk1le : k - 1 ≤ k := by omega
        have hkk : (k - 1) * (k - 1) ≤ k * k := Nat.mul_le_mul hk1le hk1le
        have : k * k ≤ n := by simpa [sq] using hk2
        nlinarith [Nat.sub_add_cancel h2k]
      nlinarith [Nat.zero_le ((n - k - 1).choose (k - 2))]
    have hmulR : ((k - 1 : ℕ) : ℝ) * ((n - k - 1).choose (k - 2) : ℝ) ≤
        ((n - k - 1).choose (k - 1) : ℝ) := by exact_mod_cast hmul
    linarith
  have hsum_nonneg : 0 ≤ ∑ S ∈ F1, bsum x S := by
    rw [show ∑ S ∈ F1, bsum x S =
      (((n - k - 1).choose (k - 1) : ℝ) - ((k - 1 : ℕ) : ℝ) * ((n - k - 1).choose (k - 2) : ℝ)) *
        bsum x A from hsum1]
    exact mul_nonneg hpos_coef hbA.le
  have hbC_nonneg : 0 ≤ bsum x C := by
    by_contra hlt
    push Not at hlt
    have hneg_all : ∀ S ∈ F1, bsum x S ≤ bsum x C := fun S hS => by
      simp only [F1, mem_filter] at hS
      exact hmaxC S hS.1 hS.2
    have hsum_lt : ∑ S ∈ F1, bsum x S < 0 := by
      calc ∑ S ∈ F1, bsum x S
        _ ≤ ∑ _S ∈ F1, bsum x C := Finset.sum_le_sum hneg_all
        _ = (F1.card : ℝ) * bsum x C := by rw [Finset.sum_const, nsmul_eq_mul]
        _ < 0 := by
            have hcard_pos : (0 : ℝ) < (F1.card : ℝ) := by
              exact_mod_cast Finset.card_pos.mpr ⟨C, hC_in⟩
            exact mul_neg_of_pos_of_neg hcard_pos hlt
    linarith
  have hF1_le : ∑ S ∈ F1, bsum x S ≤
      ∑ S ∈ F1.filter (fun S => 0 ≤ bsum x S), bsum x S := by
    rw [← Finset.sum_filter_add_sum_filter_not F1 (fun S => 0 ≤ bsum x S) (bsum x)]
    have hneg : ∑ S ∈ F1.filter (fun S => ¬ 0 ≤ bsum x S), bsum x S ≤ 0 :=
      Finset.sum_nonpos fun S hS => le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hS).2)
    linarith
  have hF1_ub : ∑ S ∈ F1.filter (fun S => 0 ≤ bsum x S), bsum x S ≤
      ((n - 1).choose (k - 1) : ℝ) * bsum x C := by
    have hsub : (F1.filter (fun S => 0 ≤ bsum x S)).card ≤ (n - 1).choose (k - 1) := by
      calc (F1.filter (fun S => 0 ≤ bsum x S)).card
        _ ≤ nonnegSubsetCount n k x := by
            unfold nonnegSubsetCount
            refine Finset.card_le_card fun S hS => ?_
            simp only [F1, mem_filter] at hS
            exact Finset.mem_filter.mpr ⟨hS.1.1, hS.2⟩
        _ ≤ (n - 1).choose (k - 1) := hle
    have hsum_ub : ∑ S ∈ F1.filter (fun S => 0 ≤ bsum x S), bsum x S ≤
        ∑ _S ∈ F1.filter (fun S => 0 ≤ bsum x S), bsum x C := by
      refine Finset.sum_le_sum fun S hS => ?_
      simp only [F1, mem_filter] at hS
      exact hmaxC S hS.1.1 hS.1.2
    rw [Finset.sum_const, nsmul_eq_mul] at hsum_ub
    exact le_trans hsum_ub (mul_le_mul_of_nonneg_right (by exact_mod_cast hsub) hbC_nonneg)
  have hchain : (((n - k - 1).choose (k - 1) : ℝ) -
      ((k - 1 : ℕ) : ℝ) * ((n - k - 1).choose (k - 2) : ℝ)) * bsum x A ≤
      ((n - 1).choose (k - 1) : ℝ) * bsum x C := by
    rw [← hsum1]
    exact le_trans hF1_le hF1_ub
  have hD_pos : (0 : ℝ) < ((n - 2 * k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - 2 * k + 1 by omega)
  have heqR : ((n - 2 * k + 1 : ℕ) : ℝ) * ((n - k - 1).choose (k - 2) : ℝ) =
      ((k - 1 : ℕ) : ℝ) * ((n - k - 1).choose (k - 1) : ℝ) := by
    exact_mod_cast heq_choose
  have hfrac1 : ((n - k - 1).choose (k - 2) : ℝ) =
      (((k - 1 : ℕ) : ℝ) / ((n - 2 * k + 1 : ℕ) : ℝ)) * ((n - k - 1).choose (k - 1) : ℝ) := by
    field_simp [hD_pos.ne']
    linarith
  have hcoef_eq : ((n - k - 1).choose (k - 1) : ℝ) -
      ((k - 1 : ℕ) : ℝ) * ((n - k - 1).choose (k - 2) : ℝ) =
      (1 - ((k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
        ((n - k - 1).choose (k - 1) : ℝ) := by
    rw [hfrac1]
    ring
  have hsub_k := choose_sub_ge hk (show k ≤ n - k by omega) h2k
  have hn1k : ((n - 1 - k).choose (k - 1) : ℝ) = ((n - k - 1).choose (k - 1) : ℝ) := by
    have : n - 1 - k = n - k - 1 := by omega
    rw [this]
  rw [hn1k] at hsub_k
  have h1a_nonneg : 0 ≤ 1 - ((k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) / ((n - 2 * k + 1 : ℕ) : ℝ) := by
    have hkm : ((k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) ≤ ((n - 2 * k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show (k - 1) * (k - 1) ≤ n - 2 * k + 1 by
        have hk1le : k - 1 ≤ k := by omega
        have hkk : (k - 1) * (k - 1) ≤ k * k := Nat.mul_le_mul hk1le hk1le
        have : k * k ≤ n := by simpa [sq] using hk2
        nlinarith [Nat.sub_add_cancel h2k])
    rw [sub_nonneg, div_le_one hD_pos]
    exact hkm
  have hcomb : (1 - ((k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
      (1 - ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
        ((n - 1).choose (k - 1) : ℝ) ≤
      ((n - k - 1).choose (k - 1) : ℝ) -
        ((k - 1 : ℕ) : ℝ) * ((n - k - 1).choose (k - 2) : ℝ) := by
    rw [hcoef_eq, mul_assoc]
    exact mul_le_mul_of_nonneg_left hsub_k h1a_nonneg
  have ha_nonneg : 0 ≤ ((k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) / ((n - 2 * k + 1 : ℕ) : ℝ) := by
    positivity
  have hb_nonneg : 0 ≤ ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) := by
    positivity
  have h2k1 : (((2 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) =
      ((k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) / ((n - 2 * k + 1 : ℕ) : ℝ) +
        ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) := by
    have hcast : ((2 * k - 1 : ℕ) : ℝ) = ((k - 1 : ℕ) : ℝ) + (k : ℝ) := by
      have : 2 * k - 1 = (k - 1) + k := by omega
      exact_mod_cast this
    rw [hcast]
    ring
  have hprod_ge : 1 - (((2 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) ≤
      (1 - ((k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
        (1 - ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) := by
    rw [h2k1]
    nlinarith [mul_nonneg ha_nonneg hb_nonneg]
  have hch_pos : (0 : ℝ) < ((n - 1).choose (k - 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : k - 1 ≤ n - 1)
  have hfinal := le_trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hprod_ge hch_pos.le) hbA.le)
    (le_trans (mul_le_mul_of_nonneg_right hcomb hbA.le) hchain)
  have hdiv := le_of_mul_le_mul_left (by linarith :
    ((n - 1).choose (k - 1) : ℝ) *
      ((1 - (((2 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
        bsum x A) ≤
    ((n - 1).choose (k - 1) : ℝ) * bsum x C) hch_pos
  exact hdiv

private lemma choose_diff_le {a d m : ℕ} (hm : 1 ≤ m) (hd : d ≤ a) :
    a.choose m - (a - d).choose m ≤ d * (a - 1).choose (m - 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hda : d ≤ a := by omega
    have hstep : (a - d).choose m - (a - (d + 1)).choose m = (a - (d + 1)).choose (m - 1) := by
      have h := Nat.choose_succ_succ (a - (d + 1)) (m - 1)
      have h1 : a - (d + 1) + 1 = a - d := by omega
      have h2 : m - 1 + 1 = m := by omega
      simp only [Nat.succ_eq_add_one] at h
      rw [h1, h2] at h
      omega
    have hle1 : (a - (d + 1)).choose (m - 1) ≤ (a - 1).choose (m - 1) :=
      Nat.choose_le_choose (m - 1) (by omega)
    have hle2 : (a - (d + 1)).choose m ≤ (a - d).choose m :=
      Nat.choose_le_choose m (by omega)
    have hle3 : (a - d).choose m ≤ a.choose m :=
      Nat.choose_le_choose m (by omega)
    have ih' := ih hda
    calc a.choose m - (a - (d + 1)).choose m
      _ = (a.choose m - (a - d).choose m) + ((a - d).choose m - (a - (d + 1)).choose m) := by omega
      _ = (a.choose m - (a - d).choose m) + (a - (d + 1)).choose (m - 1) := by rw [hstep]
      _ ≤ d * (a - 1).choose (m - 1) + (a - 1).choose (m - 1) := Nat.add_le_add ih' hle1
      _ = (d + 1) * (a - 1).choose (m - 1) := by ring

private lemma fac_sum_ge {n k : ℕ} (hk : 2 ≤ k) (hn : 8 * k ^ 2 ≤ n) {x : Fin n → ℝ}
    (hx0 : ∑ i, x i = 0)
    (A C : Finset (Fin n)) (hA : A.card = k) (hC : C.card = k)
    (hAC : A ∩ C = {⟨0, by nlinarith⟩})
    (hbA : 0 < bsum x A)
    (hmaxA : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, bsum x S ≤ bsum x A)
    (hmaxC : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (S ∩ A).card = 1 → bsum x S ≤ bsum x C)
    (hle : nonnegSubsetCount n k x ≤ (n - 1).choose (k - 1)) :
    (1 - (((4 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
        ((n - 1).choose (k - 1) : ℝ) * bsum x A ≤
      ∑ S ∈ (((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => ¬ Disjoint S C)).filter
        (fun S => ¬ Disjoint S A), bsum x S := by
  let z : Fin n := ⟨0, by nlinarith⟩
  have h2k : 2 * k ≤ n := by nlinarith
  have h4k2 : 4 * k ^ 2 ≤ n := by nlinarith
  have hzA : z ∈ A := by
    have : z ∈ A ∩ C := by rw [hAC]; exact Finset.mem_singleton_self z
    exact (Finset.mem_inter.mp this).1
  have hzC : z ∈ C := by
    have : z ∈ A ∩ C := by rw [hAC]; exact Finset.mem_singleton_self z
    exact (Finset.mem_inter.mp this).2
  have hCA : (C ∩ A).card = 1 := by
    rw [Finset.inter_comm, hAC, Finset.card_singleton]
  have hbC_ge := bsum_C_ge hk h4k2 x hx0 A C hA hC hCA hbA hmaxC hle
  have hC_sum := sum_nondisjoint_bsum (by omega : 1 ≤ k) h2k x hx0 hC
  have hD_pos : (0 : ℝ) < ((n - 2 * k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - 2 * k + 1 by omega)
  have hch_pos : (0 : ℝ) < ((n - 1).choose (k - 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : k - 1 ≤ n - 1)
  have hsub_k := choose_sub_ge hk (show k ≤ n - k by omega) h2k
  have hn1k : ((n - 1 - k).choose (k - 1) : ℝ) = ((n - k - 1).choose (k - 1) : ℝ) := by
    have : n - 1 - k = n - k - 1 := by omega
    rw [this]
  rw [hn1k] at hsub_k
  let FC := ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => ¬ Disjoint S C)
  let FA := ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => ¬ Disjoint S A)
  have hFA_sum := sum_nondisjoint_bsum (by omega : 1 ≤ k) h2k x hx0 hA
  have hFA_count : (n - k - 1).choose (k - 1) ≤ (FA.filter (fun S => 0 ≤ bsum x S)).card := by
    by_contra hlt
    push Not at hlt
    have hlt' : (FA.filter (fun S => 0 ≤ bsum x S)).card ≤ (n - k - 1).choose (k - 1) - 1 := by omega
    have hsum_le : ∑ S ∈ FA, bsum x S ≤ ∑ S ∈ FA.filter (fun S => 0 ≤ bsum x S), bsum x S := by
      rw [← Finset.sum_filter_add_sum_filter_not FA (fun S => 0 ≤ bsum x S) (bsum x)]
      have hneg : ∑ S ∈ FA.filter (fun S => ¬ 0 ≤ bsum x S), bsum x S ≤ 0 :=
        Finset.sum_nonpos fun S hS => le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hS).2)
      linarith
    have hub : ∑ S ∈ FA.filter (fun S => 0 ≤ bsum x S), bsum x S ≤
        ((FA.filter (fun S => 0 ≤ bsum x S)).card : ℝ) * bsum x A := by
      calc ∑ S ∈ FA.filter (fun S => 0 ≤ bsum x S), bsum x S
        _ ≤ ∑ _S ∈ FA.filter (fun S => 0 ≤ bsum x S), bsum x A :=
            Finset.sum_le_sum fun S hS => hmaxA S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
        _ = ((FA.filter (fun S => 0 ≤ bsum x S)).card : ℝ) * bsum x A := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hlt_real : ((FA.filter (fun S => 0 ≤ bsum x S)).card : ℝ) < ((n - k - 1).choose (k - 1) : ℝ) := by
      exact_mod_cast hlt
    have : ∑ S ∈ FA, bsum x S < ((n - k - 1).choose (k - 1) : ℝ) * bsum x A :=
      lt_of_le_of_lt (le_trans hsum_le hub) (mul_lt_mul_of_pos_right hlt_real hbA)
    linarith [hFA_sum]
  let DisjA := ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => Disjoint S A)
  have hDisjA_count : (DisjA.filter (fun S => 0 ≤ bsum x S)).card ≤
      (n - 1).choose (k - 1) - (n - k - 1).choose (k - 1) := by
    have hdisj_sets : Disjoint (FA.filter (fun S => 0 ≤ bsum x S)) (DisjA.filter (fun S => 0 ≤ bsum x S)) := by
      rw [Finset.disjoint_left]
      intro S h1 h2
      simp only [FA, DisjA, mem_filter] at h1 h2
      exact h1.1.2 h2.1.2
    have hunion : (FA.filter (fun S => 0 ≤ bsum x S)).card + (DisjA.filter (fun S => 0 ≤ bsum x S)).card ≤
        nonnegSubsetCount n k x := by
      rw [← Finset.card_union_of_disjoint hdisj_sets]
      unfold nonnegSubsetCount
      refine Finset.card_le_card fun S hS => ?_
      rcases Finset.mem_union.mp hS with hS | hS
      · simp only [FA, mem_filter] at hS
        exact Finset.mem_filter.mpr ⟨hS.1.1, hS.2⟩
      · simp only [DisjA, mem_filter] at hS
        exact Finset.mem_filter.mpr ⟨hS.1.1, hS.2⟩
    omega
  let FAC := FC.filter (fun S => ¬ Disjoint S A)
  let FC_disjA := FC.filter (fun S => Disjoint S A)
  have hFC_disjA_sum : ∑ S ∈ FC_disjA, bsum x S ≤
      (((n - 1).choose (k - 1) - (n - k - 1).choose (k - 1) : ℕ) : ℝ) * bsum x A := by
    have h1 : ∑ S ∈ FC_disjA, bsum x S ≤ ∑ S ∈ FC_disjA.filter (fun S => 0 ≤ bsum x S), bsum x S := by
      rw [← Finset.sum_filter_add_sum_filter_not FC_disjA (fun S => 0 ≤ bsum x S) (bsum x)]
      have hneg : ∑ S ∈ FC_disjA.filter (fun S => ¬ 0 ≤ bsum x S), bsum x S ≤ 0 :=
        Finset.sum_nonpos fun S hS => le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hS).2)
      linarith
    have hsub : (FC_disjA.filter (fun S => 0 ≤ bsum x S)).card ≤
        (n - 1).choose (k - 1) - (n - k - 1).choose (k - 1) := by
      refine le_trans (Finset.card_le_card fun S hS => ?_) hDisjA_count
      simp only [FC_disjA, FC, DisjA, mem_filter] at hS ⊢
      exact ⟨⟨hS.1.1.1, hS.1.2⟩, hS.2⟩
    have h2 : ∑ S ∈ FC_disjA.filter (fun S => 0 ≤ bsum x S), bsum x S ≤
        ((FC_disjA.filter (fun S => 0 ≤ bsum x S)).card : ℝ) * bsum x A := by
      calc ∑ S ∈ FC_disjA.filter (fun S => 0 ≤ bsum x S), bsum x S
        _ ≤ ∑ _S ∈ FC_disjA.filter (fun S => 0 ≤ bsum x S), bsum x A :=
            Finset.sum_le_sum fun S hS => by
              simp only [FC_disjA, FC, mem_filter] at hS
              exact hmaxA S hS.1.1.1
        _ = ((FC_disjA.filter (fun S => 0 ≤ bsum x S)).card : ℝ) * bsum x A := by
            rw [Finset.sum_const, nsmul_eq_mul]
    exact le_trans (le_trans h1 h2) (mul_le_mul_of_nonneg_right (by exact_mod_cast hsub) hbA.le)
  have hFAC_sum : (1 - (((4 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
      ((n - 1).choose (k - 1) : ℝ) * bsum x A ≤ ∑ S ∈ FAC, bsum x S := by
    have hsplit_FC := Finset.sum_filter_add_sum_filter_not FC (fun S => ¬ Disjoint S A) (bsum x)
    have hFC_disjA_eq : FC.filter (fun S => ¬ ¬ Disjoint S A) = FC_disjA := by
      ext S; simp [FC_disjA]
    rw [hFC_disjA_eq] at hsplit_FC
    have hFC_lb : (1 - (((3 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
        ((n - 1).choose (k - 1) : ℝ) * bsum x A ≤ ∑ S ∈ FC, bsum x S := by
      have ha_nonneg : 0 ≤ ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) := by positivity
      have hb_nonneg : 0 ≤ (((2 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) := by positivity
      have h1k_nonneg : 0 ≤ 1 - ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) := by
        have : (k : ℝ) * ((k - 1 : ℕ) : ℝ) ≤ ((n - 2 * k + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show k * (k - 1) ≤ n - 2 * k + 1 by
            zify [show 1 ≤ k by omega, h2k]
            have : (k : ℤ) ^ 2 ≤ (n : ℤ) := by exact_mod_cast hk2_of_4k2 h4k2
            nlinarith)
        rw [sub_nonneg, div_le_one hD_pos]
        exact this
      have h3k1 : (((3 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) =
          ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) +
            (((2 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) := by
        have hcast : ((3 * k - 1 : ℕ) : ℝ) = (k : ℝ) + ((2 * k - 1 : ℕ) : ℝ) := by
          have : 3 * k - 1 = k + (2 * k - 1) := by omega
          exact_mod_cast this
        rw [hcast]; ring
      have hprod_ge : 1 - (((3 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) ≤
          (1 - ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
            (1 - (((2 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) := by
        rw [h3k1]
        nlinarith [mul_nonneg ha_nonneg hb_nonneg]
      have hmul1 : ((n - k - 1).choose (k - 1) : ℝ) *
          ((1 - (((2 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) * bsum x A) ≤
          ∑ S ∈ FC, bsum x S := by
        rw [show ∑ S ∈ FC, bsum x S = ((n - k - 1).choose (k - 1) : ℝ) * bsum x C from hC_sum]
        exact mul_le_mul_of_nonneg_left hbC_ge (Nat.cast_nonneg _)
      have hb_pos_or_neg : 0 ≤ (1 - (((2 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) * bsum x A := by
        have h12k_nonneg : 0 ≤ 1 - (((2 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) := by
          have : ((2 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) ≤ ((n - 2 * k + 1 : ℕ) : ℝ) := by
            exact_mod_cast (show (2 * k - 1) * (k - 1) ≤ n - 2 * k + 1 by
              zify [show 1 ≤ 2 * k by omega, show 1 ≤ k by omega, h2k]
              have : 8 * (k : ℤ) ^ 2 ≤ (n : ℤ) := by exact_mod_cast hn
              nlinarith)
          rw [sub_nonneg, div_le_one hD_pos]; exact this
        exact mul_nonneg h12k_nonneg hbA.le
      have hmul2 := le_trans (mul_le_mul_of_nonneg_right hsub_k hb_pos_or_neg) hmul1
      calc (1 - (((3 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
            ((n - 1).choose (k - 1) : ℝ) * bsum x A
        _ ≤ (1 - ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
            (1 - (((2 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
              ((n - 1).choose (k - 1) : ℝ) * bsum x A := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprod_ge hch_pos.le) hbA.le
        _ = (1 - ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
              ((n - 1).choose (k - 1) : ℝ) *
              ((1 - (((2 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) * bsum x A) := by ring
        _ ≤ ∑ S ∈ FC, bsum x S := hmul2
    have hdiff_ub : (((n - 1).choose (k - 1) - (n - k - 1).choose (k - 1) : ℕ) : ℝ) ≤
        ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) * ((n - 1).choose (k - 1) : ℝ) := by
      have hle_ch : (n - k - 1).choose (k - 1) ≤ (n - 1).choose (k - 1) :=
        Nat.choose_le_choose _ (by omega)
      have hcast : (((n - 1).choose (k - 1) - (n - k - 1).choose (k - 1) : ℕ) : ℝ) =
          ((n - 1).choose (k - 1) : ℝ) - ((n - k - 1).choose (k - 1) : ℝ) :=
        Nat.cast_sub hle_ch
      rw [hcast]
      linarith [hsub_k]
    have hFC_disjA_ub : ∑ S ∈ FC_disjA, bsum x S ≤
        ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) *
          ((n - 1).choose (k - 1) : ℝ) * bsum x A :=
      le_trans hFC_disjA_sum (by
        have := mul_le_mul_of_nonneg_right hdiff_ub hbA.le
        linarith)
    have h4k1 : (((4 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) =
        (((3 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) +
          ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) := by
      have hcast : ((4 * k - 1 : ℕ) : ℝ) = ((3 * k - 1 : ℕ) : ℝ) + (k : ℝ) := by
        have : 4 * k - 1 = (3 * k - 1) + k := by omega
        exact_mod_cast this
      rw [hcast]; ring
    rw [h4k1]
    linarith [hsplit_FC, hFC_lb, hFC_disjA_ub]
  exact hFAC_sum
where
  hk2_of_4k2 {k n : ℕ} (h : 4 * k ^ 2 ≤ n) : k ^ 2 ≤ n := by nlinarith

private lemma fac1_sum_le {n k : ℕ} (hk : 2 ≤ k) (hn : 8 * k ^ 2 ≤ n) {x : Fin n → ℝ}
    (hx : Antitone x) (hx0 : ∑ i, x i = 0)
    (A C : Finset (Fin n)) (hA : A.card = k) (hC : C.card = k)
    (hAC : A ∩ C = {⟨0, by nlinarith⟩})
    (hbA : 0 < bsum x A)
    (hmaxA : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, bsum x S ≤ bsum x A) :
    ∑ S ∈ ((((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => ¬ Disjoint S C)).filter
        (fun S => ¬ Disjoint S A)).filter (fun S => ⟨0, by nlinarith⟩ ∉ S), bsum x S ≤
      (2 * (((k - 1 : ℕ) : ℝ) ^ 2) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
        ((n - 1).choose (k - 1) : ℝ) * bsum x A := by
  let z : Fin n := ⟨0, by nlinarith⟩
  have h2k : 2 * k ≤ n := by nlinarith
  have hzA : z ∈ A := by
    have : z ∈ A ∩ C := by rw [hAC]; exact Finset.mem_singleton_self z
    exact (Finset.mem_inter.mp this).1
  have hzC : z ∈ C := by
    have : z ∈ A ∩ C := by rw [hAC]; exact Finset.mem_singleton_self z
    exact (Finset.mem_inter.mp this).2
  have hD_pos : (0 : ℝ) < ((n - 2 * k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - 2 * k + 1 by omega)
  have hch_pos : (0 : ℝ) < ((n - 1).choose (k - 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : k - 1 ≤ n - 1)
  let FC := ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => ¬ Disjoint S C)
  let FAC := FC.filter (fun S => ¬ Disjoint S A)
  let FAC1 := FAC.filter (fun S => z ∉ S)
  let M1 := (n - 2).choose (k - 1) - (n - k - 1).choose (k - 1)
  let M2 := (n - 2).choose (k - 1) + (n - 2 * k).choose (k - 1) - 2 * (n - k - 1).choose (k - 1)
  have hch1 : (n - k - 1).choose (k - 1) ≤ (n - 2).choose (k - 1) :=
    Nat.choose_le_choose _ (by omega)
  have hM_ord1 : (n - 2 * k).choose (k - 1) ≤ (n - k - 1).choose (k - 1) :=
    Nat.choose_le_choose _ (by omega)
  have hM_ord2 : 2 * (n - k - 1).choose (k - 1) ≤ (n - 2).choose (k - 1) + (n - 2 * k).choose (k - 1) := by
    have h1 : (n - k - 1).choose (k - 1) - (n - 2 * k).choose (k - 1) ≤
        (k - 1) * (n - k - 2).choose (k - 2) := by
      have hcd := choose_diff_le (a := n - k - 1) (d := k - 1) (m := k - 1) (by omega) (by omega)
      have heq : (n - k - 1) - (k - 1) = n - 2 * k := by omega
      have heq2 : (n - k - 1) - 1 = n - k - 2 := by omega
      have heq3 : (k - 1) - 1 = k - 2 := by omega
      rwa [heq, heq2, heq3] at hcd
    have h2 : (n - 2).choose (k - 1) - (n - k - 1).choose (k - 1) ≥
        (n - k - 1).choose (k - 1) - (n - 2 * k).choose (k - 1) := by
      have hsucc := Nat.choose_succ_right_eq (n - 2) (k - 2)
      have hk_1 : (k - 2) + 1 = k - 1 := by omega
      have hn_k : (n - 2) - (k - 2) = n - k := by omega
      rw [hk_1, hn_k] at hsucc
      have hle_diff : (k - 1) * (n - k - 2).choose (k - 2) ≤
          (n - 2).choose (k - 1) - (n - k - 1).choose (k - 1) := by
        have hstep1 : (n - k - 1).choose (k - 1) + (k - 1) * (n - k - 2).choose (k - 2) ≤
            (n - 2).choose (k - 1) := by
          have hch_eq : (n - 2).choose (k - 1) ≥ (n - k - 1).choose (k - 1) +
              (k - 1) * (n - k - 2).choose (k - 2) := by
            have hd1 : (n - 2).choose (k - 1) - (n - k - 1).choose (k - 1) ≥
                (k - 1) * (n - k - 2).choose (k - 2) := by
              -- Telescoping sum of k - 1 terms, each ≥ (n - k - 2).choose (k - 2)
              have htel : ∀ d ≤ n - 2, (n - 2).choose (k - 1) - (n - 2 - d).choose (k - 1) ≥
                  d * (n - 2 - d).choose (k - 2) := by
                intro d hd
                induction d with
                | zero => simp
                | succ d ih =>
                  have hstep : (n - 2 - d).choose (k - 1) - (n - 2 - (d + 1)).choose (k - 1) =
                      (n - 2 - (d + 1)).choose (k - 2) := by
                    have h := Nat.choose_succ_succ (n - 2 - (d + 1)) (k - 2)
                    have hA1 : n - 2 - (d + 1) + 1 = n - 2 - d := by omega
                    have hK1 : k - 2 + 1 = k - 1 := by omega
                    simp only [Nat.succ_eq_add_one] at h
                    rw [hA1, hK1] at h
                    omega
                  have hmon : (n - 2 - (d + 1)).choose (k - 2) ≤ (n - 2 - d).choose (k - 2) :=
                    Nat.choose_le_choose _ (by omega)
                  have h1_le : (n - 2 - (d + 1)).choose (k - 1) ≤ (n - 2 - d).choose (k - 1) :=
                    Nat.choose_le_choose _ (by omega)
                  have h2_le : (n - 2 - d).choose (k - 1) ≤ (n - 2).choose (k - 1) :=
                    Nat.choose_le_choose _ (by omega)
                  have ih' := ih (by omega)
                  have hmul_le : d * (n - 2 - (d + 1)).choose (k - 2) ≤
                      d * (n - 2 - d).choose (k - 2) := Nat.mul_le_mul_left d hmon
                  have hmul_eq : (d + 1) * (n - 2 - (d + 1)).choose (k - 2) =
                      d * (n - 2 - (d + 1)).choose (k - 2) + (n - 2 - (d + 1)).choose (k - 2) := by ring
                  omega
              have htel' := htel (k - 1) (by omega)
              have heqa : n - 2 - (k - 1) = n - k - 1 := by omega
              have hmon2 : (n - k - 2).choose (k - 2) ≤ (n - k - 1).choose (k - 2) :=
                Nat.choose_le_choose _ (by omega)
              rw [heqa] at htel'
              exact le_trans (Nat.mul_le_mul_left (k - 1) hmon2) htel'
            omega
          exact hch_eq
        omega
      omega
    omega
  -- Helper: count of k-subsets S with i ∈ S and Disjoint S U (for U.card = k, z ∈ U, i ∉ U)
  have hcount_disj_i : ∀ {U : Finset (Fin n)} (hU : U.card = k) (hzU : z ∈ U) {i : Fin n} (hiU : i ∉ U),
      (((Finset.univ : Finset (Fin n)).powersetCard k).filter
        (fun S => z ∉ S ∧ i ∈ S ∧ Disjoint S U)).card = (n - k - 1).choose (k - 1) := by
    intro U hU hzU i hiU
    have hbij : (((Finset.univ : Finset (Fin n)).powersetCard k).filter
          (fun S => z ∉ S ∧ i ∈ S ∧ Disjoint S U)).card =
        (((Finset.univ \ U).erase i).powersetCard (k - 1)).card := by
      refine Finset.card_bij (fun S _ => S.erase i) ?_ ?_ ?_
      · intro S hS
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at hS
        simp only [mem_powersetCard]
        refine ⟨?_, by rw [Finset.card_erase_of_mem hS.2.2.1, hS.1]⟩
        intro y hy
        obtain ⟨hne, hyS⟩ := Finset.mem_erase.mp hy
        exact Finset.mem_erase.mpr ⟨hne, Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, Finset.disjoint_left.mp hS.2.2.2 hyS⟩⟩
      · intro S₁ h₁ S₂ h₂ heq
        simp only [mem_filter] at h₁ h₂
        have : insert i (S₁.erase i) = insert i (S₂.erase i) := congrArg (insert i) heq
        simpa [Finset.insert_erase h₁.2.2.1, Finset.insert_erase h₂.2.2.1] using this
      · intro T hT
        simp only [mem_powersetCard, subset_erase] at hT
        have hzT : z ∉ T := fun h => (Finset.mem_sdiff.mp (hT.1.1 h)).2 hzU
        have hzi : z ≠ i := fun h => hiU (h ▸ hzU)
        refine ⟨insert i T, ?_, Finset.erase_insert hT.1.2⟩
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and, mem_insert,
          true_or, not_or]
        refine ⟨?_, ⟨hzi, hzT⟩, ?_⟩
        · rw [Finset.card_insert_of_notMem hT.1.2, hT.2]; omega
        · rw [Finset.disjoint_insert_left]
          exact ⟨hiU, Finset.disjoint_left.mpr fun y hy => (Finset.mem_sdiff.mp (hT.1.1 hy)).2⟩
    rw [hbij, Finset.card_powersetCard,
      Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiU⟩),
      Finset.card_sdiff_of_subset (Finset.subset_univ U), Finset.card_univ, Fintype.card_fin, hU]
  have hcount_all_i : ∀ {i : Fin n} (hiz : i ≠ z),
      (((Finset.univ : Finset (Fin n)).powersetCard k).filter
        (fun S => z ∉ S ∧ i ∈ S)).card = (n - 2).choose (k - 1) := by
    intro i hiz
    have hbij : (((Finset.univ : Finset (Fin n)).powersetCard k).filter
          (fun S => z ∉ S ∧ i ∈ S)).card =
        (((Finset.univ.erase z).erase i).powersetCard (k - 1)).card := by
      refine Finset.card_bij (fun S _ => S.erase i) ?_ ?_ ?_
      · intro S hS
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at hS
        simp only [mem_powersetCard]
        refine ⟨?_, by rw [Finset.card_erase_of_mem hS.2.2, hS.1]⟩
        intro y hy
        obtain ⟨hyi, hyS⟩ := Finset.mem_erase.mp hy
        exact Finset.mem_erase.mpr ⟨hyi, Finset.mem_erase.mpr
          ⟨fun h => hS.2.1 (h ▸ hyS), Finset.mem_univ _⟩⟩
      · intro S₁ h₁ S₂ h₂ heq
        simp only [mem_filter] at h₁ h₂
        have : insert i (S₁.erase i) = insert i (S₂.erase i) := congrArg (insert i) heq
        simpa [Finset.insert_erase h₁.2.2, Finset.insert_erase h₂.2.2] using this
      · intro T hT
        simp only [mem_powersetCard, subset_erase] at hT
        refine ⟨insert i T, ?_, Finset.erase_insert hT.1.2⟩
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and, mem_insert,
          true_or, and_true, not_or]
        refine ⟨?_, hiz.symm, hT.1.1.2⟩
        rw [Finset.card_insert_of_notMem hT.1.2, hT.2]; omega
    rw [hbij, Finset.card_powersetCard,
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hiz, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ, Fintype.card_fin]
    congr 1
  have hFAC1_card_in : ∀ i ∈ (A ∪ C).erase z,
      (FAC1.filter (fun S => i ∈ S)).card = M1 := by
    intro i hi
    obtain ⟨hiz, hiAC⟩ := Finset.mem_erase.mp hi
    rcases Finset.mem_union.mp hiAC with hiA | hiC
    · have hiC : i ∉ C := fun h => hiz (Finset.mem_singleton.mp (hAC ▸ Finset.mem_inter.mpr ⟨hiA, h⟩))
      let U := ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => z ∉ S ∧ i ∈ S)
      have hU_eq : FAC1.filter (fun S => i ∈ S) =
          U.filter (fun S => ¬ Disjoint S C) := by
        ext S
        simp only [FAC1, FAC, FC, U, mem_filter]
        constructor
        · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
          exact ⟨⟨h1, h4, h5⟩, h2⟩
        · rintro ⟨⟨h1, h4, h5⟩, h2⟩
          have h3 : ¬ Disjoint S A := Finset.not_disjoint_iff.mpr ⟨i, h5, hiA⟩
          exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
      rw [hU_eq, Finset.filter_not]
      have hcard_disj : (U.filter (fun S => Disjoint S C)).card = (n - k - 1).choose (k - 1) := by
        convert hcount_disj_i hC hzC hiC using 2
        ext S; simp [U, and_assoc]
      have hsub : U.filter (fun S => Disjoint S C) ⊆ U := Finset.filter_subset _ _
      rw [Finset.card_sdiff_of_subset hsub, hcount_all_i hiz, hcard_disj]
    · have hiA : i ∉ A := fun h => hiz (Finset.mem_singleton.mp (hAC ▸ Finset.mem_inter.mpr ⟨h, hiC⟩))
      let U := ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => z ∉ S ∧ i ∈ S)
      have hU_eq : FAC1.filter (fun S => i ∈ S) =
          U.filter (fun S => ¬ Disjoint S A) := by
        ext S
        simp only [FAC1, FAC, FC, U, mem_filter]
        constructor
        · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
          exact ⟨⟨h1, h4, h5⟩, h3⟩
        · rintro ⟨⟨h1, h4, h5⟩, h3⟩
          have h2 : ¬ Disjoint S C := Finset.not_disjoint_iff.mpr ⟨i, h5, hiC⟩
          exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
      rw [hU_eq, Finset.filter_not]
      have hcard_disj : (U.filter (fun S => Disjoint S A)).card = (n - k - 1).choose (k - 1) := by
        convert hcount_disj_i hA hzA hiA using 2
        ext S; simp [U, and_assoc]
      have hsub : U.filter (fun S => Disjoint S A) ⊆ U := Finset.filter_subset _ _
      rw [Finset.card_sdiff_of_subset hsub, hcount_all_i hiz, hcard_disj]
  have hFAC1_card_out : ∀ i ∈ Finset.univ \ (A ∪ C),
      (FAC1.filter (fun S => i ∈ S)).card = M2 := by
    intro i hi
    have hiAC : i ∉ A ∪ C := (Finset.mem_sdiff.mp hi).2
    have hiA : i ∉ A := fun h => hiAC (Finset.mem_union_left _ h)
    have hiC : i ∉ C := fun h => hiAC (Finset.mem_union_right _ h)
    have hiz : i ≠ z := fun h => hiA (h ▸ hzA)
    let U := ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => z ∉ S ∧ i ∈ S)
    let UA := U.filter (fun S => Disjoint S A)
    let UC := U.filter (fun S => Disjoint S C)
    have hU_eq : FAC1.filter (fun S => i ∈ S) = U \ (UA ∪ UC) := by
      ext S
      simp only [FAC1, FAC, FC, U, UA, UC, mem_sdiff, mem_union, mem_filter]
      constructor
      · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
        refine ⟨⟨h1, h4, h5⟩, ?_⟩
        rintro (⟨_, hdA⟩ | ⟨_, hdC⟩)
        · exact h3 hdA
        · exact h2 hdC
      · rintro ⟨⟨h1, h4, h5⟩, hnot⟩
        have h2 : ¬ Disjoint S C := fun hd => hnot (Or.inr ⟨⟨h1, h4, h5⟩, hd⟩)
        have h3 : ¬ Disjoint S A := fun hd => hnot (Or.inl ⟨⟨h1, h4, h5⟩, hd⟩)
        exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    rw [hU_eq]
    have hsub_u : UA ∪ UC ⊆ U := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [Finset.card_sdiff_of_subset hsub_u, hcount_all_i hiz]
    have hUA_card : UA.card = (n - k - 1).choose (k - 1) := by
      convert hcount_disj_i hA hzA hiA using 2
      ext S; simp [UA, U, and_assoc]
    have hUC_card : UC.card = (n - k - 1).choose (k - 1) := by
      convert hcount_disj_i hC hzC hiC using 2
      ext S; simp [UC, U, and_assoc]
    have hUAC_card : (UA ∩ UC).card = (n - 2 * k).choose (k - 1) := by
      have hbij : (UA ∩ UC).card =
          (((Finset.univ \ (A ∪ C)).erase i).powersetCard (k - 1)).card := by
        refine Finset.card_bij (fun S _ => S.erase i) ?_ ?_ ?_
        · intro S hS
          simp only [UA, UC, U, mem_inter, mem_filter, mem_powersetCard, subset_univ, true_and] at hS
          simp only [mem_powersetCard]
          refine ⟨?_, by rw [Finset.card_erase_of_mem hS.1.1.2.2, hS.1.1.1]⟩
          intro y hy
          obtain ⟨hne, hyS⟩ := Finset.mem_erase.mp hy
          refine Finset.mem_erase.mpr ⟨hne, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hyAC => ?_⟩⟩
          rcases Finset.mem_union.mp hyAC with hyA | hyC
          · exact Finset.disjoint_left.mp hS.1.2 hyS hyA
          · exact Finset.disjoint_left.mp hS.2.2 hyS hyC
        · intro S₁ h₁ S₂ h₂ heq
          simp only [UA, U, mem_inter, mem_filter] at h₁ h₂
          have : insert i (S₁.erase i) = insert i (S₂.erase i) := congrArg (insert i) heq
          simpa [Finset.insert_erase h₁.1.1.2.2, Finset.insert_erase h₂.1.1.2.2] using this
        · intro T hT
          simp only [mem_powersetCard, subset_erase] at hT
          have hzT : z ∉ T := fun h => (Finset.mem_sdiff.mp (hT.1.1 h)).2 (Finset.mem_union_left _ hzA)
          refine ⟨insert i T, ?_, Finset.erase_insert hT.1.2⟩
          simp only [UA, UC, U, mem_inter, mem_filter, mem_powersetCard, subset_univ, true_and,
            mem_insert, true_or, and_true, not_or]
          have hcardT : (insert i T).card = k := by
            rw [Finset.card_insert_of_notMem hT.1.2, hT.2]; omega
          have hdA : Disjoint (insert i T) A := by
            rw [Finset.disjoint_insert_left]
            exact ⟨hiA, Finset.disjoint_left.mpr fun y hy =>
              fun hyA => (Finset.mem_sdiff.mp (hT.1.1 hy)).2 (Finset.mem_union_left _ hyA)⟩
          have hdC : Disjoint (insert i T) C := by
            rw [Finset.disjoint_insert_left]
            exact ⟨hiC, Finset.disjoint_left.mpr fun y hy =>
              fun hyC => (Finset.mem_sdiff.mp (hT.1.1 hy)).2 (Finset.mem_union_right _ hyC)⟩
          exact ⟨⟨⟨hcardT, hiz.symm, hzT⟩, hdA⟩, ⟨⟨hcardT, hiz.symm, hzT⟩, hdC⟩⟩
      have hAC_card : (A ∪ C).card = 2 * k - 1 := by
        have := Finset.card_union_add_card_inter A C
        rw [hA, hC, hAC, Finset.card_singleton] at this
        omega
      rw [hbij, Finset.card_powersetCard,
        Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiAC⟩),
        Finset.card_sdiff_of_subset (Finset.subset_univ (A ∪ C)), Finset.card_univ, Fintype.card_fin, hAC_card]
      congr 1
      omega
    have hincl := Finset.card_union_add_card_inter UA UC
    have huni : (UA ∪ UC).card = 2 * (n - k - 1).choose (k - 1) - (n - 2 * k).choose (k - 1) := by
      omega
    rw [huni]
    omega
  have hFAC1_sum_ub : ∑ S ∈ FAC1, bsum x S ≤
      (2 * (((k - 1 : ℕ) : ℝ) ^ 2) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
        ((n - 1).choose (k - 1) : ℝ) * bsum x A := by
    have h1 : ∑ S ∈ FAC1, bsum x S =
        ∑ i ∈ Finset.univ.erase z, ((FAC1.filter (fun S => i ∈ S)).card : ℝ) * x i := by
      simp only [bsum]
      calc ∑ S ∈ FAC1, ∑ i ∈ S, x i
        _ = ∑ S ∈ FAC1, ∑ i ∈ Finset.univ.erase z, (if i ∈ S then x i else 0) := by
            refine Finset.sum_congr rfl fun S hS => ?_
            have hzS : z ∉ S := (Finset.mem_filter.mp hS).2
            rw [← Finset.sum_filter]
            refine Finset.sum_congr ?_ fun _ _ => rfl
            ext i
            simp only [mem_filter, mem_erase]
            exact ⟨fun hi => ⟨⟨fun h => hzS (h ▸ hi), Finset.mem_univ _⟩, hi⟩, fun h => h.2⟩
        _ = ∑ i ∈ Finset.univ.erase z, ∑ S ∈ FAC1, (if i ∈ S then x i else 0) := Finset.sum_comm
        _ = ∑ i ∈ Finset.univ.erase z, ((FAC1.filter (fun S => i ∈ S)).card : ℝ) * x i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    rw [h1]
    have hpart_z : Finset.univ.erase z = ((A ∪ C).erase z) ∪ (Finset.univ \ (A ∪ C)) := by
      ext i
      simp only [mem_erase, mem_univ, and_true, mem_union, mem_sdiff, true_and]
      constructor
      · intro hiz
        by_cases h : i ∈ A ∨ i ∈ C
        · exact Or.inl ⟨hiz, h⟩
        · exact Or.inr h
      · rintro (⟨hiz, _⟩ | hiAC)
        · exact hiz
        · exact fun h => hiAC (Or.inl (h ▸ hzA))
    have hdisj_z : Disjoint ((A ∪ C).erase z) (Finset.univ \ (A ∪ C)) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_erase.mp h1).2
    rw [hpart_z, Finset.sum_union hdisj_z]
    have hs1 : ∑ i ∈ (A ∪ C).erase z, ((FAC1.filter (fun S => i ∈ S)).card : ℝ) * x i =
        (M1 : ℝ) * (bsum x A + bsum x C - 2 * x z) := by
      have hcon : ∑ i ∈ (A ∪ C).erase z, ((FAC1.filter (fun S => i ∈ S)).card : ℝ) * x i =
          (M1 : ℝ) * ∑ i ∈ (A ∪ C).erase z, x i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => by rw [hFAC1_card_in i hi]
      rw [hcon]
      congr 1
      have hsum_AC : ∑ i ∈ A ∪ C, x i = bsum x A + bsum x C - x z := by
        have := Finset.sum_union_inter (s₁ := A) (s₂ := C) (f := x)
        rw [hAC, Finset.sum_singleton] at this
        change ∑ i ∈ A ∪ C, x i + x z = bsum x A + bsum x C at this
        linarith
      have hsum_er : ∑ i ∈ (A ∪ C).erase z, x i + x z = ∑ i ∈ A ∪ C, x i :=
        Finset.sum_erase_add (A ∪ C) x (Finset.mem_union_left _ hzA)
      linarith
    have hs2 : ∑ i ∈ Finset.univ \ (A ∪ C), ((FAC1.filter (fun S => i ∈ S)).card : ℝ) * x i =
        (M2 : ℝ) * (x z - bsum x A - bsum x C) := by
      have hcon : ∑ i ∈ Finset.univ \ (A ∪ C), ((FAC1.filter (fun S => i ∈ S)).card : ℝ) * x i =
          (M2 : ℝ) * ∑ i ∈ Finset.univ \ (A ∪ C), x i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => by rw [hFAC1_card_out i hi]
      rw [hcon]
      congr 1
      have hsum_AC : ∑ i ∈ A ∪ C, x i = bsum x A + bsum x C - x z := by
        have := Finset.sum_union_inter (s₁ := A) (s₂ := C) (f := x)
        rw [hAC, Finset.sum_singleton] at this
        change ∑ i ∈ A ∪ C, x i + x z = bsum x A + bsum x C at this
        linarith
      have hcomp := Finset.sum_sdiff (Finset.subset_univ (A ∪ C)) (f := x)
      rw [hx0] at hcomp
      linarith
    rw [hs1, hs2]
    have halg : (M1 : ℝ) * (bsum x A + bsum x C - 2 * x z) +
        (M2 : ℝ) * (x z - bsum x A - bsum x C) =
        ((2 * M1 - M2 : ℕ) : ℝ) * (- x z) + ((M1 - M2 : ℕ) : ℝ) * (bsum x A + bsum x C) := by
      have hle2 : M2 ≤ 2 * M1 := by omega
      have hle1 : M2 ≤ M1 := by omega
      have hc1 : ((2 * M1 - M2 : ℕ) : ℝ) = 2 * (M1 : ℝ) - (M2 : ℝ) := by
        rw [Nat.cast_sub hle2, Nat.cast_mul, Nat.cast_ofNat]
      have hc2 : ((M1 - M2 : ℕ) : ℝ) = (M1 : ℝ) - (M2 : ℝ) := Nat.cast_sub hle1
      rw [hc1, hc2]
      ring
    rw [halg]
    have hxz_pos : 0 ≤ x z := by
      have hAxz : bsum x A ≤ (k : ℝ) * x z := by
        rw [bsum]
        calc ∑ i ∈ A, x i
          _ ≤ ∑ _i ∈ A, x z := Finset.sum_le_sum fun i hi => hx (Nat.zero_le i.val)
          _ = (k : ℝ) * x z := by rw [Finset.sum_const, nsmul_eq_mul, hA]
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      exact le_of_lt (pos_of_mul_pos_right (lt_of_lt_of_le hbA hAxz) hk_pos.le)
    have hterm1 : ((2 * M1 - M2 : ℕ) : ℝ) * (- x z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (neg_nonpos.mpr hxz_pos)
    have hbCA : bsum x C ≤ bsum x A := hmaxA C (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hC⟩)
    have hM12_bound : ((M1 - M2 : ℕ) : ℝ) ≤
        (((k - 1 : ℕ) : ℝ) ^ 2 / ((n - 2 * k + 1 : ℕ) : ℝ)) * ((n - 1).choose (k - 1) : ℝ) := by
      have hsub_eq : M1 - M2 = (n - k - 1).choose (k - 1) - (n - 2 * k).choose (k - 1) := by omega
      have hle_tel : (n - k - 1).choose (k - 1) - (n - 2 * k).choose (k - 1) ≤
          (k - 1) * (n - k - 2).choose (k - 2) := by
        have hcd := choose_diff_le (a := n - k - 1) (d := k - 1) (m := k - 1) (by omega) (by omega)
        have heq1 : (n - k - 1) - (k - 1) = n - 2 * k := by omega
        have heq2 : (n - k - 1) - 1 = n - k - 2 := by omega
        have heq3 : (k - 1) - 1 = k - 2 := by omega
        rwa [heq1, heq2, heq3] at hcd
      have hle_n2 : (n - k - 2).choose (k - 2) ≤ (n - 2).choose (k - 2) :=
        Nat.choose_le_choose _ (by omega)
      have hsucc : (n - 2).choose (k - 2) * (n - 1) = (n - 1).choose (k - 1) * (k - 1) := by
        have h := Nat.add_one_mul_choose_eq (n - 2) (k - 2)
        have hA' : (n - 2) + 1 = n - 1 := by omega
        have hB' : (k - 2) + 1 = k - 1 := by omega
        rw [hA', hB'] at h
        linarith
      have hM_mul : (M1 - M2) * (n - 1) ≤ (k - 1) ^ 2 * (n - 1).choose (k - 1) := by
        have hstep1 : M1 - M2 ≤ (k - 1) * (n - 2).choose (k - 2) :=
          le_trans (le_trans hsub_eq.le hle_tel) (Nat.mul_le_mul_left _ hle_n2)
        calc (M1 - M2) * (n - 1)
          _ ≤ ((k - 1) * (n - 2).choose (k - 2)) * (n - 1) := Nat.mul_le_mul_right _ hstep1
          _ = (k - 1) * ((n - 2).choose (k - 2) * (n - 1)) := by ring
          _ = (k - 1) * ((n - 1).choose (k - 1) * (k - 1)) := by rw [hsucc]
          _ = (k - 1) ^ 2 * (n - 1).choose (k - 1) := by ring
      have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
      have hM_mulR : ((M1 - M2 : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) ≤
          ((k - 1 : ℕ) : ℝ) ^ 2 * ((n - 1).choose (k - 1) : ℝ) := by exact_mod_cast hM_mul
      have hdiv1 : ((M1 - M2 : ℕ) : ℝ) ≤
          (((k - 1 : ℕ) : ℝ) ^ 2 / ((n - 1 : ℕ) : ℝ)) * ((n - 1).choose (k - 1) : ℝ) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hn1_pos]
        exact hM_mulR
      have hden_le : ((n - 2 * k + 1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show n - 2 * k + 1 ≤ n - 1 by omega)
      have hdiv2 : ((k - 1 : ℕ) : ℝ) ^ 2 / ((n - 1 : ℕ) : ℝ) ≤
          ((k - 1 : ℕ) : ℝ) ^ 2 / ((n - 2 * k + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hD_pos hden_le
      exact le_trans hdiv1 (mul_le_mul_of_nonneg_right hdiv2 hch_pos.le)
    have hterm2 : ((M1 - M2 : ℕ) : ℝ) * (bsum x A + bsum x C) ≤
        (2 * (((k - 1 : ℕ) : ℝ) ^ 2) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
          ((n - 1).choose (k - 1) : ℝ) * bsum x A := by
      calc ((M1 - M2 : ℕ) : ℝ) * (bsum x A + bsum x C)
        _ ≤ ((M1 - M2 : ℕ) : ℝ) * (2 * bsum x A) :=
            mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
        _ ≤ (((((k - 1 : ℕ) : ℝ) ^ 2 / ((n - 2 * k + 1 : ℕ) : ℝ)) * ((n - 1).choose (k - 1) : ℝ))) * (2 * bsum x A) :=
            mul_le_mul_of_nonneg_right hM12_bound (by linarith)
        _ = (2 * (((k - 1 : ℕ) : ℝ) ^ 2) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
              ((n - 1).choose (k - 1) : ℝ) * bsum x A := by ring
    exact (add_le_add hterm1 hterm2).trans_eq (zero_add _)
  exact hFAC1_sum_ub

private lemma count_zero_ge {n k : ℕ} (hk : 2 ≤ k) (hn : 8 * k ^ 2 ≤ n) {x : Fin n → ℝ}
    (hx : Antitone x) (hx0 : ∑ i, x i = 0)
    (A C : Finset (Fin n)) (hA : A.card = k) (hC : C.card = k)
    (hAC : A ∩ C = {⟨0, by nlinarith⟩})
    (hbA : 0 < bsum x A)
    (hmaxA : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, bsum x S ≤ bsum x A)
    (hmaxC : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (S ∩ A).card = 1 → bsum x S ≤ bsum x C)
    (hle : nonnegSubsetCount n k x ≤ (n - 1).choose (k - 1)) :
    (1 - (((6 * k - 3 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
        ((n - 1).choose (k - 1) : ℝ) ≤
      ((((Finset.univ : Finset (Fin n)).powersetCard k).filter
        (fun S => ⟨0, by nlinarith⟩ ∈ S ∧ 0 ≤ bsum x S)).card : ℝ) := by
  let z : Fin n := ⟨0, by nlinarith⟩
  let FC := ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => ¬ Disjoint S C)
  let FAC := FC.filter (fun S => ¬ Disjoint S A)
  let FAC0 := FAC.filter (fun S => z ∈ S)
  let FAC1 := FAC.filter (fun S => z ∉ S)
  have hFAC_sum : (1 - (((4 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
      ((n - 1).choose (k - 1) : ℝ) * bsum x A ≤ ∑ S ∈ FAC, bsum x S :=
    fac_sum_ge hk hn hx0 A C hA hC hAC hbA hmaxA hmaxC hle
  have hFAC_split : ∑ S ∈ FAC, bsum x S = ∑ S ∈ FAC0, bsum x S + ∑ S ∈ FAC1, bsum x S :=
    (Finset.sum_filter_add_sum_filter_not FAC (fun S => z ∈ S) (bsum x)).symm
  have hFAC1_sum_ub : ∑ S ∈ FAC1, bsum x S ≤
      (2 * (((k - 1 : ℕ) : ℝ) ^ 2) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
        ((n - 1).choose (k - 1) : ℝ) * bsum x A :=
    fac1_sum_le hk hn hx hx0 A C hA hC hAC hbA hmaxA
  have hFAC0_lb : (1 - (((6 * k - 3 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
      ((n - 1).choose (k - 1) : ℝ) * bsum x A ≤ ∑ S ∈ FAC0, bsum x S := by
    have h6k3 : (((6 * k - 3 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) =
        (((4 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) +
          2 * (((k - 1 : ℕ) : ℝ) ^ 2) / ((n - 2 * k + 1 : ℕ) : ℝ) := by
      have hcast1 : ((6 * k - 3 : ℕ) : ℝ) = ((4 * k - 1 : ℕ) : ℝ) + 2 * ((k - 1 : ℕ) : ℝ) := by
        have : 6 * k - 3 = (4 * k - 1) + 2 * (k - 1) := by omega
        exact_mod_cast this
      rw [hcast1]; ring
    rw [h6k3]
    linarith [hFAC_split, hFAC_sum, hFAC1_sum_ub]
  have hFAC0_pos_sum : ∑ S ∈ FAC0, bsum x S ≤
      ((FAC0.filter (fun S => 0 ≤ bsum x S)).card : ℝ) * bsum x A := by
    have h1 : ∑ S ∈ FAC0, bsum x S ≤ ∑ S ∈ FAC0.filter (fun S => 0 ≤ bsum x S), bsum x S := by
      rw [← Finset.sum_filter_add_sum_filter_not FAC0 (fun S => 0 ≤ bsum x S) (bsum x)]
      have hneg : ∑ S ∈ FAC0.filter (fun S => ¬ 0 ≤ bsum x S), bsum x S ≤ 0 :=
        Finset.sum_nonpos fun S hS => le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hS).2)
      linarith [hneg]
    have h2 : ∑ S ∈ FAC0.filter (fun S => 0 ≤ bsum x S), bsum x S ≤
        ((FAC0.filter (fun S => 0 ≤ bsum x S)).card : ℝ) * bsum x A := by
      calc ∑ S ∈ FAC0.filter (fun S => 0 ≤ bsum x S), bsum x S
        _ ≤ ∑ _S ∈ FAC0.filter (fun S => 0 ≤ bsum x S), bsum x A :=
            Finset.sum_le_sum fun S hS => by
              simp only [FAC0, FAC, FC, mem_filter] at hS
              exact hmaxA S hS.1.1.1.1
        _ = ((FAC0.filter (fun S => 0 ≤ bsum x S)).card : ℝ) * bsum x A := by
            rw [Finset.sum_const, nsmul_eq_mul]
    exact le_trans h1 h2
  have hcard_FAC0 : (FAC0.filter (fun S => 0 ≤ bsum x S)).card ≤
      (((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => z ∈ S ∧ 0 ≤ bsum x S)).card := by
    refine Finset.card_le_card fun S hS => ?_
    simp only [FAC0, FAC, FC, mem_filter] at hS ⊢
    exact ⟨hS.1.1.1.1, hS.1.2, hS.2⟩
  have hfinal_mul : (1 - (((6 * k - 3 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
      ((n - 1).choose (k - 1) : ℝ) * bsum x A ≤
      ((((Finset.univ : Finset (Fin n)).powersetCard k).filter
        (fun S => z ∈ S ∧ 0 ≤ bsum x S)).card : ℝ) * bsum x A :=
    le_trans (le_trans hFAC0_lb hFAC0_pos_sum) (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_FAC0) hbA.le)
  exact le_of_mul_le_mul_right hfinal_mul hbA
private lemma extend_neg_subset {n k : ℕ} (x : Fin n → ℝ) (hx0 : ∑ i, x i = 0)
    (T : Finset (Fin n)) (hT : T.card = k) (hbT : bsum x T < 0)
    (j : ℕ) (hj : k + j < n) :
    ∃ U : Finset (Fin n), T ⊆ U ∧ U.card = k + j ∧ bsum x U < 0 := by
  induction j with
  | zero => exact ⟨T, Finset.Subset.refl _, hT, hbT⟩
  | succ j ih =>
    obtain ⟨W, hTW, hWcard, hbW⟩ := ih (by omega)
    have hcomp_sum : ∑ v ∈ Finset.univ \ W, bsum x (insert v W) =
        ((n - (k + j) - 1 : ℕ) : ℝ) * bsum x W := by
      have hcard_comp : (Finset.univ \ W).card = n - (k + j) := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ W), Finset.card_univ, Fintype.card_fin, hWcard]
      have hsum_ins : ∑ v ∈ Finset.univ \ W, bsum x (insert v W) =
          ∑ v ∈ Finset.univ \ W, (bsum x W + x v) := by
        refine Finset.sum_congr rfl fun v hv => ?_
        have hvW : v ∉ W := (Finset.mem_sdiff.mp hv).2
        simp [bsum, Finset.sum_insert hvW, add_comm]
      have hsum_x_comp : ∑ v ∈ Finset.univ \ W, x v = - bsum x W := by
        have := Finset.sum_sdiff (Finset.subset_univ W) (f := x)
        rw [hx0] at this
        change (∑ v ∈ Finset.univ \ W, x v) + bsum x W = 0 at this
        linarith
      rw [hsum_ins, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard_comp, hsum_x_comp]
      have hc : ((n - (k + j) - 1 : ℕ) : ℝ) = ((n - (k + j) : ℕ) : ℝ) - 1 := by
        have h1le : 1 ≤ n - (k + j) := by omega
        have hcast : ((n - (k + j) - 1 : ℕ) : ℝ) + 1 = ((n - (k + j) : ℕ) : ℝ) := by
          exact_mod_cast Nat.sub_add_cancel h1le
        linarith
      rw [hc]
      ring
    have hsum_neg : ∑ v ∈ Finset.univ \ W, bsum x (insert v W) < 0 := by
      rw [hcomp_sum]
      have hpos : (0 : ℝ) < ((n - (k + j) - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < n - (k + j) - 1 by omega)
      exact mul_neg_of_pos_of_neg hpos hbW
    have hex : ∃ v ∈ Finset.univ \ W, bsum x (insert v W) < 0 := by
      by_contra hnot
      push Not at hnot
      have hge0 : 0 ≤ ∑ v ∈ Finset.univ \ W, bsum x (insert v W) := Finset.sum_nonneg hnot
      linarith
    obtain ⟨v, hv, hbv⟩ := hex
    have hvW : v ∉ W := (Finset.mem_sdiff.mp hv).2
    refine ⟨insert v W, Finset.Subset.trans hTW (Finset.subset_insert v W), ?_, hbv⟩
    rw [Finset.card_insert_of_notMem hvW, hWcard]; omega

private lemma count_disjoint_T_ge {n k : ℕ} (hk : 2 ≤ k) (hn : 4 * k ≤ n) (x : Fin n → ℝ)
    (hx0 : ∑ i, x i = 0) (T : Finset (Fin n)) (hT : T.card = k) (hbT : bsum x T < 0) :
    (1 - (((2 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
        ((n - 1).choose (k - 1) : ℝ) ≤
      ((((Finset.univ : Finset (Fin n)).powersetCard k).filter
        (fun S => Disjoint S T ∧ 0 ≤ bsum x S)).card : ℝ) := by
  let r := n % k
  have hr_lt : r < k := Nat.mod_lt n (by omega)
  have hkr : k + r < n := by omega
  obtain ⟨U, hTU, hUcard, hbU⟩ := extend_neg_subset x hx0 T hT hbT r hkr
  let V := Finset.univ \ U
  have hVcard : V.card = n - (k + r) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ U), Finset.card_univ, Fintype.card_fin, hUcard]
  let M := V.card
  have hk_dvd : k ∣ M := by
    have hM_eq : M = n - (k + n % k) := hVcard
    have hmod : n = k * (n / k) + n % k := (Nat.div_add_mod n k).symm
    have hge1 : 1 ≤ n / k := Nat.div_pos (by omega) (by omega)
    have hM_eq2 : M = k * (n / k - 1) := by
      rw [hM_eq]
      have : k * (n / k) = k * (n / k - 1) + k := by
        conv_lhs => rw [show n / k = (n / k - 1) + 1 by omega, mul_add, mul_one]
      omega
    exact ⟨n / k - 1, hM_eq2⟩
  obtain ⟨m1, hM_eq⟩ := hk_dvd
  have hm1_pos : 1 ≤ m1 := by
    by_contra hm0
    have : m1 = 0 := by omega
    rw [this, mul_zero] at hM_eq
    omega
  let VType := {v : Fin n // v ∈ V}
  have hVType_card : Fintype.card VType = M := Fintype.card_coe V
  have hprod_card : Fintype.card VType = Fintype.card (Fin m1 × Fin k) := by
    rw [hVType_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hM_eq, Nat.mul_comm]
  let e : VType ≃ Fin m1 × Fin k := Fintype.equivOfCardEq hprod_card
  let Q : Fin m1 → Finset VType := fun j =>
    (Finset.univ : Finset (Fin k)).map
      ⟨fun t => e.symm (j, t), fun a b h => Prod.ext_iff.mp (e.symm.injective h) |>.2⟩
  have hQ_card : ∀ j : Fin m1, (Q j).card = k := by
    intro j; simp [Q]
  have hQ_disj : ∀ j₁ j₂ : Fin m1, j₁ ≠ j₂ → Disjoint (Q j₁) (Q j₂) := by
    intro j₁ j₂ hne
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [Q, mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and] at hv1 hv2
    obtain ⟨t₁, rfl⟩ := hv1
    obtain ⟨t₂, hteq⟩ := hv2
    have := Prod.ext_iff.mp (e.symm.injective hteq)
    exact hne this.1.symm
  have hQ_cover : ∀ v : VType, ∃ j : Fin m1, v ∈ Q j := by
    intro v
    refine ⟨(e v).1, ?_⟩
    simp only [Q, mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and]
    exact ⟨(e v).2, by show e.symm ((e v).1, (e v).2) = v; simp⟩
  have hQ_biUnion : (Finset.univ : Finset (Fin m1)).biUnion Q = Finset.univ := by
    ext v
    simp only [mem_biUnion, mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => hQ_cover v⟩
  let w : Finset VType → ℝ := fun S => ∑ v ∈ S, x v.val
  have hw_tot : ∑ v : VType, x v.val = - bsum x U := by
    have hcoe : ∑ v : VType, x v.val = ∑ v ∈ V, x v :=
      Finset.sum_coe_sort V x
    have hcomp := Finset.sum_sdiff (Finset.subset_univ U) (f := x)
    rw [hx0] at hcomp
    change (∑ v ∈ V, x v) + bsum x U = 0 at hcomp
    linarith
  have hw_pos : 0 < ∑ v : VType, x v.val := by
    rw [hw_tot]
    linarith
  have hperm_sum : ∀ π : Equiv.Perm VType,
      ∑ j : Fin m1, w ((Q j).map π.toEmbedding) = ∑ v : VType, x v.val := by
    intro π
    have hdisj_img : ∀ j₁ ∈ (Finset.univ : Finset (Fin m1)), ∀ j₂ ∈ (Finset.univ : Finset (Fin m1)),
        j₁ ≠ j₂ → Disjoint ((Q j₁).map π.toEmbedding) ((Q j₂).map π.toEmbedding) := by
      intro j₁ _ j₂ _ hne
      rw [Finset.disjoint_map]
      exact hQ_disj j₁ j₂ hne
    have hbiUnion_img : (Finset.univ : Finset (Fin m1)).biUnion (fun j => (Q j).map π.toEmbedding) =
        Finset.univ := by
      ext v
      simp only [mem_biUnion, mem_univ, true_and, mem_map, RelEmbedding.coe_toEmbedding]
      constructor
      · intro _; trivial
      · intro _
        obtain ⟨j, hj⟩ := hQ_cover (π.symm v)
        exact ⟨j, π.symm v, hj, by simp⟩
    calc ∑ j : Fin m1, w ((Q j).map π.toEmbedding)
      _ = ∑ v ∈ (Finset.univ : Finset (Fin m1)).biUnion (fun j => (Q j).map π.toEmbedding), x v.val :=
          (Finset.sum_biUnion hdisj_img).symm
      _ = ∑ v : VType, x v.val := by rw [hbiUnion_img]
  have hex_good_j : ∀ π : Equiv.Perm VType,
      1 ≤ ((Finset.univ : Finset (Fin m1)).filter (fun j => 0 ≤ w ((Q j).map π.toEmbedding))).card := by
    intro π
    rw [Finset.one_le_card]
    by_contra hnot
    rw [Finset.not_nonempty_iff_eq_empty] at hnot
    have hneg : ∀ j ∈ (Finset.univ : Finset (Fin m1)), w ((Q j).map π.toEmbedding) < 0 := by
      intro j _
      by_contra hge
      push Not at hge
      have hjmem : j ∈ (Finset.univ : Finset (Fin m1)).filter (fun j => 0 ≤ w ((Q j).map π.toEmbedding)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hge⟩
      rw [hnot] at hjmem
      simp at hjmem
    have hsum_neg : ∑ j : Fin m1, w ((Q j).map π.toEmbedding) ≤ 0 :=
      Finset.sum_nonpos fun j hj => le_of_lt (hneg j hj)
    linarith [hperm_sum π]
  -- Symmetry: for each j, every k-subset S of VType has the same number of π mapping Q j to S
  let goodV := ((Finset.univ : Finset VType).powersetCard k).filter (fun S => 0 ≤ w S)
  have hsymm : ∀ (j : Fin m1) (S₁ S₂ : Finset VType),
      S₁ ∈ (Finset.univ : Finset VType).powersetCard k →
      S₂ ∈ (Finset.univ : Finset VType).powersetCard k →
      ((Finset.univ : Finset (Equiv.Perm VType)).filter (fun π => (Q j).map π.toEmbedding = S₁)).card =
      ((Finset.univ : Finset (Equiv.Perm VType)).filter (fun π => (Q j).map π.toEmbedding = S₂)).card := by
    intro j S₁ S₂ hS₁ hS₂
    simp only [mem_powersetCard, subset_univ, true_and] at hS₁ hS₂
    have heq_in : Fintype.card {v : VType // v ∈ S₁} = Fintype.card {v : VType // v ∈ S₂} := by
      rw [Fintype.card_coe S₁, Fintype.card_coe S₂, hS₁, hS₂]
    have heq_out : Fintype.card {v : VType // v ∉ S₁} = Fintype.card {v : VType // v ∉ S₂} := by
      rw [Fintype.card_subtype_compl (fun v : VType => v ∈ S₁),
        Fintype.card_subtype_compl (fun v : VType => v ∈ S₂),
        Fintype.card_coe S₁, Fintype.card_coe S₂, hS₁, hS₂]
    let e1 := Fintype.equivOfCardEq heq_in
    let e2 := Fintype.equivOfCardEq heq_out
    let τ : Equiv.Perm VType :=
      { toFun := fun v => if hv : v ∈ S₁ then (e1 ⟨v, hv⟩).1 else (e2 ⟨v, hv⟩).1
        invFun := fun v => if hv : v ∈ S₂ then (e1.symm ⟨v, hv⟩).1 else (e2.symm ⟨v, hv⟩).1
        left_inv := fun v => by
          by_cases hv : v ∈ S₁
          · simp [hv, (e1 ⟨v, hv⟩).2]
          · simp [hv, (e2 ⟨v, hv⟩).2]
        right_inv := fun v => by
          by_cases hv : v ∈ S₂
          · simp [hv, (e1.symm ⟨v, hv⟩).2]
          · simp [hv, (e2.symm ⟨v, hv⟩).2] }
    have hτS : S₁.map τ.toEmbedding = S₂ := by
      ext y
      simp only [mem_map, Equiv.toEmbedding_apply]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simp only [τ, Equiv.coe_fn_mk, hx, dite_true]
        exact (e1 ⟨x, hx⟩).2
      · intro hy
        refine ⟨τ.symm y, ?_, by simp⟩
        simp only [τ, Equiv.coe_fn_symm_mk, hy, dite_true]
        exact (e1.symm ⟨y, hy⟩).2
    refine Finset.card_bij (fun π _ => τ * π) ?_ ?_ ?_
    · intro π hπ
      simp only [mem_filter, mem_univ, true_and] at hπ ⊢
      calc (Q j).map (τ * π).toEmbedding
        _ = ((Q j).map π.toEmbedding).map τ.toEmbedding := by
            ext y
            simp only [mem_map, Equiv.toEmbedding_apply, Equiv.Perm.mul_apply]
            constructor
            · rintro ⟨x, hx, rfl⟩; exact ⟨π x, ⟨x, hx, rfl⟩, rfl⟩
            · rintro ⟨a, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
        _ = S₁.map τ.toEmbedding := by rw [hπ]
        _ = S₂ := hτS
    · intro π₁ _ π₂ _ h
      exact mul_left_cancel h
    · intro π' hπ'
      simp only [mem_filter, mem_univ, true_and] at hπ'
      refine ⟨τ⁻¹ * π', ?_, by simp⟩
      simp only [mem_filter, mem_univ, true_and]
      have hmap : ((Q j).map π'.toEmbedding).map τ⁻¹.toEmbedding = S₁ := by
        rw [hπ', ← hτS]
        ext y
        simp only [mem_map, Equiv.toEmbedding_apply]
        constructor
        · rintro ⟨a, ⟨x, hx, rfl⟩, rfl⟩; simpa using hx
        · intro hy; exact ⟨τ y, ⟨y, hy, rfl⟩, by simp⟩
      calc (Q j).map (τ⁻¹ * π').toEmbedding
        _ = ((Q j).map π'.toEmbedding).map τ⁻¹.toEmbedding := by
            ext y
            simp only [mem_map, Equiv.toEmbedding_apply, Equiv.Perm.mul_apply]
            constructor
            · rintro ⟨x, hx, rfl⟩; exact ⟨π' x, ⟨x, hx, rfl⟩, rfl⟩
            · rintro ⟨a, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
        _ = S₁ := hmap
  have hQ0_mem : Q ⟨0, hm1_pos⟩ ∈ (Finset.univ : Finset VType).powersetCard k :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hQ_card ⟨0, hm1_pos⟩⟩
  let c := ((Finset.univ : Finset (Equiv.Perm VType)).filter
    (fun π => (Q ⟨0, hm1_pos⟩).map π.toEmbedding = Q ⟨0, hm1_pos⟩)).card
  have hc_val : ∀ j : Fin m1, ∀ S ∈ (Finset.univ : Finset VType).powersetCard k,
      ((Finset.univ : Finset (Equiv.Perm VType)).filter (fun π => (Q j).map π.toEmbedding = S)).card = c := by
    intro j S hS
    have h1 := hsymm j S (Q ⟨0, hm1_pos⟩) hS hQ0_mem
    have hQj_mem : Q j ∈ (Finset.univ : Finset VType).powersetCard k :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hQ_card j⟩
    -- Compare Q j and Q 0 via the bijection mapping (j, t) <-> (0, t)
    have h2 : ((Finset.univ : Finset (Equiv.Perm VType)).filter
          (fun π => (Q j).map π.toEmbedding = Q ⟨0, hm1_pos⟩)).card = c := by
      let σ0j : Equiv.Perm VType :=
        e.trans ((Equiv.prodCongr (Equiv.swap ⟨0, hm1_pos⟩ j) (Equiv.refl (Fin k))).trans e.symm)
      have hσ0j : ∀ t : Fin k, σ0j (e.symm (⟨0, hm1_pos⟩, t)) = e.symm (j, t) := by
        intro t
        simp [σ0j]
      have hmap0j : (Q ⟨0, hm1_pos⟩).map σ0j.toEmbedding = Q j := by
        ext v
        simp only [Q, mem_map, mem_univ, true_and, Equiv.toEmbedding_apply]
        constructor
        · rintro ⟨w, ⟨t, hw⟩, rfl⟩
          change e.symm (⟨0, hm1_pos⟩, t) = w at hw
          rw [← hw]
          exact ⟨t, by change e.symm (j, t) = σ0j (e.symm (⟨0, hm1_pos⟩, t)); exact (hσ0j t).symm⟩
        · rintro ⟨t, rfl⟩
          exact ⟨e.symm (⟨0, hm1_pos⟩, t), ⟨t, rfl⟩,
            by change σ0j (e.symm (⟨0, hm1_pos⟩, t)) = e.symm (j, t); exact hσ0j t⟩
      refine Finset.card_bij (fun π _ => π * σ0j) ?_ ?_ ?_
      · intro π hπ
        simp only [mem_filter, mem_univ, true_and] at hπ ⊢
        calc (Q ⟨0, hm1_pos⟩).map (π * σ0j).toEmbedding
          _ = ((Q ⟨0, hm1_pos⟩).map σ0j.toEmbedding).map π.toEmbedding := by
              ext y
              simp only [mem_map, Equiv.toEmbedding_apply, Equiv.Perm.mul_apply]
              constructor
              · rintro ⟨x, hx, rfl⟩; exact ⟨σ0j x, ⟨x, hx, rfl⟩, rfl⟩
              · rintro ⟨a, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
          _ = (Q j).map π.toEmbedding := by rw [hmap0j]
          _ = Q ⟨0, hm1_pos⟩ := hπ
      · intro π₁ _ π₂ _ h
        exact mul_right_cancel h
      · intro π' hπ'
        simp only [mem_filter, mem_univ, true_and] at hπ'
        refine ⟨π' * σ0j⁻¹, ?_, by simp⟩
        simp only [mem_filter, mem_univ, true_and]
        calc (Q j).map (π' * σ0j⁻¹).toEmbedding
          _ = ((Q j).map σ0j⁻¹.toEmbedding).map π'.toEmbedding := by
              ext y
              simp only [mem_map, Equiv.toEmbedding_apply, Equiv.Perm.mul_apply]
              constructor
              · rintro ⟨x, hx, rfl⟩; exact ⟨σ0j⁻¹ x, ⟨x, hx, rfl⟩, rfl⟩
              · rintro ⟨a, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
          _ = (Q ⟨0, hm1_pos⟩).map π'.toEmbedding := by
              rw [← hmap0j]
              congr 1
              ext y
              simp only [mem_map, Equiv.toEmbedding_apply]
              constructor
              · rintro ⟨a, ⟨x, hx, rfl⟩, rfl⟩; simpa using hx
              · intro hy; exact ⟨σ0j y, ⟨y, hy, rfl⟩, by simp⟩
          _ = Q ⟨0, hm1_pos⟩ := hπ'
    exact h1.trans h2
  have hsum_c : M.choose k * c = Fintype.card (Equiv.Perm VType) := by
    have hpart : (Finset.univ : Finset (Equiv.Perm VType)).card =
        ∑ S ∈ (Finset.univ : Finset VType).powersetCard k,
          ((Finset.univ : Finset (Equiv.Perm VType)).filter
            (fun π => (Q ⟨0, hm1_pos⟩).map π.toEmbedding = S)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext π
        simp only [mem_univ, mem_biUnion, mem_filter, mem_powersetCard, subset_univ, true_and,
          true_iff]
        exact ⟨(Q ⟨0, hm1_pos⟩).map π.toEmbedding, by simp [hQ_card], rfl⟩
      · intro S₁ _ S₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro π h1 h2
        simp only [mem_filter] at h1 h2
        exact hne (h1.2.symm.trans h2.2)
    rw [Finset.card_univ] at hpart
    have hsum_eq : ∑ S ∈ (Finset.univ : Finset VType).powersetCard k,
        ((Finset.univ : Finset (Equiv.Perm VType)).filter
          (fun π => (Q ⟨0, hm1_pos⟩).map π.toEmbedding = S)).card = M.choose k * c := by
      calc ∑ S ∈ (Finset.univ : Finset VType).powersetCard k,
            ((Finset.univ : Finset (Equiv.Perm VType)).filter
              (fun π => (Q ⟨0, hm1_pos⟩).map π.toEmbedding = S)).card
        _ = ∑ _S ∈ (Finset.univ : Finset VType).powersetCard k, c :=
            Finset.sum_congr rfl fun S hS => hc_val ⟨0, hm1_pos⟩ S hS
        _ = ((Finset.univ : Finset VType).powersetCard k).card * c := by
            rw [Finset.sum_const, smul_eq_mul]
        _ = M.choose k * c := by
            rw [Finset.card_powersetCard, Finset.card_univ, hVType_card]
    linarith
  have hdouble : Fintype.card (Equiv.Perm VType) ≤ m1 * goodV.card * c := by
    have h1 : Fintype.card (Equiv.Perm VType) ≤
        ∑ π : Equiv.Perm VType,
          ((Finset.univ : Finset (Fin m1)).filter (fun j => 0 ≤ w ((Q j).map π.toEmbedding))).card := by
      calc Fintype.card (Equiv.Perm VType)
        _ = ∑ _π : Equiv.Perm VType, 1 := by simp
        _ ≤ ∑ π : Equiv.Perm VType,
              ((Finset.univ : Finset (Fin m1)).filter (fun j => 0 ≤ w ((Q j).map π.toEmbedding))).card :=
            Finset.sum_le_sum fun π _ => hex_good_j π
    have h2 : ∑ π : Equiv.Perm VType,
          ((Finset.univ : Finset (Fin m1)).filter (fun j => 0 ≤ w ((Q j).map π.toEmbedding))).card =
        ∑ j : Fin m1,
          ((Finset.univ : Finset (Equiv.Perm VType)).filter
            (fun π => (Q j).map π.toEmbedding ∈ goodV)).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun π _ => ?_
      have hmem : (Q j).map π.toEmbedding ∈ (Finset.univ : Finset VType).powersetCard k :=
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by simp [hQ_card]⟩
      simp [goodV, hmem]
    have h3 : ∀ j : Fin m1,
        ((Finset.univ : Finset (Equiv.Perm VType)).filter
          (fun π => (Q j).map π.toEmbedding ∈ goodV)).card = goodV.card * c := by
      intro j
      have hpart : (Finset.univ : Finset (Equiv.Perm VType)).filter
            (fun π => (Q j).map π.toEmbedding ∈ goodV) =
          goodV.biUnion (fun S => (Finset.univ : Finset (Equiv.Perm VType)).filter
            (fun π => (Q j).map π.toEmbedding = S)) := by
        ext π; simp
      rw [hpart, Finset.card_biUnion]
      · calc ∑ S ∈ goodV, ((Finset.univ : Finset (Equiv.Perm VType)).filter
              (fun π => (Q j).map π.toEmbedding = S)).card
          _ = ∑ _S ∈ goodV, c :=
              Finset.sum_congr rfl fun S hS => hc_val j S (Finset.mem_filter.mp hS).1
          _ = goodV.card * c := by rw [Finset.sum_const, smul_eq_mul]
      · intro S₁ _ S₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro π h1 h2
        simp only [mem_filter] at h1 h2
        exact hne (h1.2.symm.trans h2.2)
    rw [h2] at h1
    simp_rw [h3, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    linarith [show m1 * (goodV.card * c) = m1 * goodV.card * c by ring]
  have hperm_pos : 0 < Fintype.card (Equiv.Perm VType) := Fintype.card_pos
  have hc_pos : 0 < c := by
    by_contra hc0
    have : c = 0 := by omega
    rw [this, mul_zero] at hsum_c
    omega
  have hchoose_le : M.choose k ≤ m1 * goodV.card := by
    have hmul : M.choose k * c ≤ (m1 * goodV.card) * c := by
      rw [hsum_c]
      exact hdouble
    exact Nat.le_of_mul_le_mul_right hmul hc_pos
  have hM_succ : (M - 1).choose (k - 1) ≤ goodV.card := by
    have hsucc := Nat.choose_succ_right_eq M (k - 1)
    have hk1 : (k - 1) + 1 = k := by omega
    have hM1 : M - (k - 1) = M - k + 1 := by omega
    have hadd := Nat.add_one_mul_choose_eq (M - 1) (k - 1)
    have hMeq : (M - 1) + 1 = M := by omega
    rw [hMeq, hk1] at hadd
    -- hadd : M * (M - 1).choose (k - 1) = M.choose k * k
    have hmul_le : m1 * k * (M - 1).choose (k - 1) ≤ m1 * k * goodV.card := by
      calc m1 * k * (M - 1).choose (k - 1)
        _ = M * (M - 1).choose (k - 1) := by rw [mul_comm m1 k, ← hM_eq]
        _ = M.choose k * k := hadd
        _ ≤ (m1 * goodV.card) * k := Nat.mul_le_mul_right k hchoose_le
        _ = m1 * k * goodV.card := by ring
    exact Nat.le_of_mul_le_mul_left hmul_le (by positivity)
  have hV_good_ge : goodV.card ≤
      (((Finset.univ : Finset (Fin n)).powersetCard k).filter
        (fun S => Disjoint S T ∧ 0 ≤ bsum x S)).card := by
    refine Finset.card_le_card_of_injOn
      (fun S : Finset VType => S.map ⟨Subtype.val, Subtype.val_injective⟩) ?_ ?_
    · intro S hS
      simp only [Finset.mem_coe, goodV, mem_filter, mem_powersetCard, subset_univ, true_and] at hS ⊢
      refine ⟨by simp [hS.1], ?_, ?_⟩
      · rw [Finset.disjoint_left]
        intro v hv hvT
        simp only [mem_map, Function.Embedding.coeFn_mk] at hv
        obtain ⟨u, _, rfl⟩ := hv
        exact (Finset.mem_sdiff.mp u.2).2 (hTU hvT)
      · rw [bsum, Finset.sum_map]
        exact hS.2
    · intro S₁ _ S₂ _ h
      exact Finset.map_injective ⟨Subtype.val, Subtype.val_injective⟩ h
  have hM_ge : n - 2 * k ≤ M - 1 := by
    dsimp only [M]; rw [hVcard]; omega
  have hch_ge : (n - 2 * k).choose (k - 1) ≤ (M - 1).choose (k - 1) :=
    Nat.choose_le_choose _ hM_ge
  have hcount_nat : (n - 2 * k).choose (k - 1) ≤
      (((Finset.univ : Finset (Fin n)).powersetCard k).filter
        (fun S => Disjoint S T ∧ 0 ≤ bsum x S)).card :=
    le_trans hch_ge (le_trans hM_succ hV_good_ge)
  have hsub := choose_sub_ge hk (show 2 * k - 1 ≤ n - k by omega) (by omega)
  have hneq : n - 1 - (2 * k - 1) = n - 2 * k := by omega
  rw [hneq] at hsub
  exact le_trans hsub (by exact_mod_cast hcount_nat)

private lemma main_antitone {n k : ℕ} (hk : 2 ≤ k) (hn : 8 * k ^ 2 ≤ n) {x : Fin n → ℝ}
    (hx : Antitone x) (hx0 : ∑ i, x i = 0) :
    (n - 1).choose (k - 1) ≤ nonnegSubsetCount n k x := by
  have hk_le : k ≤ n := by nlinarith
  have h2k_le : 2 * k - 1 ≤ n := by
    have : 2 * k ≤ n := by nlinarith
    omega
  let fA : Fin k ↪ Fin n := ⟨fun j => ⟨j.val, by omega⟩, fun a b h => Fin.ext (Fin.mk.inj h)⟩
  let A : Finset (Fin n) := (Finset.univ : Finset (Fin k)).map fA
  have hA_def : ∀ _ : k ≤ n, A = (Finset.univ : Finset (Fin k)).map fA := fun _ => rfl
  have hA_card : A.card = k := by simp [A]
  have hA_mem : ∀ v : Fin n, v ∈ A ↔ v.val < k := by
    intro v
    simp only [A, fA, mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and]
    constructor
    · rintro ⟨j, rfl⟩; exact j.isLt
    · intro hv; exact ⟨⟨v.val, hv⟩, Fin.ext rfl⟩
  let gC : Fin k → Fin n := fun j => if j.val = 0 then ⟨0, by omega⟩ else ⟨k - 1 + j.val, by omega⟩
  have hgC_inj : Function.Injective gC := by
    intro a b h
    dsimp only [gC] at h
    split_ifs at h with ha hb hb
    · exact Fin.ext (by omega)
    · have : (0 : ℕ) = k - 1 + b.val := congrArg Fin.val h; omega
    · have : k - 1 + a.val = 0 := congrArg Fin.val h; omega
    · have : k - 1 + a.val = k - 1 + b.val := congrArg Fin.val h; exact Fin.ext (by omega)
  let C : Finset (Fin n) := (Finset.univ : Finset (Fin k)).map ⟨gC, hgC_inj⟩
  have hC_card : C.card = k := by simp [C]
  have hAC : A ∩ C = {⟨0, by omega⟩} := by
    ext v
    simp only [mem_inter, hA_mem, mem_singleton, C, mem_map, mem_univ,
      Function.Embedding.coeFn_mk, true_and]
    constructor
    · rintro ⟨hvA, ⟨j, rfl⟩⟩
      dsimp only [gC] at hvA ⊢
      split_ifs at hvA ⊢ with hj
      · rfl
      · change k - 1 + j.val < k at hvA
        omega
    · rintro rfl
      refine ⟨by change 0 < k; omega, ⟨0, by omega⟩, ?_⟩
      simp [gC]
  have hmaxA : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, bsum x S ≤ bsum x A := by
    intro S hS
    exact bsum_le_A hx A hA_def hk_le (Finset.mem_powersetCard.mp hS).2
  have hmaxC : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      (S ∩ A).card = 1 → bsum x S ≤ bsum x C := by
    intro S hS hSA
    exact bsum_le_C hk h2k_le hx A C hA_mem gC (fun _ => rfl) hgC_inj rfl
      (Finset.mem_powersetCard.mp hS).2 hSA
  by_cases hbA : bsum x A ≤ 0
  · have hall0 : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, 0 ≤ bsum x S := by
      have htot := sum_powersetCard_bsum (by omega : 1 ≤ k) hk_le x
      rw [hx0, mul_zero] at htot
      intro S hS
      by_contra hlt
      push Not at hlt
      have hsub_le : ∀ T ∈ ((Finset.univ : Finset (Fin n)).powersetCard k).erase S,
          bsum x T ≤ 0 := fun T hT =>
        le_trans (hmaxA T (Finset.mem_erase.mp hT).2) hbA
      have hsum_er := Finset.add_sum_erase ((Finset.univ : Finset (Fin n)).powersetCard k) (bsum x) hS
      have hsum_neg : bsum x S + ∑ T ∈ ((Finset.univ : Finset (Fin n)).powersetCard k).erase S, bsum x T < 0 := by
        have h1 : ∑ T ∈ ((Finset.univ : Finset (Fin n)).powersetCard k).erase S, bsum x T ≤ 0 :=
          Finset.sum_nonpos hsub_le
        linarith
      linarith
    have hcount : nonnegSubsetCount n k x = n.choose k := by
      unfold nonnegSubsetCount
      simp only [bsum] at hall0
      rw [Finset.filter_true_of_mem hall0, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rw [hcount]
    have hch : n.choose k = (n - 1).choose (k - 1) + (n - 1).choose k := by
      have h := Nat.choose_succ_succ (n - 1) (k - 1)
      have hn_eq : n - 1 + 1 = n := by omega
      have hk_eq : k - 1 + 1 = k := by omega
      simp only [Nat.succ_eq_add_one] at h
      rw [hn_eq, hk_eq] at h
      omega
    omega
  · push Not at hbA
    let z : Fin n := ⟨0, by omega⟩
    by_cases hcase1 : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, z ∈ S → 0 ≤ bsum x S
    · have hbij : ((Finset.univ.erase z).powersetCard (k - 1)).card ≤ nonnegSubsetCount n k x := by
        unfold nonnegSubsetCount
        refine Finset.card_le_card_of_injOn (fun T => insert z T) ?_ ?_
        · intro T hT
          have hT' := Finset.mem_powersetCard.mp hT
          have hTe := Finset.subset_erase.mp hT'.1
          have hmem : insert z T ∈ (Finset.univ : Finset (Fin n)).powersetCard k := by
            simp only [mem_powersetCard, subset_univ, true_and]
            rw [Finset.card_insert_of_notMem hTe.2, hT'.2]
            omega
          exact Finset.mem_filter.mpr ⟨hmem, hcase1 _ hmem (Finset.mem_insert_self _ _)⟩
        · intro T₁ h₁ T₂ h₂ heq
          have h1e := Finset.subset_erase.mp (Finset.mem_powersetCard.mp h₁).1
          have h2e := Finset.subset_erase.mp (Finset.mem_powersetCard.mp h₂).1
          have := congrArg (fun S => S.erase z) heq
          simpa [Finset.erase_insert h1e.2, Finset.erase_insert h2e.2] using this
      rw [Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ z),
        Finset.card_univ, Fintype.card_fin] at hbij
      exact hbij
    · push Not at hcase1
      obtain ⟨T, hT_mem, hzT, hbT⟩ := hcase1
      by_contra hlt_cnt
      push Not at hlt_cnt
      have hle_cnt : nonnegSubsetCount n k x ≤ (n - 1).choose (k - 1) := by omega
      have h1 := count_zero_ge hk hn hx hx0 A C hA_card hC_card hAC hbA hmaxA hmaxC hle_cnt
      have h2 := count_disjoint_T_ge hk (by nlinarith) x hx0 T (Finset.mem_powersetCard.mp hT_mem).2 hbT
      let S0 := ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => z ∈ S ∧ 0 ≤ bsum x S)
      let ST := ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => Disjoint S T ∧ 0 ≤ bsum x S)
      have hdisj : Disjoint S0 ST := by
        rw [Finset.disjoint_left]
        intro S hS0 hST
        simp only [S0, ST, mem_filter] at hS0 hST
        exact Finset.disjoint_left.mp hST.2.1 hS0.2.1 hzT
      have hunion : S0.card + ST.card ≤ nonnegSubsetCount n k x := by
        rw [← Finset.card_union_of_disjoint hdisj]
        unfold nonnegSubsetCount
        refine Finset.card_le_card fun S hS => ?_
        rcases Finset.mem_union.mp hS with hS | hS
        · simp only [S0, mem_filter] at hS
          exact Finset.mem_filter.mpr ⟨hS.1, hS.2.2⟩
        · simp only [ST, mem_filter] at hS
          exact Finset.mem_filter.mpr ⟨hS.1, hS.2.2⟩
      have hsum_real : (2 - (((8 * k - 4 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
          ((n - 1).choose (k - 1) : ℝ) ≤ (nonnegSubsetCount n k x : ℝ) := by
        have h8k4 : (((8 * k - 4 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) =
            (((6 * k - 3 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) +
              (((2 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) := by
          have hcast : ((8 * k - 4 : ℕ) : ℝ) = ((6 * k - 3 : ℕ) : ℝ) + ((2 * k - 1 : ℕ) : ℝ) := by
            have : 8 * k - 4 = (6 * k - 3) + (2 * k - 1) := by omega
            exact_mod_cast this
          rw [hcast]; ring
        have hunionR : (S0.card : ℝ) + (ST.card : ℝ) ≤ (nonnegSubsetCount n k x : ℝ) := by
          exact_mod_cast hunion
        have h1' : (1 - (((6 * k - 3 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
            ((n - 1).choose (k - 1) : ℝ) ≤ (S0.card : ℝ) := h1
        have h2' : (1 - (((2 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ)) *
            ((n - 1).choose (k - 1) : ℝ) ≤ (ST.card : ℝ) := h2
        rw [h8k4]
        linarith [h1', h2', hunionR]
      have hstrict : (((8 * k - 4 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) < 1 := by
        have hD_pos : (0 : ℝ) < ((n - 2 * k + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 0 < n - 2 * k + 1 by omega)
        rw [div_lt_one hD_pos]
        exact_mod_cast (show (8 * k - 4) * (k - 1) < n - 2 * k + 1 by
          have h2k : 2 * k ≤ n := by nlinarith
          zify [show 4 ≤ 8 * k by omega, show 1 ≤ k by omega, h2k]
          have hnZ : 8 * (k : ℤ) ^ 2 ≤ (n : ℤ) := by exact_mod_cast hn
          nlinarith)
      have hch_pos : (0 : ℝ) < ((n - 1).choose (k - 1) : ℝ) := by
        exact_mod_cast Nat.choose_pos (by omega : k - 1 ≤ n - 1)
      have hgt : ((n - 1).choose (k - 1) : ℝ) < (nonnegSubsetCount n k x : ℝ) := by
        have h1lt : 1 < 2 - (((8 * k - 4 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ)) / ((n - 2 * k + 1 : ℕ) : ℝ) := by
          linarith
        nlinarith
      have hleR : (nonnegSubsetCount n k x : ℝ) ≤ ((n - 1).choose (k - 1) : ℝ) := by
        exact_mod_cast hle_cnt
      linarith

end OMA.MMSQuadratic

theorem OMA.solution :
    OMA.R_ManickamMiklosSinghiConjecture_manickam_miklos_singhi_conjecture_variants_pokrovskiy_R1.H1 := by
  intro n k hk hn x hx
  by_cases hk1 : k = 1
  · subst hk1
    exact ManickamMiklosSinghiConjecture.manickam_miklos_singhi_conjecture.variants.one
      n (by omega) x hx
  · have hk2 : 2 ≤ k := by omega
    obtain ⟨σ, hσ⟩ := OMA.MMSQuadratic.exists_antitone_perm x
    have hx' : ∑ i, (x ∘ σ) i = 0 := by
      simpa [Function.comp_apply] using (Equiv.sum_comp σ x).trans hx
    rw [← OMA.MMSQuadratic.nonnegSubsetCount_comp_perm x σ]
    exact OMA.MMSQuadratic.main_antitone hk2 hn hσ hx'
