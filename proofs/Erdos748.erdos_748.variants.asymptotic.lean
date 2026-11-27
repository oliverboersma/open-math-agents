import FormalConjectures.ErdosProblems.«748»
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Combinatorics.Additive.VerySmallDoubling

/-!
# Asymptotic count of sum-free subsets of `{1, ..., n}` (Erdős Problem #748 / Green / Sapozhenko)

Complete self-contained proof of `Erdos748.erdos_748.variants.asymptotic`:
1. Exact decomposition into `oddFamily`, `highFamily`, and `exceptFamily`, with exact parity-wise
   limits for `oddFamily` and `highFamily` (via finite-window shift + exponential decay of `w(d)`)
   and exponential decay of `oddFamily ∩ highFamily`.
2. Elementary 2-stage Kleitman-Winston hypergraph container theorem for Schur triples.
3. Sum-free removal lemma via Mathlib's `SimpleGraph.triangle_removal` (Král-Serra-Vena graph).
4. Exact sum-free stability via Mathlib's `Finset.card_mul_finset_lt_two` (`VerySmallDoubling`)
   and disjoint-pair counting of exceptional sum-free sets inside structured containers.
-/

namespace Erdos748Asymp

section Mod1
open Filter Real Finset
open scoped Classical

noncomputable def sfFamily (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter fun A : Finset ℕ ↦ IsSumFree (A : Set ℕ)

def oddSet (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter Odd

noncomputable def oddFamily (n : ℕ) : Finset (Finset ℕ) :=
  (sfFamily n).filter fun A ↦ A ⊆ oddSet n

noncomputable def highFamily (n : ℕ) : Finset (Finset ℕ) :=
  (sfFamily n).filter fun A ↦ ∀ x ∈ A, n / 3 < x

noncomputable def exceptFamily (n : ℕ) : Finset (Finset ℕ) :=
  (sfFamily n) \ (oddFamily n ∪ highFamily n)

lemma sfFamily_card (n : ℕ) : (sfFamily n).card = Erdos748.f n := rfl

lemma card_decomp (n : ℕ) :
    Erdos748.f n + (oddFamily n ∩ highFamily n).card =
      (oddFamily n).card + (highFamily n).card + (exceptFamily n).card := by
  have hsub : oddFamily n ∪ highFamily n ⊆ sfFamily n :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have h1 : (oddFamily n ∪ highFamily n).card + (exceptFamily n).card = (sfFamily n).card := by
    rw [exceptFamily, add_comm, Finset.card_sdiff_add_card_eq_card hsub]
  have h2 := Finset.card_union_add_card_inter (oddFamily n) (highFamily n)
  rw [sfFamily_card] at h1
  omega

lemma oddSet_card (n : ℕ) : (oddSet n).card = (n + 1) / 2 := by
  have hbij : oddSet n = (Finset.range ((n + 1) / 2)).image (fun k ↦ 2 * k + 1) := by
    ext x
    simp only [oddSet, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨k, hk⟩⟩
      exact ⟨k, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨k, rfl⟩⟩
  rw [hbij, Finset.card_image_of_injective _ (fun a b h ↦ by omega), Finset.card_range]

lemma oddFamily_eq_powerset (n : ℕ) : oddFamily n = (oddSet n).powerset := by
  apply Finset.ext
  intro A
  rw [oddFamily, sfFamily, Finset.mem_filter, Finset.mem_filter,
    Finset.mem_powerset, Finset.mem_powerset]
  constructor
  · exact fun h ↦ h.2
  · intro hA
    refine ⟨⟨fun x hx ↦ (Finset.mem_filter.mp (hA hx)).1, ?_⟩, hA⟩
    rw [isSumFree_iff]
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp (hA (Finset.mem_coe.mp hx))).2
    have hy' := (Finset.mem_filter.mp (hA (Finset.mem_coe.mp hy))).2
    have hxy' := (Finset.mem_filter.mp (hA (Finset.mem_coe.mp hxy))).2
    obtain ⟨a, ha⟩ := hx'
    obtain ⟨b, hb⟩ := hy'
    obtain ⟨c, hc⟩ := hxy'
    omega

lemma oddFamily_card (n : ℕ) : (oddFamily n).card = 2 ^ ((n + 1) / 2) := by
  rw [oddFamily_eq_powerset, Finset.card_powerset, oddSet_card]

lemma odd_inter_high_card_le (n : ℕ) :
    (oddFamily n ∩ highFamily n).card ≤ 2 ^ (n / 3 + 3) := by
  have hsub : oddFamily n ∩ highFamily n ⊆ ((oddSet n).filter (fun x ↦ n / 3 < x)).powerset := by
    intro A hA
    rw [Finset.mem_inter] at hA
    rw [Finset.mem_powerset]
    intro x hx
    rw [Finset.mem_filter]
    exact ⟨(Finset.mem_filter.mp hA.1).2 hx, (Finset.mem_filter.mp hA.2).2 x hx⟩
  have hcard_set : ((oddSet n).filter (fun x ↦ n / 3 < x)).card ≤ n / 3 + 3 := by
    have himg : (oddSet n).filter (fun x ↦ n / 3 < x) ⊆
        (Finset.Icc ((n / 3) / 2) ((n + 1) / 2)).image (fun k ↦ 2 * k + 1) := by
      intro x hx
      simp only [oddSet, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image] at hx ⊢
      obtain ⟨⟨⟨h1, h2⟩, ⟨k, hk⟩⟩, h3⟩ := hx
      exact ⟨k, ⟨by omega, by omega⟩, by omega⟩
    have hdiv6 : (n / 3) / 2 = n / 6 := Nat.div_div_eq_div_mul n 3 2
    calc ((oddSet n).filter (fun x ↦ n / 3 < x)).card
        ≤ ((Finset.Icc ((n / 3) / 2) ((n + 1) / 2)).image (fun k ↦ 2 * k + 1)).card :=
          Finset.card_le_card himg
      _ ≤ (Finset.Icc ((n / 3) / 2) ((n + 1) / 2)).card := Finset.card_image_le
      _ = (n + 1) / 2 + 1 - (n / 3) / 2 := Nat.card_Icc _ _
      _ = (n + 1) / 2 + 1 - n / 6 := by rw [hdiv6]
      _ ≤ n / 3 + 3 := by omega
  calc (oddFamily n ∩ highFamily n).card
      ≤ (((oddSet n).filter (fun x ↦ n / 3 < x)).powerset).card := Finset.card_le_card hsub
    _ = 2 ^ ((oddSet n).filter (fun x ↦ n / 3 < x)).card := Finset.card_powerset _
    _ ≤ 2 ^ (n / 3 + 3) := Nat.pow_le_pow_right (by norm_num) hcard_set

lemma tendsto_odd_inter_high_zero :
    Tendsto (fun n : ℕ ↦ ((oddFamily n ∩ highFamily n).card : ℝ) / (2 : ℝ) ^ ((n : ℝ) / 2))
      atTop (nhds 0) := by
  have hbase : (2 : ℝ) ^ (-(1 / 6 : ℝ)) < 1 := by
    have : (2 : ℝ) ^ (-(1 / 6 : ℝ)) < (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
    simpa using this
  have hgeom : Tendsto (fun n : ℕ ↦ (8 : ℝ) * ((2 : ℝ) ^ (-(1 / 6 : ℝ))) ^ n) atTop (nhds 0) := by
    have h0 : Tendsto (fun n : ℕ ↦ ((2 : ℝ) ^ (-(1 / 6 : ℝ))) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hbase
    simpa using h0.const_mul (8 : ℝ)
  refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) hgeom
  have hle : ((oddFamily n ∩ highFamily n).card : ℝ) ≤ (2 : ℝ) ^ ((n / 3 + 3 : ℕ) : ℝ) := by
    have h := odd_inter_high_card_le n
    rw [Real.rpow_natCast]
    exact_mod_cast h
  have hexp : ((n / 3 + 3 : ℕ) : ℝ) - (n : ℝ) / 2 ≤ 3 - (n : ℝ) / 6 := by
    have h3 : (3 * (n / 3) : ℕ) ≤ n := Nat.mul_div_le n 3
    have h3' : 3 * ((n / 3 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h3
    push_cast
    linarith
  calc ((oddFamily n ∩ highFamily n).card : ℝ) / (2 : ℝ) ^ ((n : ℝ) / 2)
      ≤ (2 : ℝ) ^ ((n / 3 + 3 : ℕ) : ℝ) / (2 : ℝ) ^ ((n : ℝ) / 2) := by gcongr
    _ = (2 : ℝ) ^ (((n / 3 + 3 : ℕ) : ℝ) - (n : ℝ) / 2) :=
        (Real.rpow_sub (by norm_num) _ _).symm
    _ ≤ (2 : ℝ) ^ (3 - (n : ℝ) / 6) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = (2 : ℝ) ^ (3 : ℝ) * (2 : ℝ) ^ (-(n : ℝ) / 6) := by
        rw [sub_eq_add_neg, Real.rpow_add (by norm_num)]; ring_nf
    _ = (8 : ℝ) * ((2 : ℝ) ^ (-(1 / 6 : ℝ))) ^ n := by
        congr 1
        · norm_num
        · rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          congr 1; ring

/- ### Exact `validPairs` bijection and exponential decay of `w(d)` -/

def validPairs (d : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((Finset.Icc 0 d).powerset ×ˢ (Finset.Icc 0 d).powerset).filter fun p ↦
    0 ∈ p.1 ∧ ∀ x ∈ p.1, ∀ y ∈ p.1, x + y ∉ p.2

noncomputable def w (d : ℕ) : ℝ :=
  ((validPairs d).card : ℝ) / (2 : ℝ) ^ ((3 * d : ℝ) / 2 + 1)

lemma w_nonneg (d : ℕ) : 0 ≤ w d := by
  unfold w; positivity

/-- Auxiliary `noLR` strings of length `ℓ` over `Fin 3` (`0 = L`, `1 = R`, `2 = N`). -/
def noLR (ℓ : ℕ) : Finset (Fin ℓ → Fin 3) :=
  Finset.univ.filter fun f ↦
    ∀ i : Fin ℓ, ∀ h : i.1 + 1 < ℓ, ¬(f i = 0 ∧ f ⟨i.1 + 1, h⟩ = 1)

def noLR0 (ℓ : ℕ) (hℓ : 0 < ℓ) : Finset (Fin ℓ → Fin 3) :=
  (noLR ℓ).filter fun f ↦ f ⟨ℓ - 1, Nat.sub_lt hℓ Nat.one_pos⟩ = 0

def noLR12 (ℓ : ℕ) (hℓ : 0 < ℓ) : Finset (Fin ℓ → Fin 3) :=
  (noLR ℓ).filter fun f ↦ f ⟨ℓ - 1, Nat.sub_lt hℓ Nat.one_pos⟩ ≠ 0

lemma noLR_card_split (ℓ : ℕ) (hℓ : 0 < ℓ) :
    (noLR ℓ).card = (noLR0 ℓ hℓ).card + (noLR12 ℓ hℓ).card := by
  rw [noLR0, noLR12, Finset.card_filter_add_card_filter_not]

lemma fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  fin_cases x <;> simp

def extFin3 {ℓ : ℕ} (g : Fin ℓ → Fin 3) (c : Fin 3) (i : Fin (ℓ + 1)) : Fin 3 :=
  if h : i.1 < ℓ then g ⟨i.1, h⟩ else c

lemma noLR_step (ℓ : ℕ) (hℓ : 0 < ℓ) :
    (noLR0 (ℓ + 1) (Nat.succ_pos ℓ)).card = (noLR0 ℓ hℓ).card + (noLR12 ℓ hℓ).card ∧
    (noLR12 (ℓ + 1) (Nat.succ_pos ℓ)).card = (noLR0 ℓ hℓ).card + 2 * (noLR12 ℓ hℓ).card := by
  have hlast_idx : (⟨(ℓ + 1) - 1, Nat.sub_lt (Nat.succ_pos ℓ) Nat.one_pos⟩ : Fin (ℓ + 1)) =
      Fin.last ℓ := by
    ext; simp
  have ext_at : ∀ (g : Fin ℓ → Fin 3) (c : Fin 3) (i : Fin (ℓ + 1)) (h : i.1 < ℓ),
      extFin3 g c i = g ⟨i.1, h⟩ := by
    intro g c i h; simp [extFin3, h]
  have ext_end : ∀ (g : Fin ℓ → Fin 3) (c : Fin 3) (i : Fin (ℓ + 1)),
      i.1 = ℓ → extFin3 g c i = c := by
    intro g c i h; simp [extFin3, h]
  have h1 : (noLR0 (ℓ + 1) (Nat.succ_pos ℓ)).card = (noLR ℓ).card := by
    refine Finset.card_bij (fun f _ ↦ fun i : Fin ℓ ↦ f i.castSucc) ?_ ?_ ?_
    · intro f hf
      simp only [noLR0, noLR, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      intro i hi
      have h' : i.castSucc.1 + 1 < ℓ + 1 := by simp
      exact hf.1 i.castSucc h'
    · intro f₁ hf₁ f₂ hf₂ heq
      simp only [noLR0, Finset.mem_filter] at hf₁ hf₂
      funext i
      by_cases hi : i.1 < ℓ
      · exact congr_fun heq ⟨i.1, hi⟩
      · have hi' : i = ⟨(ℓ + 1) - 1, Nat.sub_lt (Nat.succ_pos ℓ) Nat.one_pos⟩ := by
          ext; simp; omega
        rw [hi', hf₁.2, hf₂.2]
    · intro g hg
      simp only [noLR, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      refine ⟨extFin3 g 0, ?_, ?_⟩
      · simp only [noLR0, noLR, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, by rw [hlast_idx]; exact ext_end g 0 _ (by simp)⟩
        intro i hi
        by_cases hlt : i.1 + 1 < ℓ
        · rw [ext_at g 0 i (by omega), ext_at g 0 ⟨i.1 + 1, hi⟩ hlt]
          exact hg ⟨i.1, by omega⟩ hlt
        · rw [ext_end g 0 ⟨i.1 + 1, hi⟩ (by dsimp; omega)]
          rintro ⟨_, h01⟩
          exact absurd h01 (by decide)
      · funext i; exact ext_at g 0 i.castSucc i.2
  have h2a : ((noLR (ℓ + 1)).filter (fun f ↦ f (Fin.last ℓ) = 2)).card = (noLR ℓ).card := by
    refine Finset.card_bij (fun f _ ↦ fun i : Fin ℓ ↦ f i.castSucc) ?_ ?_ ?_
    · intro f hf
      simp only [noLR, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      intro i hi
      have h' : i.castSucc.1 + 1 < ℓ + 1 := by simp
      exact hf.1 i.castSucc h'
    · intro f₁ hf₁ f₂ hf₂ heq
      simp only [Finset.mem_filter] at hf₁ hf₂
      funext i
      by_cases hi : i.1 < ℓ
      · exact congr_fun heq ⟨i.1, hi⟩
      · have hi' : i = Fin.last ℓ := by ext; simp; omega
        rw [hi', hf₁.2, hf₂.2]
    · intro g hg
      simp only [noLR, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      refine ⟨extFin3 g 2, ?_, ?_⟩
      · simp only [noLR, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ext_end g 2 _ (by simp)⟩
        intro i hi
        by_cases hlt : i.1 + 1 < ℓ
        · rw [ext_at g 2 i (by omega), ext_at g 2 ⟨i.1 + 1, hi⟩ hlt]
          exact hg ⟨i.1, by omega⟩ hlt
        · rw [ext_end g 2 ⟨i.1 + 1, hi⟩ (by dsimp; omega)]
          rintro ⟨_, h21⟩
          exact absurd h21 (by decide)
      · funext i; exact ext_at g 2 i.castSucc i.2
  have h2b : ((noLR (ℓ + 1)).filter (fun f ↦ f (Fin.last ℓ) = 1)).card = (noLR12 ℓ hℓ).card := by
    refine Finset.card_bij (fun f _ ↦ fun i : Fin ℓ ↦ f i.castSucc) ?_ ?_ ?_
    · intro f hf
      simp only [noLR12, noLR, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      refine ⟨fun i hi ↦ hf.1 i.castSucc (by simp), ?_⟩
      intro h0
      have hlt : (⟨ℓ - 1, Nat.sub_lt hℓ Nat.one_pos⟩ : Fin ℓ).castSucc.1 + 1 < ℓ + 1 := by
        simp; omega
      have hbad := hf.1 (⟨ℓ - 1, Nat.sub_lt hℓ Nat.one_pos⟩ : Fin ℓ).castSucc hlt
      have heq2 : (⟨(⟨ℓ - 1, Nat.sub_lt hℓ Nat.one_pos⟩ : Fin ℓ).castSucc.1 + 1, hlt⟩ : Fin (ℓ + 1)) =
          Fin.last ℓ := by ext; simp; omega
      rw [heq2] at hbad
      exact hbad ⟨h0, hf.2⟩
    · intro f₁ hf₁ f₂ hf₂ heq
      simp only [Finset.mem_filter] at hf₁ hf₂
      funext i
      by_cases hi : i.1 < ℓ
      · exact congr_fun heq ⟨i.1, hi⟩
      · have hi' : i = Fin.last ℓ := by ext; simp; omega
        rw [hi', hf₁.2, hf₂.2]
    · intro g hg
      simp only [noLR12, noLR, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      refine ⟨extFin3 g 1, ?_, ?_⟩
      · simp only [noLR, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ext_end g 1 _ (by simp)⟩
        intro i hi
        by_cases hlt : i.1 + 1 < ℓ
        · rw [ext_at g 1 i (by omega), ext_at g 1 ⟨i.1 + 1, hi⟩ hlt]
          exact hg.1 ⟨i.1, by omega⟩ hlt
        · rw [ext_at g 1 i (by omega)]
          have heqi : (⟨i.1, by omega⟩ : Fin ℓ) = ⟨ℓ - 1, Nat.sub_lt hℓ Nat.one_pos⟩ := by
            ext; simp; omega
          rw [heqi]
          rintro ⟨h0, _⟩
          exact hg.2 h0
      · funext i; exact ext_at g 1 i.castSucc i.2
  have hsplit : noLR12 (ℓ + 1) (Nat.succ_pos ℓ) =
      ((noLR (ℓ + 1)).filter (fun f ↦ f (Fin.last ℓ) = 1)) ∪
      ((noLR (ℓ + 1)).filter (fun f ↦ f (Fin.last ℓ) = 2)) := by
    apply Finset.ext
    intro f
    simp only [noLR12, Finset.mem_filter, Finset.mem_union, hlast_idx]
    constructor
    · rintro ⟨hf, hne⟩
      rcases fin3_cases (f (Fin.last ℓ)) with h0 | h1 | h2
      · exact absurd h0 hne
      · exact Or.inl ⟨hf, h1⟩
      · exact Or.inr ⟨hf, h2⟩
    · rintro (⟨hf, h1⟩ | ⟨hf, h2⟩)
      · exact ⟨hf, by rw [h1]; decide⟩
      · exact ⟨hf, by rw [h2]; decide⟩
  have hdisj : Disjoint ((noLR (ℓ + 1)).filter (fun f ↦ f (Fin.last ℓ) = 1))
      ((noLR (ℓ + 1)).filter (fun f ↦ f (Fin.last ℓ) = 2)) := by
    rw [Finset.disjoint_filter]
    intro f _ h1 h2
    rw [h1] at h2
    exact absurd h2 (by decide)
  have h2 : (noLR12 (ℓ + 1) (Nat.succ_pos ℓ)).card =
      (noLR12 ℓ hℓ).card + (noLR ℓ).card := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj, h2a, h2b]
  rw [noLR_card_split ℓ hℓ] at h1 h2
  exact ⟨h1, by omega⟩

lemma noLR_card_le (ℓ : ℕ) (hℓ : 0 < ℓ) :
    ((noLR ℓ).card : ℝ) ≤ (11 / 8 : ℝ) * (11 / 4 : ℝ) ^ ℓ := by
  have hbound : ∀ k : ℕ, 0 < k → ∀ hk : 0 < k,
      ((noLR0 k hk).card : ℝ) ≤ (1 / 2 : ℝ) * (11 / 4 : ℝ) ^ k ∧
      ((noLR12 k hk).card : ℝ) ≤ (7 / 8 : ℝ) * (11 / 4 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => intro h; omega
    | succ m ih =>
      cases m with
      | zero =>
        intro _ hk
        have h0 : (noLR0 1 hk).card = 1 := by
          have : noLR0 1 hk = {fun _ ↦ 0} := by
            apply Finset.ext; intro f
            simp only [noLR0, noLR, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_singleton]
            constructor
            · intro h
              funext i
              have hi : i = ⟨1 - 1, Nat.sub_lt hk Nat.one_pos⟩ := by ext; omega
              rw [hi]; exact h.2
            · rintro rfl
              exact ⟨fun i hi ↦ by omega, rfl⟩
          rw [this, Finset.card_singleton]
        have h12 : (noLR12 1 hk).card = 2 := by
          have : noLR12 1 hk = {fun _ ↦ 1, fun _ ↦ 2} := by
            apply Finset.ext; intro f
            simp only [noLR12, noLR, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_insert, Finset.mem_singleton]
            constructor
            · intro h
              rcases fin3_cases (f ⟨1 - 1, Nat.sub_lt hk Nat.one_pos⟩) with hf0 | hf1 | hf2
              · exact absurd hf0 h.2
              · left; funext i
                have hi : i = ⟨1 - 1, Nat.sub_lt hk Nat.one_pos⟩ := by ext; omega
                rw [hi]; exact hf1
              · right; funext i
                have hi : i = ⟨1 - 1, Nat.sub_lt hk Nat.one_pos⟩ := by ext; omega
                rw [hi]; exact hf2
            · rintro (rfl | rfl)
              · exact ⟨fun i hi ↦ by omega, by simp⟩
              · exact ⟨fun i hi ↦ by omega, by simp⟩
          rw [this, Finset.card_pair]
          intro h
          have := congr_fun h 0
          exact absurd this (by decide)
        rw [h0, h12]
        constructor <;> norm_num
      | succ m =>
        intro _ hk
        have hm : 0 < m + 1 := Nat.succ_pos m
        obtain ⟨ha, hb⟩ := ih hm hm
        obtain ⟨hs1, hs2⟩ := noLR_step (m + 1) hm
        have hs1' : ((noLR0 (m + 2) hk).card : ℝ) =
            ((noLR0 (m + 1) hm).card : ℝ) + ((noLR12 (m + 1) hm).card : ℝ) := by exact_mod_cast hs1
        have hs2' : ((noLR12 (m + 2) hk).card : ℝ) =
            ((noLR0 (m + 1) hm).card : ℝ) + 2 * ((noLR12 (m + 1) hm).card : ℝ) := by
          exact_mod_cast hs2
        rw [hs1', hs2', pow_succ]
        constructor <;> linarith
  obtain ⟨ha, hb⟩ := hbound ℓ hℓ hℓ
  have hsp : ((noLR ℓ).card : ℝ) = ((noLR0 ℓ hℓ).card : ℝ) + ((noLR12 ℓ hℓ).card : ℝ) := by
    exact_mod_cast noLR_card_split ℓ hℓ
  linarith

lemma label3_inj {P₁ P₂ Q₁ Q₂ : Prop} [Decidable P₁] [Decidable P₂] [Decidable Q₁] [Decidable Q₂]
    (hP : ¬(P₁ ∧ P₂)) (hQ : ¬(Q₁ ∧ Q₂))
    (heq : (if P₁ then (0 : Fin 3) else if P₂ then 1 else 2) =
           (if Q₁ then 0 else if Q₂ then 1 else 2)) :
    (P₁ ↔ Q₁) ∧ (P₂ ↔ Q₂) := by
  by_cases h1 : P₁ <;> by_cases h2 : Q₁ <;> by_cases h3 : P₂ <;> by_cases h4 : Q₂ <;>
    simp only [h1, h2, h3, h4, ↓reduceIte] at heq <;>
    first | exact absurd heq (by decide) | tauto

lemma validPairs_card_le (d : ℕ) :
    ((validPairs d).card : ℝ) ≤ (2 + d : ℝ) * (11 / 4 : ℝ) ^ d := by
  let P_empty := (validPairs d).filter fun p ↦ ∀ x ∈ p.1, x = 0 ∨ d / 2 < x
  let P_b (b : ℕ) := (validPairs d).filter fun p ↦
    b ∈ p.1 ∧ ∀ x ∈ p.1, 0 < x → b ≤ x
  have hcover : validPairs d ⊆ P_empty ∪ (Finset.Icc 1 (d / 2)).biUnion P_b := by
    intro p hp
    by_cases h : ∀ x ∈ p.1, x = 0 ∨ d / 2 < x
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h⟩)
    · push Not at h
      obtain ⟨x₀, hx₀, hne0, hle⟩ := h
      have hpos : (p.1.filter (0 < ·)).Nonempty := ⟨x₀, Finset.mem_filter.mpr ⟨hx₀, by omega⟩⟩
      let b := (p.1.filter (0 < ·)).min' hpos
      have hb_mem := Finset.min'_mem (p.1.filter (0 < ·)) hpos
      have hb_in : b ∈ p.1 := (Finset.mem_filter.mp hb_mem).1
      have hb_pos : 0 < b := (Finset.mem_filter.mp hb_mem).2
      have hb_le_x₀ : b ≤ x₀ := Finset.min'_le _ x₀ (Finset.mem_filter.mpr ⟨hx₀, by omega⟩)
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      refine ⟨b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      refine Finset.mem_filter.mpr ⟨hp, hb_in, fun x hx hxp ↦ ?_⟩
      exact Finset.min'_le _ x (Finset.mem_filter.mpr ⟨hx, hxp⟩)
  have hPempty : (P_empty.card : ℝ) ≤ 2 * (11 / 4 : ℝ) ^ d := by
    let f : Finset ℕ × Finset ℕ → (Fin (d / 2) → Bool) × (Fin (d - d / 2) → Fin 3) :=
      fun p ↦
        (fun i ↦ decide (i.1 + 1 ∈ p.2),
         fun j ↦ if d / 2 + 1 + j.1 ∈ p.1 then 0 else if d / 2 + 1 + j.1 ∈ p.2 then 1 else 2)
    have hinj : Set.InjOn f P_empty := by
      intro p hp q hq heq
      rw [Finset.mem_coe] at hp hq
      have hp' := Finset.mem_filter.mp hp
      have hq' := Finset.mem_filter.mp hq
      have hpv := Finset.mem_filter.mp hp'.1
      have hqv := Finset.mem_filter.mp hq'.1
      have hp1sub : p.1 ⊆ Finset.Icc 0 d := Finset.mem_powerset.mp (Finset.mem_product.mp hpv.1).1
      have hp2sub : p.2 ⊆ Finset.Icc 0 d := Finset.mem_powerset.mp (Finset.mem_product.mp hpv.1).2
      have hq1sub : q.1 ⊆ Finset.Icc 0 d := Finset.mem_powerset.mp (Finset.mem_product.mp hqv.1).1
      have hq2sub : q.2 ⊆ Finset.Icc 0 d := Finset.mem_powerset.mp (Finset.mem_product.mp hqv.1).2
      have h1 : ∀ i : Fin (d / 2), (i.1 + 1 ∈ p.2 ↔ i.1 + 1 ∈ q.2) := by
        intro i
        have := congr_fun (congr_arg Prod.fst heq) i
        simpa [f] using this
      have h2 : ∀ j : Fin (d - d / 2),
          (d / 2 + 1 + j.1 ∈ p.1 ↔ d / 2 + 1 + j.1 ∈ q.1) ∧
          (d / 2 + 1 + j.1 ∈ p.2 ↔ d / 2 + 1 + j.1 ∈ q.2) := by
        intro j
        have hj := congr_fun (congr_arg Prod.snd heq) j
        dsimp only [f] at hj
        set x := d / 2 + 1 + j.1
        have hp_disj : ¬(x ∈ p.1 ∧ x ∈ p.2) := by
          rintro ⟨ha, hb⟩
          have := hpv.2.2 0 hpv.2.1 x ha
          rw [zero_add] at this; exact this hb
        have hq_disj : ¬(x ∈ q.1 ∧ x ∈ q.2) := by
          rintro ⟨ha, hb⟩
          have := hqv.2.2 0 hqv.2.1 x ha
          rw [zero_add] at this; exact this hb
        exact label3_inj hp_disj hq_disj hj
      apply Prod.ext
      · apply Finset.ext; intro x
        constructor <;> intro hx
        · have hxle : x ≤ d := (Finset.mem_Icc.mp (hp1sub hx)).2
          rcases hp'.2 x hx with rfl | hgt
          · exact hqv.2.1
          · have hlt : x - (d / 2 + 1) < d - d / 2 := by omega
            have hxj : d / 2 + 1 + (x - (d / 2 + 1)) = x := by omega
            have := (h2 ⟨x - (d / 2 + 1), hlt⟩).1
            rw [hxj] at this; exact this.mp hx
        · have hxle : x ≤ d := (Finset.mem_Icc.mp (hq1sub hx)).2
          rcases hq'.2 x hx with rfl | hgt
          · exact hpv.2.1
          · have hlt : x - (d / 2 + 1) < d - d / 2 := by omega
            have hxj : d / 2 + 1 + (x - (d / 2 + 1)) = x := by omega
            have := (h2 ⟨x - (d / 2 + 1), hlt⟩).1
            rw [hxj] at this; exact this.mpr hx
      · apply Finset.ext; intro x
        constructor <;> intro hx
        · have hxle : x ≤ d := (Finset.mem_Icc.mp (hp2sub hx)).2
          by_cases hx0 : x = 0
          · subst hx0; exact absurd hx (hpv.2.2 0 hpv.2.1 0 hpv.2.1)
          · by_cases hle : x ≤ d / 2
            · have := h1 ⟨x - 1, by omega⟩
              have hxe : x - 1 + 1 = x := by omega
              rw [hxe] at this; exact this.mp hx
            · have hlt : x - (d / 2 + 1) < d - d / 2 := by omega
              have hxj : d / 2 + 1 + (x - (d / 2 + 1)) = x := by omega
              have := (h2 ⟨x - (d / 2 + 1), hlt⟩).2
              rw [hxj] at this; exact this.mp hx
        · have hxle : x ≤ d := (Finset.mem_Icc.mp (hq2sub hx)).2
          by_cases hx0 : x = 0
          · subst hx0; exact absurd hx (hqv.2.2 0 hqv.2.1 0 hqv.2.1)
          · by_cases hle : x ≤ d / 2
            · have := h1 ⟨x - 1, by omega⟩
              have hxe : x - 1 + 1 = x := by omega
              rw [hxe] at this; exact this.mpr hx
            · have hlt : x - (d / 2 + 1) < d - d / 2 := by omega
              have hxj : d / 2 + 1 + (x - (d / 2 + 1)) = x := by omega
              have := (h2 ⟨x - (d / 2 + 1), hlt⟩).2
              rw [hxj] at this; exact this.mpr hx
    have hcard_le : P_empty.card ≤ 2 ^ (d / 2) * 3 ^ (d - d / 2) := by
      have h1 := Finset.card_le_card_of_injOn f (fun _ _ ↦ Finset.mem_univ _) hinj
      simpa [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using h1
    have hreal : ((2 ^ (d / 2) * 3 ^ (d - d / 2) : ℕ) : ℝ) ≤ 2 * (11 / 4 : ℝ) ^ d := by
      push_cast
      set k := d / 2
      have h6 : (2 * 3 : ℝ) ≤ (11 / 4 : ℝ) ^ 2 := by norm_num
      have h6k : ((2 : ℝ) * 3) ^ k ≤ ((11 / 4 : ℝ) ^ 2) ^ k :=
        pow_le_pow_left₀ (by norm_num) h6 k
      rcases Nat.mod_two_eq_zero_or_one d with hmod | hmod
      · have hsub : d - k = k := by omega
        have hd2 : d = 2 * k := by omega
        rw [hsub, hd2, ← mul_pow, pow_mul]
        linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ (11 / 4 : ℝ) ^ 2) k]
      · have hsub : d - k = k + 1 := by omega
        have hd2 : d = 2 * k + 1 := by omega
        rw [hsub, hd2, pow_succ, pow_succ, pow_mul]
        have h3le : (3 : ℝ) ≤ 2 * (11 / 4 : ℝ) := by norm_num
        have hmul : (2 : ℝ) ^ k * ((3 : ℝ) ^ k * 3) = 3 * ((2 : ℝ) * 3) ^ k := by
          rw [mul_pow]; ring
        rw [hmul]
        calc 3 * ((2 : ℝ) * 3) ^ k
            ≤ (2 * (11 / 4 : ℝ)) * ((11 / 4 : ℝ) ^ 2) ^ k :=
              mul_le_mul h3le h6k (by positivity) (by positivity)
          _ = 2 * (((11 / 4 : ℝ) ^ 2) ^ k * (11 / 4 : ℝ)) := by ring
    exact le_trans (by exact_mod_cast hcard_le) hreal
  have hPb : ∀ b ∈ Finset.Icc 1 (d / 2), ((P_b b).card : ℝ) ≤ (11 / 8 : ℝ) * (11 / 4 : ℝ) ^ d := by
    intro b hb
    rw [Finset.mem_Icc] at hb
    obtain ⟨hb1, hbd⟩ := hb
    let len (r : Fin b) : ℕ := (d - b - r.1) / b + 1
    have hlen_pos : ∀ r : Fin b, 0 < len r := fun r ↦ Nat.succ_pos _
    let f : Finset ℕ × Finset ℕ →
        (Fin (b - 1) → Bool) × (∀ r : Fin b, Fin (len r) → Fin 3) :=
      fun p ↦
        (fun i ↦ decide (i.1 + 1 ∈ p.2),
         fun r j ↦
           let x := b + r.1 + j.1 * b
           if x ∈ p.1 then 0 else if x ∈ p.2 then 1 else 2)
    let T : Finset ((Fin (b - 1) → Bool) × (∀ r : Fin b, Fin (len r) → Fin 3)) :=
      Finset.univ ×ˢ Fintype.piFinset (fun r : Fin b ↦ noLR (len r))
    have hmaps : Set.MapsTo f (P_b b) T := by
      intro p hp
      rw [Finset.mem_coe] at hp ⊢
      have hp' := Finset.mem_filter.mp hp
      have hpv := Finset.mem_filter.mp hp'.1
      rw [Finset.mem_product]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Fintype.mem_piFinset]
      intro r
      rw [noLR, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro j hj
      rintro ⟨h0, h1⟩
      dsimp only [f] at h0 h1
      have hx_in : b + r.1 + j.1 * b ∈ p.1 := by
        by_contra hc
        simp only [hc, ↓reduceIte] at h0
        split_ifs at h0 <;> exact absurd h0 (by decide)
      have hx1_in : b + r.1 + (j.1 + 1) * b ∈ p.2 := by
        by_contra hc
        simp only [hc, ↓reduceIte] at h1
        split_ifs at h1 <;> exact absurd h1 (by decide)
      have hsum : (b + r.1 + j.1 * b) + b = b + r.1 + (j.1 + 1) * b := by ring
      have hforb := hpv.2.2 (b + r.1 + j.1 * b) hx_in b hp'.2.1
      rw [hsum] at hforb
      exact hforb hx1_in
    have hinj : Set.InjOn f (P_b b) := by
      intro p hp q hq heq
      rw [Finset.mem_coe] at hp hq
      have hp' := Finset.mem_filter.mp hp
      have hq' := Finset.mem_filter.mp hq
      have hpv := Finset.mem_filter.mp hp'.1
      have hqv := Finset.mem_filter.mp hq'.1
      have hp1sub : p.1 ⊆ Finset.Icc 0 d := Finset.mem_powerset.mp (Finset.mem_product.mp hpv.1).1
      have hp2sub : p.2 ⊆ Finset.Icc 0 d := Finset.mem_powerset.mp (Finset.mem_product.mp hpv.1).2
      have hq1sub : q.1 ⊆ Finset.Icc 0 d := Finset.mem_powerset.mp (Finset.mem_product.mp hqv.1).1
      have hq2sub : q.2 ⊆ Finset.Icc 0 d := Finset.mem_powerset.mp (Finset.mem_product.mp hqv.1).2
      have h1 : ∀ i : Fin (b - 1), (i.1 + 1 ∈ p.2 ↔ i.1 + 1 ∈ q.2) := by
        intro i
        have := congr_fun (congr_arg Prod.fst heq) i
        simpa [f] using this
      have h2 : ∀ r : Fin b, ∀ j : Fin (len r),
          (b + r.1 + j.1 * b ∈ p.1 ↔ b + r.1 + j.1 * b ∈ q.1) ∧
          (b + r.1 + j.1 * b ∈ p.2 ↔ b + r.1 + j.1 * b ∈ q.2) := by
        intro r j
        have hrj := congr_fun (congr_fun (congr_arg Prod.snd heq) r) j
        dsimp only [f] at hrj
        set x := b + r.1 + j.1 * b
        have hp_disj : ¬(x ∈ p.1 ∧ x ∈ p.2) := by
          rintro ⟨ha, hb'⟩
          have := hpv.2.2 0 hpv.2.1 x ha
          rw [zero_add] at this; exact this hb'
        have hq_disj : ¬(x ∈ q.1 ∧ x ∈ q.2) := by
          rintro ⟨ha, hb'⟩
          have := hqv.2.2 0 hqv.2.1 x ha
          rw [zero_add] at this; exact this hb'
        exact label3_inj hp_disj hq_disj hrj
      have hrepr : ∀ x : ℕ, b ≤ x → x ≤ d →
          ∃ (r : Fin b) (j : Fin (len r)), b + r.1 + j.1 * b = x := by
        intro x hbx hxd
        have hbmod : (x - b) % b < b := Nat.mod_lt _ (by omega)
        refine ⟨⟨(x - b) % b, hbmod⟩, ⟨(x - b) / b, ?_⟩, ?_⟩
        · change (x - b) / b < (d - b - (x - b) % b) / b + 1
          have hdiv : (x - b) / b * b + (x - b) % b = x - b := by
            rw [mul_comm]; exact Nat.div_add_mod (x - b) b
          have hle : (x - b) / b * b ≤ d - b - (x - b) % b := by omega
          have := (Nat.le_div_iff_mul_le (by omega)).mpr hle
          omega
        · have hdiv : (x - b) / b * b + (x - b) % b = x - b := by
            rw [mul_comm]; exact Nat.div_add_mod (x - b) b
          dsimp only; omega
      apply Prod.ext
      · apply Finset.ext; intro x
        constructor <;> intro hx
        · have hxle : x ≤ d := (Finset.mem_Icc.mp (hp1sub hx)).2
          by_cases hx0 : x = 0
          · subst hx0; exact hqv.2.1
          · have hbx : b ≤ x := hp'.2.2 x hx (by omega)
            obtain ⟨r, j, hrj⟩ := hrepr x hbx hxle
            have := (h2 r j).1
            rw [hrj] at this; exact this.mp hx
        · have hxle : x ≤ d := (Finset.mem_Icc.mp (hq1sub hx)).2
          by_cases hx0 : x = 0
          · subst hx0; exact hpv.2.1
          · have hbx : b ≤ x := hq'.2.2 x hx (by omega)
            obtain ⟨r, j, hrj⟩ := hrepr x hbx hxle
            have := (h2 r j).1
            rw [hrj] at this; exact this.mpr hx
      · apply Finset.ext; intro x
        constructor <;> intro hx
        · have hxle : x ≤ d := (Finset.mem_Icc.mp (hp2sub hx)).2
          by_cases hx0 : x = 0
          · subst hx0; exact absurd hx (hpv.2.2 0 hpv.2.1 0 hpv.2.1)
          · by_cases hlt : x < b
            · have := h1 ⟨x - 1, by omega⟩
              have hxe : x - 1 + 1 = x := by omega
              rw [hxe] at this; exact this.mp hx
            · obtain ⟨r, j, hrj⟩ := hrepr x (by omega) hxle
              have := (h2 r j).2
              rw [hrj] at this; exact this.mp hx
        · have hxle : x ≤ d := (Finset.mem_Icc.mp (hq2sub hx)).2
          by_cases hx0 : x = 0
          · subst hx0; exact absurd hx (hqv.2.2 0 hqv.2.1 0 hqv.2.1)
          · by_cases hlt : x < b
            · have := h1 ⟨x - 1, by omega⟩
              have hxe : x - 1 + 1 = x := by omega
              rw [hxe] at this; exact this.mpr hx
            · obtain ⟨r, j, hrj⟩ := hrepr x (by omega) hxle
              have := (h2 r j).2
              rw [hrj] at this; exact this.mpr hx
    have hcard_le : (P_b b).card ≤ 2 ^ (b - 1) * ∏ r : Fin b, (noLR (len r)).card := by
      have h1 := Finset.card_le_card_of_injOn f hmaps hinj
      simpa [T, Finset.card_product, Fintype.card_piFinset, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin] using h1
    have hsum_len : ∑ r : Fin b, len r = d - b + 1 := by
      have hbij : (Finset.univ.sigma (fun r : Fin b ↦ (Finset.univ : Finset (Fin (len r))))).card =
          (Finset.Icc b d).card := by
        refine Finset.card_bij (fun p _ ↦ b + p.1.1 + p.2.1 * b) ?_ ?_ ?_
        · rintro ⟨r, j⟩ _
          dsimp only
          rw [Finset.mem_Icc]
          have hj : j.1 ≤ (d - b - r.1) / b := Nat.lt_succ_iff.mp j.2
          have hmul : j.1 * b ≤ d - b - r.1 :=
            (Nat.le_div_iff_mul_le (by omega)).mp hj
          have hrle : b + r.1 ≤ d := by omega
          exact ⟨by omega, by omega⟩
        · rintro ⟨r₁, j₁⟩ _ ⟨r₂, j₂⟩ _ heq
          dsimp only at heq
          have hsub : r₁.1 + j₁.1 * b = r₂.1 + j₂.1 * b := by omega
          have hrmod : (r₁.1 + j₁.1 * b) % b = (r₂.1 + j₂.1 * b) % b := congrArg (· % b) hsub
          rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
            Nat.mod_eq_of_lt r₁.2, Nat.mod_eq_of_lt r₂.2] at hrmod
          have hr : r₁ = r₂ := Fin.ext hrmod
          subst hr
          have hj : j₁.1 = j₂.1 := by
            have : j₁.1 * b = j₂.1 * b := by omega
            exact Nat.eq_of_mul_eq_mul_right (by omega) this
          exact Sigma.ext rfl (heq_of_eq (Fin.ext hj))
        · intro x hx
          rw [Finset.mem_Icc] at hx
          have hbmod : (x - b) % b < b := Nat.mod_lt _ (by omega)
          have hdiv : (x - b) / b * b + (x - b) % b = x - b := by
            rw [mul_comm]; exact Nat.div_add_mod (x - b) b
          have hj : (x - b) / b < len ⟨(x - b) % b, hbmod⟩ := by
            change (x - b) / b < (d - b - (x - b) % b) / b + 1
            have hle : (x - b) / b * b ≤ d - b - (x - b) % b := by omega
            have := (Nat.le_div_iff_mul_le (by omega)).mpr hle
            omega
          refine ⟨⟨⟨(x - b) % b, hbmod⟩, ⟨(x - b) / b, hj⟩⟩, by simp, ?_⟩
          dsimp; omega
      simp only [Finset.card_sigma, Finset.card_univ, Fintype.card_fin, Nat.card_Icc] at hbij
      rw [hbij]; omega
    have hprod_le : (∏ r : Fin b, ((noLR (len r)).card : ℝ)) ≤
        (11 / 8 : ℝ) ^ b * (11 / 4 : ℝ) ^ (d - b + 1) := by
      calc (∏ r : Fin b, ((noLR (len r)).card : ℝ))
          ≤ ∏ r : Fin b, ((11 / 8 : ℝ) * (11 / 4 : ℝ) ^ (len r)) :=
            Finset.prod_le_prod (fun _ _ ↦ by positivity) (fun r _ ↦ noLR_card_le (len r) (hlen_pos r))
        _ = (∏ _r : Fin b, (11 / 8 : ℝ)) * (∏ r : Fin b, (11 / 4 : ℝ) ^ (len r)) :=
            Finset.prod_mul_distrib
        _ = (11 / 8 : ℝ) ^ b * (11 / 4 : ℝ) ^ (∑ r : Fin b, len r) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_pow_eq_pow_sum]
        _ = (11 / 8 : ℝ) ^ b * (11 / 4 : ℝ) ^ (d - b + 1) := by rw [hsum_len]
    have hcard_le' : ((P_b b).card : ℝ) ≤
        (2 : ℝ) ^ (b - 1) * (∏ r : Fin b, ((noLR (len r)).card : ℝ)) := by
      exact_mod_cast hcard_le
    calc ((P_b b).card : ℝ)
        ≤ (2 : ℝ) ^ (b - 1) * ((11 / 8 : ℝ) ^ b * (11 / 4 : ℝ) ^ (d - b + 1)) :=
          le_trans hcard_le' (mul_le_mul_of_nonneg_left hprod_le (by positivity))
      _ = (11 / 8 : ℝ) * (11 / 4 : ℝ) ^ d := by
          have hb_eq : b = (b - 1) + 1 := by omega
          have hd_eq : (b - 1) + (d - b + 1) = d := by omega
          have h11 : (11 / 8 : ℝ) ^ b = (11 / 8 : ℝ) ^ (b - 1) * (11 / 8 : ℝ) := by
            conv_lhs => rw [hb_eq, pow_succ]
          rw [h11]
          calc (2 : ℝ) ^ (b - 1) * ((11 / 8 : ℝ) ^ (b - 1) * (11 / 8 : ℝ) * (11 / 4 : ℝ) ^ (d - b + 1))
              = (11 / 8 : ℝ) * (((2 : ℝ) * (11 / 8 : ℝ)) ^ (b - 1) * (11 / 4 : ℝ) ^ (d - b + 1)) := by
                rw [mul_pow]; ring
            _ = (11 / 8 : ℝ) * ((11 / 4 : ℝ) ^ (b - 1) * (11 / 4 : ℝ) ^ (d - b + 1)) := by
                have : (2 : ℝ) * (11 / 8 : ℝ) = 11 / 4 := by norm_num
                rw [this]
            _ = (11 / 8 : ℝ) * (11 / 4 : ℝ) ^ d := by rw [← pow_add, hd_eq]
  have htot : (validPairs d).card ≤ P_empty.card + ∑ b ∈ Finset.Icc 1 (d / 2), (P_b b).card := by
    calc (validPairs d).card
        ≤ (P_empty ∪ (Finset.Icc 1 (d / 2)).biUnion P_b).card := Finset.card_le_card hcover
      _ ≤ P_empty.card + ((Finset.Icc 1 (d / 2)).biUnion P_b).card := Finset.card_union_le _ _
      _ ≤ P_empty.card + ∑ b ∈ Finset.Icc 1 (d / 2), (P_b b).card := by
          gcongr; exact Finset.card_biUnion_le
  have hsum_Pb : (∑ b ∈ Finset.Icc 1 (d / 2), ((P_b b).card : ℝ)) ≤ (d : ℝ) * (11 / 4 : ℝ) ^ d := by
    calc (∑ b ∈ Finset.Icc 1 (d / 2), ((P_b b).card : ℝ))
        ≤ ∑ _b ∈ Finset.Icc 1 (d / 2), ((11 / 8 : ℝ) * (11 / 4 : ℝ) ^ d) :=
          Finset.sum_le_sum hPb
      _ = ((Finset.Icc 1 (d / 2)).card : ℝ) * ((11 / 8 : ℝ) * (11 / 4 : ℝ) ^ d) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (d : ℝ) * (11 / 4 : ℝ) ^ d := by
          have hcard : (Finset.Icc 1 (d / 2)).card = d / 2 := by simp
          rw [hcard]
          have hle : ((d / 2 : ℕ) : ℝ) * (11 / 8 : ℝ) ≤ (d : ℝ) := by
            have h2 : (2 * (d / 2) : ℕ) ≤ d := Nat.mul_div_le d 2
            have h2' : 2 * ((d / 2 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast h2
            linarith
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 4) d]
  have htot' : ((validPairs d).card : ℝ) ≤
      (P_empty.card : ℝ) + ∑ b ∈ Finset.Icc 1 (d / 2), ((P_b b).card : ℝ) := by exact_mod_cast htot
  linarith

lemma w_le (d : ℕ) :
    w d ≤ ((2 + d : ℝ) / 2) * ((11 / 4 : ℝ) / (2 : ℝ) ^ ((3 : ℝ) / 2)) ^ d := by
  unfold w
  have hpow : (2 : ℝ) ^ ((3 * d : ℝ) / 2 + 1) = 2 * ((2 : ℝ) ^ ((3 : ℝ) / 2)) ^ d := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  rw [hpow, div_pow]
  have h1 := validPairs_card_le d
  have hpos : (0 : ℝ) < 2 * ((2 : ℝ) ^ ((3 : ℝ) / 2)) ^ d := by positivity
  calc ((validPairs d).card : ℝ) / (2 * ((2 : ℝ) ^ ((3 : ℝ) / 2)) ^ d)
      ≤ ((2 + d : ℝ) * (11 / 4 : ℝ) ^ d) / (2 * ((2 : ℝ) ^ ((3 : ℝ) / 2)) ^ d) := by gcongr
    _ = ((2 + d : ℝ) / 2) * ((11 / 4 : ℝ) ^ d / ((2 : ℝ) ^ ((3 : ℝ) / 2)) ^ d) := by ring

lemma summable_w : Summable w := by
  set r : ℝ := (11 / 4 : ℝ) / (2 : ℝ) ^ ((3 : ℝ) / 2)
  have hr_pos : 0 ≤ r := by positivity
  have hr_lt : r < 1 := by
    have hsq : r ^ 2 < 1 ^ 2 := by
      have h23 : ((2 : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = 8 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [div_pow, h23]
      norm_num
    nlinarith [sq_nonneg r]
  have h1 : Summable (fun d : ℕ ↦ r ^ d) := summable_geometric_of_lt_one hr_pos hr_lt
  have h2 : Summable (fun d : ℕ ↦ (d : ℝ) * r ^ d) := by
    simpa [pow_one] using
      summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_of_nonneg hr_pos]; exact hr_lt)
  have hsum : Summable (fun d : ℕ ↦ ((2 + d : ℝ) / 2) * r ^ d) := by
    have : (fun d : ℕ ↦ ((2 + d : ℝ) / 2) * r ^ d) =
        fun d : ℕ ↦ r ^ d + (1 / 2 : ℝ) * ((d : ℝ) * r ^ d) := by
      ext d; ring
    rw [this]
    exact h1.add (h2.mul_left _)
  exact Summable.of_nonneg_of_le w_nonneg w_le hsum

/-- Exact bijection for `highFamily n` elements with minimum `a ∈ (n/3, n/2]`. -/
lemma highFamily_min_card (n a : ℕ) (h1 : n / 3 < a) (h2 : a ≤ n / 2) :
    ((highFamily n).filter (fun A ↦ ∃ h : A.Nonempty, A.min' h = a)).card =
      (validPairs (n - 2 * a)).card * 2 ^ (3 * a - n - 1) := by
  set d := n - 2 * a
  set M_set := Finset.Ioo (n - a) (2 * a)
  have hM_card : M_set.card = 3 * a - n - 1 := by
    rw [Nat.card_Ioo]
    omega
  have hgoal : ((highFamily n).filter (fun A ↦ ∃ h : A.Nonempty, A.min' h = a)).card =
      (validPairs d ×ˢ M_set.powerset).card := by
    refine Finset.card_bij
      (fun A _ ↦
        (((A.filter (· ≤ n - a)).image (· - a), (A.filter (2 * a ≤ ·)).image (· - 2 * a)),
          A.filter (fun x ↦ n - a < x ∧ x < 2 * a))) ?_ ?_ ?_
    · intro A hA
      have hA1 := Finset.mem_filter.mp hA
      have hA2 := Finset.mem_filter.mp hA1.1
      have hA3 := Finset.mem_filter.mp hA2.1
      have hAsub : A ⊆ Finset.Icc 1 n := Finset.mem_powerset.mp hA3.1
      have hAsf : IsSumFree (A : Set ℕ) := hA3.2
      obtain ⟨hne, hmin⟩ := hA1.2
      have hmin_le : ∀ x ∈ A, a ≤ x := fun x hx ↦ hmin ▸ Finset.min'_le A x hx
      have ha_in : a ∈ A := hmin ▸ Finset.min'_mem A hne
      rw [Finset.mem_product, validPairs, Finset.mem_filter, Finset.mem_product,
        Finset.mem_powerset, Finset.mem_powerset, Finset.mem_powerset]
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
      · intro u hu
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨hxA, hxle⟩ := Finset.mem_filter.mp hx
        have := hmin_le x hxA
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro u hu
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨hxA, hxge⟩ := Finset.mem_filter.mp hx
        have hxle := (Finset.mem_Icc.mp (hAsub hxA)).2
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha_in, by omega⟩, by omega⟩
      · intro u hu v hv huv
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨hxA, hxle⟩ := Finset.mem_filter.mp hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨hyA, hyle⟩ := Finset.mem_filter.mp hy
        obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp huv
        obtain ⟨hzA, hzge⟩ := Finset.mem_filter.mp hz
        have hax := hmin_le x hxA
        have hay := hmin_le y hyA
        have hxyz : x + y = z := by omega
        rw [isSumFree_iff] at hAsf
        exact hAsf x (Finset.mem_coe.mpr hxA) y (Finset.mem_coe.mpr hyA)
          (by rw [hxyz]; exact Finset.mem_coe.mpr hzA)
      · intro x hx
        exact Finset.mem_Ioo.mpr (Finset.mem_filter.mp hx).2
    · intro A hA B hB heq
      obtain ⟨hA_hne, hA_min⟩ := (Finset.mem_filter.mp hA).2
      obtain ⟨hB_hne, hB_min⟩ := (Finset.mem_filter.mp hB).2
      have hA_ge : ∀ x ∈ A, a ≤ x := fun x hx ↦ hA_min ▸ Finset.min'_le A x hx
      have hB_ge : ∀ x ∈ B, a ≤ x := fun x hx ↦ hB_min ▸ Finset.min'_le B x hx
      have hL : (A.filter (· ≤ n - a)).image (· - a) = (B.filter (· ≤ n - a)).image (· - a) :=
        congr_arg (fun p ↦ p.1.1) heq
      have hR : (A.filter (2 * a ≤ ·)).image (· - 2 * a) =
          (B.filter (2 * a ≤ ·)).image (· - 2 * a) :=
        congr_arg (fun p ↦ p.1.2) heq
      have hM : A.filter (fun x ↦ n - a < x ∧ x < 2 * a) =
          B.filter (fun x ↦ n - a < x ∧ x < 2 * a) :=
        congr_arg Prod.snd heq
      apply Finset.ext; intro x
      by_cases h1x : x ≤ n - a
      · constructor <;> intro hx
        · have : x - a ∈ (B.filter (· ≤ n - a)).image (· - a) := by
            rw [← hL]; exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, h1x⟩, rfl⟩
          obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp this
          have hyB := (Finset.mem_filter.mp hy).1
          have := hA_ge x hx; have := hB_ge y hyB
          have : x = y := by omega
          rwa [this]
        · have : x - a ∈ (A.filter (· ≤ n - a)).image (· - a) := by
            rw [hL]; exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, h1x⟩, rfl⟩
          obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp this
          have hyA := (Finset.mem_filter.mp hy).1
          have := hB_ge x hx; have := hA_ge y hyA
          have : x = y := by omega
          rwa [this]
      · by_cases h2x : 2 * a ≤ x
        · constructor <;> intro hx
          · have : x - 2 * a ∈ (B.filter (2 * a ≤ ·)).image (· - 2 * a) := by
              rw [← hR]; exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, h2x⟩, rfl⟩
            obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp this
            have ⟨hyB, hyge⟩ := Finset.mem_filter.mp hy
            have : x = y := by omega
            rwa [this]
          · have : x - 2 * a ∈ (A.filter (2 * a ≤ ·)).image (· - 2 * a) := by
              rw [hR]; exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, h2x⟩, rfl⟩
            obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp this
            have ⟨hyA, hyge⟩ := Finset.mem_filter.mp hy
            have : x = y := by omega
            rwa [this]
        · have hmid : n - a < x ∧ x < 2 * a := by omega
          constructor <;> intro hx
          · have : x ∈ B.filter (fun x ↦ n - a < x ∧ x < 2 * a) := by
              rw [← hM]; exact Finset.mem_filter.mpr ⟨hx, hmid⟩
            exact (Finset.mem_filter.mp this).1
          · have : x ∈ A.filter (fun x ↦ n - a < x ∧ x < 2 * a) := by
              rw [hM]; exact Finset.mem_filter.mpr ⟨hx, hmid⟩
            exact (Finset.mem_filter.mp this).1
    · rintro ⟨⟨L, R⟩, M⟩ hLRM
      obtain ⟨hLR, hMmem⟩ := Finset.mem_product.mp hLRM
      have hMsub : M ⊆ M_set := Finset.mem_powerset.mp hMmem
      have hLRf := Finset.mem_filter.mp hLR
      have hLsub : L ⊆ Finset.Icc 0 d := Finset.mem_powerset.mp (Finset.mem_product.mp hLRf.1).1
      have hRsub : R ⊆ Finset.Icc 0 d := Finset.mem_powerset.mp (Finset.mem_product.mp hLRf.1).2
      obtain ⟨h0L, hLRfree⟩ := hLRf.2
      let A := L.image (· + a) ∪ M ∪ R.image (· + 2 * a)
      have ha_in : a ∈ A := by
        simp only [A, Finset.mem_union, Finset.mem_image]
        exact Or.inl (Or.inl ⟨0, h0L, by omega⟩)
      have hA_bounds : ∀ x ∈ A, a ≤ x ∧ x ≤ n := by
        intro x hx
        simp only [A, Finset.mem_union, Finset.mem_image] at hx
        rcases hx with (⟨u, hu, rfl⟩ | hxM) | ⟨u, hu, rfl⟩
        · have := Finset.mem_Icc.mp (hLsub hu); omega
        · have := Finset.mem_Ioo.mp (hMsub hxM); omega
        · have := Finset.mem_Icc.mp (hRsub hu); omega
      have hA_sf : IsSumFree (A : Set ℕ) := by
        rw [isSumFree_iff]
        intro x hx y hy hxy
        have hxA := Finset.mem_coe.mp hx
        have hyA := Finset.mem_coe.mp hy
        have hxyA := Finset.mem_coe.mp hxy
        have ⟨hx1, _⟩ := hA_bounds x hxA
        have ⟨hy1, _⟩ := hA_bounds y hyA
        have ⟨_, hxy2⟩ := hA_bounds (x + y) hxyA
        have hxL : x - a ∈ L := by
          simp only [A, Finset.mem_union, Finset.mem_image] at hxA
          rcases hxA with (⟨u, hu, hux⟩ | hxM) | ⟨u, hu, hux⟩
          · have : x - a = u := by omega
            rwa [this]
          · have := Finset.mem_Ioo.mp (hMsub hxM); omega
          · have := Finset.mem_Icc.mp (hRsub hu); omega
        have hyL : y - a ∈ L := by
          simp only [A, Finset.mem_union, Finset.mem_image] at hyA
          rcases hyA with (⟨u, hu, huy⟩ | hyM) | ⟨u, hu, huy⟩
          · have : y - a = u := by omega
            rwa [this]
          · have := Finset.mem_Ioo.mp (hMsub hyM); omega
          · have := Finset.mem_Icc.mp (hRsub hu); omega
        have hxyR : (x - a) + (y - a) ∈ R := by
          simp only [A, Finset.mem_union, Finset.mem_image] at hxyA
          rcases hxyA with (⟨u, hu, hux⟩ | hxyM) | ⟨u, hu, hux⟩
          · have := Finset.mem_Icc.mp (hLsub hu); omega
          · have := Finset.mem_Ioo.mp (hMsub hxyM); omega
          · have : (x - a) + (y - a) = u := by omega
            rwa [this]
        exact hLRfree (x - a) hxL (y - a) hyL hxyR
      refine ⟨A, ?_, ?_⟩
      · rw [Finset.mem_filter, highFamily, Finset.mem_filter, sfFamily, Finset.mem_filter,
          Finset.mem_powerset]
        refine ⟨⟨⟨fun x hx ↦ Finset.mem_Icc.mpr ⟨by have := (hA_bounds x hx).1; omega,
          (hA_bounds x hx).2⟩, hA_sf⟩, fun x hx ↦ by have := (hA_bounds x hx).1; omega⟩,
          ⟨a, ha_in⟩, ?_⟩
        exact le_antisymm (Finset.min'_le A a ha_in)
          (Finset.le_min' A ⟨a, ha_in⟩ a (fun x hx ↦ (hA_bounds x hx).1))
      · refine Prod.ext (Prod.ext ?_ ?_) ?_
        · apply Finset.ext; intro u
          simp only [A, Finset.mem_image, Finset.mem_filter, Finset.mem_union]
          constructor
          · rintro ⟨x, ⟨(⟨v, hv, rfl⟩ | hxM) | ⟨v, hv, rfl⟩, hxle⟩, rfl⟩
            · simpa using hv
            · have := Finset.mem_Ioo.mp (hMsub hxM); omega
            · have := Finset.mem_Icc.mp (hRsub hv); omega
          · intro hu
            have := Finset.mem_Icc.mp (hLsub hu)
            exact ⟨u + a, ⟨Or.inl (Or.inl ⟨u, hu, rfl⟩), by omega⟩, by omega⟩
        · apply Finset.ext; intro u
          simp only [A, Finset.mem_image, Finset.mem_filter, Finset.mem_union]
          constructor
          · rintro ⟨x, ⟨(⟨v, hv, rfl⟩ | hxM) | ⟨v, hv, rfl⟩, hxge⟩, rfl⟩
            · have := Finset.mem_Icc.mp (hLsub hv); omega
            · have := Finset.mem_Ioo.mp (hMsub hxM); omega
            · simpa using hv
          · intro hu
            have := Finset.mem_Icc.mp (hRsub hu)
            exact ⟨u + 2 * a, ⟨Or.inr ⟨u, hu, rfl⟩, by omega⟩, by omega⟩
        · apply Finset.ext; intro x
          simp only [A, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
          constructor
          · rintro ⟨(⟨v, hv, rfl⟩ | hxM) | ⟨v, hv, rfl⟩, h1x, h2x⟩
            · have := Finset.mem_Icc.mp (hLsub hv); omega
            · exact hxM
            · have := Finset.mem_Icc.mp (hRsub hv); omega
          · intro hxM
            have := Finset.mem_Ioo.mp (hMsub hxM)
            exact ⟨Or.inl (Or.inr hxM), this.1, this.2⟩
  rw [hgoal, Finset.card_product, Finset.card_powerset, hM_card]

lemma highFamily_card_formula (n : ℕ) :
    ((highFamily n).card : ℝ) / (2 : ℝ) ^ ((n : ℝ) / 2) =
      ((2 ^ (n - n / 2) : ℕ) : ℝ) / (2 : ℝ) ^ ((n : ℝ) / 2) +
        ∑ a ∈ Finset.Ioc (n / 3) (n / 2), w (n - 2 * a) := by
  let topPart := (highFamily n).filter fun A ↦ ∀ x ∈ A, n / 2 < x
  let minPart (a : ℕ) := (highFamily n).filter fun A ↦ ∃ h : A.Nonempty, A.min' h = a
  have htop_eq : topPart = (Finset.Ioc (n / 2) n).powerset := by
    apply Finset.ext; intro A
    rw [Finset.mem_filter, highFamily, Finset.mem_filter, sfFamily, Finset.mem_filter,
      Finset.mem_powerset, Finset.mem_powerset]
    constructor
    · intro h x hx
      exact Finset.mem_Ioc.mpr ⟨h.2 x hx, (Finset.mem_Icc.mp (h.1.1.1 hx)).2⟩
    · intro h
      refine ⟨⟨⟨fun x hx ↦ Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Ioc.mp (h hx)).1; omega,
        (Finset.mem_Ioc.mp (h hx)).2⟩, ?_⟩,
        fun x hx ↦ by have := (Finset.mem_Ioc.mp (h hx)).1; omega⟩,
        fun x hx ↦ (Finset.mem_Ioc.mp (h hx)).1⟩
      rw [isSumFree_iff]
      intro x hx y hy hxy
      have := Finset.mem_Ioc.mp (h (Finset.mem_coe.mp hx))
      have := Finset.mem_Ioc.mp (h (Finset.mem_coe.mp hy))
      have := Finset.mem_Ioc.mp (h (Finset.mem_coe.mp hxy))
      omega
  have htop_card : topPart.card = 2 ^ (n - n / 2) := by
    rw [htop_eq, Finset.card_powerset, Nat.card_Ioc]
  have hpart : highFamily n = topPart ∪ (Finset.Ioc (n / 3) (n / 2)).biUnion minPart := by
    apply Finset.ext; intro A
    rw [Finset.mem_union, Finset.mem_biUnion]
    constructor
    · intro hA
      by_cases hall : ∀ x ∈ A, n / 2 < x
      · exact Or.inl (Finset.mem_filter.mpr ⟨hA, hall⟩)
      · push Not at hall
        obtain ⟨x₀, hx₀, hx₀le⟩ := hall
        have hne : A.Nonempty := ⟨x₀, hx₀⟩
        refine Or.inr ⟨A.min' hne, Finset.mem_Ioc.mpr ⟨?_, ?_⟩,
          Finset.mem_filter.mpr ⟨hA, hne, rfl⟩⟩
        · exact (Finset.mem_filter.mp hA).2 _ (Finset.min'_mem A hne)
        · exact le_trans (Finset.min'_le A x₀ hx₀) hx₀le
    · rintro (h1 | ⟨a, _, h2⟩)
      · exact (Finset.mem_filter.mp h1).1
      · exact (Finset.mem_filter.mp h2).1
  have hdisj_top : Disjoint topPart ((Finset.Ioc (n / 3) (n / 2)).biUnion minPart) := by
    rw [Finset.disjoint_left]
    intro A hA1 hA2
    rw [Finset.mem_biUnion] at hA2
    obtain ⟨a, ha, hAm⟩ := hA2
    obtain ⟨_, hne, hmin⟩ := Finset.mem_filter.mp hAm
    have h1 := (Finset.mem_filter.mp hA1).2 (A.min' hne) (Finset.min'_mem A hne)
    have h2 := (Finset.mem_Ioc.mp ha).2
    omega
  have hdisj_min : Set.PairwiseDisjoint (Finset.Ioc (n / 3) (n / 2) : Set ℕ) minPart := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro A hA1 hA2
    obtain ⟨_, hne1, hmin1⟩ := Finset.mem_filter.mp hA1
    obtain ⟨_, hne2, hmin2⟩ := Finset.mem_filter.mp hA2
    exact hab (hmin1.symm.trans hmin2)
  have hcard : (highFamily n).card =
      2 ^ (n - n / 2) + ∑ a ∈ Finset.Ioc (n / 3) (n / 2), (minPart a).card := by
    rw [hpart, Finset.card_union_of_disjoint hdisj_top,
      Finset.card_biUnion hdisj_min, htop_card]
  have hcardR : ((highFamily n).card : ℝ) =
      ((2 ^ (n - n / 2) : ℕ) : ℝ) + ∑ a ∈ Finset.Ioc (n / 3) (n / 2), ((minPart a).card : ℝ) := by
    exact_mod_cast hcard
  rw [hcardR, add_div, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [Finset.mem_Ioc] at ha
  have hm := highFamily_min_card n a ha.1 ha.2
  rw [show (minPart a).card = (validPairs (n - 2 * a)).card * 2 ^ (3 * a - n - 1) from hm]
  unfold w
  have hexp : ((n : ℝ) / 2) = ((3 * a - n - 1 : ℕ) : ℝ) + ((3 * (n - 2 * a : ℕ) : ℝ) / 2 + 1) := by
    have h1 : n + 1 ≤ 3 * a := by omega
    have h2 : 2 * a ≤ n := by omega
    have hcast1 : ((3 * a - n - 1 : ℕ) : ℝ) = 3 * (a : ℝ) - (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_mul]; push_cast; ring
    have hcast2 : ((n - 2 * a : ℕ) : ℝ) = (n : ℝ) - 2 * (a : ℝ) := by
      rw [Nat.cast_sub h2, Nat.cast_mul]; push_cast; ring
    rw [hcast1, hcast2]; ring
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast (2 : ℝ) (3 * a - n - 1),
    hexp, Real.rpow_add (by norm_num)]
  have hne : (2 : ℝ) ^ ((3 * a - n - 1 : ℕ) : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos (by norm_num) _).ne'
  rw [mul_comm ((2 : ℝ) ^ ((3 * a - n - 1 : ℕ) : ℝ)), mul_div_mul_right _ _ hne]

lemma tendsto_highFamily_even :
    Tendsto (fun m : ℕ ↦ ((highFamily (2 * m)).card : ℝ) / (2 : ℝ) ^ m) atTop
      (nhds (1 + ∑' k : ℕ, w (2 * k))) := by
  have hsum : Summable (fun k : ℕ ↦ w (2 * k)) :=
    summable_w.comp_injective (fun a b h ↦ by omega)
  have hts : Tendsto (fun m : ℕ ↦ ∑ k ∈ Finset.range ((m + 2) / 3), w (2 * k)) atTop
      (nhds (∑' k : ℕ, w (2 * k))) := by
    have h1 := hsum.hasSum.tendsto_sum_nat
    have h2 : Tendsto (fun m : ℕ ↦ (m + 2) / 3) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      exact ⟨3 * b, fun m hm ↦ by omega⟩
    exact h1.comp h2
  have heq : ∀ m : ℕ,
      ((highFamily (2 * m)).card : ℝ) / (2 : ℝ) ^ m =
        1 + ∑ k ∈ Finset.range ((m + 2) / 3), w (2 * k) := by
    intro m
    have hpow : (2 : ℝ) ^ ((2 * m : ℕ) / 2 : ℝ) = (2 : ℝ) ^ m := by
      push_cast
      rw [show (2 : ℝ) * (m : ℝ) / 2 = (m : ℝ) by ring, Real.rpow_natCast]
    have hf := highFamily_card_formula (2 * m)
    rw [hpow] at hf
    rw [hf]
    refine congrArg₂ (· + ·) ?_ ?_
    · have hsub : 2 * m - 2 * m / 2 = m := by omega
      rw [hsub, Nat.cast_pow, Nat.cast_ofNat, div_self (by positivity)]
    · refine Finset.sum_bij (fun a _ ↦ m - a) ?_ ?_ ?_ ?_
      · intro a ha
        rw [Finset.mem_Ioc] at ha
        rw [Finset.mem_range]
        omega
      · intro a₁ ha₁ a₂ ha₂ h
        rw [Finset.mem_Ioc] at ha₁ ha₂
        omega
      · intro k hk
        rw [Finset.mem_range] at hk
        exact ⟨m - k, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro a ha
        rw [Finset.mem_Ioc] at ha
        congr 1; omega
  simp_rw [heq]
  exact hts.const_add (1 : ℝ)

lemma tendsto_highFamily_odd :
    Tendsto (fun m : ℕ ↦ ((highFamily (2 * m + 1)).card : ℝ) / (2 : ℝ) ^ ((2 * m + 1 : ℝ) / 2))
      atTop (nhds (Real.sqrt 2 + ∑' k : ℕ, w (2 * k + 1))) := by
  have hsum : Summable (fun k : ℕ ↦ w (2 * k + 1)) :=
    summable_w.comp_injective (fun a b h ↦ by omega)
  have hts : Tendsto (fun m : ℕ ↦ ∑ k ∈ Finset.range ((m + 1) / 3), w (2 * k + 1)) atTop
      (nhds (∑' k : ℕ, w (2 * k + 1))) := by
    have h1 := hsum.hasSum.tendsto_sum_nat
    have h2 : Tendsto (fun m : ℕ ↦ (m + 1) / 3) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      exact ⟨3 * b, fun m hm ↦ by omega⟩
    exact h1.comp h2
  have heq : ∀ m : ℕ,
      ((highFamily (2 * m + 1)).card : ℝ) / (2 : ℝ) ^ ((2 * m + 1 : ℝ) / 2) =
        Real.sqrt 2 + ∑ k ∈ Finset.range ((m + 1) / 3), w (2 * k + 1) := by
    intro m
    have hf := highFamily_card_formula (2 * m + 1)
    have hcast : ((2 * m + 1 : ℕ) : ℝ) / 2 = (2 * m + 1 : ℝ) / 2 := by push_cast; ring
    rw [hcast] at hf
    rw [hf]
    refine congrArg₂ (· + ·) ?_ ?_
    · have hsub : 2 * m + 1 - (2 * m + 1) / 2 = m + 1 := by omega
      rw [hsub, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast (2 : ℝ) (m + 1),
        ← Real.rpow_sub (by norm_num)]
      have : ((m + 1 : ℕ) : ℝ) - (2 * (m : ℝ) + 1) / 2 = (1 / 2 : ℝ) := by push_cast; ring
      rw [this, Real.sqrt_eq_rpow]
    · refine Finset.sum_bij (fun a _ ↦ m - a) ?_ ?_ ?_ ?_
      · intro a ha
        rw [Finset.mem_Ioc] at ha
        rw [Finset.mem_range]
        omega
      · intro a₁ ha₁ a₂ ha₂ h
        rw [Finset.mem_Ioc] at ha₁ ha₂
        omega
      · intro k hk
        rw [Finset.mem_range] at hk
        exact ⟨m - k, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro a ha
        rw [Finset.mem_Ioc] at ha
        congr 1; omega
  simp_rw [heq]
  exact hts.const_add (Real.sqrt 2)

end Mod1

section Mod2
open Filter Real Finset
open scoped Classical

def isTriple (a b c : ℕ) : Prop :=
  a + b = c ∨ a + c = b ∨ b + c = a

def schurTriples (C : Finset ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (C ×ˢ C ×ˢ C).filter fun t ↦ t.1 + t.2.1 = t.2.2

def distinctTriples (U : Finset ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (U ×ˢ U ×ˢ U).filter fun t ↦ t.1 < t.2.1 ∧ t.1 + t.2.1 = t.2.2

noncomputable def linkPairs (U : Finset ℕ) (v : ℕ) : Finset (ℕ × ℕ) :=
  ((U.erase v) ×ˢ (U.erase v)).filter fun p ↦ p.1 < p.2 ∧ isTriple v p.1 p.2

lemma isTriple_comm {a b c : ℕ} :
    isTriple a b c → (a + b = c ∨ a + c = b ∨ b + c = a) := id

lemma schurTriples_card_le (U : Finset ℕ) :
    (schurTriples U).card ≤ 2 * (distinctTriples U).card + U.card := by
  let S_lt := (schurTriples U).filter fun t ↦ t.1 < t.2.1
  let S_gt := (schurTriples U).filter fun t ↦ t.2.1 < t.1
  let S_eq := (schurTriples U).filter fun t ↦ t.1 = t.2.1
  have hcov : schurTriples U ⊆ S_lt ∪ S_gt ∪ S_eq := by
    intro t ht
    rw [Finset.mem_union, Finset.mem_union]
    rcases lt_trichotomy t.1 t.2.1 with h | h | h
    · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨ht, h⟩))
    · exact Or.inr (Finset.mem_filter.mpr ⟨ht, h⟩)
    · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨ht, h⟩))
  have h1 : S_lt.card ≤ (distinctTriples U).card := by
    refine Finset.card_le_card fun t ht ↦ ?_
    obtain ⟨hts, hlt⟩ := Finset.mem_filter.mp ht
    obtain ⟨htp, hsum⟩ := Finset.mem_filter.mp hts
    exact Finset.mem_filter.mpr ⟨htp, hlt, hsum⟩
  have h2 : S_gt.card ≤ (distinctTriples U).card := by
    refine Finset.card_le_card_of_injOn (fun t ↦ (t.2.1, t.1, t.2.2)) ?_ ?_
    · intro t ht
      rw [Finset.mem_coe] at ht ⊢
      obtain ⟨hts, hgt⟩ := Finset.mem_filter.mp ht
      obtain ⟨htp, hsum⟩ := Finset.mem_filter.mp hts
      obtain ⟨h1', h23⟩ := Finset.mem_product.mp htp
      obtain ⟨h2', h3'⟩ := Finset.mem_product.mp h23
      rw [distinctTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_product]
      dsimp only
      exact ⟨⟨h2', h1', h3'⟩, hgt, by omega⟩
    · intro t₁ _ t₂ _ heq
      rcases t₁ with ⟨a₁, b₁, c₁⟩
      rcases t₂ with ⟨a₂, b₂, c₂⟩
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hb, ha, hc⟩ := heq
      subst ha; subst hb; subst hc; rfl
  have h3 : S_eq.card ≤ U.card := by
    refine Finset.card_le_card_of_injOn (fun t ↦ t.1) ?_ ?_
    · intro t ht
      rw [Finset.mem_coe] at ht ⊢
      exact (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1).1
    · intro t₁ ht₁ t₂ ht₂ heq
      rw [Finset.mem_coe] at ht₁ ht₂
      obtain ⟨hts1, heq1⟩ := Finset.mem_filter.mp ht₁
      obtain ⟨hts2, heq2⟩ := Finset.mem_filter.mp ht₂
      have hs1 := (Finset.mem_filter.mp hts1).2
      have hs2 := (Finset.mem_filter.mp hts2).2
      rcases t₁ with ⟨a₁, b₁, c₁⟩
      rcases t₂ with ⟨a₂, b₂, c₂⟩
      dsimp at heq heq1 heq2 hs1 hs2
      have : b₁ = b₂ := by omega
      have : c₁ = c₂ := by omega
      subst heq; subst this; subst ‹b₁ = b₂›; rfl
  calc (schurTriples U).card
      ≤ (S_lt ∪ S_gt ∪ S_eq).card := Finset.card_le_card hcov
    _ ≤ (S_lt ∪ S_gt).card + S_eq.card := Finset.card_union_le _ _
    _ ≤ S_lt.card + S_gt.card + S_eq.card := by gcongr; exact Finset.card_union_le _ _
    _ ≤ 2 * (distinctTriples U).card + U.card := by omega

lemma sum_linkPairs_card_ge (U : Finset ℕ) (hpos : ∀ x ∈ U, 0 < x) :
    3 * (distinctTriples U).card ≤ ∑ v ∈ U, (linkPairs U v).card := by
  let S := U.sigma (fun v ↦ linkPairs U v)
  have hcardS : S.card = ∑ v ∈ U, (linkPairs U v).card := Finset.card_sigma _ _
  rw [← hcardS]
  let f1 : ℕ × ℕ × ℕ → Σ _ : ℕ, ℕ × ℕ := fun t ↦ ⟨t.1, (t.2.1, t.2.2)⟩
  let f2 : ℕ × ℕ × ℕ → Σ _ : ℕ, ℕ × ℕ := fun t ↦ ⟨t.2.1, (t.1, t.2.2)⟩
  let f3 : ℕ × ℕ × ℕ → Σ _ : ℕ, ℕ × ℕ := fun t ↦ ⟨t.2.2, (t.1, t.2.1)⟩
  let I1 := (distinctTriples U).image f1
  let I2 := (distinctTriples U).image f2
  let I3 := (distinctTriples U).image f3
  have hsub1 : I1 ⊆ S := by
    intro s hs
    obtain ⟨⟨a, b, c⟩, ht, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨htp, hlt, hsum⟩ := Finset.mem_filter.mp ht
    dsimp only at hlt hsum
    obtain ⟨ha, hbc⟩ := Finset.mem_product.mp htp
    obtain ⟨hb, hc⟩ := Finset.mem_product.mp hbc
    have ha0 := hpos a ha; have hb0 := hpos b hb
    rw [Finset.mem_sigma]
    dsimp only [f1]
    refine ⟨ha, ?_⟩
    rw [linkPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_erase, Finset.mem_erase]
    exact ⟨⟨⟨by omega, hb⟩, ⟨by omega, hc⟩⟩, by omega, Or.inl hsum⟩
  have hsub2 : I2 ⊆ S := by
    intro s hs
    obtain ⟨⟨a, b, c⟩, ht, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨htp, hlt, hsum⟩ := Finset.mem_filter.mp ht
    dsimp only at hlt hsum
    obtain ⟨ha, hbc⟩ := Finset.mem_product.mp htp
    obtain ⟨hb, hc⟩ := Finset.mem_product.mp hbc
    have ha0 := hpos a ha; have hb0 := hpos b hb
    rw [Finset.mem_sigma]
    dsimp only [f2]
    refine ⟨hb, ?_⟩
    rw [linkPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_erase, Finset.mem_erase]
    exact ⟨⟨⟨by omega, ha⟩, ⟨by omega, hc⟩⟩, by omega, Or.inl (by omega)⟩
  have hsub3 : I3 ⊆ S := by
    intro s hs
    obtain ⟨⟨a, b, c⟩, ht, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨htp, hlt, hsum⟩ := Finset.mem_filter.mp ht
    dsimp only at hlt hsum
    obtain ⟨ha, hbc⟩ := Finset.mem_product.mp htp
    obtain ⟨hb, hc⟩ := Finset.mem_product.mp hbc
    have ha0 := hpos a ha; have hb0 := hpos b hb
    rw [Finset.mem_sigma]
    dsimp only [f3]
    refine ⟨hc, ?_⟩
    rw [linkPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_erase, Finset.mem_erase]
    exact ⟨⟨⟨by omega, ha⟩, ⟨by omega, hb⟩⟩, hlt, Or.inr (Or.inr hsum)⟩
  have hdisj12 : Disjoint I1 I2 := by
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    obtain ⟨⟨a1, b1, c1⟩, ht1, rfl⟩ := Finset.mem_image.mp hs1
    obtain ⟨⟨a2, b2, c2⟩, ht2, heq⟩ := Finset.mem_image.mp hs2
    obtain ⟨_, hlt1, hsum1⟩ := Finset.mem_filter.mp ht1
    obtain ⟨_, hlt2, hsum2⟩ := Finset.mem_filter.mp ht2
    dsimp only at hlt1 hsum1 hlt2 hsum2
    have hfst : b2 = a1 := congr_arg Sigma.fst heq
    have hsnd : (a2, c2) = (b1, c1) := eq_of_heq (Sigma.mk.inj_iff.mp heq).2
    have ha2 : a2 = b1 := (Prod.mk.inj hsnd).1
    omega
  have hdisj13 : Disjoint I1 I3 := by
    rw [Finset.disjoint_left]
    intro s hs1 hs3
    obtain ⟨⟨a1, b1, c1⟩, ht1, rfl⟩ := Finset.mem_image.mp hs1
    obtain ⟨⟨a3, b3, c3⟩, ht3, heq⟩ := Finset.mem_image.mp hs3
    obtain ⟨htp1, hlt1, hsum1⟩ := Finset.mem_filter.mp ht1
    obtain ⟨htp3, hlt3, hsum3⟩ := Finset.mem_filter.mp ht3
    dsimp only at hlt1 hsum1 hlt3 hsum3
    have ha1 := hpos a1 (Finset.mem_product.mp htp1).1
    have hb1 := hpos b1 (Finset.mem_product.mp (Finset.mem_product.mp htp1).2).1
    have hfst : c3 = a1 := congr_arg Sigma.fst heq
    have hsnd : (a3, b3) = (b1, c1) := eq_of_heq (Sigma.mk.inj_iff.mp heq).2
    have ha3 : a3 = b1 := (Prod.mk.inj hsnd).1
    have hb3 : b3 = c1 := (Prod.mk.inj hsnd).2
    omega
  have hdisj23 : Disjoint I2 I3 := by
    rw [Finset.disjoint_left]
    intro s hs2 hs3
    obtain ⟨⟨a2, b2, c2⟩, ht2, rfl⟩ := Finset.mem_image.mp hs2
    obtain ⟨⟨a3, b3, c3⟩, ht3, heq⟩ := Finset.mem_image.mp hs3
    obtain ⟨htp2, hlt2, hsum2⟩ := Finset.mem_filter.mp ht2
    obtain ⟨htp3, hlt3, hsum3⟩ := Finset.mem_filter.mp ht3
    dsimp only at hlt2 hsum2 hlt3 hsum3
    have ha2 := hpos a2 (Finset.mem_product.mp htp2).1
    have hb2 := hpos b2 (Finset.mem_product.mp (Finset.mem_product.mp htp2).2).1
    have hfst : c3 = b2 := congr_arg Sigma.fst heq
    have hsnd : (a3, b3) = (a2, c2) := eq_of_heq (Sigma.mk.inj_iff.mp heq).2
    have hb3 : b3 = c2 := (Prod.mk.inj hsnd).2
    omega
  have hc1 : I1.card = (distinctTriples U).card := by
    refine Finset.card_image_of_injective _ fun ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ h ↦ ?_
    have hfst : a1 = a2 := congr_arg Sigma.fst h
    have hsnd : (b1, c1) = (b2, c2) := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    rw [hfst, (Prod.mk.inj hsnd).1, (Prod.mk.inj hsnd).2]
  have hc2 : I2.card = (distinctTriples U).card := by
    refine Finset.card_image_of_injective _ fun ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ h ↦ ?_
    have hfst : b1 = b2 := congr_arg Sigma.fst h
    have hsnd : (a1, c1) = (a2, c2) := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    rw [hfst, (Prod.mk.inj hsnd).1, (Prod.mk.inj hsnd).2]
  have hc3 : I3.card = (distinctTriples U).card := by
    refine Finset.card_image_of_injective _ fun ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ h ↦ ?_
    have hfst : c1 = c2 := congr_arg Sigma.fst h
    have hsnd : (a1, b1) = (a2, b2) := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    rw [hfst, (Prod.mk.inj hsnd).1, (Prod.mk.inj hsnd).2]
  have hunion : I1 ∪ I2 ∪ I3 ⊆ S := Finset.union_subset (Finset.union_subset hsub1 hsub2) hsub3
  have hcard_u : (I1 ∪ I2 ∪ I3).card = I1.card + I2.card + I3.card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisj13, hdisj23⟩),
      Finset.card_union_of_disjoint hdisj12]
  calc 3 * (distinctTriples U).card
      = I1.card + I2.card + I3.card := by rw [hc1, hc2, hc3]; omega
    _ = (I1 ∪ I2 ∪ I3).card := hcard_u.symm
    _ ≤ S.card := Finset.card_le_card hunion

lemma distinctTriples_union_le (U T : Finset ℕ) (_hpos : ∀ x ∈ U ∪ T, 0 < x) :
    (distinctTriples (U ∪ T)).card ≤ (distinctTriples U).card + 3 * T.card * (U ∪ T).card := by
  let S := U ∪ T
  let extra := (distinctTriples S).filter fun t ↦ t.1 ∈ T ∨ t.2.1 ∈ T ∨ t.2.2 ∈ T
  have hcov : distinctTriples S ⊆ distinctTriples U ∪ extra := by
    intro t ht
    rw [Finset.mem_union]
    by_cases hT : t.1 ∈ T ∨ t.2.1 ∈ T ∨ t.2.2 ∈ T
    · exact Or.inr (Finset.mem_filter.mpr ⟨ht, hT⟩)
    · left
      obtain ⟨htp, hlt, hsum⟩ := Finset.mem_filter.mp ht
      obtain ⟨h1, h23⟩ := Finset.mem_product.mp htp
      obtain ⟨h2, h3⟩ := Finset.mem_product.mp h23
      rw [distinctTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_product]
      refine ⟨⟨?_, ?_, ?_⟩, hlt, hsum⟩
      · exact (Finset.mem_union.mp h1).resolve_right (fun h ↦ hT (Or.inl h))
      · exact (Finset.mem_union.mp h2).resolve_right (fun h ↦ hT (Or.inr (Or.inl h)))
      · exact (Finset.mem_union.mp h3).resolve_right (fun h ↦ hT (Or.inr (Or.inr h)))
  have hextra : extra.card ≤ 3 * T.card * S.card := by
    let E1 := (distinctTriples S).filter fun t ↦ t.1 ∈ T
    let E2 := (distinctTriples S).filter fun t ↦ t.2.1 ∈ T
    let E3 := (distinctTriples S).filter fun t ↦ t.2.2 ∈ T
    have hEcov : extra ⊆ E1 ∪ E2 ∪ E3 := by
      intro t ht
      obtain ⟨htd, h1 | h2 | h3⟩ := Finset.mem_filter.mp ht
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨htd, h1⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨htd, h2⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨htd, h3⟩)
    have hE1 : E1.card ≤ T.card * S.card := by
      have hsub : E1.card ≤ (T ×ˢ S).card := by
        refine Finset.card_le_card_of_injOn (fun t ↦ (t.1, t.2.1)) ?_ ?_
        · intro t ht
          rw [Finset.mem_coe] at ht ⊢
          obtain ⟨htd, h1T⟩ := Finset.mem_filter.mp ht
          have h2S := (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp htd).1).2).1
          exact Finset.mem_product.mpr ⟨h1T, h2S⟩
        · intro t₁ ht₁ t₂ ht₂ heq
          rw [Finset.mem_coe] at ht₁ ht₂
          have hs1 := (Finset.mem_filter.mp (Finset.mem_filter.mp ht₁).1).2.2
          have hs2 := (Finset.mem_filter.mp (Finset.mem_filter.mp ht₂).1).2.2
          rcases t₁ with ⟨a₁, b₁, c₁⟩; rcases t₂ with ⟨a₂, b₂, c₂⟩
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          dsimp only at hs1 hs2
          have : c₁ = c₂ := by omega
          subst this; rfl
      simpa [Finset.card_product] using hsub
    have hE2 : E2.card ≤ T.card * S.card := by
      have hsub : E2.card ≤ (T ×ˢ S).card := by
        refine Finset.card_le_card_of_injOn (fun t ↦ (t.2.1, t.1)) ?_ ?_
        · intro t ht
          rw [Finset.mem_coe] at ht ⊢
          obtain ⟨htd, h2T⟩ := Finset.mem_filter.mp ht
          have h1S := (Finset.mem_product.mp (Finset.mem_filter.mp htd).1).1
          exact Finset.mem_product.mpr ⟨h2T, h1S⟩
        · intro t₁ ht₁ t₂ ht₂ heq
          rw [Finset.mem_coe] at ht₁ ht₂
          have hs1 := (Finset.mem_filter.mp (Finset.mem_filter.mp ht₁).1).2.2
          have hs2 := (Finset.mem_filter.mp (Finset.mem_filter.mp ht₂).1).2.2
          rcases t₁ with ⟨a₁, b₁, c₁⟩; rcases t₂ with ⟨a₂, b₂, c₂⟩
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          dsimp only at hs1 hs2
          have : c₁ = c₂ := by omega
          subst this; rfl
      simpa [Finset.card_product] using hsub
    have hE3 : E3.card ≤ T.card * S.card := by
      have hsub : E3.card ≤ (T ×ˢ S).card := by
        refine Finset.card_le_card_of_injOn (fun t ↦ (t.2.2, t.1)) ?_ ?_
        · intro t ht
          rw [Finset.mem_coe] at ht ⊢
          obtain ⟨htd, h3T⟩ := Finset.mem_filter.mp ht
          have h1S := (Finset.mem_product.mp (Finset.mem_filter.mp htd).1).1
          exact Finset.mem_product.mpr ⟨h3T, h1S⟩
        · intro t₁ ht₁ t₂ ht₂ heq
          rw [Finset.mem_coe] at ht₁ ht₂
          have hs1 := (Finset.mem_filter.mp (Finset.mem_filter.mp ht₁).1).2.2
          have hs2 := (Finset.mem_filter.mp (Finset.mem_filter.mp ht₂).1).2.2
          rcases t₁ with ⟨a₁, b₁, c₁⟩; rcases t₂ with ⟨a₂, b₂, c₂⟩
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          dsimp only at hs1 hs2
          have : b₁ = b₂ := by omega
          subst this; rfl
      simpa [Finset.card_product] using hsub
    calc extra.card
        ≤ (E1 ∪ E2 ∪ E3).card := Finset.card_le_card hEcov
      _ ≤ (E1 ∪ E2).card + E3.card := Finset.card_union_le _ _
      _ ≤ E1.card + E2.card + E3.card := by gcongr; exact Finset.card_union_le _ _
      _ ≤ 3 * T.card * S.card := by nlinarith
  calc (distinctTriples S).card
      ≤ (distinctTriples U ∪ extra).card := Finset.card_le_card hcov
    _ ≤ (distinctTriples U).card + extra.card := Finset.card_union_le _ _
    _ ≤ (distinctTriples U).card + 3 * T.card * S.card := by omega

/- ### Auxiliary Graph `E` from `T₁` and Graph Degree Helpers -/

noncomputable def auxEdges (U T₁ : Finset ℕ) : Finset (ℕ × ℕ) :=
  (U ×ˢ U).filter fun p ↦ p.1 < p.2 ∧ ∃ v ∈ T₁, v ≠ p.1 ∧ v ≠ p.2 ∧ isTriple v p.1 p.2

def inducedEdges (E : Finset (ℕ × ℕ)) (B : Finset ℕ) : Finset (ℕ × ℕ) :=
  E.filter fun p ↦ p.1 ∈ B ∧ p.2 ∈ B

def gNeighbors (E : Finset (ℕ × ℕ)) (B : Finset ℕ) (x : ℕ) : Finset ℕ :=
  B.filter fun y ↦ (x, y) ∈ E ∨ (y, x) ∈ E

lemma auxEdges_sf_disj {U T₁ I : Finset ℕ} (hIsf : IsSumFree (I : Set ℕ))
    (hT1I : T₁ ⊆ I) {x y : ℕ} (hxy : (x, y) ∈ auxEdges U T₁) (hx : x ∈ I) : y ∉ I := by
  intro hy
  obtain ⟨_, _, v, hvT, _, _, htr⟩ := Finset.mem_filter.mp hxy
  have hvI : v ∈ I := hT1I hvT
  rw [isSumFree_iff] at hIsf
  rcases htr with h | h | h
  · exact hIsf v (Finset.mem_coe.mpr hvI) x (Finset.mem_coe.mpr hx)
      (by rw [h]; exact Finset.mem_coe.mpr hy)
  · exact hIsf v (Finset.mem_coe.mpr hvI) y (Finset.mem_coe.mpr hy)
      (by rw [h]; exact Finset.mem_coe.mpr hx)
  · exact hIsf x (Finset.mem_coe.mpr hx) y (Finset.mem_coe.mpr hy)
      (by rw [h]; exact Finset.mem_coe.mpr hvI)

lemma gNeighbors_auxEdges_card_le (U T₁ B : Finset ℕ) (x : ℕ) :
    (gNeighbors (auxEdges U T₁) B x).card ≤ 2 * T₁.card := by
  have hsub : gNeighbors (auxEdges U T₁) B x ⊆
      T₁.biUnion (fun v ↦ ({v + x, v - x, x - v} : Finset ℕ).filter (fun y ↦ y ≠ 0 ∧ isTriple v x y)) := by
    intro y hy
    obtain ⟨_, h1 | h2⟩ := Finset.mem_filter.mp hy
    · obtain ⟨_, hlt, v, hvT, _, _, htr⟩ := Finset.mem_filter.mp h1
      rw [Finset.mem_biUnion]
      refine ⟨v, hvT, Finset.mem_filter.mpr ⟨?_, ?_, htr⟩⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases htr with h | h | h <;> omega
      · omega
    · obtain ⟨_, hlt, v, hvT, _, _, htr⟩ := Finset.mem_filter.mp h2
      rw [Finset.mem_biUnion]
      have htr' : isTriple v x y := by
        rcases htr with h | h | h
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inr (by omega))
      refine ⟨v, hvT, Finset.mem_filter.mpr ⟨?_, ?_, htr'⟩⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases htr' with h | h | h <;> omega
      · rcases htr with h | h | h <;> omega
  have heach : ∀ v ∈ T₁,
      (({v + x, v - x, x - v} : Finset ℕ).filter (fun y ↦ y ≠ 0 ∧ isTriple v x y)).card ≤ 2 := by
    intro v _
    by_cases hvx : v ≤ x
    · have hsub2 : ({v + x, v - x, x - v} : Finset ℕ).filter (fun y ↦ y ≠ 0 ∧ isTriple v x y) ⊆
          {v + x, x - v} := by
        intro y hy
        obtain ⟨hmem, hy0, _⟩ := Finset.mem_filter.mp hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
        rcases hmem with rfl | rfl | rfl
        · exact Or.inl rfl
        · exfalso; omega
        · exact Or.inr rfl
      exact le_trans (Finset.card_le_card hsub2) Finset.card_le_two
    · have hsub2 : ({v + x, v - x, x - v} : Finset ℕ).filter (fun y ↦ y ≠ 0 ∧ isTriple v x y) ⊆
          {v + x, v - x} := by
        intro y hy
        obtain ⟨hmem, hy0, _⟩ := Finset.mem_filter.mp hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
        rcases hmem with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exfalso; omega
      exact le_trans (Finset.card_le_card hsub2) Finset.card_le_two
  calc (gNeighbors (auxEdges U T₁) B x).card
      ≤ (T₁.biUnion fun v ↦
          ({v + x, v - x, x - v} : Finset ℕ).filter (fun y ↦ y ≠ 0 ∧ isTriple v x y)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ v ∈ T₁,
          (({v + x, v - x, x - v} : Finset ℕ).filter (fun y ↦ y ≠ 0 ∧ isTriple v x y)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ T₁, 2 := Finset.sum_le_sum heach
    _ = 2 * T₁.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

lemma edges_lost_le_deg (E : Finset (ℕ × ℕ)) (U B : Finset ℕ) (D : ℕ)
    (hEsub : ∀ p ∈ E, p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 < p.2)
    (_hBsub : B ⊆ U)
    (hdeg : ∀ x ∈ U, (gNeighbors E U x).card ≤ D) :
    E.card ≤ (inducedEdges E B).card + (U \ B).card * D := by
  let lost := E.filter fun p ↦ p.1 ∈ U \ B ∨ p.2 ∈ U \ B
  have hcov : E ⊆ inducedEdges E B ∪ lost := by
    intro p hp
    rw [Finset.mem_union]
    by_cases h1 : p.1 ∈ B
    · by_cases h2 : p.2 ∈ B
      · exact Or.inl (Finset.mem_filter.mpr ⟨hp, h1, h2⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨hp, Or.inr (Finset.mem_sdiff.mpr ⟨(hEsub p hp).2.1, h2⟩)⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hp, Or.inl (Finset.mem_sdiff.mpr ⟨(hEsub p hp).1, h1⟩)⟩)
  have hlost : lost.card ≤ (U \ B).card * D := by
    have hbi : lost ⊆ (U \ B).biUnion (fun x ↦ E.filter (fun p ↦ p.1 = x ∨ p.2 = x)) := by
      intro p hp
      obtain ⟨hpE, h1 | h2⟩ := Finset.mem_filter.mp hp
      · exact Finset.mem_biUnion.mpr ⟨p.1, h1, Finset.mem_filter.mpr ⟨hpE, Or.inl rfl⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨p.2, h2, Finset.mem_filter.mpr ⟨hpE, Or.inr rfl⟩⟩
    have heach : ∀ x ∈ U \ B, (E.filter (fun p ↦ p.1 = x ∨ p.2 = x)).card ≤ D := by
      intro x hx
      have hxU : x ∈ U := (Finset.mem_sdiff.mp hx).1
      have hinj : (E.filter (fun p ↦ p.1 = x ∨ p.2 = x)).card ≤ (gNeighbors E U x).card := by
        refine Finset.card_le_card_of_injOn (fun p ↦ if p.1 = x then p.2 else p.1) ?_ ?_
        · intro p hp
          rw [Finset.mem_coe] at hp ⊢
          obtain ⟨hpE, h1 | h2⟩ := Finset.mem_filter.mp hp
          · simp only [h1, ↓reduceIte]
            exact Finset.mem_filter.mpr ⟨(hEsub p hpE).2.1, Or.inl (by rwa [← h1])⟩
          · have hne : p.1 ≠ x := by have := (hEsub p hpE).2.2; omega
            simp only [hne, ↓reduceIte]
            exact Finset.mem_filter.mpr ⟨(hEsub p hpE).1, Or.inr (by rwa [← h2])⟩
        · intro p₁ hp₁ p₂ hp₂ heq
          rw [Finset.mem_coe] at hp₁ hp₂
          obtain ⟨hp1E, h1a | h1b⟩ := Finset.mem_filter.mp hp₁
          · obtain ⟨hp2E, h2a | h2b⟩ := Finset.mem_filter.mp hp₂
            · simp only [h1a, h2a, ↓reduceIte] at heq
              exact Prod.ext (h1a.trans h2a.symm) heq
            · have hne2 : p₂.1 ≠ x := by have := (hEsub p₂ hp2E).2.2; omega
              simp only [h1a, hne2, ↓reduceIte] at heq
              have := (hEsub p₁ hp1E).2.2; have := (hEsub p₂ hp2E).2.2; omega
          · have hne1 : p₁.1 ≠ x := by have := (hEsub p₁ hp1E).2.2; omega
            obtain ⟨hp2E, h2a | h2b⟩ := Finset.mem_filter.mp hp₂
            · simp only [hne1, h2a, ↓reduceIte] at heq
              have := (hEsub p₁ hp1E).2.2; have := (hEsub p₂ hp2E).2.2; omega
            · have hne2 : p₂.1 ≠ x := by have := (hEsub p₂ hp2E).2.2; omega
              simp only [hne1, hne2, ↓reduceIte] at heq
              exact Prod.ext heq (h1b.trans h2b.symm)
      exact le_trans hinj (hdeg x hxU)
    calc lost.card
        ≤ ((U \ B).biUnion (fun x ↦ E.filter (fun p ↦ p.1 = x ∨ p.2 = x))).card :=
          Finset.card_le_card hbi
      _ ≤ ∑ x ∈ U \ B, (E.filter (fun p ↦ p.1 = x ∨ p.2 = x)).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ U \ B, D := Finset.sum_le_sum heach
      _ = (U \ B).card * D := by rw [Finset.sum_const, smul_eq_mul]
  calc E.card
      ≤ (inducedEdges E B ∪ lost).card := Finset.card_le_card hcov
    _ ≤ (inducedEdges E B).card + lost.card := Finset.card_union_le _ _
    _ ≤ (inducedEdges E B).card + (U \ B).card * D := by omega

lemma sum_gNeighbors_eq_two_mul_induced (E : Finset (ℕ × ℕ)) (B : Finset ℕ)
    (hElt : ∀ p ∈ E, p.1 < p.2) :
    2 * (inducedEdges E B).card ≤ ∑ x ∈ B, (gNeighbors E B x).card := by
  let S := B.sigma (fun x ↦ gNeighbors E B x)
  have hS : S.card = ∑ x ∈ B, (gNeighbors E B x).card := Finset.card_sigma _ _
  rw [← hS]
  let I1 := (inducedEdges E B).image (fun p ↦ (⟨p.1, p.2⟩ : Σ _ : ℕ, ℕ))
  let I2 := (inducedEdges E B).image (fun p ↦ (⟨p.2, p.1⟩ : Σ _ : ℕ, ℕ))
  have hsub1 : I1 ⊆ S := by
    intro s hs
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hpE, h1, h2⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_sigma.mpr ⟨h1, Finset.mem_filter.mpr ⟨h2, Or.inl hpE⟩⟩
  have hsub2 : I2 ⊆ S := by
    intro s hs
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hpE, h1, h2⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_sigma.mpr ⟨h2, Finset.mem_filter.mpr ⟨h1, Or.inr hpE⟩⟩
  have hdisj : Disjoint I1 I2 := by
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    obtain ⟨p1, hp1, rfl⟩ := Finset.mem_image.mp hs1
    obtain ⟨p2, hp2, heq⟩ := Finset.mem_image.mp hs2
    have hlt1 := hElt p1 (Finset.mem_filter.mp hp1).1
    have hlt2 := hElt p2 (Finset.mem_filter.mp hp2).1
    have hfst : p2.2 = p1.1 := congr_arg Sigma.fst heq
    have hsnd : p2.1 = p1.2 := eq_of_heq (Sigma.mk.inj_iff.mp heq).2
    omega
  have hc1 : I1.card = (inducedEdges E B).card := by
    refine Finset.card_image_of_injective _ fun p1 p2 h ↦ ?_
    exact Prod.ext (congr_arg Sigma.fst h) (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  have hc2 : I2.card = (inducedEdges E B).card := by
    refine Finset.card_image_of_injective _ fun p1 p2 h ↦ ?_
    exact Prod.ext (eq_of_heq (Sigma.mk.inj_iff.mp h).2) (congr_arg Sigma.fst h)
  calc 2 * (inducedEdges E B).card
      = I1.card + I2.card := by rw [hc1, hc2]; omega
    _ = (I1 ∪ I2).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ S.card := Finset.card_le_card (Finset.union_subset hsub1 hsub2)

/- ### Step A (3-Graph Peeling) and Step B (Kleitman-Winston Graph Container) -/

noncomputable def stepA (D3 s : ℕ) (Q : Finset ℕ) :
    ℕ → Finset ℕ → Finset ℕ → Finset ℕ × Finset ℕ
  | 0, A, T1 => (A, T1)
  | fuel + 1, A, T1 =>
    let cand := A.filter fun v ↦ D3 ≤ (linkPairs A v).card
    if h : T1.card < s ∧ cand.Nonempty then
      let v := cand.min' h.2
      let A' := A.erase v
      if v ∈ Q then stepA D3 s Q fuel A' (insert v T1)
      else stepA D3 s Q fuel A' T1
    else (A, T1)

lemma stepA_subset_snd (D3 s : ℕ) (Q : Finset ℕ) :
    ∀ (fuel : ℕ) (A T1 : Finset ℕ), T1 ⊆ (stepA D3 s Q fuel A T1).2 := by
  intro fuel
  induction fuel with
  | zero => intro _ _; exact Finset.Subset.rfl
  | succ fuel ih =>
    intro A T1
    dsimp only [stepA]
    set cand := A.filter fun v ↦ D3 ≤ (linkPairs A v).card
    by_cases h : T1.card < s ∧ cand.Nonempty
    · rw [dif_pos h]
      by_cases hvQ : cand.min' h.2 ∈ Q
      · rw [if_pos hvQ]; exact (Finset.subset_insert _ T1).trans (ih _ _)
      · rw [if_neg hvQ]; exact ih _ _
    · rw [dif_neg h]

lemma stepA_invariants_clean (D3 s : ℕ) (Q : Finset ℕ) :
    ∀ (fuel : ℕ) (A T1 : Finset ℕ),
      Disjoint A T1 →
      T1.card ≤ s →
      let res := stepA D3 s Q fuel A T1
      res.1 ⊆ A ∧
      T1 ⊆ res.2 ∧
      res.2 \ T1 ⊆ A ∩ Q ∧
      Disjoint res.1 res.2 ∧
      res.2.card ≤ s ∧
      (A ∩ Q ⊆ res.1 ∪ res.2) ∧
      (A.card ≤ fuel → res.2.card = s ∨ ∀ v ∈ res.1, (linkPairs res.1 v).card < D3) := by
  intro fuel
  induction fuel with
  | zero =>
    intro A T1 hdisj hTs
    dsimp [stepA]
    refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, by simp, hdisj, hTs, ?_, ?_⟩
    · intro x hx; exact Finset.mem_union_left _ (Finset.mem_inter.mp hx).1
    · intro h0
      have hAe : A = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero h0)
      right; intro v hv; simp [hAe] at hv
  | succ fuel ih =>
    intro A T1 hdisj hTs
    dsimp only [stepA]
    set cand := A.filter fun v ↦ D3 ≤ (linkPairs A v).card
    by_cases h : T1.card < s ∧ cand.Nonempty
    · rw [dif_pos h]
      set v := cand.min' h.2
      have hv_cand : v ∈ cand := Finset.min'_mem cand h.2
      have hvA : v ∈ A := (Finset.mem_filter.mp hv_cand).1
      have hvT1 : v ∉ T1 := Finset.disjoint_left.mp hdisj hvA
      have hcard_erase : (A.erase v).card = A.card - 1 := Finset.card_erase_of_mem hvA
      by_cases hvQ : v ∈ Q
      · rw [if_pos hvQ]
        have hdisj' : Disjoint (A.erase v) (insert v T1) := by
          rw [Finset.disjoint_insert_right]
          exact ⟨Finset.notMem_erase v A, Finset.disjoint_of_subset_left (Finset.erase_subset v A) hdisj⟩
        have hT1card : (insert v T1).card = T1.card + 1 := Finset.card_insert_of_notMem hvT1
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih (A.erase v) (insert v T1) hdisj' (by omega)
        refine ⟨h1.trans (Finset.erase_subset v A),
          (Finset.subset_insert v T1).trans h2, ?_, h4, h5, ?_, ?_⟩
        · intro x hx
          obtain ⟨hx2, hxnot⟩ := Finset.mem_sdiff.mp hx
          by_cases hxv : x = v
          · subst hxv; exact Finset.mem_inter.mpr ⟨hvA, hvQ⟩
          · have hxmem : x ∈ (stepA D3 s Q fuel (A.erase v) (insert v T1)).2 \ insert v T1 :=
              Finset.mem_sdiff.mpr ⟨hx2, by simp [hxv, hxnot]⟩
            have := h3 hxmem
            exact Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase (Finset.mem_inter.mp this).1,
              (Finset.mem_inter.mp this).2⟩
        · intro x hx
          obtain ⟨hxA, hxQ⟩ := Finset.mem_inter.mp hx
          by_cases hxv : x = v
          · subst hxv; exact Finset.mem_union_right _ (h2 (Finset.mem_insert_self v T1))
          · exact h6 (Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨hxv, hxA⟩, hxQ⟩)
        · intro hAle; exact h7 (by omega)
      · rw [if_neg hvQ]
        have hdisj' : Disjoint (A.erase v) T1 :=
          Finset.disjoint_of_subset_left (Finset.erase_subset v A) hdisj
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih (A.erase v) T1 hdisj' hTs
        refine ⟨h1.trans (Finset.erase_subset v A), h2, ?_, h4, h5, ?_, ?_⟩
        · intro x hx
          have := h3 hx
          exact Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase (Finset.mem_inter.mp this).1,
            (Finset.mem_inter.mp this).2⟩
        · intro x hx
          obtain ⟨hxA, hxQ⟩ := Finset.mem_inter.mp hx
          have hxv : x ≠ v := fun heq ↦ hvQ (heq ▸ hxQ)
          exact h6 (Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨hxv, hxA⟩, hxQ⟩)
        · intro hAle; exact h7 (by omega)
    · rw [dif_neg h]
      refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, by simp, hdisj, hTs, ?_, ?_⟩
      · intro x hx; exact Finset.mem_union_left _ (Finset.mem_inter.mp hx).1
      · intro _
        by_cases hs : T1.card < s
        · right
          intro v hv
          by_contra hc
          push Not at hc
          exact h ⟨hs, ⟨v, Finset.mem_filter.mpr ⟨hv, hc⟩⟩⟩
        · left; dsimp only; omega

lemma stepA_edges_lb (D3 s : ℕ) (Q : Finset ℕ) (U : Finset ℕ) :
    ∀ (fuel : ℕ) (A T1 : Finset ℕ),
      A ⊆ U →
      Disjoint A T1 →
      T1.card ≤ s →
      (∀ v ∈ T1, D3 ≤ (linkPairs U v).card) →
      ∀ v ∈ (stepA D3 s Q fuel A T1).2, D3 ≤ (linkPairs U v).card := by
  intro fuel
  induction fuel with
  | zero => intro A T1 _ _ _ hT; exact hT
  | succ fuel ih =>
    intro A T1 hAU hdisj hTs hT
    dsimp only [stepA]
    set cand := A.filter fun v ↦ D3 ≤ (linkPairs A v).card
    by_cases h : T1.card < s ∧ cand.Nonempty
    · rw [dif_pos h]
      set v := cand.min' h.2
      have hv_cand : v ∈ cand := Finset.min'_mem cand h.2
      have hvA : v ∈ A := (Finset.mem_filter.mp hv_cand).1
      have hvD : D3 ≤ (linkPairs A v).card := (Finset.mem_filter.mp hv_cand).2
      have hvDU : D3 ≤ (linkPairs U v).card := by
        refine le_trans hvD (Finset.card_le_card fun p hp ↦ ?_)
        obtain ⟨hp1, hlt, htr⟩ := Finset.mem_filter.mp hp
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp1
        rw [linkPairs, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨Finset.erase_subset_erase v hAU h1, Finset.erase_subset_erase v hAU h2⟩, hlt, htr⟩
      have hvT1 : v ∉ T1 := Finset.disjoint_left.mp hdisj hvA
      by_cases hvQ : v ∈ Q
      · rw [if_pos hvQ]
        have hdisj' : Disjoint (A.erase v) (insert v T1) := by
          rw [Finset.disjoint_insert_right]
          exact ⟨Finset.notMem_erase v A, Finset.disjoint_of_subset_left (Finset.erase_subset v A) hdisj⟩
        have hT' : ∀ w ∈ insert v T1, D3 ≤ (linkPairs U w).card := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hwT
          · exact hvDU
          · exact hT w hwT
        exact ih (A.erase v) (insert v T1) ((Finset.erase_subset v A).trans hAU) hdisj'
          (by rw [Finset.card_insert_of_notMem hvT1]; omega) hT'
      · rw [if_neg hvQ]
        exact ih (A.erase v) T1 ((Finset.erase_subset v A).trans hAU)
          (Finset.disjoint_of_subset_left (Finset.erase_subset v A) hdisj) hTs hT
    · rw [dif_neg h]; exact hT

lemma auxEdges_card_lb (U T1 : Finset ℕ) (D3 : ℕ)
    (_hpos : ∀ x ∈ U, 0 < x)
    (hdeg : ∀ v ∈ T1, D3 ≤ (linkPairs U v).card) :
    T1.card * D3 ≤ 2 * (auxEdges U T1).card := by
  let S := T1.sigma (fun v ↦ linkPairs U v)
  have hS : T1.card * D3 ≤ S.card := by
    rw [Finset.card_sigma]
    calc T1.card * D3 = ∑ _v ∈ T1, D3 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ v ∈ T1, (linkPairs U v).card := Finset.sum_le_sum hdeg
  have hfiber : S.card ≤ 2 * (auxEdges U T1).card := by
    let E := auxEdges U T1
    have hsub : S ⊆ E.biUnion (fun p ↦ ({p.2 - p.1, p.1 + p.2} : Finset ℕ).image (fun v ↦ (⟨v, p⟩ : Σ _ : ℕ, ℕ × ℕ))) := by
      intro s hs
      rcases s with ⟨v, p⟩
      obtain ⟨hvT, hp⟩ := Finset.mem_sigma.mp hs
      obtain ⟨hp1, hlt, htr⟩ := Finset.mem_filter.mp hp
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp1
      have hpE : p ∈ E := by
        simp only [E, auxEdges, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨Finset.mem_of_mem_erase h1, Finset.mem_of_mem_erase h2⟩, hlt,
          v, hvT, (Finset.mem_erase.mp h1).1.symm, (Finset.mem_erase.mp h2).1.symm, htr⟩
      rw [Finset.mem_biUnion]
      refine ⟨p, hpE, Finset.mem_image.mpr ⟨v, ?_, rfl⟩⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      dsimp only at hlt htr
      rcases htr with h | h | h
      · exact Or.inl (by omega)
      · omega
      · exact Or.inr (by omega)
    calc S.card
        ≤ (E.biUnion (fun p ↦ ({p.2 - p.1, p.1 + p.2} : Finset ℕ).image
            (fun v ↦ (⟨v, p⟩ : Σ _ : ℕ, ℕ × ℕ)))).card := Finset.card_le_card hsub
      _ ≤ ∑ p ∈ E, (({p.2 - p.1, p.1 + p.2} : Finset ℕ).image
            (fun v ↦ (⟨v, p⟩ : Σ _ : ℕ, ℕ × ℕ))).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ E, 2 := Finset.sum_le_sum fun p _ ↦
            le_trans Finset.card_image_le Finset.card_le_two
      _ = 2 * E.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  exact le_trans hS hfiber

lemma stepA_replay (D3 s : ℕ) (Q1 Q2 : Finset ℕ) (hQ : Q2 ⊆ Q1) :
    ∀ (fuel : ℕ) (A T1 : Finset ℕ),
      Disjoint A T1 →
      (stepA D3 s Q1 fuel A T1).2 \ T1 ⊆ Q2 →
      stepA D3 s Q2 fuel A T1 = stepA D3 s Q1 fuel A T1 := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _; rfl
  | succ fuel ih =>
    intro A T1 hdisj hTsub
    dsimp only [stepA]
    set cand := A.filter fun v ↦ D3 ≤ (linkPairs A v).card
    by_cases h : T1.card < s ∧ cand.Nonempty
    · rw [dif_pos h, dif_pos h]
      set v := cand.min' h.2
      have hvA : v ∈ A := (Finset.mem_filter.mp (Finset.min'_mem cand h.2)).1
      have hvT1 : v ∉ T1 := Finset.disjoint_left.mp hdisj hvA
      by_cases hvQ1 : v ∈ Q1
      · have hsub2 : insert v T1 ⊆ (stepA D3 s Q1 fuel (A.erase v) (insert v T1)).2 :=
          stepA_subset_snd D3 s Q1 fuel (A.erase v) (insert v T1)
        have hstep1 : stepA D3 s Q1 (fuel + 1) A T1 = stepA D3 s Q1 fuel (A.erase v) (insert v T1) := by
          dsimp only [stepA]; rw [dif_pos h, if_pos hvQ1]
        have hvQ2 : v ∈ Q2 := by
          apply hTsub
          rw [hstep1, Finset.mem_sdiff]
          exact ⟨hsub2 (Finset.mem_insert_self v T1), hvT1⟩
        rw [if_pos hvQ2, if_pos hvQ1]
        apply ih
        · rw [Finset.disjoint_insert_right]
          exact ⟨Finset.notMem_erase v A,
            Finset.disjoint_of_subset_left (Finset.erase_subset v A) hdisj⟩
        · intro x hx
          apply hTsub
          rw [hstep1, Finset.mem_sdiff]
          obtain ⟨hx2, hxnot⟩ := Finset.mem_sdiff.mp hx
          exact ⟨hx2, fun hxT ↦ hxnot (Finset.mem_insert_of_mem hxT)⟩
      · have hvQ2 : v ∉ Q2 := fun hc ↦ hvQ1 (hQ hc)
        rw [if_neg hvQ2, if_neg hvQ1]
        have hstep1 : stepA D3 s Q1 (fuel + 1) A T1 = stepA D3 s Q1 fuel (A.erase v) T1 := by
          dsimp only [stepA]; rw [dif_pos h, if_neg hvQ1]
        rw [hstep1] at hTsub
        exact ih (A.erase v) T1
          (Finset.disjoint_of_subset_left (Finset.erase_subset v A) hdisj) hTsub
    · rw [dif_neg h, dif_neg h]

/- ### Step B: Kleitman-Winston Graph Container -/

noncomputable def stepB (E : Finset (ℕ × ℕ)) (d : ℕ) (Q : Finset ℕ) :
    ℕ → Finset ℕ → Finset ℕ → Finset ℕ × Finset ℕ
  | 0, B, T2 => (B, T2)
  | fuel + 1, B, T2 =>
    let cand := B.filter fun v ↦ d ≤ (gNeighbors E B v).card
    if h : cand.Nonempty then
      let v := cand.min' h
      if v ∈ Q then
        let B' := (B.erase v) \ gNeighbors E B v
        stepB E d Q fuel B' (insert v T2)
      else
        stepB E d Q fuel (B.erase v) T2
    else (B, T2)

lemma stepB_invariants (E : Finset (ℕ × ℕ)) (d : ℕ) (Q : Finset ℕ)
    (hQindep : ∀ x ∈ Q, ∀ y ∈ Q, (x, y) ∉ E)
    (hElt : ∀ p ∈ E, p.1 < p.2) :
    ∀ (fuel : ℕ) (B T2 : Finset ℕ),
      Disjoint B T2 →
      let res := stepB E d Q fuel B T2
      res.1 ⊆ B ∧
      T2 ⊆ res.2 ∧
      res.2 \ T2 ⊆ B ∩ Q ∧
      Disjoint res.1 res.2 ∧
      (res.2 \ T2).card * (d + 1) ≤ B.card - res.1.card ∧
      (B ∩ Q ⊆ res.1 ∪ res.2) ∧
      (B.card ≤ fuel → ∀ v ∈ res.1, (gNeighbors E res.1 v).card < d) := by
  intro fuel
  induction fuel with
  | zero =>
    intro B T2 hdisj
    dsimp [stepB]
    refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, by simp, hdisj, by simp, ?_, ?_⟩
    · intro x hx; exact Finset.mem_union_left _ (Finset.mem_inter.mp hx).1
    · intro h0
      have hBe : B = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero h0)
      intro v hv; simp [hBe] at hv
  | succ fuel ih =>
    intro B T2 hdisj
    dsimp only [stepB]
    set cand := B.filter fun v ↦ d ≤ (gNeighbors E B v).card
    by_cases h : cand.Nonempty
    · rw [dif_pos h]
      set v := cand.min' h
      have hv_cand : v ∈ cand := Finset.min'_mem cand h
      have hvB : v ∈ B := (Finset.mem_filter.mp hv_cand).1
      have hvd : d ≤ (gNeighbors E B v).card := (Finset.mem_filter.mp hv_cand).2
      have hvT2 : v ∉ T2 := Finset.disjoint_left.mp hdisj hvB
      by_cases hvQ : v ∈ Q
      · rw [if_pos hvQ]
        set B' := (B.erase v) \ gNeighbors E B v
        have hB'sub : B' ⊆ B := Finset.sdiff_subset.trans (Finset.erase_subset v B)
        have hdisj' : Disjoint B' (insert v T2) := by
          rw [Finset.disjoint_insert_right]
          exact ⟨fun hc ↦ Finset.notMem_erase v B (Finset.sdiff_subset hc),
            Finset.disjoint_of_subset_left hB'sub hdisj⟩
        have hv_not_nb : v ∉ gNeighbors E B v := by
          intro hmem
          obtain ⟨_, h1 | h2⟩ := Finset.mem_filter.mp hmem
          · exact Nat.lt_irrefl v (hElt (v, v) h1)
          · exact Nat.lt_irrefl v (hElt (v, v) h2)
        have hnb_sub : gNeighbors E B v ⊆ B.erase v := by
          intro w hw
          have hwB := (Finset.mem_filter.mp hw).1
          exact Finset.mem_erase.mpr ⟨fun heq ↦ hv_not_nb (heq ▸ hw), hwB⟩
        have hcardB' : B'.card + (gNeighbors E B v).card + 1 = B.card := by
          have h1 := Finset.card_sdiff_add_card_eq_card hnb_sub
          have h2 := Finset.card_erase_add_one hvB
          change B'.card + (gNeighbors E B v).card = (B.erase v).card at h1
          omega
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih B' (insert v T2) hdisj'
        have hcard_res_le : (stepB E d Q fuel B' (insert v T2)).1.card ≤ B'.card :=
          Finset.card_le_card h1
        have hsdiff_card : ((stepB E d Q fuel B' (insert v T2)).2 \ T2).card =
            ((stepB E d Q fuel B' (insert v T2)).2 \ insert v T2).card + 1 := by
          have hsub_t : T2 ⊆ (stepB E d Q fuel B' (insert v T2)).2 :=
            (Finset.subset_insert v T2).trans h2
          have hsub_vt : insert v T2 ⊆ (stepB E d Q fuel B' (insert v T2)).2 := h2
          have c1 := Finset.card_sdiff_add_card_eq_card hsub_t
          have c2 := Finset.card_sdiff_add_card_eq_card hsub_vt
          have c3 := Finset.card_insert_of_notMem hvT2
          omega
        refine ⟨h1.trans hB'sub, (Finset.subset_insert v T2).trans h2, ?_, h4, ?_, ?_, ?_⟩
        · intro x hx
          obtain ⟨hx2, hxnot⟩ := Finset.mem_sdiff.mp hx
          by_cases hxv : x = v
          · subst hxv; exact Finset.mem_inter.mpr ⟨hvB, hvQ⟩
          · have hxmem : x ∈ (stepB E d Q fuel B' (insert v T2)).2 \ insert v T2 :=
              Finset.mem_sdiff.mpr ⟨hx2, by simp [hxv, hxnot]⟩
            have := h3 hxmem
            exact Finset.mem_inter.mpr ⟨hB'sub (Finset.mem_inter.mp this).1,
              (Finset.mem_inter.mp this).2⟩
        · rw [hsdiff_card, add_mul, one_mul]
          omega
        · intro x hx
          obtain ⟨hxB, hxQ⟩ := Finset.mem_inter.mp hx
          by_cases hxv : x = v
          · subst hxv; exact Finset.mem_union_right _ (h2 (Finset.mem_insert_self v T2))
          · have hxnotnb : x ∉ gNeighbors E B v := by
              intro hnb
              obtain ⟨_, h1' | h2'⟩ := Finset.mem_filter.mp hnb
              · exact hQindep v hvQ x hxQ h1'
              · exact hQindep x hxQ v hvQ h2'
            exact h6 (Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr
              ⟨Finset.mem_erase.mpr ⟨hxv, hxB⟩, hxnotnb⟩, hxQ⟩)
        · intro hBle; exact h7 (by omega)
      · rw [if_neg hvQ]
        have hcard_erase : (B.erase v).card = B.card - 1 := Finset.card_erase_of_mem hvB
        have hdisj' : Disjoint (B.erase v) T2 :=
          Finset.disjoint_of_subset_left (Finset.erase_subset v B) hdisj
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih (B.erase v) T2 hdisj'
        have hcard_res_le : (stepB E d Q fuel (B.erase v) T2).1.card ≤ (B.erase v).card :=
          Finset.card_le_card h1
        refine ⟨h1.trans (Finset.erase_subset v B), h2, ?_, h4, by omega, ?_, ?_⟩
        · intro x hx
          have := h3 hx
          exact Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase (Finset.mem_inter.mp this).1,
            (Finset.mem_inter.mp this).2⟩
        · intro x hx
          obtain ⟨hxB, hxQ⟩ := Finset.mem_inter.mp hx
          have hxv : x ≠ v := fun heq ↦ hvQ (heq ▸ hxQ)
          exact h6 (Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨hxv, hxB⟩, hxQ⟩)
        · intro hBle; exact h7 (by omega)
    · rw [dif_neg h]
      refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, by simp, hdisj, by simp, ?_, ?_⟩
      · intro x hx; exact Finset.mem_union_left _ (Finset.mem_inter.mp hx).1
      · intro _ v hv
        by_contra hc
        push Not at hc
        exact h ⟨v, Finset.mem_filter.mpr ⟨hv, hc⟩⟩

lemma stepB_replay (E : Finset (ℕ × ℕ)) (d : ℕ) (Q1 Q2 : Finset ℕ) (hQ : Q2 ⊆ Q1)
    (hQ1indep : ∀ x ∈ Q1, ∀ y ∈ Q1, (x, y) ∉ E)
    (hElt : ∀ p ∈ E, p.1 < p.2) :
    ∀ (fuel : ℕ) (B T2 : Finset ℕ),
      Disjoint B T2 →
      (stepB E d Q1 fuel B T2).2 \ T2 ⊆ Q2 →
      stepB E d Q2 fuel B T2 = stepB E d Q1 fuel B T2 := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _; rfl
  | succ fuel ih =>
    intro B T2 hdisj hTsub
    dsimp only [stepB]
    set cand := B.filter fun v ↦ d ≤ (gNeighbors E B v).card
    by_cases h : cand.Nonempty
    · rw [dif_pos h, dif_pos h]
      set v := cand.min' h
      have hvB : v ∈ B := (Finset.mem_filter.mp (Finset.min'_mem cand h)).1
      have hvT2 : v ∉ T2 := Finset.disjoint_left.mp hdisj hvB
      by_cases hvQ1 : v ∈ Q1
      · set B' := (B.erase v) \ gNeighbors E B v
        have hB'sub : B' ⊆ B := Finset.sdiff_subset.trans (Finset.erase_subset v B)
        have hdisj' : Disjoint B' (insert v T2) := by
          rw [Finset.disjoint_insert_right]
          exact ⟨fun hc ↦ Finset.notMem_erase v B (Finset.sdiff_subset hc),
            Finset.disjoint_of_subset_left hB'sub hdisj⟩
        have hsub2 : insert v T2 ⊆ (stepB E d Q1 fuel B' (insert v T2)).2 :=
          (stepB_invariants E d Q1 hQ1indep hElt fuel B' (insert v T2) hdisj').2.1
        have hstep1 : stepB E d Q1 (fuel + 1) B T2 = stepB E d Q1 fuel B' (insert v T2) := by
          dsimp only [stepB]; rw [dif_pos h, if_pos hvQ1]
        have hvQ2 : v ∈ Q2 := by
          apply hTsub
          rw [hstep1, Finset.mem_sdiff]
          exact ⟨hsub2 (Finset.mem_insert_self v T2), hvT2⟩
        rw [if_pos hvQ2, if_pos hvQ1]
        apply ih B' (insert v T2) hdisj'
        intro x hx
        apply hTsub
        rw [hstep1, Finset.mem_sdiff]
        obtain ⟨hx2, hxnot⟩ := Finset.mem_sdiff.mp hx
        exact ⟨hx2, fun hxT ↦ hxnot (Finset.mem_insert_of_mem hxT)⟩
      · have hvQ2 : v ∉ Q2 := fun hc ↦ hvQ1 (hQ hc)
        rw [if_neg hvQ2, if_neg hvQ1]
        have hstep1 : stepB E d Q1 (fuel + 1) B T2 = stepB E d Q1 fuel (B.erase v) T2 := by
          dsimp only [stepB]; rw [dif_pos h, if_neg hvQ1]
        rw [hstep1] at hTsub
        exact ih (B.erase v) T2
          (Finset.disjoint_of_subset_left (Finset.erase_subset v B) hdisj) hTsub
    · rw [dif_neg h, dif_neg h]

/- ### Multi-Round Container Algorithm -/

noncomputable def buildContainer (n M Ks : ℕ) (Q : Finset ℕ) :
    ℕ → Finset ℕ → Finset ℕ → Finset ℕ × Finset ℕ
  | 0, U, T => (U, T)
  | rounds + 1, U, T =>
    let D3 := n / M
    let s := 8 * M * Ks
    let resA := stepA D3 s Q U.card U ∅
    let A := resA.1
    let T1 := resA.2
    if T1.card < s then
      -- Terminated cleanly: every v ∈ A has deg3 A v < D3!
      (A, T ∪ T1)
    else if n ≤ 16 * M * (U \ A).card then
      -- Case 2a: U already shrank by >= n / (16 * M)!
      buildContainer n M Ks Q rounds A (T ∪ T1)
    else
      -- Case 2b: run Step B on G[A] with threshold Ks
      let E := inducedEdges (auxEdges U T1) A
      let resB := stepB E Ks Q A.card A ∅
      buildContainer n M Ks Q rounds resB.1 (T ∪ T1 ∪ resB.2)

lemma buildContainer_invariants (n M Ks : ℕ) (hM : 1 ≤ M) (hKs : 1 ≤ Ks)
    (hn : 2 * M ≤ n) (Q : Finset ℕ) (hQsf : IsSumFree (Q : Set ℕ)) :
    ∀ (rounds : ℕ) (U T : Finset ℕ),
      U ⊆ Finset.Icc 1 n →
      Disjoint U T →
      T ⊆ Q →
      let res := buildContainer n M Ks Q rounds U T
      res.1 ⊆ U ∧
      T ⊆ res.2 ∧
      res.2 ⊆ Q ∧
      Disjoint res.1 res.2 ∧
      (U ∩ Q ⊆ res.1 ∪ res.2) ∧
      (res.2 \ T).card ≤ rounds * (8 * M * Ks + n / Ks) ∧
      ((∀ v ∈ res.1, (linkPairs res.1 v).card < n / M) ∨
        rounds * n ≤ 32 * M * (U.card - res.1.card)) := by
  intro rounds
  induction rounds with
  | zero =>
    intro U T _ hdisj hTQ
    dsimp [buildContainer]
    refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, hTQ, hdisj, ?_, by simp, Or.inr (by simp)⟩
    intro x hx; exact Finset.mem_union_left _ (Finset.mem_inter.mp hx).1
  | succ rounds ih =>
    intro U T hUsub hdisj hTQ
    dsimp only [buildContainer]
    set D3 := n / M
    set s := 8 * M * Ks
    set resA := stepA D3 s Q U.card U ∅
    set A := resA.1
    set T1 := resA.2
    have hUpos : ∀ x ∈ U, 0 < x := fun x hx ↦ (Finset.mem_Icc.mp (hUsub hx)).1
    have hUcard : U.card ≤ n := by
      calc U.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hUsub
        _ = n := by simp
    obtain ⟨hAsub, _, hT1sub, hAT1disj, hT1card, hUQ, hAterm⟩ :=
      stepA_invariants_clean D3 s Q U.card U ∅ (Finset.disjoint_empty_right U) (Nat.zero_le s)
    change A ⊆ U at hAsub
    change T1 \ ∅ ⊆ U ∩ Q at hT1sub
    change Disjoint A T1 at hAT1disj
    change T1.card ≤ s at hT1card
    change U ∩ Q ⊆ A ∪ T1 at hUQ
    change U.card ≤ U.card → T1.card = s ∨ ∀ v ∈ A, (linkPairs A v).card < D3 at hAterm
    simp only [Finset.sdiff_empty] at hT1sub
    have hT1Q : T1 ⊆ Q := fun x hx ↦ (Finset.mem_inter.mp (hT1sub hx)).2
    have hT1U : T1 ⊆ U := fun x hx ↦ (Finset.mem_inter.mp (hT1sub hx)).1
    have hT1Tdisj : Disjoint T1 T := Finset.disjoint_of_subset_left hT1U hdisj
    have hA_TT1_disj : Disjoint A (T ∪ T1) :=
      Finset.disjoint_union_right.mpr ⟨Finset.disjoint_of_subset_left hAsub hdisj, hAT1disj⟩
    by_cases hlt : T1.card < s
    · rw [if_pos hlt]
      have hdegA : ∀ v ∈ A, (linkPairs A v).card < D3 := by
        rcases hAterm le_rfl with heq | hall
        · omega
        · exact hall
      refine ⟨hAsub, Finset.subset_union_left, Finset.union_subset hTQ hT1Q, hA_TT1_disj, ?_, ?_,
        Or.inl hdegA⟩
      · intro x hx
        rcases Finset.mem_union.mp (hUQ hx) with hxA | hxT1
        · exact Finset.mem_union_left _ hxA
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ hxT1)
      · calc ((T ∪ T1) \ T).card
            ≤ T1.card := Finset.card_le_card (by intro x hx; simp only [Finset.mem_sdiff, Finset.mem_union] at hx; exact hx.1.resolve_left hx.2)
          _ ≤ s := hT1card
          _ ≤ (rounds + 1) * (s + n / Ks) := by
              have : 1 * s ≤ (rounds + 1) * (s + n / Ks) :=
                Nat.mul_le_mul (Nat.succ_pos _) (Nat.le_add_right _ _)
              omega
    · rw [if_neg hlt]
      have hT1eq : T1.card = s := by omega
      by_cases hdrop : n ≤ 16 * M * (U \ A).card
      · rw [if_pos hdrop]
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
          ih A (T ∪ T1) (hAsub.trans hUsub) hA_TT1_disj (Finset.union_subset hTQ hT1Q)
        have hUAcard : (U \ A).card = U.card - A.card := by
          have := Finset.card_sdiff_add_card_eq_card hAsub; omega
        have hAcard_le : A.card ≤ U.card := Finset.card_le_card hAsub
        have hres_le_A : (buildContainer n M Ks Q rounds A (T ∪ T1)).1.card ≤ A.card :=
          Finset.card_le_card h1
        refine ⟨h1.trans hAsub, Finset.subset_union_left.trans h2, h3, h4, ?_, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_union.mp (hUQ hx) with hxA | hxT1
          · exact h5 (Finset.mem_inter.mpr ⟨hxA, (Finset.mem_inter.mp hx).2⟩)
          · exact Finset.mem_union_right _ (h2 (Finset.mem_union_right _ hxT1))
        · have hsub : (buildContainer n M Ks Q rounds A (T ∪ T1)).2 \ T ⊆
              ((buildContainer n M Ks Q rounds A (T ∪ T1)).2 \ (T ∪ T1)) ∪ T1 := by
            intro x hx
            obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.mp hx
            rw [Finset.mem_union]
            by_cases hxT1 : x ∈ T1
            · exact Or.inr hxT1
            · exact Or.inl (Finset.mem_sdiff.mpr ⟨hx1, by simp [hx2, hxT1]⟩)
          calc ((buildContainer n M Ks Q rounds A (T ∪ T1)).2 \ T).card
              ≤ (((buildContainer n M Ks Q rounds A (T ∪ T1)).2 \ (T ∪ T1)) ∪ T1).card :=
                Finset.card_le_card hsub
            _ ≤ ((buildContainer n M Ks Q rounds A (T ∪ T1)).2 \ (T ∪ T1)).card + T1.card :=
                Finset.card_union_le _ _
            _ ≤ rounds * (s + n / Ks) + s := by omega
            _ ≤ (rounds + 1) * (s + n / Ks) := by
                rw [Nat.add_mul, one_mul]
                have := Nat.zero_le (n / Ks)
                omega
        · rcases h7 with hterm | hshrink
          · exact Or.inl hterm
          · right
            rw [Nat.add_mul, one_mul]
            have h1step : n ≤ 32 * M * (U.card - A.card) := by
              calc n ≤ 16 * M * (U \ A).card := hdrop
                _ = 16 * M * (U.card - A.card) := by rw [hUAcard]
                _ ≤ 32 * M * (U.card - A.card) := Nat.mul_le_mul_right _ (by omega)
            have hsub_add : U.card - (buildContainer n M Ks Q rounds A (T ∪ T1)).1.card =
                (U.card - A.card) + (A.card - (buildContainer n M Ks Q rounds A (T ∪ T1)).1.card) := by
              omega
            rw [hsub_add, Nat.mul_add]
            omega
      · rw [if_neg hdrop]
        set E0 := auxEdges U T1
        set E := inducedEdges E0 A
        have hE0_sub : ∀ p ∈ E0, p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 < p.2 := by
          intro p hp
          obtain ⟨hp1, hltp, _⟩ := Finset.mem_filter.mp hp
          exact ⟨(Finset.mem_product.mp hp1).1, (Finset.mem_product.mp hp1).2, hltp⟩
        have hE_lt : ∀ p ∈ E, p.1 < p.2 := fun p hp ↦ (hE0_sub p (Finset.mem_filter.mp hp).1).2.2
        have hE_indep : ∀ x ∈ Q, ∀ y ∈ Q, (x, y) ∉ E := by
          intro x hx y hy hxy
          exact auxEdges_sf_disj hQsf hT1Q (Finset.mem_filter.mp hxy).1 hx hy
        set resB := stepB E Ks Q A.card A ∅
        set B := resB.1
        set T2 := resB.2
        obtain ⟨hBsub, _, hT2sub, hBT2disj, hT2drop, hAQ, hBdeg⟩ :=
          stepB_invariants E Ks Q hE_indep hE_lt A.card A ∅ (Finset.disjoint_empty_right A)
        change B ⊆ A at hBsub
        change T2 \ ∅ ⊆ A ∩ Q at hT2sub
        change Disjoint B T2 at hBT2disj
        change (T2 \ ∅).card * (Ks + 1) ≤ A.card - B.card at hT2drop
        change A ∩ Q ⊆ B ∪ T2 at hAQ
        change A.card ≤ A.card → ∀ v ∈ B, (gNeighbors E B v).card < Ks at hBdeg
        simp only [Finset.sdiff_empty] at hT2sub hT2drop
        have hT2Q : T2 ⊆ Q := fun x hx ↦ (Finset.mem_inter.mp (hT2sub hx)).2
        have hT2A : T2 ⊆ A := fun x hx ↦ (Finset.mem_inter.mp (hT2sub hx)).1
        have hB_disj : Disjoint B (T ∪ T1 ∪ T2) := by
          rw [Finset.disjoint_union_right]
          exact ⟨Finset.disjoint_of_subset_left hBsub hA_TT1_disj, hBT2disj⟩
        -- Bound T2.card ≤ n / Ks
        have hT2card : T2.card ≤ n / Ks := by
          have hA_le_n : A.card ≤ n := le_trans (Finset.card_le_card hAsub) hUcard
          have hmul : T2.card * Ks ≤ n := by
            calc T2.card * Ks ≤ T2.card * (Ks + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
              _ ≤ A.card - B.card := hT2drop
              _ ≤ n := by omega
          exact (Nat.le_div_iff_mul_le hKs).mpr hmul
        -- Lower bound on A.card - B.card: 32 * M * (A.card - B.card) ≥ n
        have hABdrop : n ≤ 32 * M * (A.card - B.card) := by
          have hT1deg : ∀ v ∈ T1, D3 ≤ (linkPairs U v).card :=
            stepA_edges_lb D3 s Q U U.card U ∅ Finset.Subset.rfl
              (Finset.disjoint_empty_right U) (Nat.zero_le s) (by simp)
          have hE0_lb : s * D3 ≤ 2 * E0.card := by
            rw [← hT1eq]; exact auxEdges_card_lb U T1 D3 hUpos hT1deg
          have hD3_lb : n ≤ 2 * M * D3 := by
            have hdiv : M * D3 + n % M = n := Nat.div_add_mod n M
            have hmod : n % M < M := Nat.mod_lt n hM
            have hD3_1 : 1 ≤ D3 := (Nat.le_div_iff_mul_le hM).mpr (by omega)
            have hMle : M ≤ M * D3 := by
              calc M = M * 1 := (Nat.mul_one M).symm
                _ ≤ M * D3 := Nat.mul_le_mul_left M hD3_1
            have h2M : 2 * M * D3 = M * D3 + M * D3 := by ring
            omega
          have hE0_sn : s * n ≤ 4 * M * E0.card := by
            calc s * n ≤ s * (2 * M * D3) := Nat.mul_le_mul_left s hD3_lb
              _ = 2 * M * (s * D3) := by ring
              _ ≤ 2 * M * (2 * E0.card) := Nat.mul_le_mul_left _ hE0_lb
              _ = 4 * M * E0.card := by ring
          have hE0_lost : E0.card ≤ E.card + (U \ A).card * (2 * s) := by
            have hdeg0 : ∀ x ∈ U, (gNeighbors E0 U x).card ≤ 2 * s := by
              intro x _
              rw [← hT1eq]; exact gNeighbors_auxEdges_card_le U T1 U x
            exact edges_lost_le_deg E0 U A (2 * s) hE0_sub hAsub hdeg0
          have hE_sn : s * n ≤ 8 * M * E.card := by
            have hlt_drop : 16 * M * (U \ A).card < n := by omega
            have h1 : 8 * M * E0.card ≤ 8 * M * E.card + 16 * M * (U \ A).card * s := by
              have := Nat.mul_le_mul_left (8 * M) hE0_lost
              calc 8 * M * E0.card ≤ 8 * M * (E.card + (U \ A).card * (2 * s)) := this
                _ = 8 * M * E.card + 16 * M * (U \ A).card * s := by ring
            have h2 : 16 * M * (U \ A).card * s ≤ s * n := by
              calc 16 * M * (U \ A).card * s ≤ n * s := Nat.mul_le_mul_right s (by omega)
                _ = s * n := Nat.mul_comm n s
            nlinarith
          -- Upper bound on inducedEdges E B
          have hEB_ub : 2 * (inducedEdges E B).card ≤ n * Ks := by
            have h1 := sum_gNeighbors_eq_two_mul_induced E B hE_lt
            have h2 : ∑ x ∈ B, (gNeighbors E B x).card ≤ ∑ _x ∈ B, Ks :=
              Finset.sum_le_sum fun x hx ↦ le_of_lt (hBdeg le_rfl x hx)
            have hBcard : B.card ≤ n := le_trans (Finset.card_le_card (hBsub.trans hAsub)) hUcard
            calc 2 * (inducedEdges E B).card
                ≤ ∑ x ∈ B, (gNeighbors E B x).card := h1
              _ ≤ ∑ _x ∈ B, Ks := h2
              _ = B.card * Ks := by rw [Finset.sum_const, smul_eq_mul]
              _ ≤ n * Ks := Nat.mul_le_mul_right Ks hBcard
          -- Edges lost from E to inducedEdges E B
          have hE_subA : ∀ p ∈ E, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 < p.2 := by
            intro p hp
            obtain ⟨hp0, h1, h2⟩ := Finset.mem_filter.mp hp
            exact ⟨h1, h2, (hE0_sub p hp0).2.2⟩
          have hE_degA : ∀ x ∈ A, (gNeighbors E A x).card ≤ 2 * s := by
            intro x _
            have hsub : gNeighbors E A x ⊆ gNeighbors E0 A x := by
              intro y hy
              obtain ⟨hyA, h1 | h2⟩ := Finset.mem_filter.mp hy
              · exact Finset.mem_filter.mpr ⟨hyA, Or.inl (Finset.mem_filter.mp h1).1⟩
              · exact Finset.mem_filter.mpr ⟨hyA, Or.inr (Finset.mem_filter.mp h2).1⟩
            calc (gNeighbors E A x).card ≤ (gNeighbors E0 A x).card := Finset.card_le_card hsub
              _ ≤ 2 * T1.card := gNeighbors_auxEdges_card_le U T1 A x
              _ = 2 * s := by rw [hT1eq]
          have hE_lostB : E.card ≤ (inducedEdges E B).card + (A \ B).card * (2 * s) :=
            edges_lost_le_deg E A B (2 * s) hE_subA hBsub hE_degA
          have hABcard : (A \ B).card = A.card - B.card := by
            have := Finset.card_sdiff_add_card_eq_card hBsub; omega
          rw [hABcard] at hE_lostB
          have hsn_bound : s * n ≤ s * (32 * M * (A.card - B.card)) := by
            have hs_def : s = 8 * M * Ks := rfl
            have h8M_EB : 16 * M * (inducedEdges E B).card ≤ s * n := by
              calc 16 * M * (inducedEdges E B).card
                  = 8 * M * (2 * (inducedEdges E B).card) := by ring
                _ ≤ 8 * M * (n * Ks) := Nat.mul_le_mul_left _ hEB_ub
                _ = (8 * M * Ks) * n := by ring
                _ = s * n := by rw [hs_def]
            have h16M : 16 * M * E.card ≤ 16 * M * (inducedEdges E B).card +
                s * (32 * M * (A.card - B.card)) := by
              have := Nat.mul_le_mul_left (16 * M) hE_lostB
              calc 16 * M * E.card
                  ≤ 16 * M * ((inducedEdges E B).card + (A.card - B.card) * (2 * s)) := this
                _ = 16 * M * (inducedEdges E B).card + s * (32 * M * (A.card - B.card)) := by ring
            nlinarith
          have hs_pos : 0 < s := by
            change 0 < 8 * M * Ks; positivity
          exact Nat.le_of_mul_le_mul_left hsn_bound hs_pos
        -- Apply induction hypothesis
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
          ih B (T ∪ T1 ∪ T2) ((hBsub.trans hAsub).trans hUsub) hB_disj
            (Finset.union_subset (Finset.union_subset hTQ hT1Q) hT2Q)
        have hBcard_le_A : B.card ≤ A.card := Finset.card_le_card hBsub
        have hAcard_le_U : A.card ≤ U.card := Finset.card_le_card hAsub
        have hres_le_B : (buildContainer n M Ks Q rounds B (T ∪ T1 ∪ T2)).1.card ≤ B.card :=
          Finset.card_le_card h1
        refine ⟨h1.trans (hBsub.trans hAsub),
          (Finset.subset_union_left.trans Finset.subset_union_left).trans h2, h3, h4, ?_, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_union.mp (hUQ hx) with hxA | hxT1
          · rcases Finset.mem_union.mp (hAQ (Finset.mem_inter.mpr ⟨hxA, (Finset.mem_inter.mp hx).2⟩))
              with hxB | hxT2
            · exact h5 (Finset.mem_inter.mpr ⟨hxB, (Finset.mem_inter.mp hx).2⟩)
            · exact Finset.mem_union_right _ (h2 (Finset.mem_union_right _ hxT2))
          · exact Finset.mem_union_right _
              (h2 (Finset.mem_union_left _ (Finset.mem_union_right _ hxT1)))
        · have hsub : (buildContainer n M Ks Q rounds B (T ∪ T1 ∪ T2)).2 \ T ⊆
              ((buildContainer n M Ks Q rounds B (T ∪ T1 ∪ T2)).2 \ (T ∪ T1 ∪ T2)) ∪ (T1 ∪ T2) := by
            intro x hx
            obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.mp hx
            rw [Finset.mem_union]
            by_cases hx12 : x ∈ T1 ∪ T2
            · exact Or.inr hx12
            · left
              refine Finset.mem_sdiff.mpr ⟨hx1, ?_⟩
              simp only [Finset.mem_union] at hx12 ⊢
              tauto
          calc ((buildContainer n M Ks Q rounds B (T ∪ T1 ∪ T2)).2 \ T).card
              ≤ (((buildContainer n M Ks Q rounds B (T ∪ T1 ∪ T2)).2 \ (T ∪ T1 ∪ T2)) ∪ (T1 ∪ T2)).card :=
                Finset.card_le_card hsub
            _ ≤ ((buildContainer n M Ks Q rounds B (T ∪ T1 ∪ T2)).2 \ (T ∪ T1 ∪ T2)).card +
                  (T1 ∪ T2).card := Finset.card_union_le _ _
            _ ≤ rounds * (s + n / Ks) + (T1.card + T2.card) := by
                have := Finset.card_union_le T1 T2; omega
            _ ≤ (rounds + 1) * (s + n / Ks) := by
                rw [Nat.add_mul, one_mul]; omega
        · rcases h7 with hterm | hshrink
          · exact Or.inl hterm
          · right
            rw [Nat.add_mul, one_mul]
            have hsub_add : U.card - (buildContainer n M Ks Q rounds B (T ∪ T1 ∪ T2)).1.card =
                (U.card - A.card) + (A.card - B.card) +
                  (B.card - (buildContainer n M Ks Q rounds B (T ∪ T1 ∪ T2)).1.card) := by omega
            rw [hsub_add, Nat.mul_add, Nat.mul_add]
            omega

lemma buildContainer_replay (n M Ks : ℕ) (hM : 1 ≤ M) (hKs : 1 ≤ Ks) (hn : 2 * M ≤ n)
    (Q1 Q2 : Finset ℕ) (hQ : Q2 ⊆ Q1) (hQ1sf : IsSumFree (Q1 : Set ℕ)) :
    ∀ (rounds : ℕ) (U T : Finset ℕ),
      U ⊆ Finset.Icc 1 n →
      Disjoint U T →
      T ⊆ Q1 →
      (buildContainer n M Ks Q1 rounds U T).2 \ T ⊆ Q2 →
      buildContainer n M Ks Q2 rounds U T = buildContainer n M Ks Q1 rounds U T := by
  intro rounds
  induction rounds with
  | zero => intro _ _ _ _ _ _; rfl
  | succ rounds ih =>
    intro U T hUsub hdisj hTQ1 hsubQ2
    set D3 := n / M
    set s := 8 * M * Ks
    set resA1 := stepA D3 s Q1 U.card U ∅
    set A1 := resA1.1
    set T1 := resA1.2
    obtain ⟨hA1sub, _, hT1sub, hA1T1disj, hT1card, _, _⟩ :=
      stepA_invariants_clean D3 s Q1 U.card U ∅ (Finset.disjoint_empty_right U) (Nat.zero_le s)
    simp only [Finset.sdiff_empty] at hT1sub
    have hT1Q1 : T1 ⊆ Q1 := fun x hx ↦ (Finset.mem_inter.mp (hT1sub hx)).2
    have hT1U : T1 ⊆ U := fun x hx ↦ (Finset.mem_inter.mp (hT1sub hx)).1
    have hT1Tdisj : Disjoint T1 T := Finset.disjoint_of_subset_left hT1U hdisj
    have hA1_TT1_disj : Disjoint A1 (T ∪ T1) :=
      Finset.disjoint_union_right.mpr ⟨Finset.disjoint_of_subset_left hA1sub hdisj, hA1T1disj⟩
    -- Show T1 ⊆ (buildContainer ... Q1 (rounds+1) U T).2, hence T1 ⊆ Q2
    have hT1_in_final : T1 ⊆ (buildContainer n M Ks Q1 (rounds + 1) U T).2 := by
      dsimp only [buildContainer]
      by_cases hlt : T1.card < s
      · rw [if_pos hlt]; exact Finset.subset_union_right
      · rw [if_neg hlt]
        by_cases hdrop : n ≤ 16 * M * (U \ A1).card
        · rw [if_pos hdrop]
          have hinv := buildContainer_invariants n M Ks hM hKs hn Q1 hQ1sf rounds A1 (T ∪ T1)
            (hA1sub.trans hUsub) hA1_TT1_disj (Finset.union_subset hTQ1 hT1Q1)
          exact Finset.subset_union_right.trans hinv.2.1
        · rw [if_neg hdrop]
          set E := inducedEdges (auxEdges U T1) A1
          have hElt : ∀ p ∈ E, p.1 < p.2 := fun p hp ↦
            (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
          have hEind : ∀ x ∈ Q1, ∀ y ∈ Q1, (x, y) ∉ E := fun x hx y hy hxy ↦
            auxEdges_sf_disj hQ1sf hT1Q1 (Finset.mem_filter.mp hxy).1 hx hy
          obtain ⟨hBsub, _, hT2sub, hBT2disj, _, _, _⟩ :=
            stepB_invariants E Ks Q1 hEind hElt A1.card A1 ∅ (Finset.disjoint_empty_right A1)
          simp only [Finset.sdiff_empty] at hT2sub
          have hT2Q1 : (stepB E Ks Q1 A1.card A1 ∅).2 ⊆ Q1 :=
            fun x hx ↦ (Finset.mem_inter.mp (hT2sub hx)).2
          have hBdisj : Disjoint (stepB E Ks Q1 A1.card A1 ∅).1
              (T ∪ T1 ∪ (stepB E Ks Q1 A1.card A1 ∅).2) := by
            rw [Finset.disjoint_union_right]
            exact ⟨Finset.disjoint_of_subset_left hBsub hA1_TT1_disj, hBT2disj⟩
          have hinv := buildContainer_invariants n M Ks hM hKs hn Q1 hQ1sf rounds
            (stepB E Ks Q1 A1.card A1 ∅).1 (T ∪ T1 ∪ (stepB E Ks Q1 A1.card A1 ∅).2)
            ((hBsub.trans hA1sub).trans hUsub) hBdisj
            (Finset.union_subset (Finset.union_subset hTQ1 hT1Q1) hT2Q1)
          exact (Finset.subset_union_right.trans Finset.subset_union_left).trans hinv.2.1
    have hT1Q2 : T1 \ ∅ ⊆ Q2 := by
      intro x hx
      rw [Finset.sdiff_empty] at hx
      exact hsubQ2 (Finset.mem_sdiff.mpr ⟨hT1_in_final hx, Finset.disjoint_left.mp hT1Tdisj hx⟩)
    have hstepA_eq : stepA D3 s Q2 U.card U ∅ = stepA D3 s Q1 U.card U ∅ :=
      stepA_replay D3 s Q1 Q2 hQ U.card U ∅ (Finset.disjoint_empty_right U) hT1Q2
    dsimp only [buildContainer]
    rw [hstepA_eq]
    by_cases hlt : T1.card < s
    · rw [if_pos hlt, if_pos hlt]
    · rw [if_neg hlt, if_neg hlt]
      by_cases hdrop : n ≤ 16 * M * (U \ A1).card
      · rw [if_pos hdrop, if_pos hdrop]
        apply ih A1 (T ∪ T1) (hA1sub.trans hUsub) hA1_TT1_disj (Finset.union_subset hTQ1 hT1Q1)
        intro x hx
        obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.mp hx
        apply hsubQ2
        rw [Finset.mem_sdiff]
        refine ⟨?_, fun hxT ↦ hx2 (Finset.mem_union_left _ hxT)⟩
        dsimp only [buildContainer]
        rw [if_neg hlt, if_pos hdrop]
        exact hx1
      · rw [if_neg hdrop, if_neg hdrop]
        set E := inducedEdges (auxEdges U T1) A1
        have hElt : ∀ p ∈ E, p.1 < p.2 := fun p hp ↦
          (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
        have hEind : ∀ x ∈ Q1, ∀ y ∈ Q1, (x, y) ∉ E := fun x hx y hy hxy ↦
          auxEdges_sf_disj hQ1sf hT1Q1 (Finset.mem_filter.mp hxy).1 hx hy
        set resB1 := stepB E Ks Q1 A1.card A1 ∅
        set B1 := resB1.1
        set T2 := resB1.2
        obtain ⟨hBsub, _, hT2sub, hBT2disj, _, _, _⟩ :=
          stepB_invariants E Ks Q1 hEind hElt A1.card A1 ∅ (Finset.disjoint_empty_right A1)
        simp only [Finset.sdiff_empty] at hT2sub
        have hT2Q1 : T2 ⊆ Q1 := fun x hx ↦ (Finset.mem_inter.mp (hT2sub hx)).2
        have hT2A1 : T2 ⊆ A1 := fun x hx ↦ (Finset.mem_inter.mp (hT2sub hx)).1
        have hT2Tdisj : Disjoint T2 T :=
          Finset.disjoint_of_subset_left (hT2A1.trans hA1sub) hdisj
        have hBdisj : Disjoint B1 (T ∪ T1 ∪ T2) := by
          rw [Finset.disjoint_union_right]
          exact ⟨Finset.disjoint_of_subset_left hBsub hA1_TT1_disj, hBT2disj⟩
        have hinv := buildContainer_invariants n M Ks hM hKs hn Q1 hQ1sf rounds
          B1 (T ∪ T1 ∪ T2) ((hBsub.trans hA1sub).trans hUsub) hBdisj
          (Finset.union_subset (Finset.union_subset hTQ1 hT1Q1) hT2Q1)
        have hT2Q2 : T2 \ ∅ ⊆ Q2 := by
          intro x hx
          rw [Finset.sdiff_empty] at hx
          apply hsubQ2
          rw [Finset.mem_sdiff]
          refine ⟨?_, Finset.disjoint_left.mp hT2Tdisj hx⟩
          dsimp only [buildContainer]
          rw [if_neg hlt, if_neg hdrop]
          exact hinv.2.1 (Finset.mem_union_right _ hx)
        have hstepB_eq : stepB E Ks Q2 A1.card A1 ∅ = stepB E Ks Q1 A1.card A1 ∅ :=
          stepB_replay E Ks Q1 Q2 hQ hEind hElt A1.card A1 ∅ (Finset.disjoint_empty_right A1) hT2Q2
        rw [hstepB_eq]
        apply ih B1 (T ∪ T1 ∪ T2) ((hBsub.trans hA1sub).trans hUsub) hBdisj
          (Finset.union_subset (Finset.union_subset hTQ1 hT1Q1) hT2Q1)
        intro x hx
        obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.mp hx
        apply hsubQ2
        rw [Finset.mem_sdiff]
        refine ⟨?_, fun hxT ↦ hx2 (Finset.mem_union_left _ (Finset.mem_union_left _ hxT))⟩
        dsimp only [buildContainer]
        rw [if_neg hlt, if_neg hdrop]
        exact hx1

/- ### Binomial Entropy Bound and Main Container Theorem -/

lemma sum_pow_card_powerset (S : Finset ℕ) (x : ℝ) :
    ∑ T ∈ S.powerset, x ^ T.card = (1 + x) ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.powerset_insert, Finset.sum_union, Finset.sum_image, Finset.card_insert_of_notMem ha,
      pow_succ]
    · have h1 : ∑ T ∈ s.powerset, x ^ (insert a T).card = x * ∑ T ∈ s.powerset, x ^ T.card := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun T hT ↦ ?_
        have haT : a ∉ T := fun hc ↦ ha (Finset.mem_powerset.mp hT hc)
        rw [Finset.card_insert_of_notMem haT, pow_succ']
      rw [h1, ih]; ring
    · intro T₁ hT₁ T₂ hT₂ heq
      have h1 : a ∉ T₁ := fun hc ↦ ha (Finset.mem_powerset.mp hT₁ hc)
      have h2 : a ∉ T₂ := fun hc ↦ ha (Finset.mem_powerset.mp hT₂ hc)
      have := congr_arg (fun X ↦ X.erase a) heq
      simpa [Finset.erase_insert h1, Finset.erase_insert h2] using this
    · rw [Finset.disjoint_left]
      intro T hT hTimg
      obtain ⟨U, _, rfl⟩ := Finset.mem_image.mp hTimg
      exact ha (Finset.mem_powerset.mp hT (Finset.mem_insert_self a U))

lemma card_small_subsets_le (n : ℕ) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    (((Finset.Icc 1 n).powerset.filter (fun T ↦ (T.card : ℝ) ≤ η * n)).card : ℝ) ≤
      ((1 + η) / η ^ η) ^ n := by
  let S := (Finset.Icc 1 n).powerset.filter (fun T ↦ (T.card : ℝ) ≤ η * n)
  have h1 : (S.card : ℝ) * η ^ (η * (n : ℝ)) ≤ ∑ T ∈ S, η ^ T.card := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun T hT ↦ ?_
    have hle : (T.card : ℝ) ≤ η * n := (Finset.mem_filter.mp hT).2
    rw [← Real.rpow_natCast η T.card]
    exact Real.rpow_le_rpow_of_exponent_ge hη0 hη1 hle
  have h2 : ∑ T ∈ S, η ^ T.card ≤ ∑ T ∈ (Finset.Icc 1 n).powerset, η ^ T.card :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ ↦ by positivity)
  have h3 : ∑ T ∈ (Finset.Icc 1 n).powerset, η ^ T.card = (1 + η) ^ n := by
    rw [sum_pow_card_powerset, Nat.card_Icc]; simp
  have hpow : η ^ (η * (n : ℝ)) = (η ^ η) ^ n := by
    rw [← Real.rpow_natCast (η ^ η) n, ← Real.rpow_mul hη0.le]
  have hpos : 0 < (η ^ η) ^ n := by positivity
  rw [div_pow, le_div_iff₀ hpos, ← hpow]
  linarith

lemma exists_small_eta (ε γ : ℝ) (hε : 0 < ε) (hγ : 0 < γ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η ≤ ε / 16 ∧ (1 + η) / η ^ η ≤ (2 : ℝ) ^ γ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let t : ℝ := min (1 / 4) (min (ε / 16) (γ * Real.log 2 / 4))
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 / 4 := min_le_left _ _
  have ht2 : t ≤ ε / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have ht3 : t ≤ γ * Real.log 2 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨t ^ 2, by positivity, by nlinarith, by nlinarith, ?_⟩
  have hη0 : 0 < t ^ 2 := by positivity
  have hlog : -t ^ 2 * Real.log (t ^ 2) ≤ 2 * t := by
    have h1 : Real.log (t⁻¹) ≤ t⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr ht0)
    rw [Real.log_inv] at h1
    have h2 : Real.log (t ^ 2) = 2 * Real.log t := by
      rw [Real.log_pow]; norm_cast
    rw [h2]
    have h3 : -Real.log t ≤ t⁻¹ := by linarith
    have h4 : 2 * t ^ 2 * (-Real.log t) ≤ 2 * t ^ 2 * t⁻¹ :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : 2 * t ^ 2 * t⁻¹ = 2 * t := by field_simp
    linarith
  have hrpow : ((t ^ 2) ^ (t ^ 2))⁻¹ ≤ Real.exp (2 * t) := by
    rw [← Real.rpow_neg hη0.le, Real.rpow_def_of_pos hη0]
    exact Real.exp_le_exp.mpr (by linarith)
  have h1p : 1 + t ^ 2 ≤ Real.exp (t ^ 2) := by linarith [Real.add_one_le_exp (t ^ 2)]
  have hexp_le : Real.exp (t ^ 2 + 2 * t) ≤ (2 : ℝ) ^ γ := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc (1 + t ^ 2) / (t ^ 2) ^ (t ^ 2)
      = (1 + t ^ 2) * ((t ^ 2) ^ (t ^ 2))⁻¹ := div_eq_mul_inv _ _
    _ ≤ Real.exp (t ^ 2) * Real.exp (2 * t) :=
        mul_le_mul h1p hrpow (by positivity) (by positivity)
    _ = Real.exp (t ^ 2 + 2 * t) := (Real.exp_add _ _).symm
    _ ≤ (2 : ℝ) ^ γ := hexp_le

private lemma container_theorem_step (ε ε₁ η γ : ℝ) (M R Ks s n : ℕ)
    (hε₁0 : 0 < ε₁) (hε₁_le : ε₁ ≤ ε) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hηε : η ≤ ε₁ / 16) (hηent : (1 + η) / η ^ η ≤ (2 : ℝ) ^ γ)
    (hM1 : 1 ≤ M) (hM_real : (8 : ℝ) / ε₁ ≤ M)
    (hR_eq : R = 32 * M + 1) (hKs1 : 1 ≤ Ks) (hKs_real : 2 * (R : ℝ) / η ≤ Ks)
    (hs_eq : s = 8 * M * Ks)
    (hn2M : 2 * M ≤ n) (hnRs : (R * s : ℝ) ≤ (η / 2) * n) (hn_eps : (1 : ℝ) ≤ (ε₁ / 4) * n) :
    ∃ F : Finset (Finset ℕ),
      (F.card : ℝ) ≤ (2 : ℝ) ^ (γ * n) ∧
      (∀ A ∈ (Finset.Icc 1 n).powerset.filter (fun A : Finset ℕ ↦ IsSumFree (A : Set ℕ)),
        ∃ C ∈ F, A ⊆ C) ∧
      (∀ C ∈ F, C ⊆ Finset.Icc 1 n ∧ ((schurTriples C).card : ℝ) ≤ ε * (n : ℝ) ^ 2) := by
  have hn_pos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  let Tset := (Finset.Icc 1 n).powerset.filter (fun T ↦ (T.card : ℝ) ≤ η * n)
  let mkC (T : Finset ℕ) : Finset ℕ :=
    let res := buildContainer n M Ks T R (Finset.Icc 1 n) ∅
    res.1 ∪ res.2
  let F := (Tset.image mkC).filter fun C ↦
    C ⊆ Finset.Icc 1 n ∧ ((schurTriples C).card : ℝ) ≤ ε * (n : ℝ) ^ 2
  refine ⟨F, ?_, ?_, ?_⟩
  · -- Cardinality bound
    calc (F.card : ℝ)
        ≤ ((Tset.image mkC).card : ℝ) := by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ (Tset.card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ ≤ ((1 + η) / η ^ η) ^ n := card_small_subsets_le n η hη0 hη1
      _ ≤ ((2 : ℝ) ^ γ) ^ n := pow_le_pow_left₀ (by positivity) hηent n
      _ = (2 : ℝ) ^ (γ * n) := by
          rw [← Real.rpow_natCast ((2 : ℝ) ^ γ) n, ← Real.rpow_mul (by norm_num)]
  · -- Covering property
    intro A hA
    obtain ⟨hApow, hAsf⟩ := Finset.mem_filter.mp hA
    have hAsub : A ⊆ Finset.Icc 1 n := Finset.mem_powerset.mp hApow
    set res := buildContainer n M Ks A R (Finset.Icc 1 n) ∅
    set Uf := res.1
    set Tf := res.2
    obtain ⟨hUfsub, _, hTfA, _, hcov, hTfcard, hterm⟩ :=
      buildContainer_invariants n M Ks hM1 hKs1 hn2M A hAsf R (Finset.Icc 1 n) ∅
        Finset.Subset.rfl (Finset.disjoint_empty_right _) (Finset.empty_subset A)
    change Uf ⊆ Finset.Icc 1 n at hUfsub
    change Tf ⊆ A at hTfA
    change (Finset.Icc 1 n) ∩ A ⊆ Uf ∪ Tf at hcov
    change (Tf \ ∅).card ≤ R * (8 * M * Ks + n / Ks) at hTfcard
    change (∀ v ∈ Uf, (linkPairs Uf v).card < n / M) ∨ R * n ≤ 32 * M * ((Finset.Icc 1 n).card - Uf.card) at hterm
    simp only [Finset.sdiff_empty] at hTfcard
    have hTf_Tset : Tf ∈ Tset := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨hTfA.trans hAsub, ?_⟩
      have hcard1 : (Tf.card : ℝ) ≤ (R : ℝ) * (s : ℝ) + (R : ℝ) * ((n / Ks : ℕ) : ℝ) := by
        rw [← hs_eq] at hTfcard
        have h' : (Tf.card : ℝ) ≤ ((R * (s + n / Ks) : ℕ) : ℝ) := by exact_mod_cast hTfcard
        push_cast at h'
        linarith
      have hdiv : ((n / Ks : ℕ) : ℝ) ≤ (n : ℝ) / (Ks : ℝ) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < Ks)]
        exact_mod_cast Nat.div_mul_le_self n Ks
      have hRKs : (R : ℝ) / (Ks : ℝ) ≤ η / 2 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < Ks)]
        rw [div_le_iff₀ hη0] at hKs_real
        linarith
      have hterm2 : (R : ℝ) * ((n / Ks : ℕ) : ℝ) ≤ (η / 2) * n := by
        calc (R : ℝ) * ((n / Ks : ℕ) : ℝ)
            ≤ (R : ℝ) * ((n : ℝ) / (Ks : ℝ)) := mul_le_mul_of_nonneg_left hdiv (by positivity)
          _ = ((R : ℝ) / (Ks : ℝ)) * (n : ℝ) := by ring
          _ ≤ (η / 2) * (n : ℝ) := mul_le_mul_of_nonneg_right hRKs (by positivity)
      linarith
    have hreplay : buildContainer n M Ks Tf R (Finset.Icc 1 n) ∅ = res := by
      apply buildContainer_replay n M Ks hM1 hKs1 hn2M A Tf hTfA hAsf R (Finset.Icc 1 n) ∅
        Finset.Subset.rfl (Finset.disjoint_empty_right _) (Finset.empty_subset A)
      simp [res, Tf]
    have hmkC : mkC Tf = Uf ∪ Tf := by simp [mkC, hreplay, Uf, Tf]
    have hdegUf : ∀ v ∈ Uf, (linkPairs Uf v).card < n / M := by
      rcases hterm with h | hshrink
      · exact h
      · exfalso
        have hIcc : (Finset.Icc 1 n).card = n := by simp
        rw [hIcc, hR_eq] at hshrink
        have hle : (n - Uf.card) ≤ n := Nat.sub_le n Uf.card
        have : (32 * M + 1) * n ≤ 32 * M * n := le_trans hshrink (Nat.mul_le_mul_left _ hle)
        have hn0 : 0 < n := by omega
        nlinarith
    have hCsub : Uf ∪ Tf ⊆ Finset.Icc 1 n := Finset.union_subset hUfsub (hTfA.trans hAsub)
    have hCpos : ∀ x ∈ Uf ∪ Tf, 0 < x := fun x hx ↦ (Finset.mem_Icc.mp (hCsub hx)).1
    have hUfpos : ∀ x ∈ Uf, 0 < x := fun x hx ↦ hCpos x (Finset.mem_union_left _ hx)
    have hUf_tri : 3 * (distinctTriples Uf).card ≤ n * (n / M) := by
      have h1 := sum_linkPairs_card_ge Uf hUfpos
      have h2 : ∑ v ∈ Uf, (linkPairs Uf v).card ≤ ∑ _v ∈ Uf, (n / M) :=
        Finset.sum_le_sum fun v hv ↦ le_of_lt (hdegUf v hv)
      have hUfcard : Uf.card ≤ n := by
        calc Uf.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hUfsub
          _ = n := by simp
      calc 3 * (distinctTriples Uf).card
          ≤ ∑ v ∈ Uf, (linkPairs Uf v).card := h1
        _ ≤ Uf.card * (n / M) := by simpa [Finset.sum_const, smul_eq_mul] using h2
        _ ≤ n * (n / M) := Nat.mul_le_mul_right _ hUfcard
    have hCcard : (Uf ∪ Tf).card ≤ n := by
      calc (Uf ∪ Tf).card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hCsub
        _ = n := by simp
    have hCtri : (schurTriples (Uf ∪ Tf)).card ≤
        2 * (distinctTriples Uf).card + 6 * Tf.card * n + n := by
      have h1 := schurTriples_card_le (Uf ∪ Tf)
      have h2 := distinctTriples_union_le Uf Tf hCpos
      have h3 : 3 * Tf.card * (Uf ∪ Tf).card ≤ 3 * Tf.card * n :=
        Nat.mul_le_mul_left _ hCcard
      have h4 : 2 * (3 * Tf.card * n) = 6 * Tf.card * n := by ring
      omega
    have hCtri_real : ((schurTriples (Uf ∪ Tf)).card : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
      have h1 : ((schurTriples (Uf ∪ Tf)).card : ℝ) ≤
          2 * ((distinctTriples Uf).card : ℝ) + 6 * (Tf.card : ℝ) * (n : ℝ) + (n : ℝ) := by
        exact_mod_cast hCtri
      have h2 : ((distinctTriples Uf).card : ℝ) ≤ (n : ℝ) ^ 2 / (3 * (M : ℝ)) := by
        have h3 : 3 * ((distinctTriples Uf).card : ℝ) ≤ (n : ℝ) * ((n / M : ℕ) : ℝ) := by
          exact_mod_cast hUf_tri
        have hdiv : ((n / M : ℕ) : ℝ) ≤ (n : ℝ) / (M : ℝ) := by
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < M)]
          exact_mod_cast Nat.div_mul_le_self n M
        have h4 : 3 * ((distinctTriples Uf).card : ℝ) ≤ (n : ℝ) ^ 2 / (M : ℝ) := by
          calc 3 * ((distinctTriples Uf).card : ℝ)
              ≤ (n : ℝ) * ((n / M : ℕ) : ℝ) := h3
            _ ≤ (n : ℝ) * ((n : ℝ) / (M : ℝ)) := mul_le_mul_of_nonneg_left hdiv (by positivity)
            _ = (n : ℝ) ^ 2 / (M : ℝ) := by ring
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 3 * M)]
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < M)] at h4
        linarith
      have hM_inv : (2 : ℝ) / (3 * (M : ℝ)) ≤ ε₁ / 8 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * M)]
        rw [div_le_iff₀ hε₁0] at hM_real
        nlinarith
      have hterm1 : 2 * ((distinctTriples Uf).card : ℝ) ≤ (ε₁ / 8) * (n : ℝ) ^ 2 := by
        calc 2 * ((distinctTriples Uf).card : ℝ)
            ≤ 2 * ((n : ℝ) ^ 2 / (3 * (M : ℝ))) := by linarith
          _ = ((2 : ℝ) / (3 * (M : ℝ))) * (n : ℝ) ^ 2 := by ring
          _ ≤ (ε₁ / 8) * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hM_inv (by positivity)
      have hTf_le : (Tf.card : ℝ) ≤ η * (n : ℝ) := (Finset.mem_filter.mp hTf_Tset).2
      have hterm2 : 6 * (Tf.card : ℝ) * (n : ℝ) ≤ (6 * ε₁ / 16) * (n : ℝ) ^ 2 := by
        have h6 : 6 * (Tf.card : ℝ) * (n : ℝ) ≤ 6 * (η * (n : ℝ)) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTf_le (by norm_num)) hn_pos.le
        have h6b : 6 * η * (n : ℝ) ^ 2 ≤ 6 * (ε₁ / 16) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg (n : ℝ))
        linarith
      have hterm3 : (n : ℝ) ≤ (ε₁ / 4) * (n : ℝ) ^ 2 := by
        calc (n : ℝ) = 1 * (n : ℝ) := (one_mul _).symm
          _ ≤ ((ε₁ / 4) * (n : ℝ)) * (n : ℝ) := mul_le_mul_of_nonneg_right hn_eps hn_pos.le
          _ = (ε₁ / 4) * (n : ℝ) ^ 2 := by ring
      have heps_n2 : ε₁ * (n : ℝ) ^ 2 ≤ ε * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hε₁_le (sq_nonneg (n : ℝ))
      linarith
    refine ⟨Uf ∪ Tf, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_image.mpr ⟨Tf, hTf_Tset, hmkC⟩, hCsub, hCtri_real⟩
    · intro x hx
      exact hcov (Finset.mem_inter.mpr ⟨hAsub hx, hx⟩)
  · intro C hC
    exact (Finset.mem_filter.mp hC).2

theorem container_theorem (ε γ : ℝ) (hε : 0 < ε) (hγ : 0 < γ) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ F : Finset (Finset ℕ),
      (F.card : ℝ) ≤ (2 : ℝ) ^ (γ * n) ∧
      (∀ A ∈ (Finset.Icc 1 n).powerset.filter (fun A : Finset ℕ ↦ IsSumFree (A : Set ℕ)),
        ∃ C ∈ F, A ⊆ C) ∧
      (∀ C ∈ F, C ⊆ Finset.Icc 1 n ∧ ((schurTriples C).card : ℝ) ≤ ε * (n : ℝ) ^ 2) := by
  let ε₁ : ℝ := min ε 1
  have hε₁0 : 0 < ε₁ := lt_min hε zero_lt_one
  have hε₁_le : ε₁ ≤ ε := min_le_left ε 1
  obtain ⟨η, hη0, hη1, hηε, hηent⟩ := exists_small_eta ε₁ γ hε₁0 hγ
  let M : ℕ := Nat.ceil (8 / ε₁) + 8
  have hM1 : 1 ≤ M := by omega
  have hM_real : (8 : ℝ) / ε₁ ≤ M := by
    have := Nat.le_ceil (8 / ε₁)
    have : (Nat.ceil (8 / ε₁) : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show Nat.ceil (8 / ε₁) ≤ M by omega)
    linarith
  let R : ℕ := 32 * M + 1
  let Ks : ℕ := Nat.ceil (2 * (R : ℝ) / η) + 1
  have hKs1 : 1 ≤ Ks := by omega
  have hKs_real : 2 * (R : ℝ) / η ≤ Ks := by
    have := Nat.le_ceil (2 * (R : ℝ) / η)
    have : (Nat.ceil (2 * (R : ℝ) / η) : ℝ) ≤ (Ks : ℝ) := by
      exact_mod_cast (show Nat.ceil (2 * (R : ℝ) / η) ≤ Ks by omega)
    linarith
  let s : ℕ := 8 * M * Ks
  let N₀ : ℕ := max (2 * M) (max (Nat.ceil (2 * (R * s : ℝ) / η) + 1) (Nat.ceil (4 / ε₁) + 1))
  refine ⟨N₀, fun n hn ↦ ?_⟩
  have hn2M : 2 * M ≤ n := le_trans (le_max_left _ _) hn
  have hnRs : (R * s : ℝ) ≤ (η / 2) * n := by
    have h1 : Nat.ceil (2 * (R * s : ℝ) / η) + 1 ≤ n :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
    have h2 : 2 * (R * s : ℝ) / η ≤ n := by
      have hc := Nat.le_ceil (2 * (R * s : ℝ) / η)
      have h1' : (Nat.ceil (2 * (R * s : ℝ) / η) : ℝ) ≤ n := by exact_mod_cast (show Nat.ceil (2 * (R * s : ℝ) / η) ≤ n by omega)
      linarith
    rw [div_le_iff₀ hη0] at h2
    linarith
  have hn_eps : (1 : ℝ) ≤ (ε₁ / 4) * n := by
    have h1 : Nat.ceil (4 / ε₁) + 1 ≤ n :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
    have h2 : 4 / ε₁ ≤ n := by
      have hc := Nat.le_ceil (4 / ε₁)
      have h1' : (Nat.ceil (4 / ε₁) : ℝ) ≤ n := by exact_mod_cast (show Nat.ceil (4 / ε₁) ≤ n by omega)
      linarith
    rw [div_le_iff₀ hε₁0] at h2
    linarith
  exact container_theorem_step ε ε₁ η γ M R Ks s n hε₁0 hε₁_le hη0 hη1 hηε hηent
    hM1 hM_real rfl hKs1 hKs_real rfl hn2M hnRs hn_eps

end Mod2

section Mod3
open Filter Real Finset SimpleGraph
open scoped Classical

/-- Tripartite Král-Serra-Vena graph for `C ⊆ [1, n]` modulo `N = 2 * n + 1`. -/
def ksvGraph (N : ℕ) (C : Finset ℕ) : SimpleGraph (Fin 3 × ZMod N) where
  Adj u v :=
    (u.1 < v.1 ∧ ∃ a ∈ C, (a : ZMod N) = v.2 - u.2) ∨
    (v.1 < u.1 ∧ ∃ a ∈ C, (a : ZMod N) = u.2 - v.2)
  symm := ⟨fun _ _ h ↦ Or.symm h⟩
  loopless := ⟨fun _ h ↦ by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> exact lt_irrefl _ h⟩

lemma zmod_natCast_inj {N a b : ℕ} (ha : a < N) (hb : b < N)
    (heq : (a : ZMod N) = (b : ZMod N)) : a = b := by
  have : NeZero N := ⟨by omega⟩
  have h1 := congr_arg ZMod.val heq
  rw [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at h1
  exact h1

lemma ksvGraph_adj_01 {N : ℕ} {C : Finset ℕ} {x y : ZMod N} :
    (ksvGraph N C).Adj (0, x) (1, y) ↔ ∃ a ∈ C, (a : ZMod N) = y - x := by
  simp only [ksvGraph]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact h
    · exact absurd h (by decide)
  · intro h; exact Or.inl ⟨by decide, h⟩

lemma ksvGraph_adj_12 {N : ℕ} {C : Finset ℕ} {x y : ZMod N} :
    (ksvGraph N C).Adj (1, x) (2, y) ↔ ∃ a ∈ C, (a : ZMod N) = y - x := by
  simp only [ksvGraph]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact h
    · exact absurd h (by decide)
  · intro h; exact Or.inl ⟨by decide, h⟩

lemma ksvGraph_adj_02 {N : ℕ} {C : Finset ℕ} {x y : ZMod N} :
    (ksvGraph N C).Adj (0, x) (2, y) ↔ ∃ a ∈ C, (a : ZMod N) = y - x := by
  simp only [ksvGraph]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact h
    · exact absurd h (by decide)
  · intro h; exact Or.inl ⟨by decide, h⟩

lemma ksvGraph_cliques_card_le (n : ℕ) (C : Finset ℕ) (hC : C ⊆ Finset.Icc 1 n) :
    ((ksvGraph (2 * n + 1) C).cliqueFinset 3).card ≤
      (2 * n + 1) * (schurTriples C).card := by
  set N := 2 * n + 1
  have : NeZero N := ⟨by omega⟩
  let G := ksvGraph N C
  let mkTri : ZMod N × (ℕ × ℕ × ℕ) → Finset (Fin 3 × ZMod N) :=
    fun p ↦ {((0 : Fin 3), p.1), ((1 : Fin 3), p.1 + (p.2.1 : ZMod N)),
             ((2 : Fin 3), p.1 + (p.2.2.2 : ZMod N))}
  have hcov : G.cliqueFinset 3 ⊆ ((Finset.univ : Finset (ZMod N)) ×ˢ schurTriples C).image mkTri := by
    intro t ht
    rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_iff] at ht
    obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := ht
    have hne_fst : ∀ p q : Fin 3 × ZMod N, G.Adj p q → p.1 ≠ q.1 := by
      intro p q hpq heq
      rcases hpq with ⟨hlt, _⟩ | ⟨hlt, _⟩ <;> rw [heq] at hlt <;> exact lt_irrefl _ hlt
    have h12 : u.1 ≠ v.1 := hne_fst u v huv
    have h13 : u.1 ≠ w.1 := hne_fst u w huw
    have h23 : v.1 ≠ w.1 := hne_fst v w hvw
    -- One of u, v, w has fst = 0, one has fst = 1, one has fst = 2
    have hexists : ∃ x y z : ZMod N,
        ({u, v, w} : Finset (Fin 3 × ZMod N)) = {((0 : Fin 3), x), ((1 : Fin 3), y), ((2 : Fin 3), z)} ∧
        G.Adj (0, x) (1, y) ∧ G.Adj (1, y) (2, z) ∧ G.Adj (0, x) (2, z) := by
      rcases u with ⟨u1, u2⟩; rcases v with ⟨v1, v2⟩; rcases w with ⟨w1, w2⟩
      have hset_perm : ∀ (a b c : Fin 3 × ZMod N),
          ({a, b, c} : Finset (Fin 3 × ZMod N)) = {a, c, b} ∧
          ({a, b, c} : Finset (Fin 3 × ZMod N)) = {b, a, c} ∧
          ({a, b, c} : Finset (Fin 3 × ZMod N)) = {b, c, a} ∧
          ({a, b, c} : Finset (Fin 3 × ZMod N)) = {c, a, b} ∧
          ({a, b, c} : Finset (Fin 3 × ZMod N)) = {c, b, a} := by
        intro a b c; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (ext p; simp [or_comm, or_left_comm])
      fin_cases u1 <;> fin_cases v1 <;> fin_cases w1
      · exact absurd rfl h12
      · exact absurd rfl h12
      · exact absurd rfl h12
      · exact absurd rfl h13
      · exact absurd rfl h23
      · exact ⟨u2, v2, w2, rfl, huv, hvw, huw⟩
      · exact absurd rfl h13
      · exact ⟨u2, w2, v2, (hset_perm _ _ _).1, huw, hvw.symm, huv⟩
      · exact absurd rfl h23
      · exact absurd rfl h23
      · exact absurd rfl h13
      · exact ⟨v2, u2, w2, (hset_perm _ _ _).2.1, huv.symm, huw, hvw⟩
      · exact absurd rfl h12
      · exact absurd rfl h12
      · exact absurd rfl h12
      · exact ⟨w2, u2, v2, (hset_perm _ _ _).2.2.2.1, huw.symm, huv, hvw.symm⟩
      · exact absurd rfl h13
      · exact absurd rfl h23
      · exact absurd rfl h23
      · exact ⟨v2, w2, u2, (hset_perm _ _ _).2.2.1, hvw, huw.symm, huv.symm⟩
      · exact absurd rfl h13
      · exact ⟨w2, v2, u2, (hset_perm _ _ _).2.2.2.2, hvw.symm, huv.symm, huw.symm⟩
      · exact absurd rfl h23
      · exact absurd rfl h13
      · exact absurd rfl h12
      · exact absurd rfl h12
      · exact absurd rfl h12
    obtain ⟨x, y, z, hset, h01, h12', h02⟩ := hexists
    obtain ⟨a, haC, haeq⟩ := ksvGraph_adj_01.mp h01
    obtain ⟨b, hbC, hbeq⟩ := ksvGraph_adj_12.mp h12'
    obtain ⟨c, hcC, hceq⟩ := ksvGraph_adj_02.mp h02
    have ha_le : a ≤ n := (Finset.mem_Icc.mp (hC haC)).2
    have hb_le : b ≤ n := (Finset.mem_Icc.mp (hC hbC)).2
    have hc_le : c ≤ n := (Finset.mem_Icc.mp (hC hcC)).2
    have hsum_mod : ((a + b : ℕ) : ZMod N) = (c : ZMod N) := by
      push_cast
      rw [haeq, hbeq, hceq]
      ring
    have hsum : a + b = c := zmod_natCast_inj (by omega) (by omega) hsum_mod
    rw [Finset.mem_image]
    refine ⟨(x, (a, b, c)), Finset.mem_product.mpr ⟨Finset.mem_univ x, ?_⟩, ?_⟩
    · rw [schurTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_product]
      exact ⟨⟨haC, hbC, hcC⟩, hsum⟩
    · rw [hset]
      dsimp only [mkTri]
      have hy : x + (a : ZMod N) = y := by rw [haeq]; ring
      have hz : x + (c : ZMod N) = z := by rw [hceq]; ring
      rw [hy, hz]
  calc (G.cliqueFinset 3).card
      ≤ (((Finset.univ : Finset (ZMod N)) ×ˢ schurTriples C).image mkTri).card :=
        Finset.card_le_card hcov
    _ ≤ ((Finset.univ : Finset (ZMod N)) ×ˢ schurTriples C).card := Finset.card_image_le
    _ = N * (schurTriples C).card := by
        rw [Finset.card_product, Finset.card_univ, ZMod.card N]

theorem sumFree_removal (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (n : ℕ) (C : Finset ℕ),
      0 < n →
      C ⊆ Finset.Icc 1 n →
      ((schurTriples C).card : ℝ) < ε * (n : ℝ) ^ 2 →
      ∃ B ⊆ C, IsSumFree (B : Set ℕ) ∧ ((C \ B).card : ℝ) ≤ δ * (n : ℝ) := by
  set ε_tri : ℝ := δ / 81
  have hε_tri_pos : 0 < ε_tri := by positivity
  set ε : ℝ := SimpleGraph.triangleRemovalBound ε_tri
  have hε_pos : 0 < ε := SimpleGraph.triangleRemovalBound_pos hε_tri_pos
  refine ⟨ε, hε_pos, fun n C hn hC htri ↦ ?_⟩
  set N := 2 * n + 1
  have : NeZero N := ⟨by omega⟩
  set G := ksvGraph N C
  have hcardV : Fintype.card (Fin 3 × ZMod N) = 3 * N := by
    rw [Fintype.card_prod, Fintype.card_fin, ZMod.card N]
  have hclique_lt : ((G.cliqueFinset 3).card : ℝ) <
      SimpleGraph.triangleRemovalBound ε_tri * (Fintype.card (Fin 3 × ZMod N) : ℝ) ^ 3 := by
    have h1 : ((G.cliqueFinset 3).card : ℝ) ≤ (N : ℝ) * ((schurTriples C).card : ℝ) := by
      exact_mod_cast ksvGraph_cliques_card_le n C hC
    have hnN : (n : ℝ) ≤ (N : ℝ) := by
      have : n ≤ N := by omega
      exact_mod_cast this
    have hNpos : (0 : ℝ) < N := by positivity
    calc ((G.cliqueFinset 3).card : ℝ)
        ≤ (N : ℝ) * ((schurTriples C).card : ℝ) := h1
      _ < (N : ℝ) * (ε * (n : ℝ) ^ 2) := mul_lt_mul_of_pos_left htri hNpos
      _ ≤ (N : ℝ) * (ε * (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (by nlinarith) hε_pos.le) hNpos.le
      _ ≤ ε * ((3 * (N : ℝ)) ^ 3) := by
          have h27 : (N : ℝ) ^ 3 ≤ (3 * (N : ℝ)) ^ 3 := by
            have : (3 * (N : ℝ)) ^ 3 = 27 * (N : ℝ) ^ 3 := by ring
            rw [this]; nlinarith [pow_nonneg hNpos.le 3]
          calc (N : ℝ) * (ε * (N : ℝ) ^ 2) = ε * (N : ℝ) ^ 3 := by ring
            _ ≤ ε * (3 * (N : ℝ)) ^ 3 := mul_le_mul_of_nonneg_left h27 hε_pos.le
      _ = SimpleGraph.triangleRemovalBound ε_tri * (Fintype.card (Fin 3 × ZMod N) : ℝ) ^ 3 := by
          rw [hcardV]; push_cast; rfl
  obtain ⟨G', hG'le, _, hdel_lt, hG'free⟩ := SimpleGraph.triangle_removal hclique_lt
  let E_del : Finset (Sym2 (Fin 3 × ZMod N)) := G.edgeFinset \ G'.edgeFinset
  have hG'sub : G'.edgeFinset ⊆ G.edgeFinset := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    exact SimpleGraph.edgeSet_mono hG'le he
  have hEdel_card : (E_del.card : ℝ) < ε_tri * ((3 * N : ℕ) : ℝ) ^ 2 := by
    have hsub : E_del.card + G'.edgeFinset.card = G.edgeFinset.card :=
      Finset.card_sdiff_add_card_eq_card hG'sub
    have hcast : (E_del.card : ℝ) = (G.edgeFinset.card : ℝ) - (G'.edgeFinset.card : ℝ) := by
      have : (E_del.card : ℝ) + (G'.edgeFinset.card : ℝ) = (G.edgeFinset.card : ℝ) := by
        exact_mod_cast hsub
      linarith
    rw [hcast]
    simpa [hcardV] using hdel_lt
  let E01 (a : ℕ) : Finset (ZMod N) := Finset.univ.filter fun x ↦ ¬ G'.Adj (0, x) (1, x + (a : ZMod N))
  let E12 (a : ℕ) : Finset (ZMod N) := Finset.univ.filter fun x ↦ ¬ G'.Adj (1, x) (2, x + (a : ZMod N))
  let E02 (a : ℕ) : Finset (ZMod N) := Finset.univ.filter fun x ↦ ¬ G'.Adj (0, x) (2, x + (a : ZMod N))
  let B : Finset ℕ := C.filter fun a ↦
    3 * (E01 a).card < N ∧ 3 * (E12 a).card < N ∧ 3 * (E02 a).card < N
  refine ⟨B, Finset.filter_subset _ _, ?_, ?_⟩
  · -- B is sum-free
    rw [isSumFree_iff]
    intro a ha b hb hab
    have haB := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
    have hbB := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
    have habB := Finset.mem_filter.mp (Finset.mem_coe.mp hab)
    let bad : Finset (ZMod N) :=
      E01 a ∪ (E12 b).image (fun y ↦ y - (a : ZMod N)) ∪ E02 (a + b)
    have hbad_lt : bad.card < (Finset.univ : Finset (ZMod N)).card := by
      have hc1 : bad.card ≤ (E01 a).card + (E12 b).card + (E02 (a + b)).card := by
        have h1 := Finset.card_union_le (E01 a ∪ (E12 b).image (fun y ↦ y - (a : ZMod N))) (E02 (a + b))
        have h2 := Finset.card_union_le (E01 a) ((E12 b).image (fun y ↦ y - (a : ZMod N)))
        have h3 := Finset.card_image_le (s := E12 b) (f := fun y ↦ y - (a : ZMod N))
        dsimp only [bad]; omega
      rw [Finset.card_univ, ZMod.card N]
      have := haB.2.1; have := hbB.2.2.1; have := habB.2.2.2
      omega
    obtain ⟨x, _, hx_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad_lt
    have hx1 : x ∉ E01 a := fun hc ↦ hx_not (Finset.mem_union_left _ (Finset.mem_union_left _ hc))
    have hx2 : x + (a : ZMod N) ∉ E12 b := by
      intro hc
      apply hx_not
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      rw [Finset.mem_image]
      exact ⟨x + (a : ZMod N), hc, by ring⟩
    have hx3 : x ∉ E02 (a + b) := fun hc ↦ hx_not (Finset.mem_union_right _ hc)
    have hadj01 : G'.Adj (0, x) (1, x + (a : ZMod N)) := by
      by_contra hc; exact hx1 (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hc⟩)
    have hadj12 : G'.Adj (1, x + (a : ZMod N)) (2, x + (a : ZMod N) + (b : ZMod N)) := by
      by_contra hc; exact hx2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    have hadj02 : G'.Adj (0, x) (2, x + (a : ZMod N) + (b : ZMod N)) := by
      by_contra hc
      have : ¬ G'.Adj (0, x) (2, x + ((a + b : ℕ) : ZMod N)) := by
        push_cast; rwa [add_assoc] at hc
      exact hx3 (Finset.mem_filter.mpr ⟨Finset.mem_univ x, this⟩)
    have hclique : G'.IsNClique 3 {((0 : Fin 3), x), ((1 : Fin 3), x + (a : ZMod N)),
        ((2 : Fin 3), x + (a : ZMod N) + (b : ZMod N))} := by
      rw [SimpleGraph.is3Clique_iff]
      exact ⟨_, _, _, hadj01, hadj02, hadj12, rfl⟩
    exact hG'free _ hclique
  · -- Bound (C \ B).card ≤ δ * n
    -- Inject the disjoint union of E01, E12, E02 over a ∈ C into E_del
    let mkE01 (a : ℕ) (x : ZMod N) : Sym2 (Fin 3 × ZMod N) := s(((0 : Fin 3), x), ((1 : Fin 3), x + (a : ZMod N)))
    let mkE12 (a : ℕ) (x : ZMod N) : Sym2 (Fin 3 × ZMod N) := s(((1 : Fin 3), x), ((2 : Fin 3), x + (a : ZMod N)))
    let mkE02 (a : ℕ) (x : ZMod N) : Sym2 (Fin 3 × ZMod N) := s(((0 : Fin 3), x), ((2 : Fin 3), x + (a : ZMod N)))
    let S01 := (C \ B).sigma E01
    let S12 := (C \ B).sigma E12
    let S02 := (C \ B).sigma E02
    let I01 := S01.image (fun p ↦ mkE01 p.1 p.2)
    let I12 := S12.image (fun p ↦ mkE12 p.1 p.2)
    let I02 := S02.image (fun p ↦ mkE02 p.1 p.2)
    have hsub01 : I01 ⊆ E_del := by
      intro e he
      obtain ⟨⟨a, x⟩, hs, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨haCB, hx⟩ := Finset.mem_sigma.mp hs
      have haC : a ∈ C := (Finset.mem_sdiff.mp haCB).1
      have hnot : ¬ G'.Adj (0, x) (1, x + (a : ZMod N)) := (Finset.mem_filter.mp hx).2
      rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset]
      refine ⟨?_, hnot⟩
      exact ksvGraph_adj_01.mpr ⟨a, haC, by ring⟩
    have hsub12 : I12 ⊆ E_del := by
      intro e he
      obtain ⟨⟨a, x⟩, hs, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨haCB, hx⟩ := Finset.mem_sigma.mp hs
      have haC : a ∈ C := (Finset.mem_sdiff.mp haCB).1
      have hnot : ¬ G'.Adj (1, x) (2, x + (a : ZMod N)) := (Finset.mem_filter.mp hx).2
      rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset]
      refine ⟨?_, hnot⟩
      exact ksvGraph_adj_12.mpr ⟨a, haC, by ring⟩
    have hsub02 : I02 ⊆ E_del := by
      intro e he
      obtain ⟨⟨a, x⟩, hs, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨haCB, hx⟩ := Finset.mem_sigma.mp hs
      have haC : a ∈ C := (Finset.mem_sdiff.mp haCB).1
      have hnot : ¬ G'.Adj (0, x) (2, x + (a : ZMod N)) := (Finset.mem_filter.mp hx).2
      rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset]
      refine ⟨?_, hnot⟩
      exact ksvGraph_adj_02.mpr ⟨a, haC, by ring⟩
    have hsym2_ne : ∀ (i1 j1 i2 j2 : Fin 3) (x1 y1 x2 y2 : ZMod N),
        i1 ≠ j1 → i2 ≠ j2 →
        (s((i1, x1), (j1, y1)) = s((i2, x2), (j2, y2))) →
        (i1 = i2 ∧ j1 = j2 ∧ x1 = x2 ∧ y1 = y2) ∨ (i1 = j2 ∧ j1 = i2 ∧ x1 = y2 ∧ y1 = x2) := by
      intro i1 j1 i2 j2 x1 y1 x2 y2 _ _ h
      rw [Sym2.eq_iff] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨congr_arg Prod.fst h1, congr_arg Prod.fst h2,
          congr_arg Prod.snd h1, congr_arg Prod.snd h2⟩
      · exact Or.inr ⟨congr_arg Prod.fst h1, congr_arg Prod.fst h2,
          congr_arg Prod.snd h1, congr_arg Prod.snd h2⟩
    have hdisj01_12 : Disjoint I01 I12 := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      obtain ⟨p1, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨p2, _, heq⟩ := Finset.mem_image.mp h2
      rcases hsym2_ne 1 2 0 1 _ _ _ _ (by decide) (by decide) heq with ⟨h, _, _, _⟩ | ⟨_, h, _, _⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    have hdisj01_02 : Disjoint I01 I02 := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      obtain ⟨p1, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨p2, _, heq⟩ := Finset.mem_image.mp h2
      rcases hsym2_ne 0 2 0 1 _ _ _ _ (by decide) (by decide) heq with ⟨_, h, _, _⟩ | ⟨h, _, _, _⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    have hdisj12_02 : Disjoint I12 I02 := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      obtain ⟨p1, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨p2, _, heq⟩ := Finset.mem_image.mp h2
      rcases hsym2_ne 0 2 1 2 _ _ _ _ (by decide) (by decide) heq with ⟨h, _, _, _⟩ | ⟨_, h, _, _⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    have hinj_aux : ∀ (i j : Fin 3), i ≠ j →
        ∀ p1 p2 : Σ _ : ℕ, ZMod N, p1.1 ∈ C → p2.1 ∈ C →
        s((i, p1.2), (j, p1.2 + (p1.1 : ZMod N))) = s((i, p2.2), (j, p2.2 + (p2.1 : ZMod N))) →
        p1 = p2 := by
      intro i j hij ⟨a1, x1⟩ ⟨a2, x2⟩ ha1 ha2 heq
      rcases hsym2_ne i j i j _ _ _ _ hij hij heq with ⟨_, _, hx, hy⟩ | ⟨h, _, _, _⟩
      · subst hx
        have hmod : (a1 : ZMod N) = (a2 : ZMod N) := by
          have := congr_arg (· - x1) hy
          simpa using this
        dsimp only at ha1 ha2
        have ha1_lt : a1 < N := by have := (Finset.mem_Icc.mp (hC ha1)).2; omega
        have ha2_lt : a2 < N := by have := (Finset.mem_Icc.mp (hC ha2)).2; omega
        have haeq : a1 = a2 := zmod_natCast_inj ha1_lt ha2_lt hmod
        subst haeq; rfl
      · exact absurd h hij
    have hc01 : I01.card = S01.card := by
      refine Finset.card_image_of_injOn fun p1 hp1 p2 hp2 heq ↦ ?_
      rw [Finset.mem_coe] at hp1 hp2
      exact hinj_aux 0 1 (by decide) p1 p2 (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hp1).1).1
        (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hp2).1).1 heq
    have hc12 : I12.card = S12.card := by
      refine Finset.card_image_of_injOn fun p1 hp1 p2 hp2 heq ↦ ?_
      rw [Finset.mem_coe] at hp1 hp2
      exact hinj_aux 1 2 (by decide) p1 p2 (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hp1).1).1
        (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hp2).1).1 heq
    have hc02 : I02.card = S02.card := by
      refine Finset.card_image_of_injOn fun p1 hp1 p2 hp2 heq ↦ ?_
      rw [Finset.mem_coe] at hp1 hp2
      exact hinj_aux 0 2 (by decide) p1 p2 (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hp1).1).1
        (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hp2).1).1 heq
    have hsum_le : S01.card + S12.card + S02.card ≤ E_del.card := by
      have hunion : I01 ∪ I12 ∪ I02 ⊆ E_del :=
        Finset.union_subset (Finset.union_subset hsub01 hsub12) hsub02
      have hcard_u : (I01 ∪ I12 ∪ I02).card = I01.card + I12.card + I02.card := by
        rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisj01_02, hdisj12_02⟩),
          Finset.card_union_of_disjoint hdisj01_12]
      calc S01.card + S12.card + S02.card
          = I01.card + I12.card + I02.card := by rw [hc01, hc12, hc02]
        _ = (I01 ∪ I12 ∪ I02).card := hcard_u.symm
        _ ≤ E_del.card := Finset.card_le_card hunion
    have hCB_mul : (C \ B).card * N ≤ 3 * E_del.card := by
      have h1 : (C \ B).card * N ≤ ∑ a ∈ C \ B, 3 * ((E01 a).card + (E12 a).card + (E02 a).card) := by
        calc (C \ B).card * N
            = ∑ _a ∈ C \ B, N := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ a ∈ C \ B, 3 * ((E01 a).card + (E12 a).card + (E02 a).card) := by
              refine Finset.sum_le_sum fun a ha ↦ ?_
              obtain ⟨haC, haNotB⟩ := Finset.mem_sdiff.mp ha
              have hnot : ¬(3 * (E01 a).card < N ∧ 3 * (E12 a).card < N ∧ 3 * (E02 a).card < N) :=
                fun hc ↦ haNotB (Finset.mem_filter.mpr ⟨haC, hc⟩)
              omega
      have h2 : ∑ a ∈ C \ B, 3 * ((E01 a).card + (E12 a).card + (E02 a).card) =
          3 * (S01.card + S12.card + S02.card) := by
        simp only [S01, S12, S02, Finset.card_sigma, ← Finset.mul_sum, Finset.sum_add_distrib]
      omega
    have hCB_real : ((C \ B).card : ℝ) * (N : ℝ) ≤ 27 * ε_tri * (N : ℝ) ^ 2 := by
      have h1 : ((C \ B).card : ℝ) * (N : ℝ) ≤ 3 * (E_del.card : ℝ) := by exact_mod_cast hCB_mul
      have h2 : (E_del.card : ℝ) < 9 * ε_tri * (N : ℝ) ^ 2 := by
        have h3N : ((3 * N : ℕ) : ℝ) ^ 2 = 9 * (N : ℝ) ^ 2 := by push_cast; ring
        rw [h3N] at hEdel_card
        linarith
      linarith
    have hNpos : (0 : ℝ) < N := by positivity
    have hCB_le_N : ((C \ B).card : ℝ) ≤ 27 * ε_tri * (N : ℝ) := by
      have hmul : ((C \ B).card : ℝ) * (N : ℝ) ≤ (27 * ε_tri * (N : ℝ)) * (N : ℝ) := by linarith
      exact le_of_mul_le_mul_right hmul hNpos
    have hN3n : (N : ℝ) ≤ 3 * (n : ℝ) := by
      have : N ≤ 3 * n := by omega
      exact_mod_cast this
    calc ((C \ B).card : ℝ)
        ≤ 27 * ε_tri * (N : ℝ) := hCB_le_N
      _ ≤ 27 * ε_tri * (3 * (n : ℝ)) := mul_le_mul_of_nonneg_left hN3n (by positivity)
      _ = δ * (n : ℝ) := by simp only [ε_tri]; ring

end Mod3

section Mod4
open Filter Real Finset
open scoped Classical Pointwise

def upperSet (n : ℕ) : Finset ℕ := Finset.Ioc (n / 2) n

/- ### Elementary Parity Interval Counting Helpers -/

lemma card_filter_odd_Ioc (a b : ℕ) :
    (b - a) / 2 ≤ ((Finset.Ioc a b).filter Odd).card ∧
    ((Finset.Ioc a b).filter Odd).card ≤ (b - a + 1) / 2 := by
  by_cases hb0 : b = 0
  · subst hb0; simp
  · have hbij : (Finset.Ioc a b).filter Odd =
        (Finset.Icc ((a + 1) / 2) ((b + 1) / 2 - 1)).image (fun k ↦ 2 * k + 1) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, ⟨k, rfl⟩⟩
        exact ⟨k, ⟨by omega, by omega⟩, rfl⟩
      · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
        exact ⟨⟨by omega, by omega⟩, ⟨k, rfl⟩⟩
    rw [hbij, Finset.card_image_of_injective _ (fun x y h ↦ by omega), Nat.card_Icc]
    omega

lemma card_filter_odd_Icc (a b : ℕ) (ha : Odd a) (hb : Odd b) (hab : a ≤ b) :
    ((Finset.Icc a b).filter Odd).card = (b - a) / 2 + 1 := by
  obtain ⟨ka, rfl⟩ := ha
  obtain ⟨kb, rfl⟩ := hb
  have hbij : (Finset.Icc (2 * ka + 1) (2 * kb + 1)).filter Odd =
      (Finset.Icc ka kb).image (fun k ↦ 2 * k + 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨k, rfl⟩⟩
      exact ⟨k, ⟨by omega, by omega⟩, rfl⟩
    · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨k, rfl⟩⟩
  rw [hbij, Finset.card_image_of_injective _ (fun x y h ↦ by omega), Nat.card_Icc]
  omega

lemma card_filter_even_Icc (a b : ℕ) :
    ((Finset.Icc a b).filter Even).card ≤ (b - a) / 2 + 1 := by
  have hsub : (Finset.Icc a b).filter Even ⊆
      (Finset.Icc ((a + 1) / 2) (b / 2)).image (fun k ↦ 2 * k) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image] at hx ⊢
    obtain ⟨⟨h1, h2⟩, ⟨k, rfl⟩⟩ := hx
    exact ⟨k, ⟨by omega, by omega⟩, by omega⟩
  calc ((Finset.Icc a b).filter Even).card
      ≤ ((Finset.Icc ((a + 1) / 2) (b / 2)).image (fun k ↦ 2 * k)).card := Finset.card_le_card hsub
    _ ≤ (Finset.Icc ((a + 1) / 2) (b / 2)).card := Finset.card_image_le
    _ = b / 2 + 1 - (a + 1) / 2 := Nat.card_Icc _ _
    _ ≤ (b - a) / 2 + 1 := by omega

lemma card_filter_even_Icc_one (n : ℕ) :
    ((Finset.Icc 1 n).filter Even).card = n / 2 := by
  have hbij : (Finset.Icc 1 n).filter Even = (Finset.Icc 1 (n / 2)).image (fun k ↦ 2 * k) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨k, rfl⟩⟩
      exact ⟨k, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨k, by omega⟩⟩
  rw [hbij, Finset.card_image_of_injective _ (fun x y h ↦ by omega), Nat.card_Icc]
  omega

/- ### Elementary Sumset Lower Bound `|X + X| ≥ 2 |X| - 1` and Sum-Free Size Bound -/

lemma card_sumset_self_ge (X : Finset ℕ) (hX : X.Nonempty) :
    2 * X.card - 1 ≤ (X + X).card := by
  let a := X.min' hX
  let b := X.max' hX
  have ha : a ∈ X := Finset.min'_mem X hX
  have hb : b ∈ X := Finset.max'_mem X hX
  let L := X.image (fun x ↦ a + x)
  let R := (X.erase a).image (fun x ↦ x + b)
  have hLsub : L ⊆ X + X := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.add_mem_add ha hx
  have hRsub : R ⊆ X + X := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.add_mem_add (Finset.mem_of_mem_erase hx) hb
  have hdisj : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro z hzL hzR
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hzL
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hzR
    have hxle : x ≤ b := Finset.le_max' X x hx
    have hay : a < y := lt_of_le_of_ne (Finset.min'_le X y (Finset.mem_of_mem_erase hy))
      (Finset.mem_erase.mp hy).1.symm
    omega
  have hcL : L.card = X.card := Finset.card_image_of_injective X (fun x y h ↦ by omega)
  have hcR : R.card = X.card - 1 := by
    rw [Finset.card_image_of_injective _ (fun x y h ↦ by omega), Finset.card_erase_of_mem ha]
  calc 2 * X.card - 1
      = L.card + R.card := by rw [hcL, hcR]; have := hX.card_pos; omega
    _ = (L ∪ R).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (X + X).card := Finset.card_le_card (Finset.union_subset hLsub hRsub)

lemma sumFree_card_le (n : ℕ) (B : Finset ℕ) (hBsub : B ⊆ Finset.Icc 1 n)
    (hBsf : IsSumFree (B : Set ℕ)) : 2 * B.card ≤ n + 1 := by
  by_cases hne : B.Nonempty
  · let m := B.max' hne
    have hmB : m ∈ B := Finset.max'_mem B hne
    have hmn : m ≤ n := (Finset.mem_Icc.mp (hBsub hmB)).2
    let B' := B.erase m
    let R := B'.image (fun x ↦ m - x)
    have hB'sub : B' ⊆ Finset.Icc 1 (m - 1) := by
      intro x hx
      obtain ⟨hxm, hxB⟩ := Finset.mem_erase.mp hx
      have hx1 := (Finset.mem_Icc.mp (hBsub hxB)).1
      have hxm' : x ≤ m := Finset.le_max' B x hxB
      exact Finset.mem_Icc.mpr ⟨hx1, by omega⟩
    have hRsub : R ⊆ Finset.Icc 1 (m - 1) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hxm, hxB⟩ := Finset.mem_erase.mp hx
      have hx1 := (Finset.mem_Icc.mp (hBsub hxB)).1
      have hxm' : x ≤ m := Finset.le_max' B x hxB
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hdisj : Disjoint B' R := by
      rw [Finset.disjoint_left]
      intro y hyB' hyR
      obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hyR
      have hxB := Finset.mem_of_mem_erase hx
      have hyB := Finset.mem_of_mem_erase hyB'
      have hxm' : x ≤ m := Finset.le_max' B x hxB
      rw [isSumFree_iff] at hBsf
      exact hBsf x (Finset.mem_coe.mpr hxB) y (Finset.mem_coe.mpr hyB)
        (by have hxy : x + y = m := by omega
            rw [hxy]; exact Finset.mem_coe.mpr hmB)
    have hcR : R.card = B'.card := by
      refine Finset.card_image_of_injOn fun x hx y hy heq ↦ ?_
      rw [Finset.mem_coe] at hx hy
      have hxle : x ≤ m := Finset.le_max' B x (Finset.mem_of_mem_erase hx)
      have hyle : y ≤ m := Finset.le_max' B y (Finset.mem_of_mem_erase hy)
      omega
    have hcard : B'.card + R.card ≤ (Finset.Icc 1 (m - 1)).card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card (Finset.union_subset hB'sub hRsub)
    have hB'card : B'.card + 1 = B.card := Finset.card_erase_add_one hmB
    have hIcc : (Finset.Icc 1 (m - 1)).card = m - 1 := by simp
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (hBsub hmB)).1
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp

lemma sumFree_even_card_le (n : ℕ) (B : Finset ℕ) (hBsub : B ⊆ Finset.Icc 1 n)
    (hBsf : IsSumFree (B : Set ℕ)) :
    4 * (B.filter Even).card ≤ n + 2 := by
  let Be := B.filter Even
  let C := Be.image (· / 2)
  have hCsub : C ⊆ Finset.Icc 1 (n / 2) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxB, ⟨k, hk⟩⟩ := Finset.mem_filter.mp hx
    have ⟨h1, h2⟩ := Finset.mem_Icc.mp (hBsub hxB)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hCsf : IsSumFree (C : Set ℕ) := by
    rw [isSumFree_iff]
    intro a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
    obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hab)
    obtain ⟨hxB, ⟨kx, hkx⟩⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyB, ⟨ky, hky⟩⟩ := Finset.mem_filter.mp hy
    obtain ⟨hzB, ⟨kz, hkz⟩⟩ := Finset.mem_filter.mp hz
    rw [isSumFree_iff] at hBsf
    exact hBsf x (Finset.mem_coe.mpr hxB) y (Finset.mem_coe.mpr hyB)
      (by have hxy : x + y = z := by omega
          rw [hxy]; exact Finset.mem_coe.mpr hzB)
  have hCcard : C.card = Be.card := by
    refine Finset.card_image_of_injOn fun x hx y hy heq ↦ ?_
    rw [Finset.mem_coe] at hx hy
    obtain ⟨_, ⟨kx, hkx⟩⟩ := Finset.mem_filter.mp hx
    obtain ⟨_, ⟨ky, hky⟩⟩ := Finset.mem_filter.mp hy
    omega
  have hle := sumFree_card_le (n / 2) C hCsub hCsf
  rw [hCcard] at hle
  dsimp only [Be] at hle
  omega

/- ### Bézout Identity for `Finset.gcd` and `VerySmallDoubling` Diameter Bound -/

lemma finset_gcd_mem_addSubgroup {R : ℕ} (A : Finset ℕ) (H : AddSubgroup (ZMod R))
    (hAH : ∀ a ∈ A, (a : ZMod R) ∈ H) :
    ((A.gcd id : ℕ) : ZMod R) ∈ H := by
  induction A using Finset.induction_on with
  | empty => simp [H.zero_mem]
  | insert a s ha ih =>
    rw [Finset.gcd_insert]
    have haH : (a : ZMod R) ∈ H := hAH a (Finset.mem_insert_self a s)
    have hsH : ((s.gcd id : ℕ) : ZMod R) ∈ H :=
      ih fun b hb ↦ hAH b (Finset.mem_insert_of_mem hb)
    set g := s.gcd id
    have hbez : (Nat.gcd a g : ℤ) = (a : ℤ) * Nat.gcdA a g + (g : ℤ) * Nat.gcdB a g :=
      Nat.gcd_eq_gcd_ab a g
    have hcast : ((Nat.gcd a g : ℕ) : ZMod R) =
        (Nat.gcdA a g) • (a : ZMod R) + (Nat.gcdB a g) • (g : ZMod R) := by
      have h1 := congr_arg (Int.cast : ℤ → ZMod R) hbez
      simpa [zsmul_eq_mul, mul_comm] using h1
    change ((Nat.gcd a g : ℕ) : ZMod R) ∈ H
    rw [hcast]
    exact H.add_mem (H.zsmul_mem haH _) (H.zsmul_mem hsH _)

/-- Core Freiman-type diameter bound via Mathlib's `Finset.card_mul_finset_lt_two`. -/
lemma diameter_bound_of_small_diff (A : Finset ℕ) (R Δ : ℕ)
    (h0A : 0 ∈ A) (hRA : R ∈ A) (hRpos : 0 < R)
    (hAsub : A ⊆ Finset.Icc 0 R)
    (hgcd : A.gcd id = 1)
    (hdiff : ((A.image (Nat.cast : ℕ → ℤ)) - (A.image (Nat.cast : ℕ → ℤ))).card ≤ 2 * A.card + Δ + 1)
    (hsmall : 4 * (Δ + 2) ≤ A.card - 1) :
    R ≤ A.card + 3 * Δ + 6 := by
  have : NeZero R := ⟨by omega⟩
  let AZ : Finset ℤ := A.image (Nat.cast : ℕ → ℤ)
  let Abar : Finset (ZMod R) := A.image (Nat.cast : ℕ → ZMod R)
  have hAcard_ge : 2 ≤ A.card := by
    have hsub : ({0, R} : Finset ℕ) ⊆ A := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    calc 2 = ({0, R} : Finset ℕ).card := (Finset.card_pair (by omega)).symm
      _ ≤ A.card := Finset.card_le_card hsub
  have hAbar_eq : Abar = (A.erase R).image (Nat.cast : ℕ → ZMod R) := by
    apply Finset.ext; intro z
    simp only [Abar, Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨a, ha, rfl⟩
      by_cases hR : a = R
      · subst hR
        exact ⟨0, ⟨by omega, h0A⟩, by simp⟩
      · exact ⟨a, ⟨hR, ha⟩, rfl⟩
    · rintro ⟨a, ⟨_, ha⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
  have hAbar_card : Abar.card = A.card - 1 := by
    rw [hAbar_eq, Finset.card_image_of_injOn, Finset.card_erase_of_mem hRA]
    intro a ha b hb heq
    rw [Finset.mem_coe] at ha hb
    have haR : a < R := lt_of_le_of_ne (Finset.mem_Icc.mp (hAsub (Finset.mem_of_mem_erase ha))).2
      (Finset.mem_erase.mp ha).1
    have hbR : b < R := lt_of_le_of_ne (Finset.mem_Icc.mp (hAsub (Finset.mem_of_mem_erase hb))).2
      (Finset.mem_erase.mp hb).1
    have h1 := congr_arg ZMod.val heq
    rw [ZMod.val_natCast_of_lt haR, ZMod.val_natCast_of_lt hbR] at h1
    exact h1
  -- Fiber counting: (Abar - Abar).card + A.card ≤ (AZ - AZ).card
  have hfiber : (Abar - Abar).card + A.card ≤ (AZ - AZ).card := by
    let D := AZ - AZ
    let F (z : ZMod R) : Finset ℤ := D.filter fun t ↦ (t : ZMod R) = z
    have hpart : ∑ z ∈ Abar - Abar, (F z).card ≤ D.card := by
      rw [← Finset.card_biUnion]
      · refine Finset.card_le_card fun t ht ↦ ?_
        obtain ⟨z, _, htz⟩ := Finset.mem_biUnion.mp ht
        exact (Finset.mem_filter.mp htz).1
      · intro z1 _ z2 _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro t h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have h0_in_Abar : (0 : ZMod R) ∈ Abar :=
      Finset.mem_image.mpr ⟨0, h0A, by simp⟩
    have hAbar_sub : Abar ⊆ Abar - Abar := by
      intro z hz
      simpa using Finset.sub_mem_sub hz h0_in_Abar
    have h0AZ : (0 : ℤ) ∈ AZ := Finset.mem_image.mpr ⟨0, h0A, rfl⟩
    have hRAZ : (R : ℤ) ∈ AZ := Finset.mem_image.mpr ⟨R, hRA, rfl⟩
    have hF0 : 3 ≤ (F 0).card := by
      have hsub : ({-(R : ℤ), 0, (R : ℤ)} : Finset ℤ) ⊆ F 0 := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rw [Finset.mem_filter]
        rcases ht with rfl | rfl | rfl
        · refine ⟨?_, by simp⟩
          change -(R : ℤ) ∈ AZ - AZ
          rw [← zero_sub]
          exact Finset.sub_mem_sub h0AZ hRAZ
        · refine ⟨?_, by simp⟩
          change (0 : ℤ) ∈ AZ - AZ
          rw [← sub_self (0 : ℤ)]
          exact Finset.sub_mem_sub h0AZ h0AZ
        · refine ⟨?_, by simp⟩
          change (R : ℤ) ∈ AZ - AZ
          rw [← sub_zero (R : ℤ)]
          exact Finset.sub_mem_sub hRAZ h0AZ
      have hc3 : ({-(R : ℤ), 0, (R : ℤ)} : Finset ℤ).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair]
        · omega
        · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      exact hc3 ▸ Finset.card_le_card hsub
    have hFA : ∀ z ∈ Abar.erase 0, 2 ≤ (F z).card := by
      intro z hz
      obtain ⟨hz0, hzAbar⟩ := Finset.mem_erase.mp hz
      rw [hAbar_eq] at hzAbar
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hzAbar
      obtain ⟨haRne, haA⟩ := Finset.mem_erase.mp ha
      have haR : a < R := lt_of_le_of_ne (Finset.mem_Icc.mp (hAsub haA)).2 haRne
      have haAZ : (a : ℤ) ∈ AZ := Finset.mem_image.mpr ⟨a, haA, rfl⟩
      have hsub : ({(a : ℤ), (a : ℤ) - (R : ℤ)} : Finset ℤ) ⊆ F (a : ZMod R) := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rw [Finset.mem_filter]
        rcases ht with rfl | rfl
        · refine ⟨?_, by simp⟩
          change (a : ℤ) ∈ AZ - AZ
          rw [← sub_zero (a : ℤ)]
          exact Finset.sub_mem_sub haAZ h0AZ
        · refine ⟨?_, by simp⟩
          exact Finset.sub_mem_sub haAZ hRAZ
      have hc2 : ({(a : ℤ), (a : ℤ) - (R : ℤ)} : Finset ℤ).card = 2 :=
        Finset.card_pair (by omega)
      exact hc2 ▸ Finset.card_le_card hsub
    have hFrest : ∀ z ∈ (Abar - Abar) \ Abar, 1 ≤ (F z).card := by
      intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.mp (Finset.mem_sdiff.mp hz).1
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      refine Finset.card_pos.mpr ⟨(a : ℤ) - (b : ℤ), Finset.mem_filter.mpr ⟨?_, by simp⟩⟩
      exact Finset.sub_mem_sub (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
        (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    have hsplit : ∑ z ∈ Abar - Abar, (F z).card =
        (F 0).card + (∑ z ∈ Abar.erase 0, (F z).card) +
        (∑ z ∈ (Abar - Abar) \ Abar, (F z).card) := by
      rw [← Finset.sum_sdiff hAbar_sub, add_comm]
      congr 1
      rw [← Finset.add_sum_erase _ _ h0_in_Abar]
    have hs1 : 2 * (Abar.erase 0).card ≤ ∑ z ∈ Abar.erase 0, (F z).card := by
      calc 2 * (Abar.erase 0).card = ∑ _z ∈ Abar.erase 0, 2 := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ z ∈ Abar.erase 0, (F z).card := Finset.sum_le_sum hFA
    have hs2 : ((Abar - Abar) \ Abar).card ≤ ∑ z ∈ (Abar - Abar) \ Abar, (F z).card := by
      calc ((Abar - Abar) \ Abar).card = ∑ _z ∈ (Abar - Abar) \ Abar, 1 := by simp
        _ ≤ ∑ z ∈ (Abar - Abar) \ Abar, (F z).card := Finset.sum_le_sum hFrest
    have hc_erase : (Abar.erase 0).card + 1 = Abar.card := Finset.card_erase_add_one h0_in_Abar
    have hc_sdiff : ((Abar - Abar) \ Abar).card + Abar.card = (Abar - Abar).card :=
      Finset.card_sdiff_add_card_eq_card hAbar_sub
    dsimp only [D] at hpart
    omega
  -- Now apply Finset.card_mul_finset_lt_two in Multiplicative (ZMod R)!
  have hAbar_sub_le : (Abar - Abar).card ≤ Abar.card + Δ + 2 := by
    dsimp only [AZ] at hfiber; omega
  let S : Finset (Multiplicative (ZMod R)) := Abar.image Multiplicative.ofAdd
  let Ainv : Finset (Multiplicative (ZMod R)) := Abar.image (fun x ↦ (Multiplicative.ofAdd x)⁻¹)
  have hScard : S.card = Abar.card :=
    Finset.card_image_of_injective Abar Multiplicative.ofAdd.injective
  have hAinvcard : Ainv.card = Abar.card :=
    Finset.card_image_of_injective Abar (fun x y h ↦ Multiplicative.ofAdd.injective (inv_injective h))
  have hmul_card : (Ainv * S).card = (Abar - Abar).card := by
    have heq : Ainv * S = (Abar - Abar).image Multiplicative.ofAdd := by
      apply Finset.ext; intro g
      simp only [Finset.mem_mul, Ainv, S, Finset.mem_image, Finset.mem_sub]
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, _, ⟨x, hx, rfl⟩, rfl⟩
        refine ⟨x - y, ⟨x, hx, y, hy, rfl⟩, ?_⟩
        rw [sub_eq_neg_add, ofAdd_add, ofAdd_neg]
      · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
        refine ⟨(Multiplicative.ofAdd y)⁻¹, ⟨y, hy, rfl⟩, Multiplicative.ofAdd x, ⟨x, hx, rfl⟩, ?_⟩
        rw [sub_eq_neg_add, ofAdd_add, ofAdd_neg]
    rw [heq, Finset.card_image_of_injective _ Multiplicative.ofAdd.injective]
  have hSpos : 0 < S.card := by omega
  have hSne : S.Nonempty := Finset.card_pos.mp hSpos
  set ε : ℝ := 1 - (Δ + 2 : ℝ) / (S.card : ℝ)
  have hSreal_pos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hSpos
  have hε_ge : (3 / 4 : ℝ) ≤ ε := by
    have hsm : 4 * ((Δ + 2 : ℕ) : ℝ) ≤ (S.card : ℝ) := by
      have : 4 * (Δ + 2) ≤ S.card := by omega
      exact_mod_cast this
    push_cast at hsm
    have hdiv : (Δ + 2 : ℝ) / (S.card : ℝ) ≤ 1 / 4 := by
      rw [div_le_iff₀ hSreal_pos]; linarith
    simp only [ε]; linarith
  have hε0 : 0 < ε := by linarith
  have hε1 : ε ≤ 1 := by
    have : 0 ≤ (Δ + 2 : ℝ) / (S.card : ℝ) := by positivity
    simp only [ε]; linarith
  have hmul_le : ((Ainv * S).card : ℝ) ≤ (2 - ε) * (S.card : ℝ) := by
    have h1 : ((Ainv * S).card : ℝ) ≤ (S.card : ℝ) + (Δ + 2 : ℝ) := by
      rw [hmul_card, hScard]
      exact_mod_cast hAbar_sub_le
    have h2 : (2 - ε) * (S.card : ℝ) = (S.card : ℝ) + (Δ + 2 : ℝ) := by
      simp only [ε]
      field_simp [hSreal_pos.ne']
      ring
    linarith
  obtain ⟨H, hFH, Z, hHcard, hZcard, hSZ⟩ :=
    Finset.card_mul_finset_lt_two hε0 hε1 hSne ⟨Ainv, by omega, hmul_le⟩
  have h2eps : 2 / ε - 1 ≤ 5 / 3 := by
    have : 2 / ε ≤ 8 / 3 := by
      rw [div_le_iff₀ hε0]; linarith
    linarith
  have hZle1 : Z.card ≤ 1 := by
    have : (Z.card : ℝ) < 2 := by linarith
    have : Z.card < 2 := by exact_mod_cast this
    omega
  have h1S : (1 : Multiplicative (ZMod R)) ∈ S :=
    Finset.mem_image.mpr ⟨0, Finset.mem_image.mpr ⟨0, h0A, by simp⟩, rfl⟩
  have hSH : ∀ x ∈ S, x ∈ H := by
    have h1HZ := hSZ (Finset.mem_coe.mpr h1S)
    obtain ⟨h1, hh1, z0, hz0, hmul1⟩ := Set.mem_mul.mp h1HZ
    have hZeq : Z = {z0} := by
      have hz0' : z0 ∈ Z := hz0
      have hcard1 : Z.card = 1 := le_antisymm hZle1 (Finset.card_pos.mpr ⟨z0, hz0'⟩)
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
      rw [hw] at hz0'
      rw [hw, Finset.mem_singleton.mp hz0']
    have hz0H : z0 ∈ H := by
      have : z0 = h1⁻¹ := eq_inv_of_mul_eq_one_right hmul1
      rw [this]; exact H.inv_mem hh1
    intro x hx
    have hxHZ := hSZ (Finset.mem_coe.mpr hx)
    obtain ⟨h2, hh2, z1, hz1, rfl⟩ := Set.mem_mul.mp hxHZ
    have hz1' : z1 = z0 := Finset.mem_singleton.mp (hZeq ▸ hz1)
    subst hz1'
    exact H.mul_mem hh2 hz0H
  -- Translate H to AddSubgroup (ZMod R) and show H = ⊤ using gcd(A) = 1
  let Hadd : AddSubgroup (ZMod R) := H.toAddSubgroup
  have hAH : ∀ a ∈ A, (a : ZMod R) ∈ Hadd := fun a ha ↦
    hSH (Multiplicative.ofAdd (a : ZMod R))
      (Finset.mem_image.mpr ⟨(a : ZMod R), Finset.mem_image.mpr ⟨a, ha, rfl⟩, rfl⟩)
  have h1H : (1 : ZMod R) ∈ Hadd := by
    have := finset_gcd_mem_addSubgroup A Hadd hAH
    rwa [hgcd, Nat.cast_one] at this
  have hHtop : H = ⊤ := by
    rw [eq_top_iff]
    intro g _
    change Multiplicative.toAdd g ∈ Hadd
    have hg : Multiplicative.toAdd g = (ZMod.val (Multiplicative.toAdd g)) • (1 : ZMod R) := by
      simp
    rw [hg]
    exact Hadd.nsmul_mem h1H _
  have hcardH_eq : @Fintype.card H hFH = R := by
    have heq1 : @Fintype.card H hFH = Fintype.card (Multiplicative (ZMod R)) := by
      subst hHtop
      exact @Fintype.card_congr _ _ hFH _ Subgroup.topEquiv.toEquiv
    rw [heq1, Fintype.card_multiplicative, ZMod.card R]
  rw [hcardH_eq] at hHcard
  have hboundR : (2 / ε - 1) * (S.card : ℝ) ≤ (S.card : ℝ) + 3 * (Δ + 2 : ℝ) := by
    have h1 : (2 / ε - 1) * (S.card : ℝ) = (S.card : ℝ) + (2 / ε) * (Δ + 2 : ℝ) := by
      have hsub : 2 / ε - 1 = 1 + 2 * (1 - ε) / ε := by field_simp [hε0.ne']; ring
      have h1e : (1 - ε) * (S.card : ℝ) = (Δ + 2 : ℝ) := by
        simp only [ε]; field_simp [hSreal_pos.ne']; ring
      calc (2 / ε - 1) * (S.card : ℝ)
          = (1 + 2 * (1 - ε) / ε) * (S.card : ℝ) := by rw [hsub]
        _ = (S.card : ℝ) + (2 / ε) * ((1 - ε) * (S.card : ℝ)) := by ring
        _ = (S.card : ℝ) + (2 / ε) * (Δ + 2 : ℝ) := by rw [h1e]
    rw [h1]
    have h2e : 2 / ε ≤ 3 := by rw [div_le_iff₀ hε0]; linarith
    have hmul : (2 / ε) * (Δ + 2 : ℝ) ≤ 3 * (Δ + 2 : ℝ) :=
      mul_le_mul_of_nonneg_right h2e (by positivity)
    linarith
  have hRreal : (R : ℝ) ≤ ((A.card + 3 * Δ + 6 : ℕ) : ℝ) := by
    have hS_le_A : (S.card : ℝ) ≤ (A.card : ℝ) := by
      have : S.card ≤ A.card := by omega
      exact_mod_cast this
    push_cast
    linarith
  exact_mod_cast hRreal

/- ### Exact Sum-Free Stability Theorem -/

private lemma diff_card_le_of_normalized (Bodd D_odd : Finset ℕ) (u d : ℕ)
    (hd_pos : 0 < d)
    (hu_le : ∀ x ∈ Bodd, u ≤ x)
    (hd_dvd : ∀ x ∈ Bodd, d ∣ x - u)
    (hD_mem : ∀ x ∈ Bodd, ∀ y ∈ Bodd, x < y → y - x ∈ D_odd) :
    let A := Bodd.image (fun x ↦ (x - u) / d)
    ((A.image (Nat.cast : ℕ → ℤ)) - (A.image (Nat.cast : ℕ → ℤ))).card ≤ 2 * D_odd.card + 1 := by
  intro A
  let AZ : Finset ℤ := A.image (Nat.cast : ℕ → ℤ)
  have hcov : AZ - AZ ⊆ ({0} : Finset ℤ) ∪
      D_odd.image (fun z ↦ ((z / d : ℕ) : ℤ)) ∪
      D_odd.image (fun z ↦ -((z / d : ℕ) : ℤ)) := by
    intro t ht
    obtain ⟨aZ, haZ, bZ, hbZ, rfl⟩ := Finset.mem_sub.mp ht
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp haZ
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hbZ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    have hxge := hu_le x hx; have hyge := hu_le y hy
    obtain ⟨qx, hqx⟩ := hd_dvd x hx
    obtain ⟨qy, hqy⟩ := hd_dvd y hy
    have hxd : (x - u) / d = qx := by rw [hqx, Nat.mul_div_cancel_left _ hd_pos]
    have hyd : (y - u) / d = qy := by rw [hqy, Nat.mul_div_cancel_left _ hd_pos]
    rw [hxd, hyd]
    rw [Finset.mem_union, Finset.mem_union]
    rcases lt_trichotomy y x with hlt | heq | hgt
    · left; right
      refine Finset.mem_image.mpr ⟨x - y, hD_mem y hy x hx hlt, ?_⟩
      have hqle : qy ≤ qx := Nat.le_of_mul_le_mul_left (by omega : d * qy ≤ d * qx) hd_pos
      have hxy : x - y = d * (qx - qy) := by
        have hsub : d * qx - d * qy = d * (qx - qy) := (Nat.mul_sub_left_distrib d qx qy).symm
        omega
      rw [hxy, Nat.mul_div_cancel_left _ hd_pos, Nat.cast_sub hqle]
    · left; left
      have : qx = qy := Nat.eq_of_mul_eq_mul_left hd_pos (by omega : d * qx = d * qy)
      simp [this]
    · right
      refine Finset.mem_image.mpr ⟨y - x, hD_mem x hx y hy hgt, ?_⟩
      have hqle : qx ≤ qy := Nat.le_of_mul_le_mul_left (by omega : d * qx ≤ d * qy) hd_pos
      have hyx : y - x = d * (qy - qx) := by
        have hsub : d * qy - d * qx = d * (qy - qx) := (Nat.mul_sub_left_distrib d qy qx).symm
        omega
      rw [hyx, Nat.mul_div_cancel_left _ hd_pos, Nat.cast_sub hqle]; ring
  have h1 := Finset.card_le_card hcov
  have h2 := Finset.card_union_le (({0} : Finset ℤ) ∪ D_odd.image (fun z ↦ ((z / d : ℕ) : ℤ)))
    (D_odd.image (fun z ↦ -((z / d : ℕ) : ℤ)))
  have h3 := Finset.card_union_le ({0} : Finset ℤ) (D_odd.image (fun z ↦ ((z / d : ℕ) : ℤ)))
  have h4 := Finset.card_image_le (s := D_odd) (f := fun z ↦ ((z / d : ℕ) : ℤ))
  have h5 := Finset.card_image_le (s := D_odd) (f := fun z ↦ -((z / d : ℕ) : ℤ))
  simp only [Finset.card_singleton] at h3
  dsimp only [AZ] at h1
  omega

theorem exact_sumFree_stability (n : ℕ) (B : Finset ℕ)
    (hn : 50000 ≤ n)
    (hBsub : B ⊆ Finset.Icc 1 n)
    (hBsf : IsSumFree (B : Set ℕ))
    (hBcard : n + 1 - 2 * B.card ≤ n / 25000) :
    ((B \ oddSet n).card + (oddSet n \ B).card ≤ n / 120) ∨
    ((B \ upperSet n).card + (upperSet n \ B).card ≤ n / 120) := by
  have h2B : 2 * B.card ≤ n + 1 := sumFree_card_le n B hBsub hBsf
  set Δ := n + 1 - 2 * B.card
  have hΔ_eq : 2 * B.card + Δ = n + 1 := by omega
  let Beven := B.filter Even
  let Bodd := B.filter Odd
  have hpart : Bodd.card + Beven.card = B.card := by
    have hdisj : Disjoint Bodd Beven := by
      rw [Finset.disjoint_filter]; intro x _ ho he
      exact Nat.not_even_iff_odd.mpr ho he
    have hunion : Bodd ∪ Beven = B := by
      ext x; simp only [Bodd, Beven, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx; rcases Nat.even_or_odd x with he | ho
        · exact Or.inr ⟨hx, he⟩
        · exact Or.inl ⟨hx, ho⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hBeven_le : 4 * Beven.card ≤ n + 2 := sumFree_even_card_le n B hBsub hBsf
  have hBodd_ge : n ≤ 4 * Bodd.card + 2 * Δ := by omega
  let Bodd_low := Bodd.filter (· ≤ n / 2)
  let Bodd_high := Bodd.filter (n / 2 < ·)
  have hodd_part : Bodd_low.card + Bodd_high.card = Bodd.card := by
    have : Bodd_high = Bodd.filter (fun x ↦ ¬(x ≤ n / 2)) := by
      ext x; simp [Bodd_high]
    rw [this, Finset.card_filter_add_card_filter_not]
  set K := n / 1000
  by_cases hcase1 : Bodd_low.card ≤ K
  · -- Case 1: B is close to upperSet n = (n/2, n]
    right
    let OddHi := (Finset.Ioc (n / 2) n).filter Odd
    have hOddHi_card : OddHi.card ≤ (n - n / 2 + 1) / 2 := (card_filter_odd_Ioc (n / 2) n).2
    have hBh_sub : Bodd_high ⊆ OddHi := by
      intro x hx
      obtain ⟨hxodd, hxgt⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxB, ho⟩ := Finset.mem_filter.mp hxodd
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hxgt, (Finset.mem_Icc.mp (hBsub hxB)).2⟩, ho⟩
    set miss := (OddHi \ Bodd_high).card
    have hmiss_eq : miss + Bodd_high.card = OddHi.card :=
      Finset.card_sdiff_add_card_eq_card hBh_sub
    have hmiss_le : miss ≤ K + Δ + 2 := by omega
    -- Pigeonhole: every e ∈ Beven satisfies n / 2 ≤ e + 4 * miss + 2
    have hBeven_ge : ∀ e ∈ Beven, n / 2 ≤ e + 4 * miss + 2 := by
      intro e he
      by_cases hegt : n / 2 < e
      · omega
      · obtain ⟨heB, he_ev⟩ := Finset.mem_filter.mp he
        let J := (Finset.Ioc (n / 2) (n - e)).filter Odd
        have hJ_card : (n - e - n / 2) / 2 ≤ J.card := (card_filter_odd_Ioc (n / 2) (n - e)).1
        have hJ_cov : J ⊆ (OddHi \ Bodd_high) ∪ (OddHi \ Bodd_high).image (· - e) := by
          intro x hx
          obtain ⟨hxIoc, hxodd⟩ := Finset.mem_filter.mp hx
          obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hxIoc
          have hxOddHi : x ∈ OddHi :=
            Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨h1, by omega⟩, hxodd⟩
          have hxeOddHi : x + e ∈ OddHi := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
            obtain ⟨kx, rfl⟩ := hxodd; obtain ⟨ke, rfl⟩ := he_ev
            exact ⟨kx + ke, by omega⟩
          rw [Finset.mem_union]
          by_cases hxBh : x ∈ Bodd_high
          · right
            refine Finset.mem_image.mpr ⟨x + e, Finset.mem_sdiff.mpr ⟨hxeOddHi, ?_⟩, by omega⟩
            intro hxeBh
            have hxB : x ∈ B := (Finset.mem_filter.mp (Finset.mem_filter.mp hxBh).1).1
            have hxeB : x + e ∈ B := (Finset.mem_filter.mp (Finset.mem_filter.mp hxeBh).1).1
            rw [isSumFree_iff] at hBsf
            exact hBsf x (Finset.mem_coe.mpr hxB) e (Finset.mem_coe.mpr heB)
              (Finset.mem_coe.mpr hxeB)
          · exact Or.inl (Finset.mem_sdiff.mpr ⟨hxOddHi, hxBh⟩)
        have hJ_le : J.card ≤ 2 * miss := by
          calc J.card ≤ ((OddHi \ Bodd_high) ∪ (OddHi \ Bodd_high).image (· - e)).card :=
                Finset.card_le_card hJ_cov
            _ ≤ miss + ((OddHi \ Bodd_high).image (· - e)).card := Finset.card_union_le _ _
            _ ≤ miss + miss := by gcongr; exact Finset.card_image_le
            _ = 2 * miss := by omega
        omega
    have hBeven_low : (Beven.filter (· ≤ n / 2)).card ≤ 2 * miss + 2 := by
      have hsub : Beven.filter (· ≤ n / 2) ⊆
          (Finset.Icc (n / 2 - (4 * miss + 2)) (n / 2)).filter Even := by
        intro e he
        obtain ⟨heBe, hele⟩ := Finset.mem_filter.mp he
        have hge := hBeven_ge e heBe
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hele⟩,
          (Finset.mem_filter.mp heBe).2⟩
      calc (Beven.filter (· ≤ n / 2)).card
          ≤ ((Finset.Icc (n / 2 - (4 * miss + 2)) (n / 2)).filter Even).card :=
            Finset.card_le_card hsub
        _ ≤ (n / 2 - (n / 2 - (4 * miss + 2))) / 2 + 1 := card_filter_even_Icc _ _
        _ ≤ 2 * miss + 2 := by omega
    have hB_sdiff : (B \ upperSet n).card ≤ 3 * K + 2 * Δ + 6 := by
      have hsub : B \ upperSet n ⊆ Bodd_low ∪ Beven.filter (· ≤ n / 2) := by
        intro x hx
        obtain ⟨hxB, hxnot⟩ := Finset.mem_sdiff.mp hx
        have hxle : x ≤ n / 2 := by
          by_contra hc
          exact hxnot (Finset.mem_Ioc.mpr ⟨by omega, (Finset.mem_Icc.mp (hBsub hxB)).2⟩)
        rw [Finset.mem_union]
        rcases Nat.even_or_odd x with he | ho
        · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hxB, he⟩, hxle⟩)
        · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hxB, ho⟩, hxle⟩)
      calc (B \ upperSet n).card
          ≤ (Bodd_low ∪ Beven.filter (· ≤ n / 2)).card := Finset.card_le_card hsub
        _ ≤ Bodd_low.card + (Beven.filter (· ≤ n / 2)).card := Finset.card_union_le _ _
        _ ≤ 3 * K + 2 * Δ + 6 := by omega
    have hU_sdiff : (upperSet n \ B).card ≤ 3 * K + 3 * Δ + 7 := by
      have h1 := Finset.card_sdiff_add_card_inter (upperSet n) B
      have h2 := Finset.card_sdiff_add_card_inter B (upperSet n)
      rw [Finset.inter_comm] at h2
      have hUcard : (upperSet n).card = n - n / 2 := Nat.card_Ioc _ _
      omega
    omega
  · -- Case 2: K < Bodd_low.card -> B is close to oddSet n
    left
    have hKlt : K < Bodd_low.card := by omega
    let D_odd : Finset ℕ := ((Bodd ×ˢ Bodd).filter (fun p ↦ p.1 < p.2)).image (fun p ↦ p.2 - p.1)
    let S_odd : Finset ℕ := ((Bodd ×ˢ Bodd).image (fun p ↦ p.1 + p.2)).filter (· ≤ n)
    have hDS_even : ∀ z ∈ D_odd ∪ S_odd, z ∈ (Finset.Icc 1 n).filter Even := by
      intro z hz
      rcases Finset.mem_union.mp hz with hzD | hzS
      · obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hzD
        obtain ⟨hprod, hlt⟩ := Finset.mem_filter.mp hxy
        dsimp only at hlt
        obtain ⟨hx, hy⟩ := Finset.mem_product.mp hprod
        obtain ⟨hxB, ⟨kx, rfl⟩⟩ := Finset.mem_filter.mp hx
        obtain ⟨hyB, ⟨ky, rfl⟩⟩ := Finset.mem_filter.mp hy
        have hxI := Finset.mem_Icc.mp (hBsub hxB)
        have hyI := Finset.mem_Icc.mp (hBsub hyB)
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
          ⟨ky - kx, by omega⟩⟩
      · obtain ⟨hzimg, hzle⟩ := Finset.mem_filter.mp hzS
        obtain ⟨⟨x, y⟩, hprod, rfl⟩ := Finset.mem_image.mp hzimg
        obtain ⟨hx, hy⟩ := Finset.mem_product.mp hprod
        obtain ⟨hxB, ⟨kx, rfl⟩⟩ := Finset.mem_filter.mp hx
        obtain ⟨hyB, ⟨ky, rfl⟩⟩ := Finset.mem_filter.mp hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hzle⟩,
          ⟨kx + ky + 1, by omega⟩⟩
    have hDS_disj : Disjoint (D_odd ∪ S_odd) Beven := by
      rw [Finset.disjoint_left]
      intro z hzDS hzBe
      have hzB : z ∈ B := (Finset.mem_filter.mp hzBe).1
      rw [isSumFree_iff] at hBsf
      rcases Finset.mem_union.mp hzDS with hzD | hzS
      · obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hzD
        obtain ⟨hprod, hlt⟩ := Finset.mem_filter.mp hxy
        dsimp only at hlt
        have hxB := (Finset.mem_filter.mp (Finset.mem_product.mp hprod).1).1
        have hyB := (Finset.mem_filter.mp (Finset.mem_product.mp hprod).2).1
        exact hBsf x (Finset.mem_coe.mpr hxB) (y - x) (Finset.mem_coe.mpr hzB)
          (by have hxy' : x + (y - x) = y := by omega
              rw [hxy']; exact Finset.mem_coe.mpr hyB)
      · obtain ⟨hzimg, _⟩ := Finset.mem_filter.mp hzS
        obtain ⟨⟨x, y⟩, hprod, rfl⟩ := Finset.mem_image.mp hzimg
        have hxB := (Finset.mem_filter.mp (Finset.mem_product.mp hprod).1).1
        have hyB := (Finset.mem_filter.mp (Finset.mem_product.mp hprod).2).1
        exact hBsf x (Finset.mem_coe.mpr hxB) y (Finset.mem_coe.mpr hyB)
          (Finset.mem_coe.mpr hzB)
    have hDS_ub : (D_odd ∪ S_odd).card + Beven.card ≤ n / 2 := by
      have hBe_sub : Beven ⊆ (Finset.Icc 1 n).filter Even := by
        intro x hx; obtain ⟨hxB, he⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hBsub hxB, he⟩
      rw [← card_filter_even_Icc_one n, ← Finset.card_union_of_disjoint hDS_disj]
      exact Finset.card_le_card (Finset.union_subset hDS_even hBe_sub)
    have hDS_le : (D_odd ∪ S_odd).card ≤ Bodd.card + Δ / 2 := by omega
    have hD_le : D_odd.card ≤ Bodd.card + Δ / 2 :=
      le_trans (Finset.card_le_card Finset.subset_union_left) hDS_le
    -- Normalize Bodd
    have hBodd_ne : Bodd.Nonempty := Finset.card_pos.mp (by omega)
    let u := Bodd.min' hBodd_ne
    let v := Bodd.max' hBodd_ne
    have hu_in : u ∈ Bodd := Finset.min'_mem Bodd hBodd_ne
    have hv_in : v ∈ Bodd := Finset.max'_mem Bodd hBodd_ne
    have hu_odd : Odd u := (Finset.mem_filter.mp hu_in).2
    have hv_odd : Odd v := (Finset.mem_filter.mp hv_in).2
    have hu_le : ∀ x ∈ Bodd, u ≤ x := fun x hx ↦ Finset.min'_le Bodd x hx
    have hv_ge : ∀ x ∈ Bodd, x ≤ v := fun x hx ↦ Finset.le_max' Bodd x hx
    have huv_lt : u < v := by
      have hcard2 : 2 ≤ Bodd.card := by omega
      by_contra hc
      have huv : u = v := le_antisymm (hu_le v hv_in) (by omega)
      have hsub : Bodd ⊆ {u} := fun x hx ↦ Finset.mem_singleton.mpr (by have := hu_le x hx; have := hv_ge x hx; omega)
      have := Finset.card_le_card hsub; simp at this; omega
    let d := (Bodd.image (· - u)).gcd id
    have hd_dvd : ∀ x ∈ Bodd, d ∣ x - u := fun x hx ↦
      Finset.gcd_dvd (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    have hd_pos : 0 < d := by
      by_contra hc
      have hd0 : d = 0 := by omega
      have hvd : 0 ∣ v - u := hd0 ▸ hd_dvd v hv_in
      rw [zero_dvd_iff] at hvd
      omega
    have h2_dvd_d : 2 ∣ d := by
      refine Finset.dvd_gcd fun y hy ↦ ?_
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨_, ⟨kx, rfl⟩⟩ := Finset.mem_filter.mp hx
      obtain ⟨ku, hku⟩ := hu_odd
      have := hu_le (2 * kx + 1) hx
      exact ⟨kx - ku, by dsimp only [id]; omega⟩
    let A : Finset ℕ := Bodd.image (fun x ↦ (x - u) / d)
    set R := (v - u) / d
    have hAcard : A.card = Bodd.card := by
      refine Finset.card_image_of_injOn fun x hx y hy heq ↦ ?_
      rw [Finset.mem_coe] at hx hy
      have h1 := Nat.mul_div_cancel' (hd_dvd x hx)
      have h2 := Nat.mul_div_cancel' (hd_dvd y hy)
      have hxge := hu_le x hx; have hyge := hu_le y hy
      have : x - u = y - u := by rw [← h1, ← h2, heq]
      omega
    have h0A : 0 ∈ A := Finset.mem_image.mpr ⟨u, hu_in, by simp⟩
    have hRA : R ∈ A := Finset.mem_image.mpr ⟨v, hv_in, rfl⟩
    have hRpos : 0 < R := by
      have h1 : d * R = v - u := Nat.mul_div_cancel' (hd_dvd v hv_in)
      by_contra hc
      have hR0 : R = 0 := Nat.eq_zero_of_not_pos hc
      rw [hR0, mul_zero] at h1
      omega
    have hAsub : A ⊆ Finset.Icc 0 R := by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.div_le_div_right (by have := hv_ge x hx; omega)⟩
    have hAgcd : A.gcd id = 1 := by
      set g := A.gcd id
      have hg_pos : 0 < g := by
        by_contra hc
        have hg0 : g = 0 := Nat.eq_zero_of_not_pos hc
        have : A.gcd id ∣ id R := Finset.gcd_dvd hRA
        change g ∣ R at this
        rw [hg0, zero_dvd_iff] at this
        omega
      have hdg_dvd : d * g ∣ d := by
        refine Finset.dvd_gcd fun y hy ↦ ?_
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        have h1 : g ∣ (x - u) / d := Finset.gcd_dvd (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
        obtain ⟨q, hq⟩ := h1
        have h2 := Nat.mul_div_cancel' (hd_dvd x hx)
        exact ⟨q, by dsimp only [id]; rw [← h2, hq]; ring⟩
      have hle : d * g ≤ d * 1 := by simpa using Nat.le_of_dvd hd_pos hdg_dvd
      have hg1 : g ≤ 1 := Nat.le_of_mul_le_mul_left hle hd_pos
      omega
    have hAdiff : ((A.image (Nat.cast : ℕ → ℤ)) - (A.image (Nat.cast : ℕ → ℤ))).card ≤
        2 * A.card + Δ + 1 := by
      have h1 := diff_card_le_of_normalized Bodd D_odd u d hd_pos hu_le hd_dvd
        (fun x hx y hy hlt ↦ Finset.mem_image.mpr ⟨(x, y),
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hlt⟩, rfl⟩)
      change ((A.image (Nat.cast : ℕ → ℤ)) - (A.image (Nat.cast : ℕ → ℤ))).card ≤ 2 * D_odd.card + 1 at h1
      omega
    have hR_le : R ≤ Bodd.card + 3 * Δ + 6 := by
      have h := diameter_bound_of_small_diff A R Δ h0A hRA hRpos hAsub hAgcd hAdiff (by omega)
      omega
    -- Show d = 2 (since d * (Bodd.card - 1) ≤ v - u ≤ n implies d < 5, and d = 4 is impossible)
    have hR_ge : Bodd.card - 1 ≤ R := by
      have hle : A.card ≤ (Finset.Icc 0 R).card := Finset.card_le_card hAsub
      simp only [Nat.card_Icc, Nat.sub_zero] at hle
      omega
    have hd_lt5 : d < 5 := by
      have hvu_le : v - u ≤ n := by
        have := (Finset.mem_Icc.mp (hBsub (Finset.mem_filter.mp hv_in).1)).2
        omega
      have hdR : d * R = v - u := Nat.mul_div_cancel' (hd_dvd v hv_in)
      have h1 : d * (Bodd.card - 1) ≤ n := by
        calc d * (Bodd.card - 1) ≤ d * R := Nat.mul_le_mul_left d hR_ge
          _ = v - u := hdR
          _ ≤ n := hvu_le
      have hBodd_gt : n / 5 + 1 ≤ Bodd.card - 1 := by omega
      have h2 : d * (n / 5 + 1) ≤ n := le_trans (Nat.mul_le_mul_left d hBodd_gt) h1
      by_contra hc
      have h5le : 5 * (n / 5 + 1) ≤ d * (n / 5 + 1) := Nat.mul_le_mul_right _ (by omega)
      omega
    have hd_eq2_or_4 : d = 2 ∨ d = 4 := by
      obtain ⟨k, hk⟩ := h2_dvd_d
      omega
    have hd_eq2 : d = 2 := by
      rcases hd_eq2_or_4 with h2 | h4
      · exact h2
      · exfalso
        have hmod4 : ∀ x ∈ Bodd, x % 4 = u % 4 := by
          intro x hx
          have hdv : 4 ∣ x - u := h4 ▸ hd_dvd x hx
          have hge := hu_le x hx
          omega
        have hdisj_DS : Disjoint D_odd S_odd := by
          rw [Finset.disjoint_left]
          intro z hzD hzS
          obtain ⟨⟨x1, y1⟩, h1, rfl⟩ := Finset.mem_image.mp hzD
          obtain ⟨hprod1, hlt1⟩ := Finset.mem_filter.mp h1
          dsimp only at hlt1
          have hx1 := hmod4 x1 (Finset.mem_product.mp hprod1).1
          have hy1 := hmod4 y1 (Finset.mem_product.mp hprod1).2
          obtain ⟨hzimg, _⟩ := Finset.mem_filter.mp hzS
          obtain ⟨⟨x2, y2⟩, hprod2, heq⟩ := Finset.mem_image.mp hzimg
          have hx2 := hmod4 x2 (Finset.mem_product.mp hprod2).1
          have hy2 := hmod4 y2 (Finset.mem_product.mp hprod2).2
          obtain ⟨ku, hku⟩ := hu_odd
          omega
        have hD_ge : Bodd.card - 1 ≤ D_odd.card := by
          have hsub : (Bodd.erase u).image (· - u) ⊆ D_odd := by
            intro z hz
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
            obtain ⟨hne, hxB⟩ := Finset.mem_erase.mp hx
            have hux : u < x := lt_of_le_of_ne (hu_le x hxB) hne.symm
            exact Finset.mem_image.mpr ⟨(u, x),
              Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu_in, hxB⟩, hux⟩, rfl⟩
          calc Bodd.card - 1
              = (Bodd.erase u).card := (Finset.card_erase_of_mem hu_in).symm
            _ = ((Bodd.erase u).image (· - u)).card := by
                symm; refine Finset.card_image_of_injOn fun x hx y hy heq ↦ ?_
                rw [Finset.mem_coe] at hx hy
                have := hu_le x (Finset.mem_of_mem_erase hx)
                have := hu_le y (Finset.mem_of_mem_erase hy)
                omega
            _ ≤ D_odd.card := Finset.card_le_card hsub
        have hS_ge : 2 * Bodd_low.card - 1 ≤ S_odd.card := by
          have hsub : Bodd_low + Bodd_low ⊆ S_odd := by
            intro z hz
            obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
            obtain ⟨hxO, hxle⟩ := Finset.mem_filter.mp hx
            obtain ⟨hyO, hyle⟩ := Finset.mem_filter.mp hy
            exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(x, y),
              Finset.mem_product.mpr ⟨hxO, hyO⟩, rfl⟩, by omega⟩
          have hne_low : Bodd_low.Nonempty := Finset.card_pos.mp (by omega)
          exact le_trans (card_sumset_self_ge Bodd_low hne_low) (Finset.card_le_card hsub)
        have hunion_card := Finset.card_union_of_disjoint hdisj_DS
        omega
    -- Now d = 2!
    let Iuv := (Finset.Icc u v).filter Odd
    have hIuv_card : Iuv.card = (v - u) / 2 + 1 := card_filter_odd_Icc u v hu_odd hv_odd (by omega)
    have hBodd_sub_Iuv : Bodd ⊆ Iuv := fun x hx ↦
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hu_le x hx, hv_ge x hx⟩,
        (Finset.mem_filter.mp hx).2⟩
    set miss2 := (Iuv \ Bodd).card
    have hmiss2_eq : miss2 + Bodd.card = Iuv.card :=
      Finset.card_sdiff_add_card_eq_card hBodd_sub_Iuv
    have hmiss2_le : miss2 ≤ 3 * Δ + 7 := by
      have : (v - u) / 2 = R := by simp [R, hd_eq2]
      omega
    -- Pigeonhole A: no even e in [2, v - u - 4*miss2 - 2] belongs to Beven
    have hpigA : ∀ e ∈ Beven, v - u < e + 4 * miss2 + 2 := by
      intro e he
      by_contra hc
      push Not at hc
      obtain ⟨heB, he_ev⟩ := Finset.mem_filter.mp he
      have he_pos : 2 ≤ e := by
        have h1 := (Finset.mem_Icc.mp (hBsub heB)).1
        obtain ⟨k, rfl⟩ := he_ev; omega
      have hve_odd : Odd (v - e) := by
        obtain ⟨kv, hkv⟩ := hv_odd; obtain ⟨ke, hke⟩ := he_ev
        exact ⟨kv - ke, by omega⟩
      let J := (Finset.Icc u (v - e)).filter Odd
      have hJ_card : J.card = (v - e - u) / 2 + 1 :=
        card_filter_odd_Icc u (v - e) hu_odd hve_odd (by omega)
      have hJ_cov : J ⊆ (Iuv \ Bodd) ∪ (Iuv \ Bodd).image (· - e) := by
        intro x hx
        obtain ⟨hxIcc, hxodd⟩ := Finset.mem_filter.mp hx
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hxIcc
        have hxIuv : x ∈ Iuv := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, by omega⟩, hxodd⟩
        have hxeIuv : x + e ∈ Iuv := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
          obtain ⟨kx, rfl⟩ := hxodd; obtain ⟨ke, rfl⟩ := he_ev; exact ⟨kx + ke, by omega⟩
        rw [Finset.mem_union]
        by_cases hxBo : x ∈ Bodd
        · right
          refine Finset.mem_image.mpr ⟨x + e, Finset.mem_sdiff.mpr ⟨hxeIuv, ?_⟩, by omega⟩
          intro hxeBo
          rw [isSumFree_iff] at hBsf
          exact hBsf x (Finset.mem_coe.mpr (Finset.mem_filter.mp hxBo).1)
            e (Finset.mem_coe.mpr heB)
            (Finset.mem_coe.mpr (Finset.mem_filter.mp hxeBo).1)
        · exact Or.inl (Finset.mem_sdiff.mpr ⟨hxIuv, hxBo⟩)
      have hJ_le : J.card ≤ 2 * miss2 := by
        calc J.card ≤ ((Iuv \ Bodd) ∪ (Iuv \ Bodd).image (· - e)).card := Finset.card_le_card hJ_cov
          _ ≤ miss2 + ((Iuv \ Bodd).image (· - e)).card := Finset.card_union_le _ _
          _ ≤ miss2 + miss2 := by gcongr; exact Finset.card_image_le
          _ = 2 * miss2 := by omega
      omega
    -- Pigeonhole B: no even e in [2*u + 4*miss2 + 2, 2*v - 4*miss2 - 2] belongs to Beven
    have hpigB : ∀ e ∈ Beven, e < 2 * u + 4 * miss2 + 2 ∨ 2 * v < e + 4 * miss2 + 2 := by
      intro e he
      by_contra hc
      push Not at hc
      obtain ⟨hge, hle⟩ := hc
      obtain ⟨heB, he_ev⟩ := Finset.mem_filter.mp he
      let lo := max u (e - v)
      let hi := min v (e - u)
      have hlo_odd : Odd lo := by
        by_cases h : u ≤ e - v
        · rw [show lo = e - v from max_eq_right h]
          obtain ⟨ku, hku⟩ := hu_odd; obtain ⟨kv, hkv⟩ := hv_odd; obtain ⟨ke, hke⟩ := he_ev
          exact ⟨ke - kv - 1, by omega⟩
        · rw [show lo = u from max_eq_left (by omega)]
          exact hu_odd
      have hhi_odd : Odd hi := by
        by_cases h : v ≤ e - u
        · rw [show hi = v from min_eq_left h]
          exact hv_odd
        · rw [show hi = e - u from min_eq_right (by omega)]
          obtain ⟨ku, hku⟩ := hu_odd; obtain ⟨ke, hke⟩ := he_ev
          exact ⟨ke - ku - 1, by omega⟩
      have hlohi : lo ≤ hi := by omega
      let J := (Finset.Icc lo hi).filter Odd
      have hJ_card : J.card = (hi - lo) / 2 + 1 := card_filter_odd_Icc lo hi hlo_odd hhi_odd hlohi
      have hJ_cov : J ⊆ (Iuv \ Bodd) ∪ (Iuv \ Bodd).image (fun y ↦ e - y) := by
        intro x hx
        obtain ⟨hxIcc, hxodd⟩ := Finset.mem_filter.mp hx
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hxIcc
        have hxIuv : x ∈ Iuv := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hxodd⟩
        have hexIuv : e - x ∈ Iuv := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
          obtain ⟨kx, rfl⟩ := hxodd; obtain ⟨ke, rfl⟩ := he_ev; exact ⟨ke - kx - 1, by omega⟩
        rw [Finset.mem_union]
        by_cases hxBo : x ∈ Bodd
        · right
          refine Finset.mem_image.mpr ⟨e - x, Finset.mem_sdiff.mpr ⟨hexIuv, ?_⟩, by omega⟩
          intro hexBo
          rw [isSumFree_iff] at hBsf
          have hxe_eq : x + (e - x) = e := by omega
          exact hBsf x (Finset.mem_coe.mpr (Finset.mem_filter.mp hxBo).1)
            (e - x) (Finset.mem_coe.mpr (Finset.mem_filter.mp hexBo).1)
            (by rw [hxe_eq]; exact Finset.mem_coe.mpr heB)
        · exact Or.inl (Finset.mem_sdiff.mpr ⟨hxIuv, hxBo⟩)
      have hJ_le : J.card ≤ 2 * miss2 := by
        calc J.card ≤ ((Iuv \ Bodd) ∪ (Iuv \ Bodd).image (fun y ↦ e - y)).card :=
              Finset.card_le_card hJ_cov
          _ ≤ miss2 + ((Iuv \ Bodd).image (fun y ↦ e - y)).card := Finset.card_union_le _ _
          _ ≤ miss2 + miss2 := by gcongr; exact Finset.card_image_le
          _ = 2 * miss2 := by omega
      omega
    -- Bound 2*v from below
    have h2v_ge : n ≤ 2 * v + 2 * Δ + 4 := by
      have : 2 * Bodd.card ≤ v - u + 2 := by omega
      omega
    -- Every e ∈ Beven lies in Icc (v - u - (4*miss2 + 1)) (2*u + 4*miss2 + 1) OR Icc (n - (14*Δ + 34)) n
    let gap1 := (Finset.Icc (v - u - (4 * miss2 + 1)) (2 * u + 4 * miss2 + 1)).filter Even
    let gap2 := (Finset.Icc (n - (14 * Δ + 34)) n).filter Even
    have hBeven_cov : Beven ⊆ gap1 ∪ gap2 := by
      intro e he
      have hA := hpigA e he
      have hB := hpigB e he
      have he_ev : Even e := (Finset.mem_filter.mp he).2
      have he_le : e ≤ n := (Finset.mem_Icc.mp (hBsub (Finset.mem_filter.mp he).1)).2
      rw [Finset.mem_union]
      rcases hB with hB1 | hB2
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, he_ev⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, he_le⟩, he_ev⟩)
    have hgap2_le : gap2.card ≤ 7 * Δ + 18 := by
      calc gap2.card ≤ (n - (n - (14 * Δ + 34))) / 2 + 1 := card_filter_even_Icc _ _
        _ ≤ 7 * Δ + 18 := by omega
    by_cases h3u : 3 * u ≤ v
    · -- Subcase (i): 3*u ≤ v -> Beven is tiny -> B is close to oddSet n!
      have hgap1_le : gap1.card ≤ 4 * miss2 + 3 := by
        calc gap1.card ≤ (2 * u + 4 * miss2 + 1 - (v - u - (4 * miss2 + 1))) / 2 + 1 :=
              card_filter_even_Icc _ _
          _ ≤ 4 * miss2 + 3 := by omega
      have hBe_tiny : Beven.card ≤ 19 * Δ + 50 := by
        calc Beven.card ≤ (gap1 ∪ gap2).card := Finset.card_le_card hBeven_cov
          _ ≤ gap1.card + gap2.card := Finset.card_union_le _ _
          _ ≤ 19 * Δ + 50 := by omega
      have hB_sdiff_odd : (B \ oddSet n).card = Beven.card := by
        congr 1; ext x
        simp only [Finset.mem_sdiff, oddSet, Beven, Finset.mem_filter]
        constructor
        · rintro ⟨hxB, hnot⟩
          exact ⟨hxB, Nat.not_odd_iff_even.mp fun ho ↦ hnot ⟨hBsub hxB, ho⟩⟩
        · rintro ⟨hxB, he⟩
          exact ⟨hxB, fun ⟨_, ho⟩ ↦ Nat.not_even_iff_odd.mpr ho he⟩
      have hOdd_sdiff_B : (oddSet n \ B).card ≤ 20 * Δ + 51 := by
        have h1 := Finset.card_sdiff_add_card_inter (oddSet n) B
        have h2 : oddSet n ∩ B = Bodd := by
          ext x; simp only [Finset.mem_inter, oddSet, Bodd, Finset.mem_filter]
          exact ⟨fun ⟨⟨_, ho⟩, hxB⟩ ↦ ⟨hxB, ho⟩, fun ⟨hxB, ho⟩ ↦ ⟨⟨hBsub hxB, ho⟩, hxB⟩⟩
        have hodd_card : (oddSet n).card ≤ (n + 1) / 2 := by
          dsimp only [oddSet]
          have := (card_filter_odd_Ioc 0 n).2
          have hI : Finset.Ioc 0 n = Finset.Icc 1 n := by ext x; simp; omega
          rw [hI, Nat.sub_zero] at this; exact this
        rw [h2] at h1
        omega
      rw [hB_sdiff_odd]; omega
    · -- Subcase (ii): 3*u > v -> |B| ≤ u + O(Δ) -> u near n/2 -> contradicts K < Bodd_low.card!
      exfalso
      have hgap1_le : gap1.card ≤ (3 * u - v) / 2 + 4 * miss2 + 3 := by
        calc gap1.card ≤ (2 * u + 4 * miss2 + 1 - (v - u - (4 * miss2 + 1))) / 2 + 1 :=
              card_filter_even_Icc _ _
          _ ≤ (3 * u - v) / 2 + 4 * miss2 + 3 := by omega
      have hBe_bound : Beven.card ≤ (3 * u - v) / 2 + 19 * Δ + 50 := by
        calc Beven.card ≤ (gap1 ∪ gap2).card := Finset.card_le_card hBeven_cov
          _ ≤ gap1.card + gap2.card := Finset.card_union_le _ _
          _ ≤ (3 * u - v) / 2 + 19 * Δ + 50 := by omega
      have hBodd_le : Bodd.card ≤ (v - u) / 2 + 1 := by
        have := Finset.card_le_card hBodd_sub_Iuv
        rw [hIuv_card] at this; exact this
      -- Combine: B.card = Bodd.card + Beven.card ≤ u + 19*Δ + 52
      have hu_big : n / 2 ≤ u + 20 * Δ + 55 := by omega
      -- Therefore Bodd_low ⊆ (Icc u (n / 2)).filter Odd has size ≤ 10*Δ + 30 < K!
      have hlow_sub : Bodd_low ⊆ (Finset.Ioc (u - 1) (n / 2)).filter Odd := by
        intro x hx
        obtain ⟨hxO, hxle⟩ := Finset.mem_filter.mp hx
        have hux := hu_le x hxO
        have hu1 : 1 ≤ u := (Finset.mem_Icc.mp (hBsub (Finset.mem_filter.mp hu_in).1)).1
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hxle⟩,
          (Finset.mem_filter.mp hxO).2⟩
      have hlow_le : Bodd_low.card ≤ (n / 2 - (u - 1) + 1) / 2 :=
        le_trans (Finset.card_le_card hlow_sub) (card_filter_odd_Ioc (u - 1) (n / 2)).2
      omega

/- ### Half 4B: Disjoint-Pair Exceptional Counting Inside Structured Containers -/

noncomputable def avoidPairs (U : Finset ℕ) (P : Finset (ℕ × ℕ)) : Finset (Finset ℕ) :=
  U.powerset.filter fun A : Finset ℕ ↦ ∀ p ∈ P, ¬(p.1 ∈ A ∧ p.2 ∈ A)

lemma mem_avoidPairs {U : Finset ℕ} {P : Finset (ℕ × ℕ)} {A : Finset ℕ} :
    A ∈ avoidPairs U P ↔ A ⊆ U ∧ ∀ p ∈ P, ¬(p.1 ∈ A ∧ p.2 ∈ A) := by
  simp only [avoidPairs, Finset.mem_filter, Finset.mem_powerset]

lemma card_subsets_avoiding_pairs (U : Finset ℕ) (P : Finset (ℕ × ℕ))
    (hPsub : ∀ p ∈ P, p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 ≠ p.2)
    (hPdisj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) :
    ((avoidPairs U P).card : ℝ) ≤
      (3 / 4 : ℝ) ^ P.card * (2 : ℝ) ^ U.card := by
  induction P using Finset.induction_on generalizing U with
  | empty =>
    simp [avoidPairs, Finset.card_powerset]
  | insert p P' hp ih =>
    rcases p with ⟨x, y⟩
    have hxy0 := hPsub (x, y) (Finset.mem_insert_self _ _)
    dsimp only at hxy0
    obtain ⟨hxU, hyU, hxy⟩ := hxy0
    let U' := (U.erase x).erase y
    have hU'card : U'.card + 2 = U.card := by
      have h1 : y ∈ U.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hyU⟩
      have c1 : U'.card + 1 = (U.erase x).card := Finset.card_erase_add_one h1
      have c2 : (U.erase x).card + 1 = U.card := Finset.card_erase_add_one hxU
      omega
    have hP'sub : ∀ q ∈ P', q.1 ∈ U' ∧ q.2 ∈ U' ∧ q.1 ≠ q.2 := by
      intro q hq
      have hqsub := hPsub q (Finset.mem_insert_of_mem hq)
      have hne : (x, y) ≠ q := fun heq ↦ hp (heq ▸ hq)
      have hdis := hPdisj (x, y) (Finset.mem_insert_self _ _) q (Finset.mem_insert_of_mem hq) hne
      refine ⟨Finset.mem_erase.mpr ⟨hdis.2.2.1.symm, Finset.mem_erase.mpr ⟨hdis.1.symm, hqsub.1⟩⟩,
              Finset.mem_erase.mpr ⟨hdis.2.2.2.symm, Finset.mem_erase.mpr ⟨hdis.2.1.symm, hqsub.2.1⟩⟩,
              hqsub.2.2⟩
    have hP'disj : ∀ q1 ∈ P', ∀ q2 ∈ P', q1 ≠ q2 →
        q1.1 ≠ q2.1 ∧ q1.1 ≠ q2.2 ∧ q1.2 ≠ q2.1 ∧ q1.2 ≠ q2.2 :=
      fun q1 h1 q2 h2 ↦ hPdisj q1 (Finset.mem_insert_of_mem h1) q2 (Finset.mem_insert_of_mem h2)
    let S := avoidPairs U (insert (x, y) P')
    let S' := avoidPairs U' P'
    have hcard_S : S.card ≤ 3 * S'.card := by
      let f : Finset ℕ → Fin 3 × Finset ℕ := fun A ↦
        (if x ∈ A then 1 else if y ∈ A then 2 else 0, (A.erase x).erase y)
      let T : Finset (Fin 3 × Finset ℕ) := (Finset.univ : Finset (Fin 3)) ×ˢ S'
      have hmaps : Set.MapsTo f (S : Set (Finset ℕ)) (T : Set (Fin 3 × Finset ℕ)) := by
        intro A hA
        rw [Finset.mem_coe] at hA ⊢
        obtain ⟨hAsub, hAav⟩ := mem_avoidPairs.mp hA
        dsimp only [T, S', f]
        rw [Finset.mem_product, mem_avoidPairs]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · intro z hz
          obtain ⟨hzy, hz1⟩ := Finset.mem_erase.mp hz
          obtain ⟨hzx, hzA⟩ := Finset.mem_erase.mp hz1
          exact Finset.mem_erase.mpr ⟨hzy, Finset.mem_erase.mpr ⟨hzx, hAsub hzA⟩⟩
        · intro q hq ⟨h1, h2⟩
          exact hAav q (Finset.mem_insert_of_mem hq)
            ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h1),
             Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h2)⟩
      have hinj : Set.InjOn f (S : Set (Finset ℕ)) := by
        intro A hA B hB heq
        rw [Finset.mem_coe] at hA hB
        obtain ⟨_, hAav⟩ := mem_avoidPairs.mp hA
        obtain ⟨_, hBav⟩ := mem_avoidPairs.mp hB
        have hAxy : ¬(x ∈ A ∧ y ∈ A) := hAav (x, y) (Finset.mem_insert_self _ _)
        have hBxy : ¬(x ∈ B ∧ y ∈ B) := hBav (x, y) (Finset.mem_insert_self _ _)
        have h1 : (if x ∈ A then (1 : Fin 3) else if y ∈ A then 2 else 0) =
            (if x ∈ B then 1 else if y ∈ B then 2 else 0) := congr_arg Prod.fst heq
        have h2 : (A.erase x).erase y = (B.erase x).erase y := congr_arg Prod.snd heq
        have hxAB : x ∈ A ↔ x ∈ B := by
          by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;>
            by_cases hyA : y ∈ A <;> by_cases hyB : y ∈ B <;>
            simp only [hxA, hxB, hyA, hyB, ↓reduceIte] at h1 <;>
            first | exact absurd h1 (by decide) | tauto
        have hyAB : y ∈ A ↔ y ∈ B := by
          by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;>
            by_cases hyA : y ∈ A <;> by_cases hyB : y ∈ B <;>
            simp only [hxA, hxB, hyA, hyB, ↓reduceIte] at h1 <;>
            first | exact absurd h1 (by decide) | tauto
        apply Finset.ext; intro z
        by_cases hzx : z = x
        · subst hzx; exact hxAB
        · by_cases hzy : z = y
          · subst hzy; exact hyAB
          · have := Finset.ext_iff.mp h2 z
            simpa [Finset.mem_erase, hzx, hzy] using this
      have h := Finset.card_le_card_of_injOn f hmaps hinj
      simpa [T, Finset.card_product, Fintype.card_fin] using h
    have hih := ih U' hP'sub hP'disj
    have hcard_S' : (S.card : ℝ) ≤ 3 * (S'.card : ℝ) := by exact_mod_cast hcard_S
    rw [Finset.card_insert_of_notMem hp, pow_succ]
    have h2U : (2 : ℝ) ^ U.card = 4 * (2 : ℝ) ^ U'.card := by
      rw [← hU'card, pow_add]; ring
    rw [h2U]
    calc (S.card : ℝ) ≤ 3 * (S'.card : ℝ) := hcard_S'
      _ ≤ 3 * ((3 / 4 : ℝ) ^ P'.card * (2 : ℝ) ^ U'.card) :=
          mul_le_mul_of_nonneg_left hih (by norm_num)
      _ = (3 / 4 : ℝ) ^ P'.card * (3 / 4 : ℝ) * (4 * (2 : ℝ) ^ U'.card) := by ring

/-- For any even `e ∈ [1, n]`, there are at least `n / 8 - 2` pairwise disjoint pairs in `oddSet n`
    that cannot both lie in a sum-free set containing `e`. -/
lemma exists_disj_pairs_odd (n e : ℕ) (he : e ∈ Finset.Icc 1 n) (hev : Even e) :
    ∃ P : Finset (ℕ × ℕ),
      n / 8 ≤ P.card + 2 ∧
      (∀ p ∈ P, p.1 ∈ oddSet n ∧ p.2 ∈ oddSet n ∧ p.1 ≠ p.2 ∧
        (p.1 + e = p.2 ∨ p.1 + p.2 = e)) ∧
      (∀ p ∈ P, ∀ q ∈ P, p ≠ q → p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) := by
  have ⟨he1, hen⟩ := Finset.mem_Icc.mp he
  have he2 : 2 ≤ e := by obtain ⟨k, rfl⟩ := hev; omega
  by_cases hle : e ≤ n / 2
  · let S0 := ((Finset.Icc 1 (n - e)).filter (fun x ↦ Odd x ∧ (x / e) % 2 = 0))
    let S1 := ((Finset.Icc 1 (n - e)).filter (fun x ↦ Odd x ∧ (x / e) % 2 = 1))
    let P0 := S0.image (fun x ↦ (x, x + e))
    let P1 := S1.image (fun x ↦ (x, x + e))
    have hS01_sum : S0.card + S1.card = ((Finset.Icc 1 (n - e)).filter Odd).card := by
      have hdisj : Disjoint S0 S1 := by
        rw [Finset.disjoint_filter]; intro x _ h1 h2; omega
      have hunion : S0 ∪ S1 = (Finset.Icc 1 (n - e)).filter Odd := by
        ext x; simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩) <;> exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          rcases Nat.mod_two_eq_zero_or_one (x / e) with h0 | h1'
          · exact Or.inl ⟨h1, h2, h0⟩
          · exact Or.inr ⟨h1, h2, h1'⟩
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hcard_odd : (n - e) / 2 ≤ ((Finset.Icc 1 (n - e)).filter Odd).card := by
      have h := (card_filter_odd_Ioc 0 (n - e)).1
      have hI : Finset.Ioc 0 (n - e) = Finset.Icc 1 (n - e) := by ext x; simp; omega
      rw [hI, Nat.sub_zero] at h; exact h
    have hP0card : P0.card = S0.card :=
      Finset.card_image_of_injective S0 (fun x y h ↦ (Prod.mk.inj h).1)
    have hP1card : P1.card = S1.card :=
      Finset.card_image_of_injective S1 (fun x y h ↦ (Prod.mk.inj h).1)
    have hdisj_mod : ∀ (r : ℕ) (S : Finset ℕ),
        (∀ x ∈ S, (x / e) % 2 = r) →
        ∀ p ∈ S.image (fun x ↦ (x, x + e)), ∀ q ∈ S.image (fun x ↦ (x, x + e)), p ≠ q →
          p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2 := by
      intro r S hSr p hp q hq hpq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
      have hxy : x ≠ y := fun h ↦ hpq (by subst h; rfl)
      have hrx := hSr x hx; have hry := hSr y hy
      have hdiv_add : ∀ z : ℕ, ((z + e) / e) % 2 ≠ r → z + e ≠ x ∧ z + e ≠ y := by
        intro z hz; exact ⟨fun h ↦ hz (by rw [h, hrx]), fun h ↦ hz (by rw [h, hry])⟩
      have hxe : ((x + e) / e) % 2 ≠ r := by
        rw [Nat.add_div_right x (by omega)]; omega
      have hye : ((y + e) / e) % 2 ≠ r := by
        rw [Nat.add_div_right y (by omega)]; omega
      refine ⟨hxy, ?_, ?_, by omega⟩
      · intro h; dsimp only at h; exact hye (by rw [← h, hrx])
      · intro h; dsimp only at h; exact hxe (by rw [h, hry])
    have hsub_props : ∀ (S : Finset ℕ),
        (∀ x ∈ S, x ∈ Finset.Icc 1 (n - e) ∧ Odd x) →
        ∀ p ∈ S.image (fun x ↦ (x, x + e)),
          p.1 ∈ oddSet n ∧ p.2 ∈ oddSet n ∧ p.1 ≠ p.2 ∧ (p.1 + e = p.2 ∨ p.1 + p.2 = e) := by
      intro S hS p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hxI, hxodd⟩ := hS x hx
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hxI
      have hxe_odd : Odd (x + e) := by
        obtain ⟨kx, rfl⟩ := hxodd; obtain ⟨ke, rfl⟩ := hev; exact ⟨kx + ke, by omega⟩
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, by omega⟩, hxodd⟩,
             Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hxe_odd⟩,
             by omega, Or.inl rfl⟩
    by_cases h01 : S1.card ≤ S0.card
    · refine ⟨P0, by omega, hsub_props S0 (fun x hx ↦ ⟨(Finset.mem_filter.mp hx).1,
        (Finset.mem_filter.mp hx).2.1⟩),
        hdisj_mod 0 S0 (fun x hx ↦ (Finset.mem_filter.mp hx).2.2)⟩
    · refine ⟨P1, by omega, hsub_props S1 (fun x hx ↦ ⟨(Finset.mem_filter.mp hx).1,
        (Finset.mem_filter.mp hx).2.1⟩),
        hdisj_mod 1 S1 (fun x hx ↦ (Finset.mem_filter.mp hx).2.2)⟩
  · -- e > n / 2: pairs (x, e - x) for odd x ∈ [1, e / 2 - 1]
    let S := (Finset.Icc 1 (e / 2 - 1)).filter Odd
    let P := S.image (fun x ↦ (x, e - x))
    have hPcard : P.card = S.card :=
      Finset.card_image_of_injective S (fun x y h ↦ (Prod.mk.inj h).1)
    have hScard : (e / 2 - 1) / 2 ≤ S.card := by
      have h := (card_filter_odd_Ioc 0 (e / 2 - 1)).1
      have hI : Finset.Ioc 0 (e / 2 - 1) = Finset.Icc 1 (e / 2 - 1) := by ext x; simp; omega
      rw [hI, Nat.sub_zero] at h; exact h
    refine ⟨P, by omega, ?_, ?_⟩
    · intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hxI, hxodd⟩ := Finset.mem_filter.mp hx
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hxI
      have hex_odd : Odd (e - x) := by
        obtain ⟨kx, rfl⟩ := hxodd; obtain ⟨ke, rfl⟩ := hev; exact ⟨ke - kx - 1, by omega⟩
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, by omega⟩, hxodd⟩,
             Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hex_odd⟩,
             by omega, Or.inr (by omega)⟩
    · intro p hp q hq hpq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
      have hx2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1).2
      have hy2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hy).1).2
      have hxy : x ≠ y := fun h ↦ hpq (by subst h; rfl)
      obtain ⟨ke, rfl⟩ := hev
      refine ⟨hxy, by omega, by omega, by omega⟩

/-- For any `a ∈ [1, n / 3]`, there are at least `n / 12 - 2` pairwise disjoint pairs `(x, x + a)`
    inside `upperSet n = (n / 2, n]`. -/
lemma exists_disj_pairs_upper (n a : ℕ) (ha1 : 1 ≤ a) (ha2 : a ≤ n / 3) :
    ∃ P : Finset (ℕ × ℕ),
      n / 12 ≤ P.card + 2 ∧
      (∀ p ∈ P, p.1 ∈ upperSet n ∧ p.2 ∈ upperSet n ∧ p.1 ≠ p.2 ∧ p.1 + a = p.2) ∧
      (∀ p ∈ P, ∀ q ∈ P, p ≠ q → p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) := by
  let S0 := (Finset.Ioc (n / 2) (n - a)).filter fun x ↦ (x / a) % 2 = 0
  let S1 := (Finset.Ioc (n / 2) (n - a)).filter fun x ↦ (x / a) % 2 = 1
  let P0 := S0.image (fun x ↦ (x, x + a))
  let P1 := S1.image (fun x ↦ (x, x + a))
  have hS01 : S0.card + S1.card = (Finset.Ioc (n / 2) (n - a)).card := by
    have hdisj : Disjoint S0 S1 := by rw [Finset.disjoint_filter]; intro x _ h1 h2; omega
    have hunion : S0 ∪ S1 = Finset.Ioc (n / 2) (n - a) := by
      ext x; simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx; rcases Nat.mod_two_eq_zero_or_one (x / a) with h0 | h1
        · exact Or.inl ⟨hx, h0⟩
        · exact Or.inr ⟨hx, h1⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hIoc : (Finset.Ioc (n / 2) (n - a)).card = n - a - n / 2 := Nat.card_Ioc _ _
  have hP0card : P0.card = S0.card :=
    Finset.card_image_of_injective S0 (fun x y h ↦ (Prod.mk.inj h).1)
  have hP1card : P1.card = S1.card :=
    Finset.card_image_of_injective S1 (fun x y h ↦ (Prod.mk.inj h).1)
  have hdisj_mod : ∀ (r : ℕ) (S : Finset ℕ),
      (∀ x ∈ S, (x / a) % 2 = r) →
      ∀ p ∈ S.image (fun x ↦ (x, x + a)), ∀ q ∈ S.image (fun x ↦ (x, x + a)), p ≠ q →
        p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2 := by
    intro r S hSr p hp q hq hpq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
    have hxy : x ≠ y := fun h ↦ hpq (by subst h; rfl)
    have hrx := hSr x hx; have hry := hSr y hy
    have hxa : ((x + a) / a) % 2 ≠ r := by rw [Nat.add_div_right x (by omega)]; omega
    have hya : ((y + a) / a) % 2 ≠ r := by rw [Nat.add_div_right y (by omega)]; omega
    refine ⟨hxy, ?_, ?_, by omega⟩
    · intro h; dsimp only at h; exact hya (by rw [← h, hrx])
    · intro h; dsimp only at h; exact hxa (by rw [h, hry])
  have hsub_props : ∀ (S : Finset ℕ),
      (∀ x ∈ S, x ∈ Finset.Ioc (n / 2) (n - a)) →
      ∀ p ∈ S.image (fun x ↦ (x, x + a)),
        p.1 ∈ upperSet n ∧ p.2 ∈ upperSet n ∧ p.1 ≠ p.2 ∧ p.1 + a = p.2 := by
    intro S hS p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp (hS x hx)
    exact ⟨Finset.mem_Ioc.mpr ⟨h1, by omega⟩, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩,
      by omega, rfl⟩
  by_cases h01 : S1.card ≤ S0.card
  · refine ⟨P0, by omega, hsub_props S0 (fun x hx ↦ (Finset.mem_filter.mp hx).1),
      hdisj_mod 0 S0 (fun x hx ↦ (Finset.mem_filter.mp hx).2)⟩
  · refine ⟨P1, by omega, hsub_props S1 (fun x hx ↦ (Finset.mem_filter.mp hx).1),
      hdisj_mod 1 S1 (fun x hx ↦ (Finset.mem_filter.mp hx).2)⟩

/-- Counting exceptional sum-free subsets inside a container `C` close to `oddSet n`. -/
lemma count_except_in_near_odd (n : ℕ) (C : Finset ℕ) (hn : 1000 ≤ n)
    (hCsub : C ⊆ Finset.Icc 1 n)
    (hclose : (C \ oddSet n).card + (oddSet n \ C).card ≤ n / 100) :
    (((C.powerset.filter fun A : Finset ℕ ↦ IsSumFree (A : Set ℕ) ∧ ¬(A ⊆ oddSet n)).card : ℝ)) ≤
      (2 * n : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * n) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  let S : Finset (Finset ℕ) :=
    C.powerset.filter fun A : Finset ℕ ↦ IsSumFree (A : Set ℕ) ∧ ¬(A ⊆ oddSet n)
  let Ev := C \ oddSet n
  let Se (e : ℕ) := S.filter (e ∈ ·)
  have hcov : S ⊆ Ev.biUnion Se := by
    intro A hA
    obtain ⟨hApow, _, hnot⟩ := Finset.mem_filter.mp hA
    have hAsub : A ⊆ C := Finset.mem_powerset.mp hApow
    rw [Finset.subset_iff] at hnot
    push Not at hnot
    obtain ⟨e, heA, henot⟩ := hnot
    exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_sdiff.mpr ⟨hAsub heA, henot⟩,
      Finset.mem_filter.mpr ⟨hA, heA⟩⟩
  have heach : ∀ e ∈ Ev, ((Se e).card : ℝ) ≤
      (2 : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * n) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
    intro e he
    obtain ⟨heC, henot⟩ := Finset.mem_sdiff.mp he
    have heIcc : e ∈ Finset.Icc 1 n := hCsub heC
    have hev : Even e := Nat.not_odd_iff_even.mp fun ho ↦ henot (Finset.mem_filter.mpr ⟨heIcc, ho⟩)
    obtain ⟨P, hPcard, hPprops, hPdisj⟩ := exists_disj_pairs_odd n e heIcc hev
    let U := C ∩ oddSet n
    let P' := P.filter fun p ↦ p.1 ∈ C ∧ p.2 ∈ C
    have hP'_card : 7 * (n / 100) ≤ P'.card := by
      let bad := P.filter fun p ↦ p.1 ∉ C ∨ p.2 ∉ C
      have hbad_le : bad.card ≤ (oddSet n \ C).card := by
        refine Finset.card_le_card_of_injOn (fun p ↦ if p.1 ∉ C then p.1 else p.2) ?_ ?_
        · intro p hp
          rw [Finset.mem_coe] at hp ⊢
          obtain ⟨hpP, h1 | h2⟩ := Finset.mem_filter.mp hp
          · dsimp only; rw [if_pos h1]
            exact Finset.mem_sdiff.mpr ⟨(hPprops p hpP).1, h1⟩
          · dsimp only
            by_cases h1' : p.1 ∉ C
            · rw [if_pos h1']
              exact Finset.mem_sdiff.mpr ⟨(hPprops p hpP).1, h1'⟩
            · rw [if_neg h1']
              exact Finset.mem_sdiff.mpr ⟨(hPprops p hpP).2.1, h2⟩
        · intro p hp q hq heq
          rw [Finset.mem_coe] at hp hq
          dsimp only at heq
          by_contra hpq
          have hd := hPdisj p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 hpq
          split_ifs at heq <;> first | exact hd.1 heq | exact hd.2.1 heq | exact hd.2.2.1 heq | exact hd.2.2.2 heq
      have hpartP : P'.card + bad.card = P.card := by
        have : bad = P.filter (fun p ↦ ¬(p.1 ∈ C ∧ p.2 ∈ C)) := by
          ext p; simp only [bad, Finset.mem_filter]; tauto
        rw [this, Finset.card_filter_add_card_filter_not]
      omega
    let Uav := avoidPairs U P'
    have hSe_le : (Se e).card ≤ Ev.powerset.card * Uav.card := by
      have h1 : (Se e).card ≤ (Ev.powerset ×ˢ Uav).card := by
        refine Finset.card_le_card_of_injOn (fun A ↦ (A \ oddSet n, A ∩ oddSet n)) ?_ ?_
        · intro A hA
          rw [Finset.mem_coe] at hA ⊢
          obtain ⟨hAS, heA⟩ := Finset.mem_filter.mp hA
          obtain ⟨hApow, hAsf, _⟩ := Finset.mem_filter.mp hAS
          have hAsub : A ⊆ C := Finset.mem_powerset.mp hApow
          dsimp only [Uav]
          rw [Finset.mem_product, Finset.mem_powerset, mem_avoidPairs]
          refine ⟨Finset.sdiff_subset_sdiff hAsub Finset.Subset.rfl,
            Finset.inter_subset_inter_right hAsub, ?_⟩
          intro p hp ⟨h1, h2⟩
          have hp1A : p.1 ∈ A := (Finset.mem_inter.mp h1).1
          have hp2A : p.2 ∈ A := (Finset.mem_inter.mp h2).1
          rw [isSumFree_iff] at hAsf
          rcases (hPprops p (Finset.mem_filter.mp hp).1).2.2.2 with hs | hs
          · exact hAsf p.1 (Finset.mem_coe.mpr hp1A) e (Finset.mem_coe.mpr heA)
              (by rw [hs]; exact Finset.mem_coe.mpr hp2A)
          · exact hAsf p.1 (Finset.mem_coe.mpr hp1A) p.2 (Finset.mem_coe.mpr hp2A)
              (by rw [hs]; exact Finset.mem_coe.mpr heA)
        · intro A _ B _ heq
          have h1 : A \ oddSet n = B \ oddSet n := congr_arg Prod.fst heq
          have h2 : A ∩ oddSet n = B ∩ oddSet n := congr_arg Prod.snd heq
          rw [← Finset.sdiff_union_inter A (oddSet n), ← Finset.sdiff_union_inter B (oddSet n), h1, h2]
      simpa [Finset.card_product] using h1
    have hUav_le : (Uav.card : ℝ) ≤ (3 / 4 : ℝ) ^ P'.card * (2 : ℝ) ^ U.card := by
      refine card_subsets_avoiding_pairs U P' ?_ ?_
      · intro p hp
        obtain ⟨hpP, h1, h2⟩ := Finset.mem_filter.mp hp
        have hpr := hPprops p hpP
        exact ⟨Finset.mem_inter.mpr ⟨h1, hpr.1⟩, Finset.mem_inter.mpr ⟨h2, hpr.2.1⟩, hpr.2.2.1⟩
      · intro p hp q hq
        exact hPdisj p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
    have hUcard : U.card ≤ (n + 1) / 2 := by
      calc U.card ≤ (oddSet n).card := Finset.card_le_card Finset.inter_subset_right
        _ ≤ (n + 1) / 2 := by
            have := (card_filter_odd_Ioc 0 n).2
            have hI : Finset.Ioc 0 n = Finset.Icc 1 n := by ext x; simp; omega
            rw [hI, Nat.sub_zero] at this; exact this
    have hEvcard : Ev.card ≤ n / 100 := by dsimp only [Ev]; omega
    set q := n / 100
    have hSe_real : ((Se e).card : ℝ) ≤ (2 : ℝ) ^ Ev.card * (Uav.card : ℝ) := by
      have h' : ((Se e).card : ℝ) ≤ ((Ev.powerset.card * Uav.card : ℕ) : ℝ) := by exact_mod_cast hSe_le
      rw [Nat.cast_mul, Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat] at h'
      exact h'
    have hU2 : (2 : ℝ) ^ U.card ≤ (2 : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have h2 : 2 * U.card ≤ n + 1 := by omega
      have h2' : 2 * (U.card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast h2
      linarith
    have hfactor : (2 : ℝ) ^ Ev.card * (3 / 4 : ℝ) ^ P'.card * (2 : ℝ) ^ (1 / 2 : ℝ) ≤
        (2 : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ)) := by
      have h1 : (2 : ℝ) ^ Ev.card ≤ (2 : ℝ) ^ q := pow_le_pow_right₀ (by norm_num) hEvcard
      have h2 : (3 / 4 : ℝ) ^ P'.card ≤ (3 / 4 : ℝ) ^ (7 * q) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hP'_card
      have hbase : (2 : ℝ) * (3 / 4 : ℝ) ^ 7 ≤ (1 / 3 : ℝ) := by norm_num
      have h3 : (2 : ℝ) ^ q * (3 / 4 : ℝ) ^ (7 * q) ≤ (1 / 3 : ℝ) ^ q := by
        rw [pow_mul, ← mul_pow]
        exact pow_le_pow_left₀ (by positivity) hbase q
      have hq10 : 10 ≤ q := by omega
      have h23 : (2 / 3 : ℝ) ^ q ≤ (1 / 4 : ℝ) := by
        calc (2 / 3 : ℝ) ^ q ≤ (2 / 3 : ℝ) ^ 10 :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) hq10
          _ ≤ 1 / 4 := by norm_num
      have h13 : (1 / 3 : ℝ) ^ q ≤ (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ q := by
        have : (1 / 3 : ℝ) ^ q = (2 / 3 : ℝ) ^ q * (1 / 2 : ℝ) ^ q := by rw [← mul_pow]; norm_num
        rw [this]
        exact mul_le_mul_of_nonneg_right h23 (by positivity)
      have hhalf : (1 / 2 : ℝ) ^ q ≤ 2 * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ)) := by
        rw [one_div, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
        have h21 : 2 * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ)) =
            (2 : ℝ) ^ (1 + -(1 / 100 : ℝ) * (n : ℝ)) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one]
        rw [h21]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hdiv : n ≤ 100 * q + 99 := by omega
        have hdiv' : (n : ℝ) ≤ 100 * (q : ℝ) + 99 := by exact_mod_cast hdiv
        linarith
      have hsqrt2 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
        have : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        simpa using this
      have hprod : (2 : ℝ) ^ Ev.card * (3 / 4 : ℝ) ^ P'.card ≤ (1 / 3 : ℝ) ^ q :=
        le_trans (mul_le_mul h1 h2 (by positivity) (by positivity)) h3
      have hprod2 : (2 : ℝ) ^ Ev.card * (3 / 4 : ℝ) ^ P'.card ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ)) := by
        calc (2 : ℝ) ^ Ev.card * (3 / 4 : ℝ) ^ P'.card
            ≤ (1 / 3 : ℝ) ^ q := hprod
          _ ≤ (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ q := h13
          _ ≤ (1 / 4 : ℝ) * (2 * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ))) :=
              mul_le_mul_of_nonneg_left hhalf (by norm_num)
          _ = (1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ)) := by ring
      calc (2 : ℝ) ^ Ev.card * (3 / 4 : ℝ) ^ P'.card * (2 : ℝ) ^ (1 / 2 : ℝ)
          ≤ ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ))) * 2 :=
            mul_le_mul hprod2 hsqrt2 (by positivity) (by positivity)
        _ = (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ)) := by ring
        _ ≤ 2 * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ)) := by
            linarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-(1 / 100 : ℝ) * (n : ℝ))]
    calc ((Se e).card : ℝ)
        ≤ (2 : ℝ) ^ Ev.card * ((3 / 4 : ℝ) ^ P'.card * (2 : ℝ) ^ U.card) :=
          le_trans hSe_real (mul_le_mul_of_nonneg_left hUav_le (by positivity))
      _ ≤ (2 : ℝ) ^ Ev.card * ((3 / 4 : ℝ) ^ P'.card * ((2 : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU2 (by positivity)) (by positivity)
      _ = ((2 : ℝ) ^ Ev.card * (3 / 4 : ℝ) ^ P'.card * (2 : ℝ) ^ (1 / 2 : ℝ)) * (2 : ℝ) ^ ((n : ℝ) / 2) := by ring
      _ ≤ (2 * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ))) * (2 : ℝ) ^ ((n : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hfactor (by positivity)
  have hS_le : (S.card : ℝ) ≤ ∑ e ∈ Ev, ((Se e).card : ℝ) := by
    have : S.card ≤ ∑ e ∈ Ev, (Se e).card :=
      le_trans (Finset.card_le_card hcov) Finset.card_biUnion_le
    exact_mod_cast this
  have hEv_le_n : (Ev.card : ℝ) ≤ (n : ℝ) := by
    have : Ev.card ≤ n := by
      calc Ev.card ≤ C.card := Finset.card_le_card Finset.sdiff_subset
        _ ≤ (Finset.Icc 1 n).card := Finset.card_le_card hCsub
        _ = n := by simp
    exact_mod_cast this
  calc (S.card : ℝ)
      ≤ ∑ e ∈ Ev, ((Se e).card : ℝ) := hS_le
    _ ≤ ∑ _e ∈ Ev, ((2 : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * n) * (2 : ℝ) ^ ((n : ℝ) / 2)) :=
        Finset.sum_le_sum heach
    _ = (Ev.card : ℝ) * ((2 : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * n) * (2 : ℝ) ^ ((n : ℝ) / 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) * ((2 : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * n) * (2 : ℝ) ^ ((n : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hEv_le_n (by positivity)
    _ = (2 * n : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * n) * (2 : ℝ) ^ ((n : ℝ) / 2) := by ring

/-- Counting exceptional sum-free subsets inside a container `C` close to `upperSet n = (n/2, n]`. -/
lemma count_except_in_near_upper (n : ℕ) (C : Finset ℕ) (hn : 1000 ≤ n)
    (hCsub : C ⊆ Finset.Icc 1 n)
    (hclose : (C \ upperSet n).card + (upperSet n \ C).card ≤ n / 100) :
    (((C.powerset.filter fun A : Finset ℕ ↦ IsSumFree (A : Set ℕ) ∧ ¬(∀ x ∈ A, n / 3 < x)).card : ℝ)) ≤
      (2 * n : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * n) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  let S : Finset (Finset ℕ) :=
    C.powerset.filter fun A : Finset ℕ ↦ IsSumFree (A : Set ℕ) ∧ ¬(∀ x ∈ A, n / 3 < x)
  let Low := C.filter (· ≤ n / 3)
  let Sa (a : ℕ) := S.filter (a ∈ ·)
  have hcov : S ⊆ Low.biUnion Sa := by
    intro A hA
    obtain ⟨hApow, _, hnot⟩ := Finset.mem_filter.mp hA
    have hAsub : A ⊆ C := Finset.mem_powerset.mp hApow
    push Not at hnot
    obtain ⟨a, haA, hale⟩ := hnot
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_filter.mpr ⟨hAsub haA, hale⟩,
      Finset.mem_filter.mpr ⟨hA, haA⟩⟩
  have heach : ∀ a ∈ Low, ((Sa a).card : ℝ) ≤
      (2 : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * n) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
    intro a ha
    obtain ⟨haC, hale⟩ := Finset.mem_filter.mp ha
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (hCsub haC)).1
    obtain ⟨P, hPcard, hPprops, hPdisj⟩ := exists_disj_pairs_upper n a ha1 hale
    let U := C ∩ upperSet n
    let Rem := C \ upperSet n
    let P' := P.filter fun p ↦ p.1 ∈ C ∧ p.2 ∈ C
    have hP'_card : 7 * (n / 100) ≤ P'.card := by
      let bad := P.filter fun p ↦ p.1 ∉ C ∨ p.2 ∉ C
      have hbad_le : bad.card ≤ (upperSet n \ C).card := by
        refine Finset.card_le_card_of_injOn (fun p ↦ if p.1 ∉ C then p.1 else p.2) ?_ ?_
        · intro p hp
          rw [Finset.mem_coe] at hp ⊢
          obtain ⟨hpP, h1 | h2⟩ := Finset.mem_filter.mp hp
          · dsimp only; rw [if_pos h1]
            exact Finset.mem_sdiff.mpr ⟨(hPprops p hpP).1, h1⟩
          · dsimp only
            by_cases h1' : p.1 ∉ C
            · rw [if_pos h1']
              exact Finset.mem_sdiff.mpr ⟨(hPprops p hpP).1, h1'⟩
            · rw [if_neg h1']
              exact Finset.mem_sdiff.mpr ⟨(hPprops p hpP).2.1, h2⟩
        · intro p hp q hq heq
          rw [Finset.mem_coe] at hp hq
          dsimp only at heq
          by_contra hpq
          have hd := hPdisj p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 hpq
          split_ifs at heq <;> first | exact hd.1 heq | exact hd.2.1 heq | exact hd.2.2.1 heq | exact hd.2.2.2 heq
      have hpartP : P'.card + bad.card = P.card := by
        have : bad = P.filter (fun p ↦ ¬(p.1 ∈ C ∧ p.2 ∈ C)) := by
          ext p; simp only [bad, Finset.mem_filter]; tauto
        rw [this, Finset.card_filter_add_card_filter_not]
      omega
    let Uav := avoidPairs U P'
    have hSa_le : (Sa a).card ≤ Rem.powerset.card * Uav.card := by
      have h1 : (Sa a).card ≤ (Rem.powerset ×ˢ Uav).card := by
        refine Finset.card_le_card_of_injOn (fun A ↦ (A \ upperSet n, A ∩ upperSet n)) ?_ ?_
        · intro A hA
          rw [Finset.mem_coe] at hA ⊢
          obtain ⟨hAS, haA⟩ := Finset.mem_filter.mp hA
          obtain ⟨hApow, hAsf, _⟩ := Finset.mem_filter.mp hAS
          have hAsub : A ⊆ C := Finset.mem_powerset.mp hApow
          dsimp only [Uav]
          rw [Finset.mem_product, Finset.mem_powerset, mem_avoidPairs]
          refine ⟨Finset.sdiff_subset_sdiff hAsub Finset.Subset.rfl,
            Finset.inter_subset_inter_right hAsub, ?_⟩
          intro p hp ⟨h1, h2⟩
          have hp1A : p.1 ∈ A := (Finset.mem_inter.mp h1).1
          have hp2A : p.2 ∈ A := (Finset.mem_inter.mp h2).1
          rw [isSumFree_iff] at hAsf
          exact hAsf p.1 (Finset.mem_coe.mpr hp1A) a (Finset.mem_coe.mpr haA)
            (by rw [(hPprops p (Finset.mem_filter.mp hp).1).2.2.2]; exact Finset.mem_coe.mpr hp2A)
        · intro A _ B _ heq
          have h1 : A \ upperSet n = B \ upperSet n := congr_arg Prod.fst heq
          have h2 : A ∩ upperSet n = B ∩ upperSet n := congr_arg Prod.snd heq
          rw [← Finset.sdiff_union_inter A (upperSet n), ← Finset.sdiff_union_inter B (upperSet n), h1, h2]
      simpa [Finset.card_product] using h1
    have hUav_le : (Uav.card : ℝ) ≤ (3 / 4 : ℝ) ^ P'.card * (2 : ℝ) ^ U.card := by
      refine card_subsets_avoiding_pairs U P' ?_ ?_
      · intro p hp
        obtain ⟨hpP, h1, h2⟩ := Finset.mem_filter.mp hp
        have hpr := hPprops p hpP
        exact ⟨Finset.mem_inter.mpr ⟨h1, hpr.1⟩, Finset.mem_inter.mpr ⟨h2, hpr.2.1⟩, hpr.2.2.1⟩
      · intro p hp q hq
        exact hPdisj p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
    have hUcard : U.card ≤ (n + 1) / 2 := by
      calc U.card ≤ (upperSet n).card := Finset.card_le_card Finset.inter_subset_right
        _ = n - n / 2 := Nat.card_Ioc _ _
        _ ≤ (n + 1) / 2 := by omega
    have hRemcard : Rem.card ≤ n / 100 := by dsimp only [Rem]; omega
    set q := n / 100
    have hSa_real : ((Sa a).card : ℝ) ≤ (2 : ℝ) ^ Rem.card * (Uav.card : ℝ) := by
      have h' : ((Sa a).card : ℝ) ≤ ((Rem.powerset.card * Uav.card : ℕ) : ℝ) := by exact_mod_cast hSa_le
      rw [Nat.cast_mul, Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat] at h'
      exact h'
    have hU2 : (2 : ℝ) ^ U.card ≤ (2 : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have h2 : 2 * U.card ≤ n + 1 := by omega
      have h2' : 2 * (U.card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast h2
      linarith
    have hfactor : (2 : ℝ) ^ Rem.card * (3 / 4 : ℝ) ^ P'.card * (2 : ℝ) ^ (1 / 2 : ℝ) ≤
        (2 : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ)) := by
      have h1 : (2 : ℝ) ^ Rem.card ≤ (2 : ℝ) ^ q := pow_le_pow_right₀ (by norm_num) hRemcard
      have h2 : (3 / 4 : ℝ) ^ P'.card ≤ (3 / 4 : ℝ) ^ (7 * q) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hP'_card
      have hbase : (2 : ℝ) * (3 / 4 : ℝ) ^ 7 ≤ (1 / 3 : ℝ) := by norm_num
      have h3 : (2 : ℝ) ^ q * (3 / 4 : ℝ) ^ (7 * q) ≤ (1 / 3 : ℝ) ^ q := by
        rw [pow_mul, ← mul_pow]
        exact pow_le_pow_left₀ (by positivity) hbase q
      have hq10 : 10 ≤ q := by omega
      have h23 : (2 / 3 : ℝ) ^ q ≤ (1 / 4 : ℝ) := by
        calc (2 / 3 : ℝ) ^ q ≤ (2 / 3 : ℝ) ^ 10 :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) hq10
          _ ≤ 1 / 4 := by norm_num
      have h13 : (1 / 3 : ℝ) ^ q ≤ (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ q := by
        have : (1 / 3 : ℝ) ^ q = (2 / 3 : ℝ) ^ q * (1 / 2 : ℝ) ^ q := by rw [← mul_pow]; norm_num
        rw [this]
        exact mul_le_mul_of_nonneg_right h23 (by positivity)
      have hhalf : (1 / 2 : ℝ) ^ q ≤ 2 * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ)) := by
        rw [one_div, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
        have h21 : 2 * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ)) =
            (2 : ℝ) ^ (1 + -(1 / 100 : ℝ) * (n : ℝ)) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one]
        rw [h21]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hdiv : n ≤ 100 * q + 99 := by omega
        have hdiv' : (n : ℝ) ≤ 100 * (q : ℝ) + 99 := by exact_mod_cast hdiv
        linarith
      have hsqrt2 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
        have : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        simpa using this
      have hprod : (2 : ℝ) ^ Rem.card * (3 / 4 : ℝ) ^ P'.card ≤ (1 / 3 : ℝ) ^ q :=
        le_trans (mul_le_mul h1 h2 (by positivity) (by positivity)) h3
      have hprod2 : (2 : ℝ) ^ Rem.card * (3 / 4 : ℝ) ^ P'.card ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ)) := by
        calc (2 : ℝ) ^ Rem.card * (3 / 4 : ℝ) ^ P'.card
            ≤ (1 / 3 : ℝ) ^ q := hprod
          _ ≤ (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ q := h13
          _ ≤ (1 / 4 : ℝ) * (2 * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ))) :=
              mul_le_mul_of_nonneg_left hhalf (by norm_num)
          _ = (1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ)) := by ring
      calc (2 : ℝ) ^ Rem.card * (3 / 4 : ℝ) ^ P'.card * (2 : ℝ) ^ (1 / 2 : ℝ)
          ≤ ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ))) * 2 :=
            mul_le_mul hprod2 hsqrt2 (by positivity) (by positivity)
        _ = (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ)) := by ring
        _ ≤ 2 * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ)) := by
            linarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-(1 / 100 : ℝ) * (n : ℝ))]
    calc ((Sa a).card : ℝ)
        ≤ (2 : ℝ) ^ Rem.card * ((3 / 4 : ℝ) ^ P'.card * (2 : ℝ) ^ U.card) :=
          le_trans hSa_real (mul_le_mul_of_nonneg_left hUav_le (by positivity))
      _ ≤ (2 : ℝ) ^ Rem.card * ((3 / 4 : ℝ) ^ P'.card * ((2 : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU2 (by positivity)) (by positivity)
      _ = ((2 : ℝ) ^ Rem.card * (3 / 4 : ℝ) ^ P'.card * (2 : ℝ) ^ (1 / 2 : ℝ)) * (2 : ℝ) ^ ((n : ℝ) / 2) := by ring
      _ ≤ (2 * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ))) * (2 : ℝ) ^ ((n : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hfactor (by positivity)
  have hS_le : (S.card : ℝ) ≤ ∑ a ∈ Low, ((Sa a).card : ℝ) := by
    have : S.card ≤ ∑ a ∈ Low, (Sa a).card :=
      le_trans (Finset.card_le_card hcov) Finset.card_biUnion_le
    exact_mod_cast this
  have hLow_le_n : (Low.card : ℝ) ≤ (n : ℝ) := by
    have : Low.card ≤ n := by
      calc Low.card ≤ C.card := Finset.card_le_card (Finset.filter_subset _ _)
        _ ≤ (Finset.Icc 1 n).card := Finset.card_le_card hCsub
        _ = n := by simp
    exact_mod_cast this
  calc (S.card : ℝ)
      ≤ ∑ a ∈ Low, ((Sa a).card : ℝ) := hS_le
    _ ≤ ∑ _a ∈ Low, ((2 : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * n) * (2 : ℝ) ^ ((n : ℝ) / 2)) :=
        Finset.sum_le_sum heach
    _ = (Low.card : ℝ) * ((2 : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * n) * (2 : ℝ) ^ ((n : ℝ) / 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) * ((2 : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * n) * (2 : ℝ) ^ ((n : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hLow_le_n (by positivity)
    _ = (2 * n : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * n) * (2 : ℝ) ^ ((n : ℝ) / 2) := by ring

end Mod4

section Glue
open Filter Real Finset
open scoped Classical

/- ### Final Assembly: Vanishing of Exceptional Family and Main Asymptotic Theorem -/

lemma tendsto_exceptFamily_zero :
    Tendsto (fun n : ℕ ↦ ((exceptFamily n).card : ℝ) / (2 : ℝ) ^ ((n : ℝ) / 2))
      atTop (nhds 0) := by
  obtain ⟨ε_rem, hε_rem_pos, hrem⟩ := sumFree_removal (1 / 100000 : ℝ) (by norm_num)
  obtain ⟨N₁, hcont⟩ :=
    container_theorem (ε_rem / 2) (1 / 200000 : ℝ) (by positivity) (by norm_num)
  set N₀ : ℕ := max N₁ 100000
  have hbase_lt : (2 : ℝ) ^ (-(1 / 200000 : ℝ)) < 1 := by
    have : (2 : ℝ) ^ (-(1 / 200000 : ℝ)) < (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
    simpa using this
  have hdom : Tendsto (fun n : ℕ ↦ (2 * (n : ℝ)) * ((2 : ℝ) ^ (-(1 / 200000 : ℝ))) ^ n)
      atTop (nhds 0) := by
    have hsum : Summable (fun n : ℕ ↦ (n : ℝ) * ((2 : ℝ) ^ (-(1 / 200000 : ℝ))) ^ n) := by
      have h := summable_pow_mul_geometric_of_norm_lt_one 1
        (r := (2 : ℝ) ^ (-(1 / 200000 : ℝ)))
        (by rw [Real.norm_of_nonneg (by positivity)]; exact hbase_lt)
      simpa only [pow_one] using h
    have h0 := hsum.tendsto_atTop_zero.const_mul (2 : ℝ)
    simpa [mul_assoc] using h0
  refine squeeze_zero' (Eventually.of_forall fun n ↦ by positivity) ?_ hdom
  filter_upwards [Filter.eventually_ge_atTop N₀] with n hn
  have hnN1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn100k : 100000 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨F, hFcard, hFcov, hFprop⟩ := hcont n hnN1
  have hcov_exc : exceptFamily n ⊆ F.biUnion (fun C ↦ (exceptFamily n).filter (· ⊆ C)) := by
    intro A hA
    have hAsf : A ∈ sfFamily n := (Finset.mem_sdiff.mp hA).1
    obtain ⟨C, hCF, hAC⟩ := hFcov A hAsf
    exact Finset.mem_biUnion.mpr ⟨C, hCF, Finset.mem_filter.mpr ⟨hA, hAC⟩⟩
  have heachC : ∀ C ∈ F,
      (((exceptFamily n).filter (· ⊆ C)).card : ℝ) ≤
        (2 * (n : ℝ)) * (2 : ℝ) ^ (-(1 / 100000 : ℝ) * (n : ℝ)) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
    intro C hCF
    obtain ⟨hCsub, hCtri⟩ := hFprop C hCF
    by_cases hsmall : n / 50000 < n + 1 - 2 * C.card
    · -- Small container: 2^|C| already exponentially smaller than 2^(n/2)!
      have hsub : (exceptFamily n).filter (· ⊆ C) ⊆ C.powerset := fun A hA ↦
        Finset.mem_powerset.mpr (Finset.mem_filter.mp hA).2
      have hcard_le : (((exceptFamily n).filter (· ⊆ C)).card : ℝ) ≤ (2 : ℝ) ^ (C.card : ℝ) := by
        rw [Real.rpow_natCast]
        have h1 : ((exceptFamily n).filter (· ⊆ C)).card ≤ 2 ^ C.card := by
          rw [← Finset.card_powerset]; exact Finset.card_le_card hsub
        exact_mod_cast h1
      have hC_ub : (C.card : ℝ) ≤ (n : ℝ) / 2 - (1 / 100000 : ℝ) * (n : ℝ) + 1 := by
        have hnat : 2 * C.card + n / 50000 ≤ n := by omega
        have hdiv : n ≤ 50000 * (n / 50000) + 49999 := by omega
        have hnat' : 2 * (C.card : ℝ) + ((n / 50000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnat
        have hdiv' : (n : ℝ) ≤ 50000 * ((n / 50000 : ℕ) : ℝ) + 49999 := by exact_mod_cast hdiv
        linarith
      have h2pow : (2 : ℝ) ^ (C.card : ℝ) ≤
          2 * (2 : ℝ) ^ (-(1 / 100000 : ℝ) * (n : ℝ)) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
        calc (2 : ℝ) ^ (C.card : ℝ)
            ≤ (2 : ℝ) ^ ((n : ℝ) / 2 - (1 / 100000 : ℝ) * (n : ℝ) + 1) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hC_ub
          _ = (2 : ℝ) ^ ((1 : ℝ) + (-(1 / 100000 : ℝ) * (n : ℝ) + (n : ℝ) / 2)) := by
              congr 1; ring
          _ = 2 * (2 : ℝ) ^ (-(1 / 100000 : ℝ) * (n : ℝ)) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
              rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_one]; ring
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
      calc (((exceptFamily n).filter (· ⊆ C)).card : ℝ)
          ≤ 2 * (2 : ℝ) ^ (-(1 / 100000 : ℝ) * (n : ℝ)) * (2 : ℝ) ^ ((n : ℝ) / 2) :=
            le_trans hcard_le h2pow
        _ ≤ (2 * (n : ℝ)) * (2 : ℝ) ^ (-(1 / 100000 : ℝ) * (n : ℝ)) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
            have hpos : 0 ≤ (2 : ℝ) ^ (-(1 / 100000 : ℝ) * (n : ℝ)) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
              positivity
            nlinarith
    · -- Large container: remove ≤ n/100000 elements to get sum-free B ⊆ C, apply stability!
      have htri_lt : ((schurTriples C).card : ℝ) < ε_rem * (n : ℝ) ^ 2 := by
        have hn2pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
        linarith [mul_lt_mul_of_pos_right (show ε_rem / 2 < ε_rem by linarith) hn2pos]
      obtain ⟨B, hBC, hBsf, hCB_le⟩ := hrem n C (by omega) hCsub htri_lt
      have hCB_nat : (C \ B).card ≤ n / 100000 := by
        have hmul : ((100000 * (C \ B).card : ℕ) : ℝ) ≤ (n : ℝ) := by
          push_cast; linarith
        have hmul_nat : 100000 * (C \ B).card ≤ n := by exact_mod_cast hmul
        omega
      have hB_card_eq : (C \ B).card + B.card = C.card := Finset.card_sdiff_add_card_eq_card hBC
      have hB_gap : n + 1 - 2 * B.card ≤ n / 25000 := by omega
      have hstab := exact_sumFree_stability n B (by omega) (hBC.trans hCsub) hBsf hB_gap
      have hexp_mon : (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ)) ≤
          (2 : ℝ) ^ (-(1 / 100000 : ℝ) * (n : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      rcases hstab with hnear_odd | hnear_upper
      · have hC_close : (C \ oddSet n).card + (oddSet n \ C).card ≤ n / 100 := by
          have h1 : C \ oddSet n ⊆ (C \ B) ∪ (B \ oddSet n) := by
            intro x hx
            obtain ⟨hxC, hxno⟩ := Finset.mem_sdiff.mp hx
            rw [Finset.mem_union]
            by_cases hxB : x ∈ B
            · exact Or.inr (Finset.mem_sdiff.mpr ⟨hxB, hxno⟩)
            · exact Or.inl (Finset.mem_sdiff.mpr ⟨hxC, hxB⟩)
          have h2 : oddSet n \ C ⊆ oddSet n \ B :=
            Finset.sdiff_subset_sdiff Finset.Subset.rfl hBC
          have c1 : (C \ oddSet n).card ≤ (C \ B).card + (B \ oddSet n).card :=
            le_trans (Finset.card_le_card h1) (Finset.card_union_le _ _)
          have c2 : (oddSet n \ C).card ≤ (oddSet n \ B).card := Finset.card_le_card h2
          omega
        have hsub : (exceptFamily n).filter (· ⊆ C) ⊆
            C.powerset.filter (fun A : Finset ℕ ↦ IsSumFree (A : Set ℕ) ∧ ¬(A ⊆ oddSet n)) := by
          intro A hA
          obtain ⟨hAexc, hAC⟩ := Finset.mem_filter.mp hA
          obtain ⟨hAsf, hAnot⟩ := Finset.mem_sdiff.mp hAexc
          have hsf : IsSumFree (A : Set ℕ) := (Finset.mem_filter.mp hAsf).2
          have hnot_odd : ¬(A ⊆ oddSet n) := fun hsub ↦
            hAnot (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hAsf, hsub⟩))
          exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hAC, hsf, hnot_odd⟩
        have hcnt := count_except_in_near_odd n C (by omega) hCsub hC_close
        calc (((exceptFamily n).filter (· ⊆ C)).card : ℝ)
            ≤ ((C.powerset.filter fun A : Finset ℕ ↦
                IsSumFree (A : Set ℕ) ∧ ¬(A ⊆ oddSet n)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card hsub
          _ ≤ (2 * (n : ℝ)) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ)) * (2 : ℝ) ^ ((n : ℝ) / 2) := hcnt
          _ ≤ (2 * (n : ℝ)) * (2 : ℝ) ^ (-(1 / 100000 : ℝ) * (n : ℝ)) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
              gcongr
      · have hC_close : (C \ upperSet n).card + (upperSet n \ C).card ≤ n / 100 := by
          have h1 : C \ upperSet n ⊆ (C \ B) ∪ (B \ upperSet n) := by
            intro x hx
            obtain ⟨hxC, hxno⟩ := Finset.mem_sdiff.mp hx
            rw [Finset.mem_union]
            by_cases hxB : x ∈ B
            · exact Or.inr (Finset.mem_sdiff.mpr ⟨hxB, hxno⟩)
            · exact Or.inl (Finset.mem_sdiff.mpr ⟨hxC, hxB⟩)
          have h2 : upperSet n \ C ⊆ upperSet n \ B :=
            Finset.sdiff_subset_sdiff Finset.Subset.rfl hBC
          have c1 : (C \ upperSet n).card ≤ (C \ B).card + (B \ upperSet n).card :=
            le_trans (Finset.card_le_card h1) (Finset.card_union_le _ _)
          have c2 : (upperSet n \ C).card ≤ (upperSet n \ B).card := Finset.card_le_card h2
          omega
        have hsub : (exceptFamily n).filter (· ⊆ C) ⊆
            C.powerset.filter (fun A : Finset ℕ ↦ IsSumFree (A : Set ℕ) ∧ ¬(∀ x ∈ A, n / 3 < x)) := by
          intro A hA
          obtain ⟨hAexc, hAC⟩ := Finset.mem_filter.mp hA
          obtain ⟨hAsf, hAnot⟩ := Finset.mem_sdiff.mp hAexc
          have hsf : IsSumFree (A : Set ℕ) := (Finset.mem_filter.mp hAsf).2
          have hnot_high : ¬(∀ x ∈ A, n / 3 < x) := fun hhi ↦
            hAnot (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hAsf, hhi⟩))
          exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hAC, hsf, hnot_high⟩
        have hcnt := count_except_in_near_upper n C (by omega) hCsub hC_close
        calc (((exceptFamily n).filter (· ⊆ C)).card : ℝ)
            ≤ ((C.powerset.filter fun A : Finset ℕ ↦
                IsSumFree (A : Set ℕ) ∧ ¬(∀ x ∈ A, n / 3 < x)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card hsub
          _ ≤ (2 * (n : ℝ)) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * (n : ℝ)) * (2 : ℝ) ^ ((n : ℝ) / 2) := hcnt
          _ ≤ (2 * (n : ℝ)) * (2 : ℝ) ^ (-(1 / 100000 : ℝ) * (n : ℝ)) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
              gcongr
  have htot : ((exceptFamily n).card : ℝ) ≤
      (F.card : ℝ) * ((2 * (n : ℝ)) * (2 : ℝ) ^ (-(1 / 100000 : ℝ) * (n : ℝ)) * (2 : ℝ) ^ ((n : ℝ) / 2)) := by
    have h1 : ((exceptFamily n).card : ℝ) ≤ ∑ C ∈ F, (((exceptFamily n).filter (· ⊆ C)).card : ℝ) := by
      have : (exceptFamily n).card ≤ ∑ C ∈ F, ((exceptFamily n).filter (· ⊆ C)).card :=
        le_trans (Finset.card_le_card hcov_exc) Finset.card_biUnion_le
      exact_mod_cast this
    calc ((exceptFamily n).card : ℝ)
        ≤ ∑ C ∈ F, (((exceptFamily n).filter (· ⊆ C)).card : ℝ) := h1
      _ ≤ ∑ _C ∈ F, ((2 * (n : ℝ)) * (2 : ℝ) ^ (-(1 / 100000 : ℝ) * (n : ℝ)) * (2 : ℝ) ^ ((n : ℝ) / 2)) :=
          Finset.sum_le_sum heachC
      _ = (F.card : ℝ) * ((2 * (n : ℝ)) * (2 : ℝ) ^ (-(1 / 100000 : ℝ) * (n : ℝ)) * (2 : ℝ) ^ ((n : ℝ) / 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hdiv_le : ((exceptFamily n).card : ℝ) / (2 : ℝ) ^ ((n : ℝ) / 2) ≤
      (F.card : ℝ) * ((2 * (n : ℝ)) * (2 : ℝ) ^ (-(1 / 100000 : ℝ) * (n : ℝ))) := by
    rw [div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)]
    linarith
  calc ((exceptFamily n).card : ℝ) / (2 : ℝ) ^ ((n : ℝ) / 2)
      ≤ (F.card : ℝ) * ((2 * (n : ℝ)) * (2 : ℝ) ^ (-(1 / 100000 : ℝ) * (n : ℝ))) := hdiv_le
    _ ≤ (2 : ℝ) ^ ((1 / 200000 : ℝ) * (n : ℝ)) *
          ((2 * (n : ℝ)) * (2 : ℝ) ^ (-(1 / 100000 : ℝ) * (n : ℝ))) :=
        mul_le_mul_of_nonneg_right hFcard (by positivity)
    _ = (2 * (n : ℝ)) * ((2 : ℝ) ^ ((1 / 200000 : ℝ) * (n : ℝ)) *
          (2 : ℝ) ^ (-(1 / 100000 : ℝ) * (n : ℝ))) := by ring
    _ = (2 * (n : ℝ)) * (2 : ℝ) ^ (-(1 / 200000 : ℝ) * (n : ℝ)) := by
        rw [← Real.rpow_add (by norm_num)]; congr 2; ring
    _ = (2 * (n : ℝ)) * ((2 : ℝ) ^ (-(1 / 200000 : ℝ))) ^ n := by
        congr 1
        rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / 200000 : ℝ))) n, ← Real.rpow_mul (by norm_num)]

end Glue

end Erdos748Asymp

theorem OMA.solution : type_of% @Erdos748.erdos_748.variants.asymptotic := by
  open Filter Real Erdos748Asymp in
  refine ⟨2 + ∑' k : ℕ, w (2 * k), 2 * Real.sqrt 2 + ∑' k : ℕ, w (2 * k + 1), ?_, ?_, ?_, ?_⟩
  · have hnonneg : 0 ≤ ∑' k : ℕ, w (2 * k) := tsum_nonneg fun k ↦ w_nonneg (2 * k)
    linarith
  · have hnonneg : 0 ≤ ∑' k : ℕ, w (2 * k + 1) := tsum_nonneg fun k ↦ w_nonneg (2 * k + 1)
    have hsq : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    linarith
  · -- Even subsequence: f (2 * m) / 2 ^ m → 2 + ∑' k, w (2 * k)
    have h2m_atTop : Tendsto (fun m : ℕ ↦ 2 * m) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]; intro b; exact ⟨b, fun m hm ↦ by omega⟩
    have hpow_even : ∀ m : ℕ, (2 : ℝ) ^ (((2 * m : ℕ) : ℝ) / 2) = (2 : ℝ) ^ m := by
      intro m; push_cast
      rw [show (2 : ℝ) * (m : ℝ) / 2 = (m : ℝ) by ring, Real.rpow_natCast]
    have hodd_even : Tendsto (fun m : ℕ ↦ ((oddFamily (2 * m)).card : ℝ) / (2 : ℝ) ^ m)
        atTop (nhds 1) := by
      have heq : (fun m : ℕ ↦ ((oddFamily (2 * m)).card : ℝ) / (2 : ℝ) ^ m) = fun _ ↦ 1 := by
        funext m
        rw [oddFamily_card, show (2 * m + 1) / 2 = m by omega, Nat.cast_pow, Nat.cast_ofNat,
          div_self (by positivity)]
      rw [heq]; exact tendsto_const_nhds
    have hhigh_even := tendsto_highFamily_even
    have hexc_even : Tendsto (fun m : ℕ ↦ ((exceptFamily (2 * m)).card : ℝ) / (2 : ℝ) ^ m)
        atTop (nhds 0) := by
      simpa only [Function.comp_def, hpow_even] using tendsto_exceptFamily_zero.comp h2m_atTop
    have hinter_even :
        Tendsto (fun m : ℕ ↦ ((oddFamily (2 * m) ∩ highFamily (2 * m)).card : ℝ) / (2 : ℝ) ^ m)
          atTop (nhds 0) := by
      simpa only [Function.comp_def, hpow_even] using tendsto_odd_inter_high_zero.comp h2m_atTop
    have hformula : ∀ m : ℕ, (Erdos748.f (2 * m) : ℝ) / (2 : ℝ) ^ m =
        ((oddFamily (2 * m)).card : ℝ) / (2 : ℝ) ^ m +
        ((highFamily (2 * m)).card : ℝ) / (2 : ℝ) ^ m +
        ((exceptFamily (2 * m)).card : ℝ) / (2 : ℝ) ^ m -
        ((oddFamily (2 * m) ∩ highFamily (2 * m)).card : ℝ) / (2 : ℝ) ^ m := by
      intro m
      have hd : (Erdos748.f (2 * m) : ℝ) + ((oddFamily (2 * m) ∩ highFamily (2 * m)).card : ℝ) =
          ((oddFamily (2 * m)).card : ℝ) + ((highFamily (2 * m)).card : ℝ) +
          ((exceptFamily (2 * m)).card : ℝ) := by exact_mod_cast card_decomp (2 * m)
      have hpos : (2 : ℝ) ^ m ≠ 0 := by positivity
      field_simp [hpos]
      linarith
    simp_rw [hformula]
    have hlim := ((hodd_even.add hhigh_even).add hexc_even).sub hinter_even
    have hval : (1 : ℝ) + (1 + ∑' k : ℕ, w (2 * k)) + 0 - 0 = 2 + ∑' k : ℕ, w (2 * k) := by ring
    rw [hval] at hlim
    exact hlim
  · -- Odd subsequence: f (2 * m + 1) / 2 ^ ((2 * m + 1) / 2) → 2 * √2 + ∑' k, w (2 * k + 1)
    have h2m1_atTop : Tendsto (fun m : ℕ ↦ 2 * m + 1) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]; intro b; exact ⟨b, fun m hm ↦ by omega⟩
    have hcast_odd : ∀ m : ℕ, ((2 * m + 1 : ℕ) : ℝ) / 2 = (2 * (m : ℝ) + 1) / 2 := by
      intro m; push_cast; ring
    have hodd_odd : Tendsto (fun m : ℕ ↦ ((oddFamily (2 * m + 1)).card : ℝ) /
        (2 : ℝ) ^ ((2 * (m : ℝ) + 1) / 2)) atTop (nhds (Real.sqrt 2)) := by
      have heq : (fun m : ℕ ↦ ((oddFamily (2 * m + 1)).card : ℝ) /
          (2 : ℝ) ^ ((2 * (m : ℝ) + 1) / 2)) = fun _ ↦ Real.sqrt 2 := by
        funext m
        rw [oddFamily_card, show (2 * m + 1 + 1) / 2 = m + 1 by omega,
          Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast (2 : ℝ) (m + 1),
          ← Real.rpow_sub (by norm_num)]
        have : ((m + 1 : ℕ) : ℝ) - (2 * (m : ℝ) + 1) / 2 = (1 / 2 : ℝ) := by push_cast; ring
        rw [this, Real.sqrt_eq_rpow]
      rw [heq]; exact tendsto_const_nhds
    have hhigh_odd := tendsto_highFamily_odd
    have hexc_odd : Tendsto (fun m : ℕ ↦ ((exceptFamily (2 * m + 1)).card : ℝ) /
        (2 : ℝ) ^ ((2 * (m : ℝ) + 1) / 2)) atTop (nhds 0) := by
      simpa only [Function.comp_def, hcast_odd] using tendsto_exceptFamily_zero.comp h2m1_atTop
    have hinter_odd :
        Tendsto (fun m : ℕ ↦ ((oddFamily (2 * m + 1) ∩ highFamily (2 * m + 1)).card : ℝ) /
          (2 : ℝ) ^ ((2 * (m : ℝ) + 1) / 2)) atTop (nhds 0) := by
      simpa only [Function.comp_def, hcast_odd] using tendsto_odd_inter_high_zero.comp h2m1_atTop
    have hformula : ∀ m : ℕ, (Erdos748.f (2 * m + 1) : ℝ) / (2 : ℝ) ^ ((2 * (m : ℝ) + 1) / 2) =
        ((oddFamily (2 * m + 1)).card : ℝ) / (2 : ℝ) ^ ((2 * (m : ℝ) + 1) / 2) +
        ((highFamily (2 * m + 1)).card : ℝ) / (2 : ℝ) ^ ((2 * (m : ℝ) + 1) / 2) +
        ((exceptFamily (2 * m + 1)).card : ℝ) / (2 : ℝ) ^ ((2 * (m : ℝ) + 1) / 2) -
        ((oddFamily (2 * m + 1) ∩ highFamily (2 * m + 1)).card : ℝ) /
          (2 : ℝ) ^ ((2 * (m : ℝ) + 1) / 2) := by
      intro m
      have hd : (Erdos748.f (2 * m + 1) : ℝ) +
          ((oddFamily (2 * m + 1) ∩ highFamily (2 * m + 1)).card : ℝ) =
          ((oddFamily (2 * m + 1)).card : ℝ) + ((highFamily (2 * m + 1)).card : ℝ) +
          ((exceptFamily (2 * m + 1)).card : ℝ) := by exact_mod_cast card_decomp (2 * m + 1)
      have hpos : (2 : ℝ) ^ ((2 * (m : ℝ) + 1) / 2) ≠ 0 :=
        (Real.rpow_pos_of_pos (by norm_num) _).ne'
      field_simp [hpos]
      linarith
    simp_rw [hformula]
    have hlim := ((hodd_odd.add hhigh_odd).add hexc_odd).sub hinter_odd
    have hval : Real.sqrt 2 + (Real.sqrt 2 + ∑' k : ℕ, w (2 * k + 1)) + 0 - 0 =
        2 * Real.sqrt 2 + ∑' k : ℕ, w (2 * k + 1) := by ring
    rw [hval] at hlim
    exact hlim
