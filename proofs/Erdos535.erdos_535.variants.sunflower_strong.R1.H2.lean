import OMAReductions.R_Erdos535_erdos_535_variants_sunflower_strong_R1
import Mathlib.Data.Nat.Pairing

/-! Elementary counting and prime-exponent representation for arithmetic sunflowers. -/

namespace OMA.SunflowerScratch

open scoped BigOperators ArithmeticFunction.Omega

private theorem countBooleanExtensions {ι : Type*} [DecidableEq ι]
    {U S P : Finset ι} (hS : S ⊆ U) (hP : P ⊆ S) :
    (U.powerset.filter (fun W => W ∩ S = P)).card = 2 ^ (U.card - S.card) := by
  have hEq : U.powerset.filter (fun W => W ∩ S = P) =
      (U \ S).powerset.image (fun T => T ∪ P) := by
    ext W
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hWU, hWP⟩
      refine ⟨W \ S, ?_, ?_⟩
      · intro i hi
        have hi' := Finset.mem_sdiff.mp hi
        exact Finset.mem_sdiff.mpr ⟨hWU hi'.1, hi'.2⟩
      · rw [← hWP, Finset.sdiff_union_inter]
    · rintro ⟨T, hT, rfl⟩
      constructor
      · intro i hi
        exact (Finset.mem_union.mp hi).elim
          (fun hi' => (Finset.mem_sdiff.mp (hT hi')).1)
          (fun hi' => hS (hP hi'))
      · ext i
        simp only [Finset.mem_inter, Finset.mem_union]
        exact ⟨fun ⟨hi, his⟩ => hi.elim
          (fun hit => False.elim ((Finset.mem_sdiff.mp (hT hit)).2 his)) id,
          fun hip => ⟨Or.inr hip, hP hip⟩⟩
  have hInj : Set.InjOn (fun T : Finset ι => T ∪ P) (↑((U \ S).powerset) : Set (Finset ι)) := by
    intro T hT V hV hEq'
    change T ∪ P = V ∪ P at hEq'
    ext i
    have hDisj (T : Finset ι) (hT : T ∈ (U \ S).powerset) (hi : i ∈ T) : i ∉ P :=
      fun hip => (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hT hi)).2 (hP hip)
    constructor
    · intro hi
      have hi' : i ∈ V ∪ P := hEq' ▸ Finset.mem_union_left _ hi
      exact (Finset.mem_union.mp hi').resolve_right (hDisj T hT hi)
    · intro hi
      have hi' : i ∈ T ∪ P := hEq'.symm ▸ Finset.mem_union_left _ hi
      exact (Finset.mem_union.mp hi').resolve_right (hDisj V hV hi)
  rw [hEq, Finset.card_image_of_injOn hInj, Finset.card_powerset,
    Finset.card_sdiff_of_subset hS]

private theorem thinBooleanRestrictions {α ι : Type*} [DecidableEq ι]
    (A : Finset α) (D P : α → Finset ι) (k : ℕ)
    (hD : ∀ n ∈ A, (D n).card = k) (hP : ∀ n ∈ A, P n ⊆ D n) :
    ∃ W : Finset ι, A.card ≤ 2 ^ k * (A.filter (fun n => W ∩ D n = P n)).card := by
  classical
  by_cases hA : A.Nonempty
  · let U := A.biUnion D
    have hU {n} (hn : n ∈ A) : D n ⊆ U := by
      intro x hx
      exact Finset.mem_biUnion.mpr ⟨n, hn, hx⟩
    have hk : k ≤ U.card := by
      obtain ⟨n, hn⟩ := hA
      rw [← hD n hn]
      exact Finset.card_le_card (hU hn)
    let score (W : Finset ι) := (A.filter (fun n => W ∩ D n = P n)).card
    obtain ⟨W, _, hW⟩ := Finset.exists_max_image U.powerset score
      ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset U)⟩
    refine ⟨W, ?_⟩
    have hSum : (∑ V ∈ U.powerset, score V) = A.card * 2 ^ (U.card - k) := by
      calc
        _ = ∑ V ∈ U.powerset, ∑ n ∈ A, if V ∩ D n = P n then 1 else 0 := by
          simp only [score, Finset.sum_boole, Nat.cast_id]
        _ = ∑ n ∈ A, ∑ V ∈ U.powerset, if V ∩ D n = P n then 1 else 0 :=
          Finset.sum_comm
        _ = ∑ _ ∈ A, 2 ^ (U.card - k) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.sum_boole, Nat.cast_id, countBooleanExtensions (hU hn) (hP n hn),
            hD n hn]
        _ = _ := by simp
    have hBound : (∑ V ∈ U.powerset, score V) ≤ U.powerset.card * score W := by
      calc
        _ ≤ ∑ _ ∈ U.powerset, score W := Finset.sum_le_sum hW
        _ = _ := by simp
    have hPow : 2 ^ U.card = 2 ^ (U.card - k) * 2 ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    rw [hSum, Finset.card_powerset, hPow] at hBound
    have hMul : 0 < 2 ^ (U.card - k) := by positivity
    exact Nat.le_of_mul_le_mul_left (by simpa only [mul_assoc, mul_comm A.card] using hBound) hMul
  · exact ⟨∅, by simp [Finset.not_nonempty_iff_eq_empty.mp hA]⟩

private def layers (n : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  n.primeFactors.sigma (fun p => Finset.range (n.factorization p))

private def terminalLayers (n : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (layers n).filter (fun x => x.2 + 1 = n.factorization x.1)

@[simp] private theorem memLayers {n p i : ℕ} :
    (⟨p, i⟩ : Σ _ : ℕ, ℕ) ∈ layers n ↔ i < n.factorization p := by
  simp only [layers, Finset.mem_sigma, Finset.mem_range]
  refine ⟨And.right, fun hi => ⟨?_, hi⟩⟩
  rw [← Nat.support_factorization, Finsupp.mem_support_iff]
  omega

private theorem layersCard (n : ℕ) : (layers n).card = Ω n := by
  rw [layers, Finset.card_sigma, ArithmeticFunction.cardFactors_eq_sum_factorization]
  simp [Finsupp.sum]

private theorem layersGcd {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    layers (a.gcd b) = layers a ∩ layers b := by
  ext ⟨p, i⟩
  simp only [Finset.mem_inter, memLayers, Nat.factorization_gcd ha hb]
  change i < min (a.factorization p) (b.factorization p) ↔ _
  exact lt_min_iff

private theorem layersInjOn : Set.InjOn layers {n : ℕ | n ≠ 0} := by
  intro a ha b hb h
  apply Nat.factorization_inj ha hb
  ext p
  apply le_antisymm
  · by_contra! hl
    have hmem : (⟨p, b.factorization p⟩ : Σ _ : ℕ, ℕ) ∈ layers a := memLayers.mpr hl
    rw [h] at hmem
    exact (lt_irrefl _) (memLayers.mp hmem)
  · by_contra! hl
    have hmem : (⟨p, a.factorization p⟩ : Σ _ : ℕ, ℕ) ∈ layers b := memLayers.mpr hl
    rw [← h] at hmem
    exact (lt_irrefl _) (memLayers.mp hmem)

private theorem agreeingExponents {W : Finset (Σ _ : ℕ, ℕ)} {a b p : ℕ}
    (ha : W ∩ layers a = terminalLayers a) (hb : W ∩ layers b = terminalLayers b)
    (hpa : 0 < a.factorization p) (hpb : 0 < b.factorization p) :
    a.factorization p = b.factorization p := by
  have step {n m : ℕ} (hn : W ∩ layers n = terminalLayers n)
      (hm : W ∩ layers m = terminalLayers m) (hpn : 0 < n.factorization p)
      (hle : n.factorization p ≤ m.factorization p) :
      n.factorization p = m.factorization p := by
    let x : Σ _ : ℕ, ℕ := ⟨p, n.factorization p - 1⟩
    have hxN : x ∈ terminalLayers n := by
      simp only [x, terminalLayers, Finset.mem_filter, memLayers]
      omega
    have hxW : x ∈ W := by
      rw [← hn] at hxN
      exact (Finset.mem_inter.mp hxN).1
    have hxM : x ∈ terminalLayers m := by
      rw [← hm]
      exact Finset.mem_inter.mpr ⟨hxW, memLayers.mpr (by omega)⟩
    have he := (Finset.mem_filter.mp hxM).2
    dsimp [x] at he
    omega
  rcases le_total (a.factorization p) (b.factorization p) with hle | hle
  · exact step ha hb hpa hle
  · exact (step hb ha hpb hle).symm

private theorem coprimeGcdQuotient {W : Finset (Σ _ : ℕ, ℕ)} {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hwa : W ∩ layers a = terminalLayers a)
    (hwb : W ∩ layers b = terminalLayers b) :
    ∃ q, a = (a.gcd b) * q ∧ Nat.gcd q (a.gcd b) = 1 := by
  let d := a.gcd b
  have hd : 0 < d := Nat.gcd_pos_of_pos_left _ ha
  obtain ⟨q, hq⟩ := Nat.gcd_dvd_left a b
  change a = d * q at hq
  have hq0 : q ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hq
    omega
  refine ⟨q, hq, Nat.coprime_of_dvd ?_⟩
  intro p hp hpq hpd
  have hpa : 0 < a.factorization p :=
    hp.factorization_pos_of_dvd ha.ne' (hpd.trans (Nat.gcd_dvd_left a b))
  have hpb : 0 < b.factorization p :=
    hp.factorization_pos_of_dvd hb.ne' (hpd.trans (Nat.gcd_dvd_right a b))
  have hpd' : d.factorization p = a.factorization p := by
    dsimp [d]
    rw [Nat.factorization_gcd ha.ne' hb.ne']
    change min (a.factorization p) (b.factorization p) = a.factorization p
    rw [agreeingExponents hwa hwb hpa hpb, min_self]
  have hpq' : 0 < q.factorization p := hp.factorization_pos_of_dvd hq0 hpq
  have hsum : a.factorization p = d.factorization p + q.factorization p := by
    rw [hq, Nat.factorization_mul hd.ne' hq0]
    rfl
  omega

theorem integerFamilyRepresentation :
    ∀ (r k : ℕ) (A : Finset ℕ), Erdos535.AllBigOmega k A →
      ∃ B ⊆ A, A.card ≤ 2 ^ k * B.card ∧
        ∃ enc : ℕ → Finset ℕ, Set.InjOn enc (B : Set ℕ) ∧
          (∀ n ∈ B, (enc n).card = k) ∧
          (∀ S ⊆ B, S.card = r →
            (∃ K : Finset ℕ,
              (S : Set ℕ).Pairwise (fun a b => enc a ∩ enc b = K)) →
            ∃ d, 0 < d ∧ (S : Set ℕ).Pairwise (fun a b => Nat.gcd a b = d) ∧
              ∀ a ∈ S, ∃ b, a = d * b ∧ Nat.gcd b d = 1) := by
  intro r k A hΩ
  obtain ⟨W, hW⟩ := thinBooleanRestrictions A layers terminalLayers k
    (fun n hn => (layersCard n).trans (hΩ n hn).2)
    (fun n _ => Finset.filter_subset _ _)
  let B := A.filter (fun n => W ∩ layers n = terminalLayers n)
  let e := ((Equiv.sigmaEquivProd ℕ ℕ).trans Nat.pairEquiv).toEmbedding
  let enc (n : ℕ) := (layers n).map e
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have positive {a : ℕ} (ha : a ∈ B) : 0 < a := (hΩ a (hBA ha)).1
  have compatible {a : ℕ} (ha : a ∈ B) : W ∩ layers a = terminalLayers a :=
    (Finset.mem_filter.mp ha).2
  refine ⟨B, hBA, hW, enc, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    exact layersInjOn (positive ha).ne' (positive hb).ne' (Finset.map_injective e hab)
  · intro n hn
    change ((layers n).map e).card = k
    rw [Finset.card_map, layersCard, (hΩ n (hBA hn)).2]
  intro S hSB hSr hSunflower
  by_cases hSmall : r ≤ 1
  · refine ⟨1, by decide, ?_, fun a _ => ⟨a, by simp, by simp⟩⟩
    intro a ha b hb hab
    have hcard : 1 < S.card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
    omega
  have hcard : 1 < S.card := by omega
  obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ := Finset.one_lt_card.mp hcard
  obtain ⟨K, hK⟩ := hSunflower
  let d := a₀.gcd b₀
  have hd : 0 < d := Nat.gcd_pos_of_pos_left _ (positive (hSB ha₀))
  have common {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
      a.gcd b = d := by
    apply layersInjOn (Nat.gcd_pos_of_pos_left _ (positive (hSB ha))).ne' hd.ne'
    change layers (a.gcd b) = layers (a₀.gcd b₀)
    rw [layersGcd (positive (hSB ha)).ne' (positive (hSB hb)).ne',
      layersGcd (positive (hSB ha₀)).ne' (positive (hSB hb₀)).ne']
    apply Finset.map_injective e
    simpa only [Finset.map_inter] using (hK ha hb hab).trans (hK ha₀ hb₀ hab₀).symm
  refine ⟨d, hd, fun _ ha _ hb hab => common ha hb hab, ?_⟩
  intro a ha
  obtain ⟨b, hb, hab⟩ : ∃ b ∈ S, a ≠ b := by
    by_cases h : a = a₀
    · exact ⟨b₀, hb₀, h ▸ hab₀⟩
    · exact ⟨a₀, ha₀, h⟩
  simpa only [common ha hb hab] using
    coprimeGcdQuotient (positive (hSB ha)) (positive (hSB hb))
      (compatible (hSB ha)) (compatible (hSB hb))

end OMA.SunflowerScratch

theorem OMA.solution : OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1.H2 :=
  OMA.SunflowerScratch.integerFamilyRepresentation
