import FormalConjectures.ErdosProblems.«402»
import Mathlib.Tactic

-- Reduction Erdos402.erdos_402.R1 of Erdős Problem 402 (Graham's gcd conjecture).
-- Credit: @cosmaticdev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Reduction of Erdős 402 (Graham's gcd conjecture)

Target: for `A : Finset ℕ` with `0 ∉ A` and `A.Nonempty`, some `a b ∈ A` satisfy
`a.gcd b ≤ (a / A.card : ℚ)`, i.e. `max_{a,b} a / gcd(a,b) ≥ |A|`.

The glue in `main` (all proved below, no hypotheses) follows the standard reduction used in the
published proofs (Balasubramanian–Soundararajan, Acta Arithmetica 75 (1996); Boyle; Szegedy;
Zaharescu; see also Ford, Canad. Math. Bull. 47 (2004) for the notation):

* `|A| = 1` is immediate (`a = b`).
* Scaling by `g = gcd A` reduces to `gcd A = 1`: the statement for `A` is equivalent to the
  statement for `A.image (· / g)` (proved in `Glue.transfer` and friends).
* If some element has a prime factor `p ≥ |A|` then, since `gcd A = 1`, some `b ∈ A` is not
  divisible by `p`, so `gcd(a,b) ∣ a/p ≤ a/|A|` (`Glue.large_prime`).
* Hence it remains to treat sets with all prime factors `< |A|`; this splits into the
  Boyle range `2p ≥ |A|` (H1) and the deep smooth case `2p < |A|` (H2).

`H1` is Boyle's theorem (a prime `p > (|A|-1)/2` dividing some element forces the conclusion);
`H2` is the hard smooth core, proved by Balasubramanian–Soundararajan with analytic number
theory (Brun–Titchmarsh, explicit prime-counting bounds).
-/

namespace OMA.R_Erdos402_erdos_402_R1

-- H1 (Boyle-type range): some element has a prime factor p with |A| <= 2p, i.e. p > (|A|-1)/2.
def H1 : Prop := ∀ (A : Finset ℕ), 0 ∉ A → A.Nonempty →
  (∃ a ∈ A, ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ A.card ≤ 2 * p) →
  ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ)

-- H2 (deep smooth case): gcd 1 and every prime factor p of every element satisfies 2p < |A|.
def H2 : Prop := ∀ (A : Finset ℕ), 0 ∉ A → A.Nonempty → A.gcd id = 1 →
  (∀ a ∈ A, ∀ p : ℕ, p.Prime → p ∣ a → 2 * p < A.card) →
  ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ)

namespace Glue

lemma pos_of_mem {A : Finset ℕ} (h0 : 0 ∉ A) {a : ℕ} (ha : a ∈ A) : 0 < a :=
  Nat.pos_of_ne_zero (fun h => h0 (h ▸ ha))

lemma card_one (A : Finset ℕ) (hne : A.Nonempty) (hc : A.card = 1) :
    ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  obtain ⟨a, ha⟩ := hne
  refine ⟨a, ha, a, ha, ?_⟩
  simp [Nat.gcd_self, hc]

lemma gcd_pos (A : Finset ℕ) (h0 : 0 ∉ A) (hne : A.Nonempty) : 0 < A.gcd id := by
  have hne0 : ¬ ∀ x ∈ A, (id x) = 0 := by
    push Not
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, ha, Nat.ne_of_gt (pos_of_mem h0 ha)⟩
  rw [Nat.pos_iff_ne_zero, Ne, Finset.gcd_eq_zero_iff]
  exact hne0

lemma image_zero_not_mem (A : Finset ℕ) (h0 : 0 ∉ A) {g : ℕ} (hg : g = A.gcd id)
    (hgpos : 0 < g) : 0 ∉ A.image (fun a => a / g) := by
  intro h
  obtain ⟨a, ha, hdiv⟩ := Finset.mem_image.mp h
  have ha_pos : 0 < a := pos_of_mem h0 ha
  have hg_dvd : g ∣ a := by rw [hg]; exact Finset.gcd_dvd ha
  have hlt : 0 < a / g := Nat.div_pos (Nat.le_of_dvd ha_pos hg_dvd) hgpos
  rw [hdiv] at hlt
  exact lt_irrefl 0 hlt

lemma image_card (A : Finset ℕ) {g : ℕ} (hg : g = A.gcd id) :
    (A.image (fun a => a / g)).card = A.card := by
  rw [Finset.card_image_iff]
  intro a ha b hb hab
  have hab2 : a / g = b / g := hab
  have ha' : a ∈ A := Finset.mem_coe.mp ha
  have hb' : b ∈ A := Finset.mem_coe.mp hb
  have hga : g ∣ a := by rw [hg]; exact Finset.gcd_dvd ha'
  have hgb : g ∣ b := by rw [hg]; exact Finset.gcd_dvd hb'
  rw [← Nat.mul_div_cancel' hga, ← Nat.mul_div_cancel' hgb, hab2]

lemma image_nonempty (A : Finset ℕ) (hne : A.Nonempty) (g : ℕ) :
    (A.image (fun a => a / g)).Nonempty := by
  obtain ⟨a, ha⟩ := hne
  exact ⟨a / g, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩

lemma image_gcd_eq_one (A : Finset ℕ) (h0 : 0 ∉ A) (hne : A.Nonempty) {g : ℕ}
    (hg : g = A.gcd id) (hgpos : 0 < g) : (A.image (fun a => a / g)).gcd id = 1 := by
  set d := (A.image (fun a => a / g)).gcd id with hd
  have hdvd : ∀ a ∈ A, d ∣ a / g := by
    intro a ha
    exact Finset.gcd_dvd (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have hdg : ∀ a ∈ A, d * g ∣ a := by
    intro a ha
    have hga : g ∣ a := by rw [hg]; exact Finset.gcd_dvd ha
    rw [(Nat.div_mul_cancel hga).symm]
    exact Nat.mul_dvd_mul (hdvd a ha) (dvd_refl g)
  have h : d * g ∣ A.gcd id := Finset.dvd_gcd hdg
  rw [← hg] at h
  have hle : d * g ≤ g := Nat.le_of_dvd hgpos h
  obtain ⟨a, ha⟩ := hne
  have ha_pos : 0 < a := pos_of_mem h0 ha
  have hga : g ∣ a := by rw [hg]; exact Finset.gcd_dvd ha
  have hpos : 0 < a / g := Nat.div_pos (Nat.le_of_dvd ha_pos hga) hgpos
  have hd0 : 0 < d := by
    by_contra hc
    push Not at hc
    have hd0' : d = 0 := by omega
    rw [hd0', Nat.zero_mul] at h
    have hg0 : g = 0 := Nat.eq_zero_of_zero_dvd h
    omega
  have hd1 : d ≤ 1 := by nlinarith [hle, hgpos]
  have hd_eq : d = 1 := by omega
  exact hd_eq

lemma large_prime (A : Finset ℕ) (h0 : 0 ∉ A) (hne : A.Nonempty) (hg : A.gcd id = 1)
    {a : ℕ} (ha : a ∈ A) {p : ℕ} (hp : p.Prime) (hpa : p ∣ a) (hpn : A.card ≤ p) :
    ∃ x ∈ A, ∃ y ∈ A, x.gcd y ≤ (x / A.card : ℚ) := by
  have hnot : ¬ ∀ x ∈ A, p ∣ x := by
    intro h
    have h2 : p ∣ A.gcd id := Finset.dvd_gcd h
    rw [hg] at h2
    exact hp.not_dvd_one h2
  push Not at hnot
  obtain ⟨b, hb, hpb⟩ := hnot
  refine ⟨a, ha, b, hb, ?_⟩
  have hgl : a.gcd b ∣ a := Nat.gcd_dvd_left ..
  have hgr : a.gcd b ∣ b := Nat.gcd_dvd_right ..
  have hcop : (a.gcd b).Coprime p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    exact fun h => hpb (h.trans hgr)
  have ha_eq : p * (a / p) = a := Nat.mul_div_cancel' hpa
  have h2 : a.gcd b ∣ p * (a / p) := by rw [ha_eq]; exact hgl
  have hdvd : a.gcd b ∣ a / p := hcop.dvd_of_dvd_mul_left h2
  have ha_pos : 0 < a := pos_of_mem h0 ha
  have hle : a.gcd b ≤ a / p :=
    Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd ha_pos hpa) hp.pos) hdvd
  have h1 : a.gcd b * A.card ≤ a.gcd b * p := Nat.mul_le_mul (le_refl _) hpn
  have h3 : a.gcd b * p ≤ a := (Nat.le_div_iff_mul_le hp.pos).mp hle
  have h4 : a.gcd b * A.card ≤ a := h1.trans h3
  have h5 : (a.gcd b : ℚ) * (A.card : ℚ) ≤ (a : ℚ) := by exact_mod_cast h4
  have hcard : 0 < (A.card : ℚ) := by exact_mod_cast Finset.card_pos.mpr hne
  exact (le_div_iff₀ hcard).mpr h5

lemma transfer (A : Finset ℕ) {g : ℕ} (hg : g = A.gcd id) (hgpos : 0 < g)
    (hcard : (A.image (fun a => a / g)).card = A.card)
    (h : ∃ a' ∈ A.image (fun a => a / g), ∃ b' ∈ A.image (fun a => a / g),
      a'.gcd b' ≤ (a' / (A.image (fun a => a / g)).card : ℚ)) :
    ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  obtain ⟨a', ha', b', hb', hle⟩ := h
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha'
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb'
  have hga : g ∣ a := by rw [hg]; exact Finset.gcd_dvd ha
  have hgb : g ∣ b := by rw [hg]; exact Finset.gcd_dvd hb
  rw [hcard] at hle
  refine ⟨a, ha, b, hb, ?_⟩
  have hab : a.gcd b = g * ((a / g).gcd (b / g)) := by
    rw [← Nat.gcd_mul_left, Nat.mul_div_cancel' hga, Nat.mul_div_cancel' hgb]
  have ha' : (a : ℚ) = ↑g * ↑(a / g) := by rw [← Nat.cast_mul, Nat.mul_div_cancel' hga]
  have hg0 : (0 : ℚ) ≤ ↑g := Nat.cast_nonneg g
  have key : (a.gcd b : ℚ) ≤ (a : ℚ) / (A.card : ℚ) := by
    rw [hab, Nat.cast_mul, ha', mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hle hg0
  exact key

end Glue

theorem main : H1 → H2 → type_of% @Erdos402.erdos_402 := by
  intro h₁ h₂ A h0 hne
  by_cases hc1 : A.card = 1
  · exact Glue.card_one A hne hc1
  · have hcard_pos : 0 < A.card := Finset.card_pos.mpr hne
    have hn2 : 2 ≤ A.card := by omega
    set g := A.gcd id with hgdef
    have hgpos : 0 < g := Glue.gcd_pos A h0 hne
    have hg : g = A.gcd id := hgdef
    let A' := A.image (fun a => a / g)
    have h0' : 0 ∉ A' := Glue.image_zero_not_mem A h0 hg hgpos
    have hne' : A'.Nonempty := Glue.image_nonempty A hne g
    have hcard' : A'.card = A.card := Glue.image_card A hg
    have hgcd' : A'.gcd id = 1 := Glue.image_gcd_eq_one A h0 hne hg hgpos
    have hconc : ∃ a' ∈ A', ∃ b' ∈ A', a'.gcd b' ≤ (a' / A'.card : ℚ) := by
      by_cases hbig : ∃ a ∈ A', ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ A'.card ≤ p
      · obtain ⟨a, ha, p, hp, hpa, hpn⟩ := hbig
        exact Glue.large_prime A' h0' hne' hgcd' ha hp hpa hpn
      · push Not at hbig
        by_cases hmid : ∃ a ∈ A', ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ A'.card ≤ 2 * p
        · exact h₁ A' h0' hne' hmid
        · push Not at hmid
          exact h₂ A' h0' hne' hgcd' hmid
    exact Glue.transfer A hg hgpos hcard' hconc

end OMA.R_Erdos402_erdos_402_R1
