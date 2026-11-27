import FormalConjectures.ErdosProblems.«402»
import Mathlib

/-!
Graham's gcd bound reduced to finite and large smooth cores.
The elementary Boyle, prime-cardinality, and lcm arguments are adapted
from Boris Alexeev's Lean development, formal authors Codex and GPT-5.6 Sol:
https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos402.lean
Source blob f64dbcb0cb7d999a5205bdc380a23191b11d241b.
Normalization follows the existing R1 reduction. The squarefree case
uses Mathlib's Marica–Schönheim theorem. No native certificates are used.
-/
namespace OMA.R_Erdos402_erdos_402_R2

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

private lemma primeFree_inj {p a b : ℕ} (hp : p.Prime) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : a / a.gcd b < p) (hb : b / a.gcd b < p)
    (hc : ((ordCompl[p] a : ℕ) : ZMod p) = ((ordCompl[p] b : ℕ) : ZMod p)) : a = b := by
  letI : Fact p.Prime := ⟨hp⟩
  let g := a.gcd b
  let x := a / g
  let y := b / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
  have hxpos : 0 < x := Nat.div_pos (Nat.gcd_le_left b (Nat.pos_of_ne_zero ha0)) hgpos
  have hypos : 0 < y := Nat.div_pos (Nat.gcd_le_right a (Nat.pos_of_ne_zero hb0)) hgpos
  have hxlt : x < p := ha
  have hylt : y < p := hb
  have hpx : ¬p ∣ x := by
    intro h
    exact (not_lt_of_ge (Nat.le_of_dvd hxpos h)) hxlt
  have hpy : ¬p ∣ y := by
    intro h
    exact (not_lt_of_ge (Nat.le_of_dvd hypos h)) hylt
  have hox : ordCompl[p] x = x :=
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd x hp).mpr (Or.inr hpx)
  have hoy : ordCompl[p] y = y :=
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd y hp).mpr (Or.inr hpy)
  have hga : g * x = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hgb : g * y = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hcg0 : ((ordCompl[p] g : ℕ) : ZMod p) ≠ 0 := by
    intro hz
    exact Nat.not_dvd_ordCompl hp hgpos.ne'
      ((ZMod.natCast_eq_zero_iff (ordCompl[p] g : ℕ) p).mp hz)
  have hc' : ((ordCompl[p] g : ℕ) : ZMod p) * x =
      ((ordCompl[p] g : ℕ) : ZMod p) * y := by
    simpa only [← hga, ← hgb, Nat.ordCompl_mul, hox, hoy, Nat.cast_mul] using hc
  have hxyZ : (x : ZMod p) = y := mul_left_cancel₀ hcg0 hc'
  have hxy : x = y := by
    have hv := congrArg ZMod.val hxyZ
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] using hv
  rw [← hga, ← hgb, hxy]

lemma grahamBound_of_prime_card (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hp : A.card.Prime) : (∃ a ∈ A, ∃ b ∈ A, A.card * a.gcd b ≤ a) := by
  by_contra hbad
  let p := A.card
  letI : Fact p.Prime := ⟨hp⟩
  have hquot : ∀ a ∈ A, ∀ b ∈ A, a / a.gcd b < p := by
    intro a ha b hb
    have ha0 : a ≠ 0 := fun hz ↦ h₀ (hz ▸ ha)
    have hgpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
    rw [Nat.div_lt_iff_lt_mul hgpos]
    by_contra h
    apply hbad
    exact ⟨a, ha, b, hb, by simpa [p, mul_comm] using h⟩
  letI := Fintype.ofFinite {z : ZMod p // z ≠ 0}
  let color : {a // a ∈ A} → {z : ZMod p // z ≠ 0} := fun a ↦
    ⟨((ordCompl[p] a.1 : ℕ) : ZMod p), by
      intro hz
      have ha0 : a.1 ≠ 0 := fun h ↦ h₀ (h ▸ a.2)
      exact Nat.not_dvd_ordCompl hp ha0
        ((ZMod.natCast_eq_zero_iff (ordCompl[p] a.1 : ℕ) p).mp hz)⟩
  have hcolor : Function.Injective color := by
    intro a b hab
    apply Subtype.ext
    apply primeFree_inj hp
    · exact fun h ↦ h₀ (h ▸ a.2)
    · exact fun h ↦ h₀ (h ▸ b.2)
    · exact hquot a.1 a.2 b.1 b.2
    · simpa [Nat.gcd_comm] using hquot b.1 b.2 a.1 a.2
    · exact congrArg Subtype.val hab
  have hle := Fintype.card_le_of_injective color hcolor
  have hcod : Fintype.card {z : ZMod p // z ≠ 0} = p - 1 := by
    rw [Fintype.card_subtype_compl (fun z : ZMod p ↦ z = 0)]
    simp
  rw [Fintype.card_coe, hcod] at hle
  exact (not_le_of_gt (Nat.sub_lt hp.pos Nat.zero_lt_one)) (by simpa [p] using hle)

private lemma div_gcd_lt_card_of_not_grahamBound (A : Finset ℕ)
    (hbad : ¬ (∃ a ∈ A, ∃ b ∈ A, A.card * a.gcd b ≤ a)) {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (ha0 : a ≠ 0) : a / a.gcd b < A.card := by
  have hgpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
  rw [Nat.div_lt_iff_lt_mul hgpos]
  exact Nat.lt_of_not_ge fun h ↦ hbad ⟨a, ha, b, hb, by simpa [mul_comm] using h⟩

private lemma prime_not_dvd_of_card_le (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ (∃ a ∈ A, ∃ b ∈ A, A.card * a.gcd b ≤ a)) {p : ℕ} (hp : p.Prime)
    (hcard : A.card ≤ p) {a : ℕ} (ha : a ∈ A) : ¬p ∣ a := by
  intro hpa
  have hex : ∃ b ∈ A, ¬p ∣ b := by
    by_contra h
    push Not at h
    have hpgcd : p ∣ A.gcd id := Finset.dvd_gcd fun b hb ↦ h b hb
    rw [hgcd] at hpgcd
    exact hp.not_dvd_one hpgcd
  obtain ⟨b, hb, hpb⟩ := hex
  have ha0 : a ≠ 0 := fun hz ↦ h₀ (hz ▸ ha)
  have hgpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
  have hpg : ¬p ∣ a.gcd b := fun h ↦ hpb (h.trans (Nat.gcd_dvd_right a b))
  have hpquot : p ∣ a / a.gcd b := by
    have hprod : (a / a.gcd b) * a.gcd b = a :=
      Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
    have hp_prod : p ∣ (a / a.gcd b) * a.gcd b := by
      rw [hprod]
      exact hpa
    exact (hp.dvd_mul.mp hp_prod).resolve_right hpg
  have hqpos : 0 < a / a.gcd b :=
    Nat.div_pos (Nat.gcd_le_left b (Nat.pos_of_ne_zero ha0)) hgpos
  have hple : p ≤ a / a.gcd b := Nat.le_of_dvd hqpos hpquot
  have hlt := div_gcd_lt_card_of_not_grahamBound A hbad ha hb ha0
  omega

private lemma prime_not_dvd_of_card_le_two_mul (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ (∃ a ∈ A, ∃ b ∈ A, A.card * a.gcd b ≤ a)) {q : ℕ} (hq : q.Prime)
    (hlarge : A.card ≤ 2 * q) {a : ℕ} (ha : a ∈ A) : ¬q ∣ a := by
  classical
  by_cases hcard : A.card ≤ q
  · exact prime_not_dvd_of_card_le A h₀ hgcd hbad hq hcard ha
  have hqn : q < A.card := Nat.lt_of_not_ge hcard
  intro hqa
  let C := A.filter fun x ↦ q ∣ x
  let V := A.filter fun x ↦ ¬q ∣ x
  let U := C.image fun x ↦ x / q
  have hCne : C.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, hqa⟩⟩
  have hVne : V.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hall : ∀ x ∈ A, q ∣ x := by
      intro x hx
      by_contra hqx
      have : x ∈ V := Finset.mem_filter.mpr ⟨hx, hqx⟩
      simpa [h] using this
    have hqgcd : q ∣ A.gcd id := Finset.dvd_gcd hall
    rw [hgcd] at hqgcd
    exact hq.not_dvd_one hqgcd
  have hUne : U.Nonempty := hCne.image _
  have hUcard : U.card = C.card := by
    dsimp only [U]
    rw [Finset.card_image_of_injOn]
    intro x hx y hy hxy
    have hqx : q ∣ x := (Finset.mem_filter.mp hx).2
    have hqy : q ∣ y := (Finset.mem_filter.mp hy).2
    exact (Nat.div_left_inj hqx hqy).mp hxy
  have hpartition : C.card + V.card = A.card := by
    simpa only [C, V] using
      (Finset.card_filter_add_card_filter_not (s := A) (p := fun x ↦ q ∣ x))
  have hcross : ∀ c ∈ C, ∀ v ∈ V, c / q ∣ v := by
    intro c hc v hv
    have hcA : c ∈ A := (Finset.mem_filter.mp hc).1
    have hqc : q ∣ c := (Finset.mem_filter.mp hc).2
    have hvA : v ∈ A := (Finset.mem_filter.mp hv).1
    have hqv : ¬q ∣ v := (Finset.mem_filter.mp hv).2
    have hc0 : c ≠ 0 := fun hz ↦ h₀ (hz ▸ hcA)
    have hgpos : 0 < c.gcd v := Nat.gcd_pos_of_pos_left v (Nat.pos_of_ne_zero hc0)
    have hqg : ¬q ∣ c.gcd v := fun h ↦ hqv (h.trans (Nat.gcd_dvd_right c v))
    have hqquot : q ∣ c / c.gcd v := by
      have hprod : (c / c.gcd v) * c.gcd v = c :=
        Nat.div_mul_cancel (Nat.gcd_dvd_left c v)
      have : q ∣ (c / c.gcd v) * c.gcd v := by simpa [hprod] using hqc
      exact (hq.dvd_mul.mp this).resolve_right hqg
    have hquotpos : 0 < c / c.gcd v :=
      Nat.div_pos (Nat.gcd_le_left v (Nat.pos_of_ne_zero hc0)) hgpos
    have hquotlt : c / c.gcd v < A.card :=
      div_gcd_lt_card_of_not_grahamBound A hbad hcA hvA hc0
    have hquoteq : c / c.gcd v = q := by
      obtain ⟨k, hk⟩ := hqquot
      have hkpos : 0 < k := by
        exact Nat.pos_of_mul_pos_left (hk ▸ hquotpos)
      have hkle : k = 1 := by
        by_contra hk1
        have hk2 : 2 ≤ k := by omega
        have htwo : 2 * q ≤ c / c.gcd v := by
          calc
            2 * q = q * 2 := Nat.mul_comm 2 q
            _ ≤ q * k := Nat.mul_le_mul_left q hk2
            _ = c / c.gcd v := hk.symm
        omega
      simpa [hkle] using hk
    have hcprod : q * (c / q) = c := by
      simpa [mul_comm] using Nat.mul_div_cancel' hqc
    have hgprod : q * c.gcd v = c := by
      calc
        q * c.gcd v = (c / c.gcd v) * c.gcd v := by rw [hquoteq]
        _ = c := Nat.div_mul_cancel (Nat.gcd_dvd_left c v)
    have hg : c.gcd v = c / q := Nat.mul_left_cancel hq.pos (hgprod.trans hcprod.symm)
    rw [← hg]
    exact Nat.gcd_dvd_right c v
  have hcrossU : ∀ u ∈ U, ∀ v ∈ V, u ∣ v := by
    intro u hu v hv
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hu
    exact hcross c hc v hv
  let u₀ := U.min' hUne
  let v₀ := V.min' hVne
  have hu₀ : u₀ ∈ U := U.min'_mem hUne
  have hv₀ : v₀ ∈ V := V.min'_mem hVne
  have hu₀pos : 0 < u₀ := by
    obtain ⟨c, hc, hcu⟩ := Finset.mem_image.mp hu₀
    have hcA : c ∈ A := (Finset.mem_filter.mp hc).1
    have hc0 : c ≠ 0 := fun h ↦ h₀ (h ▸ hcA)
    have hqc : q ∣ c := (Finset.mem_filter.mp hc).2
    rw [← hcu]
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hc0) hqc) hq.pos
  have hv₀pos : 0 < v₀ := by
    exact Nat.pos_of_ne_zero fun h ↦ h₀ (h ▸ (Finset.mem_filter.mp hv₀).1)
  let S₁ := U.image fun u ↦ v₀ / u
  let S₂ := (V.erase v₀).image fun v ↦ v / u₀
  have hS₁card : S₁.card = U.card := by
    dsimp only [S₁]
    rw [Finset.card_image_of_injOn]
    intro u hu w hw huw
    have huv : u ∣ v₀ := hcrossU u hu v₀ hv₀
    have hwv : w ∣ v₀ := hcrossU w hw v₀ hv₀
    have hu0 : 0 < u := by
      exact Nat.pos_of_dvd_of_pos huv hv₀pos
    have hquotpos : 0 < v₀ / u := Nat.div_pos (Nat.le_of_dvd hv₀pos huv) hu0
    change v₀ / u = v₀ / w at huw
    apply Nat.mul_left_cancel hquotpos
    calc
      (v₀ / u) * u = v₀ := Nat.div_mul_cancel huv
      _ = (v₀ / w) * w := (Nat.div_mul_cancel hwv).symm
      _ = (v₀ / u) * w := congrArg (fun z ↦ z * w) huw.symm
  have hS₂card : S₂.card = V.card - 1 := by
    dsimp only [S₂]
    rw [Finset.card_image_of_injOn]
    · rw [Finset.card_erase_of_mem hv₀]
    · intro v hv w hw hvw
      have hvV : v ∈ V := Finset.mem_of_mem_erase hv
      have hwV : w ∈ V := Finset.mem_of_mem_erase hw
      have huv : u₀ ∣ v := hcrossU u₀ hu₀ v hvV
      have huw : u₀ ∣ w := hcrossU u₀ hu₀ w hwV
      change v / u₀ = w / u₀ at hvw
      calc
        v = (v / u₀) * u₀ := (Nat.div_mul_cancel huv).symm
        _ = (w / u₀) * u₀ := congrArg (fun z ↦ z * u₀) hvw
        _ = w := Nat.div_mul_cancel huw
  have hSdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx₁
    obtain ⟨v, hv, huvEq⟩ := Finset.mem_image.mp hx₂
    have hvV : v ∈ V := Finset.mem_of_mem_erase hv
    have hvne : v ≠ v₀ := (Finset.mem_erase.mp hv).1
    have hv₀lt : v₀ < v := (V.min'_le v hvV).lt_of_ne (Ne.symm hvne)
    have hu₀le : u₀ ≤ u := U.min'_le u hu
    have huv₀ : u ∣ v₀ := hcrossU u hu v₀ hv₀
    have hu₀v : u₀ ∣ v := hcrossU u₀ hu₀ v hvV
    have hvle : v ≤ v₀ := by
      calc
        v = (v / u₀) * u₀ := (Nat.div_mul_cancel hu₀v).symm
        _ = (v₀ / u) * u₀ := by rw [huvEq]
        _ ≤ (v₀ / u) * u := Nat.mul_le_mul_left (v₀ / u) hu₀le
        _ = v₀ := Nat.div_mul_cancel huv₀
    exact (not_le_of_gt hv₀lt) hvle
  let R := S₁ ∪ S₂
  have hRcard : R.card = A.card - 1 := by
    dsimp only [R]
    rw [Finset.card_union_of_disjoint hSdisj, hS₁card, hS₂card, hUcard]
    have hVpos : 0 < V.card := Finset.card_pos.mpr hVne
    omega
  let T := (Finset.Ico 1 A.card).erase q
  have hratio_mem_T : ∀ u ∈ U, ∀ v ∈ V, v / u ∈ T := by
    intro u hu v hv
    have huv : u ∣ v := hcrossU u hu v hv
    have hvA : v ∈ A := (Finset.mem_filter.mp hv).1
    have hv0 : v ≠ 0 := fun h ↦ h₀ (h ▸ hvA)
    have hu0 : 0 < u := Nat.pos_of_dvd_of_pos huv (Nat.pos_of_ne_zero hv0)
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_Ico.mpr ⟨?_, ?_⟩⟩
    · intro heq
      have hqratio : q ∣ v / u := heq ▸ dvd_refl q
      have hqv : q ∣ v := by
        rw [← Nat.div_mul_cancel huv]
        exact dvd_mul_of_dvd_left hqratio u
      exact (Finset.mem_filter.mp hv).2 hqv
    · exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hv0) huv) hu0
    · obtain ⟨c, hc, hcu⟩ := Finset.mem_image.mp hu
      have hcA : c ∈ A := (Finset.mem_filter.mp hc).1
      have hc0 : c ≠ 0 := fun h ↦ h₀ (h ▸ hcA)
      have hqc : q ∣ c := (Finset.mem_filter.mp hc).2
      have hg : c.gcd v = u := by
        have hgprod : q * c.gcd v = c := by
          have hgpos : 0 < c.gcd v := Nat.gcd_pos_of_pos_left v (Nat.pos_of_ne_zero hc0)
          have hqv : ¬q ∣ v := (Finset.mem_filter.mp hv).2
          have hqg : ¬q ∣ c.gcd v := fun h ↦ hqv (h.trans (Nat.gcd_dvd_right c v))
          have hqquot : q ∣ c / c.gcd v := by
            have hp : q ∣ (c / c.gcd v) * c.gcd v := by
              rw [Nat.div_mul_cancel (Nat.gcd_dvd_left c v)]
              exact hqc
            exact (hq.dvd_mul.mp hp).resolve_right hqg
          have hquotpos : 0 < c / c.gcd v :=
            Nat.div_pos (Nat.gcd_le_left v (Nat.pos_of_ne_zero hc0)) hgpos
          have hquotlt := div_gcd_lt_card_of_not_grahamBound A hbad hcA hvA hc0
          obtain ⟨k, hk⟩ := hqquot
          have hkpos : 0 < k := Nat.pos_of_mul_pos_left (hk ▸ hquotpos)
          have hkone : k = 1 := by
            by_contra hk1
            have hk2 : 2 ≤ k := by omega
            have htwo : 2 * q ≤ c / c.gcd v := by
              calc
                2 * q = q * 2 := Nat.mul_comm 2 q
                _ ≤ q * k := Nat.mul_le_mul_left q hk2
                _ = c / c.gcd v := hk.symm
            omega
          have hquoteq : c / c.gcd v = q := by simpa [hkone] using hk
          calc
            q * c.gcd v = (c / c.gcd v) * c.gcd v := by rw [hquoteq]
            _ = c := Nat.div_mul_cancel (Nat.gcd_dvd_left c v)
        have hcprod : q * (c / q) = c := by
          simpa [mul_comm] using Nat.mul_div_cancel' hqc
        have hgg : c.gcd v = c / q :=
          Nat.mul_left_cancel hq.pos (hgprod.trans hcprod.symm)
        simpa [hcu] using hgg
      have hlt := div_gcd_lt_card_of_not_grahamBound A hbad hvA hcA hv0
      rw [Nat.gcd_comm v c, hg] at hlt
      exact hlt
  have hRsub : R ⊆ T := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      exact hratio_mem_T u hu v₀ hv₀
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      exact hratio_mem_T u₀ hu₀ v (Finset.mem_of_mem_erase hv)
  have hqT : q ∈ Finset.Ico 1 A.card := Finset.mem_Ico.mpr ⟨hq.one_le, hqn⟩
  have hTcard : T.card = A.card - 2 := by
    dsimp only [T]
    rw [Finset.card_erase_of_mem hqT, Nat.card_Ico]
    omega
  have hRupper : R.card ≤ A.card - 2 :=
    (Finset.card_le_card hRsub).trans_eq hTcard
  omega

private lemma lcm_div_gcd_eq (a : ℕ) (ha : a ≠ 0) (S : Finset ℕ) :
    S.lcm (fun b ↦ a / a.gcd b) = a / a.gcd (S.gcd id) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Nat.div_self (Nat.pos_of_ne_zero ha)]
  | @insert b S hb ih =>
      rw [Finset.lcm_insert, Finset.gcd_insert, ih]
      change Nat.lcm (a / a.gcd b) (a / a.gcd (S.gcd id)) =
        a / a.gcd (b.gcd (S.gcd id))
      rw [Nat.div_lcm_eq_div_gcd (Nat.gcd_dvd_left a b)
        (Nat.gcd_dvd_left a (S.gcd id))]
      have hden : (a.gcd b).gcd (a.gcd (S.gcd id)) =
          a.gcd (b.gcd (S.gcd id)) := by
        rw [Nat.gcd_assoc, Nat.gcd_left_comm b a (S.gcd id), ← Nat.gcd_assoc,
          Nat.gcd_self]
      rw [hden]

private lemma dvd_lcm_Ico_of_not_grahamBound (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ (∃ a ∈ A, ∃ b ∈ A, A.card * a.gcd b ≤ a)) {a : ℕ} (ha : a ∈ A) :
    a ∣ (Finset.Ico 1 A.card).lcm id := by
  classical
  have ha0 : a ≠ 0 := fun h ↦ h₀ (h ▸ ha)
  have hquot : ∀ b ∈ A, a / a.gcd b ∈ Finset.Ico 1 A.card := by
    intro b hb
    have hgpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
    have hqpos : 0 < a / a.gcd b :=
      Nat.div_pos (Nat.gcd_le_left b (Nat.pos_of_ne_zero ha0)) hgpos
    have hlt : a / a.gcd b < A.card := by
      rw [Nat.div_lt_iff_lt_mul hgpos]
      exact Nat.lt_of_not_ge fun hle ↦ hbad ⟨a, ha, b, hb, by simpa [mul_comm] using hle⟩
    exact Finset.mem_Ico.mpr ⟨hqpos, hlt⟩
  have hlcm : A.lcm (fun b ↦ a / a.gcd b) ∣ (Finset.Ico 1 A.card).lcm id :=
    Finset.lcm_dvd fun b hb ↦ Finset.dvd_lcm (hquot b hb)
  rw [lcm_div_gcd_eq a ha0 A, hgcd, Nat.gcd_one_right, Nat.div_one] at hlcm
  exact hlcm

lemma squarefree_case (A : Finset ℕ) (hA : A.Nonempty)
    (hsq : ∀ a ∈ A, Squarefree a) :
    ∃ a ∈ A, ∃ b ∈ A, A.card * a.gcd b ≤ a := by
  classical
  let f (k : ℕ) := if hk : k < A.card then A.orderEmbOfFin rfl ⟨k,hk⟩ else 0
  have hf (k : ℕ) (hk : k < A.card) : f k = A.orderEmbOfFin rfl ⟨k,hk⟩ := by
    simp [f,hk]
  have hm : StrictMonoOn f (Set.Iio A.card) := by
    intro i hi j hj hij
    rw [hf i hi,hf j hj]
    exact (A.orderEmbOfFin rfl).strictMono hij
  have hs (k : ℕ) (hk : k < A.card) : Squarefree (f k) := by
    rw [hf k hk]
    exact hsq _ (A.orderEmbOfFin_mem rfl ⟨k,hk⟩)
  obtain ⟨i,hi,j,hj,h⟩ := Nat.grahamConjecture_of_squarefree f hs
    (Finset.card_ne_zero.mpr hA) hm
  refine ⟨A.orderEmbOfFin rfl ⟨i,hi⟩,A.orderEmbOfFin_mem rfl ⟨i,hi⟩,
    A.orderEmbOfFin rfl ⟨j,hj⟩,A.orderEmbOfFin_mem rfl ⟨j,hj⟩,?_⟩
  simpa [hf i hi,hf j hj,mul_comm] using h

def H1 : Prop := ∀ A : Finset ℕ, 0 ∉ A → A.gcd id = 1 →
  4 ≤ A.card → A.card ≤ 7000 → ¬ A.card.Prime →
  (¬ ∀ a ∈ A, Squarefree a) →
  (∀ a ∈ A, a ∣ (Finset.Ico 1 A.card).lcm id) →
  (∀ a ∈ A, ∀ p : ℕ, p.Prime → p ∣ a → 2*p < A.card) →
  ∃ a ∈ A, ∃ b ∈ A, A.card * a.gcd b ≤ a

def H2 : Prop := ∀ A : Finset ℕ, 0 ∉ A → A.gcd id = 1 →
  7001 ≤ A.card → ¬ A.card.Prime →
  (¬ ∀ a ∈ A, Squarefree a) →
  (∀ a ∈ A, a ∣ (Finset.Ico 1 A.card).lcm id) →
  (∀ a ∈ A, ∀ p : ℕ, p.Prime → p ∣ a → 2*p < A.card) →
  ∃ a ∈ A, ∃ b ∈ A, A.card * a.gcd b ≤ a

theorem main : H1 → H2 → type_of% @Erdos402.erdos_402 := by
  intro small large A h0 hA
  let g := A.gcd id
  have gp : 0 < g := Glue.gcd_pos A h0 hA
  let B := A.image (fun a => a/g)
  have B0 : 0 ∉ B := Glue.image_zero_not_mem A h0 rfl gp
  have Bne : B.Nonempty := Glue.image_nonempty A hA g
  have Bcard : B.card = A.card := Glue.image_card A rfl
  have Bgcd : B.gcd id = 1 := Glue.image_gcd_eq_one A h0 hA rfl gp
  have bound : ∃ a ∈ B, ∃ b ∈ B, B.card*a.gcd b ≤ a := by
    by_contra bad
    have notprime : ¬ B.card.Prime := fun hp => bad (grahamBound_of_prime_card B B0 hp)
    have notsq : ¬ ∀ a ∈ B, Squarefree a := fun hs => bad (squarefree_case B Bne hs)
    have card4 : 4 ≤ B.card := by
      have cp := Finset.card_pos.mpr Bne
      have cn1 : B.card ≠ 1 := by
        intro hc
        obtain ⟨a,ha⟩ := Bne
        exact bad ⟨a,ha,a,ha,by simp [hc]⟩
      have cn2 : B.card ≠ 2 := fun h => notprime (h ▸ Nat.prime_two)
      have cn3 : B.card ≠ 3 := fun h => notprime (h ▸ Nat.prime_three)
      omega
    have divides : ∀ a ∈ B, a ∣ (Finset.Ico 1 B.card).lcm id :=
      fun a ha => dvd_lcm_Ico_of_not_grahamBound B B0 Bgcd bad ha
    have smooth : ∀ a ∈ B, ∀ p : ℕ, p.Prime → p ∣ a → 2*p < B.card := by
      intro a ha p hp hpa
      by_contra! h
      exact prime_not_dvd_of_card_le_two_mul B B0 Bgcd bad hp h ha hpa
    by_cases hc : B.card ≤ 7000
    · exact bad (small B B0 Bgcd card4 hc notprime notsq divides smooth)
    · exact bad (large B B0 Bgcd (by omega) notprime notsq divides smooth)
  apply Glue.transfer A rfl gp Bcard
  obtain ⟨a,ha,b,hb,h⟩ := bound
  refine ⟨a,ha,b,hb,?_⟩
  apply (le_div_iff₀ (by exact_mod_cast Finset.card_pos.mpr Bne : (0:ℚ)<B.card)).mpr
  exact_mod_cast (show a.gcd b * B.card ≤ a by simpa [mul_comm] using h)

end OMA.R_Erdos402_erdos_402_R2
