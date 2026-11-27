import OMAReductions.R_Erdos44_erdos_44_R1

/-!
An affine Ruzsa graph modulo p(p-1) hits a prescribed seed precisely when
the powers of a primitive root at the prescribed exponents lie on the required
affine line. For three distinct points this is one polynomial equation in the
generator. Sieve the prime divisors of its multiplicative index in two stages.
The finite construction below adapts the CRT argument in the parent reduction
by marcusbuffett, originally based on ldy985's Ruzsa construction.
-/

namespace OMA.R_Erdos44_erdos_44_R1_H1_R1
open Finset Filter

open scoped Classical

/-- Positive lower density for each finite collection of index obstructions,
with a lower bound independent of the finite sieve cutoff. -/
def H1 : Prop :=
  ∀ A : Finset ℕ, 0 ∉ A → IsSidon (A : Set ℕ) → A.card = 3 →
  let fits (q : ℕ) (g : (ZMod (q+1))ˣ) : Prop :=
    ∃ C D : ZMod (q+1), D ≠ 0 ∧ ∀ x ∈ A,
    C + D * ((g ^ (x-1) : (ZMod (q+1))ˣ) : ZMod (q+1)) = x
  let sifted (q K : ℕ) (g : (ZMod (q+1))ˣ) : Prop :=
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≤ K → ¬ ℓ ∣ q / orderOf g
  let primeRange (X : ℕ) := (range X).filter fun q => (q+1).Prime
  let candidates (B K X : ℕ) := (primeRange X).filter fun q =>
    B ≤ q ∧ ∃ g, fits q g ∧ sifted q K g
  ∃ C : ℕ, 0 < C ∧ ∀ K B : ℕ, ∀ᶠ X : ℕ in atTop,
      (primeRange X).card ≤ C * (candidates B K X).card

/-- The proportion of compatible primes lost to a large index factor can
be made arbitrarily small along a sequence of counting cutoffs. -/
def H2 : Prop :=
  ∀ A : Finset ℕ, 0 ∉ A → IsSidon (A : Set ℕ) → A.card = 3 →
  let fits (q : ℕ) (g : (ZMod (q+1))ˣ) : Prop :=
    ∃ C D : ZMod (q+1), D ≠ 0 ∧ ∀ x ∈ A,
    C + D * ((g ^ (x-1) : (ZMod (q+1))ˣ) : ZMod (q+1)) = x
  let sifted (q K : ℕ) (g : (ZMod (q+1))ˣ) : Prop :=
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≤ K → ¬ ℓ ∣ q / orderOf g
  let primeRange (X : ℕ) := (range X).filter fun q => (q+1).Prime
  let exceptional (K X : ℕ) := (primeRange X).filter fun q =>
    ∃ g, fits q g ∧ sifted q K g ∧ ∃ ℓ : ℕ, ℓ.Prime ∧ K < ℓ ∧ ℓ ∣ q / orderOf g
  ∀ C : ℕ, 0 < C → ∃ K : ℕ, ∃ᶠ X : ℕ in atTop,
      C * (exceptional K X).card < (primeRange X).card

theorem generator {A : Finset ℕ} (hz : 0 ∉ A) (hs : IsSidon (A : Set ℕ))
    (hc : A.card = 3) (h₁ : H1) (h₂ : H2) (B : ℕ) :
    ∃ q ≥ B, (q+1).Prime ∧ ∃ g : (ZMod (q+1))ˣ, orderOf g = q ∧ ∃ C D : ZMod (q+1), D ≠ 0 ∧ ∀ x ∈ A,
    C + D * ((g ^ (x-1) : (ZMod (q+1))ˣ) : ZMod (q+1)) = x := by
  classical
  let fits (q : ℕ) (g : (ZMod (q+1))ˣ) : Prop :=
    ∃ C D : ZMod (q+1), D ≠ 0 ∧ ∀ x ∈ A,
    C + D * ((g ^ (x-1) : (ZMod (q+1))ˣ) : ZMod (q+1)) = x
  let sifted (q K : ℕ) (g : (ZMod (q+1))ˣ) : Prop :=
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≤ K → ¬ ℓ ∣ q / orderOf g
  let primeRange (X : ℕ) := (range X).filter fun q => (q+1).Prime
  let candidates (B K X : ℕ) := (primeRange X).filter fun q =>
    B ≤ q ∧ ∃ g, fits q g ∧ sifted q K g
  let exceptional (K X : ℕ) := (primeRange X).filter fun q =>
    ∃ g, fits q g ∧ sifted q K g ∧ ∃ ℓ : ℕ, ℓ.Prime ∧ K < ℓ ∧ ℓ ∣ q / orderOf g
  obtain ⟨C,hC,hfinite⟩ := h₁ A hz hs hc
  obtain ⟨K,htail⟩ := h₂ A hz hs hc C hC
  obtain ⟨X,ht,hf⟩ := (htail.and_eventually (hfinite K B)).exists
  change C * (exceptional K X).card < (primeRange X).card at ht
  change (primeRange X).card ≤ C * (candidates B K X).card at hf
  have hlt : (exceptional K X).card < (candidates B K X).card := by
    by_contra! hn
    exact (not_lt_of_ge (hf.trans (Nat.mul_le_mul_left C hn))) ht
  obtain ⟨q,hq,hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  change q ∈ (primeRange X).filter (fun q => B ≤ q ∧ ∃ g, fits q g ∧ sifted q K g) at hq
  obtain ⟨hpRange,hB,g,hfit,hsift⟩ := Finset.mem_filter.mp hq
  have hp : (q+1).Prime := (Finset.mem_filter.mp hpRange).2
  haveI : Fact (q+1).Prime := ⟨hp⟩
  have hd : orderOf g ∣ q := by
    simpa only [Nat.card_eq_fintype_card,ZMod.card_units,Nat.add_sub_cancel] using orderOf_dvd_natCard g
  refine ⟨q,hB,hp,g,?_,hfit⟩
  have hindex : q / orderOf g = 1 := by
    by_contra hi
    obtain ⟨ℓ,hℓ,hdvd⟩ := Nat.exists_prime_and_dvd hi
    have hlarge : K < ℓ := lt_of_not_ge fun h => hsift ℓ hℓ h hdvd
    apply hnot
    exact Finset.mem_filter.mpr ⟨hpRange,g,hfit,hsift,ℓ,hℓ,hlarge,hdvd⟩
  have hprod := Nat.div_mul_cancel hd
  simpa only [hindex,one_mul] using hprod

private theorem anchored {A : Finset ℕ} {q : ℕ} (hp : (q+1).Prime)
    (hA : A ⊆ Icc 1 q) {g : (ZMod (q+1))ˣ} (hg : orderOf g = q)
    (hf : ∃ C D : ZMod (q+1), D ≠ 0 ∧ ∀ x ∈ A,
    C + D * ((g ^ (x-1) : (ZMod (q+1))ˣ) : ZMod (q+1)) = x) :
    ∃ S : Finset ℕ, S ⊆ Icc 1 ((q+1)*q) ∧ IsSidon (S : Set ℕ) ∧ S.card=q ∧ A ⊆ S := by
  haveI : Fact (q+1).Prime := ⟨hp⟩
  obtain ⟨C,D,hD,hline⟩ := hf
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ZMod (q + 1), ∀ i, u i = ((g ^ i : (ZMod (q + 1))ˣ) : ZMod (q + 1)) :=
    ⟨_, fun _ => rfl⟩
  have hu_inj : ∀ a b, a < q → b < q → u a = u b → a = b := by
    intro a b ha hb hab
    rw [hu, hu] at hab
    have h1 : g ^ a = g ^ b := Units.ext hab
    have h2 : a ≡ b [MOD orderOf g] := pow_eq_pow_iff_modEq.1 h1
    rw [hg] at h2
    exact Nat.ModEq.eq_of_lt_of_lt h2 ha hb
  let v (i : ℕ) := C+D*u i
  obtain ⟨k, hk⟩ : ∃ k : ℕ → ℕ, ∀ i, k i = (1+i + (q + 1) - (v i).val) % (q + 1) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, ∀ i, f i = 1 + i + q * k i := ⟨_, fun _ => rfl⟩
  have hk_lt : ∀ i, k i < q + 1 := fun i => by
    rw [hk]
    exact Nat.mod_lt _ (Nat.succ_pos q)
  have hqcast : ((q : ℕ) : ZMod (q + 1)) = -1 := by
    have h0 : ((q + 1 : ℕ) : ZMod (q + 1)) = 0 := ZMod.natCast_self (q + 1)
    push_cast at h0
    linear_combination h0
  have hkcast : ∀ i, ((k i : ℕ) : ZMod (q + 1)) = 1+(i : ZMod (q + 1)) - v i := by
    intro i
    have hval : (v i).val ≤ 1+i + (q + 1) := (ZMod.val_lt (v i)).le.trans (Nat.le_add_left _ _)
    have h0 : ((q + 1 : ℕ) : ZMod (q + 1)) = 0 := ZMod.natCast_self (q + 1)
    rw [hk, ZMod.natCast_mod, Nat.cast_sub hval, Nat.cast_add, h0, ZMod.natCast_zmod_val]
    push_cast
    ring
  have hfcast : ∀ i, ((f i : ℕ) : ZMod (q + 1)) = v i := by
    intro i
    rw [hf]
    push_cast
    rw [hqcast, hkcast]
    ring
  have hf_mod : ∀ i, f i % q = (1 + i) % q := by
    intro i
    rw [hf]
    exact Nat.add_mul_mod_self_left _ _ _
  have hit (j z : ℕ) (hj : j<q) (hz : z<q+1) (he : j+1=z) (hv : v j=z) :
      z ∈ (Finset.range q).image f := by
    refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, ?_⟩
    have hval : (v j).val=z := by rw [hv,ZMod.val_natCast,Nat.mod_eq_of_lt hz]
    rw [hf,hk,hval,show 1+j+(q+1)-z=q+1 by omega,Nat.mod_self]
    omega
  refine ⟨(Finset.range q).image f, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    have hi' := Finset.mem_range.1 hi
    have hki := hk_lt i
    rw [Finset.mem_Icc, hf]
    refine ⟨by omega, ?_⟩
    have h1 : q * k i ≤ q * q := Nat.mul_le_mul_left q (by omega)
    have h2 : (q + 1) * q = q * q + q := by ring
    omega
  · intro x hx y hy z hz w hw hsum
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hz)
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hw)
    have ha' := Finset.mem_range.1 ha
    have hb' := Finset.mem_range.1 hb
    have hc' := Finset.mem_range.1 hc
    have hd' := Finset.mem_range.1 hd
    -- the sum of the exponents is determined modulo q
    have hmod : a + c ≡ b + d [MOD q] := by
      have e : a + c + q * (k a + k c + 0) + 2 = b + d + q * (k b + k d + 0) + 2 := by
        have := hsum
        rw [hf a, hf b, hf c, hf d] at this
        simp only [Nat.mul_add, Nat.add_zero]
        omega
      have e' : a + c + q * (k a + k c + 0) = b + d + q * (k b + k d + 0) := by omega
      have e2 := congrArg (· % q) e'
      simp only [Nat.add_mul_mod_self_left] at e2
      exact e2
    have hgpow : g ^ (a + c) = g ^ (b + d) := pow_eq_pow_iff_modEq.2 (by rw [hg]; exact hmod)
    have hprod : u a * u c = u b * u d := by
      rw [hu, hu, hu, hu, ← Units.val_mul, ← Units.val_mul, ← pow_add, ← pow_add, hgpow]
    have hadd : u a + u c = u b + u d := by
      have e := congrArg (Nat.cast : ℕ → ZMod (q + 1)) hsum
      rw [Nat.cast_add, Nat.cast_add, hfcast, hfcast, hfcast, hfcast] at e
      apply mul_left_cancel₀ hD
      dsimp only [v] at e
      linear_combination e
    have hzero : (u a - u b) * (u a - u d) = 0 := by
      linear_combination (u a) * hadd - hprod
    rcases mul_eq_zero.1 hzero with h | h
    · have hab : a = b := hu_inj a b ha' hb' (sub_eq_zero.1 h)
      have hcd : c = d := by
        apply hu_inj c d hc' hd'
        rw [hab] at hadd
        exact add_left_cancel hadd
      exact Or.inl ⟨by rw [hab], by rw [hcd]⟩
    · have had : a = d := hu_inj a d ha' hd' (sub_eq_zero.1 h)
      have hcb : c = b := by
        apply hu_inj c b hc' hb'
        rw [had] at hadd
        have : u d + u c = u d + u b := by rw [hadd]; ring
        exact add_left_cancel this
      exact Or.inr ⟨by rw [had], by rw [hcb]⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have hi' : i < q := Finset.mem_range.1 (Finset.mem_coe.1 hi)
    have hj' : j < q := Finset.mem_range.1 (Finset.mem_coe.1 hj)
    have h1 : (1 + i) % q = (1 + j) % q := by rw [← hf_mod, ← hf_mod, hij]
    have h2 : (1 + i) ≡ (1 + j) [MOD q] := h1
    have h3 : i ≡ j [MOD q] := Nat.ModEq.add_left_cancel' 1 h2
    exact Nat.ModEq.eq_of_lt_of_lt h3 hi' hj'

  · intro x hx
    have hbounds := Finset.mem_Icc.mp (hA hx)
    apply hit (x-1) x (by omega) (by omega) (by omega)
    simpa only [v,hu] using hline x hx

theorem main : H1 → H2 → OMA.R_Erdos44_erdos_44_R1.H1 := by
  intro h₁ h₂ A hz hs hc δ hδ L
  obtain ⟨K,hK⟩ := exists_nat_gt (1/δ)
  obtain ⟨q,hqB,hp,g,hg,hfit⟩ := generator hz hs hc h₁ h₂ (K+A.sup id+L+1)
  have hA : A ⊆ Icc 1 q := by
    intro x hx
    have hle : x ≤ A.sup id := Finset.le_sup (f := id) hx
    exact Finset.mem_Icc.mpr ⟨by by_contra! hn; exact hz (by simpa [show x=0 by omega] using hx), by omega⟩
  obtain ⟨S,hsub,hsid,hcard,hAS⟩ := anchored hp hA hg hfit
  have hbig : q ≤ (q+1)*q := Nat.le_mul_of_pos_left q (by omega)
  refine ⟨(q+1)*q,by omega,S,hsub,hAS,hsid,?_⟩
  rw [hcard]
  have hroot : Real.sqrt ((q+1)*q : ℕ) ≤ (q+1:ℕ) := by
    apply (Real.sqrt_le_iff).2
    push_cast
    constructor <;> nlinarith
  by_cases hd : 1 ≤ δ
  · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _)).trans (by positivity)
  have hbound : 1 ≤ δ*(q+1 : ℕ) := by
    have hle : 1/δ ≤ (q+1:ℕ) := hK.le.trans (by exact_mod_cast (by omega : K ≤ q+1))
    exact (div_le_iff₀ hδ).mp hle |> fun h => by simpa [mul_comm] using h
  have h := mul_le_mul_of_nonneg_left hroot (by linarith : 0 ≤ 1-δ)
  push_cast at h hbound ⊢
  linarith

end OMA.R_Erdos44_erdos_44_R1_H1_R1
