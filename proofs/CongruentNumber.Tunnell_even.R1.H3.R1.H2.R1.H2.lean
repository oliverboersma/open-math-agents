import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1
import Mathlib

/-!
# Fourier evaluation of the finite winding and lattice sums

Primary Gaussian integer coefficients give the Euler factors of the conductor-32 form.
The primitive character twist gives a sum of paired integrals at rational cusps. Fricke
inversion and translation compute their real modular symbols by nearest-integer descent.
The sine product at a primitive root identifies the positive square root in the Gauss-sum
sign test. Dissection of the three theta series and the two ternary congruence conditions
give the individual Fourier evaluations.
-/

section

/-
# The base curve and its eta product

The coefficients of η(4z)²η(8z)² are sums of primary Gaussian integers of
fixed norm. Finite Gaussian binomial identities prove the theta expansion,
including Jacobi's cubic identity by differentiation. Coprime factorization
and prime-power recurrences on the Gaussian integers give the Hecke relations.
For split primes the quartic Jacobi sum has norm p, and the rational subgroup
of order eight determines the primary generator giving the Frobenius trace.
-/

/- Primary generators in the Gaussian coefficient formula for η(4τ)²η(8τ)². -/

namespace TunnellGaussian

open GaussianInt

def Primary (z : GaussianInt) : Prop := (⟨2,2⟩ : GaussianInt) ∣ z-1

lemma primary_iff (z : GaussianInt) :
    Primary z ↔ z.im % 2 = 0 ∧ (z.re + z.im) % 4 = 1 := by
  constructor
  · rintro ⟨⟨u,v⟩,h⟩
    have ha := congrArg Zsqrtd.re h
    have hb := congrArg Zsqrtd.im h
    change z.re - 1 = 2*u + -1*2*v at ha
    change z.im - 0 = 2*v + 2*u at hb
    omega
  · rintro ⟨h₁,h₂⟩
    refine ⟨⟨(z.re + z.im - 1)/4, (z.im - z.re + 1)/4⟩, ?_⟩
    ext
    · change z.re - 1 = 2*((z.re + z.im - 1)/4) + -1*2*((z.im - z.re + 1)/4)
      omega
    · change z.im - 0 = 2*((z.im - z.re + 1)/4) + 2*((z.re + z.im - 1)/4)
      omega

lemma primary_mul_iff {z w : GaussianInt} (hz : Primary z) : Primary (z*w) ↔ Primary w := by
  have h : (⟨2,2⟩ : GaussianInt) ∣ (z-1)*w := dvd_mul_of_dvd_left hz _
  unfold Primary
  rw [show z*w - 1 = (z-1)*w + (w-1) by ring, dvd_add_right h]

lemma primary_star {z : GaussianInt} (hz : Primary z) : Primary (star z) := by
  rw [primary_iff] at hz ⊢
  change (-z.im) % 2 = 0 ∧ (z.re - z.im) % 4 = 1
  omega

lemma norm_sq (z : GaussianInt) : z.norm = z.re^2 + z.im^2 := by rw [Zsqrtd.norm_def]; ring

lemma units_cases {u : GaussianInt} (hu : IsUnit u) :
    (u.re = 1 ∧ u.im = 0) ∨ (u.re = -1 ∧ u.im = 0) ∨
    (u.re = 0 ∧ u.im = 1) ∨ (u.re = 0 ∧ u.im = -1) := by
  have h := (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) u).mpr hu
  rw [norm_sq] at h
  have hr : -1 ≤ u.re ∧ u.re ≤ 1 := by constructor <;> nlinarith [sq_nonneg (u.re+1), sq_nonneg (u.re-1), sq_nonneg u.im]
  have hi : -1 ≤ u.im ∧ u.im ≤ 1 := by constructor <;> nlinarith [sq_nonneg (u.im+1), sq_nonneg (u.im-1), sq_nonneg u.re]
  obtain ⟨hr₁, hr₂⟩ := hr
  obtain ⟨hi₁, hi₂⟩ := hi
  interval_cases h₁ : u.re <;> interval_cases h₂ : u.im <;> simp_all

lemma primary_unit_eq_one {u : GaussianInt} (h : Primary u) (hu : IsUnit u) : u = 1 := by
  have h' := (primary_iff _).mp h
  rcases units_cases hu with h | h | h | h <;> rcases h with ⟨hr, hi⟩ <;> simp [hr,hi] at h'
  ext <;> assumption

lemma primary_associated_eq {z w : GaussianInt} (hz : Primary z) (hw : Primary w) (h : Associated z w) :
    z = w := by
  obtain ⟨u,rfl⟩ := h
  rw [primary_unit_eq_one ((primary_mul_iff hz).mp hw) u.isUnit, mul_one]

lemma square_mod_two (a : ℤ) : a^2 % 2 = a % 2 := by
  rw [sq, Int.mul_emod]
  rcases (show a%2 = 0 ∨ a%2 = 1 by omega) with h | h <;> rw [h] <;> decide

lemma exists_primary_associate (z : GaussianInt) (ho : z.norm % 2 = 1) :
    ∃ w : GaussianInt, Primary w ∧ Associated w z := by
  rw [norm_sq, Int.add_emod, square_mod_two, square_mod_two] at ho
  have orient (v : GaussianInt) (hi : v.im % 2 = 0) (hr : v.re % 2 = 1) :
      ∃ w : GaussianInt, Primary w ∧ Associated w v := by
    by_cases hs : (v.re + v.im) % 4 = 1
    · exact ⟨v, (primary_iff _).mpr ⟨hi,hs⟩, Associated.refl _⟩
    · refine ⟨-v, (primary_iff _).mpr ?_, ?_⟩
      · change (-v.im)%2 = 0 ∧ (-v.re + -v.im)%4 = 1
        omega
      · simpa using associated_mul_unit_left v (-1) (isUnit_neg.mpr isUnit_one)
  by_cases he : z.im % 2 = 0
  · exact orient _ he (by omega)
  · let i : GaussianInt := ⟨0,1⟩
    have hu : IsUnit i := (Zsqrtd.norm_eq_one_iff' (by decide : (-1:ℤ) ≤ 0) i).mp (by decide)
    obtain ⟨w,hw,hwz⟩ := orient (z*i)
      (by change (z.re * 1 + z.im * 0)%2 = 0; omega)
      (by change (z.re * 0 + -1*z.im*1)%2 = 1; omega)
    exact ⟨w,hw,hwz.trans (associated_mul_unit_left z i hu)⟩

lemma primary_odd_norm {z : GaussianInt} (h : Primary z) : z.norm % 2 = 1 := by
  rw [norm_sq, Int.add_emod, square_mod_two, square_mod_two]
  have := (primary_iff _).mp h
  omega

lemma coprime_of_norms {z w : GaussianInt} (hc : Nat.Coprime z.norm.natAbs w.norm.natAbs) :
    IsCoprime z w := by
  have h := hc.isCoprime.map (Int.castRingHom GaussianInt)
  have hz : z ∣ (z.norm.natAbs : GaussianInt) := by
    rw [GaussianInt.natCast_natAbs_norm, Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right _ _
  have hw : w ∣ (w.norm.natAbs : GaussianInt) := by
    rw [GaussianInt.natCast_natAbs_norm, Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right _ _
  apply IsCoprime.of_isCoprime_of_dvd_right _ hw
  apply IsCoprime.of_isCoprime_of_dvd_left _ hz
  simpa using h

lemma norm_dvd_sq {z : GaussianInt} {m : ℕ} (h : z ∣ (m : GaussianInt)) :
    z.norm.natAbs ∣ m^2 := by
  obtain ⟨w,hw⟩ := h
  refine ⟨w.norm.natAbs, ?_⟩
  have he := congrArg (fun t : GaussianInt => t.norm.natAbs) hw
  simpa [sq, Int.natAbs_mul] using he

lemma scalar_split {a b m n : ℕ} (h : m.Coprime n) (ha : a ∣ m^2) (hb : b ∣ n^2)
    (he : a*b = m*n) : a = m := by
  apply Nat.dvd_antisymm
  · apply ((h.pow_left 2).coprime_dvd_left ha).dvd_of_dvd_mul_right
    rw [← he]
    exact dvd_mul_right _ _
  · apply ((h.pow_right 2).coprime_dvd_right hb).dvd_of_dvd_mul_right
    rw [he]
    exact dvd_mul_right _ _

lemma primary_factor {z : GaussianInt} {m n : ℕ} (hz : Primary z) (hc : m.Coprime n)
    (hn : z.norm.natAbs = m*n) :
    ∃ v w : GaussianInt, Primary v ∧ Primary w ∧ v.norm.natAbs = m ∧ w.norm.natAbs = n ∧ z = v*w := by
  have hd : z ∣ (m : GaussianInt)*(n : GaussianInt) := by
    rw [← Nat.cast_mul, ← hn, GaussianInt.natCast_natAbs_norm, Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right _ _
  obtain ⟨v,w,hv,hw,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  simp only [Zsqrtd.norm_mul, Int.natAbs_mul] at hn
  have hvm := scalar_split hc (norm_dvd_sq hv) (norm_dvd_sq hw) hn
  have hwn := scalar_split hc.symm (norm_dvd_sq hw) (norm_dvd_sq hv)
    (by simpa only [mul_comm] using hn)
  have ho := primary_odd_norm hz
  rw [Zsqrtd.norm_mul, Int.mul_emod] at ho
  have hvodd : v.norm % 2 = 1 := by
    by_contra he
    have e : v.norm % 2 = 0 := by omega
    simp [e] at ho
  obtain ⟨t,ht,htv⟩ := exists_primary_associate v hvodd
  have htvn := Zsqrtd.norm_eq_of_associated (by decide : (-1:ℤ) ≤ 0) htv
  obtain ⟨u,hu⟩ := htv
  have he : v*w = t*(u*w) := by rw [← hu, mul_assoc]
  have hwu := (primary_mul_iff ht).mp (he ▸ hz)
  have hun := (Zsqrtd.norm_eq_one_iff' (by decide : (-1:ℤ) ≤ 0) (u:GaussianInt)).mpr u.isUnit
  refine ⟨t, u*w, ht, hwu, by simpa only [htvn] using hvm, ?_, he⟩
  simpa only [Zsqrtd.norm_mul, hun, one_mul] using hwn

lemma primary_factor_unique {v w v' w' : GaussianInt} (hv : Primary v) (hv' : Primary v')
    (hc : Nat.Coprime v.norm.natAbs w.norm.natAbs) (hvm : v.norm.natAbs = v'.norm.natAbs)
    (hwn : w.norm.natAbs = w'.norm.natAbs) (he : v*w = v'*w') : v = v' ∧ w = w' := by
  have h₁ : v ∣ v' := (coprime_of_norms (hwn ▸ hc)).dvd_of_dvd_mul_right
    (he ▸ dvd_mul_right v w)
  have h₂ : v' ∣ v := (coprime_of_norms (hvm ▸ hc)).dvd_of_dvd_mul_right
    (he.symm ▸ dvd_mul_right v' w')
  have h := primary_associated_eq hv hv' (associated_of_dvd_dvd h₁ h₂)
  subst v'
  have h0 : v ≠ 0 := by intro e; simp [e] at hv; have := primary_odd_norm hv; simp at this
  exact ⟨rfl,mul_left_cancel₀ h0 he⟩

lemma shell_finite (n : ℕ) :
    {z : GaussianInt | Primary z ∧ z.norm.natAbs = n}.Finite := by
  let box := Set.Icc (-((n:ℤ)+1)) ((n:ℤ)+1)
  have hf : box.Finite := Set.finite_Icc _ _
  apply ((hf.prod hf).image (fun ab : ℤ × ℤ => (⟨ab.1, ab.2⟩ : GaussianInt))).subset
  rintro ⟨a,b⟩ ⟨-, hn⟩
  have h := GaussianInt.abs_natCast_norm (⟨a,b⟩ : GaussianInt)
  rw [hn, norm_sq] at h
  change (n:ℤ) = a^2 + b^2 at h
  refine ⟨(a,b), ⟨?_,?_⟩,rfl⟩
  · constructor <;> nlinarith [sq_nonneg (a-1),sq_nonneg (a+1),sq_nonneg b,sq_nonneg a]
  · constructor <;> nlinarith [sq_nonneg (b-1),sq_nonneg (b+1),sq_nonneg b,sq_nonneg a]

noncomputable def shell (n : ℕ) : Finset GaussianInt := (shell_finite n).toFinset

lemma mem_shell {z : GaussianInt} {n : ℕ} : z ∈ shell n ↔ Primary z ∧ z.norm.natAbs = n :=
  (shell_finite n).mem_toFinset

noncomputable def mass (n : ℕ) : GaussianInt := ∑ z ∈ shell n, z

theorem mass_mul {m n : ℕ} (hc : m.Coprime n) : mass (m*n) = mass m * mass n := by
  classical
  unfold mass
  simp only [Finset.sum_mul, Finset.mul_sum]
  symm
  rw [← Finset.sum_product']
  apply Finset.sum_bij (fun p _ => p.1*p.2)
  · rintro ⟨v,w⟩ hvw
    obtain ⟨hv,hw⟩ := Finset.mem_product.mp hvw
    obtain ⟨hvp,hvn⟩ := mem_shell.mp hv
    obtain ⟨hwp,hwn⟩ := mem_shell.mp hw
    exact mem_shell.mpr ⟨(primary_mul_iff hvp).mpr hwp, by simp [hvn,hwn,Int.natAbs_mul,mul_comm]⟩
  · rintro ⟨v,w⟩ hvw ⟨v',w'⟩ hvw' he
    simp only [Finset.mem_product,mem_shell] at hvw hvw'
    have h := primary_factor_unique hvw.1.1 hvw'.1.1 (by simpa only [hvw.1.2,hvw.2.2] using hc.symm)
      (hvw.1.2.trans hvw'.1.2.symm) (hvw.2.2.trans hvw'.2.2.symm) he
    exact Prod.ext h.1 h.2
  · intro z hz
    obtain ⟨hP, hn⟩ := mem_shell.mp hz
    obtain ⟨v,w,hv,hw,hvm,hwn,he⟩ := primary_factor hP hc.symm (by simpa only [mul_comm] using hn)
    exact ⟨(v,w),Finset.mem_product.mpr ⟨mem_shell.mpr ⟨hv,hvm⟩,mem_shell.mpr ⟨hw,hwn⟩⟩,he.symm⟩
  · intro p _
    exact mul_comm _ _

theorem mass_real (n : ℕ) : (mass n).im = 0 := by
  have hs : star (mass n) = mass n := by
    unfold mass
    rw [star_sum]
    apply Finset.sum_bij (fun z _ => star z)
    · intro z hz
      obtain ⟨hP,hn⟩ := mem_shell.mp hz
      exact mem_shell.mpr ⟨primary_star hP, by simpa using hn⟩
    · intro _ _ _ _ h
      exact star_injective h
    · intro z hz
      obtain ⟨hP,hn⟩ := mem_shell.mp hz
      exact ⟨star z,mem_shell.mpr ⟨primary_star hP,by simpa using hn⟩,star_star _⟩
    · intro _ _; rfl
  have := congrArg Zsqrtd.im hs
  change -(mass n).im = (mass n).im at this
  omega

theorem coefficient_mul {m n : ℕ} (hc : m.Coprime n) :
    (mass (m*n)).re = (mass m).re * (mass n).re := by simp [mass_mul hc,mass_real]

end TunnellGaussian

namespace TunnellGaussian

open GaussianInt Finset

lemma norm_product (z : GaussianInt) : z * star z = (z.norm.natAbs : GaussianInt) := by
  rw [GaussianInt.natCast_natAbs_norm, Zsqrtd.norm_eq_mul_conj]

lemma unit_of_norm_one {z : GaussianInt} (h : z.norm.natAbs = 1) : IsUnit z := by
  apply (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) z).mp
  have h' := GaussianInt.abs_natCast_norm z
  simpa [h] using h'.symm

lemma norm_prime {z : GaussianInt} {p : ℕ} (hp : p.Prime) (h : z.norm.natAbs = p) : Prime z := by
  apply Irreducible.prime
  constructor
  · intro hu
    have hn := (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) z).mpr hu
    simp [hn] at h
    exact hp.ne_one h.symm
  · intro a b hab
    rw [hab, Zsqrtd.norm_mul, Int.natAbs_mul] at h
    rcases hp.eq_one_or_self_of_dvd _ (h ▸ dvd_mul_right _ _) with hh | hh
    · exact Or.inl (unit_of_norm_one hh)
    · exact Or.inr (unit_of_norm_one (Nat.eq_of_mul_eq_mul_left hp.pos (by simpa [hh] using h)))

lemma mem_shell_image {r : GaussianInt} {p n : ℕ} (hr : Primary r) (hrn : r.norm.natAbs = p)
    (hp : 0 < p) (z : GaussianInt) :
    z ∈ (shell n).image (r * ·) ↔ z ∈ shell (p*n) ∧ r ∣ z := by
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hw, hwn⟩ := mem_shell.mp hw
    exact ⟨mem_shell.mpr ⟨(primary_mul_iff hr).mpr hw, by simp [Int.natAbs_mul, hrn, hwn]⟩,
      dvd_mul_right _ _⟩
  · rintro ⟨hz, w, rfl⟩
    obtain ⟨hz, hn⟩ := mem_shell.mp hz
    simp only [Zsqrtd.norm_mul, Int.natAbs_mul, hrn] at hn
    exact Finset.mem_image.mpr ⟨w, mem_shell.mpr ⟨(primary_mul_iff hr).mp hz,
      Nat.eq_of_mul_eq_mul_left hp hn⟩, rfl⟩

lemma shell_sum_image (r : GaussianInt) (hr : r ≠ 0) (n : ℕ) :
    ∑ z ∈ (shell n).image (r * ·), z = r * mass n := by
  rw [Finset.sum_image (by intro a _ b _ h; exact mul_left_cancel₀ hr h)]
  exact (Finset.mul_sum ..).symm

lemma norm_dvd_by_prime {p : ℕ} {r z : GaussianInt} (hr : Prime r) (hrp : r ∣ (p : GaussianInt))
    (hz : p ∣ z.norm.natAbs) : r ∣ z ∨ star r ∣ z := by
  have h : r ∣ z * star z := (norm_product z).symm ▸ hrp.trans (Nat.cast_dvd_cast hz)
  rcases hr.dvd_mul.mp h with h | h
  · exact Or.inl h
  · obtain ⟨a, ha⟩ := h
    right
    exact ⟨star a, by simpa [mul_comm] using congrArg star ha⟩

lemma split_recurrence {r : GaussianInt} {p : ℕ} (hp : p.Prime) (hr : r ∈ shell p)
    (hne : r ≠ star r) (hsm : mass p = r + star r) (k : ℕ) :
    mass (p^(k+2)) = mass p * mass (p^(k+1)) - (p : GaussianInt)*mass (p^k) := by
  classical
  obtain ⟨hP,hn⟩ := mem_shell.mp hr
  have hPs := primary_star hP
  have hns : (star r).norm.natAbs = p := by simpa using hn
  have hprime := norm_prime hp hn
  have hsprime := norm_prime hp hns
  have fact : r * star r = (p : GaussianInt) := by rw [norm_product,hn]
  have hno : ¬star r ∣ r := fun h => hne (primary_associated_eq hPs hP
    (hsprime.associated_of_dvd hprime h)).symm
  let B := (shell (p^(k+1))).image (r * ·)
  let C := (shell (p^(k+1))).image (star r * ·)
  have hmB (z : GaussianInt) : z ∈ B ↔ z ∈ shell (p^(k+2)) ∧ r ∣ z := by
    simpa only [B, pow_succ' p (k+1)] using mem_shell_image hP hn hp.pos z (n := p^(k+1))
  have hmC (z : GaussianInt) : z ∈ C ↔ z ∈ shell (p^(k+2)) ∧ star r ∣ z := by
    simpa only [C, pow_succ' p (k+1)] using mem_shell_image hPs hns hp.pos z (n := p^(k+1))
  have hUnion : B ∪ C = shell (p^(k+2)) := by
    ext z
    rw [mem_union,hmB,hmC]
    constructor
    · rintro (h|h) <;> exact h.1
    · intro hz
      have hnz := (mem_shell.mp hz).2
      rcases norm_dvd_by_prime hprime (fact ▸ dvd_mul_right r (star r)) (z := z)
          (by rw [hnz]; exact dvd_pow_self p (by omega)) with hv | hv
      · exact Or.inl ⟨hz,hv⟩
      · exact Or.inr ⟨hz,hv⟩
  have hInt : B ∩ C = (shell (p^k)).image ((p : GaussianInt) * ·) := by
    have hpP : Primary (p : GaussianInt) := fact ▸ (primary_mul_iff hP).mpr hPs
    have hpn : (p : GaussianInt).norm.natAbs = p^2 := by simp [sq, Int.natAbs_mul]
    ext z
    rw [mem_inter,hmB,hmC,mem_shell_image hpP hpn (pow_pos hp.pos 2), ← pow_add,
        add_comm 2 k]
    constructor
    · rintro ⟨⟨hz, a, rfl⟩, _, h⟩
      obtain ⟨w, rfl⟩ := (hsprime.dvd_mul.mp h).resolve_left hno
      exact ⟨hz, w, by rw [← fact, mul_assoc]⟩
    · rintro ⟨hz, h⟩
      rw [← fact] at h
      exact ⟨⟨hz,(dvd_mul_right _ _).trans h⟩,hz,(dvd_mul_left _ _).trans h⟩
  have eqn := Finset.sum_union_inter (s₁ := B) (s₂ := C) (f := fun z => z)
  rw [hUnion, hInt, shell_sum_image _ (Nat.cast_ne_zero.mpr hp.ne_zero)] at eqn
  change mass _ + _ = _ + _ at eqn
  dsimp only [B,C] at eqn
  rw [shell_sum_image _ hprime.ne_zero, shell_sum_image _ hsprime.ne_zero] at eqn
  rw [hsm, add_mul]
  exact eq_sub_of_add_eq eqn

lemma inert_recurrence (p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) (k : ℕ) :
    mass (p^(k+2)) = mass p * mass (p^(k+1)) - (p : GaussianInt)*mass (p^k) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hprime := (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p).mpr h3
  have hall (z : GaussianInt) (h : p ∣ z.norm.natAbs) : (p : GaussianInt) ∣ z := by
    rcases norm_dvd_by_prime hprime dvd_rfl h with h' | h'
    · exact h'
    · simpa using h'
  have hP : Primary (-(p : GaussianInt)) := by
    rw [primary_iff]
    change (-(0 : ℤ)) % 2 = 0 ∧ (-(p:ℤ) + -0) % 4 = 1
    omega
  have hN : (-(p : GaussianInt)).norm.natAbs = p^2 := by simp [sq, Int.natAbs_mul]
  have h0 : shell p = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨_,hn⟩ := mem_shell.mp hz
    obtain ⟨a,ha⟩ := hall z (hn ▸ dvd_rfl)
    have h : p^2 ∣ p := by
      refine ⟨a.norm.natAbs, ?_⟩
      rw [ha] at hn
      simpa [sq, Int.natAbs_mul] using hn.symm
    have := Nat.le_of_dvd hp.pos h
    nlinarith [hp.two_le]
  have hi : shell (p^(k+2)) = (shell (p^k)).image ((-(p : GaussianInt)) * ·) := by
    ext z
    rw [mem_shell_image hP hN (pow_pos hp.pos 2), ← pow_add, add_comm 2 k]
    refine ⟨fun hz => ⟨hz,?_⟩, And.left⟩
    apply neg_dvd.mpr
    apply hall
    rw [(mem_shell.mp hz).2]
    exact dvd_pow_self p (by omega)
  have hem : mass p = 0 := by simp [mass,h0]
  have hmass : mass (p^(k+2)) = -(p : GaussianInt) * mass (p^k) := by
    unfold mass at *
    rw [hi, shell_sum_image _ (by exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.ne_zero))]
    rfl
  simp [hmass,hem]


lemma shell_split_prime {p : ℕ} (hp : p.Prime) {z : GaussianInt} (hz : z ∈ shell p) :
    shell p = {z, star z} := by
  have ⟨hzP,hn⟩ := mem_shell.mp hz
  have hstar : star z ∈ shell p := mem_shell.mpr ⟨primary_star hzP, by simpa using hn⟩
  ext w
  constructor
  · intro hw
    obtain ⟨hwP,hwn⟩ := mem_shell.mp hw
    have hwprim := norm_prime hp hwn
    have hzprim := norm_prime hp hn
    have hstprim := norm_prime hp (mem_shell.mp hstar).2
    have H : w ∣ z * star z := by
      rw [← Zsqrtd.norm_eq_mul_conj, ← GaussianInt.natCast_natAbs_norm, hn, ← hwn,
        GaussianInt.natCast_natAbs_norm, Zsqrtd.norm_eq_mul_conj]
      exact dvd_mul_right _ _
    rcases hwprim.dvd_or_dvd H with h | h
    · have := primary_associated_eq hwP hzP (hwprim.associated_of_dvd hzprim h)
      simp [this]
    · have := primary_associated_eq hwP (primary_star hzP)
        (hwprim.associated_of_dvd hstprim h)
      simp [this]
  · simp only [mem_insert,mem_singleton]
    rintro (rfl|rfl) <;> assumption

lemma distinct_star_of_prime {p : ℕ} (hp : p.Prime) {z : GaussianInt} (hn : z.norm.natAbs = p) :
    z ≠ star z := by
  intro e
  have h := congrArg Zsqrtd.im e
  change z.im = -z.im at h
  have hi : z.im = 0 := by omega
  rw [norm_sq, hi, zero_pow (by decide : 2 ≠ 0), add_zero, Int.natAbs_pow] at hn
  exact Nat.Prime.not_prime_pow (by decide : 2 ≤ 2) (show (z.re.natAbs ^ 2).Prime by rwa [hn])

theorem mass_prime_power (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (k : ℕ) :
    mass (p^(k+2)) = mass p * mass (p^(k+1)) - (p : GaussianInt)*mass (p^k) := by
  by_cases h3 : p % 4 = 3
  · exact inert_recurrence p hp h3 k
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a,b,hab⟩ := Nat.Prime.sq_add_sq h3
  let w : GaussianInt := ⟨a,b⟩
  have hw : w.norm = p := by
    rw [norm_sq]
    change (a : ℤ)^2 + (b : ℤ)^2 = p
    exact_mod_cast hab
  obtain ⟨r, hr, he⟩ := exists_primary_associate w (by
    rw [hw]; exact_mod_cast hp.eq_two_or_odd.resolve_left hodd)
  have hn : r.norm.natAbs = p := by
    rw [Zsqrtd.norm_eq_of_associated (by decide : (-1 : ℤ) ≤ 0) he,hw,Int.natAbs_natCast]
  have hr' := mem_shell.mpr (And.intro hr hn)
  have hne := distinct_star_of_prime hp hn
  apply split_recurrence hp hr' hne _ k
  simp [mass, shell_split_prime hp hr', hne]

theorem coefficient_prime_power (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (k : ℕ) :
    (mass (p^(k+2))).re =
      (mass p).re * (mass (p^(k+1))).re - (p : ℤ) * (mass (p^k)).re := by
  rw [mass_prime_power p hp hodd k]
  simp [mass_real]

end TunnellGaussian

/-
# Local properties of the congruent-number curves
-/

namespace TunnellPeriodCoates

open WeierstrassCurve WeierstrassCurve.Affine

def E {K : Type*} [CommRing K] (n : K) : WeierstrassCurve K := ⟨0,0,0,-n^2,0⟩

lemma E_discriminant {K : Type*} [CommRing K] (n : K) : (E n).Δ = 64*n^6 := by
  simp [E, Δ, b₂,b₄,b₆,b₈]
  ring

lemma E_equation {K : Type*} [CommRing K] (n x y : K) :
    (E n).toAffine.Equation x y ↔ y^2 = x^3-n^2*x := by
  simp [Affine.equation_iff, E, sub_eq_add_neg]

lemma E_elliptic {K : Type*} [Field K] {n : K} (h2 : (2:K) ≠ 0) (hn : n ≠ 0) :
    (E n).IsElliptic := by
  constructor
  rw [E_discriminant, show (64:K)=(2:K)^6 by norm_num, isUnit_iff_ne_zero]
  exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ hn)

lemma card_points {K : Type*} [Field K] [Fintype K] [DecidableEq K] (n : K)
    [(E n).IsElliptic] : Nat.card (E n).toAffine.Point =
    (Finset.univ.filter (fun xy : K × K => xy.2^2 = xy.1^3-n^2*xy.1)).card + 1 := by
  classical
  have eqv := (E n).toAffine.pointEquiv.trans
    ((Equiv.subtypeEquivRight (fun xy : K×K => E_equation n xy.1 xy.2)).optionCongr)
  calc
    _ = Nat.card (Option {xy : K×K // xy.2^2 = xy.1^3-n^2*xy.1}) := Nat.card_congr eqv
    _ = _ := by simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma eight_dvd_of_four_two {G : Type*} [AddCommGroup G] (P Q : G)
    (h4 : (4:ℕ) • P = 0) (hp : (2:ℕ) • P ≠ 0) (hq : (2:ℕ) • Q = 0)
    (hq0 : Q ≠ 0) (hdiff : Q ≠ (2:ℕ) • P) : 8 ∣ Nat.card G := by
  have hord : addOrderOf P = 4 := by
    apply addOrderOf_eq_of_nsmul_and_div_prime_nsmul (by decide) h4
    intro p hp' hdiv
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).mp
      (hp'.dvd_of_dvd_pow (by simpa using hdiv : p ∣ 2^2))
    subst p
    exact hp
  let H := AddSubgroup.zmultiples P
  have hnon : Q ∉ H := by
    rintro ⟨m,hm⟩
    have hred : (m % 4) • P = Q := by
      simpa [hord, hm] using (mod_addOrderOf_zsmul P m)
    have hlo := Int.emod_nonneg m (by decide : (4:ℤ) ≠ 0)
    have hhi := Int.emod_lt_of_pos m (by decide : 0 < (4:ℤ))
    generalize hr : m % 4 = a at hred hlo hhi
    interval_cases a
    · exact hq0 (by simpa using hred.symm)
    · have hPQ : P = Q := by simpa using hred
      exact hp (hPQ ▸ hq)
    · exact hdiff (by exact_mod_cast hred.symm)
    · have h6 : (6:ℕ) • P = 0 := by
        calc _ = (2:ℕ) • ((3:ℕ) • P) := by rw [← mul_smul]; rfl
             _ = (2:ℕ) • Q := by rw [show (3:ℕ) • P = Q by exact_mod_cast hred]
             _ = 0 := hq
      change (4+2:ℕ) • P = 0 at h6
      rw [add_smul, h4, zero_add] at h6
      exact hp h6
  have hco : addOrderOf (Q : G ⧸ H) = 2 :=
    addOrderOf_eq_prime (by simpa only [← QuotientAddGroup.mk_nsmul, hq, QuotientAddGroup.mk_zero])
      (fun h => hnon ((QuotientAddGroup.eq_zero_iff _).mp h))
  have hdiv := addOrderOf_dvd_natCard (Q : G ⧸ H)
  rw [hco] at hdiv
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H, Nat.card_zmultiples, hord]
  omega


lemma eight_dvd_points_base (p : ℕ) [Fact p.Prime] (hp : p%4=1) :
    8 ∣ ((Finset.univ.filter (fun xy : ZMod p × ZMod p =>
      xy.2^2 = xy.1^3-xy.1)).card + 1) := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2:ZMod p) ≠ 0 := by
    change ((2:ℕ) : ZMod p) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)
  let W := E (1 : ZMod p)
  have : W.IsElliptic := E_elliptic h2 one_ne_zero
  obtain ⟨i,hi⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)
  have hi2 : i^2 = -1 := by simpa [pow_two] using hi.symm
  have hy : (1-i : ZMod p) ≠ 0 := by
    intro h
    have hii : i=1 := (sub_eq_zero.mp h).symm
    rw [hii, one_pow] at hi2
    apply h2
    linear_combination hi2
  have H0 : W.toAffine.Equation 0 0 := by simp [W, E]
  have HQ : W.toAffine.Equation 1 0 := by simp [W, E_equation]
  have HP : W.toAffine.Equation i (1-i) := by
    rw [E_equation]; linear_combination -(i-1)*hi2
  let R := Affine.Point.mk H0
  let Q := Affine.Point.mk HQ
  let P := Affine.Point.mk HP
  have hR : R ≠ 0 := Affine.Point.some_ne_zero _
  have hQ : Q ≠ 0 := Affine.Point.some_ne_zero _
  have hQR : Q ≠ R := by
    change Affine.Point.some _ _ _ ≠ Affine.Point.some _ _ _
    simp
  have r2 : (2:ℕ) • R=0 := by
    rw [two_nsmul]; apply Affine.Point.add_self_of_Y_eq; simp [W, E, Affine.negY]
  have q2 : (2:ℕ) • Q=0 := by
    rw [two_nsmul]; apply Affine.Point.add_self_of_Y_eq; simp [W, E, Affine.negY]
  have hneg : 1-i ≠ W.toAffine.negY i (1-i) := by
    simp only [W,E,Affine.negY,zero_mul,sub_zero]
    intro h
    apply (mul_ne_zero h2 hy)
    linear_combination h
  have hs : W.toAffine.slope i i (1-i) (1-i) = -(1+i) := by
    rw [Affine.slope_of_Y_ne rfl hneg]
    apply (div_eq_iff (sub_ne_zero.mpr hneg)).mpr
    simp only [W,E,Affine.negY,zero_mul,mul_zero,add_zero,sub_zero,one_pow]
    linear_combination hi2
  have hx : W.toAffine.addX i i (-(1+i)) = 0 := by
    simp only [W,E,Affine.addX,zero_mul,add_zero,sub_zero]
    linear_combination hi2
  have hh : (2:ℕ) • P = R := by
    rw [two_nsmul]
    change Affine.Point.some _ _ _ + Affine.Point.some _ _ _ = Affine.Point.some _ _ _
    rw [Affine.Point.add_self_of_Y_ne hneg]
    simp only [Affine.Point.some.injEq, hs, hx, true_and]
    simp only [Affine.addY, Affine.negAddY, hx]
    simp only [W,E,Affine.negY,zero_mul,sub_zero]
    linear_combination -hi2
  have h4 : (4:ℕ) • P = 0 := by simpa only [show (4:ℕ)=2*2 by decide, mul_smul, hh] using r2
  have he := eight_dvd_of_four_two P Q h4 (hh ▸ hR) q2 hQ (hh ▸ hQR)
  rw [card_points] at he
  simpa using he

end TunnellPeriodCoates

/- The quartic Jacobi sum for the split primes of the congruent-number base curve. -/

namespace TunnellSplit

open Finset
open scoped ComplexConjugate

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def phi (F : Type*) [Field F] [Fintype F] [DecidableEq F] : MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

@[simp] lemma phi_apply (a : F) : phi F a = (quadraticChar F a : ℂ) := rfl

lemma phi_square : phi F ^ 2 = 1 := by
  ext x
  rw [MulChar.pow_apply_coe, phi_apply, MulChar.one_apply x.isUnit]
  exact_mod_cast quadraticChar_sq_one x.ne_zero

lemma quadratic_unique {χ ψ : MulChar F ℂ}
    (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1) (hc : χ ≠ 1) (hd : ψ ≠ 1) : χ = ψ := by
  let e := MulChar.equiv_rootsOfUnity F ℂ
  let h : MulChar F ℂ →* ℂ := (Units.coeHom ℂ).comp
    ((rootsOfUnity (Fintype.card Fˣ) ℂ).subtype.comp e.toMonoidHom)
  have hi : Function.Injective h := Units.val_injective.comp (Subtype.val_injective.comp e.injective)
  have hn (a : MulChar F ℂ) (ha : a^2 = 1) (hb : a ≠ 1) : h a = -1 := by
    apply (sq_eq_one_iff.mp (show (h a)^2 = 1 by rw [← map_pow, ha, map_one])).resolve_left
    exact fun he => hb (hi (he.trans h.map_one.symm))
  exact hi ((hn χ hχ hc).trans (hn ψ hψ hd).symm)

theorem quartic_exists (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ χ : MulChar (ZMod p) ℂ, orderOf χ = 4 ∧ χ ^ 2 = phi (ZMod p) := by
  have hd : 4 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  obtain ⟨χ, hχ⟩ := MulChar.exists_mulChar_orderOf (ZMod p) hd Complex.isPrimitiveRoot_I
  refine ⟨χ, hχ, quadratic_unique ?_ phi_square ?_ ?_⟩
  · rw [← pow_mul, show 2 * 2 = 4 by decide, ← hχ, pow_orderOf_eq_one]
  · intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hχ] at this
    omega
  · apply (MulChar.ringHomComp_ne_one_iff (Int.cast_injective (α := ℂ))).mpr
    apply quadraticChar_ne_one
    rw [ZMod.ringChar_zmod_n]; omega

lemma square_grouping (hc : ringChar F ≠ 2) (f : F → ℂ) :
    ∑ x : F, f (x^2) = ∑ y : F, (1 + phi F y) * f y := by
  classical
  calc
    _ = ∑ y : F, ∑ x ∈ univ.filter (fun x : F => x^2 = y), f (x^2) := by
      rw [sum_fiberwise_of_maps_to (fun x _ => mem_univ (x^2))]
    _ = _ := by
      apply sum_congr rfl
      intro y _
      have he : ∑ x ∈ univ.filter (fun x : F => x^2 = y), f (x^2) =
          ∑ _x ∈ univ.filter (fun x : F => x^2 = y), f y :=
        sum_congr rfl (fun x hx => congrArg f (mem_filter.mp hx).2)
      rw [he, sum_const, nsmul_eq_mul]
      have h := quadraticChar_card_sqrts hc y
      rw [Set.toFinset_ofPred] at h
      have hc' : ((univ.filter (fun x : F => x^2 = y)).card : ℂ) = phi F y + 1 := by
        rw [phi_apply]; exact_mod_cast h
      rw [hc', add_comm]

theorem trace_jacobi (p : Nat.Primes) [Fact p.val.Prime] (hp : p.val % 4 = 1)
    (χ : MulChar (ZMod p.val) ℂ) (hχ : χ ^ 2 = phi (ZMod p.val)) :
    let a : ℤ := (p.val : ℤ) - (univ.filter (fun xy : ZMod p.val × ZMod p.val =>
      xy.2^2 = xy.1^3 - xy.1)).card
    (a : ℂ) = -(jacobiSum χ (phi (ZMod p.val)) + jacobiSum (χ^3) (phi (ZMod p.val))) := by
  let F := ZMod p.val
  have hp2 : p.val ≠ 2 := by omega
  have hc : ringChar (ZMod p.val) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  have hn : quadraticChar (ZMod p.val) (-1) = 1 := by
    simpa only [legendreSym, Int.cast_neg, Int.cast_one] using
      (legendreSym.at_neg_one hp2).trans (ZMod.χ₄_nat_one_mod_four hp)
  have hφ (x : ZMod p.val) : phi (ZMod p.val) x = χ x ^ 2 := by
    rw [← hχ, MulChar.pow_apply' _ (by decide : 2 ≠ 0)]
  have hf (x : ZMod p.val) : (quadraticChar (ZMod p.val) (x^3 - x) : ℂ) =
      χ (x^2) * phi (ZMod p.val) (1-x^2) := by
    rw [show x^3 - x = (-1) * x * (1-x^2) by ring, map_mul, map_mul, hn, one_mul, Int.cast_mul,
      ← phi_apply, ← phi_apply, hφ x, map_pow]
  have ht := OMA.R_CongruentNumber_Tunnell_even_R1.trace_eq_neg_sum 1 p hp2
  simp only [Nat.cast_one, one_pow, one_mul] at ht
  dsimp only
  rw [ht, Int.cast_neg, Int.cast_sum]
  simp_rw [hf]
  rw [square_grouping hc (fun x => χ x * phi (ZMod p.val) (1-x))]
  congr 1
  rw [jacobiSum, jacobiSum, ← sum_add_distrib]
  apply sum_congr rfl
  intro y _
  rw [hφ y, MulChar.pow_apply' _ (by decide : 3 ≠ 0)]
  ring

open GaussianInt in
lemma jacobi_is_gaussian {χ : MulChar F ℂ} (hχ : χ ^ 4 = 1) :
    ∃ g : GaussianInt, (g : ℂ) = jacobiSum χ (phi F) := by
  have hφ : (phi F) ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by decide, pow_mul, phi_square, one_pow]
  have hm := jacobiSum_mem_algebraAdjoin_of_pow_eq_one hχ hφ Complex.isPrimitiveRoot_I
  let e := GaussianInt.toComplex.toIntAlgHom
  have H : Algebra.adjoin ℤ ({Complex.I} : Set ℂ) ≤ e.range := by
    apply Algebra.adjoin_le
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    refine ⟨⟨0, 1⟩, ?_⟩
    change ((⟨0, 1⟩ : GaussianInt) : ℂ) = Complex.I
    simp [GaussianInt.toComplex_def']
  exact H hm

omit [DecidableEq F] in
lemma conj_jacobi (χ ψ : MulChar F ℂ) :
    conj (jacobiSum χ ψ) = jacobiSum χ⁻¹ ψ⁻¹ := by
  unfold jacobiSum
  rw [map_sum]
  apply sum_congr rfl
  intro x _
  rw [map_mul]
  exact congrArg₂ (· * ·) (χ.star_apply' _) (ψ.star_apply' _)

theorem split_trace_norm (p : Nat.Primes) [Fact p.val.Prime] (hp : p.val % 4 = 1) :
    let t : ℤ := (p.val : ℤ) - (univ.filter (fun xy : ZMod p.val × ZMod p.val =>
      xy.2^2 = xy.1^3 - xy.1)).card
    ∃ a b : ℤ, t = 2 * a ∧ a^2 + b^2 = p.val := by
  dsimp only
  obtain ⟨χ, ho, hχ⟩ := quartic_exists p.val hp
  let ψ := phi (ZMod p.val)
  have h4 : χ ^ 4 = 1 := ho ▸ pow_orderOf_eq_one χ
  have h3 : χ ^ 3 = χ⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    exact h4
  have hψ : ψ⁻¹ = ψ := by
    symm; apply eq_inv_of_mul_eq_one_left
    rw [← pow_two]; exact phi_square
  have hne {k : ℕ} (hk : ¬ 4 ∣ k) : χ ^ k ≠ 1 := by
    intro h
    exact hk (ho ▸ orderOf_dvd_of_pow_eq_one h)
  have hc : ringChar ℂ ≠ ringChar (ZMod p.val) := by
    rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]
    exact p.property.ne_zero.symm
  have hn := jacobiSum_mul_jacobiSum_inv (F' := ℂ) hc
    (χ := χ) (φ := ψ) (by simpa using hne (k := 1) (by decide))
    (by simpa only [ψ, ← hχ] using hne (k := 2) (by decide))
    (by change χ * phi (ZMod p.val) ≠ 1; rw [← hχ, ← pow_succ']; exact hne (by decide))
  rw [← conj_jacobi, ZMod.card] at hn
  have ht := trace_jacobi p hp χ hχ
  change _ = -(jacobiSum χ ψ + jacobiSum (χ^3) ψ) at ht
  have hh : jacobiSum χ⁻¹ ψ = conj (jacobiSum χ ψ) := by rw [conj_jacobi, hψ]
  rw [h3, hh] at ht
  obtain ⟨g, hg⟩ := jacobi_is_gaussian h4
  change (g : ℂ) = jacobiSum χ ψ at hg
  rw [← hg, GaussianInt.toComplex_def₂] at hn ht
  refine ⟨-g.re, g.im, ?_, ?_⟩
  · have ht' := congrArg Complex.re ht
    simp only [Complex.intCast_re, Complex.neg_re, Complex.add_re, Complex.conj_re] at ht'
    norm_cast at ht'
    rw [Int.subNatNat_eq_coe] at ht'
    linarith
  · have hn' := congrArg Complex.re hn
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.natCast_re] at hn'
    norm_cast at hn'
    nlinarith

end TunnellSplit

/- The Frobenius trace of every congruent-number twist vanishes at primes 3 modulo 4. -/

namespace TunnellInert

open Finset Polynomial

theorem eta_zero_of_mod_four {m : ℕ} (hm : m % 4 ≠ 1) :
    (X * ∏ k ∈ Icc 1 m, ((1 - (X : ℤ[X])^(4*k))^2 * (1-X^(8*k))^2)).coeff m = 0 := by
  cases m with
  | zero => simp
  | succ d =>
    let P : ℤ[X] := ∏ k ∈ Icc 1 (d+1), ((1-X^k)^2 * (1-X^(2*k))^2)
    have hP : (expand ℤ 4) P =
        ∏ k ∈ Icc 1 (d+1), ((1-(X : ℤ[X])^(4*k))^2 * (1-X^(8*k))^2) := by
      dsimp only [P]
      simp only [map_prod, map_mul, map_pow, map_sub, map_one, expand_X, ← pow_mul,
        ← Nat.mul_assoc]
    rw [← hP, Polynomial.coeff_X_mul, Polynomial.coeff_expand (by decide : 0 < 4)]
    exact if_neg (by omega)

theorem inert_trace_zero (n : ℕ) (p : Nat.Primes) (hp : p.val % 4 = 3) :
    letI : NeZero p.val := ⟨p.property.ne_zero⟩
    (p.val : ℤ) - (Finset.univ.filter (fun xy : ZMod p.val × ZMod p.val =>
      xy.2^2 = xy.1^3 - (n : ZMod p.val)^2 * xy.1)).card = 0 := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  have hp' : p.val ≠ 2 := by omega
  let f (x : ZMod p.val) := quadraticChar (ZMod p.val) (x^3 - (n : ZMod p.val)^2*x)
  have hchi : quadraticChar (ZMod p.val) (-1) = -1 := by
    simpa only [legendreSym, Int.cast_neg, Int.cast_one] using
      ((legendreSym.at_neg_one hp').trans (ZMod.χ₄_nat_three_mod_four hp))
  have hf (x : ZMod p.val) : f (-x) = - f x := by
    dsimp only [f]
    rw [show (-x)^3-(n : ZMod p.val)^2 * (-x) = (-1)*(x^3-(n : ZMod p.val)^2*x) by ring,
      map_mul, hchi, neg_one_mul]
  have hsum := Equiv.sum_comp (Equiv.neg (ZMod p.val)) f
  change (∑ x : ZMod p.val, f (-x)) = ∑ x : ZMod p.val, f x at hsum
  simp_rw [hf, Finset.sum_neg_distrib] at hsum
  have ht := OMA.R_CongruentNumber_Tunnell_even_R1.trace_eq_neg_sum n p hp'
  change _ = - ∑ x : ZMod p.val, f x at ht
  omega

theorem inert_coefficient_eq_trace (p : Nat.Primes) (hp : p.val % 4 = 3) :
    letI : NeZero p.val := ⟨p.property.ne_zero⟩
    (X * ∏ k ∈ Icc 1 p.val, ((1 - (X : ℤ[X])^(4*k))^2 * (1-X^(8*k))^2)).coeff p.val =
    (p.val : ℤ) - (Finset.univ.filter (fun xy : ZMod p.val × ZMod p.val =>
      xy.2^2 = xy.1^3 - xy.1)).card := by
  rw [eta_zero_of_mod_four (by omega)]
  simpa only [Nat.cast_one, one_pow, one_mul] using (inert_trace_zero 1 p hp).symm

end TunnellInert

/- Identification of the coefficient of the Gaussian Hecke theta series at every odd prime. -/

namespace TunnellSplitMass

open Finset TunnellGaussian

lemma trace_primary {a b : ℤ} (h : (8 : ℤ) ∣ a^2 + b^2 + 1 - 2*a) :
    Primary (⟨a,b⟩ : GaussianInt) := by
  rw [primary_iff]
  have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr h
  push_cast at hh
  have finite_check : ∀ x y : ZMod 8, x^2 + y^2 + 1 - 2*x = 0 →
      y.val % 2 = 0 ∧ (x.val + y.val) % 4 = 1 := by decide
  obtain ⟨he,hr⟩ := finite_check _ _ hh
  have ha := ZMod.val_intCast (n := 8) a
  have hb := ZMod.val_intCast (n := 8) b
  change b%2 = 0 ∧ (a+b)%4 = 1
  omega

lemma primary_trace_exists (p : Nat.Primes) [Fact p.val.Prime] (hp : p.val % 4 = 1) :
    ∃ z ∈ shell p.val,
      (p.val : ℤ) - (univ.filter (fun xy : ZMod p.val × ZMod p.val =>
        xy.2^2 = xy.1^3 - xy.1)).card = 2 * z.re := by
  obtain ⟨a,b,ht,hn⟩ := TunnellSplit.split_trace_norm p hp
  have hd := TunnellPeriodCoates.eight_dvd_points_base p.val hp
  have h : (8 : ℤ) ∣ a^2 + b^2 + 1 - 2*a := by
    obtain ⟨k,hk⟩ := hd
    refine ⟨k, ?_⟩
    rw [hn, ← ht]
    omega
  have hz : (⟨a,b⟩ : GaussianInt).norm = p.val := by rw [norm_sq]; exact hn
  exact ⟨⟨a,b⟩, mem_shell.mpr ⟨trace_primary h, by simp [hz]⟩, ht⟩

theorem trace_mass_split (p : Nat.Primes) [Fact p.val.Prime] (hp : p.val % 4 = 1) :
    (mass p.val).re = (p.val : ℤ) - (univ.filter (fun xy : ZMod p.val × ZMod p.val =>
      xy.2^2 = xy.1^3 - xy.1)).card := by
  classical
  obtain ⟨z,hz,ht⟩ := primary_trace_exists p hp
  unfold mass
  rw [shell_split_prime p.property hz, sum_pair (distinct_star_of_prime p.property (mem_shell.mp hz).2), ht]
  change z.re + z.re = 2 * z.re
  ring

lemma shell_mod_four {n : ℕ} (hn : n % 4 = 3) : shell n = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hh := GaussianInt.abs_natCast_norm z
  rw [(mem_shell.mp hz).2, norm_sq] at hh
  have h : ((n : ℕ) : ZMod 4) = 3 := by
    apply ZMod.val_injective 4
    rw [ZMod.val_natCast, hn]
    decide
  have hx := congrArg (fun k : ℤ => (k : ZMod 4)) hh
  push_cast at hx
  rw [h] at hx
  have no_three : ∀ a b : ZMod 4, (3 : ZMod 4) ≠ a^2 + b^2 := by decide
  exact no_three _ _ hx

theorem trace_mass_odd (p : Nat.Primes) (hp : p.val ≠ 2) :
    letI : NeZero p.val := ⟨p.property.ne_zero⟩
    (mass p.val).re = (p.val : ℤ) - (univ.filter (fun xy : ZMod p.val × ZMod p.val =>
      xy.2^2 = xy.1^3 - xy.1)).card := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  have ho := p.property.odd_of_ne_two hp
  rcases (show p.val % 4 = 1 ∨ p.val % 4 = 3 by obtain ⟨k,hk⟩ := ho; omega) with h|h
  · exact trace_mass_split p h
  · have ht := TunnellInert.inert_trace_zero 1 p h
    simp only [Nat.cast_one, one_pow, one_mul] at ht
    simp [mass, shell_mod_four h, ht]

end TunnellSplitMass

/- Truncated unary theta identities imply the signed two-dimensional lattice expansion. -/

namespace TunnellJacobiFiniteBridge

open Polynomial Finset

def H1 : Prop := ∀ d : ℕ,
  (X : ℤ[X])^(d+1) ∣
    (∏ t ∈ Icc 1 d, (1-X^(8*t)))^3 -
    ∑ k ∈ range (d+1), C ((-1:ℤ)^k * (2*k+1)) * X^(8*(k+1).choose 2)

def H2 : Prop := ∀ d : ℕ,
  (X : ℤ[X])^(d+1) ∣
    (∏ t ∈ Icc 1 d, (1-X^(4*t)))^2 -
    (∑ j ∈ Icc (-(d:ℤ)) (d:ℤ), C (j.negOnePow:ℤ) * X^(4*j.natAbs^2)) *
    ∏ t ∈ Icc 1 d, (1-X^(8*t))

lemma exponent_eq (k : ℕ) : 1+8*(k+1).choose 2 = (2*k+1)^2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

lemma unary_to_lattice (h₁ : H1) (h₂ : H2) (d : ℕ) :
    (X * ∏ t ∈ Icc 1 d, ((1-(X:ℤ[X])^(4*t))^2 * (1-X^(8*t))^2)).coeff d =
      ∑ k ∈ range (d+1), ∑ j ∈ Icc (-(d:ℤ)) (d:ℤ),
        if (2*k+1)^2 + 4*j.natAbs^2 = d then
            (((k:ℤ)+j).negOnePow : ℤ) * (2*k+1) else 0 := by
  let f (a : ℕ) : ℤ[X] := ∏ t ∈ Icc 1 d, (1-X^(a*t))
  let c (k : ℕ) : ℤ[X] := C ((-1:ℤ)^k*(2*k+1))*X^(8*(k+1).choose 2)
  let g (j : ℤ) : ℤ[X] := C (j.negOnePow:ℤ)*X^(4*j.natAbs^2)
  let S := ∑ k ∈ range (d+1), c k
  let T := ∑ j ∈ Icc (-(d:ℤ)) (d:ℤ), g j
  have hc : X^(d+1) ∣ f 8 ^ 3 - S := h₁ d
  have ht : X^(d+1) ∣ f 4 ^ 2 - T * f 8 := h₂ d
  have hd : X^(d+1) ∣ X*f 4^2*f 8^2 - X*S*T := by
    have h := dvd_add (ht.mul_left (X * f 8 ^2)) (hc.mul_left (X*T))
    convert h using 1
    ring
  have he := X_pow_dvd_iff.1 hd d (by omega)
  rw [coeff_sub,sub_eq_zero] at he
  have hf : (∏ t ∈ Icc 1 d, ((1-(X:ℤ[X])^(4*t))^2 * (1-X^(8*t))^2)) =
      f 4^2 * f 8^2 := by simp only [f, prod_mul_distrib, prod_pow]
  rw [hf, ←mul_assoc, he]
  have hm (k : ℕ) (j : ℤ) : (X*c k*g j).coeff d =
    if (2*k+1)^2+4*j.natAbs^2=d then (((k:ℤ)+j).negOnePow:ℤ)*(2*k+1) else 0 := by
    have hp : X*c k*g j = C (((-1:ℤ)^k*(2*k+1))*(j.negOnePow:ℤ)) *
      X^(1+8*(k+1).choose 2+4*j.natAbs^2) := by
      simp only [c,g,map_mul,pow_add,pow_one]
      ring
    rw [hp,exponent_eq,coeff_C_mul_X_pow]
    simp only [Int.negOnePow_add, Units.val_mul, Int.coe_negOnePow_natCast]
    split_ifs <;> first | contradiction | (exfalso; solve_by_elim [Eq.symm]) | ring
  simp only [S,T,mul_sum,sum_mul,finsetSum_coeff,hm]
  exact Finset.sum_comm

end TunnellJacobiFiniteBridge

/- The signed lattice parametrization of the primary Gaussian integers of a fixed norm. -/

namespace TunnellEtaLattice

open Finset TunnellGaussian

def weight (k : ℕ) (j : ℤ) : ℤ := (Int.negOnePow ((k:ℤ)+j) : ℤ) * (2*(k:ℤ)+1)

def encode (k : ℕ) (j : ℤ) : GaussianInt := ⟨weight k j, 2*j⟩

lemma weight_cases (k : ℕ) (j : ℤ) :
    (weight k j = 2*(k:ℤ)+1 ∧ ((k:ℤ)+j)%2=0) ∨
    (weight k j = -(2*(k:ℤ)+1) ∧ ((k:ℤ)+j)%2=1) := by
  rcases Int.even_or_odd ((k:ℤ)+j) with h|h
  · left; rw [weight, Int.negOnePow_even _ h]; simp only [Units.val_one,one_mul,true_and]
    obtain ⟨v,hv⟩ := h; omega
  · right; rw [weight, Int.negOnePow_odd _ h]; simp only [Units.val_one,one_mul,Units.val_neg,neg_mul,true_and]
    obtain ⟨v,hv⟩ := h; omega

lemma primary_encode (k : ℕ) (j : ℤ) : Primary (encode k j) := by
  rw [primary_iff]
  change (2*j)%2=0 ∧ (weight k j+2*j)%4=1
  rcases weight_cases k j with ⟨h,he⟩|⟨h,he⟩ <;> omega

lemma norm_encode (k : ℕ) (j : ℤ) :
    (encode k j).norm = (2*(k:ℤ)+1)^2 + 4*j^2 := by
  rw [norm_sq]
  change (weight k j)^2+(2*j)^2 = _
  rcases weight_cases k j with ⟨h,-⟩|⟨h,-⟩ <;> rw [h] <;> ring

lemma abs_encode (k : ℕ) (j : ℤ) : (encode k j).re.natAbs = 2*k+1 := by
  change (weight k j).natAbs = _
  have hc : 2*(k:ℤ)+1 = ((2*k+1:ℕ):ℤ) := by push_cast; ring
  rcases weight_cases k j with ⟨h,-⟩|⟨h,-⟩ <;> rw [h,hc] <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]

lemma encode_injective {k l : ℕ} {j h : ℤ} (e : encode k j = encode l h) : k=l ∧ j=h := by
  have a := congrArg (fun z : GaussianInt => z.re.natAbs) e
  simp only [abs_encode] at a
  have b := congrArg Zsqrtd.im e
  change 2*j=2*h at b
  omega

lemma encode_surjective {z : GaussianInt} (hz : Primary z) :
    ∃ k : ℕ, ∃ j : ℤ, encode k j = z := by
  obtain ⟨hi,hr⟩ := (primary_iff _).mp hz
  let k := z.re.natAbs/2
  let j := z.im/2
  have hj : 2*j = z.im := by dsimp [j]; omega
  have habs : z.re = (z.re.natAbs : ℤ) ∨ z.re = -(z.re.natAbs : ℤ) := Int.natAbs_eq z.re
  have hk : z.re.natAbs = 2*k+1 := by dsimp [k]; omega
  refine ⟨k,j, ?_⟩
  have hp := (primary_iff _).mp (primary_encode k j)
  change _ ∧ (weight k j + 2*j)%4=1 at hp
  ext
  · change weight k j = z.re
    rcases weight_cases k j with ⟨he,-⟩|⟨he,-⟩ <;> omega
  · exact hj

def indices (n : ℕ) : Finset (ℕ × ℤ) :=
  ((range (n+1)) ×ˢ (Icc (-(n:ℤ)) (n:ℤ))).filter (fun kj =>
    (2*(kj.1:ℤ)+1)^2+4*kj.2^2 = n)

lemma indices_iff (n k : ℕ) (j : ℤ) :
    (k,j) ∈ indices n ↔ (2*(k:ℤ)+1)^2+4*j^2 = n := by
  simp only [indices,mem_filter,mem_product,mem_range,mem_Icc]
  refine ⟨And.right, fun h => ⟨⟨?_,?_,?_⟩,h⟩⟩
  · have hk : (k:ℤ) ≤ n := by nlinarith [sq_nonneg (k:ℤ),sq_nonneg j]
    omega
  · nlinarith [sq_nonneg (2*(k:ℤ)+1),sq_nonneg (2*j+1)]
  · nlinarith [sq_nonneg (2*(k:ℤ)+1),sq_nonneg (2*j-1)]

theorem mass_eq_lattice (n : ℕ) :
    (mass n).re = ∑ kj ∈ indices n, weight kj.1 kj.2 := by
  let re : GaussianInt →+ ℤ := { toFun := Zsqrtd.re, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change re (∑ z ∈ shell n, z) = _
  rw [map_sum]
  symm
  apply sum_bij (fun kj _ => encode kj.1 kj.2)
  · rintro ⟨k,j⟩ h
    have hn := (indices_iff _ _ _).mp h
    exact mem_shell.mpr ⟨primary_encode k j, by simp [norm_encode,hn]⟩
  · rintro ⟨k,j⟩ _ ⟨l,h⟩ _ e
    exact Prod.ext (encode_injective e).1 (encode_injective e).2
  · intro z h
    obtain ⟨hz,hn⟩ := mem_shell.mp h
    obtain ⟨k,j,e⟩ := encode_surjective hz
    have h := GaussianInt.abs_natCast_norm z
    rw [hn, ← e, norm_encode] at h
    exact ⟨(k,j),(indices_iff _ _ _).mpr h.symm,e⟩
  · intro _ _; rfl

end TunnellEtaLattice

/- Finite Gaussian binomials and their stabilized coefficients. -/

namespace TunnellQBin

open Polynomial Finset

variable {R : Type*} [CommRing R]

def choose (q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, _+1 => 0
  | _+1, 0 => 1
  | n+1, k+1 => choose q n (k+1) + q^(n-k)*choose q n k

def fac (q : R) (n : ℕ) : R := ∏ i ∈ range n, (1-q^(i+1))

lemma choose_zero (q : R) (n : ℕ) : choose q n 0 = 1 := by cases n <;> rfl

lemma choose_above (q : R) {n k : ℕ} (h : n < k) : choose q n k = 0 := by
  induction n generalizing k with
  | zero => cases k <;> first | rfl | omega
  | succ n ih =>
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [choose, ih (by omega), ih (by omega), mul_zero, add_zero]

lemma choose_self (q : R) (n : ℕ) : choose q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [choose, choose_above _ (by omega), Nat.sub_self, pow_zero, one_mul, ih, zero_add]

lemma fac_succ (q : R) (n : ℕ) : fac q (n+1) = fac q n * (1-q^(n+1)) := prod_range_succ ..

theorem factorial_formula (q : R) (n k : ℕ) (hk : k ≤ n) :
    choose q n k * fac q k * fac q (n-k) = fac q n := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k=0 := Nat.eq_zero_of_le_zero hk
    simp [choose,fac]
  | succ n ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [choose_zero,fac]
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0.ne'
    by_cases h : l=n
    · subst l; simp [choose_self,fac]
    have hl : l+1 ≤ n := by omega
    have ha := ih (l+1) hl
    have hb := ih l (by omega)
    have step : n - l = n - (l+1) + 1 := by omega
    have ep : n-l + (l+1) = n+1 := by omega
    rw [choose, Nat.succ_sub_succ_eq_sub]
    calc
      _ = (choose q n (l+1)*fac q (l+1)*fac q (n-(l+1))) * (1-q^(n-l)) +
          q^(n-l) * (choose q n l*fac q l*fac q (n-l)) * (1-q^(l+1)) := by
          have hfac : fac q (n-l) = fac q (n-(l+1))*(1-q^(n-l)) := by
            simpa only [← step] using fac_succ q (n-(l+1))
          rw [hfac,fac_succ q l]
          ring
      _ = _ := by rw [ha,hb,fac_succ,← ep,pow_add]; ring

noncomputable def product (q : R) (n : ℕ) : R[X] :=
  ∏ i ∈ range n, (1 + C (q^i) * X)

lemma product_coeff (q : R) (n k : ℕ) :
    (product q n).coeff k = q^(k.choose 2)*choose q n k := by
  induction n generalizing k with
  | zero =>
    cases k <;> simp [product,choose,Polynomial.coeff_one]
  | succ n ih =>
    have e : product q (n+1) = product q n + C (q^n)*(product q n*X) := by
      rw [product,prod_range_succ]
      change product q n*(1+C (q^n)*X) = _
      ring
    rw [e,coeff_add,coeff_C_mul]
    cases k with
    | zero => simp [choose_zero,ih]
    | succ k =>
      rw [Polynomial.coeff_mul_X,ih,ih,choose]
      by_cases h : k ≤ n
      · have htri : (k+1).choose 2 = k.choose 2 + k := by rw [Nat.choose_succ_succ]; simp [add_comm]
        have hexp : n + k.choose 2 = (k+1).choose 2 + (n-k) := by omega
        rw [mul_add]
        congr 1
        rw [← mul_assoc,← pow_add,hexp,pow_add,mul_assoc]
      · rw [choose_above _ (by omega : n < k)]
        simp

theorem expansion (q : R) (n : ℕ) :
    (∏ j ∈ range n, (1 + C (q^j)*X)) =
      ∑ k ∈ range (n+1), C (q^(k.choose 2)*choose q n k) * X^k := by
  ext k
  change (product q n).coeff k = _
  rw [product_coeff, finsetSum_coeff]
  simp only [coeff_C_mul,coeff_X_pow,mul_ite,mul_one,mul_zero]
  by_cases hk : k < n+1
  · simp [hk]
  · simp [hk, choose_above q (show n < k by omega)]

lemma fac_unit (q : R) (hq : IsNilpotent q) (n : ℕ) : IsUnit (fac q n) := by
  induction n with
  | zero => simp [fac]
  | succ n ih =>
    rw [fac_succ]
    exact ih.mul ((hq.pow_of_pos (by omega : n+1 ≠ 0)).isUnit_one_sub)

lemma fac_stable (q : R) {d : ℕ} (hq : q^(d+1) = 0) {n : ℕ} (hn : d ≤ n) :
    fac q n = fac q d := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc,fac_succ,show d+k+1 = d+1+k by omega,pow_add,hq,zero_mul,
      sub_zero,mul_one,ih (by omega)]

theorem choose_stable (q : R) {d : ℕ} (hq : q^(d+1) = 0) (n k : ℕ)
    (hk : k ≤ n) (hd : d ≤ k) (ht : d ≤ n-k) : choose q n k * fac q d = 1 := by
  apply (fac_unit q ⟨_,hq⟩ d).mul_left_injective
  have h := factorial_formula q n k hk
  rw [fac_stable q hq hd,fac_stable q hq ht,fac_stable q hq (hd.trans hk)] at h
  simpa only [one_mul] using h

theorem map_choose {S : Type*} [CommRing S] (f : R →+* S) (q : R) (n k : ℕ) :
    f (choose q n k) = choose (f q) n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [choose]
  | succ n ih => cases k <;> simp [choose,ih]

theorem expansion_eval (q t : R) (n : ℕ) :
    (∏ j ∈ range n, (1 + q^j*t)) =
      ∑ k ∈ range (n+1), (q^(k.choose 2)*choose q n k)*t^k := by
  have h := congrArg (Polynomial.evalRingHom t) (expansion q n)
  simpa only [map_prod,map_sum,map_add,map_one,map_mul,map_pow,coe_evalRingHom,eval_C,eval_X] using h

end TunnellQBin

/- A finite balanced specialization of the Gaussian binomial theorem. -/

namespace TunnellBalanced

open Finset
variable {K : Type*} [Field K]

private lemma normalizer (t : K) (N : ℕ) :
    ∏ i ∈ range N, (-t^(2*i+1)) = (-1 : K)^N * t^(N^2) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ih, show (n+1)^2 = n^2 + (2*n+1) by ring, pow_add, pow_succ (-1 : K)]
    ring

private lemma product_side (t : K) (ht : t ≠ 0) (N : ℕ) :
    ((-1 : K)^N * t^(N^2)) *
        (∏ j ∈ range (2*N), (1+(t^2)^j * (-t^(1-2*(N:ℤ))))) =
      ∏ i ∈ range N, (1-t^(2*i+1))^2 := by
  let F (j : ℕ) := 1 - t^(2*(j:ℤ)+1-2*(N:ℤ))
  have he (j : ℕ) : 1+(t^2)^j*(-t^(1-2*(N:ℤ))) = F j := by
    dsimp [F]
    rw [← pow_mul, ← zpow_natCast t (2*j), mul_neg, ← zpow_add₀ ht, ← sub_eq_add_neg]
    congr 2
    push_cast
    ring
  have hs : (∏ j ∈ range (2*N), F j) =
      (∏ j ∈ range N, F (N-1-j)) * ∏ j ∈ range N, F (N+j) := by
    rw [Finset.prod_range_reflect, ←prod_range_add, two_mul]
  simp only [he]
  rw [hs, ←normalizer, ←mul_assoc, ←prod_mul_distrib, ←prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  have hneg : (2*((N-1-i:ℕ):ℤ)+1-2*(N:ℤ)) = -((2*i+1:ℕ):ℤ) := by omega
  have hpos : (2*((N+i:ℕ):ℤ)+1-2*(N:ℤ)) = ((2*i+1:ℕ):ℤ) := by omega
  dsimp only [F]
  rw [hneg, hpos, zpow_neg, zpow_natCast]
  field_simp
  ring

private lemma triangular (k : ℕ) : 2*k.choose 2 + k = k^2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

private lemma power_side (t : K) (ht : t ≠ 0) (N k : ℕ) :
    t^(N^2) * (t^2)^k.choose 2 * (t^(1-2*(N:ℤ)))^k
      = t^(((k:ℤ)-(N:ℤ)).natAbs^2) := by
  rw [← pow_mul, ← zpow_natCast t (N^2), ← zpow_natCast t (2*k.choose 2),
      ← zpow_natCast (t^(1-2*(N:ℤ))) k, ← zpow_mul, ← zpow_add₀ ht, ← zpow_add₀ ht,
      ← zpow_natCast t (((k:ℤ)-(N:ℤ)).natAbs^2)]
  congr 1
  push_cast
  rw [sq_abs]
  have h : (2:ℤ)*(k.choose 2:ℕ) + (k:ℤ) = (k:ℤ)^2 := by exact_mod_cast triangular k
  linarith only [h]

private theorem balanced_field (t : K) (ht : t ≠ 0) (N : ℕ) :
    (∏ i ∈ range N, (1-t^(2*i+1))^2) =
    ∑ k ∈ range (2*N+1), ((Int.negOnePow ((k:ℤ)-(N:ℤ)) : ℤ) : K) *
        t ^ (((k:ℤ)-(N:ℤ)).natAbs ^ 2) * TunnellQBin.choose (t^2) (2*N) k := by
  rw [←product_side t ht N, TunnellQBin.expansion_eval, Finset.mul_sum]
  apply sum_congr rfl
  intro k hk
  have hs : ((Int.negOnePow ((k:ℤ)-(N:ℤ)) : ℤ) : K) =
      (-1:K)^k * (-1:K)^N := by
    rw [Int.negOnePow_sub, Units.val_mul, Int.cast_mul, Int.cast_negOnePow_natCast,
      Int.cast_negOnePow_natCast]
  rw [hs, ← power_side t ht, neg_eq_neg_one_mul (t^(1-2*(N:ℤ))), mul_pow]
  ring

open Polynomial in
theorem balanced {R : Type*} [CommRing R] (t : R) (N : ℕ) :
    (∏ i ∈ range N, (1-t^(2*i+1))^2) =
    ∑ k ∈ range (2*N+1), ((Int.negOnePow ((k:ℤ)-(N:ℤ)) : ℤ) : R) *
        t ^ (((k:ℤ)-(N:ℤ)).natAbs^2) * TunnellQBin.choose (t^2) (2*N) k := by
  let x : ℤ[X] := X
  let f := algebraMap ℤ[X] (FractionRing ℤ[X])
  have hf : Function.Injective f := IsFractionRing.injective _ _
  have hx : f x ≠ 0 := by
    rw [← map_zero f]
    exact fun h ↦ Polynomial.X_ne_zero (hf h)
  have hpoly : (∏ i ∈ range N, (1-x^(2*i+1))^2) =
      ∑ k ∈ range (2*N+1), ((Int.negOnePow ((k:ℤ)-(N:ℤ)) : ℤ) : ℤ[X]) *
        x ^ (((k:ℤ)-(N:ℤ)).natAbs^2) * TunnellQBin.choose (x^2) (2*N) k := by
    apply hf
    simpa only [map_prod, map_sum, map_pow, map_sub, map_one, map_mul, map_intCast,
      TunnellQBin.map_choose] using balanced_field (f x) hx N
  let g := Polynomial.eval₂RingHom (Int.castRingHom R) t
  have hxt : g x = t := by simp [g,x]
  simpa only [map_prod, map_sum, map_pow, map_sub, map_one, map_mul, map_intCast,
    TunnellQBin.map_choose,hxt] using congrArg g hpoly

end TunnellBalanced

/- Finite Jacobi cubic identity by differentiating the Gaussian binomial theorem. -/

namespace TunnellCubicFinite

open Finset Polynomial TunnellQBin
open LaurentPolynomial hiding C

abbrev L := LaurentPolynomial ℤ
noncomputable abbrev q : L := T 1

lemma fac_ne (n : ℕ) : fac q n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj he
  have e : (1 : ℤ[X]) = X^(j+1) := by
    apply Polynomial.toLaurent_injective
    simpa only [map_one,map_pow,toLaurent_X,q] using sub_eq_zero.mp he
  have c := congrArg (fun p : ℤ[X] => p.coeff 0) e
  simp at c

lemma choose_symm (m k : ℕ) (hk : k ≤ m) :
    choose q m k = choose q m (m-k) := by
  have a := factorial_formula q m k hk
  have b := factorial_formula q m (m-k) (by omega)
  rw [Nat.sub_sub_self hk, mul_right_comm] at b
  exact mul_right_cancel₀ (fac_ne k) (mul_right_cancel₀ (fac_ne (m-k)) (a.trans b.symm))

lemma derivative_monom {S : Type*} [CommRing S] (t a : S) (k : ℕ) :
    t * (derivative (C a * X^k)).eval t = (k:S)*a*t^k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [derivative_C_mul, derivative_X_pow_succ]
    simp only [eval_mul,eval_C,eval_pow,eval_X,pow_succ,Nat.cast_succ]
    ring

lemma weighted_expansion (n : ℕ) (t : L) :
    t * ((∏ j ∈ range n, (1 + C (q^j)*X)).derivative.eval t) =
      ∑ k ∈ range (n+1), (k:L)*(q^(k.choose 2)*choose q n k)*t^k := by
  rw [expansion, map_sum, eval_finsetSum, mul_sum]
  exact sum_congr rfl fun k _ => derivative_monom _ _ _

lemma reflected_fac (n : ℕ) :
    ∏ i ∈ range n, (1 - (T (-((i:ℤ)+1)) : L)) =
      (-1)^n * T (-((n+1).choose 2 : ℤ)) * fac q n := by
  induction n with
  | zero => simp [fac]
  | succ n ih =>
    rw [prod_range_succ, ih, fac_succ, pow_succ]
    have hp : (1 - (T (-((n:ℤ)+1)) : L)) =
      -T (-((n:ℤ)+1))*(1-q^(n+1)) := by
      simp only [q,T_pow,mul_one,Nat.cast_add,Nat.cast_one,mul_sub,neg_mul,← T_add,neg_add_cancel,T_zero]
      ring
    rw [hp]
    have he : ((n+1+1).choose 2 : ℤ) = ((n+1).choose 2 : ℤ) + (n+1:ℕ) := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add]
      ring
    have ht : (T (-((n+1+1).choose 2:ℤ)) : L) =
        T (-((n+1).choose 2:ℤ)) * T (-((n:ℤ)+1)) := by
      rw [← T_add,he,Nat.cast_add,Nat.cast_one]
      congr 1
      ring
    rw [ht]
    ring

lemma weighted_root (n : ℕ) :
    let t : L := -T (-(n:ℤ))
    t * ((∏ j ∈ range (2*n+1), (1 + C (q^j)*X)).derivative.eval t) =
      (-1)^(n+1) * T (-((n+1).choose 2 : ℤ)) * fac q n ^ 2 := by
  dsimp only
  let t : L := -T (-(n:ℤ))
  let f (j : ℕ) : L[X] := 1+C (q^j)*X
  change t*((∏ j ∈ range (2*n+1), f j).derivative.eval t) = _
  have ev (j : ℕ) : (f j).eval t = 1-T ((j:ℤ)-n) := by
    simp only [f,t,q,eval_add,eval_one,eval_mul,eval_C,eval_X,T_pow,mul_one,mul_neg,← T_add,sub_eq_add_neg]
  have ht : t*q^n = -1 := by
    simp only [t,q,T_pow,mul_one,neg_mul,← T_add,neg_add_cancel,T_zero]
  have center : (f n).eval t = 0 := by simp [ev]
  have dc : (f n).derivative.eval t = q^n := by simp [f]
  have left : ∏ j ∈ range n, (f j).eval t =
      (-1)^n*T (-((n+1).choose 2 : ℤ))*fac q n := by
    have hr := prod_range_reflect (fun j => (f j).eval t) n
    rw [← hr]
    convert reflected_fac n using 1
    apply prod_congr rfl
    intro i hi
    rw [ev]
    congr 2
    have := mem_range.mp hi
    omega
  have right : ∏ j ∈ range n, (f (n+1+j)).eval t = fac q n := by
    apply prod_congr rfl
    intro j _
    rw [ev]
    simp [q,T_pow]
    congr 1
    omega
  rw [show 2*n+1=n+1+n by omega, prod_range_add,prod_range_succ,derivative_mul,derivative_mul]
  simp only [eval_add,eval_mul,eval_prod,center,mul_zero,zero_mul,zero_add,add_zero,dc,left,right]
  calc _ = (t*q^n)*((-1)^n*T (-((n+1).choose 2 : ℤ)) * fac q n ^ 2) := by ring
       _ = _ := by rw [ht,pow_succ]; ring

lemma double_choose (m : ℕ) : 2*(m.choose 2 : ℤ) = (m:ℤ)*(m-1:ℤ) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    nlinarith

noncomputable def weight (n r : ℕ) : L :=
  (-1)^(n+1)*T ((n+1).choose 2 : ℤ) *
    ((r:L)*(q^(r.choose 2)*choose q (2*n+1) r)*(-T (-(n:ℤ)))^r)

lemma weight_clean (n r : ℕ) : weight n r =
    (-1)^(n+1+r)*T (((n+1).choose 2 : ℤ) + (r.choose 2:ℤ) - (n:ℤ)*r) *
      (r:L) * choose q (2*n+1) r := by
  simp only [weight,q,neg_pow (T (-(n:ℤ)) : L),T_pow,mul_one,pow_add,sub_eq_add_neg,T_add,
    mul_neg, mul_comm (r:ℤ) (n:ℤ)]
  ring

lemma weight_pair (n k : ℕ) (hk : k ≤ n) :
    weight n (n-k) + weight n (n+1+k) =
      (-1)^k*(2*k+1:L)*q^((k+1).choose 2)*choose q (2*n+1) (n+1+k) := by
  have hc := choose_symm (2*n+1) (n-k) (by omega)
  rw [show 2*n+1-(n-k)=n+1+k by omega] at hc
  have hsub : ((n-k:ℕ):ℤ) = (n:ℤ)-k := Nat.cast_sub hk
  have eL : ((n+1).choose 2:ℤ) + ((n-k).choose 2:ℤ) - n*(n-k:ℕ) = ((k+1).choose 2:ℤ) := by
    have a := double_choose (n+1)
    have b := double_choose (n-k)
    have c := double_choose (k+1)
    rw [hsub] at b ⊢
    push_cast at a c
    nlinarith
  have eR : ((n+1).choose 2:ℤ) + ((n+1+k).choose 2:ℤ) - n*(n+1+k:ℕ) = ((k+1).choose 2:ℤ) := by
    have a := double_choose (n+1)
    have b := double_choose (n+1+k)
    have c := double_choose (k+1)
    push_cast at a b c ⊢
    nlinarith
  have sign (a b : ℕ) : (-1:L)^(a+a+b) = (-1)^b := by
    rw [← two_mul, pow_add,pow_mul]
    norm_num
  rw [weight_clean,weight_clean,eL,eR, hc,
    show n+1+(n-k)=(n-k)+(n-k)+(k+1) by omega, sign,
    show n+1+(n+1+k)=(n+1)+(n+1)+k by omega,sign,pow_succ]
  rw [show (q^((k+1).choose 2):L)=T ((k+1).choose 2:ℤ) by simp only [q,T_pow,mul_one]]
  rw [Nat.cast_sub hk]
  push_cast
  ring

theorem cubic_laurent (n : ℕ) : fac q n ^ 2 =
    ∑ k ∈ range (n+1), (-1)^k * (2*k+1:L) * q^((k+1).choose 2) *
      choose q (2*n+1) (n+1+k) := by
  have h := (weighted_root n).symm.trans (weighted_expansion (2*n+1) (-T (-(n:ℤ))))
  have h' := congrArg (fun u:L => (-1)^(n+1)*T ((n+1).choose 2:ℤ) * u) h
  rw [mul_sum] at h'
  change _ = ∑ r ∈ range (2*n+1+1), weight n r at h'
  have hunit (a:ℕ) (b:ℤ) : ((-1)^a * T b:L) * ((-1)^a * T (-b)*fac q n^2) = fac q n^2 := by
    calc _ = (-1)^(a+a) * (T b*T (-b)) * fac q n^2 := by rw [pow_add]; ring
         _ = _ := by rw [← two_mul,pow_mul,← T_add,add_neg_cancel,T_zero]; norm_num
  rw [hunit,show 2*n+1+1=(n+1)+(n+1) by omega,sum_range_add] at h'
  rw [h',← sum_range_reflect (weight n) (n+1), ←sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  have hk' := mem_range.mp hk
  simpa only [Nat.add_sub_cancel] using weight_pair n k (by omega)

end TunnellCubicFinite

/- Specialize the finite Jacobi identity from the universal Laurent polynomial. -/

namespace TunnellCubicFinite

open Polynomial Finset TunnellQBin

theorem cubic {R : Type*} [CommRing R] (q : R) (N : ℕ) :
    fac q N ^ 2 = ∑ k ∈ range (N+1), (-1)^k * (2*k+1:R) *
      q^((k+1).choose 2) * TunnellQBin.choose q (2*N+1) (N+1+k) := by
  have hp : fac (X : ℤ[X]) N ^ 2 = ∑ k ∈ range (N+1), (-1)^k * (2*k+1:ℤ[X]) *
      X^((k+1).choose 2) * TunnellQBin.choose (X : ℤ[X]) (2*N+1) (N+1+k) := by
    apply Polynomial.toLaurent_injective
    simpa only [fac, map_pow, map_prod, map_sub, map_one, map_sum, map_mul, map_add,
      map_neg, map_ofNat, map_natCast, map_choose, toLaurent_X] using cubic_laurent N
  let g := Polynomial.eval₂RingHom (Int.castRingHom R) q
  have hx : g X = q := by simp [g]
  simpa only [fac, map_pow, map_prod, map_sub, map_one, map_sum, map_mul, map_add,
    map_neg, map_ofNat, map_natCast, map_choose, hx] using congrArg g hp


end TunnellCubicFinite

/- Truncate the centered finite Jacobi identities at arbitrary degree. -/

namespace TunnellTruncated

open TunnellQBin Polynomial Finset

variable {R : Type*} [CommRing R]

lemma triangle_ge (k : ℕ) : k ≤ (k+1).choose 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.choose_succ_succ,Nat.choose_one_right]; omega

theorem cubic_stabilized (q : R) (d N : ℕ) (hN : 2*d ≤ N) (hq : q^(d+1)=0)
    (h : fac q N ^ 2 = ∑ k ∈ range (N+1),
      ((-1:R)^k * (2*(k:R)+1)) * q^((k+1).choose 2) * choose q (2*N+1) (N+1+k)) :
    fac q d ^ 3 = ∑ k ∈ range (d+1), ((-1:R)^k * (2*(k:R)+1)) * q^((k+1).choose 2) := by
  let f (k : ℕ) := ((-1:R)^k*(2*(k:R)+1))*q^((k+1).choose 2)
  change _ = ∑ k ∈ range (d+1), f k
  change fac q N ^ 2 = ∑ k ∈ range (N+1), f k * choose q (2*N+1) (N+1+k) at h
  have htail (k : ℕ) (hk : d < k) : f k = 0 := by
    have hpow := pow_eq_zero_of_le (show d+1 ≤ (k+1).choose 2 by have := triangle_ge k; omega) hq
    simp [f,hpow]
  have hs : ∑ k ∈ range (N+1), (f k * choose q (2*N+1) (N+1+k))*fac q d =
      ∑ k ∈ range (d+1), (f k * choose q (2*N+1) (N+1+k))*fac q d := by
    symm
    apply sum_subset (range_mono (by omega))
    intro k _ hk
    simp only [mem_range,not_lt] at hk
    rw [htail k (by omega),zero_mul,zero_mul]
  rw [fac_stable q hq (n:=N) (by omega)] at h
  calc
    _ = (fac q d)^2 * fac q d := by ring
    _ = _ := by
      rw [h,sum_mul,hs]
      apply sum_congr rfl
      intro k hk
      rw [mem_range] at hk
      rw [mul_assoc,choose_stable q hq _ _ (by omega) (by omega) (by omega),mul_one]

lemma map_fac {S : Type*} [CommRing S] (f : R →+* S) (q : R) (n : ℕ) :
    f (fac q n) = fac (f q) n := by simp [fac]

lemma poly_fac (s n : ℕ) :
    fac ((X : ℤ[X])^s) n = ∏ t ∈ Icc 1 n, (1-X^(s*t)) := by
  induction n with
  | zero => simp [fac]
  | succ n ih =>
    rw [fac_succ,ih,prod_Icc_succ_top (by omega : 1 ≤ n+1),← pow_mul]

noncomputable def trunc (d : ℕ) := AdjoinRoot.mk ((X : ℤ[X])^(d+1))

lemma nilpotent_trunc (d : ℕ) : (trunc d X)^(d+1)=0 := by
  rw [← map_pow]
  exact AdjoinRoot.mk_self

lemma trunc_pow (d s : ℕ) (hs : s ≠ 0) : (trunc d (X^s))^(d+1)=0 := by
  rw [map_pow,← pow_mul,mul_comm,pow_mul,nilpotent_trunc,zero_pow hs]

theorem cubic_congruence
    (hc : ∀ N : ℕ, let q := (X:ℤ[X])^8
      fac q N ^ 2 = ∑ k ∈ range (N+1),
        ((-1:ℤ[X])^k * (2*(k:ℤ[X])+1)) * q^((k+1).choose 2) * choose q (2*N+1) (N+1+k)) :
    TunnellJacobiFiniteBridge.H1 := by
  intro d
  let t := trunc d
  let q := (X:ℤ[X])^8
  apply (AdjoinRoot.mk_eq_mk).mp
  change t _ = t _
  have he := congrArg t (hc (2*d))
  change t (fac q (2*d)^2) = t (∑ k ∈ range (2*d+1),
    ((-1:ℤ[X])^k * (2*(k:ℤ[X])+1)) * q^((k+1).choose 2)*choose q (2*(2*d)+1) (2*d+1+k)) at he
  simp only [map_pow,map_fac,map_sum,map_mul,map_add,map_neg,map_one,map_ofNat,map_natCast,map_choose] at he
  have hh := cubic_stabilized (t q) d (2*d) (by omega) (trunc_pow d 8 (by decide)) he
  rw [← poly_fac]
  simp only [map_pow,map_fac,map_sum,map_mul]
  apply hh.trans
  apply sum_congr rfl
  intro k _
  have hcst (a : ℤ) : t (C a) = (a : _) := by
    rw [show C a = (a : ℤ[X]) by simp, map_intCast]
  simp only [hcst]
  push_cast
  dsimp only [q]
  rw [map_pow,← pow_mul]

lemma fac_even_odd (t : R) (N : ℕ) :
    fac t (2*N) = fac (t^2) N * (∏ i ∈ range N, (1-t^(2*i+1))) := by
  induction N with
  | zero => simp [fac]
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+1+1 by omega,fac_succ,fac_succ,ih,fac_succ,prod_range_succ,
      ← pow_mul,show 2*(n+1) = 2*n+1+1 by omega]
    ring

lemma centered_sum (N : ℕ) (f : ℤ → R) :
    ∑ k ∈ range (2*N+1), f ((k:ℤ)-(N:ℤ)) = ∑ j ∈ Icc (-(N:ℤ)) (N:ℤ), f j := by
  apply sum_bij (fun (k : ℕ) _ => (k:ℤ)-(N:ℤ))
  · intro k hk
    simp only [mem_range] at hk
    rw [mem_Icc]; omega
  · intro k _ l _ he; omega
  · intro j hj
    rw [mem_Icc] at hj
    refine ⟨(j+N).toNat,mem_range.mpr (by omega),by omega⟩
  · intro _ _; rfl

theorem theta_stabilized (t : R) (d N : ℕ) (hN : 2*d ≤ N) (ht : t^(d+1)=0)
    (h : (∏ i ∈ range N, (1-t^(2*i+1))^2) = ∑ k ∈ range (2*N+1),
      (((((k:ℤ)-(N:ℤ)).negOnePow : ℤ) : R) * t^(((k:ℤ)-(N:ℤ)).natAbs^2)) *
        choose (t^2) (2*N) k) :
    fac t d ^ 2 = (∑ j ∈ Icc (-(d:ℤ)) (d:ℤ),
      ((j.negOnePow : ℤ) : R) * t^(j.natAbs^2)) * fac (t^2) d := by
  let f (j : ℤ) := ((j.negOnePow : ℤ) : R) * t^(j.natAbs^2)
  change fac t d ^ 2 = (∑ j ∈ Icc (-(d:ℤ)) (d:ℤ), f j) * fac (t^2) d
  have hq : (t^2)^(d+1)=0 := by rw [← pow_mul,mul_comm,pow_mul,ht,zero_pow (by decide : 2≠0)]
  have htail (j : ℤ) (hj : ¬ j ∈ Icc (-(d:ℤ)) (d:ℤ)) : f j = 0 := by
    have habs := Int.natAbs_eq j
    simp only [mem_Icc,not_and_or,not_le] at hj
    have hjd : d+1 ≤ j.natAbs := by omega
    have hd : d+1 ≤ j.natAbs^2 := by nlinarith [Nat.le_mul_self j.natAbs]
    simp [f,pow_eq_zero_of_le hd ht]
  have hside : fac t d ^ 2 = (∏ i ∈ range N, (1-t^(2*i+1))^2) * fac (t^2) d ^ 2 := by
    have hfac := fac_even_odd t N
    rw [fac_stable t ht (n:=2*N) (by omega),fac_stable (t^2) hq (n:=N) (by omega)] at hfac
    rw [hfac,prod_pow]; ring
  rw [hside,h,pow_two (fac (t^2) d),← mul_assoc]
  congr 1
  rw [sum_mul]
  calc
    _ = ∑ k ∈ range (2*N+1), f ((k:ℤ)-(N:ℤ)) := by
      apply sum_congr rfl
      intro k hk
      change f ((k:ℤ)-N) * _ * _ = _
      by_cases hj : ((k:ℤ)-N) ∈ Icc (-(d:ℤ)) (d:ℤ)
      · rw [mem_Icc] at hj
        rw [mul_assoc,choose_stable (t^2) hq _ _ (by omega) (by omega) (by omega),mul_one]
      · rw [htail _ hj,zero_mul,zero_mul]
    _ = _ := by
      rw [centered_sum]
      symm
      apply sum_subset (fun j hj => ?_) (fun j _ hj => htail j hj)
      simp only [mem_Icc] at hj ⊢
      omega

theorem theta_congruence
    (hc : ∀ (d N : ℕ), let t := trunc d (X^4)
      (∏ i ∈ range N, (1-t^(2*i+1))^2) = ∑ k ∈ range (2*N+1),
        (((((k:ℤ)-(N:ℤ)).negOnePow : ℤ) : _) * t^(((k:ℤ)-(N:ℤ)).natAbs^2)) *
          choose (t^2) (2*N) k) : TunnellJacobiFiniteBridge.H2 := by
  intro d
  apply (AdjoinRoot.mk_eq_mk).mp
  change trunc d _ = trunc d _
  have he := theta_stabilized (trunc d (X^4)) d (2*d) (by omega) (trunc_pow d 4 (by decide)) (hc d (2*d))
  rw [← poly_fac,← poly_fac]
  have hh : trunc d (X^8) = (trunc d (X^4))^2 := by rw [← map_pow,← pow_mul]
  simp only [map_pow,map_mul,map_sum,map_fac] at he ⊢
  rw [he]
  congr 1
  · apply sum_congr rfl
    intro j _
    have hC : trunc d (C (j.negOnePow : ℤ)) = ((j.negOnePow:ℤ) : _) := by
      rw [show C (j.negOnePow:ℤ) = ((j.negOnePow:ℤ):ℤ[X]) by simp, map_intCast]
    rw [hC,← pow_mul]
  · rw [← pow_mul]

end TunnellTruncated

/- The arithmetic of the base congruent-number cusp form. -/

namespace TunnellArithmetic

open Polynomial Finset TunnellGaussian TunnellEtaLattice

theorem eta_eq_mass (h₁ : TunnellJacobiFiniteBridge.H1) (h₂ : TunnellJacobiFiniteBridge.H2) (n : ℕ) :
    (X * ∏ i ∈ Icc 1 n, ((1-(X:ℤ[X])^(4*i))^2*(1-X^(8*i))^2)).coeff n = (mass n).re := by
  rw [TunnellJacobiFiniteBridge.unary_to_lattice h₁ h₂, mass_eq_lattice]
  unfold indices
  rw [sum_filter,sum_product]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro j _
  have hsq : ((j.natAbs : ℤ)^2) = j^2 := by
    rcases Int.natAbs_eq j with h|h <;> nlinarith [congrArg (fun x : ℤ => x^2) h]
  have hiff : (2*k+1)^2+4*j.natAbs^2 = n ↔ (2*(k:ℤ)+1)^2+4*j^2 = n := by
    rw [← hsq]
    exact_mod_cast Iff.rfl
  simp only [hiff,weight]

end TunnellArithmetic



/- The absolutely convergent Gaussian lattice expansion of the twisted L-series. -/

namespace TunnellCMLSeries

open Finset TunnellGaussian

noncomputable def gaussianTerm (s : ℝ) (z : GaussianInt) : ℂ :=
  (z:ℂ) / (((z.norm.natAbs:ℝ)^s : ℝ):ℂ)

lemma norm_sq_real (z : GaussianInt) : (z.norm.natAbs:ℝ) = ‖(z:ℂ)‖^2 := by
  have h := congrArg Complex.re (GaussianInt.intCast_complex_norm z)
  simp only [Complex.intCast_re,Complex.ofReal_re,Complex.normSq_eq_norm_sq] at h
  rw [GaussianInt.natCast_natAbs_norm]
  exact h

lemma norm_term (s : ℝ) (hs : 3/2 < s) (z : GaussianInt) :
    ‖gaussianTerm s z‖ = ‖(z:ℂ)‖^(-(2*s-1)) := by
  rw [gaussianTerm,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _),norm_sq_real]
  by_cases h : z=0
  · subst z; simp [Real.zero_rpow (by linarith : 1-2*s≠0)]
  have hz := norm_pos_iff.mpr (GaussianInt.toComplex_eq_zero.not.mpr h)
  rw [← Real.rpow_natCast,← Real.rpow_mul hz.le,
    show -(2*s-1) = 1-(2:ℝ)*s by ring,Real.rpow_sub hz,Real.rpow_one]
  rfl

lemma summable_gaussianTerm (s : ℝ) (hs : 3/2 < s) : Summable (gaussianTerm s) := by
  let coords (z : GaussianInt) : Fin 2 → ℤ := ![z.re,z.im]
  have hi : Function.Injective coords := by
    intro z w h
    exact Zsqrtd.ext (congrFun h 0) (congrFun h 1)
  have h := (EisensteinSeries.summable_one_div_norm_rpow (show 2 < 2*s-1 by linarith)).comp_injective hi
  apply Summable.of_norm
  apply h.of_nonneg_of_le (fun z => norm_nonneg _)
  intro z
  rw [norm_term s hs]
  change _ ≤ ‖coords z‖^(-(2*s-1))
  have hc0 : coords 0 = 0 := by funext i; fin_cases i <;> rfl
  by_cases hz : z=0
  · subst z; rw [hc0]; simp
  have hpos : 0 < ‖coords z‖ := by
    apply norm_pos_iff.mpr
    exact fun he => hz (hi (he.trans hc0.symm))
  apply Real.rpow_le_rpow_of_nonpos hpos _ (by linarith)
  rw [EisensteinSeries.norm_eq_max_natAbs, Nat.cast_max,max_le_iff]
  constructor
  · have h := Complex.abs_re_le_norm (z:ℂ)
    simpa only [coords,Matrix.cons_val_zero,Nat.cast_max,← GaussianInt.intCast_re,
      Nat.cast_natAbs,Int.cast_abs] using h
  · have h := Complex.abs_im_le_norm (z:ℂ)
    simpa only [coords,Matrix.cons_val_one,Matrix.cons_val_zero,Nat.cast_max,← GaussianInt.intCast_im,
      Nat.cast_natAbs,Int.cast_abs] using h

noncomputable def twistSign (n m : ℕ) : ℤ := if Odd m then jacobiSym n m else 0

lemma norm_twist_le (n m : ℕ) : ‖((twistSign n m : ℤ):ℂ)‖ ≤ 1 := by
  unfold twistSign
  split
  · rcases jacobiSym.trichotomy (n:ℤ) m with h|h|h <;> simp [h]
  · simp

noncomputable def term (n : ℕ) (s : ℝ) (z : GaussianInt) : ℂ :=
  by classical exact if Primary z then (twistSign n z.norm.natAbs : ℂ) * gaussianTerm s z else 0

theorem summable_lattice (n : ℕ) (s : ℝ) (hs : 3/2<s) : Summable (term n s) := by
  classical
  apply Summable.of_norm
  apply (summable_gaussianTerm s hs).norm.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro z
  unfold term
  split
  · rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_twist_le _ _)
  · simp

noncomputable def shellEquiv : (Σ n : ℕ, ↥(shell n)) ≃ {z : GaussianInt // Primary z} where
  toFun x := ⟨x.2.val,(mem_shell.mp x.2.property).1⟩
  invFun z := ⟨z.val.norm.natAbs, z.val, mem_shell.mpr ⟨z.property,rfl⟩⟩
  left_inv := by rintro ⟨n,z,hz⟩; obtain rfl := (mem_shell.mp hz).2; rfl
  right_inv := by intro z; rfl

noncomputable def latticeValue (n : ℕ) (s : ℝ) : ℂ :=
  ∑' z : {z : GaussianInt // Primary z},
    (twistSign n z.val.norm.natAbs : ℂ) * gaussianTerm s z.val

theorem shell_expansion (n : ℕ) (s : ℝ) (hs : 3/2<s) :
    HasSum (fun m : ℕ => (twistSign n m : ℂ) * ((mass m).re : ℂ) / ((m:ℂ)^(s:ℂ)))
      (latticeValue n s) := by
  classical
  let f (z : {z : GaussianInt // Primary z}) : ℂ :=
    (twistSign n z.val.norm.natAbs : ℂ) * gaussianTerm s z.val
  have hf : Summable f := by
    simpa only [Function.comp_def,f,term,Subtype.property,if_true] using (summable_lattice n s hs).subtype Primary
  have hsum : HasSum (fun c => f (shellEquiv c)) (latticeValue n s) :=
    shellEquiv.hasSum_iff.mpr hf.hasSum
  apply hsum.sigma
  intro m
  convert hasSum_fintype (fun v : ↥(shell m) => f (shellEquiv ⟨m,v⟩)) using 1
  have cst (v : ↥(shell m)) : f (shellEquiv ⟨m,v⟩) =
      (twistSign n m : ℂ) * ((v.val : GaussianInt) : ℂ) / (m:ℂ)^(s:ℂ) := by
    change _ * (_ / _) = _
    dsimp [f,shellEquiv,gaussianTerm]
    rw [(mem_shell.mp v.property).2,Complex.ofReal_cpow (Nat.cast_nonneg m)]
    push_cast
    ring
  simp only [cst,← Finset.sum_div,← Finset.mul_sum]
  have hc := (map_sum GaussianInt.toComplex (fun z => z) (shell m))
  change (↑(mass m) : ℂ) = ∑ z ∈ shell m, (z : ℂ) at hc
  have hre : (↑(mass m) : ℂ) = ((mass m).re : ℂ) := by simp [GaussianInt.toComplex_def,mass_real]
  rw [← hre,hc,← Finset.sum_attach (shell m) (fun z => (z : ℂ))]
  rfl

end TunnellCMLSeries


/- Euler product of the Gaussian Hecke L-series for the congruent-number twists. -/

namespace TunnellCMLSeries

open TunnellGaussian OMA.R_CongruentNumber_Tunnell_even_R1 Finset

lemma mass_one : mass 1 = 1 := by
  have e : shell 1 = {1} := by
    ext z
    rw [mem_shell,mem_singleton]
    constructor
    · rintro ⟨hz,hn⟩
      exact primary_unit_eq_one hz (Zsqrtd.norm_eq_one_iff.mp hn)
    · rintro rfl
      exact ⟨(primary_iff _).mpr (by decide),by simp⟩
  simp [mass,e]

lemma twistSign_one (n : ℕ) : twistSign n 1 = 1 := by simp [twistSign]

lemma twistSign_mul (n a b : ℕ) : twistSign n (a*b) = twistSign n a * twistSign n b := by
  by_cases ha : Odd a <;> by_cases hb : Odd b <;> simp [twistSign, Nat.odd_mul, ha, hb]
  exact jacobiSym.mul_right' _ (fun e => by simp [e] at ha) (fun e => by simp [e] at hb)

lemma twistSign_pow (n a k : ℕ) : twistSign n (a^k) = twistSign n a ^ k := by
  induction k with
  | zero => simp [twistSign_one]
  | succ k ih => rw [pow_succ,twistSign_mul,ih,pow_succ]

lemma twistSign_prime (n : ℕ) (p : Nat.Primes) [Fact p.val.Prime] (hp : p.val ≠ 2) :
    twistSign n p.val = quadraticChar (ZMod p.val) (n : ZMod p.val) := by
  have ho : Odd p.val := Nat.odd_iff.mpr (p.property.eq_two_or_odd.resolve_left hp)
  dsimp only [twistSign]
  rw [if_pos ho, ← jacobiSym.legendreSym.to_jacobiSym, legendreSym]
  simp

lemma twistSign_bad (n : ℕ) (p : Nat.Primes) (hp : p.val ∣ 2*n) : twistSign n p.val = 0 := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  by_cases h : p.val = 2
  · simp [twistSign,h]
  · have hd : p.val ∣ n := (p.property.dvd_mul.mp hp).resolve_left
      (fun e => h ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two).mp e))
    rw [twistSign_prime n p h, (ZMod.natCast_eq_zero_iff n _).mpr hd, quadraticChar_zero]

noncomputable def gaussCoeff (n m : ℕ) : ℂ := (twistSign n m:ℂ) * ((mass m).re : ℂ)

noncomputable def curveTrace (n : ℕ) (p : Nat.Primes) : ℤ :=
  letI : NeZero p.val := ⟨p.property.ne_zero⟩
  (p.val:ℤ) - (univ.filter (fun xy : ZMod p.val × ZMod p.val =>
    xy.2^2 = xy.1^3 - (n : ZMod p.val)^2 * xy.1)).card

lemma gaussCoeff_prime (n : ℕ) (p : Nat.Primes) (hp : ¬ p.val ∣ 2*n) :
    gaussCoeff n p.val = (curveTrace n p : ℂ) := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  have hp2 : p.val ≠ 2 := fun h => hp (h ▸ dvd_mul_right _ _)
  have hpn : ¬ p.val ∣ n := fun h => hp (dvd_mul_of_dvd_right h 2)
  rw [gaussCoeff,twistSign_prime n p hp2,TunnellSplitMass.trace_mass_odd p hp2]
  simpa only [curveTrace,Int.cast_mul,Nat.cast_one,one_pow,one_mul] using congrArg (fun z : ℤ => (z:ℂ)) (traceOfFrobenius_twist n p hp2 hpn).symm

lemma gaussCoeff_rec (n : ℕ) (p : Nat.Primes) (hp : ¬ p.val ∣ 2*n) (k : ℕ) :
    gaussCoeff n (p.val^(k+2)) = gaussCoeff n p.val * gaussCoeff n (p.val^(k+1)) -
      (p.val : ℂ)*gaussCoeff n (p.val^k) := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  have hp2 : p.val ≠ 2 := fun h => hp (h ▸ dvd_mul_right _ _)
  have hpn : ¬ p.val ∣ n := fun h => hp (dvd_mul_of_dvd_right h 2)
  have hs : ((twistSign n p.val : ℤ):ℂ)^2 = 1 := by
    rw [twistSign_prime n p hp2]; exact_mod_cast quadraticChar_sq_one ((ZMod.natCast_eq_zero_iff n p.val).not.mpr hpn)
  simp only [gaussCoeff,twistSign_pow,Int.cast_pow,coefficient_prime_power p.val p.property hp2 k,
    Int.cast_sub,Int.cast_mul,Int.cast_natCast]
  linear_combination -((twistSign n p.val:ℂ)^k*p.val*((mass (p.val^k)).re:ℂ))*hs

theorem lattice_euler (n : ℕ) (s : ℝ) (hs : 3/2 < s) :
    HasProd (fun p : Nat.Primes => if p.val ∣ 2*n then (1:ℂ) else
      let T : ℂ := (p.val : ℂ)^(-(s:ℂ))
      (1-(curveTrace n p:ℂ)*T+(p.val:ℂ)*T^2)⁻¹) (latticeValue n s) := by
  classical
  let g (m : ℕ) := gaussCoeff n m / (m:ℂ)^(s:ℂ)
  have hsum : HasSum g (latticeValue n s) := shell_expansion n s hs
  have hfirst : gaussCoeff n 1 = 1 := by simp [gaussCoeff,mass_one,twistSign_one]
  have hf : g 1 = 1 := by simp [g,hfirst]
  have hz : g 0 = 0 := by simp [g, Complex.zero_cpow (by exact_mod_cast (by linarith : s≠0) : (s:ℂ)≠0)]
  have hm {a b : ℕ} (hc : a.Coprime b) : g (a*b) = g a * g b := by
    dsimp only [g,gaussCoeff]
    rw [twistSign_mul,coefficient_mul hc,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
    push_cast
    ring
  have h := EulerProduct.eulerProduct_hasProd hf (fun {_ _} h => hm h) hsum.summable.norm hz
  rw [hsum.tsum_eq] at h
  convert h using 2 with p
  let T := (p.val:ℂ)^(-(s:ℂ))
  let c (e : ℕ) := gaussCoeff n (p.val^e)*T^e
  have he (e : ℕ) : g (p.val^e) = c e := weight_prime_power p s e (gaussCoeff n (p.val^e))
  simp_rw [he]
  have hc0 : c 0 = 1 := by simp [c,hfirst]
  by_cases hp : p.val ∣ 2*n
  · rw [if_pos hp]
    symm
    apply (hasSum_single (0 : ℕ) ?_).tsum_eq.trans hc0
    rintro (_|e) he0
    · exact False.elim (he0 rfl)
    · simp [c,gaussCoeff,twistSign_pow,twistSign_bad n p hp]
  · rw [if_neg hp]
    symm
    have hc : Summable c := by
      simpa only [Function.comp_def,he] using hsum.summable.comp_injective (Nat.pow_right_injective p.property.one_lt)
    refine (tsum_of_euler_recurrence c ((curveTrace n p:ℂ)*T) ((p.val:ℂ)*T^2) hc hc0 ?_ ?_).tsum_eq
    · simp [c,gaussCoeff_prime n p hp]
    · intro r
      simp only [c,gaussCoeff_rec n p hp r,gaussCoeff_prime n p hp]
      ring

end TunnellCMLSeries

end

section

namespace TunnellBaseTranslations
open MatrixGroups UpperHalfPlane Finset

namespace TunnellTranslate

open Matrix MatrixGroups ConjAct Pointwise UpperHalfPlane ModularForm
open Matrix.GeneralLinearGroup

lemma rational_translation_map (r : ℚ) :
    (upperRightHom r).map (Rat.castHom ℝ) = upperRightHom (r : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma translate_apply {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (F : CuspForm Γ k)
    (r : ℝ) (τ : ℍ) : (CuspForm.translate F (upperRightHom r)) τ = F (r +ᵥ τ) := by
  change (⇑F ∣[k] (upperRightHom r)) τ = _
  have hact : upperRightHom r • τ = r +ᵥ τ := by
    ext
    simp [σ, num, denom, coe_vadd, UpperHalfPlane.coe_smul, add_comm]
  simp_rw [slash_def, hact]
  simp [σ, denom, val_det_apply]

theorem exists_sum_rational_translates {ι : Type*} [Fintype ι]
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hwidth : Γ.strictWidthInfty = 1)
    {k : ℤ} (F : CuspForm Γ k) (r : ι → ℚ) (c : ι → ℂ) :
    ∃ H : Subgroup (GL (Fin 2) ℝ), H.IsArithmetic ∧ H.strictWidthInfty = 1 ∧
      ∃ G : CuspForm H k, ∀ τ : ℍ, G τ = ∑ i, c i * F ((r i : ℝ) +ᵥ τ) := by
  classical
  let T (i : ι) := upperRightHom (r i : ℝ)
  let C (i : ι) := (toConjAct (T i)⁻¹) • Γ
  have hC (i : ι) : (C i).IsArithmetic := by
    have h := Subgroup.IsArithmetic.conj Γ (upperRightHom (r i))⁻¹
    simpa only [map_inv, rational_translation_map, C, T] using h
  let H := 𝒮ℒ ⊓ Finset.univ.inf C
  have hH (s : Finset ι) : (𝒮ℒ ⊓ s.inf C).IsArithmetic := by
    induction s using Finset.induction_on with
    | empty => simpa using (inferInstance : Subgroup.IsArithmetic 𝒮ℒ)
    | insert i s hi ih =>
      rw [Finset.inf_insert, inf_left_comm]
      exact @Subgroup.IsArithmetic.inter _ _ (hC i) ih
  have harith : H.IsArithmetic := hH Finset.univ
  have hHC (i : ι) : H ≤ C i := inf_le_right.trans (Finset.inf_le (Finset.mem_univ i))
  have hunit : upperRightHom (1 : ℝ) ∈ Γ := by
    have h := Γ.strictWidthInfty_mem_strictPeriods
    rwa [hwidth, Subgroup.mem_strictPeriods_iff] at h
  have hcunit (i : ι) : upperRightHom (1 : ℝ) ∈ C i := by
    change upperRightHom 1 ∈ toConjAct (T i)⁻¹ • Γ
    rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
    have hcomm : T i * upperRightHom 1 = upperRightHom 1 * T i := by
      simp only [T, ← AddChar.map_add_eq_mul, add_comm]
    rwa [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hperiods : H.strictPeriods = AddSubgroup.zmultiples 1 := by
    apply le_antisymm
    · rw [← Subgroup.strictPeriods_SL2Z]
      exact fun x hx => Subgroup.mem_strictPeriods_iff.mpr
        ((Subgroup.mem_strictPeriods_iff.mp hx).1)
    · apply AddSubgroup.zmultiples_le.mpr
      apply Subgroup.mem_strictPeriods_iff.mpr
      constructor
      · have h := (AddSubgroup.mem_zmultiples (1 : ℝ))
        rwa [← Subgroup.strictPeriods_SL2Z, Subgroup.mem_strictPeriods_iff] at h
      · simpa [Finset.inf_eq_iInf] using hcunit
  have hHW : H.strictWidthInfty = 1 := by
    rw [Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty, Eq.comm,
      AddSubgroup.zmultiples_eq_zmultiples_iff
        (not_isOfFinAddOrder_of_isAddTorsionFree one_ne_zero)] at hperiods
    grind [Subgroup.strictWidthInfty_nonneg]
  let restrictCusp {H Γ : Subgroup (GL (Fin 2) ℝ)} (h : H ≤ Γ) {k : ℤ} (F : CuspForm Γ k) :
      CuspForm H k := {
    toFun := F
    slash_action_eq' g hg := F.slash_action_eq' g (h hg)
    holo' := F.holo'
    zero_at_cusps' hc := F.zero_at_cusps' (hc.mono h) }
  let forms (i : ι) : CuspForm H k := restrictCusp (hHC i) (CuspForm.translate F (T i))
  refine ⟨H, harith, hHW, ∑ i, c i • forms i, ?_⟩
  intro τ
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => congrArg (c i * ·) (translate_apply F _ τ))

end TunnellTranslate

namespace TunnellTwistFourier
open UpperHalfPlane MatrixGroups
open scoped Real

lemma translated_qpow {N : ℕ} [NeZero N] (j : ZMod N) (z : ℍ) (m : ℕ) :
    Function.Periodic.qParam 1 (((-(j.val : ℝ) / (N : ℝ)) +ᵥ z : ℍ) : ℂ) ^ m =
      ZMod.stdAddChar (-(j * (m : ZMod N))) * Function.Periodic.qParam 1 (z : ℂ) ^ m := by
  have h := ZMod.stdAddChar_coe (N := N) (-((j.val : ℤ) * m))
  push_cast at h
  rw [ZMod.natCast_zmod_val] at h
  rw [h]
  simp only [Function.Periodic.qParam, UpperHalfPlane.coe_vadd, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_natCast, Complex.ofReal_one, div_one,
    ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  ring

theorem twist_coefficients {N : ℕ} [NeZero N] (w : ZMod N → ℂ)
    {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] [Γ'.IsArithmetic]
    (hΓ : Γ.strictWidthInfty = 1) (hΓ' : Γ'.strictWidthInfty = 1)
    (F : CuspForm Γ 2) (G : CuspForm Γ' 2)
    (heq : ∀ z : ℍ, G z = ∑ j : ZMod N,
      (ZMod.dft.symm w) j * F ((-(j.val : ℝ) / (N : ℝ)) +ᵥ z)) (m : ℕ) :
    (qExpansion 1 G).coeff m = w (m : ZMod N) * (qExpansion 1 F).coeff m := by
  let c := ZMod.dft.symm w
  have hper : (1 : ℝ) ∈ Γ.strictPeriods := hΓ ▸ Γ.strictWidthInfty_mem_strictPeriods
  have hper' : (1 : ℝ) ∈ Γ'.strictPeriods := hΓ' ▸ Γ'.strictWidthInfty_mem_strictPeriods
  symm
  apply ModularFormClass.qExpansion_coeff_unique one_pos hper' _ m
  intro z
  rw [heq z]
  have hterm (j : ZMod N) := (ModularForm.hasSum_qExpansion F one_pos hper
    ((-(j.val : ℝ) / (N : ℝ)) +ᵥ z)).mul_left (c j)
  have hsum := hasSum_sum (s := Finset.univ) (fun j _ => hterm j)
  apply hsum.congr_fun
  intro k
  simp only [translated_qpow, smul_eq_mul]
  have heval : ∑ j : ZMod N, ZMod.stdAddChar (-(j * (k : ZMod N))) * c j = w k := by
    simpa only [ZMod.dft_apply, smul_eq_mul] using congrFun (ZMod.dft.apply_symm_apply w) (k : ZMod N)
  rw [← heval, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

end TunnellTwistFourier
end TunnellBaseTranslations

end

section

/- Disk primitive and level-two Fricke transformation for the conductor-32 eta product. -/

namespace TunnellFricke

open Complex hiding eta
open Function ModularForm Set Filter Metric
open UpperHalfPlane hiding I
open scoped Real Topology

noncomputable def h (z : ℂ) := eta z ^2 * eta (2*z)^2
noncomputable def W (z : ℂ) := -1/(2*z)
noncomputable def disk (q : ℂ) := (∏' n : ℕ, (1-(q^4)^(n+1)))^2 *
  (∏' n : ℕ, (1-(q^8)^(n+1)))^2

lemma disk_hol : DifferentiableOn ℂ disk (ball 0 1) := by
  have hc (a : ℕ) (ha : 0<a) : MapsTo (fun q : ℂ => q^a) (ball 0 1) (ball 0 1) := by
    intro q hq
    simpa [mem_ball,norm_pow] using pow_lt_one₀ (norm_nonneg q) (by simpa using hq) ha.ne'
  have hf (a : ℕ) (ha : 0<a) := differentiableOn_tprod_one_sub_pow.comp
    (show DifferentiableOn ℂ (fun q : ℂ => q^a) (ball 0 1) by fun_prop) (hc a ha)
  exact ((hf 4 (by decide)).pow 2).mul ((hf 8 (by decide)).pow 2)

lemma disk_rot (q : ℂ) : disk (I*q) = disk q := by
  simp [disk,mul_pow,I_pow_four,show Complex.I^8=1 by rw [show 8=4*2 by decide,pow_mul,I_pow_four,one_pow]]

lemma present (z : ℂ) : h z = Periodic.qParam 4 z * disk (Periodic.qParam 4 z) := by
  have h1 : Periodic.qParam 1 z = Periodic.qParam 4 z ^4 := by
    simp only [Periodic.qParam,← Complex.exp_nat_mul]; push_cast; congr 1; ring
  have h2 : Periodic.qParam 1 (2*z) = Periodic.qParam 4 z ^8 := by
    simp only [Periodic.qParam,← Complex.exp_nat_mul]; push_cast; congr 1; ring
  have h0 : Periodic.qParam 24 z ^2 * Periodic.qParam 24 (2*z)^2 = Periodic.qParam 4 z := by
    simp only [Periodic.qParam,← Complex.exp_nat_mul,← Complex.exp_add]; push_cast; congr 1; ring
  simp only [h,eta,eta_q,h1,h2,mul_pow,disk]
  linear_combination (∏' k : ℕ, (1-(Periodic.qParam 4 z ^ 4)^(k+1)))^2 *
    (∏' k : ℕ, (1-(Periodic.qParam 4 z ^ 8)^(k+1)))^2 * h0

lemma sq_csqrt (z : ℂ) (hz : z ≠ 0) : sqrt z ^ 2 = z := by
  rw [sqrt_eq_exp hz,← exp_nat_mul]
  convert Complex.exp_log hz using 2 <;> ring

lemma eta_S_sq (z : ℂ) (hz : 0<z.im) : eta (-1/z)^2 = (-I)*z*eta z^2 := by
  have e : eta (-1/z) = (sqrt I)⁻¹*(sqrt z * eta z) := eta_comp_eq_csqrt_I_inv hz
  rw [e,mul_pow,mul_pow,inv_pow,sq_csqrt I I_ne_zero,sq_csqrt z (ne_zero (⟨z,hz⟩:ℍ)),inv_I]
  ring

lemma h_fricke (z : ℂ) (hz : 0<z.im) : h (W z) = -2*z^2*h z := by
  have hz' : 0<(2*z).im := by simpa [mul_im] using hz
  have hz0 := ne_zero (⟨z,hz⟩:ℍ)
  simp only [h,W,eta_S_sq _ hz',show 2*(-1/(2*z)) = -1/z by field_simp,eta_S_sq _ hz]
  linear_combination 2*z^2*eta z^2*eta (2*z)^2*I_sq

lemma W_mem {z : ℂ} (hz : 0<z.im) : 0<(W z).im := by
  have h2 : 0<(2*z).im := by simpa [mul_im] using hz
  simpa [W,neg_div] using (⟨2*z,h2⟩:ℍ).im_inv_neg_coe_pos

noncomputable def c : ℂ := 2*(Real.pi:ℂ)*I/4

lemma hasDeriv_q (z : ℂ) : HasDerivAt (Periodic.qParam 4) (c*Periodic.qParam 4 z) z := by
  have e : Periodic.qParam 4 = fun z => exp (c*z) := by
    ext z
    simp only [Periodic.qParam,c]
    push_cast
    congr 1
    ring
  rw [e]
  simpa [mul_comm] using ((hasDerivAt_id z).const_mul c).cexp

lemma q_T (z : ℂ) : Periodic.qParam 4 (z+1) = I*Periodic.qParam 4 z := by
  simp only [Periodic.qParam]
  push_cast
  rw [show 2*(Real.pi:ℂ)*I*(z+1)/4 = Real.pi/2*I + 2*Real.pi*I*z/4 by ring,
    exp_add,exp_pi_div_two_mul_I]

theorem primitive :
    ∃ J : ℂ → ℂ, (∀ z, 0<z.im → HasDerivAt J (c*h z) z) ∧
      Tendsto J (comap Complex.im atTop) (𝓝 0) ∧
      (∀ z, 0<z.im → J (z+1) = I*J z) ∧
      ∃ C : ℂ, ∀ z, 0<z.im → J (W z) = C-J z := by
  obtain ⟨G,hG0,hG⟩ := disk_hol.isExactOn_ball.with_val_at 0 0
  let J (z : ℂ) := G (Periodic.qParam 4 z)
  have qmem {z : ℂ} (hz : 0<z.im) : Periodic.qParam 4 z ∈ ball 0 1 := by
    simpa using Periodic.norm_qParam_lt_one (by norm_num : (0:ℝ)<4) hz
  have hJ (z : ℂ) (hz : 0<z.im) : HasDerivAt J (c*h z) z := by
    rw [show c*h z = disk (Periodic.qParam 4 z)*(c*Periodic.qParam 4 z) by rw [present]; ring]
    exact (hG _ (qmem hz)).comp z (hasDeriv_q z)
  have h0 : Tendsto J (comap Complex.im atTop) (𝓝 0) := by
    have hh := (hG 0 (mem_ball_self (by norm_num))).continuousAt.tendsto
    rw [hG0] at hh
    exact hh.comp ((Periodic.qParam_tendsto (by norm_num : (0:ℝ)<4)).mono_right nhdsWithin_le_nhds)
  have hA {q : ℂ} (hq : q ∈ ball 0 1) : I*q ∈ ball 0 1 := by simpa [mem_ball] using hq
  have da {q : ℂ} (hq : q ∈ ball 0 1) : HasDerivAt (fun w => G (I*w)) (I*disk q) q := by
    simpa only [Function.comp_def,id_eq, mul_one,disk_rot, mul_comm (disk q) I] using (hG _ (hA hq)).comp q ((hasDerivAt_id q).const_mul I)
  have db {q : ℂ} (hq : q ∈ ball 0 1) : HasDerivAt (fun w => I*G w) (I*disk q) q := (hG _ hq).const_mul I
  have rot : (ball 0 1).EqOn (fun w => G (I*w)) (fun w => I*G w) := by
    refine isOpen_ball.eqOn_of_deriv_eq (convex_ball (0:ℂ) 1).isPreconnected
      (fun q hq => (da hq).differentiableAt.differentiableWithinAt)
      (fun q hq => (db hq).differentiableAt.differentiableWithinAt)
      (fun q hq => (da hq).deriv.trans (db hq).deriv.symm) (x:=0) (by simp) ?_
    simp [hG0]
  refine ⟨J,hJ,h0,fun z hz => ?_,?_⟩
  · simpa [J,q_T] using rot (qmem hz)
  · have dW (z : ℂ) (hz : 0<z.im) : HasDerivAt W (1/(2*z^2)) z := by
      have hz0 := ne_zero (⟨z,hz⟩:ℍ)
      have hh := (hasDerivAt_const z (-1:ℂ)).div ((hasDerivAt_id z).const_mul 2) (mul_ne_zero two_ne_zero hz0)
      change HasDerivAt W ((0*(2*z)-(-1)*(2*1))/(2*z)^2) z at hh
      rwa [show (0*(2*z)-(-1)*(2*1))/(2*z)^2 = 1/(2*z^2) by field_simp; ring] at hh
    have da (z : ℂ) (hz : 0<z.im) : HasDerivAt (fun w => J (W w)) (-(c*h z)) z := by
      have hz0 := ne_zero (⟨z,hz⟩:ℍ)
      rw [show -(c*h z) = c*h (W z)*(1/(2*z^2)) by rw [h_fricke z hz]; field_simp]
      exact (hJ (W z) (W_mem hz)).comp z (dW z hz)
    have db (z : ℂ) (hz : 0<z.im) := (hJ z hz).neg
    obtain ⟨C,hC⟩ := isOpen_upperHalfPlaneSet.exists_eq_add_of_deriv_eq
      (convex_halfSpace_im_gt 0).isPreconnected
      (fun z hz => (da z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (db z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (da z hz).deriv.trans (db z hz).deriv.symm)
    exact ⟨C,fun z hz => by simpa [sub_eq_add_neg,add_comm] using hC hz⟩

end TunnellFricke

end

section

/-
# The base cusp form for the congruent-number curves

The twelfth power of the eta product is a product of two rational dilates of
the modular discriminant. Its multiplier therefore has finite image, and on
the kernel the eta product is a weight-two cusp form. Its period is one.
Uniform convergence of the truncated products on compact subsets of the disk
identifies the Fourier coefficients with the prescribed integer coefficients.
-/

namespace TunnellRoot

open Complex UpperHalfPlane Matrix MatrixGroups ModularForm
open scoped Manifold Topology

lemma pow_slash (f : ℍ → ℂ) (g : SL(2, ℤ)) (k n : ℕ) :
    (f ^ n) ∣[((n*k : ℕ) : ℤ)] g = (f ∣[(k:ℤ)] g) ^ n := by
  induction n with
  | zero =>
    ext z
    simp [SL_slash_apply]
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul, Nat.cast_add, mul_slash_SL2, ih, pow_succ]

lemma zero_of_twelfth_power {f : ℍ → ℂ} (h : IsZeroAtImInfty (f ^ 12)) : IsZeroAtImInfty f := by
  rw [isZeroAtImInfty_iff] at h ⊢
  intro ε hε
  obtain ⟨b,hb⟩ := h (ε^12) (by positivity)
  refine ⟨b, fun z hz => ?_⟩
  have ht := hb z hz
  simp only [Pi.pow_apply, norm_pow] at ht
  exact le_of_pow_le_pow_left₀ (by decide : 12 ≠ 0) hε.le ht

lemma constant_of_twelfth_power (q : ℍ → ℂ) (hq : Continuous q) (hp : ∀ z, q z ^ 12 = 1)
    (x y : ℍ) : q x = q y := by
  let Z := Polynomial.nthRootsFinset 12 (1:ℂ)
  apply isPreconnected_univ.constant_of_mapsTo (T := (Z : Set ℂ)) Z.finite_toSet.isDiscrete
    hq.continuousOn _ (Set.mem_univ x) (Set.mem_univ y)
  exact fun z _ => (Polynomial.mem_nthRootsFinset (by decide : 0 < 12) 1).mpr (hp z)

theorem exists_cusp_root {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (f : ℍ → ℂ) (hhol : MDiff f) (hf : ∀ z, f z ≠ 0)
    (hperiod : f ∣[(2 : ℤ)] ModularGroup.T = f)
    (F : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 24) (hpow : ⇑F = f ^ 12) :
    ∃ H : Subgroup SL(2, ℤ), H.FiniteIndex ∧ ModularGroup.T ∈ H ∧
      ∃ G : CuspForm (H : Subgroup (GL (Fin 2) ℝ)) 2, ⇑G = f := by
  classical
  let base : ℍ := UpperHalfPlane.I
  let ratio (g : Γ) (z : ℍ) := (f ∣[(2 : ℤ)] (g.val)) z / f z
  have hpowg (g : Γ) : (f ∣[(2 : ℤ)] (g.val)) ^ 12 = f^12 := by
    have hh : (f^12) ∣[(24:ℤ)] g.val = (f∣[(2:ℤ)]g.val)^12 := pow_slash f g.val 2 12
    rw [← hh, ← hpow]
    exact F.slash_action_eq' _ ⟨g.val,g.property,rfl⟩
  have hrpow (g : Γ) (z : ℍ) : ratio g z ^ 12 = 1 := by
    have ht := congrFun (hpowg g) z
    change ((f ∣[(2 : ℤ)] (g.val)) z)^12 = f z ^12 at ht
    dsimp only [ratio]
    rw [div_pow, ht, div_self (pow_ne_zero _ (hf z))]
  have hrc (g : Γ) (z : ℍ) : ratio g z = ratio g base := by
    apply constant_of_twelfth_power _ _ (hrpow g)
    exact (hhol.slash 2 (g.val : GL (Fin 2) ℝ)).continuous.div hhol.continuous hf
  have hslash (g : Γ) : f ∣[(2 : ℤ)] g.val = ratio g base • f := by
    funext z
    exact (div_eq_iff (hf z)).mp (hrc g z)
  let χ : Γ →* ℂ := {
    toFun := fun g => ratio g base
    map_one' := by simp [ratio, hf]
    map_mul' := by
      intro g h
      have heq : (f ∣[(2 : ℤ)] ((g*h).val)) = (ratio g base * ratio h base) • f := by
        rw [Subgroup.coe_mul, SlashAction.slash_mul, hslash g, SL_slash,
          smul_slash, ← SL_slash, hslash h]
        simp [σ, smul_smul]
      exact (div_eq_iff (hf base)).mpr (congrFun heq base) }
  let χ' : Γ →* rootsOfUnity 12 ℂ := χ.toHomUnits.codRestrict _ (fun g => by
    change χ.toHomUnits g ^ 12 = 1
    ext
    exact hrpow g base)
  let H := χ'.ker.map Γ.subtype
  have hH : H.FiniteIndex := by
    constructor
    rw [Subgroup.index_map_subtype]
    exact Nat.mul_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := χ'.ker)) (Subgroup.FiniteIndex.index_ne_zero (H := Γ))
  have hker (g : Γ) : g ∈ χ'.ker ↔ ratio g base = 1 := by
    change χ' g = 1 ↔ _
    simp only [Subtype.ext_iff, Units.ext_iff]
    rfl
  have hsH (γ : SL(2, ℤ)) (hγ : γ ∈ H) : f ∣[(2 : ℤ)] γ = f := by
    obtain ⟨g,hg,rfl⟩ := hγ
    change f ∣[(2:ℤ)] g.val = f
    rw [hslash g, hker g |>.mp hg, one_smul]
  have hT' : ModularGroup.T ∈ H := by
    refine ⟨⟨_,hT⟩, (hker _).mpr ?_, rfl⟩
    simp [ratio, hperiod, hf]
  refine ⟨H,hH,hT', { toFun := f, slash_action_eq' := ?_, holo' := hhol, zero_at_cusps' := ?_ }, rfl⟩
  · rintro _ ⟨γ,hγ,rfl⟩
    exact hsH γ hγ
  · intro c hc
    have hsub : (H : Subgroup (GL (Fin 2) ℝ)) ≤ (Γ : Subgroup (GL (Fin 2) ℝ)) := by
      apply Subgroup.map_mono
      rintro γ ⟨g,-,rfl⟩
      exact g.property
    have hcSL : IsCusp c 𝒮ℒ := hc.mono (Subgroup.map_le_range _ _)
    apply (OnePoint.isZeroAt_iff_forall_SL2Z hcSL).mpr
    intro γ hγ
    apply zero_of_twelfth_power
    have hh : (f^12) ∣[(24:ℤ)] γ = (f∣[(2:ℤ)]γ)^12 := pow_slash f γ 2 12
    rw [← hh, ← hpow]
    exact ((OnePoint.isZeroAt_iff_forall_SL2Z hcSL).mp (F.zero_at_cusps' (hc.mono hsub))) γ hγ

end TunnellRoot

namespace TunnellRoot

open Complex UpperHalfPlane Matrix MatrixGroups ModularForm
open Matrix.GeneralLinearGroup Matrix.SpecialLinearGroup ConjAct Pointwise
open scoped Manifold

noncomputable def dilation (d : ℕ) (hd : 0 < d) : GL (Fin 2) ℚ :=
  mkOfDetNeZero !![(d:ℚ), 0; 0, 1] (by simp [Matrix.det_fin_two, hd.ne'])

noncomputable def dilR (d : ℕ) (hd : 0 < d) : GL (Fin 2) ℝ :=
  (dilation d hd).map (Rat.castHom ℝ)

lemma val_dilR (d : ℕ) (hd : 0 < d) : ((dilR d hd : GL (Fin 2) ℝ) : Matrix _ _ _) =
    !![(d:ℝ), 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dilR, dilation, mkOfDetNeZero]

lemma det_dilR (d : ℕ) (hd : 0 < d) : (dilR d hd).det.val = d := by
  rw [val_det_apply, val_dilR, Matrix.det_fin_two]
  simp

lemma delta_dilate_slash (d : ℕ) (hd : 0 < d) (τ : ℍ) :
    CuspForm.translate CuspForm.discriminant (dilR d hd) τ =
    ModularForm.eta ((d:ℂ) * (τ : ℂ)) ^ 24 * (d : ℂ)^11 := by
  let g := dilR d hd
  have hdet : g.det.val = (d : ℝ) := det_dilR d hd
  have hpos : 0 < g.det.val := hdet ▸ (by exact_mod_cast hd)
  have hz : ↑(g • τ) = (d : ℂ) * (τ : ℂ) := by
    simp [UpperHalfPlane.coe_smul_of_det_pos hpos, num, denom, g,
      val_dilR]
  change (⇑CuspForm.discriminant ∣[(12:ℤ)] g) τ = _
  simp only [slash_apply, σ, hdet,
    CuspForm.coe_discriminant, ModularForm.discriminant, hz]
  simp [denom, g, val_dilR]
  norm_num [hd]

noncomputable def dilConj (d : ℕ) (hd : 0 < d) : Subgroup (GL (Fin 2) ℝ) :=
  toConjAct (dilR d hd)⁻¹ • 𝒮ℒ

lemma arith_dilConj (d : ℕ) (hd : 0 < d) : (dilConj d hd).IsArithmetic := by
  simpa only [map_inv, dilConj, dilR] using Subgroup.IsArithmetic.conj 𝒮ℒ (dilation d hd)⁻¹

lemma T_mem_dilConj (d : ℕ) (hd : 0 < d) : mapGL ℝ ModularGroup.T ∈ dilConj d hd := by
  change _ ∈ toConjAct (dilR d hd)⁻¹ • 𝒮ℒ
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
  refine ⟨ModularGroup.T ^ (d:ℤ), ?_⟩
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply Units.ext
  change (mapGL ℝ (ModularGroup.T ^ (d:ℤ))).val * (dilR d hd).val = (dilR d hd).val * (mapGL ℝ ModularGroup.T).val
  simp only [val_dilR, mapGL_coe_matrix, map_apply_coe, ModularGroup.coe_T_zpow, ModularGroup.coe_T]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

private def restrictCusp {H Γ : Subgroup (GL (Fin 2) ℝ)} (h : H ≤ Γ) {k : ℤ}
    (F : CuspForm Γ k) : CuspForm H k where
  toFun := F
  slash_action_eq' g hg := F.slash_action_eq' g (h hg)
  holo' := F.holo'
  zero_at_cusps' hc := F.zero_at_cusps' (hc.mono h)

theorem exists_eta_base_cusp (f : ℍ → ℂ) (hhol : MDiff f) (hf : ∀ z, f z ≠ 0)
    (hperiod : f ∣[(2:ℤ)] ModularGroup.T = f)
    (hpow : ∀ z : ℍ, f z ^ 12 =
      ModularForm.eta (4 * (z : ℂ))^24 * ModularForm.eta (8 * (z : ℂ))^24) :
    ∃ H : Subgroup (GL (Fin 2) ℝ), H.IsArithmetic ∧ H.strictWidthInfty = 1 ∧
      ∃ G : CuspForm H 2, ⇑G = f := by
  let A := dilConj 4 (by decide)
  let B := dilConj 8 (by decide)
  have : A.IsArithmetic := arith_dilConj _ _
  have : B.IsArithmetic := arith_dilConj _ _
  let Γ := (A ⊓ B).comap (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
  have : Γ.FiniteIndex := Subgroup.IsArithmetic.finiteIndex_comap _
  have hT : ModularGroup.T ∈ Γ := ⟨T_mem_dilConj _ _, T_mem_dilConj _ _⟩
  have hsub : (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ A ⊓ B := Subgroup.map_comap_le _ _
  let Fa := restrictCusp (hsub.trans inf_le_left)
    (CuspForm.translate CuspForm.discriminant (dilR 4 (by decide)))
  let Fb := restrictCusp (hsub.trans inf_le_right)
    (CuspForm.translate CuspForm.discriminant (dilR 8 (by decide)))
  let F : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 24 :=
    (((4:ℝ)^11 * 8^11)⁻¹) • Fa.mulModularForm (CuspForm.toModularFormₗ Fb)
  have hF : ⇑F = f^12 := by
    funext τ
    change (((4:ℝ)^11 * 8^11)⁻¹) •
      (CuspForm.translate CuspForm.discriminant (dilR 4 (by decide)) τ *
       CuspForm.translate CuspForm.discriminant (dilR 8 (by decide)) τ) = f τ ^ 12
    rw [delta_dilate_slash, delta_dilate_slash, hpow]
    norm_num [Complex.real_smul]
    ring
  obtain ⟨H,hH,hHT,G,hG⟩ := exists_cusp_root hT f hhol hf hperiod F hF
  let : H.FiniteIndex := hH
  exact ⟨H, inferInstance, Subgroup.strictWidthInfty_eq_one_of_T_mem hHT, G, hG⟩

end TunnellRoot

namespace TunnellEtaUniform

open Filter Finset Polynomial
open scoped Topology

lemma eval_base_partial (D : ℕ) (q : ℂ) :
    (X * ∏ k ∈ Icc 1 D, ((1 - (X : ℂ[X])^(4*k))^2 * (1-X^(8*k))^2)).eval q =
      q * (∏ k ∈ range D, (1-(q^4)^(k+1)))^2 * (∏ k ∈ range D, (1-(q^8)^(k+1)))^2 := by
  simp only [eval_mul, eval_X, eval_prod, eval_pow, eval_sub, eval_one]
  induction D with
  | zero => simp
  | succ d ih =>
    rw [prod_Icc_succ_top (by omega : 1 ≤ d+1), prod_range_succ, prod_range_succ,
      ← mul_assoc, ih]
    simp only [← pow_mul]
    ring

theorem base_locallyUniform :
    TendstoLocallyUniformlyOn
      (fun (D : ℕ) (q : ℂ) =>
        (X * ∏ k ∈ Icc 1 D, ((1 - (X : ℂ[X])^(4*k))^2 * (1-X^(8*k))^2)).eval q)
      (fun q => q * (∏' k : ℕ, (1 - (q^4)^(k+1)))^2 * (∏' k : ℕ, (1 - (q^8)^(k+1)))^2)
      atTop (Metric.ball 0 1) := by
  let U := Metric.ball (0 : ℂ) 1
  let E (a : ℕ) (q : ℂ) : ℂ := ∏' k : ℕ, (1 - (q^a)^(k+1))
  let P (a D : ℕ) (q : ℂ) : ℂ := ∏ k ∈ range D, (1 - (q^a)^(k+1))
  have maps (a : ℕ) (ha : 0 < a) : Set.MapsTo (fun q : ℂ => q^a) U U := by
    intro q hq
    simp only [U, Metric.mem_ball, dist_zero_right, norm_pow] at hq ⊢
    exact pow_lt_one₀ (norm_nonneg _) hq ha.ne'
  have h (a : ℕ) (ha : 0 < a) : TendstoLocallyUniformlyOn (P a) (E a) atTop U := by
    dsimp only [P, E]
    exact (ModularForm.multipliableLocallyUniformlyOn_one_sub_pow.comp _ (maps a ha)
      (by fun_prop)).hasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
  have hc (a : ℕ) (ha : 0 < a) : ContinuousOn (E a) U := by
    dsimp only [E]
    exact ModularForm.differentiableOn_tprod_one_sub_pow.continuousOn.comp (by fun_prop) (maps a ha)
  have hi : TendstoLocallyUniformlyOn (fun (_ : ℕ) (q : ℂ) => q) id atTop U := by
    intro u hu x _
    exact ⟨Set.univ, univ_mem, .of_forall fun _ y _ => refl_mem_uniformity hu⟩
  have hs (a : ℕ) (ha : 0 < a) := (h a ha).mul₀ (h a ha) (hc a ha) (hc a ha)
  have hu := (hi.mul₀ (hs 4 (by decide)) continuousOn_id ((hc 4 (by decide)).mul (hc 4 (by decide)))).mul₀
    (hs 8 (by decide)) (continuousOn_id.mul ((hc 4 (by decide)).mul (hc 4 (by decide))))
    ((hc 8 (by decide)).mul (hc 8 (by decide)))
  simp_rw [eval_base_partial]
  simp only [pow_two]
  exact hu

end TunnellEtaUniform

namespace TunnellTaylor

open Filter Polynomial Finset
open scoped Topology

lemma deriv_eval (p : ℂ[X]) :
    deriv (fun z => p.eval z) = fun z => p.derivative.eval z :=
  funext fun z => (p.hasDerivAt z).deriv

lemma taylor_of_convergent_polynomials (P : ℕ → ℂ[X]) (f : ℂ → ℂ)
    (h : TendstoLocallyUniformlyOn (fun D z => (P D).eval z) f atTop (Metric.ball 0 1))
    (m : ℕ) (b : ℂ) (hst : ∀ D ≥ m, (P D).coeff m = b) :
    (m.factorial : ℂ)⁻¹ * iteratedDeriv m f 0 = b := by
  have iter (j : ℕ) : TendstoLocallyUniformlyOn
      (fun D z => (derivative^[j] (P D)).eval z) (iteratedDeriv j f)
      atTop (Metric.ball 0 1) := by
    induction j with
    | zero => simpa using h
    | succ j ih =>
      have h' := ih.deriv (Eventually.of_forall fun D => (derivative^[j] (P D)).differentiableOn)
        Metric.isOpen_ball
      simpa only [iteratedDeriv_succ, Function.comp_def, deriv_eval, Function.iterate_succ_apply'] using h'
  have ht := (iter m).tendsto_at (show (0 : ℂ) ∈ Metric.ball 0 1 by simp)
  have hconst : ∀ᶠ D in atTop, (derivative^[m] (P D)).eval 0 = (m.factorial : ℂ) * b := by
    filter_upwards [eventually_ge_atTop m] with D hD
    rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
    simp [hst D hD, mul_comm, Nat.descFactorial_self]
  have hev : iteratedDeriv m f 0 = (m.factorial : ℂ) * b :=
    tendsto_nhds_unique ht (tendsto_nhds_of_eventually_eq hconst)
  rw [hev]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero m), one_mul]

lemma coeff_mul_one_sub_pow {R : Type*} [CommRing R] (p : R[X]) {m k : ℕ} (hk : m < k) :
    (p * (1 - X ^ k)).coeff m = p.coeff m := by
  simp only [mul_sub, mul_one, coeff_sub, coeff_mul_X_pow', if_neg (by omega : ¬k ≤ m), sub_zero]

lemma base_stable {R : Type*} [CommRing R] (m D : ℕ) (hD : m ≤ D) :
    (X * ∏ k ∈ Icc 1 D, ((1 - (X : R[X])^(4*k))^2 * (1-X^(8*k))^2)).coeff m =
    (X * ∏ k ∈ Icc 1 m, ((1 - (X : R[X])^(4*k))^2 * (1-X^(8*k))^2)).coeff m := by
  induction D, hD using Nat.le_induction with
  | base => rfl
  | succ D hD ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ D+1)]
    simp only [pow_two, ← mul_assoc]
    rw [coeff_mul_one_sub_pow _ (by omega : m < 8*(D+1)),
      coeff_mul_one_sub_pow _ (by omega : m < 8*(D+1)),
      coeff_mul_one_sub_pow _ (by omega : m < 4*(D+1)),
      coeff_mul_one_sub_pow _ (by omega : m < 4*(D+1))]
    simpa only [pow_two, ← mul_assoc] using ih

lemma base_taylor (f : ℂ → ℂ)
    (h : TendstoLocallyUniformlyOn
      (fun (D : ℕ) (z : ℂ) => z * ∏ k ∈ Icc 1 D, ((1-z^(4*k))^2 * (1-z^(8*k))^2))
      f atTop (Metric.ball 0 1)) (m : ℕ) :
    (m.factorial : ℂ)⁻¹ * iteratedDeriv m f 0 =
      (((X * ∏ k ∈ Icc 1 m, ((1-(X : ℤ[X])^(4*k))^2 * (1-X^(8*k))^2)).coeff m : ℤ) : ℂ) := by
  let P (D : ℕ) : ℤ[X] := X * ∏ k ∈ Icc 1 D, ((1-X^(4*k))^2 * (1-X^(8*k))^2)
  apply taylor_of_convergent_polynomials (fun D => (P D).map (Int.castRingHom ℂ))
  · simpa only [P, Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_mul,
      Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_one,
      Polynomial.eval_X] using h
  · intro D hD
    rw [Polynomial.coeff_map]
    exact congrArg (fun z : ℤ => (z : ℂ)) (base_stable (R := ℤ) m D hD)

end TunnellTaylor

namespace TunnellEtaValue
open UpperHalfPlane Function MatrixGroups ModularForm
open scoped Manifold Real Topology

noncomputable def etaValue (z : ℍ) : ℂ :=
  eta (4*(z:ℂ))^2 * eta (8*(z:ℂ))^2

noncomputable def diskValue (q : ℂ) : ℂ :=
  q * (∏' k : ℕ, (1-(q^4)^(k+1)))^2 * (∏' k : ℕ, (1-(q^8)^(k+1)))^2

lemma etaValue_hol : MDiff etaValue := by
  have h (a : ℕ) (ha : 0 < a) : MDiff (fun z : ℍ => eta ((a:ℂ)*z)) := by
    intro z
    have hz : (a:ℂ)*(z:ℂ) ∈ upperHalfPlaneSet := by
      change 0 < ((a:ℂ)*(z:ℂ)).im
      simpa [Complex.mul_im] using mul_pos (Nat.cast_pos.mpr ha : 0 < (a : ℝ)) z.im_pos
    exact (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).mdifferentiableAt.comp z
      (mdifferentiableAt_const.mul (UpperHalfPlane.mdifferentiable_coe z))
  exact ((h 4 (by decide)).pow 2).mul ((h 8 (by decide)).pow 2)

lemma etaValue_ne (z : ℍ) : etaValue z ≠ 0 := by
  have h (a : ℕ) (ha : 0 < a) : eta ((a:ℂ)*z) ≠ 0 := by
    apply eta_ne_zero
    change 0 < ((a:ℂ)*(z:ℂ)).im
    simpa [Complex.mul_im] using mul_pos (Nat.cast_pos.mpr ha : 0 < (a:ℝ)) z.im_pos
  exact mul_ne_zero (pow_ne_zero 2 (h 4 (by decide))) (pow_ne_zero 2 (h 8 (by decide)))

lemma etaValue_pow (z : ℍ) :
    etaValue z ^ 12 = eta (4*(z:ℂ)) ^ 24 * eta (8*(z:ℂ)) ^ 24 := by
  simp only [etaValue, mul_pow, ← pow_mul]

lemma qparam_dilate (a : ℕ) (z : ℂ) :
    Periodic.qParam 1 ((a:ℂ)*z) = (Periodic.qParam 1 z)^a := by
  simp only [Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_nat_mul]
  congr 1
  ring

lemma etaValue_eq (z : ℍ) : etaValue z = diskValue (Periodic.qParam 1 z) := by
  have hlead : Periodic.qParam 24 (4*(z:ℂ))^2 * Periodic.qParam 24 (8*(z:ℂ))^2 =
      Periodic.qParam 1 z := by
    simp only [Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]
    push_cast
    congr 1
    ring
  unfold etaValue diskValue eta eta_q
  rw [show (4:ℂ) = (4:ℕ) by norm_num, qparam_dilate,
    show (8:ℂ) = (8:ℕ) by norm_num, qparam_dilate]
  rw [mul_pow, mul_pow]
  linear_combination (∏' k : ℕ, (1-(Periodic.qParam 1 z ^ 4)^(k+1)))^2 *
    (∏' k : ℕ, (1-(Periodic.qParam 1 z ^ 8)^(k+1)))^2 * hlead

lemma etaValue_period : etaValue ∣[(2:ℤ)] ModularGroup.T = etaValue := by
  funext z
  have hd : denom (ModularGroup.T : GL (Fin 2) ℝ) z = 1 := by
    simp [denom, Matrix.SpecialLinearGroup.map_apply_coe, ModularGroup.coe_T]
  rw [SL_slash_apply, hd, one_zpow, mul_one, modular_T_smul]
  simp only [etaValue_eq]
  have h : Periodic.qParam 1 (1+(z:ℂ)) = Periodic.qParam 1 z := by
    simp only [Periodic.qParam, Complex.ofReal_one, div_one, mul_add, mul_one, Complex.exp_add]
    rw [show 2*(Real.pi:ℂ)*Complex.I = (2*Real.pi:ℝ)*Complex.I by push_cast; rfl]
    simp
  change diskValue (Periodic.qParam 1 (1+(z:ℂ))) = _
  rw [h]

lemma cusp_disk_near_zero {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (hwidth : Γ.strictWidthInfty = 1) (G : CuspForm Γ 2) (hg : ⇑G = etaValue) :
    UpperHalfPlane.cuspFunction 1 G =ᶠ[𝓝 0] diskValue := by
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : 0 < (1:ℝ))] with q hq
  by_cases h0 : q=0
  · subst q
    rw [CuspFormClass.cuspFunction_apply_zero G one_pos (hwidth ▸ Γ.strictWidthInfty_mem_strictPeriods)]
    simp [diskValue]
  have him := Periodic.im_invQParam_pos_of_norm_lt_one one_pos (by simpa using hq : ‖q‖ < 1) h0
  let z : ℍ := ⟨Periodic.invQParam 1 q, him⟩
  have hqz : Periodic.qParam 1 (z:ℂ) = q := Periodic.qParam_right_inv one_ne_zero h0
  rw [← hqz, SlashInvariantFormClass.eq_cuspFunction G z
    (hwidth ▸ Γ.strictWidthInfty_mem_strictPeriods) one_ne_zero, hg, etaValue_eq]

end TunnellEtaValue

open UpperHalfPlane MatrixGroups
open TunnellEtaValue

theorem TunnellEtaValue.actual_form :
    ∃ (H : Subgroup (GL (Fin 2) ℝ)) (hH : H.IsArithmetic) (_ : H.strictWidthInfty = 1)
      (F : CuspForm H 2), (∀ z : ℍ, F z = TunnellFricke.h (4*(z:ℂ))) ∧
      ∀ m : ℕ, (qExpansion 1 F).coeff m = (((Polynomial.X *
        ∏ i ∈ Finset.Icc 1 m, ((1-(Polynomial.X:Polynomial ℤ)^(4*i))^2*(1-Polynomial.X^(8*i))^2)).coeff m:ℤ):ℂ) := by
  obtain ⟨H, hH, hw, G, hg⟩ := TunnellRoot.exists_eta_base_cusp etaValue
    etaValue_hol etaValue_ne etaValue_period etaValue_pow
  let _ := hH
  refine ⟨H, hH, hw, G, ?_, ?_⟩
  · intro z
    rw [hg]
    simp only [etaValue,TunnellFricke.h,show 2*(4*(z:ℂ)) = 8*z by ring]
  intro m
  rw [qExpansion_coeff, (cusp_disk_near_zero hw G hg).iteratedDeriv_eq]
  apply TunnellTaylor.base_taylor
  unfold diskValue
  convert TunnellEtaUniform.base_locallyUniform using 1
  funext D z
  simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_one, Polynomial.eval_X]

end

section

/- Uniqueness of analytic continuation and the normalized central Mellin integral. -/

namespace TunnellMellin

open Filter Set Complex UpperHalfPlane MatrixGroups MeasureTheory
open scoped Topology ModularForm

theorem entire_unique {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ)
    (B : ℝ) (h : ∀ x : ℝ, B<x → f x = g x) : f = g := by
  let a : ℝ := B+1
  have hm : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] a) (𝓝[≠] (a:ℂ)) := by
    exact continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (fun _ _ => by simp_all)
  apply hf.eq_of_frequently_eq hg (hm.frequently ?_)
  apply Filter.Eventually.frequently
  filter_upwards [(eventually_gt_nhds (show B<a by dsimp [a]; linarith)).filter_mono nhdsWithin_le_nhds] with x hx
  exact h x hx

theorem unique_euler_product {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hg : AnalyticOnNhd ℂ g univ) {I : Type*} (u : ℝ → I → ℂ) (B : ℝ)
    (h₁ : ∀ x : ℝ, B<x → HasProd (u x) (f x))
    (h₂ : ∀ x : ℝ, B<x → HasProd (u x) (g x)) : f = g :=
  entire_unique hf hg B (fun x hx => (h₁ x hx).unique (h₂ x hx))

theorem central_integral {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (F : CuspForm Γ 2) :
    ModularForm.L (by decide : (0:ℤ)<2) F 1 =
      (2*Real.pi:ℂ) * ∫ t in Ioi (0:ℝ), F (ofComplex (Complex.I*t)) := by
  rw [ModularForm.L,CuspForm.Λ_eq_mellin,Complex.Gammaℂ_one]
  simp [mellin, smul_eq_mul, mul_comm, div_eq_mul_inv]

end TunnellMellin

end

section

/- The central value of a twist as vertical integrals at rational cusps. -/

namespace TunnellModularSymbol

open TunnellBaseTranslations TunnellMellin
open MatrixGroups UpperHalfPlane MeasureTheory Set
open scoped ModularForm

lemma integrable_vertical {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (F : CuspForm Γ 2) :
    IntegrableOn (fun t : ℝ => F (ofComplex (Complex.I*t))) (Ioi 0) := by
  have h := ((CuspForm.isStrongFEPair (by decide : (0:ℤ)<2) F).hasMellin 1).1
  simpa [MellinConvergent, ModularForm.weakFEPair] using h

lemma integrable_translate {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (hw : Γ.strictWidthInfty = 1) (F : CuspForm Γ 2) (r : ℚ) :
    IntegrableOn (fun t : ℝ => F ((r:ℝ)+ᵥ ofComplex (Complex.I*t))) (Ioi 0) := by
  obtain ⟨H, hH, _, G, heq⟩ := TunnellTranslate.exists_sum_rational_translates hw F
    (fun _ : Unit => r) (fun _ => 1)
  letI := hH
  simpa [heq] using integrable_vertical G

theorem twist_central_integral {N : ℕ} [NeZero N] (w : ZMod N → ℂ)
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hw : Γ.strictWidthInfty = 1)
    (F : CuspForm Γ 2) :
    ∃ (H : Subgroup (GL (Fin 2) ℝ)) (hH : H.IsArithmetic) (_ : H.strictWidthInfty = 1)
      (G : CuspForm H 2),
      (∀ m : ℕ, (qExpansion 1 G).coeff m = w m * (qExpansion 1 F).coeff m) ∧
      ModularForm.L (by decide : (0:ℤ)<2) G 1 =
        ∑ j : ZMod N, ZMod.dft.symm w j *
          ((2*Real.pi:ℂ) * ∫ t in Ioi (0:ℝ), F ((-(j.val:ℝ)/N)+ᵥ ofComplex (Complex.I*t))) := by
  obtain ⟨H,hH,hW,G,he⟩ := TunnellTranslate.exists_sum_rational_translates hw F
    (fun j : ZMod N => -(j.val:ℚ)/N) (ZMod.dft.symm w)
  letI := hH
  have he' (z : ℍ) : G z = ∑ j : ZMod N, ZMod.dft.symm w j * F ((-(j.val:ℝ)/N)+ᵥ z) := by
    simpa only [Rat.cast_div,Rat.cast_natCast,Rat.cast_neg] using he z
  refine ⟨H,hH,hW,G,TunnellTwistFourier.twist_coefficients w hw hW F G he',?_⟩
  have hi (j : ZMod N) := (integrable_translate hw F (-(j.val:ℚ)/N)).const_mul (ZMod.dft.symm w j)
  rw [central_integral]
  simp_rw [he']
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  · intro j _
    simpa only [Rat.cast_div,Rat.cast_natCast,Rat.cast_neg] using hi j

theorem gauss_sq {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) (he : χ.Even) :
    gaussSum χ ZMod.stdAddChar ^ 2 = (N:ℂ) := by
  have h (k : ZMod N) := hχ.fourierTransform_eq_inv_mul_gaussSum k
  simp only [hq.inv,he.eval_neg] at h
  have h2 := congrFun (ZMod.dft_dft (χ : ZMod N → ℂ)) 1
  rw [funext h, ZMod.dft_mul_const] at h2
  dsimp only at h2
  rw [h] at h2
  simpa [pow_two,he.eval_neg] using h2

theorem primitive_weights {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) (he : χ.Even) (j : ZMod N) :
    (gaussSum χ ZMod.stdAddChar) * ZMod.dft.symm (χ : ZMod N → ℂ) j = χ j := by
  rw [ZMod.invDFT_apply',hχ.fourierTransform_eq_inv_mul_gaussSum,neg_neg,hq.inv, smul_eq_mul]
  have h := gauss_sq hχ hq he
  field_simp [NeZero.ne (N:ℂ)]
  linear_combination χ j * h

end TunnellModularSymbol

end

section

namespace TunnellTwistCharacter

def weight (n m : ℕ) : ℤ := if Odd m then jacobiSym n m else 0

lemma weight_one (n : ℕ) : weight n 1 = 1 := by simp [weight]

lemma weight_mul (n a b : ℕ) : weight n (a*b) = weight n a * weight n b := by
  by_cases ha : Odd a <;> by_cases hb : Odd b <;> simp [weight, Nat.odd_mul, ha, hb]
  exact jacobiSym.mul_right' _ (fun e => by simp [e] at ha) (fun e => by simp [e] at hb)

lemma weight_mod (n m : ℕ) : weight n (m % (4*n)) = weight n m := by
  have he : Even (4*n) := Even.mul_right (by decide) _
  have h : Odd (m % (4*n)) ↔ Odd m := by
    simp only [Nat.odd_iff, Nat.mod_mod_of_dvd _ he.two_dvd]
  by_cases hm : Odd m
  · simpa [weight, h, hm] using (jacobiSym.mod_right' n hm).symm
  · simp [weight, h, hm]

lemma weight_periodic (n : ℕ) : Function.Periodic (weight n) (4*n) := by
  intro m
  rw [← weight_mod n (m+4*n), Nat.add_mod_right, weight_mod]

lemma weight_prime (n : ℕ) (p : Nat.Primes) [Fact p.val.Prime] (hp : p.val ≠ 2) :
    weight n p.val = quadraticChar (ZMod p.val) (n : ZMod p.val) := by
  have ho : Odd p.val := Nat.odd_iff.mpr (p.property.eq_two_or_odd.resolve_left hp)
  rw [weight, if_pos ho, ← jacobiSym.legendreSym.to_jacobiSym, legendreSym]
  simp

lemma weight_bad_prime (n : ℕ) (p : Nat.Primes) (hp : p.val ∣ 2*n) :
    weight n p.val = 0 := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  by_cases h : p.val = 2
  · simp [weight, h]
  · have hd : p.val ∣ n := (p.property.dvd_mul.mp hp).resolve_left
      (fun e => h ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two).mp e))
    rw [weight_prime n p h, (ZMod.natCast_eq_zero_iff n _).mpr hd, quadraticChar_zero]

lemma weight_zero_of_not_coprime (n m : ℕ) (h : ¬m.Coprime (4*n)) :
    weight n m = 0 := by
  by_cases hm : Odd m
  · letI : NeZero m := ⟨fun e => by simp [e] at hm⟩
    rw [weight, if_pos hm, jacobiSym.eq_zero_iff_not_coprime]
    intro h'
    apply h
    apply Nat.coprime_mul_iff_right.mpr
    constructor
    · exact hm.coprime_two_right.pow_right 2
    · apply Nat.Coprime.symm
      simpa [Nat.coprime_iff_gcd_eq_one, Int.gcd_eq_natAbs] using h'
  · simp [weight, hm]

noncomputable def character (n : ℕ) (hn : n ≠ 0) : DirichletCharacter ℂ (4*n) where
  toFun z := (weight n z.val : ℂ)
  map_one' := by rw [ZMod.val_one_eq_one_mod, weight_mod, weight_one]; norm_num
  map_mul' a b := by rw [ZMod.val_mul, weight_mod, weight_mul]; push_cast; rfl
  map_nonunit' a ha := by
    letI : NeZero (4*n) := ⟨Nat.mul_ne_zero (by decide) hn⟩
    have h : ¬a.val.Coprime (4*n) := fun hc => ha (by
      simpa [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime _ _).mpr hc)
    rw [weight_zero_of_not_coprime n a.val h]
    norm_num

lemma character_apply_nat (n : ℕ) (hn : n ≠ 0) (m : ℕ) :
    character n hn (m : ZMod (4*n)) = (weight n m : ℂ) := by
  change (weight n (m : ZMod (4*n)).val : ℂ) = _
  rw [ZMod.val_natCast, weight_mod]

end TunnellTwistCharacter

end

section

/- The Jacobi character of conductor 8d, for squarefree d congruent to one modulo four. -/

namespace TunnellTwistCharacter

lemma character_quadratic (n : ℕ) (hn : n ≠ 0) : (character n hn).IsQuadratic := by
  intro a
  change (weight n a.val : ℂ) = 0 ∨ (weight n a.val : ℂ) = 1 ∨ (weight n a.val : ℂ) = -1
  by_cases ha : Odd a.val
  · rw [weight, if_pos ha]
    exact_mod_cast jacobiSym.trichotomy n a.val
  · simp [weight,ha]

lemma weight_two_mul {d a : ℕ} (hd : d%4=1) (ha : Odd a) :
    weight (2*d) a = ZMod.χ₈ a * jacobiSym a d := by
  rw [weight,if_pos ha,Nat.cast_mul,Nat.cast_ofNat,jacobiSym.mul_left,jacobiSym.at_two ha,
    jacobiSym.quadratic_reciprocity_one_mod_four hd ha]

lemma character_even {d : ℕ} (hd : d%4=1) :
    (character (2*d) (by omega)).Even := by
  let a := 8*d - 1
  have hz : (-1 : ZMod (4*(2*d))) = (a : ℕ) := by
    dsimp [a]
    rw [Nat.cast_sub (by omega), show 8*d = 4*(2*d) by ring]
    simp
  change character (2*d) _ (-1) = 1
  rw [hz, character_apply_nat, weight_two_mul hd (Nat.odd_iff.mpr (by dsimp [a]; omega))]
  have hj : jacobiSym (a:ℤ) d = jacobiSym (-1) d := by
    apply jacobiSym.mod_left'
    dsimp [a]
    rw [Nat.cast_sub (by omega)]
    push_cast
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-8,by ring⟩
  rw [hj,jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)),ZMod.χ₄_nat_mod_four,hd,
    ZMod.χ₈_nat_mod_eight, show a%8 = 7 by dsimp [a]; omega]
  exact_mod_cast (by decide : ZMod.χ₈ (7:ℕ) * ZMod.χ₄ (1:ℕ) = 1)

lemma primitive_of_witness {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hw : ∀ p : ℕ, p.Prime → p ∣ N → ∃ a : ℕ, a ≡ 1 [MOD N/p] ∧ χ a = -1) :
    χ.IsPrimitive := by
  change χ.conductor = N
  by_contra h
  obtain ⟨q,heq⟩ := χ.conductor_dvd_level
  have hq : q ≠ 1 := by rintro rfl; simp_all
  obtain ⟨p,hp,r,hr⟩ := Nat.exists_prime_and_dvd hq
  have hn : N = (χ.conductor*r)*p := heq.trans (by rw [hr]; ring)
  have hdiv : N/p = χ.conductor*r := (congrArg (· / p) hn).trans (Nat.mul_div_cancel _ hp.pos)
  obtain ⟨a,ha,hval⟩ := hw p hp (hn ▸ dvd_mul_left _ _)
  have hunit : IsUnit (a : ZMod N) := by
    by_contra hu
    rw [χ.map_nonunit hu] at hval
    norm_num at hval
  have hsmall : (a : ZMod χ.conductor) = 1 := by
    have h := ha.of_dvd (show χ.conductor ∣ N/p by rw [hdiv]; exact dvd_mul_right _ _)
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  have hc := ((ZMod.isUnit_iff_coprime a N).mp hunit).isCoprime
  have hv := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ.primitiveCharacter χ.conductor_dvd_level hc
  rw [χ.changeLevel_primitiveCharacter] at hv
  simp only [Int.cast_natCast] at hv
  rw [hsmall,map_one,hval] at hv
  norm_num at hv

lemma jacobi_congr {a b d : ℕ} (h : a ≡ b [MOD d]) : jacobiSym a d = jacobiSym b d := by
  apply jacobiSym.mod_left'
  exact_mod_cast h

lemma primitive_witness {d : ℕ} (hd : d%4=1) (hs : Squarefree d)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ 4*(2*d)) :
    ∃ a : ℕ, a ≡ 1 [MOD 4*(2*d)/p] ∧ weight (2*d) a = -1 := by
  have hd0 : 0 < d := by omega
  by_cases ht : p = 2
  · subst p
    refine ⟨4*d+1, ?_, ?_⟩
    · rw [show 4*(2*d)/2 = 4*d by omega]
      simp [Nat.ModEq]
    · rw [weight_two_mul hd (Nat.odd_iff.mpr (by omega)),ZMod.χ₈_nat_mod_eight,
        show (4*d+1)%8=5 by omega, jacobi_congr (b:=1) (by simp [Nat.ModEq]),
        Nat.cast_one,jacobiSym.one_left,mul_one]
      decide
  have h8 : p.Coprime 8 := by
    have hc := hp.coprime_iff_not_dvd.mpr (fun h => ht ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
    exact hc.pow_right 3
  have hpd : p ∣ d := (hp.dvd_mul.mp (show p ∣ 8*d by rwa [show 8*d = 4*(2*d) by ring])).resolve_left
    (hp.coprime_iff_not_dvd.mp h8)
  obtain ⟨v,hv⟩ := hpd
  have hpv : p.Coprime v := Nat.coprime_of_squarefree_mul (hv ▸ hs)
  have hv0 : v ≠ 0 := by rintro rfl; simp_all
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b,hb⟩ := quadraticChar_exists_neg_one (F := ZMod p) (by simpa only [ZMod.ringChar_zmod_n] using ht)
  obtain ⟨a,hab,ha1⟩ := Nat.chineseRemainder (Nat.coprime_mul_iff_right.mpr ⟨h8,hpv⟩) b.val 1
  have ht8 : a ≡ 1 [MOD 8] := ha1.of_dvd (dvd_mul_right ..)
  have hv1 : a ≡ 1 [MOD v] := ha1.of_dvd (dvd_mul_left ..)
  have ha : Odd a := Nat.odd_iff.mpr (ht8.of_dvd (by decide : 2 ∣ 8))
  have hj : jacobiSym a p = -1 := by
    rw [←jacobiSym.legendreSym.to_jacobiSym,legendreSym]
    simpa only [ZMod.natCast_eq_natCast_iff, Int.cast_natCast,
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hab,ZMod.natCast_zmod_val] using hb
  refine ⟨a, ?_, ?_⟩
  · convert ha1 using 1
    rw [hv,show 4*(2*(p*v)) = (8*v)*p by ring, Nat.mul_div_cancel _ hp.pos]
  · rw [weight_two_mul hd ha,ZMod.χ₈_nat_mod_eight,show a%8=1 from ht8,hv,
      jacobiSym.mul_right' _ hp.ne_zero hv0,hj,jacobi_congr hv1]
    simp

theorem character_primitive {d : ℕ} (hd : d%4=1) (hs : Squarefree d) :
    (character (2*d) (by omega)).IsPrimitive := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  apply primitive_of_witness
  intro p hp hpn
  obtain ⟨a,ha,hw⟩ := primitive_witness hd hs hp hpn
  refine ⟨a,ha,?_⟩
  rw [character_apply_nat,hw]
  norm_num


end TunnellTwistCharacter

end

section

/- Normalize the modular-symbol formula for the primitive positive even quadratic twists. -/

namespace TunnellModularSymbol

open MatrixGroups UpperHalfPlane MeasureTheory Set TunnellTwistCharacter
open scoped ModularForm

noncomputable def periodSymbol {Γ : Subgroup (GL (Fin 2) ℝ)} (F : CuspForm Γ 2) (r : ℝ) : ℂ :=
  (2*Real.pi:ℂ) * ∫ t in Ioi (0:ℝ), F (r +ᵥ ofComplex (Complex.I*t))

lemma reflected_symbol {Γ : Subgroup (GL (Fin 2) ℝ)} (F : CuspForm Γ 2)
    (hw : Γ.strictWidthInfty = 1) {N : ℕ} [NeZero N] (a : ZMod N) :
    periodSymbol F (-((-a).val:ℝ)/N) = periodSymbol F ((a.val:ℝ)/N) := by
  by_cases ha : a=0
  · simp [ha]
  have hN : (N:ℝ) ≠ 0 := NeZero.ne _
  have he : -((-a).val:ℝ)/N = -1 + (a.val:ℝ)/N := by
    rw [ZMod.neg_val,if_neg ha,Nat.cast_sub (ZMod.val_lt _).le]
    field_simp
    ring
  have hper : (-1:ℝ) ∈ Γ.strictPeriods :=
    Γ.strictPeriods.neg_mem (hw ▸ Γ.strictWidthInfty_mem_strictPeriods)
  simp only [he,periodSymbol, add_vadd, SlashInvariantForm.vAdd_apply_of_mem_strictPeriods F _ hper]

theorem scaled_twist_integral {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) (he : χ.Even)
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hw : Γ.strictWidthInfty = 1)
    (F : CuspForm Γ 2) :
    ∃ (H : Subgroup (GL (Fin 2) ℝ)) (hH : H.IsArithmetic) (_ : H.strictWidthInfty = 1)
      (G : CuspForm H 2),
      (∀ m : ℕ, (qExpansion 1 G).coeff m = χ m * (qExpansion 1 F).coeff m) ∧
      gaussSum χ ZMod.stdAddChar * ModularForm.L (by decide : (0:ℤ)<2) G 1 =
        ∑ j : ZMod N, χ j * periodSymbol F ((j.val:ℝ)/N) := by
  obtain ⟨H,hH,hW,G,hcf,hV⟩ := twist_central_integral (χ : ZMod N → ℂ) hw F
  refine ⟨H,hH,hW,G,hcf,?_⟩
  rw [hV,Finset.mul_sum]
  simp_rw [←mul_assoc,primitive_weights hχ hq he]
  exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun j => by
    simp only [Equiv.neg_apply,he.eval_neg]
    simpa only [neg_neg,periodSymbol,mul_assoc] using congrArg (χ j * ·) (reflected_symbol F hw (-j)))

theorem gauss_sign {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) (he : χ.Even) :
    ∃ ε : ℤ, (ε=1 ∨ ε = -1) ∧ (Real.sqrt N:ℂ) = ε * gaussSum χ ZMod.stdAddChar := by
  have h := gauss_sq hχ hq he
  have hsq : (Real.sqrt N:ℂ)^2 = (N:ℂ) := by exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsq.trans h.symm) with e|e
  · exact ⟨1,Or.inl rfl,by simpa using e⟩
  · exact ⟨-1,Or.inr rfl,by simpa using e⟩

theorem jacobi_twist_integral {n : ℕ} (hn : n%8=2) (hs : Squarefree n)
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hw : Γ.strictWidthInfty = 1)
    (F : CuspForm Γ 2) :
    haveI : NeZero (4*n) := ⟨by omega⟩
    let χ := character n (by omega)
    ∃ (H : Subgroup (GL (Fin 2) ℝ)) (hH : H.IsArithmetic) (_ : H.strictWidthInfty = 1)
      (G : CuspForm H 2),
      (∀ m : ℕ, (qExpansion 1 G).coeff m = (weight n m:ℂ) * (qExpansion 1 F).coeff m) ∧
      gaussSum χ ZMod.stdAddChar * ModularForm.L (by decide : (0:ℤ)<2) G 1 =
        ∑ j : ZMod (4*n), (weight n j.val:ℂ) * periodSymbol F ((j.val:ℝ)/(4*n)) ∧
      gaussSum χ ZMod.stdAddChar ^ 2 = (4*n:ℂ) := by
  obtain ⟨d,hd⟩ : 2 ∣ n := by exact Nat.dvd_of_mod_eq_zero (by omega)
  subst n
  have hd4 : d%4=1 := by omega
  have hsd := hs.squarefree_of_dvd (dvd_mul_left d 2)
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  let χ := character (2*d) (by omega)
  let hh := character_primitive hd4 hsd
  let hq := character_quadratic (2*d) (by omega)
  let he := character_even hd4
  obtain ⟨H,hH,hW,G,hcf,hV⟩ := scaled_twist_integral hh hq he hw F
  refine ⟨H,hH,hW,G,fun m => ?_,?_,?_⟩
  · simpa only [character_apply_nat] using hcf m
  · have hc (j : ZMod (4*(2*d))) : character (2*d) (by omega) j = (weight (2*d) j.val:ℂ) := rfl
    simpa only [Nat.cast_mul,Nat.cast_ofNat,hc] using hV
  · simpa only [Nat.cast_mul,Nat.cast_ofNat] using gauss_sq hh hq he

theorem rational_period_of_paired_symbols {n : ℕ} (hn : n%8=2) (hs : Squarefree n)
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hw : Γ.strictWidthInfty=1)
    (F : CuspForm Γ 2) (Ω : ℂ)
    (hper : ∀ r : ℚ, ∃ c : ℚ, periodSymbol F (r:ℝ) + periodSymbol F (-(r:ℝ)) = c*Ω) :
    ∃ (H : Subgroup (GL (Fin 2) ℝ)) (hH : H.IsArithmetic) (_ : H.strictWidthInfty=1)
      (G : CuspForm H 2) (c : ℚ),
      (∀ m : ℕ, (qExpansion 1 G).coeff m = (weight n m:ℂ) * (qExpansion 1 F).coeff m) ∧
      (Real.sqrt n:ℂ)*ModularForm.L (by decide : (0:ℤ)<2) G 1 = c*Ω := by
  classical
  obtain ⟨d,hd⟩ : 2 ∣ n := by exact Nat.dvd_of_mod_eq_zero (by omega)
  subst n
  have hd4 : d%4=1 := by omega
  have hsd := hs.squarefree_of_dvd (dvd_mul_left d 2)
  let n := 2*d
  let χ := character n (by dsimp [n]; omega)
  letI : NeZero (4*n) := ⟨by dsimp [n]; omega⟩
  have he : χ.Even := character_even hd4
  obtain ⟨ε,hε,hg⟩ := gauss_sign (character_primitive hd4 hsd) (character_quadratic n _) he
  obtain ⟨H,hH,hW,G,hcf,hV,_⟩ := jacobi_twist_integral hn hs hw F
  let P (j : ZMod (4*n)) := periodSymbol F ((j.val:ℝ)/(4*n))
  let M (j : ZMod (4*n)) := periodSymbol F (-(j.val:ℝ)/(4*n))
  have hsym : ∑ j, χ j * P j = ∑ j, χ j * M j := by
    apply Fintype.sum_equiv (Equiv.neg _)
    intro j
    rw [Equiv.neg_apply,he.eval_neg]
    congr 1
    simpa only [P,M,Nat.cast_mul,Nat.cast_ofNat] using (reflected_symbol F hw j).symm
  choose c hc using hper
  let r (j : ZMod (4*n)) : ℚ := (j.val:ℚ)/(4*n)
  let C : ℚ := ∑ j : ZMod (4*n), (weight n j.val:ℚ)*c (r j)
  have hc' (j : ZMod (4*n)) : P j + M j = (c (r j):ℂ)*Ω := by
    simpa only [P,M,r,Rat.cast_div,Rat.cast_natCast,Rat.cast_mul,Rat.cast_ofNat,neg_div]
      using hc (r j)
  have hC : (2:ℂ) * (∑ j, χ j*P j) = C*Ω := by
    calc _ = (∑ j, χ j*P j) + ∑ j, χ j*M j := by rw [←hsym,two_mul]
         _ = ∑ j, χ j*(P j+M j) := by simp [mul_add,Finset.sum_add_distrib]
         _ = _ := by
           simp only [hc',C,Rat.cast_sum,Rat.cast_mul,Rat.cast_intCast,Finset.sum_mul,mul_assoc]
           rfl
  have hv : gaussSum χ ZMod.stdAddChar * ModularForm.L (by decide : (0:ℤ)<2) G 1 = ∑ j, χ j*P j := hV
  have hgs : (2:ℂ)*(Real.sqrt n:ℂ) = ε * gaussSum χ ZMod.stdAddChar := by
    have heq : (Real.sqrt (((4*n:ℕ):ℝ)):ℂ) = 2*(Real.sqrt n:ℂ) := by
      rw [Nat.cast_mul,Nat.cast_ofNat,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), Complex.ofReal_mul]
      norm_num
    rw [←heq]
    exact hg
  refine ⟨H,hH,hW,G,((ε:ℚ)*C/4),hcf,?_⟩
  change (Real.sqrt n:ℂ) * _ = _
  push_cast
  linear_combination (ModularForm.L (by decide : (0:ℤ)<2) G 1 / 2)*hgs +
    (ε:ℂ)/2*hv + (ε:ℂ)/4*hC


end TunnellModularSymbol

end

section

/- Generation of all rational cusps by translation and the level-two Fricke involution. -/

namespace TunnellFrickeOrbit

theorem rational_cusps (P : ℚ → Prop) (hzero : P 0)
    (hT : ∀ x k, P x → P (x + (k:ℤ)))
    (hW : ∀ x, x ≠ 0 → P x → P (-1/(2*x))) (x : ℚ) : P x := by
  have hnegHalf : P (-1/2) := by
    simpa using hW 1 one_ne_zero (by simpa using hT 0 1 hzero)
  have hfrac (d : ℕ) : ∀ a : ℤ, 0<d → P ((a:ℚ)/d) := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro a hd
      let r := a.bmod d
      have hdq : (d:ℚ) ≠ 0 := by positivity
      have bound := (Int.bmod_eq_iff (a:=a) hd).mp (rfl : a.bmod d = r)
      have eqr : (a:ℚ)/d = (r:ℚ)/d + (a.bdiv d:ℚ) := by
        field_simp
        exact_mod_cast (Int.bmod_add_bdiv a d).symm
      rw [eqr]
      apply hT
      by_cases hr0 : r = 0
      · simpa [hr0] using hzero
      have hrq : (r:ℚ) ≠ 0 := by exact_mod_cast hr0
      by_cases hedge : 2*r = -(d:ℤ)
      · have e : (r:ℚ)/d = -1/2 := by
          have hh : 2*(r:ℚ) = -(d:ℚ) := by exact_mod_cast hedge
          field_simp
          linarith
        rwa [e]
      have hsmall : 2*r.natAbs < d := by omega
      have hpos : 0<2*r.natAbs := by omega
      by_cases hrpos : 0 ≤ r
      · have ee : (r.natAbs : ℚ) = r := by
          have e : (r.natAbs : ℤ) = r := by omega
          simpa only [Int.cast_natCast] using congrArg (fun a : ℤ => (a:ℚ)) e
        have hh := ih (2*r.natAbs) hsmall (-(d:ℤ)) hpos
        rw [Nat.cast_mul,Nat.cast_two,ee,Int.cast_neg,Int.cast_natCast] at hh
        convert hW _ (div_ne_zero (neg_ne_zero.mpr hdq) (mul_ne_zero (by norm_num) hrq)) hh using 1 <;> field_simp <;> ring
      · have ee : (r.natAbs : ℚ) = -r := by
          have e : (r.natAbs : ℤ) = -r := by omega
          simpa only [Int.cast_natCast,Int.cast_neg] using congrArg (fun a : ℤ => (a:ℚ)) e
        have hh := ih (2*r.natAbs) hsmall (d:ℤ) hpos
        rw [Nat.cast_mul,Nat.cast_two,ee,Int.cast_natCast] at hh
        convert hW _ (div_ne_zero hdq (mul_ne_zero (by norm_num) (neg_ne_zero.mpr hrq))) hh using 1 <;> field_simp <;> ring
  simpa only [Rat.num_div_den] using hfrac x.den x.num x.den_pos

noncomputable def integralMultiple (a b : ℂ) : Prop := ∃ c : GaussianInt, a = (c:ℂ)*b

theorem symbols_are_gaussian_multiples (J : ℚ → ℂ)
    (hT : ∀ x (k : ℤ), ∃ u : GaussianInt, J (x+k) = (u:ℂ)*J x)
    (hW : ∀ x, x≠0 → J (-1/(2*x)) = J 0-J x) (x : ℚ) :
    integralMultiple (J x) (J 0) := by
  apply rational_cusps (fun q => integralMultiple (J q) (J 0)) _ _ _ x
  · exact ⟨1,by simp⟩
  · rintro q k ⟨b,hb⟩
    obtain ⟨a,ha⟩ := hT q k
    exact ⟨a*b,by rw [ha,hb]; simp [mul_assoc]⟩
  · rintro q hq ⟨a,ha⟩
    exact ⟨1-a,by rw [hW q hq,ha]; rw [map_sub,map_one]; ring⟩

end TunnellFrickeOrbit

end

section

/- Boundary values of the conductor-32 primitive at all rational cusps. -/

namespace TunnellFricke

open Complex Function Filter Set
open UpperHalfPlane hiding I
open scoped Topology

noncomputable def height (r : ℝ) (z : ℂ) : ℝ := z.im / normSq (z-r)

noncomputable def cusp (r : ℝ) : Filter ℂ := comap (height r) atTop

lemma eventually_upper (r : ℝ) : ∀ᶠ z in cusp r, 0<z.im := by
  filter_upwards [(tendsto_comap (f:=height r) (x:=atTop)).eventually (eventually_gt_atTop 0)] with z hz
  exact (div_pos_iff.mp hz).elim (fun h => h.1) (fun h => False.elim ((normSq_nonneg _).not_gt h.2))

lemma W_involution {z : ℂ} (hz : z ≠ 0) : W (W z) = z := by
  unfold W
  field_simp

lemma W_im (z : ℂ) : (W z).im = height 0 z / 2 := by
  simp [W,height,Complex.div_im,Complex.mul_im,Complex.normSq_mul,pow_two]
  ring

lemma height_add (r t : ℝ) (z : ℂ) : height (r+t) (z+t) = height r z := by
  simp [height,add_sub_add_right_eq_sub]

lemma height_W (r : ℝ) (hr : r≠0) (z : ℂ) (hz : 0<z.im) :
    height (-1/(2*r)) (W z) = 2*r^2*height r z := by
  have hz0 := ne_zero (⟨z,hz⟩:ℍ)
  have hrC : (r:ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  have hz' : z-(r:ℂ)≠0 := by
    intro he
    have e := congrArg Complex.im (sub_eq_zero.mp he)
    simp at e
    linarith
  have dif : W z - ((-1/(2*r):ℝ):ℂ) = (z-r)/(2*z*r) := by
    unfold W
    push_cast
    field_simp
    ring
  rw [height,W_im,dif,normSq_div,height,height]
  simp only [ofReal_zero,sub_zero,map_mul,normSq_ofReal]
  field_simp [Complex.normSq_eq_zero.not.mpr hz0,Complex.normSq_eq_zero.not.mpr hz',hr]
  norm_num [normSq_apply]
  <;> ring

lemma move_W (r : ℝ) (hr : r≠0) : Tendsto W (cusp r) (cusp (-1/(2*r))) := by
  apply tendsto_comap_iff.mpr
  apply Tendsto.congr' _ (tendsto_comap (f:=height r) (x:=atTop) |>.const_mul_atTop (show 0<2*r^2 by positivity))
  filter_upwards [eventually_upper r] with z hz
  exact (height_W r hr z hz).symm

lemma move_add (r t : ℝ) : Tendsto (fun z : ℂ => z+t) (cusp r) (cusp (r+t)) := by
  apply tendsto_comap_iff.mpr
  exact tendsto_comap.congr (fun z => (height_add r t z).symm)

lemma move_zero : Tendsto W (cusp 0) (comap Complex.im atTop) := by
  apply tendsto_comap_iff.mpr
  exact ((tendsto_comap (f:=height 0) (x:=atTop)).atTop_mul_const (by norm_num : (0:ℝ)<2⁻¹)).congr (fun z => by simp [Function.comp_def,W_im,div_eq_mul_inv])

lemma integer_steps (P : ℚ → Prop)
    (hp : ∀ x, P x → P (x+1)) (hm : ∀ x, P x → P (x-1))
    (x : ℚ) (k : ℤ) (hx : P x) : P (x+k) := by
  induction k using Int.induction_on with
  | zero => simpa using hx
  | succ i ih => simpa [Int.cast_add,add_assoc] using hp (x+i) ih
  | pred i ih => simpa [Int.cast_sub,sub_eq_add_neg,add_assoc] using hm (x+(-(i:ℤ):ℚ)) ih

noncomputable def gi : GaussianInt := ⟨0,1⟩
lemma coe_gi : (gi:ℂ) = I := by simp [gi,GaussianInt.toComplex_def]

def Bound (J : ℂ → ℂ) (C : ℂ) (x : ℚ) (a : GaussianInt) : Prop :=
  Tendsto J (cusp x) (𝓝 ((a:ℂ)*C))

theorem cusp_rules {J : ℂ → ℂ} {C : ℂ}
    (h0 : Tendsto J (comap Complex.im atTop) (𝓝 0))
    (hT : ∀ z, 0<z.im → J (z+1) = I*J z)
    (hW : ∀ z, 0<z.im → J (W z) = C-J z) :
    Bound J C 0 1 ∧
    (∀ x a, Bound J C x a → Bound J C (x+1) (gi*a)) ∧
    (∀ x a, Bound J C x a → Bound J C (x-1) (-gi*a)) ∧
    (∀ x, x≠0 → ∀ a, Bound J C x a → Bound J C (-1/(2*x)) (1-a)) := by
  unfold Bound
  refine ⟨?_,?_,?_,?_⟩
  · simp only [map_one,one_mul,Rat.cast_zero]
    have ht := tendsto_const_nhds (x:=C) |>.sub (h0.comp move_zero)
    rw [sub_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_upper 0] with z hz
    simp [Function.comp_def,hW z hz]
  · intro x a ha
    simp only [Rat.cast_add,Rat.cast_one,map_mul,coe_gi,mul_assoc]
    have ht := move_add ((x:ℝ)+1) (-1)
    simp only [add_neg_cancel_right] at ht
    apply (ha.comp ht |>.const_mul I).congr'
    filter_upwards [eventually_upper ((x:ℝ)+1)] with z hz
    have he := hT (z-1) (by simpa using hz)
    simpa [Function.comp_def,sub_eq_add_neg] using he.symm
  · intro x a ha
    simp only [Rat.cast_sub,Rat.cast_one,map_mul,map_neg,coe_gi,mul_assoc]
    have ht := move_add ((x:ℝ)-1) 1
    simp only [sub_add_cancel] at ht
    apply (ha.comp ht |>.const_mul (-I)).congr'
    filter_upwards [eventually_upper ((x:ℝ)-1)] with z hz
    change (-I)*J (z+(1:ℝ)) = J z
    simp [hT z hz,← mul_assoc]
  · intro x hx a ha
    have hr : (x:ℝ) ≠ 0 := by exact_mod_cast hx
    have ht := move_W (-1/(2*(x:ℝ))) (by positivity)
    rw [show -1 / (2 * (-1/(2*(x:ℝ)))) = x by field_simp] at ht
    simp only [Rat.cast_div,Rat.cast_neg,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat,map_sub,map_one,sub_mul,one_mul]
    apply (tendsto_const_nhds (x:=C) |>.sub (ha.comp ht)).congr'
    filter_upwards [eventually_upper (-1/(2*(x:ℝ)))] with z hz
    simp [Function.comp_def,hW z hz]


theorem paired_cusp_values {J : ℂ → ℂ} {C : ℂ}
    (h0 : Tendsto J (comap Complex.im atTop) (𝓝 0))
    (hT : ∀ z, 0<z.im → J (z+1) = I*J z)
    (hW : ∀ z, 0<z.im → J (W z) = C-J z) (r : ℚ) :
    ∃ a : GaussianInt, Bound J C r a ∧ Bound J C (-r) (star a) := by
  obtain ⟨hz,hp,hm,hw⟩ := cusp_rules h0 hT hW
  have hi : star gi = -gi := by rfl
  apply TunnellFrickeOrbit.rational_cusps (fun x => ∃ a : GaussianInt, Bound J C x a ∧ Bound J C (-x) (star a)) _ _ _ r
  · exact ⟨1,hz,by simpa using hz⟩
  · apply integer_steps
    · rintro x ⟨a,h,k⟩
      refine ⟨gi*a,hp x a h,?_⟩
      simpa [star_mul,hi,mul_comm,add_comm,sub_eq_add_neg] using hm (-x) (star a) k
    · rintro x ⟨a,h,k⟩
      refine ⟨-gi*a,hm x a h,?_⟩
      simpa [star_mul,hi,mul_comm,add_comm,sub_eq_add_neg] using hp (-x) (star a) k
  · rintro x hx ⟨a,h,k⟩
    refine ⟨1-a,hw x hx a h,?_⟩
    simpa [div_eq_mul_inv] using hw (-x) (neg_ne_zero.mpr hx) (star a) k

end TunnellFricke

end

section

/- The actual paired vertical integrals are integral multiples of the base central value. -/


namespace TunnellFricke

open Complex Filter Set MeasureTheory TunnellModularSymbol
open UpperHalfPlane hiding I
open scoped Topology

noncomputable def path (r : ℝ) (t : ℂ) := 4*((r:ℂ)+I*t)

lemma path_im (r t : ℝ) : (path r t).im = 4*t := by simp [path,mul_im]

lemma tendsto_path_bottom (r : ℝ) :
    Tendsto (fun t : ℝ => path r t) (𝓝[>] 0) (cusp (4*r)) := by
  apply tendsto_comap_iff.mpr
  apply Tendsto.congr' _ (tendsto_inv_nhdsGT_zero |>.const_mul_atTop (by norm_num : (0:ℝ)<1/4))
  filter_upwards [self_mem_nhdsWithin] with t ht
  change (1/4)*t⁻¹ = height (4*r) (path r t)
  rw [height,path_im,show path r t-(↑(4*r):ℂ) = 4*I*t by simp [path,mul_add,mul_assoc]]
  simp only [map_mul,normSq_I,normSq_ofReal]
  norm_num [normSq_apply]
  have ht' : 0<t := ht
  field_simp <;> norm_num

lemma tendsto_path_top (r : ℝ) :
    Tendsto (fun t : ℝ => path r t) atTop (comap Complex.im atTop) := by
  apply tendsto_comap_iff.mpr
  simpa only [Function.comp_def,path_im,id_eq] using
    (tendsto_id (α:=ℝ) (x:=atTop)).const_mul_atTop (by norm_num : (0:ℝ)<4)

lemma path_deriv (r : ℝ) (z : ℂ) : HasDerivAt (path r) (4*I) z := by
  unfold path
  simpa using (((hasDerivAt_id z).const_mul I).const_add (r:ℂ)).const_mul 4

theorem symbol_eq_boundary {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (hw : Γ.strictWidthInfty=1) (F : CuspForm Γ 2)
    (hF : ∀ z : ℍ, F z = h (4*(z:ℂ))) (r : ℚ) {J : ℂ → ℂ} {A : ℂ}
    (hJ : ∀ z, 0<z.im → HasDerivAt J (c*h z) z)
    (h0 : Tendsto J (comap Complex.im atTop) (𝓝 0))
    (hb : Tendsto J (cusp (4*(r:ℝ))) (𝓝 A)) : periodSymbol F r = A := by
  let f (t : ℝ) := F ((r:ℝ) +ᵥ ofComplex (I*t))
  let g (t : ℝ) := if t=0 then A else J (path r t)
  have hfall (t : ℝ) (ht : 0<t) : f t = h (path r t) := by
    unfold f
    rw [hF,coe_vadd,ofComplex_apply_of_im_pos (by simpa using ht)]
    rfl
  have hder (t : ℝ) (ht : 0<t) : HasDerivAt g (-(2*(Real.pi:ℂ))*f t) t := by
    have hd := (hJ (path r t) (by rw [path_im]; positivity)).comp (t:ℂ) (path_deriv r t) |>.comp_ofReal
    have hh : c*h (path r t)*(4*I) = -(2*(Real.pi:ℂ))*f t := by
      rw [hfall t ht,c]
      linear_combination (2*(Real.pi:ℂ)*h (path r t))*I_sq
    rw [hh] at hd
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds ht.ne'] with u hu
    simp [g,hu,Function.comp_def]
  have hg : ContinuousWithinAt g (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    change Tendsto g _ (𝓝 (g 0))
    simp only [g,if_pos rfl]
    apply (hb.comp (tendsto_path_bottom r)).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [ne_of_gt (show 0<t from ht)]
  have hg' : Tendsto g atTop (𝓝 0) := by
    apply (h0.comp (tendsto_path_top r)).congr'
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [g,ht.ne',Function.comp_def]
  have hi : IntegrableOn f (Ioi 0) := integrable_translate hw F r
  have e := integral_Ioi_of_hasDerivAt_of_tendsto hg hder (hi.const_mul (-(2*(Real.pi:ℂ)))) hg'
  rw [integral_const_mul,show g 0 = A by simp [g],zero_sub] at e
  change 2*(Real.pi:ℂ)*(∫ t in Ioi (0:ℝ), f t) = A
  linear_combination -e

theorem paired_symbols {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (hw : Γ.strictWidthInfty=1) (F : CuspForm Γ 2)
    (hF : ∀ z : ℍ, F z = h (4*(z:ℂ))) (r : ℚ) :
    ∃ m : ℤ, periodSymbol F r + periodSymbol F (-(r:ℝ)) = m*periodSymbol F 0 := by
  obtain ⟨J,hJ,h0,hT,C,hW⟩ := primitive
  obtain ⟨a,ha,hb⟩ := paired_cusp_values h0 hT hW (4*r)
  obtain ⟨hz,_,_,_⟩ := cusp_rules h0 hT hW
  have e₀ := symbol_eq_boundary hw F hF 0 hJ h0 (A:=C) (by simpa [Bound] using hz)
  have e₁ := symbol_eq_boundary hw F hF r hJ h0 (A:=(a:ℂ)*C) (by simpa [Bound] using ha)
  have e₂ := symbol_eq_boundary hw F hF (-r) hJ h0 (A:=(star a:ℂ)*C) (by simpa [Bound] using hb)
  simp only [Rat.cast_neg,Rat.cast_zero] at e₂ e₀
  refine ⟨2*a.re,?_⟩
  rw [e₀,e₁,e₂,← add_mul]
  congr 1
  simp [GaussianInt.toComplex_def]
  ring

end TunnellFricke

end

section

/- Algebraicity of every normalized positive even twist relative to one explicit eta integral. -/

namespace TunnellFricke

open MeasureTheory Set TunnellCMLSeries TunnellGaussian TunnellModularSymbol Finset
open UpperHalfPlane hiding I

noncomputable def baseConstant : ℂ :=
  (2*Real.pi:ℂ) * ∫ t in Ioi (0:ℝ), h (4*(Complex.I*t))

lemma zero_symbol {Γ : Subgroup (GL (Fin 2) ℝ)} (F : CuspForm Γ 2)
    (hF : ∀ z : ℍ, F z = h (4*(z:ℂ))) : periodSymbol F 0 = baseConstant := by
  unfold periodSymbol baseConstant
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [zero_vadd,hF,ofComplex_apply_of_im_pos (by simpa using ht : 0<(Complex.I*(t:ℂ)).im)]

theorem normalized_twists (n : ℕ) (hn : n%8=2) (hs : Squarefree n) (L : ℂ → ℂ)
    (he : AnalyticOnNhd ℂ L univ) (hprod : ∀ s : ℝ, 2<s →
      HasProd (fun p : Nat.Primes => if p.val ∣ 2*n then (1:ℂ) else
        let T := (p.val:ℂ)^(-(s:ℂ))
        (1-(curveTrace n p:ℂ)*T+(p.val:ℂ)*T^2)⁻¹) (L s)) :
    ∃ c : ℚ, (Real.sqrt n:ℂ)*L 1 = c*baseConstant := by
  obtain ⟨H,hH,hw,F,hF,hfc⟩ := TunnellEtaValue.actual_form
  letI : H.IsArithmetic := hH
  have hper (r : ℚ) : ∃ c : ℚ, periodSymbol F (r:ℝ)+periodSymbol F (-(r:ℝ)) = c*baseConstant := by
    obtain ⟨m,hm⟩ := paired_symbols hw F hF r
    exact ⟨m,by simpa only [Rat.cast_intCast,zero_symbol F hF] using hm⟩
  obtain ⟨K,hK,kw,G,r,ht,hr⟩ := rational_period_of_paired_symbols hn hs hw F baseConstant hper
  letI : K.IsArithmetic := hK
  let M := ModularForm.L (by decide : (0:ℤ)<2) G
  have a (m : ℕ) : (qExpansion 1 G).coeff m = gaussCoeff n m := by
    rw [ht,hfc,TunnellArithmetic.eta_eq_mass
      (TunnellTruncated.cubic_congruence (fun N => TunnellCubicFinite.cubic (Polynomial.X^8) N))
      (TunnellTruncated.theta_congruence (fun d N =>
        TunnellBalanced.balanced (TunnellTruncated.trunc d (Polynomial.X^4)) N))]
    rfl
  have hM : AnalyticOnNhd ℂ M univ := fun z _ =>
    (CuspForm.differentiable_L (by decide : (0:ℤ)<2) G).analyticAt z
  have eqM := TunnellMellin.entire_unique he hM 2 (fun s hgt => by
    have hl := (hprod s hgt).unique (lattice_euler n s (by linarith))
    have hsum : HasSum (fun m : ℕ => gaussCoeff n m / (m:ℂ)^(s:ℂ)) (M s) := by
      have h := CuspForm.hasSum_L (by decide : (0:ℤ)<2) G (s:=(s:ℂ)) (by norm_num; linarith)
      simpa only [kw,Complex.ofReal_one,Complex.one_cpow,one_mul,a,M] using h
    exact hl.trans ((shell_expansion n s (by linarith)).unique hsum))
  exact ⟨r,eqM ▸ hr⟩

end TunnellFricke

end

section

/- Eta quotients for the Fermat-quartic modular parameter. -/

namespace TunnellLambda
open Complex hiding eta
open ModularForm EisensteinSeries Set Function Filter
open UpperHalfPlane hiding I
open scoped Topology Real ComplexOrder

lemma qParam_imag (h t : ℝ) : Periodic.qParam h (I*t) = (Real.exp (-2*Real.pi*t/h):ℝ) := by
  rw [Periodic.qParam,ofReal_exp]
  congr 1
  push_cast
  linear_combination (2*(Real.pi:ℂ)*t/h)*I_sq

noncomputable def etaR (t : ℝ) : ℝ := Real.exp (-2*Real.pi*t/24)*∏' n : ℕ, (1-Real.exp (-2*Real.pi*t)^(n+1))

lemma eta_imag (t : ℝ) : eta (I*t) = (etaR t:ℂ) := by
  have hh := (RCLike.isUniformEmbedding_ofReal (𝕜:=ℂ)).isClosedEmbedding.map_tprod
    (L:=SummationFilter.unconditional ℕ) (g:=Complex.ofRealHom.toMonoidHom) (fun n : ℕ => 1-Real.exp (-2*Real.pi*t)^(n+1))
  unfold eta etaR eta_q
  rw [qParam_imag,qParam_imag,ofReal_mul]
  simp only [RingHom.toMonoidHom_eq_coe,MonoidHom.coe_coe,ofRealHom_eq_coe] at hh
  simp only [ofReal_sub,ofReal_one,ofReal_pow] at hh
  simpa only [div_one] using congrArg (fun w : ℂ => (Real.exp (-2*Real.pi*t/24):ℂ)*w) hh.symm

lemma etaR_pos {t : ℝ} (ht : 0<t) : 0<etaR t := by
  have hq : Real.exp (-2*Real.pi*t)<1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos Real.pi_pos ht])
  have h0 : 0 ≤ etaR t := mul_nonneg (Real.exp_pos _).le (tprod_nonneg (fun n =>
    sub_nonneg.mpr (pow_le_one₀ (Real.exp_pos _).le hq.le)))
  apply lt_of_le_of_ne h0
  intro h
  have hn : eta (I*t) ≠ 0 := eta_ne_zero (show I*t∈upperHalfPlaneSet by change 0<(I*t).im; simpa [mul_im])
  exact hn (by rw [eta_imag,←h,ofReal_zero])

end TunnellLambda

end

section

/- Reality and positivity of the eta differential on the imaginary axis. -/

namespace TunnellFricke

open Complex hiding eta
open ModularForm Function MeasureTheory Set Filter
open scoped Topology

lemma eta_imag {t : ℝ} (ht : 0<t) : ∃ x : ℝ, 0<x ∧ eta (I*t) = x :=
  ⟨TunnellLambda.etaR t,TunnellLambda.etaR_pos ht,TunnellLambda.eta_imag t⟩

noncomputable def imaginaryValue (t : ℝ) := (h (4*(I*t))).re

lemma imaginary_cast {t : ℝ} (ht : 0<t) :
    0 < imaginaryValue t ∧ h (4*(I*t)) = (imaginaryValue t:ℂ) := by
  obtain ⟨a,ha,he⟩ := eta_imag (show 0<4*t by positivity)
  obtain ⟨b,hb,hf⟩ := eta_imag (show 0<8*t by positivity)
  have v : h (4*(I*t)) = ((a^2*b^2:ℝ):ℂ) := by
    rw [h,show 4*(I*(t:ℂ)) = I*((4*t:ℝ):ℂ) by push_cast; ring,
      show 2*(I*(((4*t:ℝ):ℂ))) = I*((8*t:ℝ):ℂ) by push_cast; ring,he,hf]
    push_cast
    rfl
  simp only [imaginaryValue,v,ofReal_re]
  exact ⟨by positivity,trivial⟩

lemma baseConstant_real : baseConstant = ((2*Real.pi*(∫ t in Ioi (0:ℝ), imaginaryValue t):ℝ):ℂ) := by
  unfold baseConstant
  push_cast
  rw [← integral_complex_ofReal]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  exact fun t ht => (imaginary_cast ht).2

end TunnellFricke

end

section

/- Coefficients of the three local theta test functions in the even twist family. -/

namespace TunnellLocalFourier

open OMA.R_CongruentNumber_Tunnell_even_R1_H3_R1.TunnellCentralSeries

open Finset Filter Polynomial
open scoped Topology PowerSeries.WithPiTopology

lemma theta_locally_uniform (t : ℕ) (ht : 0<t) :
    TendstoLocallyUniformlyOn
      (fun (D : ℕ) (q : ℂ) => ∑ k ∈ range D, q^(t*(k+1)^2))
      (fun q => ∑' k : ℕ, q^(t*(k+1)^2)) atTop (Metric.ball 0 1) := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball]
  intro K hK hcK
  rcases K.eq_empty_or_nonempty with rfl | hN
  · exact tendstoUniformlyOn_empty
  obtain ⟨q₀, hq₀, _, hb⟩ := hcK.exists_sSup_image_eq_and_ge hN
    (show ContinuousOn (fun q : ℂ ↦ ‖q‖) K by fun_prop)
  have hlt : ‖q₀‖ < 1 := by simpa using hK hq₀
  apply tendstoUniformlyOn_tsum_nat (summable_geometric_of_lt_one (norm_nonneg q₀) hlt)
  intro k q hq
  rw [norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _) (hb q hq) _).trans
    (pow_le_pow_of_le_one (norm_nonneg _) hlt.le (by nlinarith [Nat.zero_le (k*k), Nat.mul_le_mul_right ((k+1)^2) (show 1 ≤ t by omega)]))

lemma eval_partial (t : ℕ) (D : ℕ) (q : ℂ) :
    ((X * ∏ k ∈ Icc 1 D, ((1-(X : ℂ[X])^(8*k))*(1-X^(16*k)))) *
      (1+2*∑ k ∈ Icc 1 D, X^(t*k^2))).eval q =
        q * (∏ k ∈ range D, (1-(q^8)^(k+1))) *
          (∏ k ∈ range D, (1-(q^16)^(k+1))) * (1+2*∑ k ∈ range D, q^(t*(k+1)^2)) := by
  have hI : Icc 1 D = Ico 1 (D+1) := by ext k; simp
  rw [hI, prod_mul_distrib, prod_Ico_eq_prod_range, prod_Ico_eq_prod_range, sum_Ico_eq_sum_range]
  simp [eval_finsetSum, eval_prod, ← pow_mul, add_comm 1, mul_assoc]

lemma product_locally_uniform (t : ℕ) (ht : 0<t) :
    TendstoLocallyUniformlyOn
      (fun (D : ℕ) (q : ℂ) => ((X * ∏ k ∈ Icc 1 D, ((1-(X : ℂ[X])^(8*k))*(1-X^(16*k)))) *
        (1+2*∑ k ∈ Icc 1 D, X^(t*k^2))).eval q)
      (fun q => q * (∏' k : ℕ, (1-(q^8)^(k+1))) *
        (∏' k : ℕ, (1-(q^16)^(k+1))) * (1+2*∑' k : ℕ, q^(t*(k+1)^2)))
      atTop (Metric.ball 0 1) := by
  let U := Metric.ball (0 : ℂ) 1
  let E (a : ℕ) (q : ℂ) : ℂ := ∏' k : ℕ, (1 - (q^a)^(k+1))
  let P (a D : ℕ) (q : ℂ) : ℂ := ∏ k ∈ range D, (1 - (q^a)^(k+1))
  have maps (a : ℕ) (ha : 0 < a) : Set.MapsTo (fun q : ℂ => q^a) U U := by
    intro q hq
    simp only [U, Metric.mem_ball, dist_zero_right, norm_pow] at hq ⊢
    exact pow_lt_one₀ (norm_nonneg _) hq ha.ne'
  have h (a : ℕ) (ha : 0 < a) : TendstoLocallyUniformlyOn (P a) (E a) atTop U := by
    exact (ModularForm.multipliableLocallyUniformlyOn_one_sub_pow.comp _ (maps a ha)
      (by fun_prop)).hasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
  have hc (a : ℕ) (ha : 0 < a) : ContinuousOn (E a) U :=
    ModularForm.differentiableOn_tprod_one_sub_pow.continuousOn.comp (by fun_prop) (maps a ha)
  have cst (g : ℂ → ℂ) : TendstoLocallyUniformlyOn (fun _ : ℕ => g) g atTop U := by
    intro u hu x _
    exact ⟨Set.univ, univ_mem, .of_forall fun _ y _ => refl_mem_uniformity hu⟩
  have he := ((cst id).mul₀ (h 8 (by decide)) continuousOn_id (hc 8 (by decide))).mul₀
    (h 16 (by decide)) (continuousOn_id.mul (hc 8 (by decide))) (hc 16 (by decide))
  have hec := (continuousOn_id.mul (hc 8 (by decide))).mul (hc 16 (by decide))
  have htc := (theta_locally_uniform t ht).continuousOn (.of_forall (fun _ => by fun_prop))
  have hts := (cst (fun _ => (2:ℂ))).mul₀ (theta_locally_uniform t ht) continuousOn_const htc
  have hth := (cst (fun _ => (1:ℂ))).add hts
  simp_rw [eval_partial]
  exact he.mul₀ hth hec (continuousOn_const.add (continuousOn_const.mul htc))


open OMA.R_CongruentNumber_Tunnell_even_R1.FourierSeries
open PowerSeries

theorem finite_coeff_of_le (t : ℕ) (ht : 0<t) (d m : ℕ) (hm : m ≤ d) :
    let X : Polynomial ℤ := Polynomial.X
    let eta := X * ∏ k ∈ Icc 1 d, ((1 - X ^ (8 * k)) * (1 - X ^ (16 * k)))
    let theta := 1 + 2 * ∑ k ∈ Icc 1 d, X ^ (t * k ^ 2)
    (eta * theta).coeff m =
      PowerSeries.coeff m ((PowerSeries.X : ℤ⟦X⟧) *
        (∏' k : ℕ, (1 - PowerSeries.X ^ (8 * (k + 1)))) *
        (∏' k : ℕ, (1 - PowerSeries.X ^ (16 * (k + 1)))) *
        (1 + 2 * ∑' k : ℕ, PowerSeries.X ^ (t * (k + 1) ^ 2))) := by
  dsimp only
  have hI : Icc 1 d = Ico 1 (d + 1) := by ext k; simp
  rw [hI, Finset.prod_mul_distrib, Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range,
    Finset.sum_Ico_eq_sum_range, ← mul_assoc, ← Polynomial.coeff_coe]
  rw [← Polynomial.coeToPowerSeries.ringHom_apply]
  simp only [map_mul, map_prod, map_sub, map_one, map_pow, map_add, map_sum, map_ofNat,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, Nat.add_one_sub_one, add_comm 1]
  apply mul_coeff_congr _ _ m hm
  · apply mul_coeff_congr
    · apply mul_coeff_congr
      · exact fun _ _ => rfl
      · exact fun m hm => coeff_tprod_high (fun k => 8 * (k+1)) (by intro k; omega) hm
    · exact fun m hm => coeff_tprod_high (fun k => 16 * (k+1)) (by intro k; omega) hm
  · intro m hm
    rw [map_add, map_add]
    congr 1
    apply mul_coeff_congr (fun _ _ => rfl) _ m hm
    exact fun k hk => coeff_tsum_high (fun j => t * (j+1)^2)
      (by intro j; nlinarith [Nat.zero_le (j*j), Nat.mul_le_mul_right ((j+1)^2) (show 1 ≤ t by omega)]) hk

theorem analytic_theta_coefficient (t : ℕ) (ht : 0<t) (m : ℕ) :
    (m.factorial : ℂ)⁻¹ * iteratedDeriv m
      (fun q : ℂ => q * (∏' k : ℕ, (1-(q^8)^(k+1))) *
        (∏' k : ℕ, (1-(q^16)^(k+1))) * (1+2*∑' k : ℕ, q^(t*(k+1)^2))) 0 =
      (PowerSeries.coeff m ((PowerSeries.X : ℤ⟦X⟧) *
        (∏' k : ℕ, (1 - PowerSeries.X ^ (8 * (k + 1)))) *
        (∏' k : ℕ, (1 - PowerSeries.X ^ (16 * (k + 1)))) *
        (1 + 2 * ∑' k : ℕ, PowerSeries.X ^ (t * (k + 1) ^ 2))) : ℤ) := by
  let P (D : ℕ) : ℤ[X] := (Polynomial.X * ∏ k ∈ Icc 1 D,
      ((1-Polynomial.X^(8*k))*(1-Polynomial.X^(16*k)))) *
        (1+2*∑ k ∈ Icc 1 D, Polynomial.X^(t*k^2))
  apply taylor_of_convergent_polynomials (fun D => (P D).map (Int.castRingHom ℂ))
  · simpa only [P, Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_add,
      Polynomial.map_sum, Polynomial.map_ofNat] using product_locally_uniform t ht
  · intro D hD
    rw [Polynomial.coeff_map]
    exact congrArg (fun z : ℤ => (z : ℂ)) (finite_coeff_of_le t ht D m hD)

open UpperHalfPlane Function ModularForm

lemma upper_value (t : ℕ) (ht : 0<t) (z : ℍ) :
    let q := Periodic.qParam 1 (z:ℂ)
    ModularForm.eta (8*(z:ℂ)) * ModularForm.eta (16*(z:ℂ)) * jacobiTheta ((2*t:ℂ)*(z:ℂ)) =
      q * (∏' k : ℕ, (1-(q^8)^(k+1))) *
        (∏' k : ℕ, (1-(q^16)^(k+1))) * (1+2*∑' k : ℕ, q^(t*(k+1)^2)) := by
  dsimp only
  have hlead : Periodic.qParam 24 (8*(z:ℂ)) * Periodic.qParam 24 (16*(z:ℂ)) =
      Periodic.qParam 1 z := by
    simp only [Periodic.qParam, ← Complex.exp_add]
    push_cast
    congr 1
    ring
  have htheta : jacobiTheta ((2*t:ℂ)*(z:ℂ)) = 1 + 2 * ∑' k : ℕ, (Periodic.qParam 1 (z:ℂ))^(t*(k+1)^2) := by
    have him : 0 < ((2*t:ℂ)*(z:ℂ)).im := by simp [Complex.mul_im]; positivity [z.im_pos]
    rw [jacobiTheta_eq_tsum_nat him]
    congr 2
    apply tsum_congr
    intro k
    simp only [Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_nat_mul]
    push_cast
    congr 1
    ring
  rw [htheta]
  congr 1
  unfold ModularForm.eta eta_q
  rw [show (8:ℂ) = (8:ℕ) by norm_num, qparam_dilate,
    show (16:ℂ) = (16:ℕ) by norm_num, qparam_dilate]
  linear_combination (∏' k : ℕ, (1-(Periodic.qParam 1 z ^ 8)^(k+1))) *
    (∏' k : ℕ, (1-(Periodic.qParam 1 z ^ 16)^(k+1))) * hlead

theorem qExpansion_local (t : ℕ) (ht : 0<t) (m : ℕ) :
    (qExpansion 1 (fun z : ℍ => ModularForm.eta (8*(z:ℂ)) * ModularForm.eta (16*(z:ℂ)) * jacobiTheta ((2*t:ℂ)*(z:ℂ)))).coeff m =
      (((Polynomial.X * ∏ k ∈ Icc 1 m, ((1-(Polynomial.X : ℤ[X])^(8*k))*(1-Polynomial.X^(16*k)))) *
        (1+2*∑ k ∈ Icc 1 m, Polynomial.X^(t*k^2))).coeff m : ℤ) := by
  have hc := (product_locally_uniform t ht).continuousOn (.of_forall fun D => by fun_prop)
  have hd := cuspFunction_of_disk (hc.continuousAt (Metric.ball_mem_nhds (0:ℂ) one_pos)) (upper_value t ht)
  rw [qExpansion_coeff,hd.iteratedDeriv_eq,analytic_theta_coefficient t ht m]
  exact_mod_cast (finite_coeff_of_le t ht m m le_rfl).symm

end TunnellLocalFourier

end

section

/- The restrictions of Tunnell's three theta test functions to odd indices. -/

namespace TunnellLocalFourier
open Polynomial Finset UpperHalfPlane

noncomputable def core (m : ℕ) : ℤ[X] := X * ∏ k ∈ Icc 1 m, ((1-X^(8*k))*(1-X^(16*k)))
noncomputable def term (t m k : ℕ) : ℤ := (core m * X^(t*k^2)).coeff m
noncomputable def repr (t m : ℕ) : ℤ := (core m * (1+2*∑ k ∈ Icc 1 m, X^(t*k^2))).coeff m

noncomputable def b (t m : ℕ) : ℂ := (qExpansion 1 (fun z : UpperHalfPlane =>
    ModularForm.eta (8*(z:ℂ))*ModularForm.eta (16*(z:ℂ))*jacobiTheta ((2*t:ℂ)*(z:ℂ)))).coeff m

lemma b_eq (t : ℕ) (ht : 0<t) (m : ℕ) : b t m=(repr t m:ℂ) := qExpansion_local t ht m

lemma core_zero {m n : ℕ} (hn : n%8≠1) : (core m).coeff n=0 := by
  let Q : ℤ[X] := ∏ k ∈ Icc 1 m, ((1-X^k)*(1-X^(2*k)))
  have h : expand ℤ 8 Q = ∏ k ∈ Icc 1 m, ((1-X^(8*k))*(1-X^(16*k))) := by
    simp [Q,expand_X,←pow_mul,←Nat.mul_assoc]
  unfold core
  rw [←h]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_X_mul,coeff_expand (by decide : 0<8)]
    exact if_neg (by omega)

lemma expansion (t m : ℕ) : repr t m=(core m).coeff m + 2*∑ k ∈ Icc 1 m,term t m k := by
  simp [repr,term,mul_add,mul_one,show ∀ a b : ℤ[X], a*(2*b)=2*(a*b) by intros; ring,
    mul_sum,coeff_sum, two_mul,add_mul,coeff_add]

lemma term_zero_of_large {t m k : ℕ} (h : m<t*k^2) : term t m k=0 := by
  simp [term,coeff_mul_X_pow',if_neg (by omega : ¬ t*k^2 ≤ m)]

lemma term_zero_of_residue {t m k : ℕ} (h : m%8≠(1+t*k^2)%8) : term t m k=0 := by
  unfold term
  rw [coeff_mul_X_pow']
  split_ifs with hk
  · apply core_zero
    omega
  · rfl

def inds (t m : ℕ) : Finset ℕ := (Icc 1 m).filter (fun k => t*k^2 ≤ m)

lemma expansion' (t m : ℕ) : repr t m=(core m).coeff m + 2*∑ k ∈ inds t m,term t m k := by
  rw [expansion,inds,sum_filter]
  congr 2
  apply sum_congr rfl
  intro k hk
  split_ifs with h
  · rfl
  · exact term_zero_of_large (by omega)

lemma dissection (t m : ℕ) (ht : 0<t) (odd_off : ∀ k, Odd k → m%8≠(1+t*k^2)%8) :
    repr t m=repr (4*t) m := by
  rw [expansion',expansion']
  congr 2
  calc
    _ = ∑ k ∈ (inds t m).filter Even, term t m k := by
      rw [sum_filter]
      apply sum_congr rfl
      intro k _
      split_ifs with he
      · rfl
      · exact term_zero_of_residue (odd_off k (Nat.not_even_iff_odd.mp he))
    _ = _ := by
      apply sum_nbij' (fun k:ℕ => k/2) (fun j:ℕ => 2*j)
      · intro k hk
        rcases mem_filter.mp hk with ⟨h,⟨j,hj⟩⟩
        obtain ⟨hi,hk⟩ := mem_filter.mp h
        obtain ⟨hpos,hmax⟩ := mem_Icc.mp hi
        have he : 4*t*(k/2)^2=t*k^2 := by rw [show k=2*j by omega,Nat.mul_div_cancel_left _ (by decide : 0<2)]; ring
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,he ▸ hk⟩
      · intro j hj
        obtain ⟨hi,hj⟩ := mem_filter.mp hj
        have h : 2*j ≤ t*(2*j)^2 := by
          have hs := Nat.le_mul_self (2*j)
          have hT := Nat.mul_le_mul_right ((2*j)^2) (show 1≤t by omega)
          nlinarith
        have hd : t*(2*j)^2=4*t*j^2 := by ring
        rw [hd] at h
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by have := (mem_Icc.mp hi).1; omega,by omega⟩,hd ▸ hj⟩,even_two_mul _⟩
      · intro k hk
        obtain ⟨j,hj⟩ := (mem_filter.mp hk).2
        omega
      · intro j _; omega
      · intro k hk
        obtain ⟨j,hj⟩ := (mem_filter.mp hk).2
        have he : t*k^2=4*t*(k/2)^2 := by rw [show k=2*j by omega,Nat.mul_div_cancel_left _ (by decide : 0<2)]; ring
        simp only [term,he]

lemma one_eq_four {d : ℕ} (hd : Odd d) : b 1 d=b 4 d := by
  rw [b_eq 1 (by decide),b_eq 4 (by decide)]
  apply congrArg (fun n:ℤ => (n:ℂ))
  apply dissection 1 d (by decide)
  intro k hk
  have hodd := Nat.odd_iff.mp (hk.pow (n:=2))
  have hd' := Nat.odd_iff.mp hd
  simp only [one_mul]
  omega

lemma four_eq_sixteen {d : ℕ} (hd : d%8=1) : b 4 d=b 16 d := by
  rw [b_eq 4 (by decide),b_eq 16 (by decide)]
  apply congrArg (fun n:ℤ => (n:ℂ))
  apply dissection 4 d (by decide)
  intro k hk
  have hh := Nat.odd_iff.mp (hk.pow (n:=2))
  omega

lemma sixteen_zero {d : ℕ} (hd : d%8≠1) : b 16 d=0 := by
  rw [b_eq 16 (by decide),expansion,core_zero hd,sum_eq_zero (fun k _ => term_zero_of_residue (by omega : d%8≠(1+16*k^2)%8))]
  norm_num

lemma four_zero {d : ℕ} (hd : d%4≠1) : b 4 d=0 := by
  rw [b_eq 4 (by decide),expansion,core_zero (by omega),sum_eq_zero (fun k _ => term_zero_of_residue (by omega : d%8≠(1+4*k^2)%8))]
  norm_num

end TunnellLocalFourier

end

section

/- # The ternary square shell for the weight-three-halves coefficients -/

namespace TunnellShell

open OMA.R_CongruentNumber_Tunnell_even_R1 CongruentNumber Finset
open scoped PowerSeries.WithPiTopology

abbrev Triple := ℤ × ℤ × ℤ

def normSq (v : Triple) : ℤ := v.1^2+v.2.1^2+v.2.2^2

def shell (N : ℕ) : Finset Triple :=
  let I := Finset.Icc (-(N:ℤ)-1) (N+1:ℤ)
  (I ×ˢ (I ×ˢ I)).filter (fun v => normSq v=N)

@[simp] lemma mem_shell {N : ℕ} {v : Triple} : v ∈ shell N ↔ normSq v=N := by
  obtain ⟨x,y,z⟩ := v
  simp only [shell,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc]
  refine ⟨And.right,fun h => ⟨?_,h⟩⟩
  change x^2+y^2+z^2=(N:ℤ) at h
  have hbound (a:ℤ) (ha:a^2≤N) : -(N:ℤ)-1 ≤ a ∧ a ≤ N+1 :=
    ⟨by nlinarith [sq_nonneg (a+1)],by nlinarith [sq_nonneg (a-1)]⟩
  exact ⟨hbound x (by nlinarith [sq_nonneg y,sq_nonneg z]), hbound y (by nlinarith [sq_nonneg x,sq_nonneg z]),
    hbound z (by nlinarith [sq_nonneg x,sq_nonneg y])⟩

def admissible (v : Triple) : Prop := Odd v.1 ∧ Odd v.2.1 ∧ v.2.2%4=0
instance (v : Triple) : Decidable (admissible v) := by unfold admissible; infer_instance

def coordWeight (v : Triple) : ℤ := if admissible v then ((v.2.2/4).negOnePow : ℤ) else 0

def rot (v : Triple) : Triple := (v.2.1,v.2.2,v.1)

def weight (v : Triple) : ℤ := coordWeight v + coordWeight (rot v) + coordWeight (rot (rot v))

lemma rotation_sum (N : ℕ) (f : Triple → ℤ) :
    ∑ v ∈ shell N, f (rot v) = ∑ v ∈ shell N, f v := by
  apply sum_nbij' rot (fun v => rot (rot v))
  · rintro ⟨x,y,z⟩ h
    simp only [mem_shell,normSq,rot] at h ⊢
    linarith
  · rintro ⟨x,y,z⟩ h
    simp only [mem_shell,normSq,rot] at h ⊢
    linarith
  all_goals intro v _; rfl

lemma sum_weight (N : ℕ) : ∑ v ∈ shell N, weight v = 3*∑ v ∈ shell N, coordWeight v := by
  change ∑ v ∈ _, (coordWeight v+coordWeight (rot v)+coordWeight (rot (rot v))) = _
  simp only [sum_add_distrib]
  rw [rotation_sum N (fun v => coordWeight (rot v)),rotation_sum N coordWeight]
  ring

def slice (N : ℕ) (P : ℤ → Prop) : Set Triple :=
  {v | (v ∈ shell N ∧ admissible v) ∧ P (v.2.2/4)}

lemma sum_coordWeight (N : ℕ) : ∑ v ∈ shell N, coordWeight v =
    (slice N Even).ncard - ((slice N Odd).ncard : ℤ) := by
  calc
    _ = ∑ v ∈ shell N, if v∈shell N ∧ admissible v then ((v.2.2 / 4).negOnePow : ℤ) else 0 := by
      apply sum_congr rfl; intro v hv; simp [coordWeight,hv]
    _ = _ := sum_sign_eq_ncard (shell N) _ _ (fun _ h => h.1)

lemma slice_card {m : ℕ} (hm : m%4=1) (P : ℤ → Prop) :
    (slice (2*m) P).ncard = 2* {v ∈ D (2*m) | P v.2.2}.ncard := by
  let S := slice (2*m) P
  let good := {v ∈ S | v.1%4 = v.2.1%4}
  let bad := {v ∈ S | v.1%4 ≠ v.2.1%4}
  have hf : S.Finite := (shell (2*m)).finite_toSet.subset (fun _ h => h.1.1)
  have hsplit : S = good ∪ bad := by ext v; simp [good,bad]; tauto
  have hdis : Disjoint good bad := Set.disjoint_left.mpr (fun _ hu hv => hv.2 hu.2)
  have hpair : bad.ncard = good.ncard := by
    apply Set.ncard_congr (fun v _ => (-v.1,v.2.1,v.2.2))
    · rintro ⟨x,y,z⟩ ⟨⟨⟨hs,hx,hy,hz⟩,hp⟩,hne⟩
      have hx' := Int.odd_iff.mp hx
      have hy' := Int.odd_iff.mp hy
      exact ⟨⟨⟨by simpa [normSq] using hs,by simpa using hx,hy,hz⟩,hp⟩,by dsimp at hne hx' hy' ⊢; omega⟩
    · rintro ⟨x,y,z⟩ ⟨x',y',z'⟩ _ _ h; simpa using h
    · rintro ⟨x,y,z⟩ ⟨⟨⟨hs,hx,hy,hz⟩,hp⟩,he⟩
      have hx' := Int.odd_iff.mp hx
      exact ⟨(-x,y,z),⟨⟨⟨by simpa [normSq] using hs,by simpa using hx,hy,hz⟩,hp⟩,by dsimp at he hx' ⊢; omega⟩,by simp⟩
  have count : {v ∈ D (2*m) | P v.2.2}.ncard = good.ncard := by
    apply Set.ncard_congr (fun v _ => (v.2.1+2*v.1,v.2.1-2*v.1,4*v.2.2))
    · rintro ⟨r,a,t⟩ ⟨hd,hp⟩
      have ha := y_residues (n:=2*m) (by omega) hd
      have ha' : Odd a := Int.odd_iff.mpr (by omega)
      change ((2*m:ℕ):ℤ)=8*r^2+2*a^2+16*t^2 at hd
      refine ⟨⟨⟨mem_shell.mpr ?_,Int.odd_iff.mpr (by change (a+2*r)%2=1; omega),Int.odd_iff.mpr (by change (a-2*r)%2=1; omega),by dsimp; omega⟩,?_⟩,by dsimp; omega⟩
      · dsimp [normSq]; push_cast at hd; linear_combination -hd
      · simpa using hp
    · rintro ⟨r,a,t⟩ ⟨r',a',t'⟩ h h' he
      simp only [Prod.mk.injEq] at he ⊢
      exact ⟨by omega,by omega,by omega⟩
    · rintro ⟨x,y,z⟩ ⟨⟨⟨hs,hx,hy,hz⟩,hp⟩,he⟩
      have hx' := Int.odd_iff.mp hx
      have hy' := Int.odd_iff.mp hy
      change x%4=y%4 at he
      change z%4=0 at hz
      let r := (x-y)/4
      let a := (x+y)/2
      let t := z/4
      have h1 : a+2*r=x := by dsimp [a,r]; omega
      have h2 : a-2*r=y := by dsimp [a,r]; omega
      have h3 : 4*t=z := by dsimp [t]; omega
      refine ⟨(r,a,t),⟨?_,hp⟩,by simp [h1,h2,h3]⟩
      have hs' := mem_shell.mp hs
      change x^2+y^2+z^2=((2*m:ℕ):ℤ) at hs'
      rw [← h1,← h2,← h3] at hs'
      change ((2*m:ℕ):ℤ)=8*r^2+2*a^2+16*t^2
      linear_combination -hs'
  change S.ncard = _
  rw [hsplit,Set.ncard_union_eq hdis (hf.subset (Set.sep_subset _ _)) (hf.subset (Set.sep_subset _ _)), hpair, ←count]
  omega

noncomputable def b (m : ℕ) : ℤ :=
  let X : PowerSeries ℤ := PowerSeries.X
  PowerSeries.coeff m (X * (∏' k : ℕ, (1-X^(8*(k+1)))) * (∏' k : ℕ, (1-X^(16*(k+1)))) *
    (1+2*∑' k : ℕ, X^(4*(k+1)^2)))

lemma b_zero {m : ℕ} (hm : m%4≠1) : b m=0 := by
  have empty (P : ℤ→Prop) :
      {t : Triple | 1 + 8*pentagonal t.1 + 16*pentagonal t.2.1 + 4*t.2.2.natAbs^2=m ∧
        P (t.1+t.2.1)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    have h := ht.1
    omega
  rw [b,← FourierSeries.finite_eq_infinite, coefficient_count,empty Even,empty Odd]
  simp

lemma odd_square_mod8 (x : ℤ) (hx : Odd x) : x^2%8=1 := by
  have h := Int.odd_iff.mp hx
  have h0 := Int.emod_nonneg x (by decide : (8:ℤ) ≠ 0)
  have h8 := Int.emod_lt_of_pos x (by decide : (0:ℤ) < 8)
  rw [sq,Int.mul_emod]
  interval_cases he : x%8 <;> omega

lemma admissible_residue {m : ℕ} {v : Triple} (hv : v∈shell (2*m)) (ha : admissible v) : m%4=1 := by
  rcases v with ⟨x,y,z⟩
  obtain ⟨hx,hy,hz⟩ := ha
  change z%4=0 at hz
  have h1 := odd_square_mod8 x hx
  have h2 := odd_square_mod8 y hy
  have hz' : z=4*(z/4) := by omega
  have h3 : z^2%8=0 := by
    rw [show z^2 = 8*(2*(z/4)^2) by nth_rw 1 [hz']; ring]
    simp
  have he := mem_shell.mp hv
  change x^2+y^2+z^2=((2*m:ℕ):ℤ) at he
  push_cast at he
  omega

theorem sum_weight_eq_twelve (m : ℕ) : (∑ v ∈ shell (2*m),weight v) = 12*b m := by
  rw [sum_weight]
  by_cases hm : m%4=1
  · rw [sum_coordWeight, slice_card hm Even, slice_card hm Odd]
    have hn : (2*m)%8=2 := by omega
    have hb := signed_theta_expansion (2*m) hn
    dsimp only at hb
    simp only [Nat.mul_div_cancel_left _ (by decide : 0<2)] at hb
    rw [FourierSeries.finite_eq_infinite] at hb
    change b m = _ at hb
    have hE := sign_pairing hn (finite_D (2*m)) Even
    have hO := sign_pairing hn (finite_D (2*m)) Odd
    omega
  · have hz : (∑ v ∈ shell (2*m), coordWeight v) = 0 := by
      apply sum_eq_zero
      intro v hv
      exact if_neg (fun ha => hm (admissible_residue hv ha))
    rw [hz,b_zero hm]
    ring

theorem sum_weight_eq_fourier (m : ℕ) :
    ((∑ v ∈ shell (2*m),weight v):ℂ) = 12*
      (UpperHalfPlane.qExpansion 1 (fun z : UpperHalfPlane =>
        ModularForm.eta (8*(z:ℂ))*ModularForm.eta (16*(z:ℂ))*jacobiTheta (8*(z:ℂ)))).coeff m := by
  rw [OMA.R_CongruentNumber_Tunnell_even_R1_H3_R1.TunnellCentralSeries.qExpansion_theta_coefficient]
  exact_mod_cast sum_weight_eq_twelve m


end TunnellShell

end

section

/- The two trace-zero quaternion lattices of the local test vector at 2.
The bases are those of Burungale and Tian, section 3.3.1. -/

namespace TunnellTestVector

open TunnellShell Finset
open scoped Classical

def first (v : Triple) : Triple := (v.1+2*v.2.1,v.1-2*v.2.1,8*v.2.2)
def second (v : Triple) : Triple := (2*v.1+2*v.2.1+v.2.2,-2*v.1+2*v.2.1+v.2.2,-4*v.2.2)

lemma first_iff (v : Triple) : v∈Set.range first ↔ v.1%4=v.2.1%4 ∧ v.2.2%8=0 := by
  obtain ⟨x,y,z⟩ := v
  constructor
  · rintro ⟨⟨a,b,c⟩,h⟩
    simp [first,Prod.ext_iff] at h
    dsimp only
    omega
  · rintro ⟨h,hz⟩
    dsimp only at h hz
    exact ⟨((x+y)/2,(x-y)/4,z/8),by apply Prod.ext <;> simp [first,Prod.ext_iff] <;> omega⟩

lemma second_iff (v : Triple) : v∈Set.range second ↔ v.1%4=v.2.1%4 ∧
    v.2.2%4=0 ∧ (v.1+v.2.1+2*(v.2.2/4))%4=0 := by
  obtain ⟨x,y,z⟩ := v
  constructor
  · rintro ⟨⟨a,b,c⟩,h⟩
    simp [second,Prod.ext_iff] at h
    dsimp only
    omega
  · rintro ⟨h,hz,hs⟩
    dsimp only at h hz hs
    exact ⟨((x-y)/4,(x+y+2*(z/4))/4,-(z/4)),by
      apply Prod.ext <;> simp [second,Prod.ext_iff] <;> omega⟩

def same (v : Triple) : Prop := v.1%4=v.2.1%4
def positive (v : Triple) : Prop := Odd v.1 ∧ Odd v.2.1 ∧ v.2.2%8=0
def negative (v : Triple) : Prop := Odd v.1 ∧ Odd v.2.1 ∧ v.2.2%8=4

lemma odd_coordinates {d : ℕ} (hd : Odd d) {v : Triple} (hv : v∈shell (2*d)) (hz : Even v.2.2) :
    Odd v.1 ∧ Odd v.2.1 := by
  have hn := mem_shell.mp hv
  change v.1^2+v.2.1^2+v.2.2^2=((2*d:ℕ):ℤ) at hn
  obtain ⟨k,hk⟩ := hd
  obtain ⟨c,hz⟩ := hz
  have hq := congrArg (fun a:ℤ => (a:ZMod 4)) hn
  push_cast at hq
  rw [hk,hz] at hq
  push_cast at hq
  have hc : ∀ x y z k : ZMod 4, x^2+y^2+(z+z)^2=2*(2*k+1) → x.val%2=1 ∧ y.val%2=1 := by decide
  obtain ⟨hx,hy⟩ := hc _ _ _ _ hq
  have hxv := ZMod.val_intCast (n:=4) v.1
  have hyv := ZMod.val_intCast (n:=4) v.2.1
  rw [Int.odd_iff,Int.odd_iff]
  omega

lemma on_shell {d : ℕ} (hd : Odd d) {v : Triple} (hv : v∈shell (2*d)) :
    (v∈Set.range first ↔ same v ∧ positive v) ∧ (v∈Set.range second ↔ same v ∧ negative v) := by
  rw [first_iff,second_iff]
  change (_ ↔ _ ∧ (Odd v.1 ∧ Odd v.2.1 ∧ _)) ∧ (_ ↔ _ ∧ (Odd v.1 ∧ Odd v.2.1 ∧ _))
  have ho (h : v.2.2%4=0) := odd_coordinates hd hv (Int.even_iff.mpr (by omega : v.2.2%2=0))
  constructor
  · exact ⟨fun ⟨h,hz⟩ => ⟨h,(ho (by omega)).1,(ho (by omega)).2,hz⟩,fun h => ⟨h.1,h.2.2.2⟩⟩
  · change (_ ↔ v.1%4=v.2.1%4 ∧ _)
    constructor
    · rintro ⟨h,hz,hs⟩
      obtain ⟨hx,hy⟩ := ho hz
      refine ⟨h,hx,hy,?_⟩
      have := Int.odd_iff.mp hx
      omega
    · rintro ⟨h,hx,hy,hz⟩
      have := Int.odd_iff.mp hx
      exact ⟨h,by omega,by omega⟩

def flip (v : Triple) : Triple := (v.1,-v.2.1,v.2.2)

lemma flip_shell {v : Triple} {n : ℕ} (hv : v∈shell n) : flip v∈shell n := by
  simpa [mem_shell,normSq,flip] using hv

lemma half_card (n : ℕ) (P : Triple → Prop) (hP : ∀ v, P (flip v) ↔ P v)
    (hod : ∀ v, P v → Odd v.1 ∧ Odd v.2.1) :
    ((shell n).filter P).card = 2*((shell n).filter (fun v => same v ∧ P v)).card := by
  let S := (shell n).filter P
  have hh : (S.filter (fun v => ¬same v)).card = (S.filter same).card := by
    apply card_nbij' flip flip
    · intro v h
      obtain ⟨hS,hs⟩ := mem_filter.mp h
      obtain ⟨hv,hp⟩ := mem_filter.mp hS
      obtain ⟨hx,hy⟩ := hod v hp
      simp only [Int.odd_iff] at hx hy
      change ¬v.1%4=v.2.1%4 at hs
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨flip_shell hv,(hP v).mpr hp⟩,
        by change v.1%4=(-v.2.1)%4; omega⟩
    · intro v h
      obtain ⟨hS,hs⟩ := mem_filter.mp h
      obtain ⟨hv,hp⟩ := mem_filter.mp hS
      obtain ⟨hx,hy⟩ := hod v hp
      simp only [Int.odd_iff] at hx hy
      change v.1%4=v.2.1%4 at hs
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨flip_shell hv,(hP v).mpr hp⟩,
        by change ¬v.1%4=(-v.2.1)%4; omega⟩
    all_goals intro v _; simp [flip]
  have he := card_filter_add_card_filter_not (s:=S) same
  rw [hh] at he
  simpa [S,filter_filter,and_comm,two_mul] using he.symm

lemma coordinate (v : Triple) : coordWeight v = (if positive v then 1 else 0) - (if negative v then 1 else 0) := by
  obtain ⟨x,y,z⟩ := v
  dsimp only [coordWeight,admissible,positive,negative]
  by_cases hx : Odd x <;> by_cases hy : Odd y <;> simp only [hx,hy,true_and,false_and,ite_false,sub_zero]
  split_ifs <;> first
    | rw [Int.negOnePow_even _ (Int.even_iff.mpr (by omega))]; rfl
    | rw [Int.negOnePow_odd _ (Int.odd_iff.mpr (by omega))]; rfl
    | omega

theorem signed_shell (d : ℕ) (hd : Odd d) :
    (((shell (2*d)).filter (fun v => v∈Set.range first)).card:ℤ) -
      ((shell (2*d)).filter (fun v => v∈Set.range second)).card = 2*b d := by
  let S := shell (2*d)
  have h1 : S.filter (fun v => v∈Set.range first) = S.filter (fun v => same v ∧ positive v) :=
    filter_congr (fun _ hv => (on_shell hd hv).1)
  have h2 : S.filter (fun v => v∈Set.range second) = S.filter (fun v => same v ∧ negative v) :=
    filter_congr (fun _ hv => (on_shell hd hv).2)
  have hf := half_card (2*d) positive (fun _ => by simp [positive,flip]) (fun _ h => ⟨h.1,h.2.1⟩)
  have hg := half_card (2*d) negative (fun _ => by simp [negative,flip]) (fun _ h => ⟨h.1,h.2.1⟩)
  have hc := sum_weight_eq_twelve d
  rw [sum_weight] at hc
  simp_rw [coordinate] at hc
  simp only [sum_sub_distrib,sum_boole] at hc
  change ((S.filter (fun v => v∈Set.range first)).card:ℤ)-_=_
  rw [h1,h2]
  dsimp only [S] at *
  rw [show ((shell (2*d)).filter (fun x => positive x)).card = _ from hf,
    show ((shell (2*d)).filter (fun x => negative x)).card = _ from hg] at hc
  push_cast at hc
  omega

/-- Conjugation by 1+2j acts on the pure lattice over ℤ₂. Its norm 5
is invertible there, so the integral adjoint computes the same lattice test. -/
lemma conjugate_second (v : Triple) :
    v∈Set.range second ↔ (-3*v.1-4*v.2.2,5*v.2.1,4*v.1-3*v.2.2)∈Set.range first := by
  rw [first_iff,second_iff]
  dsimp only
  omega


end TunnellTestVector

end

section

/- Reduction of the entire test-function span to one even-twist genus period. -/

namespace TunnellWaldspurgerLocal
open Finset TunnellLocalFourier

noncomputable def localPeriod (d : ℕ) : ℤ :=
  open scoped Classical in
  (((TunnellShell.shell (2*d)).filter (fun v=>v∈Set.range TunnellTestVector.first)).card:ℤ)-
    ((TunnellShell.shell (2*d)).filter (fun v=>v∈Set.range TunnellTestVector.second)).card

lemma period_fourier (d : ℕ) (hd : Odd d) : (localPeriod d:ℂ)=2*b 4 d := by
  have h := TunnellTestVector.signed_shell d hd
  change localPeriod d=_ at h
  rw [h]
  have hc := TunnellShell.sum_weight_eq_fourier d
  rw [←Int.cast_sum,TunnellShell.sum_weight_eq_twelve] at hc
  push_cast at hc ⊢
  unfold b
  norm_num only [Nat.cast_ofNat,show (2:ℂ)*4=8 by norm_num]
  linear_combination hc/6

end TunnellWaldspurgerLocal

end

section

/- The normalized conductor-32 cusp symbol by the nearest-integer Euclidean algorithm. -/

namespace TunnellCuspEuclid

open TunnellFricke

def iunit : GaussianInt := ⟨0,1⟩

def rot (k : ℤ) : GaussianInt :=
  if k%4=0 then 1 else if k%4=1 then iunit else if k%4=2 then -1 else -iunit

lemma rot_succ (k : ℤ) : rot (k+1)=iunit*rot k := by
  unfold rot
  split_ifs <;> first | decide | omega

lemma rot_pred (k : ℤ) : rot (k-1)=(-iunit)*rot k := by
  unfold rot
  split_ifs <;> first | decide | omega

def symbolAux : ℕ → ℤ → ℕ → GaussianInt
  | 0, _, _ => 1
  | fuel+1, a, d =>
    let r := a.bmod d
    rot (a.bdiv d) * (if r=0 then 1 else if 2*r=-(d:ℤ) then 1-iunit else
      1-symbolAux fuel (if 0≤r then -(d:ℤ) else (d:ℤ)) (2*r.natAbs))

def symbol (a : ℤ) (d : ℕ) := symbolAux d a d

lemma symbol_rules (B : ℚ → GaussianInt → Prop) (h0 : B 0 1)
    (hp : ∀ x a, B x a → B (x+1) (iunit*a)) (hm : ∀ x a, B x a → B (x-1) (-iunit*a))
    (hw : ∀ x, x≠0 → ∀ a, B x a → B (-1/(2*x)) (1-a)) (a : ℤ) (d : ℕ) (hd : 0<d) :
    B ((a:ℚ)/d) (symbol a d) := by
  have ht (x : ℚ) (b : GaussianInt) (hb : B x b) (k : ℤ) : B (x+k) (rot k*b) := by
    induction k using Int.induction_on with
    | zero => simpa [rot] using hb
    | succ i ih => simpa [rot_succ,Int.cast_add,add_assoc,mul_assoc] using hp _ _ ih
    | pred i ih =>
      rw [rot_pred]
      simpa [Int.cast_sub,sub_eq_add_neg,add_assoc,mul_assoc] using hm _ _ ih
  suffices all : ∀ (fuel d : ℕ) (a : ℤ), 0<d → d≤fuel → B ((a:ℚ)/d) (symbolAux fuel a d) from all d d a hd le_rfl
  intro fuel
  induction fuel with
  | zero => intro d a hd h; omega
  | succ n ih =>
    intro d a hd hdn
    let r := a.bmod d
    have hr := (Int.bmod_eq_iff (a:=a) hd).mp (rfl : a.bmod d=r)
    have hdq : (d:ℚ) ≠ 0 := by positivity
    have eqr : (a:ℚ)/d = (r:ℚ)/d + (a.bdiv d:ℚ) := by
      field_simp
      exact_mod_cast (Int.bmod_add_bdiv a d).symm
    rw [eqr]
    unfold symbolAux
    apply ht
    change B ((r:ℚ)/d) (if r=0 then 1 else if 2*r=-(d:ℤ) then 1-iunit else _)
    by_cases h0r : r=0
    · simpa [h0r] using h0
    rw [if_neg h0r]
    by_cases he : 2*r=-(d:ℤ)
    · rw [if_pos he]
      have e : (r:ℚ)/d = -1/2 := by
        have hh : 2*(r:ℚ) = -(d:ℚ) := by exact_mod_cast he
        field_simp
        linarith
      rw [e]
      simpa using hw 1 one_ne_zero _ (by simpa using hp _ _ h0)
    · rw [if_neg he]
      have hsmall : 2*r.natAbs<d := by omega
      have hpos : 0<2*r.natAbs := by omega
      have hrq : (r:ℚ)≠0 := by exact_mod_cast h0r
      split_ifs with hsign
      · have ee : (r.natAbs:ℚ)=r := by
          have e : (r.natAbs:ℤ)=r := by omega
          simpa only [Int.cast_natCast] using congrArg (fun a:ℤ => (a:ℚ)) e
        have hh := ih _ (-(d:ℤ)) hpos (by omega)
        rw [Nat.cast_mul,Nat.cast_two,ee,Int.cast_neg,Int.cast_natCast] at hh
        convert hw _ (div_ne_zero (neg_ne_zero.mpr hdq) (mul_ne_zero (by norm_num) hrq)) _ hh using 1 <;> field_simp <;> ring
      · have ee : (r.natAbs:ℚ) = -r := by
          have e : (r.natAbs:ℤ) = -r := by omega
          simpa only [Int.cast_natCast,Int.cast_neg] using congrArg (fun a:ℤ => (a:ℚ)) e
        have hh := ih _ (d:ℤ) hpos (by omega)
        rw [Nat.cast_mul,Nat.cast_two,ee,Int.cast_natCast] at hh
        convert hw _ (div_ne_zero hdq (mul_ne_zero (by norm_num) (neg_ne_zero.mpr hrq))) _ hh using 1 <;> field_simp <;> ring

open Complex Filter
open scoped Topology

theorem cusp_value {J : ℂ → ℂ} {C : ℂ}
    (h0 : Tendsto J (comap Complex.im atTop) (𝓝 0))
    (hT : ∀ z, 0<z.im → J (z+1) = I*J z)
    (hW : ∀ z, 0<z.im → J (W z) = C-J z) (a : ℤ) (d : ℕ) (hd : 0<d) :
    Bound J C ((a:ℚ)/d) (symbol a d) ∧ Bound J C (-((a:ℚ)/d)) (star (symbol a d)) := by
  obtain ⟨hz,hp,hm,hw⟩ := cusp_rules h0 hT hW
  have hi : star iunit = -iunit := rfl
  apply symbol_rules (fun x g => Bound J C x g ∧ Bound J C (-x) (star g)) _ _ _ _ a d hd
  · exact ⟨hz,by simpa using hz⟩
  · rintro x g ⟨hb,he⟩
    exact ⟨hp _ _ hb,by simpa only [neg_add_rev,neg_add,neg_one_mul,star_mul,hi,show gi=iunit from rfl,neg_neg,star_neg,mul_comm,add_comm,sub_eq_add_neg] using hm (-x) (star g) he⟩
  · rintro x g ⟨hb,he⟩
    exact ⟨hm _ _ hb,by simpa only [neg_add_rev,neg_add,neg_one_mul,star_mul,hi,show gi=iunit from rfl,neg_neg,star_neg,mul_comm,add_comm,sub_eq_add_neg] using hp (-x) (star g) he⟩
  · rintro x hx g ⟨hb,he⟩
    exact ⟨hw _ hx _ hb,by simpa [div_eq_mul_inv] using hw (-x) (neg_ne_zero.mpr hx) _ he⟩

end TunnellCuspEuclid

end

section

/- Finite, explicitly computable normalized rational-cusp evaluations of the quadratic twists. -/

namespace TunnellFiniteSymbols
open TunnellFricke TunnellCuspEuclid TunnellTwistCharacter TunnellModularSymbol
open TunnellCMLSeries UpperHalfPlane Finset
open Set Filter
open scoped Topology

/-- The real Gaussian modular-symbol sum, with the conductor-32 winding symbol normalized to one. -/
def winding (n : ℕ) (hn : 0<n) : ℤ :=
  haveI : NeZero (4*n) := ⟨by omega⟩
  ∑ j : ZMod (4*n), weight n j.val * (symbol (j.val:ℤ) n).re

noncomputable def tau (n : ℕ) (hn : 0<n) : ℂ :=
  haveI : NeZero (4*n) := ⟨by omega⟩
  gaussSum (character n hn.ne') ZMod.stdAddChar

lemma paired {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hw : Γ.strictWidthInfty=1) (F : CuspForm Γ 2)
    (hF : ∀ z : ℍ, F z=h (4*(z:ℂ))) (n j : ℕ) (hn : 0<n) :
    periodSymbol F ((j:ℝ)/(4*n)) + periodSymbol F (-(j:ℝ)/(4*n)) =
      2*((symbol (j:ℤ) n).re:ℂ)*baseConstant := by
  obtain ⟨J,hJ,h0,hT,C,hW⟩ := primitive
  obtain ⟨hz,_,_,_⟩ := cusp_rules h0 hT hW
  have e0 := symbol_eq_boundary hw F hF 0 hJ h0 (A:=C) (by simpa [Bound] using hz)
  have hC : C=baseConstant := by simpa only [Rat.cast_zero,zero_symbol F hF] using e0.symm
  let r : ℚ := (j:ℚ)/(4*n)
  have he : 4*(r:ℝ)=((j:ℤ):ℝ)/n := by dsimp [r]; push_cast; field_simp
  obtain ⟨hp,hm⟩ := cusp_value h0 hT hW (j:ℤ) n hn
  have e1 := symbol_eq_boundary hw F hF r hJ h0 (A:=((symbol (j:ℤ) n:GaussianInt):ℂ)*C) (by
    simpa only [Bound,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,he] using hp)
  have e2 := symbol_eq_boundary hw F hF (-r) hJ h0 (A:=((star (symbol (j:ℤ) n):GaussianInt):ℂ)*C) (by
    simpa only [Bound,Rat.cast_neg,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,mul_neg,he] using hm)
  rw [hC] at e1 e2
  have hsum := congrArg₂ (·+·) e1 e2
  simp only [r,Rat.cast_neg,Rat.cast_div,Rat.cast_natCast,Rat.cast_mul,Rat.cast_ofNat,←neg_div,←add_mul] at hsum
  rw [hsum]
  congr 1
  simp [GaussianInt.toComplex_def]
  ring

lemma twist_sum (n : ℕ) (hn : n%8=2) (hs : Squarefree n) (L : ℂ → ℂ)
    (he : AnalyticOnNhd ℂ L univ) (hprod : ∀ s : ℝ, 2<s →
      HasProd (fun p : Nat.Primes => if p.val ∣ 2*n then (1:ℂ) else
        let T := (p.val:ℂ)^(-(s:ℂ))
        (1-(curveTrace n p:ℂ)*T+(p.val:ℂ)*T^2)⁻¹) (L s)) :
    tau n (by omega) * L 1 = (winding n (by omega):ℂ)*baseConstant := by
  obtain ⟨H,hH,hw,F,hF,hfc⟩ := TunnellEtaValue.actual_form
  letI : H.IsArithmetic := hH
  letI : NeZero (4*n) := ⟨by omega⟩
  obtain ⟨K,hK,kw,G,ht,hv,_⟩ := jacobi_twist_integral hn hs hw F
  letI : K.IsArithmetic := hK
  let M := ModularForm.L (by decide : (0:ℤ)<2) G
  have a (m : ℕ) : (qExpansion 1 G).coeff m = gaussCoeff n m := by
    rw [ht,hfc,TunnellArithmetic.eta_eq_mass
      (TunnellTruncated.cubic_congruence (fun N => TunnellCubicFinite.cubic (Polynomial.X^8) N))
      (TunnellTruncated.theta_congruence (fun d N => TunnellBalanced.balanced _ N))]
    rfl
  have hM : AnalyticOnNhd ℂ M univ := fun z _ => (CuspForm.differentiable_L (by decide : (0:ℤ)<2) G).analyticAt z
  have eqM := TunnellMellin.entire_unique he hM 2 (fun s hgt => by
    have hl := (hprod s hgt).unique (lattice_euler n s (by linarith))
    have hsum : HasSum (fun m : ℕ => gaussCoeff n m / (m:ℂ)^(s:ℂ)) (M s) := by
      have h := CuspForm.hasSum_L (by decide : (0:ℤ)<2) G (s:=(s:ℂ)) (by norm_num; linarith)
      simpa only [kw,Complex.ofReal_one,Complex.one_cpow,one_mul,a,M] using h
    exact hl.trans ((shell_expansion n s (by linarith)).unique hsum))
  rw [eqM]
  let χ := character n (by omega)
  let P (j : ZMod (4*n)) := periodSymbol F ((j.val:ℝ)/(4*n))
  let Q (j : ZMod (4*n)) := periodSymbol F (-(j.val:ℝ)/(4*n))
  have evenχ : χ.Even := by
    obtain ⟨d,hd⟩ : 2∣n := Nat.dvd_of_mod_eq_zero (by omega)
    subst n
    exact character_even (by omega)
  have hsym : ∑ j, χ j * P j = ∑ j, χ j * Q j := by
    apply Fintype.sum_equiv (Equiv.neg _)
    intro j
    rw [Equiv.neg_apply,evenχ.eval_neg]
    congr 1
    simpa only [P,Q,Nat.cast_mul,Nat.cast_ofNat] using (reflected_symbol F hw j).symm
  have sum2 : (2:ℂ)*(∑ j, χ j*P j) = 2*(winding n (by omega):ℂ)*baseConstant := by
    calc _ = (∑ j, χ j*P j) + ∑ j, χ j*Q j := by rw [←hsym,two_mul]
         _ = ∑ j, χ j*(P j+Q j) := by simp [mul_add,Finset.sum_add_distrib]
         _ = _ := by
           unfold winding
           simp only [P,Q,paired hw F hF n _ (by omega),Int.cast_sum,Int.cast_mul,Finset.mul_sum,Finset.sum_mul]
           apply Finset.sum_congr rfl
           intro j _
           change (weight n j.val:ℂ)*_=_
           ring
  change gaussSum χ ZMod.stdAddChar * M 1 = _
  change gaussSum χ ZMod.stdAddChar * M 1 = ∑ j, χ j*P j at hv
  linear_combination hv + sum2/2

end TunnellFiniteSymbols

end

section

/- The square-value assertion as a finite winding-symbol identity for each squarefree d ≡ 1 mod 4. -/

namespace TunnellFiniteSymbols
open TunnellFricke TunnellModularSymbol TunnellWaldspurgerLocal TunnellTwistCharacter
open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology

lemma base_ne_zero : baseConstant ≠ 0 := by
  rw [baseConstant_real,Complex.ofReal_ne_zero]
  apply (mul_pos (by positivity : 0<2*Real.pi) _).ne'
  obtain ⟨H,hH,hw,F,hF,_⟩ := TunnellEtaValue.actual_form
  letI : H.IsArithmetic := hH
  have hi : IntegrableOn imaginaryValue (Ioi (0:ℝ)) := by
    have hr := (integrable_vertical F).re
    apply hr.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change (F (ofComplex (Complex.I*t))).re = (h (4*(Complex.I*t))).re
    rw [hF,ofComplex_apply_of_im_pos (by simpa using (show 0<t from ht) : 0<(Complex.I*(t:ℂ)).im)]
  apply (setIntegral_pos_iff_support_of_nonneg_ae _ hi).mpr
  · have hs : Function.support imaginaryValue ∩ Ioi (0:ℝ) = Ioi 0 :=
      inter_eq_right.mpr (fun _ ht => (imaginary_cast ht).1.ne')
    rw [hs,Real.volume_Ioi]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (imaginary_cast ht).1.le

end TunnellFiniteSymbols

end

section

/- A distinguished polynomial representative of the positive square root of 8d in a cyclotomic field. -/

namespace TunnellRootPolynomial
open Finset Polynomial Complex
open scoped Real

noncomputable def root (d : ℕ) := exp (2*(Real.pi:ℂ)*I/(16*d))
noncomputable def angle (d j : ℕ) := Real.pi * j/(8*d)
noncomputable def chord (d j : ℕ) := 2*Real.sin (angle d j)

noncomputable def chordPoly (d j : ℕ) : ℤ[X] := (X^(16*d-j)-X^j)*X^(4*d)
noncomputable def rootPoly (d : ℕ) : ℤ[X] := chordPoly d (2*d) * ∏ j ∈ range (4*d-1), chordPoly d (j+1)

lemma primitive {d : ℕ} (hd : 0<d) : IsPrimitiveRoot (root d) (16*d) := by
  simpa [root] using Complex.isPrimitiveRoot_exp (16*d) (by omega)

lemma root_pow (d j : ℕ) : root d ^ j = exp ((angle d j:ℝ)*I) := by
  rw [root,←exp_nat_mul]; congr 1; unfold angle; push_cast; ring

lemma angle_half {d : ℕ} (hd : 0<d) : angle d (4*d) = Real.pi/2 := by
  simp only [angle,Nat.cast_mul,Nat.cast_ofNat]; field_simp; ring

lemma angle_quarter {d : ℕ} (hd : 0<d) : angle d (2*d) = Real.pi/4 := by
  simp only [angle,Nat.cast_mul,Nat.cast_ofNat]; field_simp; ring

lemma eval_chord {d : ℕ} (hd : 0<d) {j : ℕ} (hj : j≤16*d) :
    aeval (root d) (chordPoly d j) = (chord d j:ℂ) := by
  have hr : root d≠0 := exp_ne_zero _
  have hinv : root d ^ (16*d-j) = (root d^j)⁻¹ := by
    rw [←one_div]
    apply (eq_div_iff (pow_ne_zero j hr)).mpr
    rw [←pow_add,Nat.sub_add_cancel hj,(primitive hd).pow_eq_one]
  have hi : root d^(4*d)=I := by
    rw [root_pow,angle_half hd,ofReal_div,ofReal_ofNat,exp_pi_div_two_mul_I]
  rw [chordPoly,map_mul,map_sub,map_pow,map_pow,map_pow,aeval_X,hinv,hi,root_pow,←exp_neg]
  unfold chord
  push_cast
  rw [two_sin,neg_mul]

lemma chord_pos {d j : ℕ} (hj : 0<j) (hjd : j<8*d) : 0<chord d j := by
  have hd : 0<d := by omega
  apply mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi (by dsimp [angle]; positivity) _)
  dsimp [angle]
  apply (div_lt_iff₀ (by positivity : (0:ℝ)<8*d)).mpr
  apply mul_lt_mul_of_pos_left _ Real.pi_pos
  exact_mod_cast hjd

lemma chord_reflect {d j : ℕ} (hd : 0<d) (hj : j≤8*d) : chord d (8*d-j)=chord d j := by
  have h : angle d (8*d-j) = Real.pi-angle d j := by
    simp only [angle,Nat.cast_sub hj,Nat.cast_mul,Nat.cast_ofNat]
    field_simp
  rw [chord,h,Real.sin_pi_sub,chord]

lemma norm_factor {d j : ℕ} (hj : 0<j) (hjd : j<8*d) :
    ‖1-(root d^2)^j‖ = chord d j := by
  rw [norm_sub_rev,←pow_mul,root_pow]
  rw [mul_comm _ I, norm_exp_I_mul_ofReal_sub_one]
  have hr : angle d (2*j)/2=angle d j := by unfold angle; push_cast; ring
  rw [hr,Real.norm_eq_abs]
  exact abs_of_nonneg (chord_pos hj hjd).le

private lemma reflect_product (f : ℕ→ℝ) (m : ℕ) (hs : ∀ j < m, f (m+(j+1))= f (m-1-j)) :
    ∏ j ∈ range (2*m+1), f j = (∏ j ∈ range m, f j)^2*f m := by
  rw [show 2*m+1=m+(m+1) by omega,prod_range_add,prod_range_succ']
  have he : (∏ j ∈ range m, f (m+(j+1))) = ∏ j ∈ range m,f j :=
    (prod_congr rfl (fun j hj => hs j (mem_range.mp hj))).trans (prod_range_reflect f m)
  rw [he]; ring

lemma real_product {d : ℕ} (hd : 0<d) :
    2*(∏ j ∈ range (4*d-1),chord d (j+1))^2 = 8*(d:ℝ) := by
  let m := 4*d-1
  have hm : 4*d=m+1 := by dsimp [m]; omega
  have hn : 8*d=(2*m+1)+1 := by omega
  have hp : IsPrimitiveRoot (root d^2) (8*d) := by
    exact (primitive hd).pow (by omega) (show 16*d = 2*(8*d) by omega)
  rw [hn] at hp
  have prodEq := congrArg norm hp.prod_one_sub_pow_eq_order
  simp only [norm_prod] at prodEq
  have hf : (∏ k ∈ range (2*m+1), ‖1-(root d^2)^(k+1)‖) = ∏ k∈range (2*m+1),chord d (k+1) :=
    prod_congr rfl (fun k hk => norm_factor (Nat.succ_pos _) (by have := mem_range.mp hk; omega))
  rw [hf,reflect_product (fun k => chord d (k+1)) m] at prodEq
  · rw [←hm,chord,angle_half hd,Real.sin_pi_div_two,mul_one] at prodEq
    have hnorm : ‖(((2*m+1:ℕ):ℂ)+1)‖=8*(d:ℝ) := by
      rw [show (((2*m+1:ℕ):ℂ)+1)=((8*d:ℕ):ℂ) by rw [hn]; push_cast; ring]
      simp
    change 2*_=8*(d:ℝ)
    rw [←hnorm,←prodEq]
    ring
  · intro k hk
    have h : m+(k+1)+1=8*d-(m-1-k+1) := by omega
    rw [h,chord_reflect hd (by omega)]

theorem eval_rootPoly {d : ℕ} (hd : 0<d) :
    aeval (root d) (rootPoly d) = (Real.sqrt (8*d):ℂ) := by
  have he : (∏ k∈range (4*d-1),aeval (root d) (chordPoly d (k+1))) =
      ((∏ k∈range (4*d-1),chord d (k+1):ℝ):ℂ) := by
    rw [ofReal_prod]
    exact prod_congr rfl (fun k hk => eval_chord hd (by have := mem_range.mp hk; omega))
  rw [rootPoly,map_mul,map_prod,he,eval_chord hd (by omega),chord,angle_quarter hd,Real.sin_pi_div_four]
  norm_num only [mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)]
  rw [←ofReal_mul,ofReal_inj]
  have hprod : 0≤∏ j∈range (4*d-1),chord d (j+1) := prod_nonneg (fun k hk => (chord_pos (by omega) (by have := mem_range.mp hk; omega)).le)
  have hh := real_product hd
  have hsq := Real.sq_sqrt (show 0≤8*(d:ℝ) by positivity)
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [mul_pow,h2,hsq,hh]

end TunnellRootPolynomial

end

section

/- An integer polynomial test for the Gauss sign and a finite modular-symbol square identity. -/

namespace TunnellFiniteSymbols
open Finset Polynomial TunnellRootPolynomial TunnellTwistCharacter TunnellWaldspurgerLocal

noncomputable def chiPoly (d : ℕ) (hd : 0<d) : ℤ[X] :=
  haveI : NeZero (4*(2*d)) := ⟨by omega⟩
  ∑ j : ZMod (4*(2*d)), C (weight (2*d) j.val)*X^(2*j.val)

lemma eval_chiPoly {d : ℕ} (hd : 0<d) : aeval (root d) (chiPoly d hd)=tau (2*d) (by omega) := by
  let : NeZero (4*(2*d)) := ⟨by omega⟩
  unfold chiPoly tau gaussSum
  simp only [map_sum,map_mul,aeval_C,map_pow,aeval_X]
  apply sum_congr rfl
  intro j _
  change (weight (2*d) j.val:ℂ)*_= (weight (2*d) j.val:ℂ)*_
  congr 1
  have h := ZMod.stdAddChar_coe (N:=4*(2*d)) (j.val:ℤ)
  rw [Int.cast_natCast,ZMod.natCast_zmod_val] at h
  rw [h,root_pow]
  congr 1
  simp only [angle,Nat.cast_mul,Nat.cast_ofNat,Complex.ofReal_div,Complex.ofReal_mul,
    Complex.ofReal_natCast,Complex.ofReal_ofNat,Int.cast_natCast]
  ring

/-- The sign of the real quadratic Gauss sum, using only division of integer polynomials. -/
noncomputable def epsilon (d : ℕ) (hd : 0<d) : ℤ :=
  if (chiPoly d hd-rootPoly d) %ₘ cyclotomic (16*d) ℤ = 0 then 1 else -1

lemma sign_iff {d : ℕ} (hd : 0<d) :
    (chiPoly d hd-rootPoly d) %ₘ cyclotomic (16*d) ℤ = 0 ↔
      tau (2*d) (by omega)=(Real.sqrt (8*d):ℂ) := by
  rw [modByMonic_eq_zero_iff_dvd (cyclotomic.monic _ _),
    cyclotomic_eq_minpoly (primitive hd) (by omega),
    ←minpoly.isIntegrallyClosed_dvd_iff ((primitive hd).isIntegral (by omega)),
    map_sub,eval_chiPoly hd,eval_rootPoly hd,sub_eq_zero]

lemma signed_root {d : ℕ} (hs : Squarefree d) (hd : d%4=1) :
    tau (2*d) (by omega)=(epsilon d (by omega):ℂ)*(Real.sqrt (8*d):ℂ) := by
  have hd' : 0<d := by omega
  let : NeZero (4*(2*d)) := ⟨by omega⟩
  have hh := TunnellModularSymbol.gauss_sq (character_primitive hd hs)
    (character_quadratic (2*d) (by omega)) (character_even hd)
  change tau (2*d) (by omega)^2=((4*(2*d):ℕ):ℂ) at hh
  have hsq : (Real.sqrt (8*d):ℂ)^2=((4*(2*d):ℕ):ℂ) := by
    rw [←Complex.ofReal_pow,Real.sq_sqrt (by positivity)]
    push_cast
    ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hh.trans hsq.symm) with he|he
  · simp [epsilon,(sign_iff hd').mpr he,he]
  · by_cases h : (chiPoly d hd'-rootPoly d) %ₘ cyclotomic (16*d) ℤ = 0
    · simp [epsilon,h,(sign_iff hd').mp h]
    · simp [epsilon,h,he]

/-- Difference of two finite three-square counts, with explicit congruences for each lattice. -/
def shellPeriod (d : ℕ) : ℤ :=
  (((TunnellShell.shell (2*d)).filter (fun v => v.1%4=v.2.1%4 ∧ v.2.2%8=0)).card:ℤ)-
  ((TunnellShell.shell (2*d)).filter (fun v => v.1%4=v.2.1%4 ∧ v.2.2%4=0 ∧
    (v.1+v.2.1+2*(v.2.2/4))%4=0)).card

lemma shellPeriod_eq (d : ℕ) : shellPeriod d=localPeriod d := by
  classical
  simp only [shellPeriod,localPeriod,TunnellTestVector.first_iff,TunnellTestVector.second_iff]

end TunnellFiniteSymbols

end

lemma TunnellCuspEuclid.rec_eq_aux (k : ℕ) :
    Nat.rec (motive:=fun _ => ℤ → ℕ → GaussianInt) (fun _ _ => 1)
      (fun _ f a n => let r := a.bmod n
                      rot (a.bdiv n)*(if r=0 then 1 else if 2*r=-(n:ℤ) then 1-iunit else
                        1-f (if 0≤r then -(n:ℤ) else (n:ℤ)) (2*r.natAbs))) k = symbolAux k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext a n
    simp only [ih,symbolAux]

lemma TunnellCuspEuclid.rec_re (k : ℕ) (a : ℤ) (n : ℕ) :
    (Nat.rec (motive:=fun _ => ℤ → ℕ → GaussianInt) (fun _ _ => 1)
      (fun _ f b m => let r := b.bmod m
                      (if b.bdiv m%4=0 then 1 else if b.bdiv m%4=1 then (⟨0,1⟩:GaussianInt)
                        else if b.bdiv m%4=2 then -1 else -(⟨0,1⟩:GaussianInt))*
                        (if r=0 then 1 else if 2*r=-(m:ℤ) then 1-(⟨0,1⟩:GaussianInt) else
                          1-f (if 0≤r then -(m:ℤ) else (m:ℤ)) (2*r.natAbs))) k a n).re =
    (symbolAux k a n).re := by
  exact congrArg (fun f : ℤ → ℕ → GaussianInt => (f a n).re) (rec_eq_aux k)

theorem OMA.solution : OMA.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1.H2 := by
  classical
  refine ⟨TunnellFricke.baseConstant,TunnellFiniteSymbols.base_ne_zero,?_,?_⟩
  · intro d hs hd L hL hp
    have hs2 : Squarefree (2*d) := (Nat.squarefree_mul
      ((Nat.odd_iff.mpr (by omega) : Odd d).coprime_two_left)).mpr ⟨Nat.prime_two.squarefree,hs⟩
    have h := TunnellFiniteSymbols.twist_sum (2*d) (by omega) hs2 L hL hp
    rw [TunnellFiniteSymbols.signed_root hs hd] at h
    simp only [TunnellCuspEuclid.rec_re]
    change (Real.sqrt (8*d):ℂ)*L 1 =
      ((TunnellFiniteSymbols.epsilon d (by omega)*TunnellFiniteSymbols.winding (2*d) (by omega):ℤ):ℂ)*
      TunnellFricke.baseConstant
    rw [Int.cast_mul]
    by_cases he : TunnellFiniteSymbols.epsilon d (by omega)=1
    · simpa [he] using h
    · have hm : TunnellFiniteSymbols.epsilon d (by omega)= -1 := by
        unfold TunnellFiniteSymbols.epsilon at he ⊢
        split_ifs <;> simp_all
      simp only [hm,Int.cast_neg,Int.cast_one,neg_mul] at *
      linear_combination -h
  · intro d hd
    change TunnellLocalFourier.b 1 d=TunnellLocalFourier.b 4 d ∧
      (TunnellFiniteSymbols.shellPeriod d:ℂ)=2*TunnellLocalFourier.b 4 d ∧ _ ∧ _
    refine ⟨TunnellLocalFourier.one_eq_four hd,?_,?_,TunnellLocalFourier.four_zero⟩
    · rw [TunnellFiniteSymbols.shellPeriod_eq,TunnellWaldspurgerLocal.period_fourier d hd]
    · change TunnellLocalFourier.b 16 d=if d%8=1 then TunnellLocalFourier.b 4 d else 0
      split_ifs with ht
      · exact (TunnellLocalFourier.four_eq_sixteen ht).symm
      · exact TunnellLocalFourier.sixteen_zero ht
