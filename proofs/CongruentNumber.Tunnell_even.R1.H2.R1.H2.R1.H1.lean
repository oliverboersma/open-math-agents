import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1
import Mathlib

/-! The Gaussian Euler product and the holomorphic regularization of its weight-one kernel. -/

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
/- Grouping the Hecke character by its Gaussian residue classes. -/

namespace TunnellCMLSeries

open TunnellGaussian Finset

abbrev Residues (n : ℕ) := ZMod (4*n) × ZMod (4*n)

def residue (n : ℕ) (z : GaussianInt) : Residues n := (z.re, z.im)

def liftResidue {n : ℕ} (r : Residues n) : GaussianInt := ⟨r.1.val,r.2.val⟩

lemma residue_lift {n : ℕ} (hn : 0<n) (r : Residues n) : residue n (liftResidue r) = r := by
  letI : NeZero (4*n) := ⟨by omega⟩
  simp [liftResidue,residue]

noncomputable def charWeight (n : ℕ) (z : GaussianInt) : ℤ := by
  classical exact if Primary z then twistSign n z.norm.natAbs else 0

lemma twistSign_mod (n m : ℕ) : twistSign n (m % (4*n)) = twistSign n m := by
  have he : Even (4*n) := Even.mul_right (by decide) _
  have h : Odd (m % (4*n)) ↔ Odd m := by
    simp only [Nat.odd_iff, Nat.mod_mod_of_dvd _ he.two_dvd]
  by_cases hm : Odd m
  · simpa [twistSign, h, hm] using (jacobiSym.mod_right' n hm).symm
  · simp [twistSign, h, hm]

theorem charWeight_residue (n : ℕ) {z w : GaussianInt} (h : residue n z = residue n w) :
    charWeight n z = charWeight n w := by
  have ha := (ZMod.intCast_eq_intCast_iff _ _ _).mp (congrArg Prod.fst h)
  have hb := (ZMod.intCast_eq_intCast_iff _ _ _).mp (congrArg Prod.snd h)
  change z.re ≡ w.re [ZMOD ↑(4*n)] at ha
  change z.im ≡ w.im [ZMOD ↑(4*n)] at hb
  have h2 : (2:ℤ) ∣ (↑(4*n) : ℤ) := by exact_mod_cast (dvd_mul_of_dvd_left (by decide : 2∣4) n)
  have h4 : (4:ℤ) ∣ (↑(4*n) : ℤ) := by exact_mod_cast dvd_mul_right 4 n
  have hpr : Primary z ↔ Primary w := by
    rw [primary_iff,primary_iff,(hb.of_dvd h2).eq,((ha.add hb).of_dvd h4).eq]
  have hnorm : (z.norm.natAbs : ℕ) ≡ w.norm.natAbs [MOD 4*n] := by
    apply Int.natCast_modEq_iff.mp
    rw [GaussianInt.natCast_natAbs_norm,GaussianInt.natCast_natAbs_norm,norm_sq,norm_sq]
    exact (ha.pow 2).add (hb.pow 2)
  classical
  simp only [charWeight,hpr]
  have he := (twistSign_mod n z.norm.natAbs).symm.trans ((congrArg (twistSign n) hnorm).trans (twistSign_mod n w.norm.natAbs))
  rw [he]

lemma term_eq_weight (n : ℕ) (s : ℝ) (z : GaussianInt) :
    term n s z = (charWeight n z : ℂ) * gaussianTerm s z := by
  classical by_cases h : Primary z <;> simp [term,charWeight,h]

lemma lattice_as_tsum (n : ℕ) (s : ℝ) : latticeValue n s = ∑' z, term n s z := by
  classical
  exact tsum_subtype {z : GaussianInt | Primary z}
    (fun z => (twistSign n z.norm.natAbs:ℂ) * gaussianTerm s z)

noncomputable def residueSum (n : ℕ) (s : ℝ) (r : Residues n) : ℂ :=
  ∑' z : {z : GaussianInt // residue n z = r}, gaussianTerm s z.val

theorem lattice_by_residues (n : ℕ) (hn : 0<n) (s : ℝ) (hs : 3/2<s) :
    latticeValue n s =
      letI : NeZero (4*n) := ⟨by omega⟩
      ∑ r : Residues n, (charWeight n (liftResidue r):ℂ) * residueSum n s r := by
  classical
  letI : NeZero (4*n) := ⟨by omega⟩
  rw [lattice_as_tsum]
  have h := (summable_lattice n s hs).hasSum.tsum_fiberwise (residue n)
  rw [← h.tsum_eq,tsum_fintype]
  apply Finset.sum_congr rfl
  intro r _
  rw [residueSum,← tsum_mul_left]
  apply tsum_congr
  intro z
  rw [term_eq_weight,charWeight_residue n (z.property.trans (residue_lift hn r).symm)]

end TunnellCMLSeries
end

section
/- The regularized Weierstrass zeta function for constructing logarithmic derivatives of elliptic units. -/

namespace TunnellEllipticZeta

open Complex Filter Set
open scoped Topology PeriodPair

noncomputable def summand (w z : ℂ) := (z-w)⁻¹ + w⁻¹ + z/w^2
noncomputable def zeta (L : PeriodPair) (z : ℂ) := ∑' w : L.lattice, summand w z

lemma bound (r : ℝ) (hr : 0<r) (w z : ℂ) (hz : ‖z‖<r) (hw : 2*r≤‖w‖) :
    ‖summand w z‖ ≤ 2*r^2*‖w‖^(-3:ℝ) := by
  have hp : 0<‖w‖ := by linarith
  have hw0 := norm_pos_iff.mp hp
  have hzw : z-w≠0 := sub_ne_zero.mpr (fun e => by rw [e] at hz; linarith)
  have hdist : ‖w‖/2 ≤ ‖z-w‖ := by
    rw [norm_sub_rev]
    linarith [norm_sub_norm_le w z]
  have e : summand w z = z^2/(w^2*(z-w)) := by
    unfold summand
    field_simp
    ring
  rw [e,norm_div,norm_pow,norm_mul,norm_pow]
  calc
    _ ≤ r^2/(‖w‖^2*(‖w‖/2)) := by gcongr
    _ = 2*r^2*‖w‖^(-3:ℝ) := by
      rw [Real.rpow_neg hp.le, Real.rpow_ofNat]
      field_simp

theorem locally_uniform (L : PeriodPair) :
    HasSumLocallyUniformly (fun (w : L.lattice) z => summand w z) (zeta L) := by
  refine L.hasSumLocallyUniformly_aux _ (fun r w => 2*r^2*‖w‖^(-3:ℝ))
    (fun _ _ => (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) ?_
  intro r hr
  filter_upwards [eventually_ge_atTop (2*r)] with R hR
  rintro z hz w rfl
  exact bound r hr w z hz hR

lemma summand_deriv (w z : ℂ) (hz : z≠w) :
    HasDerivAt (summand w) (-(1/(z-w)^2-1/w^2)) z := by
  have h := ((((hasDerivAt_id z).sub_const w).inv (sub_ne_zero.mpr hz)).add_const w⁻¹).add
    ((hasDerivAt_id z).div_const (w^2))
  apply h.congr_deriv
  dsimp
  ring

theorem zeta_deriv (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    HasDerivAt (zeta L) (-L.weierstrassP z) z := by
  let U := (L.lattice : Set ℂ)ᶜ
  have ho : IsOpen U := L.isClosed_lattice.isOpen_compl
  have hdiff (s : Finset L.lattice) : DifferentiableOn ℂ (fun u => ∑ w ∈ s, summand w u) U := by
    apply DifferentiableOn.fun_sum
    intro w _
    exact fun u hu => (summand_deriv w u (fun e => hu (e ▸ w.property))).differentiableAt.differentiableWithinAt
  have hfun := (locally_uniform L).tendstoLocallyUniformlyOn (s := U)
  have hd := (hfun.deriv (.of_forall hdiff) ho).tendsto_at hz
  have e : deriv (zeta L) z = -L.weierstrassP z := by
    apply tendsto_nhds_unique hd
    apply ((L.hasSum_weierstrassP z).neg).congr'
    apply Filter.Eventually.of_forall
    intro s
    simp only [Function.comp_def]
    rw [deriv_fun_sum (fun (w : L.lattice) _ => (summand_deriv w z (fun e => hz (e ▸ w.property))).differentiableAt)]
    apply Finset.sum_congr rfl
    intro w _
    exact (summand_deriv w z (fun e => hz (e ▸ w.property))).deriv.symm
  rw [← e]
  exact (hfun.differentiableOn (.of_forall hdiff) ho).differentiableAt (ho.mem_nhds hz) |>.hasDerivAt

lemma zeta_neg (L : PeriodPair) (z : ℂ) : zeta L (-z) = -zeta L z := by
  unfold zeta
  rw [← tsum_neg]
  convert (Equiv.neg L.lattice).tsum_eq (fun w : L.lattice => -summand w z) using 1
  apply tsum_congr
  intro w
  simp only [Equiv.neg_apply,Submodule.coe_neg,summand]
  rw [show -z-(w:ℂ) = -(z-(-w:ℂ)) by ring, inv_neg]
  simp only [inv_neg,neg_sq,neg_div]
  ring

lemma quasi_period (L : PeriodPair) (l : L.lattice) :
    ∃ A : ℂ, ∀ z ∉ L.lattice, zeta L (z+l)=zeta L z+A := by
  let U := (L.lattice : Set ℂ)ᶜ
  have hcnt : (L.lattice : Set ℂ).Countable := by
    let : Countable L.lattice := Countable.of_equiv _ L.latticeEquivProd.toEquiv.symm
    exact to_countable _
  have hr : 1 < Module.rank ℝ ℂ := by simp
  have hc : IsPreconnected U := (hcnt.isPathConnected_compl_of_one_lt_rank hr).isConnected.isPreconnected
  have ho : IsOpen U := L.isClosed_lattice.isOpen_compl
  have hu {z : ℂ} (hz : z∈U) : z+(l:ℂ)∈U := fun e => hz (by
    simpa using sub_mem e l.property)
  have da {z : ℂ} (hz : z∈U) : HasDerivAt (fun w : ℂ => zeta L (w+l)) (-L.weierstrassP z) z := by
    simpa only [L.weierstrassP_add_coe,mul_one,Function.comp_def,id_eq] using! (zeta_deriv L _ (hu hz)).comp z ((hasDerivAt_id z).add_const (l:ℂ))
  obtain ⟨A,hA⟩ := ho.exists_eq_add_of_deriv_eq hc
    (fun z hz => (da hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (zeta_deriv L z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (da hz).deriv.trans (zeta_deriv L z hz).deriv.symm)
  exact ⟨A,fun z hz => hA hz⟩

private lemma translate_outside (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice)
    (l : L.lattice) : z+(l:ℂ) ∉ L.lattice := fun e => hz (by simpa using sub_mem e l.property)

noncomputable def increment (L : PeriodPair) (l : L.lattice) : ℂ :=
  zeta L (L.ω₁/2 + l) - zeta L (L.ω₁/2)

lemma zeta_shift (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) (l : L.lattice) :
    zeta L (z+l) = zeta L z + increment L l := by
  obtain ⟨A, hA⟩ := quasi_period L l
  rw [increment, hA _ L.ω₁_div_two_notMem_lattice, hA _ hz]
  ring

noncomputable def quasiPeriods (L : PeriodPair) : L.lattice →+ ℂ where
  toFun := increment L
  map_zero' := by simp [increment]
  map_add' l k := by
    change zeta L (L.ω₁/2 + ((l+k : L.lattice):ℂ)) - _ = _
    rw [Submodule.coe_add, ← add_assoc,
      zeta_shift L (translate_outside L L.ω₁_div_two_notMem_lattice l) k,
      zeta_shift L L.ω₁_div_two_notMem_lattice l]
    ring

/-- The logarithmic derivative of the integer-multiplication elliptic unit. -/
noncomputable def multiplicationZeta (L : PeriodPair) (a : ℕ) (z : ℂ) : ℂ :=
  (a:ℂ) * zeta L ((a:ℂ)*z) - (a:ℂ)^2 * zeta L z

lemma multiplicationZeta_periodic (L : PeriodPair) (a : ℕ) (z : ℂ) (l : L.lattice)
    (hz : z ∉ L.lattice) (haz : (a:ℂ)*z ∉ L.lattice) :
    multiplicationZeta L a (z+l) = multiplicationZeta L a z := by
  have H : increment L (a • l) = (a:ℂ) * increment L l :=
    (map_nsmul (quasiPeriods L) a l).trans (nsmul_eq_mul a _)
  have e : (a:ℂ)*(l:ℂ) = ((a • l : L.lattice):ℂ) := by simp [nsmul_eq_mul]
  unfold multiplicationZeta
  rw [mul_add, e, zeta_shift L haz, zeta_shift L hz, H]
  ring

lemma multiplicationZeta_odd (L : PeriodPair) (a : ℕ) (z : ℂ) :
    multiplicationZeta L a (-z) = -multiplicationZeta L a z := by
  simp only [multiplicationZeta, mul_neg, zeta_neg]
  ring

end TunnellEllipticZeta
end

section
/- The weight-one Eisenstein kernel with the integer Euler factor applied before summation. -/

namespace TunnellCMRegularized

open Complex Filter Set
open scoped Topology

noncomputable def kernel (s w : ℂ) := w * exp (-2*s*(Real.log ‖w‖ : ℂ))

lemma kernel_mul (s w u : ℂ) : kernel s (w*u) = kernel s w * kernel s u := by
  by_cases hw : w=0
  · simp [hw,kernel]
  by_cases hu : u=0
  · simp [hu,kernel]
  rw [kernel,kernel,kernel,norm_mul,Real.log_mul (norm_ne_zero_iff.mpr hw) (norm_ne_zero_iff.mpr hu),
    ofReal_add,mul_add,exp_add]
  ring

lemma norm_kernel (s w : ℂ) (hw : w≠0) : ‖kernel s w‖ = ‖w‖^(1-2*s.re) := by
  have hp := norm_pos_iff.mpr hw
  rw [kernel,norm_mul,norm_exp,Real.rpow_def_of_pos hp]
  nth_rw 1 [← Real.exp_log hp]
  rw [← Real.exp_add]
  congr 1
  simp [Complex.mul_re]
  ring

lemma kernel_differentiable (w : ℂ) : Differentiable ℂ (kernel · w) := by
  unfold kernel
  fun_prop

lemma norm_log_error {u : ℂ} (hu : ‖u‖ ≤ 1/2) :
    |Real.log ‖1+u‖-u.re| ≤ ‖u‖^2 := by
  have hi : (1-‖u‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div,div_le_iff₀ (by linarith)]
    linarith
  calc
    _ ≤ ‖log (1+u)-u‖ := by simpa only [sub_re, log_re] using abs_re_le_norm (log (1+u)-u)
    _ ≤ ‖u‖^2 * (1-‖u‖)⁻¹ / 2 := norm_log_one_add_sub_self_le (by linarith)
    _ ≤ ‖u‖^2 * 2 / 2 := by gcongr
    _ = _ := by ring

noncomputable def linearPart (s u : ℂ) := u - 2*s*(u.re : ℂ)

lemma local_error {s u : ℂ} {R : ℝ} (hs : ‖s‖ ≤ R) (hu : ‖u‖ ≤ 1/2)
    (hsmall : 3*R*‖u‖ ≤ 1) :
    ‖kernel s (1+u) - 1 - linearPart s u‖ ≤ (9*R^2+8*R)*‖u‖^2 := by
  have hR := (norm_nonneg s).trans hs
  have hu0 := norm_nonneg u
  let A : ℂ := -2*s*(Real.log ‖1+u‖ : ℂ)
  let B : ℂ := -2*s*(u.re : ℂ)
  have ha : ‖A‖ ≤ 3*R*‖u‖ := by
    have hl : |Real.log ‖1+u‖| ≤ 3/2*‖u‖ :=
      by simpa only [log_re] using (abs_re_le_norm (log (1+u))).trans (norm_log_one_add_half_le_self hu)
    dsimp [A]
    simp only [norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ 2*R*(3/2*‖u‖) := by gcongr
      _ = _ := by ring
  have hAB : ‖A-B‖ ≤ 2*R*‖u‖^2 := by
    dsimp [A,B]
    rw [← mul_sub, ← ofReal_sub]
    simp only [norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs]
    gcongr
    exact norm_log_error hu
  have e : kernel s (1+u) - 1 - linearPart s u =
      (exp A-1-A) + (A-B) + u*(exp A-1) := by
    unfold kernel linearPart
    dsimp [A,B]
    ring
  rw [e]
  calc
    _ ≤ (‖exp A-1-A‖+‖A-B‖) + ‖u‖*‖exp A-1‖ := by
      rw [← norm_mul]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ((3*R*‖u‖)^2+2*R*‖u‖^2) + ‖u‖*(2*(3*R*‖u‖)) := by
      gcongr
      · exact (norm_exp_sub_one_sub_id_le (ha.trans hsmall)).trans (pow_le_pow_left₀ (norm_nonneg _) ha 2)
      · exact (norm_exp_sub_one_le (ha.trans hsmall)).trans (by gcongr)
    _ = _ := by ring

noncomputable def difference (a : ℕ) (z w s : ℂ) :=
  (a:ℂ)^2 * (kernel s (w+z)-kernel s w) -
    (a:ℂ) * (kernel s (w+(a:ℂ)*z)-kernel s w)

lemma linear_nat (a : ℕ) (s u : ℂ) :
    linearPart s ((a:ℂ)*u) = (a:ℂ)*linearPart s u := by
  simp [linearPart, Complex.mul_re]
  ring

lemma difference_bound {s z w : ℂ} (hw : w≠0) {R : ℝ} (hs : ‖s‖ ≤ R) (a : ℕ)
    (hu : ‖z/w‖ ≤ 1/2) (hv : ‖(a:ℂ)*(z/w)‖ ≤ 1/2)
    (hsu : 3*R*‖z/w‖ ≤ 1) (hsv : 3*R*‖(a:ℂ)*(z/w)‖ ≤ 1) :
    ‖difference a z w s‖ ≤ (((a:ℝ)^2+(a:ℝ)^3)*(9*R^2+8*R)*‖z‖^2) *
      ‖w‖^(-1-2*s.re) := by
  let u := z/w
  let err (v : ℂ) := kernel s (1+v) - 1 - linearPart s v
  have e : difference a z w s = kernel s w * ((a:ℂ)^2*err u-(a:ℂ)*err ((a:ℂ)*u)) := by
    have e₁ : w+z = w*(1+u) := by dsimp [u]; field_simp
    have e₂ : w+(a:ℂ)*z = w*(1+(a:ℂ)*u) := by dsimp [u]; field_simp
    unfold difference
    rw [e₁,e₂,kernel_mul,kernel_mul]
    dsimp [err]
    rw [linear_nat]
    ring
  have h₁ := local_error hs hu hsu
  have h₂ := local_error hs hv hsv
  rw [e,norm_mul,norm_kernel _ _ hw]
  calc
    _ ≤ ‖w‖^(1-2*s.re) * ((a:ℝ)^2 * ((9*R^2+8*R)*‖u‖^2) +
        (a:ℝ) * ((9*R^2+8*R)*‖(a:ℂ)*u‖^2)) := by
      gcongr
      apply (norm_sub_le _ _).trans
      simp only [norm_mul,norm_pow,Complex.norm_natCast]
      gcongr
      simpa only [norm_mul,Complex.norm_natCast] using h₂
    _ = _ := by
      have hp := norm_pos_iff.mpr hw
      have he : (-1-2*s.re)=(1-2*s.re)-2 := by ring
      simp only [u,norm_div,norm_mul,Complex.norm_natCast]
      rw [he,Real.rpow_sub hp (1-2*s.re) 2,Real.rpow_ofNat]
      ring

def domain : Set ℂ := {s | 3/4 < s.re}

lemma domain_open : IsOpen domain := isOpen_lt continuous_const continuous_re

theorem regularized_summable (L : PeriodPair) (a : ℕ) (z : ℂ) :
    SummableLocallyUniformlyOn (fun (w : L.lattice) => difference a z w) domain := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually domain_open
  intro K hK hc
  obtain ⟨R₀,hR₀⟩ := hc.exists_bound_of_continuousOn (continuous_id (X := ℂ)).continuousOn
  let R := max R₀ 1
  have hR : 0 ≤ R := le_trans (by norm_num : (0:ℝ)≤1) (le_max_right _ _)
  let C := ((a:ℝ)^2+(a:ℝ)^3)*(9*R^2+8*R)*‖z‖^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨fun w => C*‖(w:ℂ)‖^(-5/2:ℝ),
    (ZLattice.summable_norm_rpow L.lattice _ (by simp; norm_num)).mul_left _, ?_⟩
  have htop : Tendsto (fun w : L.lattice => ‖(w:ℂ)‖) cofinite atTop :=
    tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding L.isClosed_lattice.isClosedEmbedding_subtypeVal
  have ht : Tendsto (fun w : L.lattice => ‖z/(w:ℂ)‖) cofinite (𝓝 0) := by
    simp only [norm_div]
    exact tendsto_const_nhds.div_atTop htop
  have ht' : Tendsto (fun w : L.lattice => ‖(a:ℂ)*(z/(w:ℂ))‖) cofinite (𝓝 0) := by
    simpa only [norm_mul,mul_zero] using ht.const_mul ‖(a:ℂ)‖
  have hu := ht.eventually_le_const (by norm_num : (0:ℝ)<1/2)
  have hv := ht'.eventually_le_const (by norm_num : (0:ℝ)<1/2)
  have hsu : ∀ᶠ w : L.lattice in cofinite, 3*R*‖z/(w:ℂ)‖ ≤ 1 :=
    ((ht.const_mul (3*R)).eventually_le_const (by simp))
  have hsv : ∀ᶠ w : L.lattice in cofinite, 3*R*‖(a:ℂ)*(z/(w:ℂ))‖ ≤ 1 :=
    ((ht'.const_mul (3*R)).eventually_le_const (by simp))
  filter_upwards [hu,hv,hsu,hsv,htop.eventually_ge_atTop 1] with w h1 h2 h3 h4 hw
  intro s hs
  have hsR : ‖s‖ ≤ R := (hR₀ s hs).trans (le_max_left _ _)
  apply (difference_bound (norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hw)) hsR a h1 h2 h3 h4).trans
  apply mul_le_mul_of_nonneg_left _ hC
  exact Real.rpow_le_rpow_of_exponent_le hw (by have := hK hs; change 3/4 < s.re at this; linarith)

noncomputable def regularized (L : PeriodPair) (a : ℕ) (z s : ℂ) :=
  ∑' w : L.lattice, difference a z w s

theorem regularized_holomorphic (L : PeriodPair) (a : ℕ) (z : ℂ) :
    DifferentiableOn ℂ (regularized L a z) domain := by
  apply (regularized_summable L a z).differentiableOn domain_open
  intro w s _
  unfold difference kernel
  fun_prop

open scoped ComplexConjugate

lemma kernel_one (w : ℂ) : kernel 1 w = conj (w⁻¹) := by
  by_cases hw : w = 0
  · simp [hw,kernel]
  have hp := norm_pos_iff.mpr hw
  have e : (-2:ℂ)*1*(Real.log ‖w‖ : ℂ) = (↑(-2*Real.log ‖w‖ : ℝ):ℂ) := by push_cast; ring
  rw [kernel,e,← Complex.ofReal_exp,show (-2:ℝ)*Real.log ‖w‖ = -(Real.log ‖w‖ * 2) by ring,
    Real.exp_neg,Real.exp_mul,Real.exp_log hp,Real.rpow_ofNat,← normSq_eq_norm_sq,Complex.inv_def]
  simp

theorem regularized_critical (L : PeriodPair) (a : ℕ) (z : ℂ) :
    regularized L a z 1 = -conj (TunnellEllipticZeta.multiplicationZeta L a z) := by
  let f (z : ℂ) (w : L.lattice) := TunnellEllipticZeta.summand (-w) z
  have hf (z : ℂ) : HasSum (f z) (TunnellEllipticZeta.zeta L z) := by
    exact (Equiv.neg L.lattice).hasSum_iff.mpr (TunnellEllipticZeta.locally_uniform L).hasSum
  have ht := ((hf z).mul_left ((a:ℂ)^2)).sub ((hf ((a:ℂ)*z)).mul_left (a:ℂ))
  unfold regularized
  rw [show -conj (TunnellEllipticZeta.multiplicationZeta L a z) =
      conj ((a:ℂ)^2*TunnellEllipticZeta.zeta L z-(a:ℂ)*TunnellEllipticZeta.zeta L ((a:ℂ)*z)) by
        rw [← map_neg]; congr 1; unfold TunnellEllipticZeta.multiplicationZeta; ring,
    ← ht.tsum_eq,Complex.conj_tsum]
  apply tsum_congr
  intro w
  simp only [difference,kernel_one, f, TunnellEllipticZeta.summand, sub_neg_eq_add, inv_neg,
    neg_sq, map_sub,map_add,map_mul,map_pow,map_neg,map_natCast, map_div₀, map_inv₀]
  rw [add_comm (conj z) (conj (w:ℂ)),add_comm ((a:ℂ)*conj z) (conj (w:ℂ))]
  ring

lemma shifted_summable (L : PeriodPair) (z s : ℂ) (hs : 3/2<s.re) :
    Summable (fun w : L.lattice => kernel s (w+z)) := by
  have he : 1-2*s.re < -2 := by linarith
  apply Summable.of_norm
  apply (ZLattice.summable_norm_sub_rpow L.lattice (1-2*s.re) (by simpa using he) (-z)).congr
  intro w
  simp only [sub_neg_eq_add]
  by_cases h : (w:ℂ)+z=0
  · rw [h]
    simp [kernel,Real.zero_rpow (show 1-2*s.re≠0 by linarith)]
  · exact (norm_kernel _ _ h).symm

lemma unshifted_zero (L : PeriodPair) (s : ℂ) : ∑' w : L.lattice, kernel s w = 0 := by
  have h := (Equiv.neg L.lattice).tsum_eq (fun w : L.lattice => kernel s w)
  simp only [Equiv.neg_apply,Submodule.coe_neg] at h
  have hneg (w : ℂ) : kernel s (-w) = -(kernel s w) := by simp [kernel]
  simp only [hneg,tsum_neg] at h
  linear_combination -h/2

lemma shifted_period (L : PeriodPair) (z s : ℂ) (l : L.lattice) :
    (∑' w : L.lattice, kernel s (w+(z+l))) = ∑' w : L.lattice, kernel s (w+z) := by
  convert (Equiv.addRight l).tsum_eq (fun w : L.lattice => kernel s (w+z)) using 2 with w
  congr 1
  simp [add_left_comm,add_comm,add_assoc]

theorem regularized_large (L : PeriodPair) (a : ℕ) (z s : ℂ) (hs : 3/2<s.re)
    (hz : ((a:ℂ)-1)*z ∈ L.lattice) :
    regularized L a z s = ((a:ℂ)^2-(a:ℂ)) * ∑' w : L.lattice, kernel s (w+z) := by
  let l : L.lattice := ⟨((a:ℂ)-1)*z,hz⟩
  have he : (a:ℂ)*z=z+l := by dsimp [l]; ring
  have h₀ : Summable fun w : L.lattice => kernel s w := by
    simpa using shifted_summable L 0 s hs
  have h := (((shifted_summable L z s hs).hasSum.sub h₀.hasSum).mul_left ((a:ℂ)^2)).sub
    (((shifted_summable L ((a:ℂ)*z) s hs).hasSum.sub h₀.hasSum).mul_left (a:ℂ))
  rw [show regularized L a z s = _ from h.tsum_eq,unshifted_zero,he,shifted_period]
  ring

end TunnellCMRegularized
end

section
/- The critical CM L-value as a finite trace of multiplication-zeta values. -/

namespace TunnellCMCritical

open Complex Filter Set TunnellCMRegularized TunnellCMLSeries
open scoped Topology ComplexConjugate

noncomputable def periods (n : ℕ) (hn : 0<n) : PeriodPair where
  ω₁ := (4*n:ℕ)
  ω₂ := ((4*n:ℕ):ℂ)*I
  indep := by
    apply LinearIndependent.pair_iff.mpr
    intro x y he
    have hr := congrArg re he
    have hi := congrArg im he
    simp [Complex.mul_re,Complex.mul_im,hn.ne'] at hr hi
    exact ⟨hr,hi⟩

noncomputable def aux (n : ℕ) := 1+3*(4*n)

lemma aux_integral (n : ℕ) (hn : 0<n) (z : GaussianInt) :
    (((aux n:ℕ):ℂ)-1)*(z:ℂ) ∈ (periods n hn).lattice := by
  apply PeriodPair.mem_lattice.mpr
  refine ⟨3*z.re,3*z.im,?_⟩
  rw [GaussianInt.toComplex_def]
  simp [periods,aux]
  ring

lemma coe_sub_mem (n : ℕ) (hn : 0<n) {x y : GaussianInt} (he : residue n x=residue n y) :
    (x:ℂ)-(y:ℂ) ∈ (periods n hn).lattice := by
  have hx := (ZMod.intCast_eq_intCast_iff_dvd_sub y.re x.re (4*n)).mp (congrArg Prod.fst he.symm)
  have hy := (ZMod.intCast_eq_intCast_iff_dvd_sub y.im x.im (4*n)).mp (congrArg Prod.snd he.symm)
  obtain ⟨k,hk⟩ := hx
  obtain ⟨l,hl⟩ := hy
  refine PeriodPair.mem_lattice.mpr ⟨k,l,?_⟩
  have e₁ := congrArg (Int.cast : ℤ → ℂ) hk
  have e₂ := congrArg (Int.cast : ℤ → ℂ) hl
  simp only [Int.cast_sub,Int.cast_mul,Int.cast_natCast] at e₁ e₂
  change _ * (↑(4*n:ℕ):ℂ) + _ * ((↑(4*n:ℕ):ℂ)*I) = _
  rw [GaussianInt.toComplex_def,GaussianInt.toComplex_def]
  linear_combination -e₁-I*e₂

noncomputable def shiftMap (n : ℕ) (hn : 0<n) (r : Residues n)
    (x : {z : GaussianInt // residue n z=r}) : (periods n hn).lattice :=
  ⟨(x.val:ℂ)-(liftResidue r:ℂ), coe_sub_mem n hn (x.property.trans (residue_lift hn r).symm)⟩

lemma shift_bijective (n : ℕ) (hn : 0<n) (r : Residues n) : Function.Bijective (shiftMap n hn r) := by
  constructor
  · intro x y he
    have h := congrArg Subtype.val he
    apply Subtype.ext
    apply GaussianInt.toComplex_injective
    change (x.val:ℂ)-(liftResidue r:ℂ) = (y.val:ℂ)-(liftResidue r:ℂ) at h
    exact sub_left_inj.mp h
  · intro w
    obtain ⟨k,l,hw⟩ := PeriodPair.mem_lattice.mp w.property
    let y := liftResidue r
    let x : GaussianInt := ⟨y.re + (4*n:ℕ)*k, y.im + (4*n:ℕ)*l⟩
    have hx : residue n x=residue n y := by
      have hzero : ((↑(4*n:ℕ):ℤ) : ZMod (4*n)) = 0 := by simp only [Int.cast_natCast,ZMod.natCast_self]
      apply Prod.ext <;> simp only [residue,x,Int.cast_add,Int.cast_mul,hzero,zero_mul,add_zero]
    refine ⟨⟨x,hx.trans (residue_lift hn r)⟩,Subtype.ext ?_⟩
    change (x:ℂ)-(y:ℂ)=(w:ℂ)
    rw [← hw,GaussianInt.toComplex_def,GaussianInt.toComplex_def]
    change _ = (k:ℂ)*(↑(4*n:ℕ):ℂ)+(l:ℂ)*((↑(4*n:ℕ):ℂ)*I)
    simp only [x,Int.cast_add,Int.cast_mul,Int.cast_natCast]
    ring

lemma kernel_gaussian (s : ℝ) (z : GaussianInt) :
    kernel (s:ℂ) (z:ℂ) = gaussianTerm s z := by
  by_cases h : z=0
  · simp [h,kernel,gaussianTerm]
  have hp := norm_pos_iff.mpr (GaussianInt.toComplex_eq_zero.not.mpr h)
  rw [kernel,gaussianTerm,norm_sq_real,Real.rpow_def_of_pos (sq_pos_of_pos hp),Real.log_pow]
  have e : (-2:ℂ)*(s:ℂ)*(Real.log ‖(z:ℂ)‖ : ℂ) =
      -(↑((2:ℝ)*Real.log ‖(z:ℂ)‖*s):ℂ) := by push_cast; ring
  rw [e, Complex.exp_neg,← ofReal_exp,div_eq_mul_inv]
  norm_num

lemma shifted_residue (n : ℕ) (hn : 0<n) (r : Residues n) (s : ℝ) :
    (∑' w : (periods n hn).lattice, kernel (s:ℂ) (w+(liftResidue r:ℂ))) = residueSum n s r := by
  let e := Equiv.ofBijective _ (shift_bijective n hn r)
  rw [← e.tsum_eq (fun w : (periods n hn).lattice => kernel (s:ℂ) (w+(liftResidue r:ℂ)))]
  apply tsum_congr
  intro x
  change kernel (s:ℂ) (((x.val:ℂ)-(liftResidue r:ℂ))+(liftResidue r:ℂ)) = _
  rw [sub_add_cancel,kernel_gaussian]

noncomputable def traceSeries (n : ℕ) (hn : 0<n) (s : ℂ) : ℂ :=
  letI : NeZero (4*n) := ⟨by omega⟩
  ∑ r : Residues n, (charWeight n (liftResidue r):ℂ) *
    regularized (periods n hn) (aux n) (liftResidue r:ℂ) s

lemma traceSeries_large (n : ℕ) (hn : 0<n) (s : ℝ) (hs : 3/2<s) :
    traceSeries n hn s = ((aux n:ℂ)^2-(aux n:ℂ))*latticeValue n s := by
  letI : NeZero (4*n) := ⟨by omega⟩
  rw [traceSeries,lattice_by_residues n hn s hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [regularized_large _ _ _ _ (by simpa using hs) (aux_integral n hn (liftResidue r)),
    shifted_residue]
  ring

lemma traceSeries_analytic (n : ℕ) (hn : 0<n) : AnalyticOnNhd ℂ (traceSeries n hn) domain := by
  letI : NeZero (4*n) := ⟨by omega⟩
  apply DifferentiableOn.analyticOnNhd _ domain_open
  unfold traceSeries
  apply DifferentiableOn.fun_sum
  intro r _
  exact (regularized_holomorphic _ _ _).const_mul _

theorem central_trace (n : ℕ) (hn : 0<n) (L : ℂ → ℂ) (hL : AnalyticOnNhd ℂ L univ)
    (he : ∀ s : ℝ, 2<s → L s=latticeValue n s) :
    ((aux n:ℂ)^2-(aux n:ℂ))*L 1 =
        letI : NeZero (4*n) := ⟨by omega⟩
        ∑ r : Residues n, (charWeight n (liftResidue r):ℂ) *
          (-conj (TunnellEllipticZeta.multiplicationZeta (periods n hn) (aux n) (liftResidue r:ℂ))) := by
  letI : NeZero (4*n) := ⟨by omega⟩
  let G (s : ℂ) := ((aux n:ℂ)^2-(aux n:ℂ))*L s
  have hG : AnalyticOnNhd ℂ G domain := analyticOnNhd_const.mul (hL.mono (subset_univ _))
  have hm : Tendsto ((↑):ℝ → ℂ) (𝓝[≠] (3:ℝ)) (𝓝[≠] (3:ℂ)) := by
    apply continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
    intro x hx hy
    apply hx
    change (x:ℂ)=(3:ℂ) at hy
    exact_mod_cast hy
  have heq : EqOn G (traceSeries n hn) domain :=
    hG.eqOn_of_preconnected_of_frequently_eq (traceSeries_analytic n hn)
      (convex_halfSpace_re_gt _).isPreconnected (by norm_num [domain] : (3:ℂ)∈domain) <|
      hm.frequently <| Filter.Eventually.frequently <| by
        filter_upwards [(eventually_gt_nhds (show (2:ℝ)<3 by norm_num)).filter_mono nhdsWithin_le_nhds] with s hs
        dsimp [G]
        rw [he _ hs,traceSeries_large _ _ _ (by linarith)]
  calc
    _ = traceSeries n hn 1 := heq (by norm_num [domain] : (1:ℂ)∈domain)
    _ = _ := by simp only [traceSeries,regularized_critical]

end TunnellCMCritical
end

theorem OMA.solution : OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1.H1 := by
  classical
  refine fun n hn L hL hE => ?_
  exact TunnellCMCritical.central_trace n hn L hL (fun s hs =>
    (hE s hs).unique (TunnellCMLSeries.lattice_euler n s (by linarith)))
