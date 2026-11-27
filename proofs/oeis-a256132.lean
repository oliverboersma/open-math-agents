import OMAStatements.S_oeis_a256132
import Mathlib

/-!
Legendre–Gauss three squares, sufficiency. The squarefree reduction, auxiliary primes, and Minkowski argument are from Kenta Kitamura, KitaKen1/lean-eval-conway-schneeberger-fifteen, Submission/ConwayFifteen.lean at commit 4fafb6bb0d8fb1129b11e348b7ede02330da8b5c. Copyright 2026 Kenta Kitamura. Used under the Apache License, Version 2.0. The source project includes benchmark scaffolding copyright 2026 Lean FRO, LLC under the same license. This extraction uses only the proof and adds the natural-number and zero cases.
-/
open Matrix
namespace ThreeSquares

def IsSum3Sq (n : ℤ) : Prop := ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n

theorem IsSum3Sq.mul_sq {n : ℤ} (k : ℤ) (h : IsSum3Sq n) :
    IsSum3Sq (k ^ 2 * n) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨k * x, k * y, k * z, by linear_combination (k ^ 2) * hxyz⟩

private lemma odd_sq_mod8 {k : ℕ} (hk : ¬ 2 ∣ k) : k ^ 2 % 8 = 1 := by
  obtain ⟨j, hj⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t, j * (j + 1) = 2 * t := (Nat.even_mul_succ_self j).exists_two_nsmul _
  have : k ^ 2 = 8 * t + 1 := by subst hj; ring_nf; nlinarith [ht]
  omega

theorem isSum3Sq_of_core
    (core : ∀ m : ℕ, Squarefree m →
      (m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 6) →
      IsSum3Sq (m : ℤ)) :
    ∀ n : ℕ, 0 < n → (∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7)) →
      IsSum3Sq (n : ℤ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn hform
    by_cases h4 : 4 ∣ n
    · obtain ⟨m, rfl⟩ := h4
      have hm : IsSum3Sq (m : ℤ) :=
        IH m (by omega) (by omega)
          (fun a b hab => hform (a + 1) b (by rw [hab]; ring))
      obtain ⟨x, y, z, hxyz⟩ := hm
      exact ⟨2 * x, 2 * y, 2 * z, by push_cast; linear_combination (4 : ℤ) * hxyz⟩
    · by_cases h8 : n % 8 = 7
      · exact absurd (by omega : n = 4 ^ 0 * (8 * (n / 8) + 7))
          (hform 0 (n / 8))
      · -- strip the square part
        obtain ⟨m, k, hmk, hsf⟩ := Nat.sq_mul_squarefree n
        have hk2 : ¬ 2 ∣ k := by
          intro ⟨j, hj⟩
          exact h4 ⟨j ^ 2 * m, by subst hj; rw [← hmk]; ring⟩
        have hkodd : k ^ 2 % 8 = 1 := odd_sq_mod8 hk2
        have hmmod : m % 8 = n % 8 := by
          have h1 : n % 8 = k ^ 2 % 8 * (m % 8) % 8 := by
            rw [← Nat.mul_mod, hmk]
          rw [hkodd, one_mul] at h1
          omega
        have hcore : IsSum3Sq (m : ℤ) := by
          refine core m hsf ?_
          have hmod4 : ¬ n % 4 = 0 := fun hc => h4 (Nat.dvd_of_mod_eq_zero hc)
          omega
        have := hcore.mul_sq (k : ℤ)
        rwa [show ((k : ℤ)) ^ 2 * (m : ℤ) = ((n : ℕ) : ℤ) by
          rw [← hmk]; push_cast; ring] at this
end ThreeSquares
namespace Dirichlet

open Finset Function

theorem exists_prime_with_residues (n : ℕ) (hn : Squarefree n)
    (hodd : ¬ 2 ∣ n) (hpos : 0 < n) (c : ZMod 8) (hc : IsUnit c)
    (b : ∀ i : n.primeFactors, ZMod (i : ℕ)) (hb : ∀ i, b i ≠ 0) (N₀ : ℕ) :
    ∃ q : ℕ, q.Prime ∧ N₀ < q ∧ (q : ZMod 8) = c ∧
      ∀ i : n.primeFactors, (q : ZMod (i : ℕ)) = b i := by
  classical
  have hprime : ∀ i : n.primeFactors, Nat.Prime (i : ℕ) := fun i =>
    Nat.prime_of_mem_primeFactors i.2
  set a : n.primeFactors → ℕ := fun i => (i : ℕ) with ha
  have hprod : ∏ i, a i = n := by
    rw [ha]
    calc (∏ i : n.primeFactors, ((i : ℕ) : ℕ))
        = ∏ p ∈ n.primeFactors, p :=
          Finset.prod_coe_sort n.primeFactors (fun p => p)
      _ = n := Nat.prod_primeFactors_of_squarefree hn
  have hcop : Pairwise (Nat.Coprime on a) := by
    intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun hc' => hij (Subtype.ext hc')
    exact (Nat.coprime_primes (hprime i) (hprime j)).mpr hne
  have h8P : Nat.Coprime 8 (∏ i, a i) := by
    rw [hprod]
    have h2 : Nat.Coprime 2 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
    have := h2.pow_left 3
    norm_num at this
    exact this
  haveI : NeZero (8 * ∏ i, a i) :=
    ⟨by rw [hprod]; exact Nat.mul_ne_zero (by norm_num) hpos.ne'⟩
  set eP := ZMod.prodEquivPi a hcop with heP
  set e2 := ZMod.chineseRemainder h8P with he2
  set β : ZMod (∏ i, a i) := eP.symm b with hβ
  set α : ZMod (8 * ∏ i, a i) := e2.symm (c, β) with hα
  have hunitβ : IsUnit β := by
    refine IsUnit.map eP.symm ?_
    rw [Pi.isUnit_iff]
    intro i
    haveI : Fact (Nat.Prime (i : ℕ)) := ⟨hprime i⟩
    exact isUnit_iff_ne_zero.mpr (hb i)
  have hunitα : IsUnit α := by
    refine IsUnit.map e2.symm ?_
    rw [Prod.isUnit_iff]
    exact ⟨hc, hunitβ⟩
  obtain ⟨q, hqgt, hqp, hqeq⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod hunitα N₀
  refine ⟨q, hqp, hqgt, ?_, ?_⟩
  all_goals
    have hsplit : ((q : ZMod 8), (q : ZMod (∏ i, a i))) = (c, β) := by
      have h1 : e2 ((q : ℕ) : ZMod (8 * ∏ i, a i)) = (c, β) := by
        rw [hqeq, hα, RingEquiv.apply_symm_apply]
      rw [map_natCast] at h1
      rw [← h1, Prod.ext_iff]
      exact ⟨(Prod.fst_natCast q).symm, (Prod.snd_natCast q).symm⟩
  · exact (Prod.mk.injEq _ _ _ _).mp hsplit |>.1
  · intro i
    have hβq : (q : ZMod (∏ i, a i)) = β :=
      (Prod.mk.injEq _ _ _ _).mp hsplit |>.2
    have h2 : eP ((q : ℕ) : ZMod (∏ i, a i)) = b := by
      rw [hβq, hβ, RingEquiv.apply_symm_apply]
    rw [map_natCast] at h2
    have := congrFun h2 i
    simpa using this

end Dirichlet

namespace Ankeny

def formR (m c b t x y z : ℤ) : ℤ := t * (c * x + b * y) + m * z

def formPsi (c b h' x y : ℤ) : ℤ := c * x ^ 2 + 2 * b * x * y + h' * y ^ 2

def formQ (m c b h' t x y z : ℤ) : ℤ :=
  formR m c b t x y z ^ 2 + formPsi c b h' x y

theorem c_mul_formPsi {m c b h' : ℤ} (hch : c * h' = b ^ 2 + m) (x y : ℤ) :
    c * formPsi c b h' x y = (c * x + b * y) ^ 2 + m * y ^ 2 := by
  unfold formPsi
  linear_combination y ^ 2 * hch

theorem formPsi_nonneg {m c b h' : ℤ} (hc : 0 < c) (hm : 0 < m)
    (hch : c * h' = b ^ 2 + m) (x y : ℤ) : 0 ≤ formPsi c b h' x y := by
  have h := c_mul_formPsi hch x y
  nlinarith [sq_nonneg (c * x + b * y), sq_nonneg y]

theorem formPsi_pos {m c b h' : ℤ} (hc : 0 < c) (hm : 0 < m)
    (hch : c * h' = b ^ 2 + m) {x y : ℤ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < formPsi c b h' x y := by
  have h := c_mul_formPsi hch x y
  by_cases hy : y = 0
  · subst hy
    have hx : x ≠ 0 := by
      rcases hxy with h' | h'
      · exact h'
      · exact absurd rfl h'
    have hcx : c * x ≠ 0 := mul_ne_zero hc.ne' hx
    have h2 : 0 < (c * x) ^ 2 := by
      rcases lt_or_gt_of_ne hcx with h' | h' <;> nlinarith
    nlinarith [h]
  · have hy2 : 0 < y ^ 2 := by
      rcases lt_or_gt_of_ne hy with h' | h' <;> nlinarith
    nlinarith [h, sq_nonneg (c * x + b * y), mul_pos hm hy2]

theorem formQ_pos {m c b h' t : ℤ} (hc : 0 < c) (hm : 0 < m)
    (hch : c * h' = b ^ 2 + m) {x y z : ℤ}
    (hxyz : ¬(x = 0 ∧ y = 0 ∧ z = 0)) :
    0 < formQ m c b h' t x y z := by
  by_cases hxy : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := hxy
    have hz : z ≠ 0 := fun hz => hxyz ⟨rfl, rfl, hz⟩
    have hQ : formQ m c b h' t 0 0 z = (m * z) ^ 2 := by
      unfold formQ formR formPsi
      ring
    rw [hQ]
    have hmz : m * z ≠ 0 := mul_ne_zero hm.ne' hz
    rcases lt_or_gt_of_ne hmz with h' | h' <;> nlinarith
  · have hxy' : x ≠ 0 ∨ y ≠ 0 := by tauto
    have h1 := formPsi_pos hc hm hch hxy'
    have h2 := sq_nonneg (formR m c b t x y z)
    unfold formQ
    linarith

theorem m_dvd_formQ {m c b h' t : ℤ} (hch : c * h' = b ^ 2 + m)
    (hmt : m ∣ c * t ^ 2 + 1) (hcm : IsCoprime c m) (x y z : ℤ) :
    m ∣ formQ m c b h' t x y z := by
  obtain ⟨k, hk⟩ := hmt
  have hdvd : m ∣ c * formQ m c b h' t x y z := by
    refine ⟨k * (c * x + b * y) ^ 2 + 2 * c * t * (c * x + b * y) * z
      + c * m * z ^ 2 + y ^ 2, ?_⟩
    unfold formQ formR formPsi
    linear_combination ((c * x + b * y) ^ 2) * hk + y ^ 2 * hch
  exact hcm.symm.dvd_of_dvd_mul_left hdvd

theorem eq_of_dvd_of_lt_two_mul {m v : ℤ} (hm : 0 < m) (hv : m ∣ v)
    (h0 : 0 < v) (h2 : v < 2 * m) : v = m := by
  obtain ⟨k, rfl⟩ := hv
  have h1 : 1 ≤ k := by nlinarith
  have hk2 : k < 2 := by nlinarith
  have hk : k = 1 := by omega
  rw [hk, mul_one]

theorem formQ_eq_m {m c b h' t : ℤ} (hc : 0 < c) (hm : 0 < m)
    (hch : c * h' = b ^ 2 + m) (hmt : m ∣ c * t ^ 2 + 1) (hcm : IsCoprime c m)
    {x y z : ℤ} (hne : ¬(x = 0 ∧ y = 0 ∧ z = 0))
    (hlt : formQ m c b h' t x y z < 2 * m) :
    formQ m c b h' t x y z = m :=
  eq_of_dvd_of_lt_two_mul hm (m_dvd_formQ hch hmt hcm x y z)
    (formQ_pos hc hm hch hne) hlt

theorem even_factorization_of_not_isSquare {p m : ℕ} [hp : Fact p.Prime]
    (hns : ¬ IsSquare (-(m : ZMod p))) :
    ∀ N a b : ℕ, N = a ^ 2 + m * b ^ 2 → N ≠ 0 → Even (N.factorization p) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro a b hN hN0
    by_cases hpN : p ∣ N
    · have hpb : p ∣ b := by
        by_contra hpb
        apply hns
        have hb0 : (b : ZMod p) ≠ 0 := fun hb0 =>
          hpb ((CharP.cast_eq_zero_iff (ZMod p) p b).mp hb0)
        have hzero : ((a : ZMod p)) ^ 2 + (m : ZMod p) * ((b : ZMod p)) ^ 2 = 0 := by
          have h1 : ((N : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff _ p N).mpr hpN
          rw [hN] at h1
          push_cast at h1
          exact h1
        refine ⟨(a : ZMod p) * ((b : ZMod p))⁻¹, ?_⟩
        field_simp
        linear_combination -hzero
      have hpa : p ∣ a := by
        have hmb : p ∣ m * b ^ 2 := Dvd.dvd.mul_left (dvd_pow hpb two_ne_zero) m
        have ha2 : p ∣ a ^ 2 := by
          have hsub := Nat.dvd_sub hpN hmb
          have heq : N - m * b ^ 2 = a ^ 2 := by omega
          rwa [heq] at hsub
        exact hp.out.dvd_of_dvd_pow ha2
      obtain ⟨a', rfl⟩ := hpa
      obtain ⟨b', rfl⟩ := hpb
      have hNfac : N = p ^ 2 * (a' ^ 2 + m * b' ^ 2) := by rw [hN]; ring
      have hN'0 : a' ^ 2 + m * b' ^ 2 ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hNfac
        exact hN0 hNfac
      have hplt : 2 ≤ p := hp.out.two_le
      have hlt : a' ^ 2 + m * b' ^ 2 < N := by
        have h1 : 0 < a' ^ 2 + m * b' ^ 2 := Nat.pos_of_ne_zero hN'0
        have hp4 : 4 ≤ p ^ 2 := by nlinarith
        nlinarith [hNfac, h1, hp4]
      have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.out.pos.ne'
      have hval : N.factorization p
          = 2 + (a' ^ 2 + m * b' ^ 2).factorization p := by
        rw [hNfac, Nat.factorization_mul hp2 hN'0, Finsupp.add_apply, hp.out.factorization_pow, Finsupp.single_eq_same]
      rw [hval]
      exact Even.add ⟨1, rfl⟩ (IH _ hlt a' b' rfl hN'0)
    · rw [Nat.factorization_eq_zero_of_not_dvd hpN]
      exact Even.zero

theorem core_of_minkowski_point
    {m : ℕ} (hm : 0 < m) (hsf : Squarefree m)
    {q : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1)
    {δ c b h' t : ℤ} (hδ : δ = 1 ∨ δ = 2) (hcδ : c = δ * q)
    (hch : c * h' = b ^ 2 + (m : ℤ))
    (hmt : (m : ℤ) ∣ c * t ^ 2 + 1)
    (hcm : IsCoprime c (m : ℤ))
    (hC1 : ∀ p : ℕ, p.Prime → p ∣ m → p ≠ 2 → IsSquare ((-c : ℤ) : ZMod p))
    {x y z : ℤ} (hne : ¬(x = 0 ∧ y = 0 ∧ z = 0))
    (hlt : formQ (m : ℤ) c b h' t x y z < 2 * m) :
    ThreeSquares.IsSum3Sq (m : ℤ) := by
  have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq.pos
  have hc : 0 < c := by
    rcases hδ with h1 | h1 <;> rw [hcδ, h1] <;> linarith
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hQm := formQ_eq_m hc hmZ hch hmt hcm hne hlt
  have hcpsi := c_mul_formPsi hch x y
  have hv0 : 0 ≤ formPsi c b h' x y := formPsi_nonneg hc hmZ hch x y
  set v : ℤ := formPsi c b h' x y with hvd
  set R₁ : ℤ := formR (m : ℤ) c b t x y z with hRd
  have hv : R₁ ^ 2 + v = (m : ℤ) := by rw [hRd, hvd]; exact hQm
  have hVv : ((v.toNat : ℕ) : ℤ) = v := Int.toNat_of_nonneg hv0
  have h2sq : ∃ X Y : ℕ, v.toNat = X ^ 2 + Y ^ 2 := by
    rw [Nat.eq_sq_add_sq_iff]
    intro p hpmem hp43
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    haveI : Fact p.Prime := ⟨hpp⟩
    have hpV : p ∣ v.toNat := Nat.dvd_of_mem_primeFactors hpmem
    have hV0 : v.toNat ≠ 0 := (Nat.mem_primeFactors.mp hpmem).2.2
    have hp2 : p ≠ 2 := by omega
    have hpq : p ≠ q := by intro h; rw [h] at hp43; omega
    have hppZ : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hpp
    have hpvZ : ((p : ℕ) : ℤ) ∣ v := by
      have h := Int.natCast_dvd_natCast.mpr hpV
      rwa [hVv] at h
    have hpc : ¬ ((p : ℕ) : ℤ) ∣ c := by
      rw [hcδ]
      intro hdvd
      rcases hppZ.dvd_mul.mp hdvd with hdδ | hdq
      · rcases hδ with h1 | h1 <;> rw [h1] at hdδ
        · exact hppZ.not_unit (isUnit_of_dvd_one hdδ)
        · have h2' : p ∣ 2 := by exact_mod_cast hdδ
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h2')
      · have hq' : p ∣ q := by exact_mod_cast hdq
        exact hpq ((Nat.prime_dvd_prime_iff_eq hpp hq).mp hq')
    have hpcZ : ((c : ℤ) : ZMod p) ≠ 0 := by
      intro h0
      exact hpc ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp h0)
    by_cases hpm : p ∣ m
    · -- impossible branch
      exfalso
      have hpmZ : ((p : ℕ) : ℤ) ∣ (m : ℤ) := Int.natCast_dvd_natCast.mpr hpm
      have hpR : ((p : ℕ) : ℤ) ∣ R₁ := by
        refine hppZ.dvd_of_dvd_pow (n := 2) ?_
        have hRe : R₁ ^ 2 = (m : ℤ) - v := by rw [← hv]; ring
        rw [hRe]
        exact dvd_sub hpmZ hpvZ
      have hpA : ((p : ℕ) : ℤ) ∣ (c * x + b * y) := by
        refine hppZ.dvd_of_dvd_pow (n := 2) ?_
        have hAe : (c * x + b * y) ^ 2 = c * v - (m : ℤ) * y ^ 2 := by
          rw [hvd, hcpsi]; ring
        rw [hAe]
        exact dvd_sub (Dvd.dvd.mul_left hpvZ c) (Dvd.dvd.mul_right hpmZ (y ^ 2))
      obtain ⟨m₁, hm₁⟩ := hpm
      have hpm₁ : ¬ p ∣ m₁ := by
        rintro ⟨k, hk⟩
        have hu := Nat.isUnit_iff.mp (hsf p ⟨k, by rw [hm₁, hk]; ring⟩)
        have h2le := hpp.two_le
        omega
      obtain ⟨R', hR'⟩ := hpR
      obtain ⟨A', hA'⟩ := hpA
      have hmZcast : (m : ℤ) = ((p : ℕ) : ℤ) * ((m₁ : ℕ) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hm₁
      have hpne : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hpp.pos.ne'
      have hcancel : (c - y ^ 2) * ((m₁ : ℕ) : ℤ)
          = ((p : ℕ) : ℤ) * (c * R' ^ 2 + A' ^ 2) := by
        refine mul_left_cancel₀ hpne ?_
        linear_combination (-c) * hv + hcpsi + (c * (R₁ + ((p : ℕ) : ℤ) * R')) * hR'
          + ((c * x + b * y) + ((p : ℕ) : ℤ) * A') * hA'
          + (-(c - y ^ 2)) * hmZcast
      have hdvd2 : ((p : ℕ) : ℤ) ∣ (c - y ^ 2) := by
        rcases hppZ.dvd_mul.mp ⟨c * R' ^ 2 + A' ^ 2, hcancel⟩ with h | h
        · exact h
        · exact absurd (Int.natCast_dvd_natCast.mp h) hpm₁
      have hsqc : IsSquare ((c : ℤ) : ZMod p) := by
        have h0 : ((c - y ^ 2 : ℤ) : ZMod p) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd2
        push_cast at h0
        exact ⟨((y : ℤ) : ZMod p), by linear_combination h0⟩
      have hsqnc : IsSquare ((-c : ℤ) : ZMod p) := hC1 p hpp ⟨m₁, hm₁⟩ hp2
      have hsqneg : IsSquare (-1 : ZMod p) := by
        have hmul := hsqnc.mul hsqc.inv
        have he : ((-c : ℤ) : ZMod p) * ((c : ℤ) : ZMod p)⁻¹ = -1 := by
          push_cast
          field_simp
        rwa [he] at hmul
      rw [ZMod.exists_sq_eq_neg_one_iff] at hsqneg
      exact hsqneg hp43
    · -- descent branch
      have hmp0 : ((m : ℕ) : ZMod p) ≠ 0 := by
        intro h0
        exact hpm ((CharP.cast_eq_zero_iff (ZMod p) p m).mp h0)
      have hnsm : ¬ IsSquare (-((m : ℕ)) : ZMod p) := by
        intro hsq
        have hsqm : IsSquare ((m : ℕ) : ZMod p) := by
          have hveq : ((v : ℤ) : ZMod p) = 0 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpvZ
          have hcast := congrArg (fun w : ℤ => (w : ZMod p)) hv
          push_cast at hcast
          rw [hveq] at hcast  -- placeholder; fixed below if needed
          exact ⟨((R₁ : ℤ) : ZMod p), by linear_combination -hcast⟩
        have hone : IsSquare (-1 : ZMod p) := by
          have hmul := hsq.mul hsqm.inv
          have he : (-((m : ℕ)) : ZMod p) * ((m : ℕ) : ZMod p)⁻¹ = -1 := by
            field_simp
          rwa [he] at hmul
        rw [ZMod.exists_sq_eq_neg_one_iff] at hone
        exact hone hp43
      -- ℕ-side equation `c·v = A² + m·y²`
      have hcN : ((c.natAbs : ℕ) : ℤ) = c := Int.natAbs_of_nonneg hc.le
      have hEqN : c.natAbs * v.toNat
          = (c * x + b * y).natAbs ^ 2 + m * y.natAbs ^ 2 := by
        have hcast : ((c.natAbs * v.toNat : ℕ) : ℤ)
            = (((c * x + b * y).natAbs ^ 2 + m * y.natAbs ^ 2 : ℕ) : ℤ) := by
          push_cast
          rw [abs_of_nonneg hc.le, sq_abs, sq_abs, hVv]
          linarith [hcpsi]
        exact_mod_cast hcast
      have hcabs0 : c.natAbs ≠ 0 := by
        intro h0
        rw [Int.natAbs_eq_zero] at h0
        exact hc.ne' h0
      have hprod0 : c.natAbs * v.toNat ≠ 0 := Nat.mul_ne_zero hcabs0 hV0
      have heven := even_factorization_of_not_isSquare hnsm
        (c.natAbs * v.toNat) (c * x + b * y).natAbs y.natAbs hEqN hprod0
      have hpcabs : ¬ p ∣ c.natAbs := by
        intro hdvd
        exact hpc (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hdvd))
      rw [Nat.factorization_mul hcabs0 hV0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hpcabs, zero_add] at heven
      first
      | simpa only [Nat.factorization_def _ hpp] using heven
      | simpa only [Nat.padicValNat_def, Nat.factorization_def _ hpp] using heven
  obtain ⟨X, Y, hXY⟩ := h2sq
  refine ⟨R₁, X, Y, ?_⟩
  have hvXY : v = (X : ℤ) ^ 2 + (Y : ℤ) ^ 2 := by
    rw [← hVv]
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hXY
  linarith [hv, hvXY]

theorem exists_prime_delta (m₀ : ℕ) (hm₀ : 0 < m₀) (hodd : ¬ 2 ∣ m₀)
    (δ : ℕ) (hδ : δ = 1 ∨ δ = 2) (r : ℕ) (hr : r = 1 ∨ r = 5) (N₀ : ℕ) :
    ∃ q : ℕ, q.Prime ∧ N₀ < q ∧ q % 8 = r ∧ (m₀ : ℤ) ∣ (δ : ℤ) * q + 1 := by
  haveI : NeZero m₀ := ⟨hm₀.ne'⟩
  haveI : NeZero (8 * m₀) := ⟨by positivity⟩
  have h8m : Nat.Coprime 8 m₀ := by
    have h2 : Nat.Coprime 2 m₀ := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
    have h8 := h2.pow_left 3
    norm_num at h8
    exact h8
  have hδu : IsUnit ((δ : ℕ) : ZMod m₀) := by
    rcases hδ with h1 | h1 <;> subst h1
    · simp
    · rw [Nat.cast_ofNat]
      refine (ZMod.isUnit_iff_coprime 2 m₀).mpr ?_
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
  have hru : IsUnit ((r : ℕ) : ZMod 8) := by
    rcases hr with h1 | h1 <;> subst h1
    · simp
    · exact ⟨⟨5, 5, by decide, by decide⟩, by rfl⟩
  set w : ZMod m₀ := -(((δ : ℕ) : ZMod m₀))⁻¹ with hw
  have hwu : IsUnit w := by
    rw [hw]
    have hmul : (-((((δ : ℕ) : ZMod m₀)))⁻¹) * (-(((δ : ℕ) : ZMod m₀))) = 1 := by
      rw [neg_mul_neg, mul_comm]
      exact ZMod.mul_inv_of_unit _ hδu
    exact ⟨⟨_, _, hmul, by rwa [mul_comm] at hmul⟩, rfl⟩
  set e2 := ZMod.chineseRemainder h8m with he2
  set α : ZMod (8 * m₀) := e2.symm (((r : ℕ) : ZMod 8), w) with hα
  have hunitα : IsUnit α := by
    refine IsUnit.map e2.symm ?_
    rw [Prod.isUnit_iff]
    exact ⟨hru, hwu⟩
  obtain ⟨q, hqgt, hqp, hqeq⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunitα N₀
  have hsplit : ((q : ZMod 8), (q : ZMod m₀)) = (((r : ℕ) : ZMod 8), w) := by
    have h1 : e2 ((q : ℕ) : ZMod (8 * m₀)) = (((r : ℕ) : ZMod 8), w) := by
      rw [hqeq, hα, RingEquiv.apply_symm_apply]
    rw [map_natCast] at h1
    rw [← h1, Prod.ext_iff]
    exact ⟨(Prod.fst_natCast q).symm, (Prod.snd_natCast q).symm⟩
  have hq8 : q % 8 = r := by
    have h1 : (q : ZMod 8) = ((r : ℕ) : ZMod 8) := (Prod.mk.injEq _ _ _ _).mp hsplit |>.1
    have h2 : q % 8 = r % 8 := (ZMod.natCast_eq_natCast_iff' q r 8).mp h1
    rcases hr with h3 | h3 <;> omega
  have hqm₀ : (m₀ : ℤ) ∣ (δ : ℤ) * q + 1 := by
    have h1 : (q : ZMod m₀) = w := (Prod.mk.injEq _ _ _ _).mp hsplit |>.2
    have h2 : (((δ : ℤ) * q + 1 : ℤ) : ZMod m₀) = 0 := by
      push_cast
      rw [h1, hw]
      have := ZMod.mul_inv_of_unit _ hδu
      ring_nf
      ring_nf at this
      linear_combination -this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ m₀).mp h2
  exact ⟨q, hqp, hqgt, hq8, hqm₀⟩

open scoped NumberTheorySymbols in

theorem jacobi_chain_odd {m : ℕ} (hm2 : m % 2 = 1)
    {δ q : ℕ} (hq4 : q % 4 = 1) (hqodd : q % 2 = 1)
    (hδcase : (δ = 1 ∧ m % 4 = 1) ∨ (δ = 2 ∧ m % 8 = 3))
    (hres : (m : ℤ) ∣ (δ : ℤ) * q + 1) :
    J((-(m : ℤ)) | q) = 1 := by
  have hoddm : Odd m := Nat.odd_iff.mpr hm2
  have hoddq : Odd q := Nat.odd_iff.mpr hqodd
  have h1 : J((-(m : ℤ)) | q) = J((-1 : ℤ) | q) * J(((m : ℕ) : ℤ) | q) := by
    rw [← jacobiSym.mul_left]
    congr 1
    ring
  have h2 : J((-1 : ℤ) | q) = 1 := by
    rw [jacobiSym.at_neg_one hoddq, ZMod.χ₄_nat_eq_if_mod_four]
    simp [hqodd, hq4]
  have h3 : J(((m : ℕ) : ℤ) | q) = J(((q : ℕ) : ℤ) | m) :=
    (jacobiSym.quadratic_reciprocity_one_mod_four hq4 hoddm).symm
  have hδm : Int.gcd ((δ : ℕ) : ℤ) m = 1 := by
    rcases hδcase with ⟨h6, _⟩ | ⟨h6, _⟩ <;> subst h6
    · simp
    · have hcop : Nat.Coprime 2 m :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
      simpa [Int.gcd] using hcop
  have h4 : J(((δ : ℕ) : ℤ) | m) * J(((q : ℕ) : ℤ) | m) = J((-1 : ℤ) | m) := by
    rw [← jacobiSym.mul_left]
    refine jacobiSym.mod_left' ?_
    have hmodeq : (((δ : ℕ) : ℤ) * ((q : ℕ) : ℤ)) ≡ (-1 : ℤ) [ZMOD (m : ℕ)] :=
      Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by
        rw [show (((δ : ℕ) : ℤ) * ((q : ℕ) : ℤ)) - (-1) = (δ : ℤ) * q + 1 by ring]
        exact hres))
    exact hmodeq
  have hsq := jacobiSym.sq_one hδm
  have h5 : J(((q : ℕ) : ℤ) | m)
      = J(((δ : ℕ) : ℤ) | m) * J((-1 : ℤ) | m) := by
    calc J(((q : ℕ) : ℤ) | m)
        = J(((δ : ℕ) : ℤ) | m) ^ 2 * J(((q : ℕ) : ℤ) | m) := by rw [hsq, one_mul]
      _ = J(((δ : ℕ) : ℤ) | m)
          * (J(((δ : ℕ) : ℤ) | m) * J(((q : ℕ) : ℤ) | m)) := by ring
      _ = J(((δ : ℕ) : ℤ) | m) * J((-1 : ℤ) | m) := by rw [h4]
  rcases hδcase with ⟨h6, hm4⟩ | ⟨h6, hm8⟩ <;> subst h6
  · have e1 : J(((1 : ℕ) : ℤ) | m) = 1 := by
      norm_num [jacobiSym.one_left]
    have e2 : J((-1 : ℤ) | m) = 1 := by
      rw [jacobiSym.at_neg_one hoddm, ZMod.χ₄_nat_eq_if_mod_four]
      simp [hm2, hm4]
    rw [h1, h2, h3, h5, e1, e2]
    norm_num
  · have hm4 : m % 4 = 3 := by omega
    have e1 : J(((2 : ℕ) : ℤ) | m) = -1 := by
      rw [show ((2 : ℕ) : ℤ) = (2 : ℤ) by norm_num,
        jacobiSym.at_two hoddm, ZMod.χ₈_nat_eq_if_mod_eight]
      simp [hm2, hm8]
    have e2 : J((-1 : ℤ) | m) = -1 := by
      rw [jacobiSym.at_neg_one hoddm, ZMod.χ₄_nat_eq_if_mod_four]
      simp [hm2, hm4]
    rw [h1, h2, h3, h5, e1, e2]
    norm_num

open scoped NumberTheorySymbols in

theorem jacobi_chain_even {m₀ : ℕ} (hm₀2 : m₀ % 2 = 1)
    {q : ℕ} (hqodd : q % 2 = 1) (hq4 : q % 4 = 1)
    (hcase : (m₀ % 4 = 1 ∧ q % 8 = 1) ∨ (m₀ % 4 = 3 ∧ q % 8 = 5))
    (hres : (m₀ : ℤ) ∣ (q : ℤ) + 1) :
    J((-((2 * m₀ : ℕ) : ℤ)) | q) = 1 := by
  have hoddm : Odd m₀ := Nat.odd_iff.mpr hm₀2
  have hoddq : Odd q := Nat.odd_iff.mpr hqodd
  have h1 : J((-((2 * m₀ : ℕ) : ℤ)) | q)
      = J((-1 : ℤ) | q) * (J((2 : ℤ) | q) * J(((m₀ : ℕ) : ℤ) | q)) := by
    rw [← jacobiSym.mul_left, ← jacobiSym.mul_left]
    congr 1
    push_cast
    ring
  have h2 : J((-1 : ℤ) | q) = 1 := by
    rw [jacobiSym.at_neg_one hoddq, ZMod.χ₄_nat_eq_if_mod_four]
    simp [hqodd, hq4]
  have h3 : J(((m₀ : ℕ) : ℤ) | q) = J(((q : ℕ) : ℤ) | m₀) :=
    (jacobiSym.quadratic_reciprocity_one_mod_four hq4 hoddm).symm
  have h4 : J(((q : ℕ) : ℤ) | m₀) = J((-1 : ℤ) | m₀) := by
    refine jacobiSym.mod_left' ?_
    have hmodeq : (((q : ℕ) : ℤ)) ≡ (-1 : ℤ) [ZMOD (m₀ : ℕ)] :=
      Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by
        rw [show (((q : ℕ) : ℤ)) - (-1) = (q : ℤ) + 1 by ring]
        exact hres))
    exact hmodeq
  rcases hcase with ⟨hm4, hq8⟩ | ⟨hm4, hq8⟩
  · have e1 : J((2 : ℤ) | q) = 1 := by
      rw [jacobiSym.at_two hoddq, ZMod.χ₈_nat_eq_if_mod_eight]
      simp [hqodd, hq8]
    have e2 : J((-1 : ℤ) | m₀) = 1 := by
      rw [jacobiSym.at_neg_one hoddm, ZMod.χ₄_nat_eq_if_mod_four]
      simp [hm₀2, hm4]
    rw [h1, h2, h3, h4, e1, e2]
    norm_num
  · have e1 : J((2 : ℤ) | q) = -1 := by
      rw [jacobiSym.at_two hoddq, ZMod.χ₈_nat_eq_if_mod_eight]
      simp [hqodd, hq8]
    have e2 : J((-1 : ℤ) | m₀) = -1 := by
      rw [jacobiSym.at_neg_one hoddm, ZMod.χ₄_nat_eq_if_mod_four]
      simp [hm₀2, hm4]
    rw [h1, h2, h3, h4, e1, e2]
    norm_num

theorem exists_b_h' {m q : ℕ} [Fact q.Prime] (hqodd : q % 2 = 1)
    {δ : ℕ} (hδ : δ = 1 ∨ δ = 2) (hmδ : δ = 2 → m % 2 = 1)
    (hsq : IsSquare (-((m : ℕ) : ZMod q))) :
    ∃ b h' : ℤ, ((δ : ℤ) * q) * h' = b ^ 2 + (m : ℤ) := by
  obtain ⟨r, hr⟩ := hsq
  have hb₀ : (q : ℤ) ∣ ((r.val : ℤ)) ^ 2 + m := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp ?_
    push_cast at hr ⊢
    rw [ZMod.natCast_rightInverse r]
    linear_combination -hr
  rcases hδ with h1 | h1 <;> subst h1
  · obtain ⟨h', hh'⟩ := hb₀
    refine ⟨(r.val : ℤ), h', ?_⟩
    push_cast
    linarith [hh']
  · have hm2 := hmδ rfl
    set b : ℤ := if 2 ∣ (r.val : ℤ) then (r.val : ℤ) + q else (r.val : ℤ) with hb
    have hqb : (q : ℤ) ∣ b ^ 2 + m := by
      rw [hb]
      split_ifs with h
      · have hexp : ((r.val : ℤ) + q) ^ 2 + m
            = ((r.val : ℤ) ^ 2 + m) + (q : ℤ) * (2 * r.val + q) := by ring
        rw [hexp]
        exact dvd_add hb₀ (Dvd.intro _ rfl)
      · exact hb₀
    have hbodd : ¬ (2 : ℤ) ∣ b := by
      rw [hb]
      split_ifs with h
      · intro h2
        omega
      · exact h
    have h2b : (2 : ℤ) ∣ b ^ 2 + m := by
      obtain ⟨k, hk⟩ : ∃ k, b = 2 * k + 1 := ⟨(b - 1) / 2, by omega⟩
      obtain ⟨j, hj⟩ : ∃ j, (m : ℤ) = 2 * j + 1 := ⟨((m : ℤ) - 1) / 2, by omega⟩
      exact ⟨2 * k ^ 2 + 2 * k + j + 1, by rw [hk, hj]; ring⟩
    have hcop : IsCoprime (2 : ℤ) (q : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have hc : Nat.Coprime 2 q :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
      simpa [Int.gcd] using hc
    obtain ⟨h', hh'⟩ := hcop.mul_dvd h2b hqb
    refine ⟨b, h', ?_⟩
    push_cast
    linarith [hh']

theorem exists_ankeny_data {m : ℕ} (hm : 0 < m)
    (hmod : m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 6) :
    ∃ (q : ℕ) (δ c b h' t : ℤ),
      q.Prime ∧ q % 4 = 1 ∧ (δ = 1 ∨ δ = 2) ∧ c = δ * q ∧
      c * h' = b ^ 2 + (m : ℤ) ∧ ((m : ℤ) ∣ c * t ^ 2 + 1) ∧
      IsCoprime c (m : ℤ) ∧
      (∀ p : ℕ, p.Prime → p ∣ m → p ≠ 2 → IsSquare ((-c : ℤ) : ZMod p)) := by
  by_cases hpar : m % 2 = 1
  · -- odd case
    set δN : ℕ := if m % 8 = 3 then 2 else 1 with hδN
    have hδN12 : δN = 1 ∨ δN = 2 := by rw [hδN]; split_ifs <;> simp
    obtain ⟨q, hqp, hqgt, hq8, hres⟩ :=
      exists_prime_delta m hm (by omega) δN hδN12 1 (Or.inl rfl) m
    haveI : Fact q.Prime := ⟨hqp⟩
    have hq4 : q % 4 = 1 := by omega
    have hqodd : q % 2 = 1 := by omega
    have hδcase : (δN = 1 ∧ m % 4 = 1) ∨ (δN = 2 ∧ m % 8 = 3) := by
      rw [hδN]
      split_ifs with h
      · exact Or.inr ⟨rfl, h⟩
      · exact Or.inl ⟨rfl, by omega⟩
    have hJ := jacobi_chain_odd hpar hq4 hqodd hδcase hres
    have hsq : IsSquare (-((m : ℕ) : ZMod q)) := by
      have hs := ZMod.isSquare_of_jacobiSym_eq_one hJ
      push_cast at hs
      exact hs
    obtain ⟨b, h', hch⟩ := exists_b_h' hqodd hδN12 (fun _ => hpar) hsq
    have hqm : Nat.Coprime q m := by
      have hd1 : (Nat.gcd q m : ℤ) ∣ (δN : ℤ) * q + 1 :=
        dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right q m)) hres
      have hd2 : (Nat.gcd q m : ℤ) ∣ (δN : ℤ) * q :=
        Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left q m)) _
      have hd3 : (Nat.gcd q m : ℤ) ∣ 1 := by
        have hsub := dvd_sub hd1 hd2
        simpa using hsub
      have hd4 : (Nat.gcd q m : ℤ) = 1 :=
        Int.eq_one_of_dvd_one (by positivity) hd3
      exact_mod_cast hd4
    have hδm : Nat.Coprime δN m := by
      rcases hδN12 with h1 | h1 <;> rw [h1]
      · exact Nat.coprime_one_left m
      · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
    have hcm : IsCoprime ((δN : ℤ) * q) ((m : ℕ) : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have hcast : ((δN : ℤ) * q) = (((δN * q : ℕ)) : ℤ) := by push_cast; ring
      rw [hcast, Int.gcd_natCast_natCast]
      exact Nat.Coprime.mul_left hδm hqm
    refine ⟨q, (δN : ℤ), (δN : ℤ) * q, b, h', 1, hqp, hq4, ?_, rfl, hch, ?_, hcm, ?_⟩
    · rcases hδN12 with h1 | h1
      · exact Or.inl (by rw [h1]; norm_num)
      · exact Or.inr (by rw [h1]; norm_num)
    · rw [one_pow, mul_one]
      exact hres
    · intro p hpp hpm hp2
      have hpd : ((p : ℕ) : ℤ) ∣ (δN : ℤ) * q + 1 :=
        dvd_trans (Int.natCast_dvd_natCast.mpr hpm) hres
      have h0 : (((δN : ℤ) * q + 1 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpd
      refine ⟨1, ?_⟩
      push_cast at h0 ⊢
      linear_combination -h0
  · -- even case
    have hm₀odd : (m / 2) % 2 = 1 := by omega
    have hm₀pos : 0 < m / 2 := by omega
    have hm2 : m = 2 * (m / 2) := by omega
    set r : ℕ := if m % 8 = 2 then 1 else 5 with hrdef
    have hr15 : r = 1 ∨ r = 5 := by rw [hrdef]; split_ifs <;> simp
    obtain ⟨q, hqp, hqgt, hq8, hres⟩ :=
      exists_prime_delta (m / 2) hm₀pos (by omega) 1 (Or.inl rfl) r hr15 m
    haveI : Fact q.Prime := ⟨hqp⟩
    have hq4 : q % 4 = 1 := by rcases hr15 with h | h <;> omega
    have hqodd : q % 2 = 1 := by rcases hr15 with h | h <;> omega
    have hres' : ((m / 2 : ℕ) : ℤ) ∣ (q : ℤ) + 1 := by
      have hres2 := hres
      rw [Nat.cast_one, one_mul] at hres2
      exact hres2
    have hcase : ((m / 2) % 4 = 1 ∧ q % 8 = 1) ∨ ((m / 2) % 4 = 3 ∧ q % 8 = 5) := by
      rw [hrdef] at hq8
      split_ifs at hq8 with h
      · exact Or.inl ⟨by omega, hq8⟩
      · exact Or.inr ⟨by omega, hq8⟩
    have hJ := jacobi_chain_even hm₀odd hqodd hq4 hcase hres'
    have hJm : jacobiSym (-(m : ℤ)) q = 1 := by
      have hmcast : ((m : ℕ) : ℤ) = ((2 * (m / 2) : ℕ) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hm2
      rw [hmcast]
      exact hJ
    have hsq : IsSquare (-((m : ℕ) : ZMod q)) := by
      have hs := ZMod.isSquare_of_jacobiSym_eq_one hJm
      push_cast at hs
      exact hs
    obtain ⟨b, h', hch⟩ :=
      exists_b_h' hqodd (Or.inl rfl) (fun h => absurd h (by norm_num)) hsq
    have hmdvd : (m : ℤ) ∣ (q : ℤ) + 1 := by
      have h2d : (2 : ℤ) ∣ (q : ℤ) + 1 := by omega
      have hcop2 : IsCoprime (2 : ℤ) ((m / 2 : ℕ) : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one,
          show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, Int.gcd_natCast_natCast]
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
      have hmul := hcop2.mul_dvd h2d hres'
      have hmcast : ((m : ℕ) : ℤ) = 2 * ((m / 2 : ℕ) : ℤ) := by
        push_cast
        omega
      rw [hmcast]
      exact hmul
    have hqm : Nat.Coprime q m := by
      have hd1 : (Nat.gcd q m : ℤ) ∣ (q : ℤ) + 1 :=
        dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right q m)) hmdvd
      have hd2 : (Nat.gcd q m : ℤ) ∣ (q : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left q m)
      have hd3 : (Nat.gcd q m : ℤ) ∣ 1 := by
        have hsub := dvd_sub hd1 hd2
        simpa using hsub
      have hd4 : (Nat.gcd q m : ℤ) = 1 :=
        Int.eq_one_of_dvd_one (by positivity) hd3
      exact_mod_cast hd4
    have hcm : IsCoprime ((1 : ℤ) * q) ((m : ℕ) : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, one_mul, Int.gcd_natCast_natCast]
      exact hqm
    refine ⟨q, 1, (1 : ℤ) * q, b, h', 1, hqp, hq4, Or.inl rfl, rfl, ?_, ?_, hcm, ?_⟩
    · have hch2 := hch
      rw [Nat.cast_one] at hch2
      exact hch2
    · rw [one_pow, mul_one, one_mul]
      exact hmdvd
    · intro p hpp hpm hp2
      have hpm₀ : p ∣ m / 2 := by
        rcases (Nat.Prime.dvd_mul hpp).mp (hm2 ▸ hpm) with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h) hp2
        · exact h
      have hpd : ((p : ℕ) : ℤ) ∣ (q : ℤ) + 1 :=
        dvd_trans (Int.natCast_dvd_natCast.mpr hpm₀) hres'
      have h0 : (((q : ℤ) + 1 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpd
      refine ⟨1, ?_⟩
      push_cast at h0 ⊢
      linear_combination -h0

def MinkowskiPoint : Prop :=
  ∀ m c b h' t : ℤ, 0 < m → 0 < c → c * h' = b ^ 2 + m →
    ∃ x y z : ℤ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ formQ m c b h' t x y z < 2 * m

theorem isSum3Sq_of_minkowskiPoint (W3 : MinkowskiPoint) :
    ∀ n : ℕ, 0 < n → (∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7)) →
      ThreeSquares.IsSum3Sq (n : ℤ) := by
  refine ThreeSquares.isSum3Sq_of_core ?_
  intro m hsf hmod
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; omega)
  obtain ⟨q, δ, c, b, h', t, hqp, hq4, hδ, hcδ, hch, hmt, hcm, hC1⟩ :=
    exists_ankeny_data hm hmod
  have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hqp.pos
  have hc : 0 < c := by
    rcases hδ with h1 | h1 <;> rw [hcδ, h1] <;> linarith
  obtain ⟨x, y, z, hne, hlt⟩ :=
    W3 ((m : ℕ) : ℤ) c b h' t (by exact_mod_cast hm) hc hch
  exact core_of_minkowski_point hm hsf hqp hq4 hδ hcδ hch hmt hcm hC1 hne hlt
end Ankeny

open Matrix
namespace Ankeny


private lemma gamma_five_half : Real.Gamma ((3 : ℝ) / 2 + 1) = 3 / 4 * Real.sqrt Real.pi := by
  rw [Real.Gamma_add_one (by norm_num), show ((3 : ℝ) / 2) = 1 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  ring

private lemma sqrt_pi_pos : 0 < Real.sqrt Real.pi :=
  Real.sqrt_pos.mpr Real.pi_pos

private lemma volume_const_gt {m : ℝ} (hm : 0 < m) :
    8 * (m * Real.sqrt m)
      < Real.sqrt (2 * m) ^ 3
        * (Real.sqrt Real.pi ^ 3 / Real.Gamma ((3 : ℝ) / 2 + 1)) := by
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsπ := sqrt_pi_pos
  have h2m : Real.sqrt (2 * m) = Real.sqrt 2 * Real.sqrt m :=
    Real.sqrt_mul (by norm_num) m
  have hmm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm.le
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hππ : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hs21 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hgam : Real.sqrt Real.pi ^ 3 / (3 / 4 * Real.sqrt Real.pi)
      = 4 / 3 * Real.pi := by
    rw [div_eq_iff (by positivity)]
    linear_combination Real.sqrt Real.pi * hππ
  have hcube : (Real.sqrt 2 * Real.sqrt m) ^ 3
      = 2 * Real.sqrt 2 * (m * Real.sqrt m) := by
    linear_combination (Real.sqrt 2 * Real.sqrt m ^ 3) * h22
      + (2 * Real.sqrt 2 * Real.sqrt m) * hmm
  rw [gamma_five_half, h2m, hgam, hcube,
    show 2 * Real.sqrt 2 * (m * Real.sqrt m) * (4 / 3 * Real.pi)
      = 2 * Real.sqrt 2 * (4 / 3 * Real.pi) * (m * Real.sqrt m) by ring]
  refine mul_lt_mul_of_pos_right ?_ (mul_pos hm hsm)
  nlinarith [hπ3, hs21, hs2]

private noncomputable def matM (m c b t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![t * c, t * b, m;
     Real.sqrt c, b / Real.sqrt c, 0;
     0, Real.sqrt (m / c), 0]

private lemma matM_entries (m c b t : ℝ) (w : Fin 3 → ℝ) :
    (matM m c b t).mulVec w 0 = t * c * w 0 + t * b * w 1 + m * w 2
    ∧ (matM m c b t).mulVec w 1
        = Real.sqrt c * w 0 + b / Real.sqrt c * w 1
    ∧ (matM m c b t).mulVec w 2 = Real.sqrt (m / c) * w 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [matM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private lemma matM_det {m c b t : ℝ} (hc : 0 < c) :
    (matM m c b t).det = m * Real.sqrt m := by
  have h1 : Real.sqrt c * Real.sqrt (m / c) = Real.sqrt m := by
    rw [← Real.sqrt_mul hc.le, mul_div_cancel₀ _ hc.ne']
  rw [matM, Matrix.det_fin_three]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_fin_const,
    Matrix.cons_val_fin_one, Matrix.of_apply]
  linear_combination m * h1

private lemma matM_normsq {m c b h' t : ℝ} (hm : 0 < m) (hc : 0 < c)
    (hch : c * h' = b ^ 2 + m) (w : Fin 3 → ℝ) :
    ((matM m c b t).mulVec w 0) ^ 2 + ((matM m c b t).mulVec w 1) ^ 2
      + ((matM m c b t).mulVec w 2) ^ 2
      = (t * (c * w 0 + b * w 1) + m * w 2) ^ 2
        + (c * w 0 ^ 2 + 2 * b * w 0 * w 1 + h' * w 1 ^ 2) := by
  obtain ⟨e0, e1, e2⟩ := matM_entries m c b t w
  rw [e0, e1, e2]
  set sc : ℝ := Real.sqrt c with hscdef
  set u : ℝ := Real.sqrt (m / c) with hudef
  have hscpos : 0 < sc := Real.sqrt_pos.mpr hc
  have hscne : sc ≠ 0 := hscpos.ne'
  have hsc : sc * sc = c := Real.mul_self_sqrt hc.le
  have hu : u * u * c = m := by
    rw [hudef, Real.mul_self_sqrt (by positivity)]
    exact div_mul_cancel₀ m hc.ne'
  have hbs : b / sc = b * sc / c := by
    rw [div_eq_div_iff hscne hc.ne']
    linear_combination (-b) * hsc
  rw [hbs]
  field_simp
  ring_nf
  linear_combination (w 1 ^ 2 * c) * hu + ((c * w 0 + b * w 1) ^ 2) * hsc
    + (-(c * w 1 ^ 2)) * hch

open MeasureTheory in

private theorem exists_int_point {m c b h' t : ℝ} (hm : 0 < m) (hc : 0 < c)
    (hch : c * h' = b ^ 2 + m) :
    ∃ n : Fin 3 → ℤ, ¬(n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0) ∧
      (t * (c * (n 0 : ℝ) + b * (n 1 : ℝ)) + m * (n 2 : ℝ)) ^ 2
        + (c * (n 0 : ℝ) ^ 2 + 2 * b * (n 0 : ℝ) * (n 1 : ℝ)
            + h' * (n 1 : ℝ) ^ 2) < 2 * m := by
  classical
  have hsqm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have h2m : (0 : ℝ) < 2 * m := by linarith
  have hrpos : (0 : ℝ) < Real.sqrt (2 * m) := Real.sqrt_pos.mpr h2m
  have hdet : LinearMap.det (Matrix.toLin' (matM m c b t)) = m * Real.sqrt m := by
    rw [LinearMap.det_toLin']
    exact matM_det hc
  have hdetpos : (0 : ℝ) < m * Real.sqrt m := mul_pos hm hsqm
  have hdetne : LinearMap.det (Matrix.toLin' (matM m c b t)) ≠ 0 := by
    rw [hdet]
    exact hdetpos.ne'
  have hs₀ball : {v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 < 2 * m}
      = (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) ⁻¹'
          Metric.ball 0 (Real.sqrt (2 * m)) := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    rw [EuclideanSpace.norm_eq]
    have hcoords : ∀ i : Fin 3,
        ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3)) i‖ = |v i| := fun i => rfl
    simp only [hcoords, Fin.sum_univ_three, sq_abs]
    rw [Real.sqrt_lt_sqrt_iff (by positivity)]
  have hs₀vol : volume {v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 < 2 * m}
      = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))) := by
    rw [hs₀ball]
    exact (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
      measurableSet_ball.nullMeasurableSet
  have hs₀conv : Convex ℝ {v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 < 2 * m} := by
    rw [hs₀ball]
    exact Convex.linear_preimage
      (f := (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap)
      (convex_ball 0 _)
  set S : Set (Fin 3 → ℝ) :=
    ⇑(Matrix.toLin' (matM m c b t)) ⁻¹'
      {v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 < 2 * m} with hSdef
  have hSconv : Convex ℝ S :=
    Convex.linear_preimage hs₀conv (Matrix.toLin' (matM m c b t))
  have hSsymm : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    simp only [hSdef, Set.mem_preimage, map_neg, Set.mem_setOf_eq, Pi.neg_apply,
      neg_sq] at hx ⊢
    exact hx
  have hSvol : volume S
      = ENNReal.ofReal ((m * Real.sqrt m)⁻¹)
        * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))) := by
    rw [hSdef, Measure.addHaar_preimage_linearMap volume hdetne, hdet,
      hs₀vol, abs_of_pos (inv_pos.mpr hdetpos)]
  have hfund := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin 3)) volume
  have hvolF : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))) = 1 := by
    rw [ZSpan.volume_fundamentalDomain]
    have hone : (Matrix.of ⇑(Pi.basisFun ℝ (Fin 3)))
        = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
      ext i j
      simp [Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [hone, Matrix.det_one]
    simp
  have hballvol : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3))
        (Real.sqrt (2 * m)))
      = ENNReal.ofReal (Real.sqrt (2 * m) ^ 3
          * (Real.sqrt Real.pi ^ 3 / Real.Gamma ((3 : ℝ) / 2 + 1))) := by
    rw [EuclideanSpace.volume_ball]
    rw [← ENNReal.ofReal_pow hrpos.le, ← ENNReal.ofReal_mul (by positivity)]
    norm_num [Fintype.card_fin]
  have hineq : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3)))
      * 2 ^ Module.finrank ℝ (Fin 3 → ℝ) < volume S := by
    rw [hvolF, one_mul, hSvol, hballvol, ← ENNReal.ofReal_mul (by positivity)]
    have hrank : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by
      simp
    rw [hrank, show ((2 : ENNReal) ^ 3) = ENNReal.ofReal 8 by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ENNReal.ofReal_pow (by norm_num)]
      norm_num]
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have hkey := volume_const_gt hm
    rw [lt_inv_mul_iff₀ hdetpos]
    linarith
  haveI : Countable
      ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin 3)))).toAddSubgroup :=
    (inferInstance :
      Countable ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin 3)))))
  obtain ⟨x, hx0, hxS⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      hfund hSsymm hSconv hineq
  have hxmem : (x : Fin 3 → ℝ)
      ∈ Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin 3))) := by
    have := x.2
    rwa [Submodule.mem_toAddSubgroup] at this
  obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hxmem
  have hxfun : ∀ j, (x : Fin 3 → ℝ) j = (n j : ℝ) := by
    intro j
    rw [← hn]
    simp [Pi.basisFun_apply, Pi.single_apply, zsmul_eq_mul]
  refine ⟨n, ?_, ?_⟩
  · rintro ⟨h0, h1, h2⟩
    apply hx0
    have hcoe : (x : Fin 3 → ℝ) = 0 := by
      funext j
      rw [hxfun j]
      fin_cases j <;> simp [h0, h1, h2]
    exact (ZeroMemClass.coe_eq_zero).mp hcoe
  · have hxS' := hxS
    rw [hSdef, Set.mem_preimage, Matrix.toLin'_apply, Set.mem_setOf_eq] at hxS'
    rw [matM_normsq hm hc hch] at hxS'
    rw [hxfun 0, hxfun 1, hxfun 2] at hxS'
    exact hxS'

theorem minkowskiPoint_holds : MinkowskiPoint := by
  intro m c b h' t hm hc hch
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hchR : (c : ℝ) * (h' : ℝ) = (b : ℝ) ^ 2 + (m : ℝ) := by exact_mod_cast hch
  obtain ⟨n, hn0, hnlt⟩ := exists_int_point (t := (t : ℝ)) hmR hcR hchR
  refine ⟨n 0, n 1, n 2, hn0, ?_⟩
  have hcast : ((formQ m c b h' t (n 0) (n 1) (n 2) : ℤ) : ℝ)
      < (((2 : ℤ) * m : ℤ) : ℝ) := by
    unfold formQ formR formPsi
    push_cast
    ring_nf
    ring_nf at hnlt
    linarith
  exact_mod_cast hcast

theorem sum_three_squares (n : ℕ) (hn : 0 < n)
    (hform : ∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7)) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = (n : ℤ) :=
  isSum3Sq_of_minkowskiPoint minkowskiPoint_holds n hn hform
end Ankeny
theorem natural940 (n : ℕ) (h : ∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7)) :
    ∃ x y z : ℕ, n = x^2 + y^2 + z^2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0,0,0,by decide⟩
  obtain ⟨x,y,z,he⟩ := Ankeny.sum_three_squares n hn h
  refine ⟨x.natAbs,y.natAbs,z.natAbs,?_⟩
  zify [Int.natCast_natAbs, sq_abs]
  exact he.symm


-- Three-square proof above from open-math-agents #4995. The following
-- centre selection, residue arguments, and interval certificates are for Sun's conjecture.
-- Credit: @Iraeeee
namespace SignedPolygonal

/-- Choose a centre just below the square root. The first argument of the
certificate is the square root modulo 72. -/
private lemma chooseCentre (N : ℕ) (hN : 10000 ≤ N) (good : ℕ → ℕ → Prop)
    (cert : ∀ k : Fin 72, ∃ d : Fin 12,
      let s := (k.val+72-d.val)%72
      good s ((N%72+5184-s^2)%72)) :
    ∃ s r : ℕ, s^2+r=N ∧ 3*r<s^2 ∧ good (s%72) (r%72) := by
  let k := N.sqrt
  have hk : 100 ≤ k := Nat.le_sqrt.mpr hN
  obtain ⟨d,hd⟩ := cert ⟨k%72,Nat.mod_lt _ (by decide)⟩
  let s := k-d.val
  let r := N-s^2
  have hdk := d.isLt
  have hs : s+d.val=k := by dsimp [s]; omega
  have hlow : 89 ≤ s := by omega
  have hs2 : s^2 ≤ N := (Nat.pow_le_pow_left (show s≤k by omega) 2).trans (Nat.sqrt_le' N)
  have he : s^2+r=N := by dsimp [r]; omega
  have hbig : N < (k+1)^2 := Nat.lt_succ_sqrt' N
  have hk' : k+1 ≤ s+12 := by omega
  have hb := hbig.trans_le (Nat.pow_le_pow_left hk' 2)
  have hpos : 3*r < s^2 := by nlinarith only [hb,he,Nat.mul_le_mul_right s hlow,hlow]
  have hmod : s%72=(k%72+72-d.val)%72 := by omega
  change good ((k%72+72-d.val)%72) ((N%72+5184-((k%72+72-d.val)%72)^2)%72) at hd
  rw [← hmod] at hd
  have hr' : (s%72)^2%72+r%72 ≡ N [MOD 72] := by
    calc
      _ ≡ (s%72)^2 + r [MOD 72] := (Nat.mod_modEq _ _).add (Nat.mod_modEq _ _)
      _ ≡ s^2+r [MOD 72] := ((Nat.mod_modEq s 72).pow 2).add_right r
      _ = N := he
  have hr'' : ((s%72)^2%72+r%72)%72 = N%72 := hr'
  have hs' : (s%72)^2 ≤ 5184 := Nat.pow_le_pow_left (Nat.le_of_lt (Nat.mod_lt s (by decide))) 2
  have hrem : r%72 = (N%72+5184-(s%72)^2)%72 := by omega
  exact ⟨s,r,he,hpos,hrem ▸ hd⟩

private lemma avoid_three_obstruction {r : ℕ} (h4 : r%4 ≠ 0) (h8 : r%8 ≠ 7) :
    ∀ a b : ℕ, r ≠ 4^a*(8*b+7) := by
  rintro (_|a) b he
  · simp at he; omega
  · rw [pow_succ] at he
    have h : 4 ∣ r := ⟨4^a*(8*b+7), by rw [he]; ring⟩
    omega

private lemma positive_coordinates (s a b c : ℤ) (hs : 0 ≤ s)
    (hb : 3*(a^2+b^2+c^2) < s^2) :
    0 < s+a+b+c ∧ 0 < s+a-b-c ∧ 0 < s-a+b-c ∧ 0 < s-a-b+c := by
  have aux (x y z : ℤ) (he : 3*(x^2+y^2+z^2) < s^2) : 0 < s+x+y+z := by
    by_contra! h
    have hle : s ≤ -(x+y+z) := by omega
    have hh := mul_self_le_mul_self hs hle
    nlinarith only [hh,he,sq_nonneg (x-y),sq_nonneg (x-z),sq_nonneg (y-z)]
  exact ⟨aux a b c hb,by simpa [sub_eq_add_neg] using aux a (-b) (-c) (by simpa using hb),
    by simpa [sub_eq_add_neg] using aux (-a) b (-c) (by simpa using hb),
    by simpa [sub_eq_add_neg] using aux (-a) (-b) c (by simpa using hb)⟩

private def pent (x : ℕ) := x*(3*x-1)/2
private def secondPent (x : ℕ) := x*(3*x+1)/2

private lemma twice_half_pent (x : ℕ) (b : Bool) :
    (if b then x*(3*x+1) else x*(3*x-1)) % 2 = 0 := by
  have h : (x*(3*x+1))%2 = 0 := by
    rw [Nat.mul_mod, Nat.add_mod, Nat.mul_mod 3]
    rcases Nat.mod_two_eq_zero_or_one x with he|he <;> rw [he] <;> decide
  cases b
  · by_cases hx : x = 0
    · simp [hx]
    · have hh : x*(3*x-1)+2*x=x*(3*x+1) := by
        rw [show 3*x+1=(3*x-1)+2 by omega,Nat.mul_add]; ring
      simp only [Bool.false_eq_true,if_false]; omega
  · simpa using h

/-- Convert a positive coordinate of the required residue type into an index. -/
private lemma posPent {u : ℤ} (hu : 0 < u) (hr : u%6=5) :
    ∃ x : ℕ, 24*(pent x : ℤ)+1=u^2 := by
  let x := ((u+1)/6).toNat
  have hx : (x:ℤ)= (u+1)/6 := Int.toNat_of_nonneg (by omega)
  have he : 6*(x:ℤ)-1=u := by omega
  have h0 : 1 ≤ x := by omega
  have ht := twice_half_pent x false
  have hdiv : 2*pent x = x*(3*x-1) := by simp only [Bool.false_eq_true,if_false] at ht; dsimp [pent]; omega
  have h' : 2*(pent x : ℤ)=(x:ℤ)*(3*(x:ℤ)-1) := by
    have hle : 1 ≤ 3*x := by omega
    exact_mod_cast (show (2*pent x : ℕ) = x*(3*x-1) from hdiv)
  refine ⟨x,?_⟩
  rw [← he]
  nlinarith only [h']

private lemma posSecond {u : ℤ} (hu : 0 < u) (hr : u%6=1) :
    ∃ x : ℕ, 24*(secondPent x : ℤ)+1=u^2 := by
  let x := ((u-1)/6).toNat
  have hx : (x:ℤ)= (u-1)/6 := Int.toNat_of_nonneg (by omega)
  have he : 6*(x:ℤ)+1=u := by omega
  have ht := twice_half_pent x true
  have hdiv : 2*secondPent x = x*(3*x+1) := by simp only [if_true] at ht; dsimp [secondPent]; omega
  have h' : 2*(secondPent x : ℤ)=(x:ℤ)*(3*(x:ℤ)+1) := by exact_mod_cast hdiv
  refine ⟨x,?_⟩
  rw [← he]
  nlinarith only [h']

private lemma square_mod_two (x : ℤ) : x^2%2=x%2 := by
  rw [pow_two,Int.mul_emod]
  rcases Int.emod_two_eq_zero_or_one x with h|h <;> rw [h] <;> decide

private lemma odd_hadamard (s a b c : ℤ) (hn : (s^2+a^2+b^2+c^2)%2=1) :
    (s+a+b+c)%2=1 ∧ (s+a-b-c)%2=1 ∧ (s-a+b-c)%2=1 ∧ (s-a-b+c)%2=1 := by
  have h1 := square_mod_two s
  have h2 := square_mod_two a
  have h3 := square_mod_two b
  have h4 := square_mod_two c
  omega

private lemma nonzero_three {r a b c : ℕ} (he : r = a^2+b^2+c^2)
    (h3 : r%3=0) (h9 : r%9≠0) : a%3≠0 ∧ b%3≠0 ∧ c%3≠0 := by
  have sq (x : ℕ) : x^2%3 = if x%3=0 then 0 else 1 := by
    rw [Nat.pow_mod]
    have hh := Nat.mod_lt x (by decide : 0<3)
    interval_cases x%3 <;> decide
  have ha := sq a; have hb := sq b; have hc := sq c
  by_contra! H
  have hzero : a%3=0 ∧ b%3=0 ∧ c%3=0 := by
    split_ifs at ha hb hc <;> omega
  obtain ⟨a',rfl⟩ := Nat.dvd_of_mod_eq_zero hzero.1
  obtain ⟨b',rfl⟩ := Nat.dvd_of_mod_eq_zero hzero.2.1
  obtain ⟨c',rfl⟩ := Nat.dvd_of_mod_eq_zero hzero.2.2
  have hh : 9 ∣ r := ⟨a'^2+b'^2+c'^2,by rw [he]; ring⟩
  omega

private lemma choose_sign (a : ℕ) (h : a%3≠0) :
    ∃ u : ℤ, u^2=(a:ℤ)^2 ∧ u%3=2 := by
  by_cases h2 : (a:ℤ)%3=2
  · exact ⟨a,rfl,h2⟩
  · exact ⟨-(a:ℤ),by ring,by omega⟩

private theorem one_plus_large (three : ∀ r : ℕ, (∀ i j : ℕ, r ≠ 4^i*(8*j+7)) →
    ∃ a b c : ℕ, r=a^2+b^2+c^2) (n : ℕ) (hn : 5000 ≤ n) :
    ∃ w x y z : ℕ, n = secondPent w + pent x + pent y + pent z := by
  let N := 6*n+1
  let good := fun s r : ℕ => s%3=1 ∧ r%3=0 ∧ r%9≠0 ∧ r%4≠0 ∧ r%8≠7
  have table : ∀ i : Fin 12, ∀ k : Fin 72, ∃ d : Fin 12,
      let s := (k.val+72-d.val)%72
      good s (((6*i.val+1)%72+5184-s^2)%72) := by decide
  have modN : N%72 = (6*(n%12)+1)%72 := by dsimp [N]; omega
  have cert := table ⟨n%12,Nat.mod_lt _ (by decide)⟩
  simp only at cert
  rw [← modN] at cert
  obtain ⟨s,r,hs,hr,hg⟩ := chooseCentre N (by dsimp [N]; omega) good cert
  change _ ∧ _ ∧ _ ∧ _ ∧ _ at hg
  dsimp [good] at hg
  obtain ⟨hs3,hr3,hr9,hr4,hr8⟩ := hg
  obtain ⟨a,b,c,habc⟩ := three r (avoid_three_obstruction (by omega) (by omega))
  obtain ⟨ha,hb,hc⟩ := nonzero_three habc (by omega) (by omega)
  obtain ⟨u,hu,hu3⟩ := choose_sign a ha
  obtain ⟨v,hv,hv3⟩ := choose_sign b hb
  obtain ⟨t,ht,ht3⟩ := choose_sign c hc
  have hnat : s^2 + (a^2+b^2+c^2) = 6*n+1 := habc ▸ hs
  have hid : (s:ℤ)^2+u^2+v^2+t^2=6*(n:ℤ)+1 := by
    rw [hu,hv,ht]; exact_mod_cast (by omega : s^2+a^2+b^2+c^2=6*n+1)
  have hbnd : 3*(u^2+v^2+t^2)<(s:ℤ)^2 := by
    rw [hu,hv,ht]; exact_mod_cast (habc ▸ hr : 3*(a^2+b^2+c^2)<s^2)
  obtain ⟨h0,h1,h2,h3⟩ := positive_coordinates s u v t (by positivity) hbnd
  obtain ⟨o0,o1,o2,o3⟩ := odd_hadamard s u v t (by rw [hid]; omega)
  obtain ⟨w,hw⟩ := posSecond h0 (by omega)
  obtain ⟨x,hx⟩ := posPent h1 (by omega)
  obtain ⟨y,hy⟩ := posPent h2 (by omega)
  obtain ⟨z,hz⟩ := posPent h3 (by omega)
  refine ⟨w,x,y,z,?_⟩
  have he : (n:ℤ) = secondPent w + (pent x:ℤ) + pent y + pent z := by
    linarith only [hw,hx,hy,hz,hid]
  exact_mod_cast he

private def wave (b : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => wave b f k ||| (b <<< f k)

private lemma wave_spec (b : ℕ) (f : ℕ → ℕ) (k n : ℕ) (h : (wave b f k).testBit n=true) :
    ∃ i < k, f i ≤ n ∧ b.testBit (n-f i)=true := by
  induction k with
  | zero => simp [wave] at h
  | succ k ih =>
    simp only [wave,Nat.testBit_or,Nat.testBit_shiftLeft,Bool.or_eq_true,Bool.and_eq_true,
      decide_eq_true_eq] at h
    rcases h with h|⟨hl,hb⟩
    · obtain ⟨i,hi,hle,hh⟩ := ih h
      exact ⟨i,by omega,hle,hh⟩
    · exact ⟨k,by omega,hl,hb⟩

private def fourWaves (a b c d : ℕ → ℕ) := wave (wave (wave (wave 1 d 72) c 72) b 72) a 72

set_option maxRecDepth 8192 in
private theorem finite_interval (a b c d : ℕ → ℕ)
    {K : ℕ} (mask : fourWaves a b c d % (1 <<< K) = (1 <<< K)-1)
    (n : ℕ) (hn : n < K) : ∃ w x y z : ℕ, n=a w+b x+c y+d z := by
  have hm : fourWaves a b c d % 2^K = 2^K-1 := by simpa [Nat.shiftLeft_eq] using mask
  have hb := congrArg (fun s : ℕ => s.testBit n) hm
  simp only [Nat.testBit_mod_two_pow,Nat.testBit_two_pow_sub_one,decide_eq_true hn,Bool.true_and] at hb
  obtain ⟨w,_,hw,hr⟩ := wave_spec _ _ _ _ hb
  obtain ⟨x,_,hx,hr⟩ := wave_spec _ _ _ _ hr
  obtain ⟨y,_,hy,hr⟩ := wave_spec _ _ _ _ hr
  obtain ⟨z,_,hz,hr⟩ := wave_spec _ _ _ _ hr
  let q := n-a w-b x-c y-d z
  have hq : q=0 := by
    by_contra! hh
    have hp : 1 < (2:ℕ)^q := Nat.one_lt_pow (by omega) (by decide)
    exact Bool.false_ne_true ((Nat.testBit_lt_two_pow hp).symm.trans hr)
  exact ⟨w,x,y,z,by dsimp [q] at hq; omega⟩

set_option maxRecDepth 8192 in
private theorem small_one (n : ℕ) (hn : n < 5000) :
    ∃ w x y z : ℕ, n=secondPent w+pent x+pent y+pent z :=
  finite_interval secondPent pent pent pent (by decide) n hn

end SignedPolygonal

theorem OMA.solution : type_of% @OMA.S_oeis_a256132.main := by
  intro n
  by_cases hn : n < 5000
  · exact SignedPolygonal.small_one n hn
  · exact SignedPolygonal.one_plus_large natural940 n (by omega)
