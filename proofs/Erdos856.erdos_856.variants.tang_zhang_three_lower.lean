import FormalConjectures.ErdosProblems.«856»
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Fin.Tuple.Basic

/-! The Tang–Zhang harmonic lower bound for three-term LCM patterns via a two-port sunflower construction and prime buckets. -/

open Finset

namespace TangZhangPrimeMass

private noncomputable def recip : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by simp [mul_comm]

private theorem recip_apply (n : ℕ) : recip n = (n : ℝ)⁻¹ := rfl

private theorem recip_prime_lt_one {p : ℕ} (hp : Nat.Prime p) : ‖recip p‖ < 1 := by
  rw [recip_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

private theorem log_le_prime_product {X : ℕ} (hX : 2 ≤ X) :
    Real.log (X : ℝ) ≤ ∏ p ∈ (Icc 1 X).filter Nat.Prime, (1 - (p : ℝ)⁻¹)⁻¹ := by
  classical
  let P := Icc 1 X
  obtain ⟨hsum, hprod⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := recip) (fun hp => recip_prime_lt_one hp) P
  have hmem (n : ℕ) (hn : n ∈ P) : n ∈ Nat.factoredNumbers P := by
    obtain ⟨h1, h2⟩ := mem_Icc.mp hn
    refine Nat.mem_factoredNumbers_of_primeFactors_subset (by omega) ?_
    intro p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    exact mem_Icc.mpr ⟨hpp.one_lt.le, (Nat.le_of_dvd (by omega) hpd).trans h2⟩
  let emb : ↥P ↪ Nat.factoredNumbers P :=
    ⟨fun n => ⟨n, hmem n n.property⟩,
      fun _ _ h => Subtype.ext (congrArg (fun q : Nat.factoredNumbers P => (q : ℕ)) h)⟩
  have hfinite :
      (∑ n ∈ P, (n : ℝ)⁻¹) ≤ ∑' n : Nat.factoredNumbers P, recip n := by
    calc
      _ = ∑ n ∈ P.attach.map emb, recip n := by
        rw [sum_map, ← sum_attach P (fun n : ℕ => (n : ℝ)⁻¹)]
        rfl
      _ ≤ _ := Summable.sum_le_tsum _ (fun _ _ => by rw [recip_apply]; positivity) hsum.of_norm
  have hlog : Real.log (X : ℝ) ≤ ∑ n ∈ P, (n : ℝ)⁻¹ := by
    simpa only [Nat.floor_natCast, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast, P] using
      log_le_harmonic_floor (X : ℝ) (by positivity)
  simpa only [recip_apply, P] using hlog.trans (hfinite.trans_eq hprod.tsum_eq)

private theorem log_factor_le {p : ℕ} (hp : Nat.Prime p) :
    Real.log ((1 - (p : ℝ)⁻¹)⁻¹) ≤
      (p : ℝ)⁻¹ + (((p - 1 : ℕ) : ℝ)⁻¹ - (p : ℝ)⁻¹) := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : 0 < (p : ℝ) := zero_lt_one.trans hp1
  have h0 : 0 < (p : ℝ) - 1 := sub_pos.mpr hp1
  have hdiv : ((1 - (p : ℝ)⁻¹)⁻¹) = 1 + ((p : ℝ) - 1)⁻¹ := by
    have h1 : (1 : ℝ) - (p : ℝ)⁻¹ ≠ 0 := sub_ne_zero.mpr (ne_of_gt (inv_lt_one_of_one_lt₀ hp1))
    field_simp [hp0.ne', h0.ne', h1]
    ring
  rw [hdiv, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  rw [show (p : ℝ)⁻¹ + (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹) = ((p : ℝ) - 1)⁻¹ by ring]
  have ht : 0 < (1 : ℝ) + ((p : ℝ) - 1)⁻¹ := by positivity
  linarith [Real.log_le_sub_one_of_pos ht]

private theorem telescope (n : ℕ) :
    (∑ p ∈ Icc 2 (n + 2), (((p - 1 : ℕ) : ℝ)⁻¹ - (p : ℝ)⁻¹)) =
      1 - ((n + 2 : ℕ) : ℝ)⁻¹ := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show n.succ + 2 = (n + 2) + 1 by omega, sum_Icc_succ_top (by omega), ih]
    rw [Nat.add_sub_cancel]
    ring

theorem prime_mass_lower (X : ℕ) (hX : 2 ≤ X) :
    Real.log (Real.log (X : ℝ)) - 1 ≤
      ∑ p ∈ (Icc 1 X).filter Nat.Prime, (p : ℝ)⁻¹ := by
  let S := (Icc 1 X).filter Nat.Prime
  have hX1 : 1 < (X : ℝ) := by exact_mod_cast (show 1 < X by omega)
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos hX1
  have hprod := Real.log_le_log hlog (log_le_prime_product hX)
  have hlocal (p : ℕ) (hp : p ∈ S) : (1 - (p : ℝ)⁻¹)⁻¹ ≠ 0 := by
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2.one_lt
    exact ne_of_gt (inv_pos.mpr (sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)))
  change Real.log (Real.log (X : ℝ)) ≤ Real.log (∏ p ∈ S, (1 - (p : ℝ)⁻¹)⁻¹) at hprod
  rw [Real.log_prod hlocal] at hprod
  have hsum := sum_le_sum (fun p hp => log_factor_le (mem_filter.mp hp).2 :
    ∀ p ∈ S, Real.log ((1 - (p : ℝ)⁻¹)⁻¹) ≤
      (p : ℝ)⁻¹ + (((p - 1 : ℕ) : ℝ)⁻¹ - (p : ℝ)⁻¹))
  rw [sum_add_distrib] at hsum
  have hS : S ⊆ Icc 2 X := by
    intro p hp
    exact mem_Icc.mpr ⟨(mem_filter.mp hp).2.two_le, (mem_Icc.mp (mem_filter.mp hp).1).2⟩
  have hErr :
      (∑ p ∈ S, (((p - 1 : ℕ) : ℝ)⁻¹ - (p : ℝ)⁻¹)) ≤ 1 := by
    calc
      _ ≤ ∑ p ∈ Icc 2 X, (((p - 1 : ℕ) : ℝ)⁻¹ - (p : ℝ)⁻¹) := by
        refine sum_le_sum_of_subset_of_nonneg hS fun p hp _ => sub_nonneg.mpr ?_
        refine inv_anti₀ ?_ (by exact_mod_cast Nat.sub_le p 1)
        exact_mod_cast (show 0 < p - 1 by have := (mem_Icc.mp hp).1; omega)
      _ = 1 - (X : ℝ)⁻¹ := by
        simpa only [Nat.sub_add_cancel hX] using telescope (X - 2)
      _ ≤ 1 := sub_le_self _ (by positivity)
  change Real.log (Real.log (X : ℝ)) - 1 ≤ ∑ p ∈ S, (p : ℝ)⁻¹
  linarith

end TangZhangPrimeMass

/- Encode a rigid family of bucket supports as products of distinct primes. -/

open Finset

namespace TangLowerEncoding

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private abbrev Pick (I : Finset ι) := ∀ i ∈ I, ℕ

private def pickSupport {I : Finset ι} (x : Pick I) : Finset ℕ :=
  I.attach.image (fun i => x i.val i.property)

private def pickValue {I : Finset ι} (x : Pick I) : ℕ :=
  ∏ i ∈ I.attach, x i.val i.property

omit [Fintype ι] [DecidableEq ι] in
private theorem mem_pickSupport {I : Finset ι} (x : Pick I) (p : ℕ) :
    p ∈ pickSupport x ↔ ∃ (i : ι) (hi : i ∈ I), x i hi = p := by
  unfold pickSupport
  constructor
  · rintro h
    obtain ⟨i, -, rfl⟩ := mem_image.mp h
    exact ⟨i.val, i.property, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact mem_image.mpr ⟨⟨i, hi⟩, mem_attach _ _, rfl⟩

omit [Fintype ι] in
private theorem pick_injective {P : ι → Finset ℕ} (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    {I : Finset ι} {x : Pick I} (hx : x ∈ I.pi P) :
    Function.Injective (fun i : ↥I => x i.val i.property) := by
  intro i j hij
  apply Subtype.ext
  by_contra hd
  have hxi := mem_pi.mp hx i.val i.property
  have hxj := mem_pi.mp hx j.val j.property
  change x i.val i.property = x j.val j.property at hij
  rw [← hij] at hxj
  exact Finset.disjoint_left.mp (hdis hd) hxi hxj

omit [Fintype ι] in
private theorem pickValue_eq_prod {P : ι → Finset ℕ}
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    {I : Finset ι} {x : Pick I} (hx : x ∈ I.pi P) :
    pickValue x = ∏ p ∈ pickSupport x, p := by
  unfold pickSupport pickValue
  rw [prod_image]
  exact fun _ _ _ _ h => pick_injective hdis hx h

omit [Fintype ι] in
private theorem pickValue_primeFactors {P : ι → Finset ℕ}
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hp : ∀ i p, p ∈ P i → Nat.Prime p)
    {I : Finset ι} {x : Pick I} (hx : x ∈ I.pi P) :
    (pickValue x).primeFactors = pickSupport x := by
  rw [pickValue_eq_prod hdis hx]
  apply Nat.primeFactors_prod
  intro p hp'
  obtain ⟨i, hi, rfl⟩ := (mem_pickSupport x p).mp hp'
  exact hp _ _ (mem_pi.mp hx i hi)

omit [Fintype ι] in
private theorem pickValue_pos {P : ι → Finset ℕ} (hp : ∀ i p, p ∈ P i → Nat.Prime p)
    {I : Finset ι} {x : Pick I} (hx : x ∈ I.pi P) :
    0 < pickValue x := by
  apply Finset.prod_pos
  intro i _
  exact (hp _ _ (mem_pi.mp hx _ i.property)).pos

omit [Fintype ι] in
private theorem hit_pickSupport {P : ι → Finset ℕ}
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    {I : Finset ι} {x : Pick I} (hx : x ∈ I.pi P) {i : ι} {p : ℕ} (hp : p ∈ P i) :
    p ∈ pickSupport x ↔ ∃ hi : i ∈ I, x i hi = p := by
  rw [mem_pickSupport]
  constructor
  · rintro ⟨j, hj, hxp⟩
    have hji : j = i := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdis hne) (hxp ▸ mem_pi.mp hx j hj) hp
    subst j
    exact ⟨hj, hxp⟩
  · rintro ⟨hi, hxp⟩
    exact ⟨i, hi, hxp⟩

private noncomputable def bucketSupport (P : ι → Finset ℕ) (s : Finset ℕ) : Finset ι := by
  classical
  exact univ.filter (fun i => ∃ p ∈ P i, p ∈ s)

private theorem bucketSupport_union (P : ι → Finset ℕ) (s t : Finset ℕ) :
    bucketSupport P (s ∪ t) = bucketSupport P s ∪ bucketSupport P t := by
  classical
  ext i
  simp only [bucketSupport, mem_filter, mem_univ, true_and, mem_union]
  constructor
  · rintro ⟨p, hp, hps | hpt⟩
    · exact Or.inl ⟨p, hp, hps⟩
    · exact Or.inr ⟨p, hp, hpt⟩
  · rintro (⟨p, hp, hps⟩ | ⟨p, hp, hpt⟩)
    · exact ⟨p, hp, Or.inl hps⟩
    · exact ⟨p, hp, Or.inr hpt⟩

private theorem bucketSupport_pickSupport {P : ι → Finset ℕ}
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    {I : Finset ι} {x : Pick I} (hx : x ∈ I.pi P) :
    bucketSupport P (pickSupport x) = I := by
  classical
  ext i
  simp only [bucketSupport, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, hps⟩
    exact ((hit_pickSupport hdis hx hp).mp hps).choose
  · intro hi
    refine ⟨x i hi, mem_pi.mp hx i hi, ?_⟩
    exact (mem_pickSupport x _).mpr ⟨i, hi, rfl⟩

private theorem pickValue_injective {P : ι → Finset ℕ}
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hp : ∀ i p, p ∈ P i → Nat.Prime p)
    {I J : Finset ι} {x : Pick I} {y : Pick J} (hx : x ∈ I.pi P) (hy : y ∈ J.pi P)
    (h : pickValue x = pickValue y) :
    (⟨I, x⟩ : Sigma Pick) = ⟨J, y⟩ := by
  have ht := congrArg Nat.primeFactors h
  rw [pickValue_primeFactors hdis hp hx, pickValue_primeFactors hdis hp hy] at ht
  have hI := congrArg (bucketSupport P) ht
  rw [bucketSupport_pickSupport hdis hx, bucketSupport_pickSupport hdis hy] at hI
  subst J
  congr 1
  funext i hi
  have hxval : x i hi ∈ pickSupport x := (mem_pickSupport x _).mpr ⟨i, hi, rfl⟩
  rw [ht] at hxval
  obtain ⟨hi', he⟩ := (hit_pickSupport hdis hy (mem_pi.mp hx i hi)).mp hxval
  exact he.symm

private theorem primeFactors_lcm {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.lcm a b).primeFactors = a.primeFactors ∪ b.primeFactors := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hprime, hd, -⟩ := Nat.mem_primeFactors.mp hp
    have hmul : p ∣ a * b :=
      hd.trans (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))
    rcases hprime.dvd_mul.mp hmul with h | h
    · exact mem_union.mpr (Or.inl (Nat.mem_primeFactors.mpr ⟨hprime, h, ha⟩))
    · exact mem_union.mpr (Or.inr (Nat.mem_primeFactors.mpr ⟨hprime, h, hb⟩))
  · intro hp
    rcases mem_union.mp hp with hpa | hpb
    · obtain ⟨hprime, hd, -⟩ := Nat.mem_primeFactors.mp hpa
      exact Nat.mem_primeFactors.mpr ⟨hprime, hd.trans (Nat.dvd_lcm_left _ _), Nat.lcm_ne_zero ha hb⟩
    · obtain ⟨hprime, hd, -⟩ := Nat.mem_primeFactors.mp hpb
      exact Nat.mem_primeFactors.mpr ⟨hprime, hd.trans (Nat.dvd_lcm_right _ _), Nat.lcm_ne_zero ha hb⟩

omit [Fintype ι] in
private theorem pick_rigidity_same {P : ι → Finset ℕ}
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    {I : Finset ι} {x y z : Pick I}
    (hx : x ∈ I.pi P) (hy : y ∈ I.pi P) (hz : z ∈ I.pi P)
    (h₁ : pickSupport x ∪ pickSupport y = pickSupport x ∪ pickSupport z)
    (h₂ : pickSupport x ∪ pickSupport y = pickSupport y ∪ pickSupport z) :
    x = y := by
  funext i hi
  have hxhit : x i hi ∈ pickSupport x := (mem_pickSupport x _).mpr ⟨i, hi, rfl⟩
  have hyhit : y i hi ∈ pickSupport y := (mem_pickSupport y _).mpr ⟨i, hi, rfl⟩
  have hxmem : x i hi ∈ pickSupport y ∪ pickSupport z := by
    rw [← h₂]
    exact mem_union.mpr (Or.inl hxhit)
  have hymem : y i hi ∈ pickSupport x ∪ pickSupport z := by
    rw [← h₁]
    exact mem_union.mpr (Or.inr hyhit)
  rcases mem_union.mp hxmem with hxy | hxz
  · obtain ⟨_, hxy'⟩ := (hit_pickSupport hdis hy (mem_pi.mp hx i hi)).mp hxy
    exact hxy'.symm
  rcases mem_union.mp hymem with hyx | hyz
  · obtain ⟨_, hyx'⟩ := (hit_pickSupport hdis hx (mem_pi.mp hy i hi)).mp hyx
    exact hyx'
  · obtain ⟨_, hxz'⟩ := (hit_pickSupport hdis hz (mem_pi.mp hx i hi)).mp hxz
    obtain ⟨_, hyz'⟩ := (hit_pickSupport hdis hz (mem_pi.mp hy i hi)).mp hyz
    exact hxz'.symm.trans hyz'

private theorem pick_rigidity {P : ι → Finset ℕ}
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    {F : Finset (Finset ι)}
    (hRigid : ∀ I ∈ F, ∀ J ∈ F, ∀ K ∈ F, I ∪ J = I ∪ K → I ∪ J = J ∪ K → I = J ∧ J = K)
    {I J K : Finset ι} (hI : I ∈ F) (hJ : J ∈ F) (hK : K ∈ F)
    {x : Pick I} {y : Pick J} {z : Pick K}
    (hx : x ∈ I.pi P) (hy : y ∈ J.pi P) (hz : z ∈ K.pi P)
    (h₁ : pickSupport x ∪ pickSupport y = pickSupport x ∪ pickSupport z)
    (h₂ : pickSupport x ∪ pickSupport y = pickSupport y ∪ pickSupport z) :
    pickValue x = pickValue y := by
  have he₁ := congrArg (bucketSupport P) h₁
  have he₂ := congrArg (bucketSupport P) h₂
  simp only [bucketSupport_union, bucketSupport_pickSupport hdis hx,
    bucketSupport_pickSupport hdis hy, bucketSupport_pickSupport hdis hz] at he₁ he₂
  obtain ⟨e₁, e₂⟩ := hRigid I hI J hJ K hK he₁ he₂
  subst J K
  rw [pick_rigidity_same hdis hx hy hz h₁ h₂]

noncomputable def encode (P : ι → Finset ℕ) (F : Finset (Finset ι)) : Finset ℕ := by
  classical
  exact (F.sigma (fun I => I.pi P)).image (fun a => pickValue a.2)

theorem encode_free {P : ι → Finset ℕ} (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hp : ∀ i p, p ∈ P i → Nat.Prime p)
    {F : Finset (Finset ι)}
    (hRigid : ∀ I ∈ F, ∀ J ∈ F, ∀ K ∈ F, I ∪ J = I ∪ K → I ∪ J = J ∪ K → I = J ∧ J = K) :
    ¬ Erdos856.HasEqualLcmTuple 3 (encode P F) := by
  classical
  rintro ⟨S, hS, hcard, L, hlcm⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hcard
  have hl₁ : Nat.lcm a b = Nat.lcm a c :=
    (hlcm a (by simp) b (by simp) hab).trans (hlcm a (by simp) c (by simp) hac).symm
  have hl₂ : Nat.lcm a b = Nat.lcm b c :=
    (hlcm a (by simp) b (by simp) hab).trans (hlcm b (by simp) c (by simp) hbc).symm
  have hsa := hS (show a ∈ ({a,b,c} : Finset ℕ) by simp)
  have hsb := hS (show b ∈ ({a,b,c} : Finset ℕ) by simp)
  have hsc := hS (show c ∈ ({a,b,c} : Finset ℕ) by simp)
  rcases mem_image.mp hsa with ⟨⟨I,x⟩, hIx, rfl⟩
  rcases mem_image.mp hsb with ⟨⟨J,y⟩, hJy, rfl⟩
  rcases mem_image.mp hsc with ⟨⟨K,z⟩, hKz, rfl⟩
  obtain ⟨hI, hx⟩ := mem_sigma.mp hIx
  obtain ⟨hJ, hy⟩ := mem_sigma.mp hJy
  obtain ⟨hK, hz⟩ := mem_sigma.mp hKz
  have hx0 := (pickValue_pos hp hx).ne'
  have hy0 := (pickValue_pos hp hy).ne'
  have hz0 := (pickValue_pos hp hz).ne'
  have h₁ := congrArg Nat.primeFactors hl₁
  have h₂ := congrArg Nat.primeFactors hl₂
  simp only [primeFactors_lcm hx0 hy0, primeFactors_lcm hx0 hz0, primeFactors_lcm hy0 hz0,
    pickValue_primeFactors hdis hp hx, pickValue_primeFactors hdis hp hy,
    pickValue_primeFactors hdis hp hz] at h₁ h₂
  exact hab (pick_rigidity hdis hRigid hI hJ hK hx hy hz h₁ h₂)

theorem encode_subset {P : ι → Finset ℕ} {F : Finset (Finset ι)} {X N : ℕ} (hX : 1 ≤ X)
    (hp : ∀ i p, p ∈ P i → Nat.Prime p ∧ p ≤ X)
    (hN : X ^ Fintype.card ι ≤ N) :
    encode P F ⊆ Icc 1 N := by
  classical
  intro n hn
  rcases mem_image.mp hn with ⟨⟨I,x⟩, hx, rfl⟩
  have hchoice := (mem_sigma.mp hx).2
  apply mem_Icc.mpr
  refine ⟨pickValue_pos (fun i p h => (hp i p h).1) hchoice, ?_⟩
  calc
    pickValue x ≤ X ^ I.attach.card :=
      prod_le_pow_card _ _ _ (fun i _ => (hp _ _ (mem_pi.mp hchoice _ i.property)).2)
    _ = X ^ I.card := by rw [card_attach]
    _ ≤ X ^ Fintype.card ι := Nat.pow_le_pow_right (by omega) (card_le_univ _)
    _ ≤ N := hN

theorem encode_harmonic_ge {P : ι → Finset ℕ}
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hp : ∀ i p, p ∈ P i → Nat.Prime p)
    (hmass : ∀ i, 1 ≤ ∑ p ∈ P i, (p : ℝ)⁻¹) (F : Finset (Finset ι)) :
    (F.card : ℝ) ≤ ∑ n ∈ encode P F, (n : ℝ)⁻¹ := by
  classical
  let S : Finset (Sigma Pick) := F.sigma (fun I => I.pi P)
  have hinj : ∀ a ∈ S, ∀ b ∈ S, pickValue a.2 = pickValue b.2 → a = b := by
    rintro ⟨I,x⟩ hx ⟨J,y⟩ hy h
    exact pickValue_injective hdis hp (mem_sigma.mp hx).2 (mem_sigma.mp hy).2 h
  rw [encode, sum_image hinj]
  dsimp only [S]
  rw [sum_sigma]
  calc
    _ = ∑ _I ∈ F, (1 : ℝ) := by simp
    _ ≤ ∑ I ∈ F, ∏ i ∈ I, ∑ p ∈ P i, (p : ℝ)⁻¹ :=
      sum_le_sum (fun I _ => one_le_prod (fun i _ => hmass i))
    _ = _ := by
      apply sum_congr rfl
      intro I _
      rw [prod_sum]
      apply sum_congr rfl
      intro x _
      rw [pickValue, Nat.cast_prod, prod_inv_distrib]

theorem lower_of_buckets {P : ι → Finset ℕ} {N X : ℕ} (hX : 1 ≤ X)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hp : ∀ i p, p ∈ P i → Nat.Prime p ∧ p ≤ X)
    (hmass : ∀ i, 1 ≤ ∑ p ∈ P i, (p : ℝ)⁻¹) (hN : X ^ Fintype.card ι ≤ N)
    {F : Finset (Finset ι)}
    (hRigid : ∀ I ∈ F, ∀ J ∈ F, ∀ K ∈ F, I ∪ J = I ∪ K → I ∪ J = J ∪ K → I = J ∧ J = K) :
    (F.card : ℝ) ≤ Erdos856.f 3 N := by
  have hp' (i p) (h : p ∈ P i) := (hp i p h).1
  exact (encode_harmonic_ge hdis hp' hmass F).trans
    (Erdos856.sum_le_f (encode_subset hX hp hN) (encode_free hdis hp' hRigid))

end TangLowerEncoding

/- Extraction of disjoint prime blocks with harmonic mass at least one. -/

open Finset Filter
open scoped Topology

namespace TangLowerBuckets

private theorem one_bucket (T : Finset ℕ) (w : ℕ → ℝ) {δ : ℝ}
    (hw : ∀ p ∈ T, w p ≤ δ) (hT : 1 ≤ ∑ p∈T,w p) :
    ∃ B ⊆ T, 1 ≤ ∑ p∈B,w p ∧ ∑ p∈B,w p ≤ 1+δ := by
  classical
  let C := T.powerset.filter (fun A => 1 ≤ ∑ p∈A,w p)
  have hC : C.Nonempty := ⟨T,mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl,hT⟩⟩
  obtain ⟨B,hB,hmin⟩ := C.exists_min_image Finset.card hC
  have hSub : B⊆T := mem_powerset.mp (mem_filter.mp hB).1
  have hB1 : 1 ≤ ∑ p∈B,w p := (mem_filter.mp hB).2
  have hBN : B.Nonempty := by
    by_contra! hc
    rw [hc,sum_empty] at hB1
    norm_num at hB1
  obtain ⟨q,hq⟩ := hBN
  have hE : (∑ p∈B.erase q,w p) < 1 := by
    by_contra! h
    have hmem : B.erase q∈C := mem_filter.mpr
      ⟨mem_powerset.mpr ((erase_subset _ _).trans hSub),h⟩
    exact (not_le_of_gt (card_erase_lt_of_mem hq)) (hmin _ hmem)
  refine ⟨B,hSub,hB1,?_⟩
  have hp := hw q (hSub hq)
  have hSum := sum_erase_add B w hq
  linarith

theorem greedy (w : ℕ → ℝ) {δ : ℝ} (hδ : 0≤δ) (k : ℕ) (T : Finset ℕ)
    (hw : ∀ p∈T,w p≤δ) (hMass : (k:ℝ)*(1+δ) ≤ ∑ p∈T,w p) :
    ∃ P : Fin k → Finset ℕ, (∀ i,P i⊆T) ∧
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧ ∀ i, 1≤∑ p∈P i,w p := by
  classical
  induction k generalizing T with
  | zero =>
    exact ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ k ih =>
    have hB1 : 1 ≤ ∑ p∈T,w p := by
      have hk : 1 ≤ (k.succ : ℝ) := by exact_mod_cast Nat.succ_pos k
      calc
        1=(1:ℝ)*1 := by norm_num
        _ ≤ (k.succ:ℝ)*(1+δ) :=
          mul_le_mul hk (le_add_of_nonneg_right hδ) zero_le_one (by positivity)
        _ ≤ _ := hMass
    obtain ⟨B,hSub,hB,hW⟩ := one_bucket T w hw hB1
    have hsplit := Finset.sum_sdiff (f := w) hSub
    have hRest : (k : ℝ)*(1+δ) ≤ ∑ p∈T\B,w p := by
      push_cast at hMass
      linarith
    obtain ⟨Q,hQSub,hQDisj,hQ⟩ := ih (T\B) (fun p hp => hw p (mem_sdiff.mp hp).1) hRest
    let P : Fin (k+1) → Finset ℕ := Fin.cons B Q
    have hNo (j : Fin k) : Disjoint B (Q j) := by
      apply Finset.disjoint_left.mpr
      intro p hp hpQ
      exact (mem_sdiff.mp (hQSub j hpQ)).2 hp
    refine ⟨P,?_,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [P] using hSub
      · simpa [P] using (hQSub j).trans sdiff_subset
    · intro i j hij
      revert hij
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j _ => ?_) j
        · intro h
          exact (h rfl).elim
        · simpa [P] using hNo j
      · refine Fin.cases (fun _ => ?_) (fun j hj => ?_) j
        · simpa [P] using (hNo i).symm
        · simpa [P] using hQDisj (fun h => hj (congrArg Fin.succ h))
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [P] using hB
      · simpa [P] using hQ j

noncomputable def smallMass : ℝ := ∑ p∈Icc (1 : ℕ) 199,(p:ℝ)⁻¹

def largePrimes (X : ℕ) : Finset ℕ := ((Icc 1 X).filter Nat.Prime).filter (200 ≤ ·)

theorem large_prime_mass {C : ℝ}
    (hC : ∀ X : ℕ, 2≤X → Real.log (Real.log (X : ℝ))-C ≤
      ∑ p∈(Icc 1 X).filter Nat.Prime,(p:ℝ)⁻¹)
    {X : ℕ} (hX : 2≤X) :
    Real.log (Real.log (X : ℝ))-C-smallMass ≤ ∑ p∈largePrimes X,(p:ℝ)⁻¹ := by
  classical
  let T := (Icc 1 X).filter Nat.Prime
  have hSplit : (∑ p∈largePrimes X,(p:ℝ)⁻¹) +
      (∑ p∈T.filter (fun p => ¬200≤p),(p:ℝ)⁻¹) = ∑ p∈T,(p:ℝ)⁻¹ :=
    Finset.sum_filter_add_sum_filter_not T (200≤·) _
  have hSmall : (∑ p∈T.filter (fun p => ¬200≤p),(p:ℝ)⁻¹)≤ smallMass := by
    apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)
    intro p hp
    have h1 := (mem_Icc.mp (mem_filter.mp (mem_filter.mp hp).1).1).1
    have h2 := (mem_filter.mp hp).2
    exact mem_Icc.mpr ⟨h1,by omega⟩
  have hAll := hC X hX
  change Real.log (Real.log (X : ℝ))-C ≤ ∑ p∈T,(p:ℝ)⁻¹ at hAll
  linarith

theorem prime_buckets {X k : ℕ}
    (h : (k:ℝ)*(1+1/200) ≤ ∑ p∈largePrimes X,(p:ℝ)⁻¹) :
    ∃ P : Fin k → Finset ℕ, Pairwise (fun i j => Disjoint (P i) (P j)) ∧
      (∀ i p, p∈P i → p.Prime ∧ p≤X) ∧ (∀ i, 1≤∑ p∈P i,(p:ℝ)⁻¹) := by
  have hw (p : ℕ) (hp : p∈largePrimes X) : (p:ℝ)⁻¹≤(1/200:ℝ) := by
    have hP : (200:ℝ)≤p := by exact_mod_cast (mem_filter.mp hp).2
    rw [one_div]
    exact inv_anti₀ (by norm_num) hP
  obtain ⟨P,hSub,hDisj,hP⟩ := greedy (fun p => (p:ℝ)⁻¹) (by norm_num : 0 ≤ (1/200:ℝ))
    k (largePrimes X) hw h
  refine ⟨P,hDisj,?_,hP⟩
  intro i p hp
  have hh := mem_filter.mp (mem_filter.mp (hSub i hp)).1
  exact ⟨hh.2,(mem_Icc.mp hh.1).2⟩

end TangLowerBuckets

open Finset Filter
open scoped Topology

namespace TangLowerBuckets

private theorem growth_gap : 0 < (49/400 : ℝ)*Real.log 36 - Real.log 1.551 := by
  have h1 : (1.551 : ℝ)^8 ≤ 33.49 := by norm_num
  have h2 : (33.49 : ℝ)^50 < (36 : ℝ)^49 := by norm_num
  have h : (1.551 : ℝ)^(8*50 : ℕ) < (36 : ℝ)^49 := by
    rw [pow_mul]
    exact (pow_le_pow_left₀ (by norm_num) h1 _).trans_lt h2
  have hlog := Real.log_lt_log (by positivity) h
  rw [Real.log_pow,Real.log_pow] at hlog
  norm_num at hlog
  linarith

private theorem eventual_scales (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ j X : ℕ, 2≤X ∧
      ((8*j+1 : ℕ):ℝ)*(1+1/200) ≤ Real.log (Real.log (X : ℝ))-C ∧
      X^(8*j+1) ≤ N ∧ (Real.log (N : ℝ))^(Real.log 1.551-ε) ≤ (36 : ℝ)^j := by
  let D := (49/400 : ℝ)*Real.log 36 - Real.log 1.551
  have hD : 0 < D := growth_gap
  let A := (10000/51 : ℝ)*(C+Real.log 2+201/200)
  have hll : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop (2 : ℕ),hll.eventually_ge_atTop (20000:ℝ),
    hll.eventually_ge_atTop A,hll.eventually_ge_atTop (Real.log 36/D)] with N hN hT hA hG
  let t := Real.log (Real.log (N : ℝ))
  have ht : 20000≤t := hT
  have ht0 : 0≤t := by linarith
  have hLN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  let L := Real.exp ((99/100 : ℝ)*t)
  let X := ⌊Real.exp L⌋₊
  have hL : 4≤L := by
    have he := Real.add_one_le_exp ((99/100:ℝ)*t)
    dsimp only [L]
    linarith
  have hHalf : 2 ≤ Real.exp (L/2) := by linarith [Real.add_one_le_exp (L/2)]
  have hXl : Real.exp (L/2) ≤ (X : ℝ) := by
    have hlt := Nat.lt_floor_add_one (Real.exp L)
    change Real.exp L < (X : ℝ)+1 at hlt
    have hEq : Real.exp L = Real.exp (L/2)*Real.exp (L/2) := by
      rw [←Real.exp_add]
      congr 1
      ring
    rw [hEq] at hlt
    have hq := mul_nonneg (sub_nonneg.mpr hHalf)
      (show 0 ≤ Real.exp (L/2)+1 by positivity)
    nlinarith
  have hX : 2≤X := by exact_mod_cast hHalf.trans hXl
  have hX0 : 0 < (X : ℝ) := by exact_mod_cast (show 0<X by omega)
  have hXr : (X : ℝ) ≤ Real.exp L := Nat.floor_le (Real.exp_pos _).le
  have hLogX : Real.log (X : ℝ) ≤ L := by
    have h := Real.log_le_log hX0 hXr
    rwa [Real.log_exp] at h
  have hLogX' : L/2 ≤ Real.log (X : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hXl
    rwa [Real.log_exp] at h
  have hL0 : 0<L := Real.exp_pos _
  have hLogLogX : (99/100 : ℝ)*t - Real.log 2 ≤ Real.log (Real.log (X : ℝ)) := by
    have h := Real.log_le_log (div_pos hL0 zero_lt_two) hLogX'
    rw [Real.log_div hL0.ne' two_ne_zero] at h
    simpa only [L,Real.log_exp] using h
  let j := ⌊(49/400 : ℝ)*t⌋₊
  let k := 8*j+1
  have hjle : (j : ℝ) ≤ (49/400 : ℝ)*t :=
    Nat.floor_le (by positivity)
  have hjlt : (49/400 : ℝ)*t < (j : ℝ)+1 :=
    Nat.lt_floor_add_one _
  have hk : (k : ℝ) ≤ (49/50 : ℝ)*t+1 := by
    dsimp [k]
    push_cast
    linarith
  have hMass : (k : ℝ)*(1+1/200) ≤ Real.log (Real.log (X : ℝ))-C := by
    calc
      _ ≤ ((49/50 : ℝ)*t+1)*(1+1/200) :=
        mul_le_mul_of_nonneg_right hk (by norm_num)
      _ ≤ _ := by
        change A≤t at hA
        dsimp [A] at hA
        linarith
  have heQuadratic : (t/100)^2/2 ≤ Real.exp (t/100) := by
    have he := Real.sum_le_exp_of_nonneg (show 0≤t/100 by positivity) 3
    norm_num [Finset.sum_range_succ] at he
    linarith
  have hQuad : t ≤ (t/100)^2/2 := by
    nlinarith [mul_le_mul_of_nonneg_left ht ht0]
  have hk' : (k : ℝ) ≤ t := by linarith
  have hKExp : (k : ℝ) ≤ Real.exp (t/100) := hk'.trans (hQuad.trans heQuadratic)
  have hLogPower : (k : ℝ)*Real.log (X : ℝ) ≤ Real.log (N : ℝ) := by
    calc
      _ ≤ (k : ℝ)*L := mul_le_mul_of_nonneg_left hLogX (by positivity)
      _ ≤ Real.exp (t/100)*L := mul_le_mul_of_nonneg_right hKExp hL0.le
      _ = Real.exp t := by
        unfold L
        rw [←Real.exp_add]
        congr 1
        ring
      _ = _ := Real.exp_log hLN
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0<N by omega)
  have hPow : X^k≤N := by
    have hr : (X : ℝ)^k ≤ (N : ℝ) :=
      (Real.log_le_log_iff (pow_pos hX0 k) hN0).mp (by rw [Real.log_pow]; exact hLogPower)
    exact_mod_cast hr
  have hl36 : 0 < Real.log (36 : ℝ) := Real.log_pos (by norm_num)
  have hTGap : Real.log 36 ≤ t*D := (div_le_iff₀ hD).mp hG
  have hgFloor := (mul_lt_mul_of_pos_right hjlt hl36).le
  have hj36 : t*Real.log 1.551 ≤ (j : ℝ)*Real.log 36 := by
    dsimp [D] at hTGap
    nlinarith
  have hRate : (Real.log (N : ℝ))^(Real.log 1.551-ε) ≤ (36 : ℝ)^j := by
    have he : (36 : ℝ)^j = Real.exp ((j : ℝ)*Real.log 36) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
    rw [Real.rpow_def_of_pos hLN,he]
    apply Real.exp_le_exp.mpr
    change t*(Real.log 1.551-ε) ≤ _
    exact (mul_le_mul_of_nonneg_left (sub_le_self _ hε.le) ht0).trans hj36
  exact ⟨j,X,hX,hMass,hPow,hRate⟩

/-- Scale the prime cutoff and bucket count to the target logarithmic lower exponent. -/
theorem eventual_buckets
    (hPrimes : ∃ C : ℝ, ∀ X : ℕ, 2≤X →
      Real.log (Real.log (X : ℝ))-C ≤ ∑ p∈(Icc 1 X).filter Nat.Prime,(p:ℝ)⁻¹)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∃ (j X : ℕ) (P : Fin (8*j+1) → Finset ℕ),
      Pairwise (fun i k => Disjoint (P i) (P k)) ∧
      (∀ i p, p∈P i → p.Prime ∧ p≤X) ∧
      (∀ i, 1≤∑ p∈P i,(p:ℝ)⁻¹) ∧ X^(8*j+1)≤N ∧
      (Real.log (N : ℝ))^(Real.log 1.551-ε)≤(36 : ℝ)^j := by
  obtain ⟨C,hC⟩ := hPrimes
  filter_upwards [eventual_scales (C+smallMass) ε hε] with N hN
  obtain ⟨j,X,hX,hMass,hPow,hR⟩ := hN
  have hLarge := large_prime_mass hC hX
  have hM := hMass.trans (show Real.log (Real.log (X : ℝ))-(C+smallMass) ≤
    ∑ p∈largePrimes X,(p:ℝ)⁻¹ by linarith)
  obtain ⟨P,hDisj,hSub,hP⟩ := prime_buckets hM
  exact ⟨j,X,P,hDisj,hSub,hP,hPow,hR⟩

end TangLowerBuckets

/- The 75-set family of Claude [Cla2026], Small base families for the 3-sunflower-free capacity.
The construction is recorded at https://github.com/joshua17-create/sunflower-lower-bound
(commit 6e34d78ab482). The edges of the complete graph on five vertices are numbered in
lexicographic order, starting with 01, 02, 03 and 04. The members are the five stars, the ten cuts
with both parts of size at least two, and the complements of the sixty chairs. -/

open Finset

namespace LcmBase75

def base : Finset (Finset ℕ) :=
  { {0, 1, 2, 3}, {0, 4, 5, 6}, {1, 2, 3, 4, 5, 6}, {0, 1, 3, 4, 5, 7}, {0, 2, 3, 4, 5, 7},
    {1, 2, 3, 4, 5, 7}, {0, 1, 2, 4, 6, 7}, {0, 1, 3, 4, 6, 7}, {0, 1, 2, 5, 6, 7}, {0, 2, 3, 5, 6, 7},
    {1, 2, 4, 5, 6, 7}, {0, 1, 2, 4, 5, 8}, {0, 1, 3, 4, 5, 8}, {0, 1, 2, 4, 6, 8}, {0, 2, 3, 4, 6, 8},
    {1, 2, 3, 4, 6, 8}, {0, 1, 3, 5, 6, 8}, {0, 2, 3, 5, 6, 8}, {1, 3, 4, 5, 6, 8}, {1, 4, 7, 8},
    {0, 2, 3, 4, 7, 8}, {0, 1, 2, 5, 7, 8}, {1, 2, 3, 5, 7, 8}, {0, 2, 4, 5, 7, 8}, {0, 1, 3, 6, 7, 8},
    {1, 2, 3, 6, 7, 8}, {0, 3, 4, 6, 7, 8}, {0, 1, 5, 6, 7, 8}, {2, 3, 5, 6, 7, 8}, {2, 4, 5, 6, 7, 8},
    {3, 4, 5, 6, 7, 8}, {0, 1, 2, 4, 5, 9}, {0, 2, 3, 4, 5, 9}, {0, 1, 3, 4, 6, 9}, {0, 2, 3, 4, 6, 9},
    {0, 1, 2, 5, 6, 9}, {0, 1, 3, 5, 6, 9}, {1, 2, 3, 5, 6, 9}, {2, 3, 4, 5, 6, 9}, {0, 1, 2, 4, 7, 9},
    {1, 2, 3, 4, 7, 9}, {2, 5, 7, 9}, {0, 1, 3, 5, 7, 9}, {0, 1, 4, 5, 7, 9}, {0, 2, 3, 6, 7, 9},
    {1, 2, 3, 6, 7, 9}, {0, 2, 4, 6, 7, 9}, {1, 3, 4, 6, 7, 9}, {0, 3, 5, 6, 7, 9}, {1, 4, 5, 6, 7, 9},
    {3, 4, 5, 6, 7, 9}, {0, 1, 3, 4, 8, 9}, {1, 2, 3, 4, 8, 9}, {0, 2, 3, 5, 8, 9}, {1, 2, 3, 5, 8, 9},
    {1, 2, 4, 5, 8, 9}, {0, 3, 4, 5, 8, 9}, {0, 1, 2, 6, 8, 9}, {3, 6, 8, 9}, {0, 1, 4, 6, 8, 9},
    {0, 2, 5, 6, 8, 9}, {1, 4, 5, 6, 8, 9}, {2, 4, 5, 6, 8, 9}, {0, 1, 2, 7, 8, 9}, {0, 1, 3, 7, 8, 9},
    {0, 2, 3, 7, 8, 9}, {2, 3, 4, 7, 8, 9}, {1, 3, 5, 7, 8, 9}, {0, 4, 5, 7, 8, 9}, {3, 4, 5, 7, 8, 9},
    {1, 2, 6, 7, 8, 9}, {0, 4, 6, 7, 8, 9}, {2, 4, 6, 7, 8, 9}, {0, 5, 6, 7, 8, 9}, {1, 5, 6, 7, 8, 9} }

theorem base_card : base.card = 75 := by decide +kernel

theorem base_sub : ∀ A ∈ base, A ⊆ range 10 := by decide +kernel

theorem base_fiber_card (b₀ b₁ : Bool) :
    (base.filter (fun A => decide (0 ∈ A) = b₀ ∧ decide (1 ∈ A) = b₁)).card =
      (match b₀,b₁ with | false,false => 11 | true,true => 24 | _,_ => 20) := by
  cases b₀ <;> cases b₁ <;> decide +kernel

/-- Relabel the edges by a swap of adjacent vertices of the complete graph. -/
private def edgeSwap : Fin 4 → Equiv.Perm ℕ :=
  ![((Equiv.swap 1 4).trans (Equiv.swap 2 5)).trans (Equiv.swap 3 6),
    ((Equiv.swap 0 1).trans (Equiv.swap 5 7)).trans (Equiv.swap 6 8),
    ((Equiv.swap 1 2).trans (Equiv.swap 4 5)).trans (Equiv.swap 8 9),
    ((Equiv.swap 2 3).trans (Equiv.swap 5 6)).trans (Equiv.swap 7 8)]

private def move (i : Fin 4) (A : Finset ℕ) : Finset ℕ :=
  A.map (edgeSwap i).toEmbedding

set_option maxRecDepth 20000 in
private theorem move_base : ∀ i : Fin 4, base.image (move i) = base := by decide +kernel

private def representative : Fin 3 → Finset ℕ := ![{0, 1, 2, 3}, {1, 2, 3, 4, 5, 6}, {3, 4, 5, 7, 8, 9}]

private def orbitWords : Finset (Fin 3 × List (Fin 4)) :=
  { (0, []), (0, [0]), (0, [0, 1]), (0, [0, 1, 2]),
    (0, [0, 1, 2, 3]), (1, []), (1, [1]), (1, [1, 0]),
    (1, [1, 2]), (1, [1, 0, 2]), (1, [1, 2, 3]), (1, [1, 0, 2, 1]),
    (1, [1, 0, 2, 3]), (1, [1, 0, 2, 1, 3]), (1, [1, 0, 2, 1, 3, 2]), (2, []),
    (2, [0]), (2, [1]), (2, [3]), (2, [0, 1]),
    (2, [0, 3]), (2, [1, 0]), (2, [1, 2]), (2, [1, 3]),
    (2, [3, 2]), (2, [0, 1, 0]), (2, [0, 1, 2]), (2, [0, 1, 3]),
    (2, [0, 3, 2]), (2, [1, 0, 2]), (2, [1, 0, 3]), (2, [1, 2, 3]),
    (2, [1, 3, 2]), (2, [3, 2, 1]), (2, [0, 1, 0, 2]), (2, [0, 1, 0, 3]),
    (2, [0, 1, 2, 3]), (2, [0, 1, 3, 2]), (2, [0, 3, 2, 1]), (2, [1, 0, 2, 1]),
    (2, [1, 0, 2, 3]), (2, [1, 0, 3, 2]), (2, [1, 2, 3, 2]), (2, [1, 3, 2, 1]),
    (2, [3, 2, 1, 0]), (2, [0, 1, 0, 2, 1]), (2, [0, 1, 0, 2, 3]), (2, [0, 1, 0, 3, 2]),
    (2, [0, 1, 2, 3, 2]), (2, [0, 1, 3, 2, 1]), (2, [0, 3, 2, 1, 0]), (2, [1, 0, 2, 1, 3]),
    (2, [1, 0, 2, 3, 2]), (2, [1, 0, 3, 2, 1]), (2, [1, 2, 3, 2, 1]), (2, [1, 3, 2, 1, 0]),
    (2, [0, 1, 0, 2, 1, 3]), (2, [0, 1, 0, 2, 3, 2]), (2, [0, 1, 0, 3, 2, 1]), (2, [0, 1, 2, 3, 2, 1]),
    (2, [0, 1, 3, 2, 1, 0]), (2, [1, 0, 2, 1, 3, 2]), (2, [1, 0, 2, 3, 2, 1]), (2, [1, 0, 3, 2, 1, 0]),
    (2, [1, 2, 3, 2, 1, 0]), (2, [0, 1, 0, 2, 1, 3, 2]), (2, [0, 1, 0, 2, 3, 2, 1]), (2, [0, 1, 0, 3, 2, 1, 0]),
    (2, [0, 1, 2, 3, 2, 1, 0]), (2, [1, 0, 2, 1, 3, 2, 1]), (2, [1, 0, 2, 3, 2, 1, 0]), (2, [0, 1, 0, 2, 1, 3, 2, 1]),
    (2, [0, 1, 0, 2, 3, 2, 1, 0]), (2, [1, 0, 2, 1, 3, 2, 1, 0]), (2, [0, 1, 0, 2, 1, 3, 2, 1, 0]) }

private def realize (p : Fin 3 × List (Fin 4)) : Finset ℕ :=
  p.2.foldl (fun A i => move i A) (representative p.1)

set_option maxRecDepth 20000 in
private theorem orbit_covers : orbitWords.image realize = base := by decide +kernel

private def RigidAt (A : Finset ℕ) : Prop :=
  ∀ B ∈ base, ∀ C ∈ base, A ∩ B = A ∩ C → A ∩ B = B ∩ C → A = B ∧ B = C

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem rigid_star : RigidAt (representative 0) := by unfold RigidAt; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem rigid_bipartite : RigidAt (representative 1) := by unfold RigidAt; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem rigid_chair_complement : RigidAt (representative 2) := by unfold RigidAt; decide +kernel

private theorem rigid_representative (i : Fin 3) : RigidAt (representative i) := by
  fin_cases i
  · exact rigid_star
  · exact rigid_bipartite
  · exact rigid_chair_complement

private theorem rigid_move {A : Finset ℕ} (i : Fin 4) (hA : RigidAt A) :
    RigidAt (move i A) := by
  intro B hB C hC h₁ h₂
  rw [← move_base i] at hB hC
  obtain ⟨B', hB', rfl⟩ := mem_image.1 hB
  obtain ⟨C', hC', rfl⟩ := mem_image.1 hC
  unfold move at h₁ h₂ ⊢
  simp only [← map_inter, Finset.map_inj] at h₁ h₂ ⊢
  exact hA B' hB' C' hC' h₁ h₂

private theorem rigid_word (w : List (Fin 4)) {A : Finset ℕ} (hA : RigidAt A) :
    RigidAt (w.foldl (fun B i => move i B) A) := by
  induction w generalizing A with
  | nil => exact hA
  | cons i w ih => exact ih (rigid_move i hA)

theorem base_rigid :
    ∀ A ∈ base, ∀ B ∈ base, ∀ C ∈ base, A ∩ B = A ∩ C → A ∩ B = B ∩ C →
      A = B ∧ B = C := by
  intro A hA
  rw [← orbit_covers] at hA
  obtain ⟨p, _, rfl⟩ := mem_image.1 hA
  exact rigid_word p.2 (rigid_representative p.1)

end LcmBase75

/-
The two-port product from Deuber, Erdős, Gunderson, Kostochka and Meyer,
*Intersection Statements for Systems of Sets*, Lemma 4.4
(https://kostochk.web.illinois.edu/docs/old/jcta97degm.pdf).
-/

namespace SunflowerGlue856

open Finset

/-- Equality of the three pairwise intersections forces equality of all three sets. -/
def Rigid {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F, A ∩ B = A ∩ C → A ∩ B = B ∩ C → A = B ∧ B = C

/-- Port-membership class of a family. -/
def fiber {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (a : α) (b : Bool) :
    Finset (Finset α) := F.filter (fun A => decide (a ∈ A) = b)

private theorem rigid_anti {α : Type*} [DecidableEq α] {F : Finset (Finset α)}
    (h : Rigid F) {A B : Finset α} (hA : A ∈ F) (hB : B ∈ F) (hab : A ⊆ B) : A = B :=
  (h A hA A hA B hB (by simp [inter_eq_left.mpr hab])
    (by simp [inter_eq_left.mpr hab])).2

private theorem erase_inj {α : Type*} [DecidableEq α] {F : Finset (Finset α)}
    (h : Rigid F) {A B : Finset α} (hA : A ∈ F) (hB : B ∈ F) {a : α}
    (he : A.erase a = B.erase a) : A = B := by
  have hs (U V : Finset α) (hUV : U.erase a = V.erase a) (ha : a ∉ U ∨ a ∈ V) : U ⊆ V := by
    intro x hx
    by_cases hx' : x = a
    · subst x
      exact ha.resolve_left (not_not_intro hx)
    · have hh : x ∈ V.erase a := hUV ▸ mem_erase.mpr ⟨hx', hx⟩
      exact mem_of_mem_erase hh
  by_cases ha : a ∈ A
  · exact (rigid_anti h hB hA (hs B A he.symm (Or.inr ha))).symm
  · exact rigid_anti h hA hB (hs A B he (Or.inl ha))

private def joinSet {α : Type*} [DecidableEq α] (a b : α) (p : Finset α × Finset α) :=
  p.1.erase a ∪ p.2.erase b

private def joinPairs {α : Type*} [DecidableEq α]
    (F G : Finset (Finset α)) (a b : α) :=
  (F ×ˢ G).filter (fun p => decide (a ∈ p.1) = !(decide (b ∈ p.2)))

/-- Delete two ports and combine sets with complementary memberships at the ports. -/
def glue {α : Type*} [DecidableEq α] (F G : Finset (Finset α)) (a b : α) :=
  (joinPairs F G a b).image (joinSet a b)

private theorem joinSet_inter_left {α : Type*} [DecidableEq α] {P Q A B : Finset α}
    (hPQ : Disjoint P Q) (a b : α) (hA : A.erase a ⊆ P) (hB : B.erase b ⊆ Q) :
    joinSet a b (A,B) ∩ P = A.erase a := by
  ext x
  simp only [joinSet, mem_inter, mem_union]
  constructor
  · rintro ⟨hx | hx, hP⟩
    · exact hx
    · exact (Finset.disjoint_left.mp hPQ hP (hB hx)).elim
  · exact fun hx => ⟨Or.inl hx, hA hx⟩

private theorem joinSet_inter_right {α : Type*} [DecidableEq α] {P Q A B : Finset α}
    (hPQ : Disjoint P Q) (a b : α) (hA : A.erase a ⊆ P) (hB : B.erase b ⊆ Q) :
    joinSet a b (A,B) ∩ Q = B.erase b := by
  simpa only [joinSet, union_comm] using joinSet_inter_left hPQ.symm b a hB hA

private theorem joinSet_inj {α : Type*} [DecidableEq α] {P Q : Finset α}
    {F G : Finset (Finset α)} (hPQ : Disjoint P Q)
    (a b : α) (hF : ∀ A ∈ F, A.erase a ⊆ P) (hG : ∀ B ∈ G, B.erase b ⊆ Q)
    (hrF : Rigid F) (hrG : Rigid G) :
    Set.InjOn (joinSet a b) ↑(F ×ˢ G) := by
  rintro ⟨A,B⟩ hx ⟨C,D⟩ hy h
  have hAB : A ∈ F ∧ B ∈ G := mem_product.mp hx
  have hCD : C ∈ F ∧ D ∈ G := mem_product.mp hy
  have hL := congrArg (· ∩ P) h
  have hR := congrArg (· ∩ Q) h
  rw [joinSet_inter_left hPQ a b (hF A hAB.1) (hG B hAB.2),
    joinSet_inter_left hPQ a b (hF C hCD.1) (hG D hCD.2)] at hL
  rw [joinSet_inter_right hPQ a b (hF A hAB.1) (hG B hAB.2),
    joinSet_inter_right hPQ a b (hF C hCD.1) (hG D hCD.2)] at hR
  exact Prod.ext (erase_inj hrF hAB.1 hCD.1 hL) (erase_inj hrG hAB.2 hCD.2 hR)

private theorem lift_inter_eq {α : Type*} [DecidableEq α] {a : α} {A B C D : Finset α}
    (h : A.erase a ∩ B.erase a = C.erase a ∩ D.erase a)
    (ha : (a ∈ A ∧ a ∈ B) ↔ (a ∈ C ∧ a ∈ D)) : A ∩ B = C ∩ D := by
  ext x
  simp only [mem_inter]
  by_cases hx : x = a
  · rwa [hx]
  · have hm : x ∈ A.erase a ∩ B.erase a ↔ x ∈ C.erase a ∩ D.erase a := by rw [h]
    simpa [mem_erase, hx] using hm

private def equalPairBits (a b c : Bool) : Prop :=
  (a && b) = (a && c) ∧ (a && b) = (b && c)

private theorem equalPairBits_or (a b c : Bool) :
    equalPairBits a b c ∨ equalPairBits (!a) (!b) (!c) := by
  cases a <;> cases b <;> cases c <;> simp [equalPairBits]

private theorem rigid_of_bits {α : Type*} [DecidableEq α] {F : Finset (Finset α)}
    (hr : Rigid F) {a : α} {A B C : Finset α} (hA : A ∈ F) (hB : B ∈ F) (hC : C ∈ F)
    (h₁ : A.erase a ∩ B.erase a = A.erase a ∩ C.erase a)
    (h₂ : A.erase a ∩ B.erase a = B.erase a ∩ C.erase a)
    (hbits : equalPairBits (decide (a ∈ A)) (decide (a ∈ B)) (decide (a ∈ C))) :
    A = B ∧ B = C := by
  exact hr A hA B hB C hC
    (lift_inter_eq h₁ (by simpa only [Bool.and_eq_true, decide_eq_true_eq] using
      (iff_of_eq (congrArg (fun t : Bool => t = true) hbits.1))))
    (lift_inter_eq h₂ (by simpa only [Bool.and_eq_true, decide_eq_true_eq] using
      (iff_of_eq (congrArg (fun t : Bool => t = true) hbits.2))))

private theorem glue_rigid {α : Type*} [DecidableEq α] {P Q : Finset α}
    {F G : Finset (Finset α)} (hPQ : Disjoint P Q)
    (a b : α) (hF : ∀ A ∈ F, A.erase a ⊆ P) (hG : ∀ B ∈ G, B.erase b ⊆ Q)
    (hrF : Rigid F) (hrG : Rigid G) :
    Rigid (glue F G a b) := by
  rintro U hU V hV W hW huv huw
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hU
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hV
  obtain ⟨r, hr, rfl⟩ := mem_image.mp hW
  have hp₁ := mem_product.mp (mem_filter.mp hp).1
  have hq₁ := mem_product.mp (mem_filter.mp hq).1
  have hr₁ := mem_product.mp (mem_filter.mp hr).1
  have hp₂ : decide (b ∈ p.2) = !(decide (a ∈ p.1)) := by
    have h := (mem_filter.mp hp).2
    simpa using (congrArg Bool.not h).symm
  have hq₂ : decide (b ∈ q.2) = !(decide (a ∈ q.1)) := by
    have h := (mem_filter.mp hq).2
    simpa using (congrArg Bool.not h).symm
  have hr₂ : decide (b ∈ r.2) = !(decide (a ∈ r.1)) := by
    have h := (mem_filter.mp hr).2
    simpa using (congrArg Bool.not h).symm
  have project (X Y T : Finset α) : (X ∩ Y) ∩ T = (X ∩ T) ∩ (Y ∩ T) := by
    ext; simp only [mem_inter]; tauto
  have hlp : joinSet a b p ∩ P = p.1.erase a :=
    joinSet_inter_left hPQ a b (hF _ hp₁.1) (hG _ hp₁.2)
  have hlq : joinSet a b q ∩ P = q.1.erase a :=
    joinSet_inter_left hPQ a b (hF _ hq₁.1) (hG _ hq₁.2)
  have hlr : joinSet a b r ∩ P = r.1.erase a :=
    joinSet_inter_left hPQ a b (hF _ hr₁.1) (hG _ hr₁.2)
  have hrp : joinSet a b p ∩ Q = p.2.erase b :=
    joinSet_inter_right hPQ a b (hF _ hp₁.1) (hG _ hp₁.2)
  have hrq : joinSet a b q ∩ Q = q.2.erase b :=
    joinSet_inter_right hPQ a b (hF _ hq₁.1) (hG _ hq₁.2)
  have hrr : joinSet a b r ∩ Q = r.2.erase b :=
    joinSet_inter_right hPQ a b (hF _ hr₁.1) (hG _ hr₁.2)
  have hl (hbits : equalPairBits (decide (a ∈ p.1)) (decide (a ∈ q.1)) (decide (a ∈ r.1))) :
      p.1 = q.1 ∧ q.1 = r.1 :=
    rigid_of_bits hrF hp₁.1 hq₁.1 hr₁.1
      (by simpa only [project, hlp, hlq, hlr] using congrArg (· ∩ P) huv)
      (by simpa only [project, hlp, hlq, hlr] using congrArg (· ∩ P) huw) hbits
  have hright (hbits : equalPairBits
      (decide (b ∈ p.2)) (decide (b ∈ q.2)) (decide (b ∈ r.2))) :
      p.2 = q.2 ∧ q.2 = r.2 :=
    rigid_of_bits hrG hp₁.2 hq₁.2 hr₁.2
      (by simpa only [project, hrp, hrq, hrr] using congrArg (· ∩ Q) huv)
      (by simpa only [project, hrp, hrq, hrr] using congrArg (· ∩ Q) huw) hbits
  have hb : (p.1 = q.1 ∧ q.1 = r.1) ∧ (p.2 = q.2 ∧ q.2 = r.2) := by
    rcases equalPairBits_or (decide (a ∈ p.1)) (decide (a ∈ q.1)) (decide (a ∈ r.1))
      with hbits | hbits
    · obtain ⟨h₁,h₂⟩ := hl hbits
      refine ⟨⟨h₁,h₂⟩, hright ?_⟩
      simp [equalPairBits, hp₂, hq₂, hr₂, h₁, h₂]
    · have hbits' : equalPairBits (decide (b ∈ p.2)) (decide (b ∈ q.2)) (decide (b ∈ r.2)) :=
        by simpa only [hp₂, hq₂, hr₂] using hbits
      obtain ⟨h₁,h₂⟩ := hright hbits'
      refine ⟨hl ?_, ⟨h₁,h₂⟩⟩
      have hnot (x y : Bool) (h : x = !y) : y = !x := by simp [h]
      simp [equalPairBits, hnot _ _ hp₂, hnot _ _ hq₂, hnot _ _ hr₂, h₁, h₂]
  obtain ⟨h₁,h₂⟩ := hb
  exact ⟨congrArg (joinSet a b) (Prod.ext h₁.1 h₂.1),
    congrArg (joinSet a b) (Prod.ext h₁.2 h₂.2)⟩


private theorem glue_fiber_card {α : Type*} [DecidableEq α] {P Q : Finset α}
    {F G : Finset (Finset α)} (hPQ : Disjoint P Q)
    (a b c : α) (hF : ∀ A ∈ F, A.erase a ⊆ P) (hG : ∀ B ∈ G, B.erase b ⊆ Q)
    (hrF : Rigid F) (hrG : Rigid G) (hcQ : c ∈ Q) (hcb : c ≠ b) (v : Bool) :
    (fiber (glue F G a b) c v).card =
      (fiber F a false).card * (fiber (fiber G b true) c v).card +
        (fiber F a true).card * (fiber (fiber G b false) c v).card := by
  rw [fiber, glue, filter_image, card_image_of_injOn]
  · have he :
        (joinPairs F G a b).filter (fun p => decide (c ∈ joinSet a b p) = v) =
          (fiber F a false ×ˢ fiber (fiber G b true) c v) ∪
            (fiber F a true ×ˢ fiber (fiber G b false) c v) := by
      ext p
      rcases p with ⟨A,B⟩
      simp only [joinPairs, fiber, mem_filter, mem_product, mem_union]
      by_cases hA : A ∈ F
      · have hca : c ∉ A.erase a :=
          fun hm => Finset.disjoint_left.mp hPQ (hF A hA hm) hcQ
        have hmem : c ∈ joinSet a b (A,B) ↔ c ∈ B := by
          simp only [joinSet, mem_union, hca, false_or, mem_erase]
          exact ⟨And.right, fun hx => ⟨hcb, hx⟩⟩
        simp only [hmem, hA, true_and]
        cases h₁ : decide (a ∈ A) <;> cases h₂ : decide (b ∈ B) <;>
          simp
      · simp [hA]
    have hd : Disjoint (fiber F a false ×ˢ fiber (fiber G b true) c v)
        (fiber F a true ×ˢ fiber (fiber G b false) c v) := by
      refine Finset.disjoint_left.mpr ?_
      intro p hp hq
      have h₁ := (mem_filter.mp (mem_product.mp hp).1).2
      have h₂ := (mem_filter.mp (mem_product.mp hq).1).2
      exact Bool.false_ne_true (h₁.symm.trans h₂)
    rw [he, card_union_of_disjoint hd, card_product, card_product]
  · exact (joinSet_inj hPQ a b hF hG hrF hrG).mono
      (fun _ hp => (mem_filter.mp (mem_filter.mp hp).1).1)

private theorem relabel_inj {α β : Type*} [DecidableEq α] [DecidableEq β]
    {P : Finset α} {F : Finset (Finset α)} (hF : ∀ A ∈ F, A ⊆ P)
    {e : α → β} (he : Set.InjOn e ↑P) : Set.InjOn (Finset.image e) ↑F :=
  fun A hA B hB => (image_eq_image_iff_of_injOn he (hF A hA) (hF B hB)).mp

private theorem relabel_rigid {α β : Type*} [DecidableEq α] [DecidableEq β]
    {P : Finset α} {F : Finset (Finset α)} (hF : ∀ A ∈ F, A ⊆ P)
    {e : α → β} (he : Set.InjOn e ↑P) (hr : Rigid F) : Rigid (F.image (Finset.image e)) := by
  rintro U hU V hV W hW h₁ h₂
  obtain ⟨A,hA,rfl⟩ := mem_image.mp hU
  obtain ⟨B,hB,rfl⟩ := mem_image.mp hV
  obtain ⟨C,hC,rfl⟩ := mem_image.mp hW
  have hi (A B : Finset α) (hA : A ∈ F) (hB : B ∈ F) :
      (A ∩ B).image e = A.image e ∩ B.image e :=
    image_inter_of_injOn A B (he.mono (by
      intro x hx
      exact hx.elim (fun ha => hF A hA ha) (fun hb => hF B hB hb)))
  have hAB : A ∩ B ⊆ P := inter_subset_left.trans (hF A hA)
  have hAC : A ∩ C ⊆ P := inter_subset_left.trans (hF A hA)
  have hBC : B ∩ C ⊆ P := inter_subset_left.trans (hF B hB)
  obtain ⟨hab,hbc⟩ := hr A hA B hB C hC
    ((image_eq_image_iff_of_injOn he hAB hAC).mp (by rw [hi A B hA hB, hi A C hA hC, h₁]))
    ((image_eq_image_iff_of_injOn he hAB hBC).mp (by rw [hi A B hA hB, hi B C hB hC, h₂]))
  exact ⟨congrArg (Finset.image e) hab, congrArg (Finset.image e) hbc⟩

private theorem relabel_fiber {α β : Type*} [DecidableEq α] [DecidableEq β]
    {P : Finset α} {F : Finset (Finset α)} (hF : ∀ A ∈ F, A ⊆ P)
    {e : α → β} (he : Set.InjOn e ↑P) {a : α} (ha : a ∈ P) (v : Bool) :
    fiber (F.image (Finset.image e)) (e a) v = (fiber F a v).image (Finset.image e) := by
  rw [fiber, filter_image, fiber]
  congr 1
  ext A
  simp only [mem_filter]
  constructor <;> rintro ⟨hA, hv⟩ <;> refine ⟨hA, ?_⟩
  all_goals
    have hm : e a ∈ A.image e ↔ a ∈ A := by
      constructor
      · intro h
        obtain ⟨b,hb,heq⟩ := mem_image.mp h
        exact (he (hF A hA hb) ha heq) ▸ hb
      · exact fun h => mem_image.mpr ⟨a,h,rfl⟩
  · simpa only [hm] using hv
  · simpa only [hm] using hv

private theorem fiber_card_add {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (a : α) :
    (fiber F a false).card + (fiber F a true).card = F.card := by
  rw [fiber, fiber]
  simpa using (card_filter_add_card_filter_not (s := F) (p := fun A => a ∉ A))

private def shiftBase (n t : ℕ) := n + (9 - t)

private theorem shiftBase_inj (n : ℕ) : Set.InjOn (shiftBase n) ↑(range 10) := by
  intro x hx y hy heq
  have hx' : x < 10 := mem_range.mp hx
  have hy' : y < 10 := mem_range.mp hy
  simp only [shiftBase] at heq
  omega

private theorem glue_step (Base : Finset (Finset ℕ)) (hB : ∀ A ∈ Base, A ⊆ range 10)
    (hrB : Rigid Base)
    (ht : ∀ v w : Bool, (fiber (fiber Base 0 v) 1 w).card =
      (match v,w with | false,false => 11 | true,true => 24 | _,_ => 20))
    (n : ℕ) (F : Finset (Finset ℕ)) (hF : ∀ A ∈ F, A ⊆ range (n+1)) (hrF : Rigid F) :
    ∃ G : Finset (Finset ℕ), (∀ A ∈ G, A ⊆ range (n+8+1)) ∧ Rigid G ∧
      (fiber G (n+8) false).card = 20 * (fiber F n false).card +
        11 * (fiber F n true).card ∧
      (fiber G (n+8) true).card = 24 * (fiber F n false).card +
        20 * (fiber F n true).card := by
  let e := shiftBase n
  let B := Base.image (Finset.image e)
  let P := range n
  let Q := (range 10).image e
  have he : Set.InjOn e ↑(range 10) := shiftBase_inj n
  have hB' (A : Finset ℕ) (hA : A ∈ B) : A ⊆ Q := by
    obtain ⟨A',hA',rfl⟩ := mem_image.mp hA
    exact image_mono e (hB A' hA')
  have hrs : Rigid B := relabel_rigid hB he hrB
  have hd : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxQ
    obtain ⟨x',_,rfl⟩ := mem_image.mp hxQ
    have hlt : e x' < n := mem_range.mp hxP
    change n + (9 - x') < n at hlt
    omega
  have he0 : e 0 = n+9 := rfl
  have he1 : e 1 = n+8 := rfl
  have h0 : (0:ℕ) ∈ range 10 := by decide
  have h1 : (1:ℕ) ∈ range 10 := by decide
  have hcount (v w : Bool) : (fiber (fiber B (e 0) v) (e 1) w).card =
      (match v,w with | false,false => 11 | true,true => 24 | _,_ => 20) := by
    have hsub₁ (A : Finset ℕ) (hA : A ∈ fiber Base 0 v) := hB A (mem_filter.mp hA).1
    have hsub₂ (A : Finset ℕ) (hA : A ∈ fiber (fiber Base 0 v) 1 w) :=
      hsub₁ A (mem_filter.mp hA).1
    rw [relabel_fiber hB he h0, relabel_fiber hsub₁ he h1,
      card_image_of_injOn (relabel_inj hsub₂ he), ht]
  have hF' (A : Finset ℕ) (hA : A ∈ F) : A.erase n ⊆ P := by
    intro x hx
    have hne := (mem_erase.mp hx).1
    have hlt := mem_range.mp (hF A hA (mem_of_mem_erase hx))
    exact mem_range.mpr (by omega)
  have hBe (A : Finset ℕ) (hA : A ∈ B) : A.erase (e 0) ⊆ Q :=
    (erase_subset _ _).trans (hB' A hA)
  let G := glue F B n (e 0)
  have he1Q : e 1 ∈ Q := mem_image.mpr ⟨1, h1, rfl⟩
  have hne : e 1 ≠ e 0 := by rw [he1, he0]; omega
  have hs (A : Finset ℕ) (hA : A ∈ G) : A ⊆ range (n+8+1) := by
    obtain ⟨⟨U,V⟩, hp, rfl⟩ := mem_image.mp hA
    have hUV := mem_product.mp (mem_filter.mp hp).1
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · apply mem_range.mpr
      have hx' := mem_range.mp (hF U hUV.1 (mem_of_mem_erase hx))
      omega
    · have hx' := (mem_erase.mp hx).1
      obtain ⟨x',hxx,rfl⟩ := mem_image.mp (hB' V hUV.2 (mem_of_mem_erase hx))
      have hne0 : x' ≠ 0 := fun eq => hx' (congrArg e eq)
      have hlt : x' < 10 := mem_range.mp hxx
      apply mem_range.mpr
      change n+(9-x') < n+8+1
      omega
  refine ⟨G, hs, glue_rigid hd n (e 0) hF' hBe hrF hrs, ?_, ?_⟩
  · rw [← he1, glue_fiber_card hd n (e 0) (e 1) hF' hBe hrF hrs he1Q hne false,
      hcount, hcount]
    change (fiber F n false).card * 20 + (fiber F n true).card * 11 = _
    omega
  · rw [← he1, glue_fiber_card hd n (e 0) (e 1) hF' hBe hrF hrs he1Q hne true,
      hcount, hcount]
    change (fiber F n false).card * 24 + (fiber F n true).card * 20 = _
    omega

private theorem exists_weighted (Base : Finset (Finset ℕ)) (hB : ∀ A ∈ Base, A ⊆ range 10)
    (hrB : Rigid Base)
    (ht : ∀ v w : Bool, (fiber (fiber Base 0 v) 1 w).card =
      (match v,w with | false,false => 11 | true,true => 24 | _,_ => 20)) (j : ℕ) :
    ∃ F : Finset (Finset ℕ), (∀ A ∈ F, A ⊆ range (8*j+1)) ∧ Rigid F ∧
      3 * 36^j ≤ 3 * (fiber F (8*j) false).card + 2 * (fiber F (8*j) true).card := by
  induction j with
  | zero =>
    refine ⟨{∅}, ?_, ?_, ?_⟩
    · simp
    · intro A hA B hB C hC _ _
      simp only [mem_singleton] at hA hB hC
      simp [hA,hB,hC]
    · decide
  | succ j ih =>
    obtain ⟨F,hF,hrF,hW⟩ := ih
    obtain ⟨G,hG,hrG,h₀,h₁⟩ := glue_step Base hB hrB ht (8*j) F hF hrF
    rw [show 8 * (j+1) = 8*j+8 by omega]
    refine ⟨G,hG,hrG,?_⟩
    rw [h₀,h₁,pow_succ]
    omega

/-- Equality of the three pairwise unions forces equality of all three sets. -/
def UnionRigid {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F, A ∪ B = A ∪ C → A ∪ B = B ∪ C → A = B ∧ B = C

private theorem complement_rigid {α : Type*} [Fintype α] [DecidableEq α]
    {F : Finset (Finset α)} (hF : Rigid F) :
    UnionRigid (F.image (fun A => Aᶜ)) := by
  rintro _ hU _ hV _ hW h₁ h₂
  obtain ⟨A,hA,rfl⟩ := mem_image.mp hU
  obtain ⟨B,hB,rfl⟩ := mem_image.mp hV
  obtain ⟨C,hC,rfl⟩ := mem_image.mp hW
  have hab := congrArg (fun D : Finset α => Dᶜ) h₁
  have hbc := congrArg (fun D : Finset α => Dᶜ) h₂
  simp only [Finset.compl_union, compl_compl] at hab hbc
  obtain ⟨hAB,hBC⟩ := hF A hA B hB C hC hab hbc
  simp only [hAB,hBC,and_self]

/-- Iterate the two-port product of a ten-coordinate family, then take complements. -/
theorem exists_family (Base : Finset (Finset ℕ)) (hB : ∀ A ∈ Base, A ⊆ range 10)
    (hrB : Rigid Base)
    (ht : ∀ v w : Bool, (Base.filter (fun A =>
      decide (0 ∈ A) = v ∧ decide (1 ∈ A) = w)).card =
      (match v,w with | false,false => 11 | true,true => 24 | _,_ => 20)) (j : ℕ) :
    ∃ F : Finset (Finset (Fin (8*j+1))), 36^j ≤ F.card ∧ UnionRigid F := by
  have ht' (v w : Bool) := ht v w
  have ht'' (v w : Bool) : (fiber (fiber Base 0 v) 1 w).card =
      (match v,w with | false,false => 11 | true,true => 24 | _,_ => 20) := by
    simpa only [fiber, filter_filter] using ht' v w
  obtain ⟨F,hF,hrF,hW⟩ := exists_weighted Base hB hrB ht'' j
  have hsum := fiber_card_add F (8*j)
  have hcard : 36^j ≤ F.card := by omega
  let e (a : ℕ) : Fin (8*j+1) := ⟨a % (8*j+1), Nat.mod_lt _ (by omega)⟩
  have he : Set.InjOn e ↑(range (8*j+1)) := by
    intro x hx y hy hxy
    have h := congrArg Fin.val hxy
    change x % (8*j+1) = y % (8*j+1) at h
    simpa only [Nat.mod_eq_of_lt (mem_range.mp hx), Nat.mod_eq_of_lt (mem_range.mp hy)] using h
  refine ⟨(F.image (Finset.image e)).image (fun A => Aᶜ), ?_, ?_⟩
  · rw [card_image_of_injective _ compl_injective,
      card_image_of_injOn (relabel_inj hF he)]
    exact hcard
  · exact complement_rigid (relabel_rigid hF he hrF)

end SunflowerGlue856

namespace TangLowerMain

open Finset Filter

theorem exact_of_family
    (hfamily : ∀ j : ℕ, ∃ F : Finset (Finset (Fin (8 * j + 1))),
      36 ^ j ≤ F.card ∧
        ∀ I ∈ F, ∀ J ∈ F, ∀ K ∈ F, I ∪ J = I ∪ K → I ∪ J = J ∪ K → I = J ∧ J = K) :
    type_of% @Erdos856.erdos_856.variants.tang_zhang_three_lower := by
  intro ε hε
  filter_upwards [TangLowerBuckets.eventual_buckets
    ⟨1, TangZhangPrimeMass.prime_mass_lower⟩ ε hε] with N hN
  obtain ⟨j,X,P,hDisj,hPrimes,hMass,hPow,hRate⟩ := hN
  obtain ⟨F,hF,hRigid⟩ := hfamily j
  have hX : 1 ≤ X := by
    let i : Fin (8 * j + 1) := ⟨0, by omega⟩
    have hi : (P i).Nonempty := by
      by_contra h
      have hemp : P i = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      have hh := hMass i
      rw [hemp, sum_empty] at hh
      norm_num at hh
    obtain ⟨p,hp⟩ := hi
    exact (hPrimes i p hp).1.one_lt.le.trans (hPrimes i p hp).2
  have hPow' : X ^ Fintype.card (Fin (8 * j + 1)) ≤ N := by
    simpa only [Fintype.card_fin] using hPow
  have hF' : (36 : ℝ) ^ j ≤ (F.card : ℝ) := by exact_mod_cast hF
  exact hRate.trans (hF'.trans (TangLowerEncoding.lower_of_buckets hX hDisj hPrimes hMass hPow' hRigid))

end TangLowerMain

theorem OMA.solution : type_of% @Erdos856.erdos_856.variants.tang_zhang_three_lower :=
  TangLowerMain.exact_of_family
    (SunflowerGlue856.exists_family LcmBase75.base LcmBase75.base_sub
      LcmBase75.base_rigid LcmBase75.base_fiber_card)