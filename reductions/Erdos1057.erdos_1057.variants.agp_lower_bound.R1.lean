import FormalConjectures.ErdosProblems.«1057»

/-!
# Counting products in the Alford–Granville–Pomerance construction

Prime production and the group exponent estimate in Section 4 of Alford,
Granville and Pomerance, Annals of Mathematics 139 (1994), give a reservoir
of primes with a common multiple M of their predecessors. Every sufficiently
large subset has a nonempty subproduct equal to one modulo M. In the paper
M = kL. All reservoir primes are already one modulo k, and the group
argument is carried out modulo L, which is coprime to k.

The second hypothesis is the elementary subset-counting step in Proposition
1.2 of the published paper. A t-subset is the union of a maximal product-one
part and an n-subset. Counting those pairs gives the required binomial ratio.
The proof below converts every counted subset to a different Carmichael
number in the requested interval, using Fermat at each of its prime factors.
The prime-support and Fermat arguments follow the infinitude reduction by
@Dugongue and the proof of Korselt sufficiency by @ivillar. Credit: @ZedingZhang.
-/

namespace OMA.R_Erdos1057_erdos_1057_variants_agp_lower_bound_R1

open Finset Filter
open scoped Classical

private lemma support {I : Finset ℕ} (prime : ∀ q ∈ I, q.Prime) {p : ℕ}
    (hp : p.Prime) (dvd : p ∣ ∏ q ∈ I, q) : p ∈ I := by
  obtain ⟨q, hq, pq⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun q => q)).mp dvd
  rwa [(Nat.prime_dvd_prime_iff_eq hp (prime q hq)).mp pq]

private lemma products_injective {S T : Finset ℕ}
    (hs : ∀ p ∈ S, p.Prime) (ht : ∀ p ∈ T, p.Prime)
    (same : (∏ p ∈ S, p) = ∏ p ∈ T, p) : S = T := by
  ext p
  constructor
  · intro hp
    exact support ht (hs p hp) (same ▸ Finset.dvd_prod_of_mem (fun q => q) hp)
  · intro hp
    exact support hs (ht p hp) (same.symm ▸ Finset.dvd_prod_of_mem (fun q => q) hp)

private lemma product_carmichael {S : Finset ℕ} {M : ℕ} (two : 1 < S.card)
    (prime : ∀ p ∈ S, p.Prime) (divides : ∀ p ∈ S, p-1 ∣ M)
    (oneMod : (∏ p ∈ S, p) ≡ 1 [MOD M]) : IsCarmichael (∏ p ∈ S, p) := by
  let N := ∏ p ∈ S, p
  have pos : 0 < N := Finset.prod_pos (fun p hp => (prime p hp).pos)
  obtain ⟨p, hp, q, hq, ne⟩ := Finset.one_lt_card.mp two
  have dp : p ∣ N := Finset.dvd_prod_of_mem _ hp
  have dq : q ∣ N := Finset.dvd_prod_of_mem _ hq
  have big : 1 < N := (prime p hp).one_lt.trans_le (Nat.le_of_dvd pos dp)
  have composite : ¬ N.Prime := by
    intro hn
    exact ne (((Nat.prime_dvd_prime_iff_eq (prime p hp) hn).mp dp).trans
      ((Nat.prime_dvd_prime_iff_eq (prime q hq) hn).mp dq).symm)
  have modDvd : M ∣ N-1 := (Nat.modEq_iff_dvd' (show 1 ≤ N by omega)).mp oneMod.symm
  intro b hb cop
  refine ⟨?_, composite, big⟩
  unfold Nat.ProbablePrime
  apply Finset.prod_primes_dvd _ (fun r hr => (prime r hr).prime)
  intro r hr
  letI : Fact r.Prime := ⟨prime r hr⟩
  have dr : r ∣ N := Finset.dvd_prod_of_mem _ hr
  have nz : (b : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact (prime r hr).not_dvd_one (cop.gcd_eq_one ▸ Nat.dvd_gcd dr h)
  obtain ⟨j, hj⟩ := (divides r hr).trans modDvd
  change r ∣ b^(N-1)-1
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hb), Nat.cast_pow,
    hj, pow_mul, ZMod.pow_card_sub_one_eq_one nz, one_pow, Nat.cast_one, sub_self]

/-- The quantitative prime reservoir and the product-one threshold from AGP Section 4. -/
def H1 : Prop :=
  ∀ᶠ X : ℝ in atTop, ∃ (M b n t : ℕ) (P : Finset ℕ),
    0 < b ∧ n+2 ≤ t ∧ t ≤ P.card ∧ ((b^t : ℕ) : ℝ) ≤ X ∧
    (∀ p ∈ P, p.Prime ∧ p ≤ b ∧ p-1 ∣ M) ∧
    (∀ S ⊆ P, n < S.card → ∃ I ⊆ S, I.Nonempty ∧ (∏ p ∈ I, p) ≡ 1 [MOD M]) ∧
    X^(2/7 : ℝ) * (P.card.choose n : ℝ) < (P.card.choose t : ℝ)

/-- Count distinct product-one subsets of length between t-n and t. -/
def H2 : Prop :=
  ∀ (P : Finset ℕ) (M n t : ℕ), n ≤ t → t ≤ P.card →
    (∀ S ⊆ P, n < S.card → ∃ I ⊆ S, I.Nonempty ∧ (∏ p ∈ I, p) ≡ 1 [MOD M]) →
    P.card.choose t ≤
      (P.powerset.filter (fun I => t-n ≤ I.card ∧ I.card ≤ t ∧
        (∏ p ∈ I, p) ≡ 1 [MOD M])).card * P.card.choose n

theorem main : H1 → H2 → type_of% @Erdos1057.erdos_1057.variants.agp_lower_bound := by
  classical
  intro source count
  filter_upwards [source] with X hx
  obtain ⟨M,b,n,t,P,hb,ht,hr,cap,pr,reserve,ratio⟩ := hx
  let G := P.powerset.filter (fun I => t-n ≤ I.card ∧ I.card ≤ t ∧
    (∏ p ∈ I, p) ≡ 1 [MOD M])
  let val (I : Finset ℕ) := ∏ p ∈ I, p
  have info {I : Finset ℕ} (hi : I ∈ G) :
      I ⊆ P ∧ t-n ≤ I.card ∧ I.card ≤ t ∧ val I ≡ 1 [MOD M] := by
    obtain ⟨sub, h⟩ := Finset.mem_filter.mp hi
    exact ⟨Finset.mem_powerset.mp sub, h⟩
  have inj : Set.InjOn val (↑G : Set (Finset ℕ)) := by
    intro I hi J hj eqn
    exact products_injective (fun p hp => (pr p ((info hi).1 hp)).1)
      (fun p hp => (pr p ((info hj).1 hp)).1) eqn
  have inRange : (↑(G.image val) : Set ℕ) ⊆ {m : ℕ | IsCarmichael m ∧ (m:ℝ) ≤ X} := by
    intro m hm
    obtain ⟨I, hi, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨sub, lo, high, one⟩ := info hi
    refine ⟨product_carmichael (by omega) (fun p hp => (pr p (sub hp)).1)
      (fun p hp => (pr p (sub hp)).2.2) one, ?_⟩
    have lim : val I ≤ b^t := calc
      val I ≤ ∏ _p ∈ I, b := Finset.prod_le_prod' (fun p hp => (pr p (sub hp)).2.1)
      _ = b^I.card := by simp
      _ ≤ b^t := Nat.pow_le_pow_right hb high
    exact (show (val I:ℝ) ≤ (b^t:ℕ) by exact_mod_cast lim).trans cap
  have fin : {m : ℕ | IsCarmichael m ∧ (m:ℝ) ≤ X}.Finite :=
    (Set.finite_Iic ⌊X⌋₊).subset (fun m hm => Nat.le_floor hm.2)
  have cardBound := Set.ncard_le_ncard inRange fin
  rw [Set.ncard_coe_finset, Finset.card_image_of_injOn inj] at cardBound
  have comb : P.card.choose t ≤ G.card * P.card.choose n := count P M n t (by omega) hr reserve
  have scale : (0:ℝ) ≤ (P.card.choose n:ℝ) := Nat.cast_nonneg _
  have strict := ratio.trans_le (show (P.card.choose t:ℝ) ≤ (G.card:ℝ)*(P.card.choose n:ℝ)
    by exact_mod_cast comb)
  have many : X ^ (2/7:ℝ) < (G.card:ℝ) := by
    by_contra! h
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_right h scale)) strict
  exact many.trans_le (by unfold Erdos1057.carmichaelCounting; exact_mod_cast cardBound)

end OMA.R_Erdos1057_erdos_1057_variants_agp_lower_bound_R1
