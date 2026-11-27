import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R2_H2_R1_H2_R1
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- Step Erdos1160.erdos_1160.variants.sum.R2.H2.R1.H2.R1.H1
-- Credit: @gertjanvdgoot

/- Part 1: the pc-presentation bound (from step R3.H1.R1.H2.R1.H1) -/

-- Step Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H2.R1.H1: g(p^a)^6 * p^a <= p^(a^3)
-- Credit: @gertjanvdgoot

/-!
# The pc-presentation bound g(p^n) <= p^(C(n,2)+C(n,3)) = p^((n^3-n)/6)

* `exists_pcData`: every group of order p^n has a central series with factors of order p,
  with chosen elements a k in S k but not in S (k+1).
* `nf_bijective`, `mem_S_iff`, `nf_split`: every element is a unique normal-form product
  a 0 ^ e 0 * ... * a (n-1) ^ e (n-1).
* `rigid`: the codes (coordinates of a k ^ p and of the commutator-type elements) determine
  the group up to isomorphism.
* `T_ncard`, `code_mem_T`: there are p^(C(n,2)+C(n,3)) possible codes.
* `g_le`, `OMA.solution`: injecting isomorphism classes into codes gives the bound.
-/

namespace OMA.PC

instance instNeZeroOfFactPrime (p : ℕ) [hp : Fact p.Prime] : NeZero p := ⟨hp.out.ne_zero⟩

/-- A central series `G = S 0 ≥ S 1 ≥ ... ≥ S n = ⊥` with `|S k| = p^(n-k)`, together with
chosen elements `a k ∈ S k \ S (k+1)` whose `p`-th power lies in `S (k+1)`. -/
structure PCData (p n : ℕ) (G : Type*) [Group G] where
  S : ℕ → Subgroup G
  a : ℕ → G
  S_zero : S 0 = ⊤
  S_anti : ∀ k, S (k + 1) ≤ S k
  card_S : ∀ k ≤ n, Nat.card (S k) = p ^ (n - k)
  a_mem : ∀ k, a k ∈ S k
  a_not_mem : ∀ k < n, a k ∉ S (k + 1)
  pow_mem : ∀ k, a k ^ p ∈ S (k + 1)
  central : ∀ k, ∀ g : G, ∀ x ∈ S k, g * x * g⁻¹ * x⁻¹ ∈ S (k + 1)

variable {p n : ℕ} {G : Type*} [Group G] {H : Type*} [Group H]

/-! ## M1: existence -/

/-- Every group of order `p^n` carries pc data. -/
theorem exists_pcData [Fact p.Prime] [Finite G] (hG : Nat.card G = p ^ n) :
    Nonempty (PCData p n G) := by
  have hp : p.Prime := Fact.out
  induction n generalizing G with
  | zero =>
    exact ⟨{
      S := fun _ => ⊤
      a := fun _ => 1
      S_zero := rfl
      S_anti := fun _ => le_rfl
      card_S := fun k hk => by simp [hG]
      a_mem := fun _ => Subgroup.mem_top _
      a_not_mem := fun k hk => absurd hk (by omega)
      pow_mem := fun _ => Subgroup.mem_top _
      central := fun _ _ _ _ => Subgroup.mem_top _ }⟩
  | succ n ih =>
    -- a central element of order p
    obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow hG (Nat.succ_pos n)
    have hdvd : p ∣ Nat.card (Subgroup.center G) := by
      rw [hk]; exact dvd_pow_self p hk0.ne'
    obtain ⟨⟨z, hzc⟩, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
    rw [Subgroup.orderOf_mk] at hz
    set Z : Subgroup G := Subgroup.zpowers z with hZdef
    have hZc : Z ≤ Subgroup.center G := (Subgroup.zpowers_le).2 hzc
    have : Z.Normal := ⟨fun x hx g => by
      rw [Subgroup.mem_center_iff.1 (hZc hx) g, mul_inv_cancel_right]; exact hx⟩
    have hZcard : Nat.card Z = p := by rw [hZdef, Nat.card_zpowers, hz]
    have hQ : Nat.card (G ⧸ Z) = p ^ n := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
      rw [hG, hZcard, pow_succ] at h
      exact (Nat.eq_of_mul_eq_mul_right hp.pos h).symm
    obtain ⟨dQ⟩ := ih hQ
    have hz1 : z ≠ 1 := by
      intro h; rw [h, orderOf_one] at hz; exact hp.one_lt.ne hz
    have hzZ : z ∈ Z := Subgroup.mem_zpowers z
    have hmk : ∀ x : G, (QuotientGroup.mk' Z x) = (x : G ⧸ Z) := fun _ => rfl
    have cardC : ∀ H : Subgroup (G ⧸ Z),
        Nat.card (H.comap (QuotientGroup.mk' Z)) = p * Nat.card H := by
      intro H
      rw [← hZcard]
      exact QuotientGroup.card_preimage_mk Z (H : Set (G ⧸ Z))
    have hSn : dQ.S n = ⊥ := by
      rw [← Subgroup.card_eq_one, dQ.card_S n le_rfl, Nat.sub_self, pow_zero]
    classical
    refine ⟨{
      S := fun k => if k ≤ n then (dQ.S k).comap (QuotientGroup.mk' Z) else ⊥
      a := fun k => if k < n then (dQ.a k).out else if k = n then z else 1
      S_zero := ?_, S_anti := ?_, card_S := ?_, a_mem := ?_, a_not_mem := ?_,
      pow_mem := ?_, central := ?_ }⟩
    · simp [dQ.S_zero]
    · intro k
      by_cases h1 : k + 1 ≤ n
      · simp only [h1, if_true, show k ≤ n by omega]
        exact Subgroup.comap_mono (dQ.S_anti k)
      · simp only [h1, if_false]; exact bot_le
    · intro k hk
      by_cases h1 : k ≤ n
      · simp only [h1, if_true]
        rw [cardC, dQ.card_S k h1, ← pow_succ']
        congr 1; omega
      · simp only [h1, if_false, Subgroup.card_bot]
        rw [show n + 1 - k = 0 by omega, pow_zero]
    · intro k
      by_cases h1 : k < n
      · simp only [h1, if_true, show k ≤ n by omega, Subgroup.mem_comap, hmk,
          QuotientGroup.out_eq']
        exact dQ.a_mem k
      · by_cases h2 : k = n
        · subst h2
          simp only [lt_irrefl, if_false, if_true, le_rfl, Subgroup.mem_comap, hSn]
          exact (QuotientGroup.eq_one_iff z).2 hzZ
        · simp only [h1, h2, if_false, show ¬ k ≤ n by omega]
          exact Subgroup.one_mem _
    · intro k hk
      by_cases h1 : k < n
      · simp only [h1, if_true, show k + 1 ≤ n by omega, Subgroup.mem_comap, hmk,
          QuotientGroup.out_eq']
        exact dQ.a_not_mem k h1
      · have h2 : k = n := by omega
        subst h2
        simp only [lt_irrefl, if_false, if_true, show ¬ k + 1 ≤ k by omega,
          Subgroup.mem_bot]
        exact hz1
    · intro k
      by_cases h1 : k < n
      · simp only [h1, if_true, show k + 1 ≤ n by omega, Subgroup.mem_comap, hmk]
        rw [QuotientGroup.mk_pow, QuotientGroup.out_eq']
        exact dQ.pow_mem k
      · by_cases h2 : k = n
        · subst h2
          simp only [lt_irrefl, if_false, if_true, show ¬ k + 1 ≤ k by omega,
            Subgroup.mem_bot]
          rw [← hz]; exact pow_orderOf_eq_one z
        · simp only [h1, h2, if_false, show ¬ k + 1 ≤ n by omega, one_pow]
          exact Subgroup.one_mem _
    · intro k g x hx
      by_cases h1 : k + 1 ≤ n
      · simp only [h1, if_true, show k ≤ n by omega, Subgroup.mem_comap] at hx ⊢
        simpa only [map_mul, map_inv] using dQ.central k _ _ hx
      · simp only [h1, if_false, Subgroup.mem_bot]
        have hxZ : x ∈ Z := by
          by_cases h2 : k ≤ n
          · have h3 : k = n := by omega
            subst h3
            simp only [h2, if_true, Subgroup.mem_comap, hSn, Subgroup.mem_bot, hmk] at hx
            exact (QuotientGroup.eq_one_iff x).1 hx
          · simp only [h2, if_false, Subgroup.mem_bot] at hx
            rw [hx]; exact Subgroup.one_mem _
        have hxc : x ∈ Subgroup.center G := hZc hxZ
        rw [Subgroup.mem_center_iff.1 hxc g]
        group

/-! ## M2: normal forms -/

/-- The normal-form product `a 0 ^ e 0 * a 1 ^ e 1 * ... * a (n-1) ^ e (n-1)`. -/
def nf (d : PCData p n G) (e : Fin n → Fin p) : G :=
  (List.ofFn fun i : Fin n => d.a i ^ (e i : ℕ)).prod

lemma S_le (d : PCData p n G) {i j : ℕ} (h : i ≤ j) : d.S j ≤ d.S i :=
  antitone_nat_of_succ_le d.S_anti h

lemma nf_mem_of_zero [Fact p.Prime] (d : PCData p n G) {k : ℕ} (e : Fin n → Fin p)
    (he : ∀ i : Fin n, i.val < k → e i = 0) : nf d e ∈ d.S k := by
  unfold nf
  apply Subgroup.list_prod_mem
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  by_cases hi : i.val < k
  · simp [he i hi]
  · exact Subgroup.pow_mem _ (S_le d (not_lt.mp hi) (d.a_mem i)) _

lemma dvd_of_pow_mem [Fact p.Prime] (d : PCData p n G) {k : ℕ} (hk : k < n) {m : ℕ}
    (hm : d.a k ^ m ∈ d.S (k + 1)) : p ∣ m := by
  have hp : p.Prime := Fact.out
  by_contra h
  have hc : Nat.Coprime m p := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr h)
  apply d.a_not_mem k hk
  have hg := Nat.gcd_eq_gcd_ab m p
  rw [hc.gcd_eq_one, Nat.cast_one] at hg
  have : d.a k = (d.a k ^ m) ^ (Nat.gcdA m p) * (d.a k ^ p) ^ (Nat.gcdB m p) := by
    rw [← zpow_natCast, ← zpow_natCast (d.a k) p, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hg,
      zpow_one]
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hm _) (Subgroup.zpow_mem _ (d.pow_mem k) _)

lemma pow_mul_inj_aux [Fact p.Prime] (d : PCData p n G) {k : ℕ} (hk : k < n) {e₁ e₂ : ℕ}
    (h12 : e₁ ≤ e₂) (h2 : e₂ < p) {y₁ y₂ : G} (hy₁ : y₁ ∈ d.S (k + 1)) (hy₂ : y₂ ∈ d.S (k + 1))
    (h : d.a k ^ e₁ * y₁ = d.a k ^ e₂ * y₂) : e₁ = e₂ := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h12
  rw [pow_add, mul_assoc, mul_right_inj] at h
  have hmem : d.a k ^ c ∈ d.S (k + 1) := by
    have : d.a k ^ c = y₁ * y₂⁻¹ := by rw [h]; group
    rw [this]; exact Subgroup.mul_mem _ hy₁ (Subgroup.inv_mem _ hy₂)
  have := dvd_of_pow_mem d hk hmem
  have hc : c = 0 := Nat.eq_zero_of_dvd_of_lt this (by omega)
  omega

lemma pow_mul_inj [Fact p.Prime] (d : PCData p n G) {k : ℕ} (hk : k < n) {e₁ e₂ : ℕ}
    (h1 : e₁ < p) (h2 : e₂ < p) {y₁ y₂ : G} (hy₁ : y₁ ∈ d.S (k + 1)) (hy₂ : y₂ ∈ d.S (k + 1))
    (h : d.a k ^ e₁ * y₁ = d.a k ^ e₂ * y₂) : e₁ = e₂ := by
  rcases le_total e₁ e₂ with h12 | h12
  · exact pow_mul_inj_aux d hk h12 h2 hy₁ hy₂ h
  · exact (pow_mul_inj_aux d hk h12 h1 hy₂ hy₁ h.symm).symm

lemma update_zero_below [Fact p.Prime] {k : ℕ} (hk : k < n) (f : Fin n → Fin p)
    (hf : ∀ i : Fin n, i.val < k → f i = 0) :
    ∀ i : Fin n, i.val < k + 1 → Function.update f ⟨k, hk⟩ 0 i = 0 := by
  intro i hi
  by_cases hik : i = ⟨k, hk⟩
  · subst hik; simp
  · rw [Function.update_of_ne hik]
    exact hf i (by
      have : i.val ≠ k := fun h' => hik (Fin.ext h')
      omega)

lemma nf_split' [Fact p.Prime] (d : PCData p n G) {k : ℕ} (hk : k < n) (e : Fin n → Fin p)
    (he : ∀ i : Fin n, i.val < k → e i = 0) :
    nf d e = d.a k ^ (e ⟨k, hk⟩ : ℕ) * nf d (Function.update e ⟨k, hk⟩ 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = k + (m + 1) := ⟨n - k - 1, by omega⟩
  have hnat : (Fin.natAdd k (0 : Fin (m + 1))) = ⟨k, hk⟩ := Fin.ext (by simp)
  have h1 : ∀ f : Fin (k + (m + 1)) → Fin p, (∀ i : Fin (k + (m + 1)), i.val < k → f i = 0) →
      (List.ofFn fun i : Fin k =>
        d.a ↑(i.castLE (Nat.le_add_right k (m + 1))) ^
          (f (i.castLE (Nat.le_add_right k (m + 1))) : ℕ)).prod = 1 := by
    intro f hf
    apply List.prod_eq_one
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    simp [hf (i.castLE (Nat.le_add_right k (m + 1))) i.isLt]
  unfold nf
  rw [List.ofFn_add (n := k) (m := m + 1), List.ofFn_add (n := k) (m := m + 1), List.prod_append, List.prod_append, h1 e he,
    h1 _ (fun i hi => update_zero_below hk e he i (by omega)), one_mul, one_mul,
    List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, hnat]
  simp only [Function.update_self, Fin.val_zero, pow_zero, one_mul]
  congr 2
  refine congrArg List.ofFn (funext fun i => ?_)
  rw [Function.update_of_ne]
  intro h
  have := congrArg Fin.val h
  simp at this

lemma nf_injective_aux [Fact p.Prime] (d : PCData p n G) :
    ∀ j k : ℕ, j + k = n → ∀ e e' : Fin n → Fin p, (∀ i : Fin n, i.val < k → e i = 0) →
      (∀ i : Fin n, i.val < k → e' i = 0) → nf d e = nf d e' → e = e' := by
  intro j
  induction j with
  | zero =>
    intro k hk e e' he he' _
    funext i
    rw [he i (by omega), he' i (by omega)]
  | succ j ih =>
    intro k hjk e e' he he' h
    have hk : k < n := by omega
    rw [nf_split' d hk e he, nf_split' d hk e' he'] at h
    have hu := fun f hf => update_zero_below (p := p) hk f hf
    have hek := pow_mul_inj d hk (e ⟨k, hk⟩).isLt (e' ⟨k, hk⟩).isLt
      (nf_mem_of_zero d _ (hu e he)) (nf_mem_of_zero d _ (hu e' he')) h
    rw [hek, mul_right_inj] at h
    have hupd := ih (k + 1) (by omega) _ _ (hu e he) (hu e' he') h
    funext i
    by_cases hik : i = ⟨k, hk⟩
    · subst hik; exact Fin.ext hek
    · have := congrFun hupd i
      rwa [Function.update_of_ne hik, Function.update_of_ne hik] at this

theorem nf_bijective [Fact p.Prime] [Finite G] (d : PCData p n G) :
    Function.Bijective (nf d) := by
  refine Function.Injective.bijective_of_nat_card_le
    (fun e e' h => nf_injective_aux d n 0 (by omega) e e' (by simp) (by simp) h) ?_
  have := d.card_S 0 (Nat.zero_le _)
  rw [d.S_zero, Subgroup.card_top] at this
  rw [this]
  simp

theorem mem_S_iff [Fact p.Prime] [Finite G] (d : PCData p n G) {k : ℕ} (hk : k ≤ n)
    (e : Fin n → Fin p) : nf d e ∈ d.S k ↔ ∀ i : Fin n, i.val < k → e i = 0 := by
  constructor
  · intro h
    induction k with
    | zero => intro i hi; omega
    | succ k ih =>
      have hk' : k < n := by omega
      have hz := ih (by omega) (S_le d (Nat.le_succ k) h)
      have hsplit := nf_split' d hk' e hz
      have hy := nf_mem_of_zero d _ (update_zero_below hk' e hz)
      have hmem : d.a k ^ (e ⟨k, hk'⟩ : ℕ) ∈ d.S (k + 1) := by
        have : d.a k ^ (e ⟨k, hk'⟩ : ℕ) =
            nf d e * (nf d (Function.update e ⟨k, hk'⟩ 0))⁻¹ := by
          rw [hsplit]; group
        rw [this]; exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ hy)
      have hek : e ⟨k, hk'⟩ = 0 :=
        Fin.ext (Nat.eq_zero_of_dvd_of_lt (dvd_of_pow_mem d hk' hmem) (e _).isLt)
      intro i hi
      by_cases hik : i.val < k
      · exact hz i hik
      · have : i = ⟨k, hk'⟩ := Fin.ext (by simp; omega)
        rw [this, hek]
  · exact nf_mem_of_zero d e

theorem nf_split [Fact p.Prime] (d : PCData p n G) {k : ℕ} (hk : k < n) (e : Fin n → Fin p)
    (he : ∀ i : Fin n, i.val < k → e i = 0) :
    nf d e = d.a k ^ (e ⟨k, hk⟩ : ℕ) * nf d (Function.update e ⟨k, hk⟩ 0) :=
  nf_split' d hk e he


/-- Coordinates: the inverse of `nf`. -/
noncomputable def coord [Fact p.Prime] [Finite G] (d : PCData p n G) : G → (Fin n → Fin p) :=
  (Equiv.ofBijective _ (nf_bijective d)).symm

/-! ## The code of pc data -/

/-- The code space: power codes and commutator codes, as coordinate vectors. -/
abbrev Code (p n : ℕ) := (Fin n → Fin n → Fin p) × (Fin n → Fin n → Fin n → Fin p)

/-- The code: coordinates of `a i ^ p`, and for `i < j` of `(a j)⁻¹ * ((a i)⁻¹ * a j * a i)`. -/
noncomputable def code [Fact p.Prime] [Finite G] (d : PCData p n G) : Code p n :=
  (fun i => coord d (d.a i ^ p),
   fun i j => if i < j then coord d ((d.a j)⁻¹ * ((d.a i)⁻¹ * d.a j * d.a i)) else 0)

/-- The codes that can occur. -/
def T (p n : ℕ) [Fact p.Prime] : Set (Code p n) :=
  {c | (∀ i t : Fin n, t.val ≤ i.val → c.1 i t = 0) ∧
       (∀ i j t : Fin n, (¬ i < j ∨ t.val ≤ j.val) → c.2 i j t = 0)}

/-! ## M3: rigidity -/


section RigidHelpers

theorem nf_coord [Fact p.Prime] [Finite G] (d : PCData p n G) (g : G) : nf d (coord d g) = g :=
  Equiv.ofBijective_apply_symm_apply _ (nf_bijective d) g

theorem coord_nf [Fact p.Prime] [Finite G] (d : PCData p n G) (e : Fin n → Fin p) :
    coord d (nf d e) = e :=
  Equiv.ofBijective_symm_apply_apply _ (nf_bijective d) e

theorem nf_zero [Fact p.Prime] (d : PCData p n G) : nf d 0 = 1 := by
  simp [nf]

theorem coord_one [Fact p.Prime] [Finite G] (d : PCData p n G) : coord d 1 = 0 := by
  rw [← nf_zero d, coord_nf]

theorem mem_S_coord [Fact p.Prime] [Finite G] (d : PCData p n G) {k : ℕ} (hk : k ≤ n) (x : G) :
    x ∈ d.S k ↔ ∀ i : Fin n, i.val < k → coord d x i = 0 := by
  conv_lhs => rw [← nf_coord d x]
  exact mem_S_iff d hk _

theorem eq_one_of_mem_S_n [Fact p.Prime] [Finite G] (d : PCData p n G) {x : G}
    (hx : x ∈ d.S n) : x = 1 := by
  have h := (mem_S_coord d le_rfl x).1 hx
  have : coord d x = 0 := funext fun i => h i i.isLt
  rw [← nf_coord d x, this, nf_zero]

theorem upd_zero_vanish {k : ℕ} (hk : k < n) (c : Fin n → Fin p) [NeZero p]
    (hc : ∀ i : Fin n, i.val < k → c i = 0) :
    ∀ i : Fin n, i.val ≤ k → Function.update c ⟨k, hk⟩ 0 i = 0 := by
  intro i hi
  by_cases h : i = ⟨k, hk⟩
  · subst h; simp
  · rw [Function.update_of_ne h]
    exact hc i (by have : i.val ≠ k := fun h' => h (Fin.ext h'); omega)

theorem nf_update [Fact p.Prime] (d : PCData p n G) {k : ℕ} (hk : k < n) (c : Fin n → Fin p)
    (hc : ∀ i : Fin n, i.val ≤ k → c i = 0) (v : ℕ) (hv : v < p) :
    nf d (Function.update c ⟨k, hk⟩ ⟨v, hv⟩) = d.a k ^ v * nf d c := by
  rw [nf_split d hk _ (fun i hi => ?_)]
  · rw [Function.update_self, Function.update_idem,
      Function.update_eq_self_iff.mpr (hc _ le_rfl).symm]
  · have hne : i ≠ ⟨k, hk⟩ := ne_of_lt (show i < ⟨k, hk⟩ from hi)
    rw [Function.update_of_ne hne]
    exact hc i hi.le

theorem decomp [Fact p.Prime] [Finite G] (d : PCData p n G) {k : ℕ} (hk : k < n) (x : G)
    (hx : x ∈ d.S k) : ∃ v < p, ∃ y ∈ d.S (k + 1), x = d.a k ^ v * y := by
  have hc : ∀ i : Fin n, i.val < k → coord d x i = 0 := (mem_S_coord d hk.le x).1 hx
  have hz := upd_zero_vanish hk (coord d x) hc
  refine ⟨(coord d x ⟨k, hk⟩).val, (coord d x ⟨k, hk⟩).isLt,
    nf d (Function.update (coord d x) ⟨k, hk⟩ 0), ?_, ?_⟩
  · rw [mem_S_iff d hk]
    intro i hi
    exact hz i (by omega)
  · rw [← nf_update d hk _ hz _ (coord d x ⟨k, hk⟩).isLt, Function.update_idem]
    simp [nf_coord]


theorem conj_mem' (d : PCData p n G) (m : ℕ) {x : G} (hx : x ∈ d.S m) (g : G) :
    g⁻¹ * x * g ∈ d.S m := by
  have := (d.S m).mul_mem (d.S_anti m (d.central m g⁻¹ x hx)) hx
  simpa [mul_assoc] using this

theorem conj_pow' (a c : G) (v : ℕ) : (a⁻¹ * c * a) ^ v = a⁻¹ * c ^ v * a := by
  induction v with
  | zero => simp
  | succ v ih => rw [pow_succ, ih, pow_succ]; group

theorem down_ind {P : ℕ → Prop} (k N : ℕ) (hN : P N)
    (hstep : ∀ m, k ≤ m → m < N → P (m + 1) → P m) : ∀ m, k ≤ m → m ≤ N → P m := by
  suffices ∀ d m, N - m = d → k ≤ m → m ≤ N → P m from fun m h1 h2 => this _ m rfl h1 h2
  intro d
  induction d with
  | zero =>
    intro m hd _ hm
    obtain rfl : m = N := by omega
    exact hN
  | succ d ih =>
    intro m hd hkm hm
    exact hstep m hkm (by omega) (ih (m + 1) (by omega) (by omega) (by omega))

/-- The candidate isomorphism. -/
noncomputable def phi [Fact p.Prime] [Finite G] [Finite H] (dG : PCData p n G)
    (dH : PCData p n H) : G → H :=
  fun x => nf dH (coord dG x)

variable [Fact p.Prime] [Finite G] [Finite H] (dG : PCData p n G) (dH : PCData p n H)

theorem phi_one : phi dG dH 1 = 1 := by
  simp only [phi, coord_one, nf_zero]

theorem phi_step {k : ℕ} (hk : k < n) {e : ℕ} (he : e < p) {y : G} (hy : y ∈ dG.S (k + 1)) :
    phi dG dH (dG.a k ^ e * y) = dH.a k ^ e * phi dG dH y := by
  have hc : ∀ i : Fin n, i.val ≤ k → coord dG y i = 0 := fun i hi =>
    (mem_S_coord dG (Nat.succ_le_of_lt hk) y).1 hy i (by omega)
  have h1 := nf_update dG hk (coord dG y) hc e he
  have h2 := nf_update dH hk (coord dG y) hc e he
  rw [nf_coord] at h1
  unfold phi
  rw [← h1, coord_nf, h2]

theorem phi_code_pow (h : code dG = code dH) {k : ℕ} (hk : k < n) :
    phi dG dH (dG.a k ^ p) = dH.a k ^ p := by
  have hc := congrFun (congrArg Prod.fst h) ⟨k, hk⟩
  dsimp only [code] at hc
  exact (congrArg (nf dH) hc).trans (nf_coord dH _)

theorem phi_conj_gen (h : code dG = code dH) {k j : ℕ} (hkj : k < j) (hj : j < n) :
    phi dG dH ((dG.a k)⁻¹ * dG.a j * dG.a k) = (dH.a k)⁻¹ * dH.a j * dH.a k := by
  have hk : k < n := by omega
  have hc := congrFun (congrFun (congrArg Prod.snd h) ⟨k, hk⟩) ⟨j, hj⟩
  dsimp only [code] at hc
  rw [if_pos (show (⟨k, hk⟩ : Fin n) < ⟨j, hj⟩ from hkj),
    if_pos (show (⟨k, hk⟩ : Fin n) < ⟨j, hj⟩ from hkj)] at hc
  have ht : (dG.a j)⁻¹ * ((dG.a k)⁻¹ * dG.a j * dG.a k) ∈ dG.S (j + 1) := by
    have := dG.central j (dG.a k)⁻¹ (dG.a j)⁻¹ (inv_mem (dG.a_mem j))
    rw [← inv_mem_iff]
    convert this using 1
    group
  have h1 : (dG.a k)⁻¹ * dG.a j * dG.a k =
      dG.a j ^ 1 * ((dG.a j)⁻¹ * ((dG.a k)⁻¹ * dG.a j * dG.a k)) := by
    rw [pow_one, mul_inv_cancel_left]
  have h2 : phi dG dH ((dG.a j)⁻¹ * ((dG.a k)⁻¹ * dG.a j * dG.a k)) =
      (dH.a j)⁻¹ * ((dH.a k)⁻¹ * dH.a j * dH.a k) :=
    (congrArg (nf dH) hc).trans (nf_coord dH _)
  rw [h1, phi_step dG dH hj (Fact.out : p.Prime).one_lt ht, h2, pow_one, mul_inv_cancel_left]

theorem hom_base : ∀ x ∈ dG.S n, ∀ x' ∈ dG.S n,
    phi dG dH (x * x') = phi dG dH x * phi dG dH x' := by
  intro x hx x' hx'
  rw [eq_one_of_mem_S_n dG hx, eq_one_of_mem_S_n dG hx', mul_one, phi_one, mul_one]

theorem hom_step (h : code dG = code dH) {k : ℕ} (hk : k < n)
    (ih : ∀ x ∈ dG.S (k + 1), ∀ x' ∈ dG.S (k + 1),
      phi dG dH (x * x') = phi dG dH x * phi dG dH x') :
    ∀ x ∈ dG.S k, ∀ x' ∈ dG.S k, phi dG dH (x * x') = phi dG dH x * phi dG dH x' := by
  have hpow : ∀ w ∈ dG.S (k + 1), ∀ e : ℕ, phi dG dH (w ^ e) = phi dG dH w ^ e := by
    intro w hw e
    induction e with
    | zero => simp [phi_one]
    | succ e ihe => rw [pow_succ, ih _ (pow_mem hw e) _ hw, ihe, pow_succ]
  have hsig : ∀ m, k + 1 ≤ m → m ≤ n → ∀ z ∈ dG.S m,
      phi dG dH ((dG.a k)⁻¹ * z * dG.a k) = (dH.a k)⁻¹ * phi dG dH z * dH.a k := by
    refine down_ind (P := fun m => ∀ z ∈ dG.S m,
      phi dG dH ((dG.a k)⁻¹ * z * dG.a k) = (dH.a k)⁻¹ * phi dG dH z * dH.a k) (k + 1) n ?_ ?_
    · intro z hz
      rw [eq_one_of_mem_S_n dG hz]
      simp [phi_one]
    · intro m hkm hmn ihm z hz
      obtain ⟨v, hv, y, hy, rfl⟩ := decomp dG hmn z hz
      have e1 : (dG.a k)⁻¹ * (dG.a m ^ v * y) * dG.a k =
          ((dG.a k)⁻¹ * dG.a m * dG.a k) ^ v * ((dG.a k)⁻¹ * y * dG.a k) := by
        rw [conj_pow']; group
      have hyk : y ∈ dG.S (k + 1) := S_le dG (by omega) hy
      have hamk : dG.a m ∈ dG.S (k + 1) := S_le dG hkm (dG.a_mem m)
      rw [e1, ih _ (pow_mem (conj_mem' dG _ hamk _) v) _ (conj_mem' dG _ hyk _),
        hpow _ (conj_mem' dG _ hamk _), phi_conj_gen dG dH h (by omega) hmn, ihm y hy,
        phi_step dG dH hmn hv hy, conj_pow']
      group
  have hsig1 := hsig (k + 1) le_rfl hk
  have hsigp : ∀ e : ℕ, ∀ z ∈ dG.S (k + 1),
      phi dG dH ((dG.a k ^ e)⁻¹ * z * dG.a k ^ e) = (dH.a k ^ e)⁻¹ * phi dG dH z * dH.a k ^ e := by
    intro e
    induction e with
    | zero => intro z hz; simp
    | succ e ihe =>
      intro z hz
      have : (dG.a k ^ (e + 1))⁻¹ * z * dG.a k ^ (e + 1) =
          (dG.a k)⁻¹ * ((dG.a k ^ e)⁻¹ * z * dG.a k ^ e) * dG.a k := by
        rw [pow_succ]; group
      rw [this, hsig1 _ (conj_mem' dG _ hz _), ihe z hz, pow_succ]
      group
  intro x hx x' hx'
  obtain ⟨v, hv, y, hy, rfl⟩ := decomp dG hk x hx
  obtain ⟨v', hv', y', hy', rfl⟩ := decomp dG hk x' hx'
  have hw : (dG.a k ^ v')⁻¹ * y * dG.a k ^ v' * y' ∈ dG.S (k + 1) :=
    mul_mem (conj_mem' dG _ hy _) hy'
  have hphiw : phi dG dH ((dG.a k ^ v')⁻¹ * y * dG.a k ^ v' * y') =
      (dH.a k ^ v')⁻¹ * phi dG dH y * dH.a k ^ v' * phi dG dH y' := by
    rw [ih _ (conj_mem' dG _ hy _) _ hy', hsigp v' y hy]
  have e1 : dG.a k ^ v * y * (dG.a k ^ v' * y') =
      dG.a k ^ (v + v') * ((dG.a k ^ v')⁻¹ * y * dG.a k ^ v' * y') := by
    rw [pow_add]; group
  have key : phi dG dH (dG.a k ^ (v + v') * ((dG.a k ^ v')⁻¹ * y * dG.a k ^ v' * y')) =
      dH.a k ^ (v + v') * phi dG dH ((dG.a k ^ v')⁻¹ * y * dG.a k ^ v' * y') := by
    by_cases hlt : v + v' < p
    · exact phi_step dG dH hk hlt hw
    · have e2 : dG.a k ^ (v + v') * ((dG.a k ^ v')⁻¹ * y * dG.a k ^ v' * y') =
          dG.a k ^ (v + v' - p) * (dG.a k ^ p * ((dG.a k ^ v')⁻¹ * y * dG.a k ^ v' * y')) := by
        rw [← mul_assoc (dG.a k ^ (v + v' - p)), ← pow_add, Nat.sub_add_cancel (by omega)]
      rw [e2, phi_step dG dH hk (by omega) (mul_mem (dG.pow_mem k) hw),
        ih _ (dG.pow_mem k) _ hw, phi_code_pow dG dH h hk, ← mul_assoc, ← pow_add,
        Nat.sub_add_cancel (by omega)]
  rw [e1, key, hphiw, phi_step dG dH hk hv hy, phi_step dG dH hk hv' hy', pow_add]
  group

end RigidHelpers

/-- Pc data with equal codes come from isomorphic groups. -/
theorem rigid [Fact p.Prime] [Finite G] [Finite H] (dG : PCData p n G) (dH : PCData p n H)
    (h : code dG = code dH) : Nonempty (G ≃* H) := by
  have h0 := down_ind (P := fun k => ∀ x ∈ dG.S k, ∀ x' ∈ dG.S k,
      phi dG dH (x * x') = phi dG dH x * phi dG dH x') 0 n (hom_base dG dH)
    (fun _ _ hm ih => hom_step dG dH h hm ih) 0 le_rfl (Nat.zero_le n)
  have hmul : ∀ x y : G, phi dG dH (x * y) = phi dG dH x * phi dG dH y := fun x y =>
    h0 x (by rw [dG.S_zero]; exact Subgroup.mem_top x) y (by rw [dG.S_zero]; exact Subgroup.mem_top y)
  have hbij : Function.Bijective (phi dG dH) :=
    (nf_bijective dH).comp (Equiv.ofBijective _ (nf_bijective dG)).symm.bijective
  exact ⟨MulEquiv.ofBijective (⟨phi dG dH, hmul⟩ : G →ₙ* H) hbij⟩


/-! ## M4: counting -/

theorem choose_arith (n : ℕ) : 6 * (n.choose 2 + n.choose 3) + n = n ^ 3 := by
  have h2 : ∀ m : ℕ, 2 * m.choose 2 + m = m ^ 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      nlinarith
  induction n with
  | zero => simp
  | succ m ih =>
    have := h2 m
    rw [Nat.choose_succ_succ m 2, Nat.choose_succ_succ m 1, Nat.choose_one_right]
    nlinarith

theorem code_mem_T [Fact p.Prime] [Finite G] (d : PCData p n G) : code d ∈ T p n := by
  have hnorm : ∀ k (g x : G), x ∈ d.S k → g * x * g⁻¹ ∈ d.S k := by
    intro k g x hx
    have h1 := d.central k g x hx
    have h2 := d.S_anti k h1
    have := (d.S k).mul_mem h2 hx
    simpa [mul_assoc] using this
  have hco : ∀ (x : G) (k : ℕ), k + 1 ≤ n → x ∈ d.S (k + 1) →
      ∀ t : Fin n, t.val ≤ k → coord d x t = 0 := by
    intro x k hk hx t ht
    have h := (mem_S_iff d hk (coord d x)).1 (by
      have : nf d (coord d x) = x := (Equiv.ofBijective _ (nf_bijective d)).apply_symm_apply x
      rw [this]; exact hx)
    exact h t (by omega)
  refine ⟨?_, ?_⟩
  · intro i t ht
    exact hco _ i (by omega) (d.pow_mem i) t (by omega)
  · intro i j t h
    show (if i < j then coord d ((d.a j)⁻¹ * ((d.a i)⁻¹ * d.a j * d.a i)) else 0) t = 0
    by_cases hij : i < j
    · rw [if_pos hij]
      have ht : t.val ≤ j.val := by
        rcases h with h | h
        · exact absurd hij h
        · exact h
      apply hco _ j (by omega) _ t ht
      have hz := d.central j (d.a i)⁻¹ (d.a j) (d.a_mem j)
      have hy := hnorm (j + 1) (d.a j)⁻¹ _ hz
      have : (d.a j)⁻¹ * ((d.a i)⁻¹ * d.a j * (d.a i)⁻¹⁻¹ * (d.a j)⁻¹) * (d.a j)⁻¹⁻¹
          = (d.a j)⁻¹ * ((d.a i)⁻¹ * d.a j * d.a i) := by group
      rw [this] at hy
      exact hy
    · rw [if_neg hij]; rfl

theorem sum_range_choose_two (m : ℕ) : ∑ i ∈ Finset.range m, i = m.choose 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ m 1, Nat.choose_one_right]; ring

theorem sum_range_choose_three (m : ℕ) : ∑ i ∈ Finset.range m, i.choose 2 = m.choose 3 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ m 2]; ring

theorem card_lt_fin (m : ℕ) (j : Fin m) : ∑ i : Fin m, (if i < j then 1 else 0 : ℕ) = j.val := by
  rw [Finset.sum_boole]
  have : (Finset.univ.filter (fun i : Fin m => i < j)) = Finset.Iio j := by
    ext x; simp
  simp [this]

theorem card_pairs (m : ℕ) :
    Fintype.card {x : Fin m × Fin m // x.1 < x.2} = m.choose 2 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  simp only [card_lt_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) m, sum_range_choose_two]

theorem card_triples (m : ℕ) :
    Fintype.card {x : Fin m × Fin m × Fin m // x.1 < x.2.1 ∧ x.2.1 < x.2.2} = m.choose 3 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  have key : ∀ t : Fin m, ∑ i : Fin m, ∑ j : Fin m,
      (if i < j ∧ j < t then 1 else 0 : ℕ) = t.val.choose 2 := by
    intro t
    rw [Finset.sum_comm]
    have : ∀ j : Fin m, ∑ i : Fin m, (if i < j ∧ j < t then 1 else 0 : ℕ)
        = if j < t then j.val else 0 := by
      intro j
      by_cases hj : j < t
      · simp only [hj, and_true, if_true]; exact card_lt_fin m j
      · simp [hj]
    simp only [this]
    simp only [Fin.lt_def]
    rw [Fin.sum_univ_eq_sum_range (fun j => if j < t.val then j else 0) m]
    rw [← sum_range_choose_two, ← Finset.sum_filter]
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext x; simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨by omega, h⟩
  simp only [Fintype.sum_prod_type]
  refine (Finset.sum_congr rfl (fun i _ => Finset.sum_comm)).trans (Finset.sum_comm.trans ?_)
  simp only [key]
  rw [Fin.sum_univ_eq_sum_range (fun i => i.choose 2) m, sum_range_choose_three]

theorem T_ncard [Fact p.Prime] : (T p n).ncard = p ^ (n.choose 2 + n.choose 3) := by
  let Φ : T p n → (({x : Fin n × Fin n // x.1 < x.2}) → Fin p) ×
      (({x : Fin n × Fin n × Fin n // x.1 < x.2.1 ∧ x.2.1 < x.2.2}) → Fin p) :=
    fun c => (fun a => c.1.1 a.1.1 a.1.2, fun b => c.1.2 b.1.1 b.1.2.1 b.1.2.2)
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro c c' h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      apply Subtype.ext
      apply Prod.ext
      · funext i t
        by_cases hit : i < t
        · exact congrFun h1 ⟨(i, t), hit⟩
        · rw [c.2.1 i t (by simpa [not_lt] using hit), c'.2.1 i t (by simpa [not_lt] using hit)]
      · funext i j t
        by_cases hb : i < j ∧ j < t
        · exact congrFun h2 ⟨(i, j, t), hb⟩
        · have : ¬ i < j ∨ t.val ≤ j.val := by
            by_cases hij : i < j
            · right; have := not_and.1 hb hij; simpa [not_lt] using this
            · left; exact hij
          rw [c.2.2 i j t this, c'.2.2 i j t this]
    · rintro ⟨f, g⟩
      refine ⟨⟨(fun i t => if h : i < t then f ⟨(i, t), h⟩ else 0,
        fun i j t => if h : i < j ∧ j < t then g ⟨(i, j, t), h⟩ else 0), ?_, ?_⟩, ?_⟩
      · intro i t ht
        have : ¬ i < t := by simpa [not_lt] using ht
        simp [this]
      · intro i j t h
        have : ¬ (i < j ∧ j < t) := by
          rintro ⟨h1, h2⟩
          rcases h with h | h
          · exact h h1
          · exact absurd h2 (by simpa [not_lt] using h)
        simp [this]
      · apply Prod.ext
        · funext ⟨⟨i, t⟩, h⟩; simp [Φ, h]
        · funext ⟨⟨i, j, t⟩, h⟩; simp [Φ, h]
  rw [← Nat.card_coe_set_eq, Nat.card_congr (Equiv.ofBijective Φ hΦ)]
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_fin, card_pairs, card_triples, pow_add]

end OMA.PC

namespace OMA.PC

open CategoryTheory

/-- The number of groups of order `p^n` is at most the number of codes. -/
theorem g_le (p n : ℕ) [Fact p.Prime] :
    Erdos1160.g (p ^ n) ≤ p ^ (n.choose 2 + n.choose 3) := by
  classical
  rw [← T_ncard (p := p) (n := n)]
  unfold Erdos1160.g
  let f : Quotient (isIsomorphicSetoid FiniteGrp.{0}) → Code p n := fun c =>
    if h : Nat.card c.out = p ^ n then code (exists_pcData h).some else 0
  -- an isomorphism in `FiniteGrp` gives equal cardinalities
  have card_eq : ∀ {X Y : FiniteGrp.{0}}, Nonempty (X ≅ Y) → Nat.card X = Nat.card Y := by
    rintro X Y ⟨e⟩
    exact Nat.card_congr ((forget FiniteGrp).mapIso e).toEquiv
  have out_card : ∀ G : FiniteGrp.{0}, Nat.card G = p ^ n →
      Nat.card (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) G).out = p ^ n := by
    intro G hG
    rw [← hG]
    exact card_eq (Quotient.mk_out (s := isIsomorphicSetoid FiniteGrp.{0}) G)
  refine Set.ncard_le_ncard_of_injOn f ?_ ?_
  · rintro _ ⟨G, hG, rfl⟩
    simp only [f, dif_pos (out_card G hG)]
    exact code_mem_T _
  · rintro _ ⟨G₁, hG₁, rfl⟩ _ ⟨G₂, hG₂, rfl⟩ hf
    simp only [f, dif_pos (out_card G₁ hG₁), dif_pos (out_card G₂ hG₂)] at hf
    obtain ⟨e⟩ := rigid _ _ hf
    rw [← Quotient.out_eq (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) G₁),
      ← Quotient.out_eq (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) G₂)]
    exact Quotient.sound ⟨InducedCategory.isoMk (MulEquiv.toGrpIso e)⟩

end OMA.PC

/- Part 2: Higman lower bound (from step R1.H2.R1.H1) -/

/-!
A direct proof of the Higman-type lower bound for the number of groups of
order 2^m, by counting class-two central extensions over the binary field.
The lower bound and its infinite-subsequence corollary use only this count.
-/

/-! Relating the canonical count of group isomorphism classes to finite
multiplication tables modulo simultaneous relabeling of their entries. -/

namespace Erdos1160.Tables

open CategoryTheory

/-- The group isomorphism classes counted by the upstream function. -/
def orderClasses (n : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = n}

/-- A labeled multiplication table which is realized by a group law. -/
def GroupTable (n : ℕ) :=
  { t : Fin n → Fin n → Fin n // ∃ s : Group (Fin n), s.mul = t }

instance {n : ℕ} : Finite (GroupTable n) := by
  unfold GroupTable
  infer_instance

/-- Bundle a labeled table as a finite group. -/
noncomputable abbrev model {n : ℕ} (t : GroupTable n) : FiniteGrp.{0} :=
  @FiniteGrp.of (Fin n) t.property.choose inferInstance

/-- Evaluate a product using the multiplication of the specified bundled group. -/
def product (G : FiniteGrp) (a b : G) : G := a * b

theorem model_mul {n : ℕ} (t : GroupTable n) (a b : Fin n) :
    product (model t) a b = t.val a b :=
  congrFun (congrFun t.property.choose_spec a) b

/-- The isomorphism class of a labeled table. -/
noncomputable def groupClass {n : ℕ} (t : GroupTable n) :
    Quotient (isIsomorphicSetoid FiniteGrp.{0}) :=
  Quotient.mk _ (model t)

/-- A multiplication-preserving bijection gives an isomorphism in the category
of finite groups. -/
theorem iso_of_mul_equiv {G H : FiniteGrp} (e : G ≃ H)
    (h : ∀ a b, e (product G a b) = product H (e a) (e b)) : Nonempty (G ≅ H) := by
  let f : G ≃* H := { e with map_mul' := h }
  exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) f.toGrpIso⟩

/-- Every group of order n can be labeled with the elements of Fin n. -/
theorem range_groupClass (n : ℕ) : Set.range (@groupClass n) = orderClasses n := by
  ext c
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨model t, Nat.card_fin n, rfl⟩
  · rintro ⟨G, hG, rfl⟩
    let e : Fin n ≃ G := ((Nat.equivFinOfCardPos (α := G) Nat.card_pos.ne').trans
      (finCongr hG)).symm
    let law : Group (Fin n) := e.group
    let t : GroupTable n := ⟨law.mul, law, rfl⟩
    refine ⟨t, Quotient.sound ?_⟩
    apply iso_of_mul_equiv e
    intro a b
    exact (congrArg (fun z => e z) (model_mul t a b)).trans (e.apply_symm_apply (e a * e b))

theorem orderClasses_finite (n : ℕ) : (orderClasses n).Finite := by
  rw [← range_groupClass]
  exact Set.finite_range _

end Erdos1160.Tables

/-!
Counting abstract groups using marked presentations. A finite family may
contain several isomorphic groups. If an isomorphism preserving all marks
determines the parameter, each class has at most as many parameters as
there are ordered tuples of marks in one representative.
-/

namespace Erdos1160.PresentationCount

open CategoryTheory

/-- Count by the fibers of a map between finite types. -/
theorem card_le_of_fiber_bound {A B : Type*} [Finite A] [Finite B] (f : A → B)
    (M : ℕ) (h : ∀ b : B, Nat.card {a : A // f a = b} ≤ M) :
    Nat.card A ≤ Nat.card B * M := by
  classical
  let : Fintype B := Fintype.ofFinite B
  calc
    Nat.card A = ∑ b : B, Nat.card {a : A // f a = b} := by
      rw [← Nat.card_sigma]
      exact (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ ≤ ∑ _b : B, M := Finset.sum_le_sum (fun b _ => h b)
    _ = Nat.card B * M := by simp [Nat.card_eq_fintype_card]

end Erdos1160.PresentationCount

namespace Erdos1160.PresentationCount

open CategoryTheory

/-- If comparisons with one fixed representative have finite codes, and a
code determines the source parameter, the number of isomorphic parameters
in each class is at most the size of the code space. -/
theorem card_le_of_relative_codes {A C : Type*} [Finite A] [Finite C] {n : ℕ}
    (X : A → FiniteGrp.{0}) (hN : ∀ a, Nat.card (X a) = n)
    (code : ∀ a b : A, (X a ≃* X b) → C)
    (sep : ∀ (a b r : A) (e : X a ≃* X r) (f : X b ≃* X r),
      code a r e = code b r f → a = b) :
    Nat.card A ≤ Erdos1160.g n * Nat.card C := by
  classical
  let classOf (a : A) : Tables.orderClasses n := ⟨Quotient.mk _ (X a), X a, hN a, rfl⟩
  let : Finite (Tables.orderClasses n) := (Tables.orderClasses_finite n).to_subtype
  apply card_le_of_fiber_bound classOf (Nat.card C)
  intro c
  let F := {a : A // classOf a = c}
  by_cases hn : Nonempty F
  · let r := Classical.choice hn
    have sameClass (a : F) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (X a.val)
        = Quotient.mk _ (X r.val) :=
      congrArg Subtype.val (a.property.trans r.property.symm)
    let transport (a : F) : X a.val ≃* X r.val :=
      ((inducedFunctor FiniteGrp.toGrp).mapIso
        (Classical.choice (Quotient.exact (sameClass a)))).groupIsoToMulEquiv
    let encode (a : F) : C := code a.val r.val (transport a)
    exact Nat.card_le_card_of_injective encode (fun {a b} h =>
      Subtype.ext (sep a.val b.val r.val (transport a) (transport b) h))
  · have empty : IsEmpty F := not_nonempty_iff.mp hn
    change Nat.card F ≤ Nat.card C
    simp

end Erdos1160.PresentationCount

namespace Erdos1160Growth

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

/-- The central extension built from an arbitrary biadditive map, with two visible coordinates. -/
structure BilinearExtension (B : V →+ V →+ W) where
  base : V
  fiber : W

namespace BilinearExtension

variable {B : V →+ V →+ W}

theorem ext {x y : BilinearExtension B} (hb : x.base = y.base) (hf : x.fiber = y.fiber) : x = y := by
  cases x
  cases y
  simp_all

instance : Mul (BilinearExtension B) :=
  ⟨fun x y => ⟨x.base + y.base, x.fiber + y.fiber + B x.base y.base⟩⟩

instance : One (BilinearExtension B) := ⟨⟨0,0⟩⟩

instance : Inv (BilinearExtension B) :=
  ⟨fun x => ⟨-x.base, -x.fiber + B x.base x.base⟩⟩

@[simp] theorem mul_base (x y : BilinearExtension B) :
    (x*y).base = x.base + y.base := rfl
@[simp] theorem mul_fiber (x y : BilinearExtension B) :
    (x*y).fiber = x.fiber + y.fiber + B x.base y.base := rfl
@[simp] theorem inv_base (x : BilinearExtension B) : (x⁻¹).base = -x.base := rfl
@[simp] theorem inv_fiber (x : BilinearExtension B) :
    (x⁻¹).fiber = -x.fiber + B x.base x.base := rfl
@[simp] theorem one_base : (1 : BilinearExtension B).base = 0 := rfl
@[simp] theorem one_fiber : (1 : BilinearExtension B).fiber = 0 := rfl

instance : Group (BilinearExtension B) where
  mul_assoc x y z := by
    apply BilinearExtension.ext <;> simp [map_add] <;> abel
  one_mul x := by
    apply BilinearExtension.ext <;> simp
  mul_one x := by
    apply BilinearExtension.ext <;> simp
  inv_mul_cancel x := by
    apply BilinearExtension.ext <;> simp

def coordinateEquiv (B : V →+ V →+ W) : BilinearExtension B ≃ V × W where
  toFun x := (x.base, x.fiber)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card (B : V →+ V →+ W) :
    Nat.card (BilinearExtension B) = Nat.card V * Nat.card W := by
  rw [Nat.card_congr (coordinateEquiv B), Nat.card_prod]

open scoped commutatorElement

theorem commutator_formula (x y : BilinearExtension B) :
    ⁅x, y⁆ = ⟨0, B x.base y.base - B y.base x.base⟩ := by
  rw [commutatorElement_def]
  apply BilinearExtension.ext <;> simp [map_add, map_neg]
  abel

end BilinearExtension

end Erdos1160Growth

namespace Erdos1160Growth.BilinearExtension

open scoped commutatorElement

private theorem double_zero {s : ℕ} (w : Fin s → ZMod 2) : w+w = 0 := by
  funext i
  have h : ∀ z : ZMod 2, z+z = 0 := by decide
  exact h (w i)

theorem lift_square_eq_of_base_eq {V : Type*} [AddCommGroup V] {s : ℕ}
    {B : V →+ V →+ (Fin s → ZMod 2)} {a b : BilinearExtension B} (h : a.base = b.base) :
    a * a = b * b := by
  apply BilinearExtension.ext
  · simp only [mul_base, h]
  · simp only [mul_fiber, double_zero, zero_add, h]

theorem lift_commutator_eq_of_base_eq {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    {B : V →+ V →+ W} {a b c d : BilinearExtension B}
    (hac : a.base = c.base) (hbd : b.base = d.base) :
    ⁅a,b⁆ = ⁅c,d⁆ := by
  rw [commutator_formula, commutator_formula, hac, hbd]

end Erdos1160Growth.BilinearExtension

open scoped BigOperators commutatorElement

namespace Erdos1160Growth.SharpFamily

abbrev V (d : ℕ) := Fin d → ZMod 2
abbrev Slot (d s : ℕ) := (Σ i : Fin d, Fin i.val) ⊕ Fin (d-s)
abbrev Param (d s : ℕ) := Slot d s → V s

variable {d s : ℕ}

def basis {k : ℕ} (i : Fin k) : V k := Pi.single i 1

def entry (t : Param d s) (i j : Fin d) : V s :=
  if h : j < i then t (.inl ⟨i, ⟨j.val,h⟩⟩)
  else if i = j then
    if hl : i.val < s then basis ⟨i.val, hl⟩
    else t (.inr ⟨i.val - s, by have := i.isLt; omega⟩)
  else 0

theorem entry_fixed {t : Param d s} (i : Fin s) (hs : s ≤ d) :
    entry t (Fin.castLE hs i) (Fin.castLE hs i) = basis i := by
  simp [entry, i.isLt]

theorem entry_upper {t : Param d s} {i j : Fin d} (h : i < j) : entry t i j = 0 := by
  simp [entry, not_lt_of_ge (le_of_lt h), ne_of_lt h]

theorem entry_injective {t u : Param d s} (h : ∀ i j, entry t i j = entry u i j) : t = u := by
  funext k
  rcases k with ⟨i,j⟩ | k
  · let j' : Fin d := ⟨j.val, j.isLt.trans i.isLt⟩
    have hj : j' < i := j.isLt
    simpa [entry,hj,j'] using h i j'
  · have hk : s + k.val < d := by have := k.isLt; omega
    let i : Fin d := ⟨s + k.val, hk⟩
    have hi : ¬ i.val < s := by simp [i]
    simpa [entry,hi,i] using h i i

def form (t : Param d s) : V d →+ V d →+ V s where
  toFun a :=
    { toFun := fun b k => ∑ i, ∑ j, a i * b j * entry t i j k
      map_zero' := by funext k; simp
      map_add' := by
        intro b c
        funext k
        simp [mul_add, add_mul, Finset.sum_add_distrib] }
  map_zero' := by ext b k; simp
  map_add' := by
    intro a b
    ext c k
    simp [add_mul, Finset.sum_add_distrib]

abbrev G (t : Param d s) := BilinearExtension (form t)

def gen (t : Param d s) (i : Fin d) : G t := ⟨basis i, 0⟩
def Z (t : Param d s) (z : V s) : G t := ⟨0, z⟩

lemma eval_basis (t : Param d s) (i j : Fin d) :
    form t (basis i) (basis j) = entry t i j := by
  funext k
  change (∑ a, ∑ b, basis i a * basis j b * entry t a b k) = _
  simp [basis, Pi.single_apply, ite_mul, mul_ite, Finset.sum_ite_eq']

theorem double_zero {k : ℕ} (v : V k) : v + v = 0 := by
  funext j
  exact (show ∀ x : ZMod 2, x + x = 0 by decide) (v j)

theorem gen_sq (t : Param d s) (i : Fin d) : gen t i * gen t i = Z t (entry t i i) := by
  apply BilinearExtension.ext
  · exact double_zero (basis i)
  · change 0 + 0 + form t (basis i) (basis i) = entry t i i
    rw [zero_add, zero_add, eval_basis]

theorem gen_comm (t : Param d s) (i j : Fin d) (h : j < i) :
    ⁅gen t i, gen t j⁆ = Z t (entry t i j) := by
  rw [BilinearExtension.commutator_formula]
  apply BilinearExtension.ext
  · rfl
  · change form t (basis i) (basis j) - form t (basis j) (basis i) = _
    rw [eval_basis, eval_basis, entry_upper h, sub_zero]
    rfl

theorem Z_injective (t : Param d s) : Function.Injective (Z t) :=
  fun _ _ h => congrArg BilinearExtension.fiber h

theorem Z_add (t : Param d s) (u v : V s) : Z t (u + v) = Z t u * Z t v := by
  apply BilinearExtension.ext <;> simp [Z]

end Erdos1160Growth.SharpFamily

namespace Erdos1160Growth.SharpFamily

open scoped commutatorElement

variable {d s : ℕ}

/-- Two homomorphisms from different presentations that agree on all coordinate fibers
agree on every element of the common central vector space. -/
theorem map_Z_agree {R : Type*} [Group R] {t u : Param d s}
    (e : G t →* R) (f : G u →* R)
    (h : ∀ i : Fin s, e (Z t (basis i)) = f (Z u (basis i))) (w : V s) :
    e (Z t w) = f (Z u w) := by
  have hz : e (Z t 0) = f (Z u 0) := e.map_one.trans f.map_one.symm
  induction w using Pi.single_induction with
  | zero => exact hz
  | add a b ha hb => rw [Z_add, Z_add, map_mul, map_mul, ha, hb]
  | single i x =>
    have bit : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    rcases bit x with rfl | rfl
    · simpa only [Pi.single_zero] using hz
    · exact h i

/-- Projecting the images of the d generators into the elementary abelian quotient
gives a complete code for presentations mapping isomorphically into one fixed target. -/
theorem recover_of_equal_base (hs : s ≤ d) (t u r : Param d s)
    (e : G t ≃* G r) (f : G u ≃* G r)
    (h : ∀ i : Fin d, (e (gen t i)).base = (f (gen u i)).base) : t = u := by
  have hsquare (i : Fin d) : e (Z t (entry t i i)) = f (Z u (entry u i i)) := by
    rw [← gen_sq, ← gen_sq, map_mul, map_mul]
    exact BilinearExtension.lift_square_eq_of_base_eq (h i)
  have hfix (i : Fin s) : e (Z t (basis i)) = f (Z u (basis i)) := by
    simpa only [entry_fixed i hs] using hsquare (Fin.castLE hs i)
  have recover {v w : V s} (hv : e (Z t v) = f (Z u w)) : v = w := by
    have hsame := map_Z_agree e.toMonoidHom f.toMonoidHom hfix v
    exact Z_injective u (f.injective (hsame.symm.trans hv))
  apply entry_injective
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [entry_upper hij, entry_upper hij]
  · exact recover (hsquare i)
  · apply recover
    rw [← gen_comm t i j hji, ← gen_comm u i j hji, map_commutatorElement, map_commutatorElement]
    exact BilinearExtension.lift_commutator_eq_of_base_eq (h i) (h j)

end Erdos1160Growth.SharpFamily

namespace Erdos1160Growth.SharpFamily

theorem triangular_card (d : ℕ) :
    Nat.card ((i : Fin d) × Fin i.val) = d * (d - 1) / 2 := by
  rw [Nat.card_sigma]
  simp only [Nat.card_fin]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) d).trans (Finset.sum_range_id d)

end Erdos1160Growth.SharpFamily

namespace Erdos1160Growth.SharpFamily

private instance {d s : ℕ} (t : Param d s) : Finite (G t) :=
  Finite.of_equiv _ (BilinearExtension.coordinateEquiv (form t)).symm

private def bundled {d s : ℕ} (t : Param d s) : FiniteGrp.{0} := FiniteGrp.of (G t)

private theorem bundled_order {d s : ℕ} (t : Param d s) : Nat.card (bundled t) = 2 ^ (d+s) := by
  change Nat.card (BilinearExtension (form t)) = _
  rw [BilinearExtension.card]
  simp only [V, Nat.card_fun, Nat.card_zmod, Nat.card_fin, pow_add]

theorem parameter_card {d s : ℕ} (hs : s ≤ d) :
    Nat.card (Param d s) = 2 ^ (s * (d * (d - 1) / 2 + d - s)) := by
  change Nat.card (Slot d s → Fin s → ZMod 2) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_fin, ← pow_mul]
  unfold Slot
  rw [Nat.card_sum, triangular_card, Nat.card_fin]
  have h : d * (d - 1) / 2 + (d - s) = d * (d - 1) / 2 + d - s := by omega
  rw [h]

/-- Lower bound from the explicit family with s diagonal squares fixed to a
fiber basis. A comparison with a representative needs only d base vectors
of d bits each. -/
theorem sharp_parameter_lower {d s : ℕ} (hs : s ≤ d) :
    2 ^ (s * (d * (d - 1) / 2 + d - s)) ≤
      Erdos1160.g (2 ^ (d+s)) * 2 ^ (d*d) := by
  let code (a r : Param d s) (e : bundled a ≃* bundled r) (i : Fin d) : V d :=
    (e (gen a i) : G r).base
  have sep (a b r : Param d s) (e : bundled a ≃* bundled r) (f : bundled b ≃* bundled r)
      (h : code a r e = code b r f) : a = b :=
    recover_of_equal_base hs a b r e f (congrFun h)
  have h := Erdos1160.PresentationCount.card_le_of_relative_codes bundled bundled_order code sep
  rw [parameter_card hs] at h
  change _ ≤ _ * Nat.card (Fin d → Fin d → ZMod 2) at h
  simpa only [Nat.card_fun, Nat.card_fin, Nat.card_zmod, ← pow_mul] using h

end Erdos1160Growth.SharpFamily

namespace Erdos1160Growth.SharpFamily

private theorem converted_bound (m d s : ℕ) (hs : s ≤ d) (horder : d+s=m)
    (hexp : 2*m^3 + (d*d)*27 ≤ (s*(d*(d-1)/2+d-s))*27 + 12*m^2) :
    2^(2*m^3) ≤ Erdos1160.g (2^m)^27 * 2^(12*m^2) := by
  have count := Nat.pow_le_pow_left (sharp_parameter_lower hs) 27
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, horder] at count
  apply Nat.le_of_mul_le_mul_right (c := 2^((d*d)*27)) _ (Nat.pow_pos (by decide))
  calc
    2^(2*m^3) * 2^((d*d)*27) = 2^(2*m^3+(d*d)*27) := (pow_add _ _ _).symm
    _ ≤ 2^((s*(d*(d-1)/2+d-s))*27+12*m^2) := Nat.pow_le_pow_right (by decide) hexp
    _ = _ := pow_add _ _ _
    _ ≤ (Erdos1160.g (2^m)^27 * 2^((d*d)*27)) * 2^(12*m^2) :=
      Nat.mul_le_mul_right _ count
    _ = _ := Nat.mul_right_comm _ _ _

private theorem triangle_even (u : ℕ) :
    (2*u)*(2*u-1)/2 = u*(2*u-1) := by
  rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]

private theorem triangle_odd (u : ℕ) :
    (2*u+1)*(2*u+1-1)/2 = (2*u+1)*u := by
  have h : 2*u+1-1 = 2*u := by omega
  rw [h, show (2*u+1)*(2*u) = (2*u+1)*u*2 by ring, Nat.mul_div_cancel _ (by decide)]

/-- The sharp cubic and quadratic terms of Higman's lower bound, with all denominators
cleared and a single estimate valid in each of the three residue classes. -/
theorem higman_lower_all (m : ℕ) (hm : 3 ≤ m) :
    2^(2*m^3) ≤ Erdos1160.g (2^m)^27 * 2^(12*m^2) := by
  let k := m/3-1
  have cases_m : m=3*(k+1) ∨ m=3*(k+1)+1 ∨ m=3*(k+1)+2 := by
    dsimp [k]
    omega
  have even_pred : 2*(k+1)-1 = 2*k+1 := by omega
  rcases cases_m with h | h | h
  · apply converted_bound m (2*(k+1)) (k+1) (by omega) (by omega)
    rw [h, triangle_even, even_pred]
    have sub_id : (k+1)*(2*k+1)+2*(k+1)-(k+1) = (k+1)*(2*k+1)+(k+1) := by omega
    rw [sub_id]
    exact le_of_eq (by ring)
  · apply converted_bound m (2*(k+1)) (k+2) (by omega) (by omega)
    rw [h, triangle_even, even_pred]
    have sub_id : (k+1)*(2*k+1)+2*(k+1)-(k+2) = (k+1)*(2*k+1)+k := by omega
    rw [sub_id]
    apply Nat.le.intro (k := 27*k+10)
    ring
  · apply converted_bound m (2*(k+1)+1) (k+2) (by omega) (by omega)
    rw [h, triangle_odd]
    have sub_id : (2*(k+1)+1)*(k+1)+(2*(k+1)+1)-(k+2) =
        (2*(k+1)+1)*(k+1)+(k+1) := by omega
    rw [sub_id]
    apply Nat.le.intro (k := 18*k+23)
    ring

end Erdos1160Growth.SharpFamily
/- Part 3: nilpotent groups -/

/-!
# Step R2.H2.R1.H1: nilpotent groups with a small Sylow 2-subgroup are few

Frozen interface (statements and definitions must not change):
* N1 `nil_le_prod`: a nilpotent group is the product of its Sylow subgroups, so the number of
  nilpotent classes of order n is at most the product of g(p^a) over the prime powers of n.
* interface `g_pow_six_le` (pc-presentation bound) and `higman` (Higman lower bound): proved in
  other files, used here as black boxes.
* N2 `target`: the step, from the three lemmas above plus arithmetic.
-/

open CategoryTheory

namespace OMA.Nil

/-- Isomorphism classes of nilpotent groups of order `n`. -/
def nilClasses (n : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsNilpotent G}

/-! ## N1 -/

/-- A group structure is determined by its multiplication, so there are finitely many on `Fin n`. -/
theorem finite_groupStr (n : ℕ) : Finite (Group (Fin n)) :=
  Finite.of_injective
    (fun s : Group (Fin n) => @HMul.hMul (Fin n) (Fin n) (Fin n) (@instHMul _ s.toMul))
    (fun _ _ h => Group.ext h)

/-- The isomorphism class of `Fin n` with a given group structure. -/
noncomputable def classOf (n : ℕ) (s : Group (Fin n)) :
    Quotient (isIsomorphicSetoid FiniteGrp.{0}) :=
  Quotient.mk _ (@FiniteGrp.of (Fin n) s inferInstance)

theorem image_subset (n : ℕ) :
    Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' {G : FiniteGrp.{0} | Nat.card G = n}
      ⊆ Set.range (classOf n) := by
  rintro _ ⟨G, hG, rfl⟩
  let e : Fin n ≃ G := ((Finite.equivFin G).trans (finCongr hG)).symm
  let s : Group (Fin n) := e.group
  refine ⟨s, Quotient.sound ⟨?_⟩⟩
  exact InducedCategory.isoMk (MulEquiv.toGrpIso (X := GrpCat.of (Fin n)) (Y := G.toGrp) e.mulEquiv)

theorem classes_finite (n : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = n}).Finite :=
  have := finite_groupStr n
  (Set.finite_range (classOf n)).subset (image_subset n)

theorem mk_eq_iff (G H : FiniteGrp.{0}) :
    Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) G = Quotient.mk _ H ↔ Nonempty (G ≃* H) := by
  constructor
  · intro h
    obtain ⟨i⟩ := Quotient.exact h
    exact ⟨Iso.groupIsoToMulEquiv ((inducedFunctor FiniteGrp.toGrp).mapIso i)⟩
  · rintro ⟨e⟩
    exact Quotient.sound ⟨InducedCategory.isoMk (MulEquiv.toGrpIso (X := G.toGrp) (Y := H.toGrp) e)⟩

theorem nil_iso {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    [Group.IsNilpotent G] [Group.IsNilpotent H] (hc : Nat.card G = Nat.card H)
    (h : ∀ p : (Nat.card G).primeFactors, ∀ (P : Sylow p G) (Q : Sylow p H), Nonempty (P ≃* Q)) :
    Nonempty (G ≃* H) := by
  have eG := Sylow.directProductOfNormal (G := G) (fun _ => inferInstance)
  have eH := Sylow.directProductOfNormal (G := H) (fun _ => inferInstance)
  rw [← hc] at eH
  have key : ∀ p : (Nat.card G).primeFactors,
      Nonempty ((∀ P : Sylow p G, P) ≃* (∀ Q : Sylow p H, Q)) := by
    intro p
    have := Fact.mk (Nat.prime_of_mem_primeFactors p.2)
    let := Sylow.unique_of_normal (default : Sylow p G) inferInstance
    let := Sylow.unique_of_normal (default : Sylow p H) inferInstance
    have e1 := MulEquiv.piUnique (fun P : Sylow p G => ↥(P : Subgroup G))
    have e2 := MulEquiv.piUnique (fun Q : Sylow p H => ↥(Q : Subgroup H))
    exact ⟨e1.trans ((Classical.choice (h p _ _)).trans e2.symm)⟩
  have e := fun p => Classical.choice (key p)
  exact ⟨eG.symm.trans ((MulEquiv.piCongrRight e).trans eH)⟩

/-- The class of a Sylow `p`-subgroup of a representative of `q`. -/
noncomputable def sylClass (q : Quotient (isIsomorphicSetoid FiniteGrp.{0})) (p : ℕ) :
    Quotient (isIsomorphicSetoid FiniteGrp.{0}) :=
  Quotient.mk _ (FiniteGrp.of (default : Sylow p q.out))

theorem out_props {n : ℕ} {q : Quotient (isIsomorphicSetoid FiniteGrp.{0})}
    (hq : q ∈ nilClasses n) : Nat.card q.out = n ∧ Group.IsNilpotent q.out := by
  obtain ⟨G, ⟨hG, hN⟩, rfl⟩ := hq
  obtain ⟨e⟩ := (mk_eq_iff _ _).1 (Quotient.out_eq (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) G))
  exact ⟨(Nat.card_congr e.toEquiv).trans hG, Group.nilpotent_of_mulEquiv e.symm⟩

theorem nil_le_prod (n : ℕ) (hn : 0 < n) :
    (nilClasses n).ncard ≤ ∏ p ∈ n.primeFactors, Erdos1160.g (p ^ n.factorization p) := by
  classical
  let T : n.primeFactors → Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) := fun p =>
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = p.1 ^ n.factorization p.1}
  let f : Quotient (isIsomorphicSetoid FiniteGrp.{0}) →
      (n.primeFactors → Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    fun q p => sylClass q p.1
  have hfin : (Set.univ.pi T).Finite := Set.Finite.pi fun p => classes_finite _
  have hle : (nilClasses n).ncard ≤ (Set.univ.pi T).ncard := by
    refine Set.ncard_le_ncard_of_injOn f ?_ ?_ hfin
    · intro q hq p _
      obtain ⟨hc, _⟩ := out_props hq
      have := Fact.mk (Nat.prime_of_mem_primeFactors p.2)
      refine ⟨_, ?_, rfl⟩
      show Nat.card (default : Sylow p.1 q.out) = _
      rw [Sylow.card_eq_multiplicity, hc]
    · intro q₁ hq₁ q₂ hq₂ hf
      obtain ⟨hc₁, hN₁⟩ := out_props hq₁
      obtain ⟨hc₂, hN₂⟩ := out_props hq₂
      rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂, mk_eq_iff]
      refine nil_iso (hc₁.trans hc₂.symm) ?_
      intro p P Q
      have hp : p.1 ∈ n.primeFactors := hc₁ ▸ p.2
      have := Fact.mk (Nat.prime_of_mem_primeFactors hp)
      let := Sylow.unique_of_normal (default : Sylow p q₁.out) inferInstance
      let := Sylow.unique_of_normal (default : Sylow p q₂.out) inferInstance
      have h1 := congrFun hf ⟨p.1, hp⟩
      obtain ⟨e⟩ := (mk_eq_iff _ _).1 h1
      rw [Subsingleton.elim P default, Subsingleton.elim Q default]
      exact ⟨e⟩
  refine hle.trans (le_of_eq ?_)
  rw [← Nat.card_coe_set_eq, Nat.card_congr (Equiv.Set.univPi T), Nat.card_pi]
  rw [← Finset.prod_coe_sort n.primeFactors]
  rfl

/-! ## Interface: the pc-presentation bound and Higman's lower bound -/

theorem g_pow_six_le (p a : ℕ) (hp : p.Prime) : Erdos1160.g (p ^ a) ^ 6 ≤ p ^ (a ^ 3) := by
  haveI : Fact p.Prime := ⟨hp⟩
  calc Erdos1160.g (p ^ a) ^ 6 ≤ (p ^ (a.choose 2 + a.choose 3)) ^ 6 :=
        Nat.pow_le_pow_left (OMA.PC.g_le p a) 6
    _ = p ^ (6 * (a.choose 2 + a.choose 3)) := by rw [← pow_mul, mul_comm]
    _ ≤ p ^ (a ^ 3) :=
        Nat.pow_le_pow_right hp.pos (by have := OMA.PC.choose_arith a; omega)

theorem higman (m : ℕ) (hm : 3 ≤ m) :
    2 ^ (2 * m ^ 3) ≤ Erdos1160.g (2 ^ m) ^ 27 * 2 ^ (12 * m ^ 2) :=
  Erdos1160Growth.SharpFamily.higman_lower_all m hm

/-! ## N2 -/

lemma h1_two (b : ℕ) : Erdos1160.g (2 ^ b) ^ 2166 ≤ 2 ^ (361 * b ^ 3) := by
  calc Erdos1160.g (2 ^ b) ^ 2166 = (Erdos1160.g (2 ^ b) ^ 6) ^ 361 := by rw [← pow_mul]
    _ ≤ (2 ^ (b ^ 3)) ^ 361 := Nat.pow_le_pow_left (g_pow_six_le 2 b Nat.prime_two) 361
    _ = 2 ^ (361 * b ^ 3) := by rw [← pow_mul, mul_comm]

lemma h1_odd (p a c : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hlt : p ^ a < 2 ^ c) :
    Erdos1160.g (p ^ a) ^ 2166 ≤ (p ^ a) ^ (144 * c ^ 2) := by
  have hsq : 361 * a ^ 2 ≤ 144 * c ^ 2 := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have h1 : 2 ^ (19 * a) < 2 ^ (12 * c) := by
      calc 2 ^ (19 * a) = (2 ^ 19) ^ a := by rw [pow_mul]
        _ ≤ (3 ^ 12) ^ a := Nat.pow_le_pow_left (by norm_num) a
        _ = (3 ^ a) ^ 12 := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ (p ^ a) ^ 12 := Nat.pow_le_pow_left (Nat.pow_le_pow_left hp3 a) 12
        _ < (2 ^ c) ^ 12 := Nat.pow_lt_pow_left hlt (by norm_num)
        _ = 2 ^ (12 * c) := by rw [← pow_mul, mul_comm]
    have h3 : 19 * a < 12 * c := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h1
    nlinarith
  have hp1 : 1 ≤ p := hp.one_lt.le
  calc Erdos1160.g (p ^ a) ^ 2166 = (Erdos1160.g (p ^ a) ^ 6) ^ 361 := by rw [← pow_mul]
    _ ≤ (p ^ (a ^ 3)) ^ 361 := Nat.pow_le_pow_left (g_pow_six_le p a hp) 361
    _ = p ^ (a * (361 * a ^ 2)) := by rw [← pow_mul]; ring_nf
    _ ≤ p ^ (a * (144 * c ^ 2)) := Nat.pow_le_pow_right hp1 (Nat.mul_le_mul_left a hsq)
    _ = (p ^ a) ^ (144 * c ^ 2) := by rw [pow_mul]

lemma h1_cubic (b c : ℕ) (h : b ≤ 3 * c) :
    64 * (361 * b ^ 3 + c * (144 * c ^ 2)) ≤ 9891 * (b + c) ^ 3 := by
  nlinarith [Nat.mul_le_mul_right (13213 * b ^ 2 + 9966 * b * c + 225 * c ^ 2) h]

lemma h1_arith (K X : ℕ) (hK : 1000 ≤ K) (hX : 64 * X ≤ 9891 * (K + 2) ^ 3) :
    X * 27 + 12 * K ^ 2 * 2166 ≤ 2 * K ^ 3 * 2166 := by
  have h1 : 1000 * K ≤ K ^ 2 := by nlinarith
  have h2 : 1000 * K ^ 2 ≤ K ^ 3 := by nlinarith
  nlinarith

theorem target2 : ∀ᶠ m : ℕ in Filter.atTop, ∀ n ∈ Finset.Ico 1 (2 ^ m),
    (¬ ∃ k : ℕ, n = 2 ^ k) → 7 * m < 11 * n.factorization 2 → 4 * n.factorization 2 ≤ 3 * m →
    (nilClasses n).ncard ≤ 2 ^ (m - 2) * Erdos1160.g (2 ^ (m - 2)) := by
  filter_upwards [Filter.eventually_ge_atTop 1002] with m hm n hn _hpow h7 h4
  rw [Finset.mem_Ico] at hn
  have hn0 : n ≠ 0 := by omega
  obtain ⟨b, hb⟩ : ∃ b, n.factorization 2 = b := ⟨_, rfl⟩
  rw [hb] at h7 h4
  obtain ⟨c, hc⟩ : ∃ c, m = b + c := ⟨m - b, by omega⟩
  have h2mem : 2 ∈ n.primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨Nat.prime_two, ?_, hn0⟩
    exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hn0).2 (by omega)
  have hfac := Nat.prod_factorization_pow_eq_self hn0
  rw [Finsupp.prod, Nat.support_factorization] at hfac
  obtain ⟨q, hq⟩ : ∃ q, ∏ p ∈ n.primeFactors.erase 2, p ^ n.factorization p = q := ⟨_, rfl⟩
  have hnq : 2 ^ b * q = n := by
    rw [← hfac, ← hq, ← hb]
    exact Finset.mul_prod_erase n.primeFactors (fun p => p ^ n.factorization p) h2mem
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h] at hnq; omega
    · exact h
  have hqc : q < 2 ^ c := by
    have : 2 ^ b * q < 2 ^ b * 2 ^ c := by rw [hnq, ← pow_add, ← hc]; exact hn.2
    exact Nat.lt_of_mul_lt_mul_left this
  set N := (nilClasses n).ncard
  have hN : N ^ 2166 ≤ 2 ^ (361 * b ^ 3 + c * (144 * c ^ 2)) := by
    calc N ^ 2166 ≤ (∏ p ∈ n.primeFactors, Erdos1160.g (p ^ n.factorization p)) ^ 2166 :=
          Nat.pow_le_pow_left (nil_le_prod n (by omega)) _
      _ = ∏ p ∈ n.primeFactors, Erdos1160.g (p ^ n.factorization p) ^ 2166 :=
          (Finset.prod_pow _ _ _).symm
      _ = Erdos1160.g (2 ^ n.factorization 2) ^ 2166 *
            ∏ p ∈ n.primeFactors.erase 2, Erdos1160.g (p ^ n.factorization p) ^ 2166 :=
          (Finset.mul_prod_erase n.primeFactors
            (fun p => Erdos1160.g (p ^ n.factorization p) ^ 2166) h2mem).symm
      _ ≤ 2 ^ (361 * b ^ 3) *
            ∏ p ∈ n.primeFactors.erase 2, (p ^ n.factorization p) ^ (144 * c ^ 2) := by
          apply Nat.mul_le_mul
          · rw [hb]; exact h1_two b
          · apply Finset.prod_le_prod'
            intro p hp
            have hp2 := Finset.ne_of_mem_erase hp
            have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
            apply h1_odd p _ c hpp hp2
            have hdvd : p ^ n.factorization p ∣ q := by
              rw [← hq]
              exact Finset.dvd_prod_of_mem (fun p => p ^ n.factorization p) hp
            exact lt_of_le_of_lt (Nat.le_of_dvd hq0 hdvd) hqc
      _ = 2 ^ (361 * b ^ 3) * q ^ (144 * c ^ 2) := by rw [Finset.prod_pow, hq]
      _ ≤ 2 ^ (361 * b ^ 3) * (2 ^ c) ^ (144 * c ^ 2) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hqc.le _)
      _ = 2 ^ (361 * b ^ 3 + c * (144 * c ^ 2)) := by rw [← pow_mul, ← pow_add]
  obtain ⟨K, hK⟩ : ∃ K, m = K + 2 := ⟨m - 2, by omega⟩
  have hK2 : m - 2 = K := by omega
  rw [hK2]
  set G := Erdos1160.g (2 ^ K)
  have hX := h1_cubic b c (by omega)
  have hbc : b + c = K + 2 := by omega
  rw [hbc] at hX
  have hA := h1_arith K _ (by omega) hX
  have hH := higman K (by omega)
  have hH' : 2 ^ (2 * K ^ 3 * 2166) ≤ G ^ 58482 * 2 ^ (12 * K ^ 2 * 2166) := by
    calc 2 ^ (2 * K ^ 3 * 2166) = (2 ^ (2 * K ^ 3)) ^ 2166 := by rw [pow_mul]
      _ ≤ (G ^ 27 * 2 ^ (12 * K ^ 2)) ^ 2166 := Nat.pow_le_pow_left hH _
      _ = G ^ (27 * 2166) * 2 ^ (12 * K ^ 2 * 2166) := by rw [mul_pow, ← pow_mul, ← pow_mul]
  have hC : N ^ 58482 * 2 ^ (12 * K ^ 2 * 2166) ≤ G ^ 58482 * 2 ^ (12 * K ^ 2 * 2166) := by
    calc N ^ 58482 * 2 ^ (12 * K ^ 2 * 2166)
          = (N ^ 2166) ^ 27 * 2 ^ (12 * K ^ 2 * 2166) := by rw [← pow_mul]
      _ ≤ (2 ^ (361 * b ^ 3 + c * (144 * c ^ 2))) ^ 27 * 2 ^ (12 * K ^ 2 * 2166) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hN _)
      _ = 2 ^ ((361 * b ^ 3 + c * (144 * c ^ 2)) * 27 + 12 * K ^ 2 * 2166) := by
          rw [← pow_mul, ← pow_add]
      _ ≤ 2 ^ (2 * K ^ 3 * 2166) := Nat.pow_le_pow_right (by norm_num) hA
      _ ≤ _ := hH'
  have hD := Nat.le_of_mul_le_mul_right hC (by positivity)
  have hNG : N ≤ G := (Nat.pow_le_pow_iff_left (by norm_num)).1 hD
  exact le_trans hNG (Nat.le_mul_of_pos_left _ (by positivity))

end OMA.Nil

theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H2_R1_H2_R1.H1 :=
  OMA.Nil.target2
