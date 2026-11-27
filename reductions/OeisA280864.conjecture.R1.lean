import FormalConjectures.OEIS.«280864»

/-!
# Structural Reduction for the Cup-of-Coffee Sequence (`OeisA280864.conjecture`)

Credit: @cybergenesis621

Reduces `OeisA280864.conjecture` to two cleanly separated milestones:
- `H1`: Existence of an infinite total sequence obeying `OeisA280864.FollowsRule`.
- `H2`: Infinitely many primes make their first appearance in any rule-following sequence as a
  composite multiple (`p ∣ a n`, `∀ i < n, ¬ p ∣ a i`, and `a n ≠ p`).

The proof of `main` establishes the exact 2-run state invariant
`forbiddenFactors (a (n - 1)) (a n) = requiredFactors (a (n - 2)) (a (n - 1))`
and the First-Appearance Dichotomy for odd primes: at the first index `n0` where an odd prime
`p` divides `a n0`, `a n0 = (∏ R0) * p`, so whenever `a n0 ≠ p` (equivalently `R0 ≠ ∅`), the
following term is `a (n0 + 1) = p`, clearing `requiredFactors (a n0) (a (n0 + 1)) = ∅` and
leaving `forbiddenFactors (a n0) (a (n0 + 1)) = {p}`. Choosing such a prime `p` larger than
both `k` and all values before the injectivity threshold forces `k` to appear.
-/

namespace OMA.R_OeisA280864_conjecture_R1

open OeisA280864

private lemma requiredFactors_prime {x y p : ℕ} (hp : p ∈ requiredFactors x y) : p.Prime :=
  Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1

private lemma forbiddenFactors_prime {x y p : ℕ} (hp : p ∈ forbiddenFactors x y) : p.Prime :=
  Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hp).1

private lemma disjoint_required_forbidden (x y : ℕ) :
    Disjoint (requiredFactors x y) (forbiddenFactors x y) := by
  rw [Finset.disjoint_left]
  intro p hreq hforb
  exact (Finset.mem_sdiff.mp hreq).2 (Finset.mem_inter.mp hforb).2

private lemma prod_primes_pos (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    0 < ∏ p ∈ S, p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    rw [Finset.prod_insert ha]
    exact Nat.mul_pos (hS a (Finset.mem_insert_self a t)).pos
      (ih fun p hp => hS p (Finset.mem_insert_of_mem hp))

private lemma prime_dvd_prod_iff {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {q : ℕ} (hq : q.Prime) :
    q ∣ ∏ p ∈ S, p ↔ q ∈ S := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [hq.not_dvd_one]
  | @insert a t ha ih =>
    have ha_prime : a.Prime := hS a (Finset.mem_insert_self a t)
    have ht_prime : ∀ p ∈ t, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert ha, hq.dvd_mul, ih ht_prime, Finset.mem_insert,
      Nat.prime_dvd_prime_iff_eq hq ha_prime]

private lemma prod_primes_dvd_of_forall_dvd {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {n : ℕ}
    (hdvd : ∀ p ∈ S, p ∣ n) :
    (∏ p ∈ S, p) ∣ n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    have ha_prime : a.Prime := hS a (Finset.mem_insert_self a t)
    have ht_prime : ∀ p ∈ t, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert ha]
    have hcop : Nat.Coprime a (∏ p ∈ t, p) := by
      refine ha_prime.coprime_iff_not_dvd.mpr ?_
      rw [prime_dvd_prod_iff ht_prime ha_prime]
      exact ha
    exact hcop.mul_dvd_of_dvd_of_dvd (hdvd a (Finset.mem_insert_self a t))
      (ih ht_prime fun p hp => hdvd p (Finset.mem_insert_of_mem hp))

private lemma primeFactors_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, p).primeFactors = S := by
  ext q
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hq, hdvd, _⟩
    exact (prime_dvd_prod_iff hS hq).mp hdvd
  · intro hq
    exact ⟨hS q hq, Finset.dvd_prod_of_mem _ hq, (prod_primes_pos S hS).ne'⟩

private lemma followsRule_pos {a : ℕ → ℕ} (ha : FollowsRule a) (n : ℕ) : 0 < a n := by
  match n with
  | 0 => rw [ha.1]; decide
  | 1 => rw [ha.2.1]; decide
  | k + 2 => exact (ha.2.2 (k + 2) (by omega)).1.1

private lemma forbiddenFactors_eq_requiredFactors_prev {a : ℕ → ℕ} (ha : FollowsRule a)
    {n : ℕ} (hn : 2 ≤ n) :
    forbiddenFactors (a (n - 1)) (a n) = requiredFactors (a (n - 2)) (a (n - 1)) := by
  have hg := ha.2.2 n hn
  have hpos := followsRule_pos ha n
  ext p
  simp only [forbiddenFactors, requiredFactors, Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hpn, hpn1⟩
    refine ⟨hpn1, ?_⟩
    intro hpn2
    have hforb : p ∈ forbiddenFactors (a (n - 2)) (a (n - 1)) :=
      Finset.mem_inter.mpr ⟨hpn1, hpn2⟩
    exact hg.1.2.2 p hforb (Nat.dvd_of_mem_primeFactors hpn)
  · rintro ⟨hpn1, hnpn2⟩
    have hreq : p ∈ requiredFactors (a (n - 2)) (a (n - 1)) :=
      Finset.mem_sdiff.mpr ⟨hpn1, hnpn2⟩
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hpn1
    have hdvd : p ∣ a n := hg.1.2.1 p hreq
    exact ⟨Nat.mem_primeFactors.mpr ⟨hp_prime, hdvd, hpos.ne'⟩, hpn1⟩

private lemma exists_index_gt_bound {a : ℕ → ℕ} (hinj : Function.Injective a) (K : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, K < a n := by
  classical
  let s : Finset ℕ := Finset.range (K + 1)
  have hfin : {n : ℕ | a n ≤ K}.Finite := by
    have hsub : {n : ℕ | a n ≤ K} ⊆ a ⁻¹' (s : Set ℕ) := by
      intro n hn
      have hn' : a n ≤ K := hn
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))
    exact (s.finite_toSet.preimage (hinj.injOn)).subset hsub
  let t : Finset ℕ := hfin.toFinset
  refine ⟨t.sup id + 1, fun n hn => ?_⟩
  by_contra hle
  push Not at hle
  have hmem : n ∈ t := hfin.mem_toFinset.mpr hle
  have hsup : n ≤ t.sup id := Finset.le_sup (f := id) hmem
  omega

private lemma first_multiple_exact {a : ℕ → ℕ} (ha : FollowsRule a)
    {p n0 : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ a n0) (hmin : ∀ i < n0, ¬ p ∣ a i) :
    2 ≤ n0 ∧
      a n0 = (∏ q ∈ requiredFactors (a (n0 - 2)) (a (n0 - 1)), q) * p ∧
      requiredFactors (a (n0 - 1)) (a n0) = {p} ∧
      forbiddenFactors (a (n0 - 1)) (a n0) = requiredFactors (a (n0 - 2)) (a (n0 - 1)) := by
  have hn0_ge2 : 2 ≤ n0 := by
    by_contra hlt
    have : n0 = 0 ∨ n0 = 1 := by omega
    rcases this with rfl | rfl
    · rw [ha.1] at hdvd; exact hp.not_dvd_one hdvd
    · rw [ha.2.1] at hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  let R0 := requiredFactors (a (n0 - 2)) (a (n0 - 1))
  let F0 := forbiddenFactors (a (n0 - 2)) (a (n0 - 1))
  have hR0 : ∀ q ∈ R0, q.Prime := fun q hq => requiredFactors_prime hq
  let r0 := ∏ q ∈ R0, q
  have hr0_pos : 0 < r0 := prod_primes_pos R0 hR0
  have hp_not_an1 : p ∉ (a (n0 - 1)).primeFactors := by
    intro hmem
    exact hmin (n0 - 1) (by omega) (Nat.dvd_of_mem_primeFactors hmem)
  have hp_not_R0 : p ∉ R0 := fun h => hp_not_an1 (Finset.mem_sdiff.mp h).1
  have hp_not_F0 : p ∉ F0 := fun h => hp_not_an1 (Finset.mem_inter.mp h).1
  have helig : Eligible (a (n0 - 2)) (a (n0 - 1)) (r0 * p) := by
    refine ⟨Nat.mul_pos hr0_pos hp.pos, ?_, ?_⟩
    · intro q hq
      exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ hq) p
    · intro q hq
      have hq_prime : q.Prime := forbiddenFactors_prime hq
      rw [hq_prime.dvd_mul]
      push Not
      refine ⟨?_, ?_⟩
      · rw [prime_dvd_prod_iff hR0 hq_prime]
        exact Finset.disjoint_right.mp (disjoint_required_forbidden (a (n0 - 2)) (a (n0 - 1))) hq
      · rw [Nat.prime_dvd_prime_iff_eq hq_prime hp]
        intro hEq; exact hp_not_F0 (hEq ▸ hq)
  have hunused : UnusedBefore a n0 (r0 * p) := by
    intro i hi heq
    exact hmin i hi (by rw [heq]; exact dvd_mul_left p r0)
  have hle : a n0 ≤ r0 * p := (ha.2.2 n0 hn0_ge2).2.2 (r0 * p) helig hunused
  have hr0_dvd : r0 ∣ a n0 := prod_primes_dvd_of_forall_dvd hR0 (ha.2.2 n0 hn0_ge2).1.2.1
  have hcop : Nat.Coprime r0 p := by
    refine (hp.coprime_iff_not_dvd.mpr ?_).symm
    rw [prime_dvd_prod_iff hR0 hp]
    exact hp_not_R0
  have hmul_dvd : r0 * p ∣ a n0 := hcop.mul_dvd_of_dvd_of_dvd hr0_dvd hdvd
  have hge : r0 * p ≤ a n0 := Nat.le_of_dvd (followsRule_pos ha n0) hmul_dvd
  have han0_eq : a n0 = r0 * p := le_antisymm hle hge
  have hpf_an0 : (a n0).primeFactors = insert p R0 := by
    rw [han0_eq, Nat.primeFactors_mul hr0_pos.ne' hp.ne_zero,
      primeFactors_prod_primes hR0, hp.primeFactors]
    ext q; simp
  have hreq_next : requiredFactors (a (n0 - 1)) (a n0) = {p} := by
    rw [requiredFactors, hpf_an0]
    ext q
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | hqR0, hqnot⟩
      · rfl
      · exact absurd (Finset.mem_sdiff.mp hqR0).1 hqnot
    · rintro rfl
      exact ⟨Or.inl rfl, hp_not_an1⟩
  have hforb_next : forbiddenFactors (a (n0 - 1)) (a n0) = R0 :=
    forbiddenFactors_eq_requiredFactors_prev ha hn0_ge2
  exact ⟨hn0_ge2, han0_eq, hreq_next, hforb_next⟩

private lemma first_appearance_dichotomy {a : ℕ → ℕ} (ha : FollowsRule a)
    {p n0 : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ a n0) (hmin : ∀ i < n0, ¬ p ∣ a i) :
    (a (n0 + 1) = p ∧
      requiredFactors (a n0) (a (n0 + 1)) = ∅ ∧
      forbiddenFactors (a n0) (a (n0 + 1)) = {p}) ∨
    (a n0 = p ∧ a (n0 + 1) = 2 * p ∧
      requiredFactors (a n0) (a (n0 + 1)) = {2} ∧
      forbiddenFactors (a n0) (a (n0 + 1)) = {p}) := by
  obtain ⟨hn0_ge2, han0_eq, hreq_next, hforb_next⟩ := first_multiple_exact ha hp hp2 hdvd hmin
  let R0 := requiredFactors (a (n0 - 2)) (a (n0 - 1))
  have hR0 : ∀ q ∈ R0, q.Prime := fun q hq => requiredFactors_prime hq
  let r0 := ∏ q ∈ R0, q
  have hr0_pos : 0 < r0 := prod_primes_pos R0 hR0
  have hp_not_R0 : p ∉ R0 := by
    intro h
    exact hmin (n0 - 1) (by omega) (Nat.dvd_of_mem_primeFactors (Finset.mem_sdiff.mp h).1)
  by_cases hR0_empty : R0 = ∅
  · right
    have han0_p : a n0 = p := by
      have hR0' : requiredFactors (a (n0 - 2)) (a (n0 - 1)) = ∅ := hR0_empty
      rw [hR0'] at han0_eq
      simpa using han0_eq
    have hforb_empty : forbiddenFactors (a (n0 - 1)) (a n0) = ∅ := by
      simpa [R0, hR0_empty] using hforb_next
    have hg1 := ha.2.2 (n0 + 1) (by omega)
    have hsub1 : n0 + 1 - 2 = n0 - 1 := by omega
    have hsub2 : n0 + 1 - 1 = n0 := by omega
    have hp_pos : 0 < p := hp.pos
    have helig2p : Eligible (a (n0 - 1)) (a n0) (2 * p) := by
      refine ⟨by omega, ?_, ?_⟩
      · intro q hq
        rw [hreq_next, Finset.mem_singleton] at hq
        subst hq; exact dvd_mul_left q 2
      · intro q hq
        rw [hforb_empty] at hq
        exact absurd hq (Finset.notMem_empty q)
    have hunused2p : UnusedBefore a (n0 + 1) (2 * p) := by
      intro i hi heq
      rcases lt_or_eq_of_le (show i ≤ n0 by omega) with hlt | rfl
      · exact hmin i hlt (by rw [heq]; exact dvd_mul_left p 2)
      · rw [han0_p] at heq; omega
    have hle2p : a (n0 + 1) ≤ 2 * p := by
      exact hg1.2.2 (2 * p) (by simpa [hsub1, hsub2] using helig2p) hunused2p
    have hp_dvd_next : p ∣ a (n0 + 1) := by
      have hreq_mem : p ∈ requiredFactors (a (n0 + 1 - 2)) (a (n0 + 1 - 1)) := by
        rw [hsub1, hsub2, hreq_next]; exact Finset.mem_singleton_self p
      exact hg1.1.2.1 p hreq_mem
    have hne_p : a (n0 + 1) ≠ p := by
      intro heq
      have := hg1.2.1 n0 (by omega)
      exact this (han0_p.trans heq.symm)
    rcases hp_dvd_next with ⟨k, hk⟩
    have hk_pos : 0 < k := by
      have hpos := followsRule_pos ha (n0 + 1)
      rcases Nat.eq_zero_or_pos k with rfl | hposk
      · simp at hk; omega
      · exact hposk
    have hk_ne1 : k ≠ 1 := by
      intro hk1; rw [hk1, mul_one] at hk; exact hne_p hk
    have ha_next_eq : a (n0 + 1) = 2 * p := by
      have hk2 : 2 ≤ k := by omega
      have hge : 2 * p ≤ a (n0 + 1) := by
        rw [hk, mul_comm 2 p]
        exact Nat.mul_le_mul_left p hk2
      omega
    have hpf_2p : (2 * p).primeFactors = {2, p} := by
      rw [Nat.primeFactors_mul (by decide) hp.ne_zero, Nat.prime_two.primeFactors, hp.primeFactors]
      ext q; simp
    have hreq2 : requiredFactors (a n0) (a (n0 + 1)) = {2} := by
      rw [requiredFactors, han0_p, ha_next_eq, hpf_2p, hp.primeFactors]
      ext q
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hne⟩
        · rfl
        · exact absurd rfl hne
      · rintro rfl
        exact ⟨Or.inl rfl, hp2.symm⟩
    have hforb2 : forbiddenFactors (a n0) (a (n0 + 1)) = {p} := by
      have h := forbiddenFactors_eq_requiredFactors_prev ha (show 2 ≤ n0 + 1 by omega)
      simpa [hsub1, hsub2, hreq_next] using h
    exact ⟨han0_p, ha_next_eq, hreq2, hforb2⟩
  · left
    obtain ⟨q0, hq0⟩ := Finset.nonempty_iff_ne_empty.mpr hR0_empty
    have hr0_ge2 : 2 ≤ r0 := by
      have hq0_ge2 : 2 ≤ q0 := (hR0 q0 hq0).two_le
      exact le_trans hq0_ge2 (Nat.le_of_dvd hr0_pos (Finset.dvd_prod_of_mem _ hq0))
    have hg1 := ha.2.2 (n0 + 1) (by omega)
    have hsub1 : n0 + 1 - 2 = n0 - 1 := by omega
    have hsub2 : n0 + 1 - 1 = n0 := by omega
    have helig_p : Eligible (a (n0 - 1)) (a n0) p := by
      refine ⟨hp.pos, ?_, ?_⟩
      · intro q hq
        rw [hreq_next, Finset.mem_singleton] at hq
        subst hq; exact dvd_refl q
      · intro q hq
        rw [hforb_next] at hq
        rw [Nat.prime_dvd_prime_iff_eq (hR0 q hq) hp]
        intro hEq; exact hp_not_R0 (hEq ▸ hq)
    have hunused_p : UnusedBefore a (n0 + 1) p := by
      intro i hi heq
      rcases lt_or_eq_of_le (show i ≤ n0 by omega) with hlt | rfl
      · exact hmin i hlt (by rw [heq])
      · have han0_r0 : a i = r0 * p := han0_eq
        have h2p : 2 * p ≤ r0 * p := Nat.mul_le_mul_right p hr0_ge2
        have hp_pos : 0 < p := hp.pos
        omega
    have hle_p : a (n0 + 1) ≤ p :=
      hg1.2.2 p (by simpa [hsub1, hsub2] using helig_p) hunused_p
    have hp_dvd_next : p ∣ a (n0 + 1) := by
      have hreq_mem : p ∈ requiredFactors (a (n0 + 1 - 2)) (a (n0 + 1 - 1)) := by
        rw [hsub1, hsub2, hreq_next]; exact Finset.mem_singleton_self p
      exact hg1.1.2.1 p hreq_mem
    have hge_p : p ≤ a (n0 + 1) := Nat.le_of_dvd (followsRule_pos ha (n0 + 1)) hp_dvd_next
    have ha_next_p : a (n0 + 1) = p := le_antisymm hle_p hge_p
    have hreq2 : requiredFactors (a n0) (a (n0 + 1)) = ∅ := by
      rw [requiredFactors, ha_next_p, hp.primeFactors]
      ext q
      simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨rfl, hnot⟩
      exact hnot (Nat.mem_primeFactors.mpr ⟨hp, hdvd, (followsRule_pos ha n0).ne'⟩)
    have hforb2 : forbiddenFactors (a n0) (a (n0 + 1)) = {p} := by
      have h := forbiddenFactors_eq_requiredFactors_prev ha (show 2 ≤ n0 + 1 by omega)
      simpa [hsub1, hsub2, hreq_next] using h
    exact ⟨ha_next_p, hreq2, hforb2⟩

/-- Existence of a total sequence obeying the greedy Cup-of-Coffee rule. -/
def H1 : Prop :=
  ∃ a : ℕ → ℕ, OeisA280864.FollowsRule a

/-- Infinitely many primes make their first appearance as a composite multiple in any
rule-following sequence. -/
def H2 : Prop :=
  ∀ a : ℕ → ℕ, OeisA280864.FollowsRule a →
    ∀ B : ℕ, ∃ p > B, p.Prime ∧ ∃ n, p ∣ a n ∧ (∀ i < n, ¬ p ∣ a i) ∧ a n ≠ p

theorem main : H1 → H2 → type_of% @OeisA280864.conjecture := by
  intro h1 h2
  obtain ⟨a, ha⟩ := h1
  refine ⟨a, ha, ?_⟩
  intro k hk
  by_contra hno
  push Not at hno
  obtain ⟨N1, hN1⟩ := exists_index_gt_bound (OeisA280864.followsRule_injective ha) k
  let B := max (max k 2) ((Finset.range N1).sup a)
  obtain ⟨p, hp_gt, hp_prime, n0, hdvd, hmin, hne_p⟩ := h2 a ha B
  have hp2 : p ≠ 2 := by omega
  have hp_gt_k : k < p := by omega
  have hn0_ge_N1 : N1 ≤ n0 := by
    by_contra hlt
    have hleB : a n0 ≤ B := le_trans
      (Finset.le_sup (f := a) (Finset.mem_range.mpr (by omega))) (le_max_right _ _)
    have hp_le : p ≤ a n0 := Nat.le_of_dvd (followsRule_pos ha n0) hdvd
    omega
  rcases first_appearance_dichotomy ha hp_prime hp2 hdvd hmin with
    ⟨_, hreq, hforb⟩ | ⟨han0_p, _, _, _⟩
  · have hnot_p_dvd : ¬ p ∣ k := fun hdiv => by
      have := Nat.le_of_dvd hk hdiv; omega
    have helig : Eligible (a n0) (a (n0 + 1)) k := by
      refine ⟨hk, ?_, ?_⟩
      · intro q hq; rw [hreq] at hq; exact absurd hq (Finset.notMem_empty q)
      · intro q hq; rw [hforb, Finset.mem_singleton] at hq; subst hq; exact hnot_p_dvd
    have hunused : UnusedBefore a (n0 + 2) k := fun i _ => hno i
    have hsub1 : n0 + 2 - 2 = n0 := by omega
    have hsub2 : n0 + 2 - 1 = n0 + 1 := by omega
    have hle : a (n0 + 2) ≤ k :=
      (ha.2.2 (n0 + 2) (by omega)).2.2 k
        (by simpa [hsub1, hsub2] using helig) hunused
    have hgt : k < a (n0 + 2) := hN1 (n0 + 2) (by omega)
    omega
  · exact hne_p han0_p

end OMA.R_OeisA280864_conjecture_R1
