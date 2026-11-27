import FormalConjectures.ErdosProblems.«522»

/-!
# Erdős Problem 522, variant `number_real_roots` (Erdős–Offord 1956)

Original proof. For random `±1` polynomials of degree `n`, the number of real roots counted with
multiplicity, divided by `log n`, tends to `2/π` in probability.

Route (all elementary; no Kac–Rice): by the symmetries `x ↦ -x`, `x ↦ 1/x` it suffices to count roots in
`(0, 1)`. On the rational grid `gx L j = (λʲ - 1)/(λʲ + 1)`, `λ = 1 + 1/L` (equal steps in `artanh`):
* upper bound: sign changes across grid windows have mean `≤ (1/(2π) + o(1)) log n` (two-point CLT by
  Fourier inversion against compactly supported bumps; Gaussian wedge `arccos ρ / (2π)` by polar
  coordinates; neighbour correlation `≥ 2√λ/(1+λ)`); multiple roots in one window are rare (Hermite
  remainder via localized Rolle with multiplicities, Taylor/Hasse second moments, Erdős's
  Littlewood–Offord bound via Sperner); a deterministic Blaschke bound near `0` and a Hermite bound
  near `1`;
* lower bound: robust straddles of block sums over disjoint coefficient blocks are independent for
  distant windows (Chebyshev), and the outside part rarely spoils the sign (independence of disjoint
  coordinate sets);
* transfer from `KacCoefficients` to uniform sign vectors and a diagonal argument for `o`, `p`.

Mathematical source: P. Erdős and A. C. Offord, *On the number of real roots of a random algebraic
equation*, Proc. London Math. Soc. (3) 6 (1956); the route here is our own (brainstormed with Claude
Fable and Gemini; every step formalized from scratch).
-/

-- ===== RR0 =====

/-!
# Erdős 522 (real roots), part 0: Erdős's Littlewood–Offord bound

For signs `ε : ι → ℤˣ` and weights `a` with `|a i| ≥ 1` on a set `I` of size `M`, the number of sign
vectors with `∑ ε i a i` in a half-open interval of length `2` is at most `2^|ι| / √M`.
(Erdős 1945, via Sperner's theorem.)
-/

open Finset Real

noncomputable section S_RR0

namespace R522

/-- Signed sum. -/
def ssum {ι : Type*} [Fintype ι] (ε : ι → ℤˣ) (a : ι → ℝ) : ℝ := ∑ i, ((ε i : ℤ) : ℝ) * a i

lemma cb_sq (p : ℕ) : (Nat.centralBinom p : ℝ) ^ 2 * (2 * p + 1) ≤ 16 ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    have h := Nat.succ_mul_centralBinom_succ p
    have hc : (Nat.centralBinom (p + 1) : ℝ) = 2 * (2 * p + 1) * Nat.centralBinom p / (p + 1) := by
      rw [eq_div_iff (by positivity)]
      have : ((p + 1 : ℕ) : ℝ) * Nat.centralBinom (p + 1) = 2 * (2 * p + 1) * Nat.centralBinom p := by
        exact_mod_cast h
      push_cast at this; linarith
    rw [hc, div_pow, div_mul_eq_mul_div]
    have hp : (0 : ℝ) < ((p : ℝ) + 1) ^ 2 := by positivity
    rw [div_le_iff₀ hp]
    have key : (2 * (p : ℝ) + 1) * (2 * ((p : ℝ) + 1) + 1) ≤ 4 * ((p : ℝ) + 1) ^ 2 := by nlinarith
    have e1 : (2 * (2 * (p : ℝ) + 1) * (Nat.centralBinom p : ℝ)) ^ 2 * (2 * ((p : ℝ) + 1) + 1)
        = 4 * (((Nat.centralBinom p : ℝ)) ^ 2 * (2 * p + 1)) * ((2 * p + 1) * (2 * ((p : ℝ) + 1) + 1)) := by
      ring
    push_cast
    rw [e1]
    have := mul_le_mul ih key (by positivity) (by positivity)
    calc 4 * (((Nat.centralBinom p : ℝ)) ^ 2 * (2 * p + 1)) * ((2 * p + 1) * (2 * ((p : ℝ) + 1) + 1))
        = 4 * ((((Nat.centralBinom p : ℝ)) ^ 2 * (2 * p + 1)) * ((2 * p + 1) * (2 * ((p : ℝ) + 1) + 1))) := by ring
      _ ≤ 4 * (16 ^ p * (4 * ((p : ℝ) + 1) ^ 2)) := by linarith
      _ = 16 ^ (p + 1) * ((p : ℝ) + 1) ^ 2 := by rw [pow_succ]; ring

lemma choose_half_sq (M : ℕ) : ((M.choose (M / 2) : ℕ) : ℝ) ^ 2 * M ≤ 4 ^ M := by
  obtain ⟨p, rfl | rfl⟩ := Nat.even_or_odd' M
  · have h2 : 2 * p / 2 = p := by omega
    rw [h2, ← Nat.centralBinom_eq_two_mul_choose]
    have := cb_sq p
    have h16 : (4 : ℝ) ^ (2 * p) = 16 ^ p := by rw [pow_mul]; norm_num
    rw [h16]; push_cast
    have : (0 : ℝ) ≤ (Nat.centralBinom p : ℝ) ^ 2 := by positivity
    nlinarith
  · have h2 : (2 * p + 1) / 2 = p := by omega
    rw [h2]
    have hsum : Nat.centralBinom (p + 1) = 2 * (2 * p + 1).choose p := by
      rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (p + 1) = (2 * p + 1) + 1 by ring,
        Nat.choose_succ_succ, Nat.choose_symm_of_eq_add (show 2 * p + 1 = (p + 1) + p by omega)]
      ring
    have := cb_sq (p + 1)
    have hc : ((2 * p + 1).choose p : ℝ) = Nat.centralBinom (p + 1) / 2 := by
      rw [hsum]; push_cast; ring
    rw [hc]
    have h16 : (4 : ℝ) ^ (2 * p + 1) = 16 ^ (p + 1) / 4 := by
      rw [pow_succ, pow_mul, pow_succ]; ring
    rw [h16]; push_cast at this ⊢
    have : (0 : ℝ) ≤ (Nat.centralBinom (p + 1) : ℝ) ^ 2 := by positivity
    nlinarith

/-- The antichain step: with the outside signs fixed, the inside sign patterns giving a sum in
`[t, t + 2)` form an antichain. -/
lemma lo_fiber {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ → ℝ) (ha : ∀ i, 1 ≤ |a i|)
    (c t : ℝ) :
    ((univ.filter fun ε : κ → ℤˣ => t ≤ c + ssum ε a ∧ c + ssum ε a < t + 2).card)
      ≤ (Fintype.card κ).choose (Fintype.card κ / 2) := by
  classical
  -- sign of each weight
  set s : κ → ℤˣ := fun i => if 0 ≤ a i then 1 else -1 with hs
  have hsa : ∀ i, ((s i : ℤ) : ℝ) * a i = |a i| := by
    intro i; simp only [hs]; split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (not_le.mp h)]
  set T : (κ → ℤˣ) → Finset κ := fun ε => univ.filter fun i => ε i = s i with hT
  have hval : ∀ (ε : κ → ℤˣ) i, ε i = s i ∨ ε i = -s i := by
    intro ε i
    rcases Int.units_eq_one_or (ε i) with h | h <;> rcases Int.units_eq_one_or (s i) with h' | h' <;>
      simp [h, h']
  have hTinj : Function.Injective T := by
    intro ε ε' h
    funext i
    have hi := congrArg (fun F => i ∈ F) h
    simp only [hT, mem_filter, mem_univ, true_and, eq_iff_iff] at hi
    rcases hval ε i with h1 | h1 <;> rcases hval ε' i with h2 | h2
    · rw [h1, h2]
    · exfalso; have := hi.mp h1; rw [this] at h2
      exact absurd h2 (by rcases Int.units_eq_one_or (s i) with h | h <;> simp [h])
    · exfalso; have := hi.mpr h2; rw [this] at h1
      exact absurd h1 (by rcases Int.units_eq_one_or (s i) with h | h <;> simp [h])
    · rw [h1, h2]
  -- sum formula: ssum ε a = 2 ∑_{T ε} |a| - ∑ |a|
  have hsum : ∀ ε : κ → ℤˣ, ssum ε a = 2 * ∑ i ∈ T ε, |a i| - ∑ i, |a i| := by
    intro ε
    unfold ssum
    have : ∀ i, ((ε i : ℤ) : ℝ) * a i = 2 * (if ε i = s i then |a i| else 0) - |a i| := by
      intro i
      rcases hval ε i with h | h
      · rw [if_pos h, h, hsa]; ring
      · rw [if_neg (by rw [h]; rcases Int.units_eq_one_or (s i) with h' | h' <;> simp [h']), h]
        push_cast; rw [neg_mul, hsa]; ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  set F := univ.filter fun ε : κ → ℤˣ => t ≤ c + ssum ε a ∧ c + ssum ε a < t + 2 with hF
  have hanti : IsAntichain (· ⊆ ·) (SetLike.coe (F.image T)) := by
    intro A hA B hB hAB hsub
    simp only [coe_image, Set.mem_image, mem_coe] at hA hB
    obtain ⟨ε, hε, rfl⟩ := hA
    obtain ⟨ε', hε', rfl⟩ := hB
    have hne : T ε ⊂ T ε' := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hAB⟩
    obtain ⟨j, hj', hj⟩ := Finset.exists_of_ssubset hne
    have hdiff : ∑ i ∈ T ε', |a i| - ∑ i ∈ T ε, |a i| ≥ 1 := by
      rw [← Finset.sum_sdiff hsub]
      have : |a j| ≤ ∑ i ∈ T ε' \ T ε, |a i| :=
        Finset.single_le_sum (f := fun i => |a i|) (fun i _ => abs_nonneg _)
          (Finset.mem_sdiff.mpr ⟨hj', hj⟩)
      linarith [ha j]
    simp only [hF, mem_filter, mem_univ, true_and] at hε hε'
    rw [hsum] at hε hε'
    linarith [hε.1, hε'.2]
  have := hanti.sperner
  rwa [Finset.card_image_of_injective _ hTinj] at this

/-- **Erdős's Littlewood–Offord bound.** -/
theorem lo_interval {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) (I : Finset ι)
    (hI : ∀ i ∈ I, 1 ≤ |a i|) (hIne : I.Nonempty) (t : ℝ) :
    ((univ.filter fun ε : ι → ℤˣ => t ≤ ssum ε a ∧ ssum ε a < t + 2).card : ℝ)
      ≤ 2 ^ Fintype.card ι / √(I.card) := by
  classical
  set p : ι → Prop := fun i => i ∈ I
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => ℤˣ)
  let κ := {i // p i}
  let ν := {i // ¬ p i}
  have hsplit : ∀ ε : ι → ℤˣ, ssum ε a = (∑ j : ν, (((e ε).2 j : ℤ) : ℝ) * a j)
      + ssum (e ε).1 (fun i : κ => a i) := by
    intro ε
    unfold ssum
    rw [add_comm]
    convert (Fintype.sum_subtype_add_sum_subtype p (fun i => ((ε i : ℤ) : ℝ) * a i)).symm <;> rfl
  -- count via the equivalence
  have hcount : ((univ.filter fun ε : ι → ℤˣ => t ≤ ssum ε a ∧ ssum ε a < t + 2).card : ℝ)
      = ∑ o : ν → ℤˣ, ((univ.filter fun ε : κ → ℤˣ =>
          t ≤ (∑ j : ν, ((o j : ℤ) : ℝ) * a j) + ssum ε (fun i : κ => a i) ∧
          (∑ j : ν, ((o j : ℤ) : ℝ) * a j) + ssum ε (fun i : κ => a i) < t + 2).card : ℝ) := by
    rw [Finset.card_filter]
    push_cast
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun o _ => ?_)
    rw [Finset.card_filter]; push_cast
    refine Finset.sum_congr rfl (fun ε _ => ?_)
    simp only [hsplit, Equiv.apply_symm_apply]
  have hfib : ∀ o : ν → ℤˣ, ((univ.filter fun ε : κ → ℤˣ =>
          t ≤ (∑ j : ν, ((o j : ℤ) : ℝ) * a j) + ssum ε (fun i : κ => a i) ∧
          (∑ j : ν, ((o j : ℤ) : ℝ) * a j) + ssum ε (fun i : κ => a i) < t + 2).card : ℝ)
        ≤ (Fintype.card κ).choose (Fintype.card κ / 2) := by
    intro o
    exact_mod_cast lo_fiber (fun i : κ => a i) (fun i => hI i i.2) _ t
  have hκ : Fintype.card κ = I.card := by
    simp only [κ, p]; exact Fintype.card_coe I
  have hν : Fintype.card (ν → ℤˣ) * 2 ^ I.card = 2 ^ Fintype.card ι := by
    rw [Fintype.card_fun, Fintype.card_units_int, ← hκ, ← pow_add]
    congr 1
    rw [add_comm, Fintype.card_subtype_compl]
    have := Fintype.card_subtype_le p
    show Fintype.card {x // p x} + _ = _
    omega
  rw [hcount]
  have hM : (0 : ℝ) < I.card := by exact_mod_cast hIne.card_pos
  calc _ ≤ ∑ _o : ν → ℤˣ, (((Fintype.card κ).choose (Fintype.card κ / 2) : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun o _ => hfib o)
    _ = Fintype.card (ν → ℤˣ) * ((I.card.choose (I.card / 2) : ℕ) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hκ]
    _ ≤ 2 ^ Fintype.card ι / √(I.card) := by
        rw [le_div_iff₀ (Real.sqrt_pos.mpr hM)]
        have h1 := choose_half_sq I.card
        have hsq : ((I.card.choose (I.card / 2) : ℕ) : ℝ) * √(I.card) ≤ 2 ^ I.card := by
          have h0 : 0 ≤ ((I.card.choose (I.card / 2) : ℕ) : ℝ) * √(I.card) := by positivity
          have : (((I.card.choose (I.card / 2) : ℕ) : ℝ) * √(I.card)) ^ 2 ≤ (2 ^ I.card) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hM.le, ← pow_mul, mul_comm I.card 2, pow_mul]; norm_num
            linarith
          exact (pow_le_pow_iff_left₀ h0 (by positivity) (by norm_num)).mp this
        have hν' : (Fintype.card (ν → ℤˣ) : ℝ) * 2 ^ I.card = 2 ^ Fintype.card ι := by
          exact_mod_cast hν
        calc (Fintype.card (ν → ℤˣ) : ℝ) * ((I.card.choose (I.card / 2) : ℕ) : ℝ) * √(I.card)
            = (Fintype.card (ν → ℤˣ) : ℝ) * (((I.card.choose (I.card / 2) : ℕ) : ℝ) * √(I.card)) := by ring
          _ ≤ (Fintype.card (ν → ℤˣ) : ℝ) * 2 ^ I.card := by gcongr
          _ = _ := hν'

end R522

end S_RR0

-- ===== RR1 =====

/-!
# Erdős 522 (real roots), part 1: root counting on intervals

* `card_Icc_le_derivative`: localized Rolle with multiplicity.
* `exists_iter_root`: `≥ k + 1` roots in `[a, b]` give a root of the `k`-th derivative there.
* `hermite`: `≥ k` roots in `[a, b]` and `c ∈ [a, b]` give `ξ ∈ [a, b]` with
  `|p c| * k! ≤ (b - a)^k * |p^{(k)} ξ|`.
* `simple_sign`: one simple root in `(a, b)` and nonzero endpoint values force a sign change.
* `poly`: the `±1` polynomial of a sign vector; it has no rational roots in `(0, 1)`.
-/

open Finset Real Polynomial

noncomputable section S_RR1

namespace R522

/-- Roots in a set, with multiplicity. -/
def nIn (p : ℝ[X]) (I : Set ℝ) : ℕ :=
  Multiset.card (@Multiset.filter _ (· ∈ I) (Classical.decPred _) p.roots)

lemma nIn_def (p : ℝ[X]) (I : Set ℝ) [DecidablePred (· ∈ I)] :
    nIn p I = Multiset.card (p.roots.filter (· ∈ I)) := by
  unfold nIn; congr

lemma nIn_eq_sum (q : ℝ[X]) (I : Set ℝ) [DecidablePred (· ∈ I)] :
    nIn q I = ∑ x ∈ q.roots.toFinset.filter (· ∈ I), q.roots.count x := by
  rw [nIn_def, ← Multiset.toFinset_sum_count_eq, Multiset.toFinset_filter]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Multiset.count_filter_of_pos]
  simp only [Finset.mem_filter] at hx
  exact hx.2

/-- **Localized Rolle, with multiplicity.** -/
theorem card_Icc_le_derivative (p : ℝ[X]) (a b : ℝ) :
    nIn p (Set.Icc a b) ≤ nIn (derivative p) (Set.Icc a b) + 1 := by
  classical
  rcases eq_or_ne (derivative p) 0 with hp' | hp'
  · rw [eq_C_of_derivative_eq_zero hp', nIn_def, nIn_def]; simp
  have hp : p ≠ 0 := ne_of_apply_ne derivative (by rwa [derivative_zero])
  set s := p.roots.toFinset.filter (· ∈ Set.Icc a b) with hs
  set t := (derivative p).roots.toFinset.filter (· ∈ Set.Icc a b) with ht
  have hint : s.card ≤ (t \ s).card + 1 := by
    refine Finset.card_le_sdiff_of_interleaved fun x hx y hy hxy _ => ?_
    simp only [hs, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hp] at hx hy
    obtain ⟨z, hz1, hz2⟩ := exists_deriv_eq_zero hxy p.continuousOn (hx.1.trans hy.1.symm)
    refine ⟨z, ?_, hz1.1, hz1.2⟩
    simp only [ht, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hp', IsRoot, ← p.deriv]
    exact ⟨hz2, hx.2.1.trans hz1.1.le, hz1.2.le.trans hy.2.2⟩
  rw [nIn_eq_sum, nIn_eq_sum]
  calc ∑ x ∈ s, p.roots.count x = ∑ x ∈ s, (p.roots.count x - 1 + 1) := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        have : 0 < p.roots.count x := Multiset.count_pos.2 (by
          simp only [hs, Finset.mem_filter, Multiset.mem_toFinset] at hx; exact hx.1)
        omega
    _ = (∑ x ∈ s, (p.rootMultiplicity x - 1)) + s.card := by
        simp only [Finset.sum_add_distrib, Finset.card_eq_sum_ones, count_roots]
    _ ≤ (∑ x ∈ s, (derivative p).rootMultiplicity x) + ((t \ s).card + 1) :=
        add_le_add (Finset.sum_le_sum fun _ _ =>
          rootMultiplicity_sub_one_le_derivative_rootMultiplicity _ _) hint
    _ ≤ (∑ x ∈ s, (derivative p).roots.count x) +
          ((∑ x ∈ t \ s, (derivative p).roots.count x) + 1) := by
        simp only [← count_roots, Finset.card_eq_sum_ones]
        gcongr with x hx
        rw [Nat.succ_le_iff, Multiset.count_pos]
        have := (Finset.mem_sdiff.1 hx).1
        simp only [ht, Finset.mem_filter, Multiset.mem_toFinset] at this
        exact this.1
    _ = (∑ x ∈ t, (derivative p).roots.count x) + 1 := by
        rw [← add_assoc, ← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union]
        congr 1
        symm
        refine Finset.sum_subset Finset.subset_union_right (fun x hx hxt => ?_)
        rw [Multiset.count_eq_zero]
        intro hmem
        apply hxt
        have hxs : x ∈ s := by
          rcases Finset.mem_union.1 hx with h | h
          · exact h
          · exact absurd h hxt
        simp only [hs, Finset.mem_filter] at hxs
        simp only [ht, Finset.mem_filter, Multiset.mem_toFinset]
        exact ⟨hmem, hxs.2⟩

lemma nIn_pos_ne_zero {p : ℝ[X]} {I : Set ℝ} (h : 0 < nIn p I) : p ≠ 0 := by
  rintro rfl; rw [nIn] at h; simp at h

lemma exists_root_of_nIn_pos {p : ℝ[X]} {I : Set ℝ} (h : 0 < nIn p I) :
    ∃ ξ ∈ I, p.eval ξ = 0 := by
  classical
  have hp := nIn_pos_ne_zero h
  rw [nIn_def] at h
  obtain ⟨ξ, hξ⟩ := Multiset.card_pos_iff_exists_mem.1 h
  rw [Multiset.mem_filter, mem_roots hp] at hξ
  exact ⟨ξ, hξ.2, hξ.1⟩

/-- Iterated Rolle. -/
theorem exists_iter_root (k : ℕ) : ∀ (F : ℝ[X]) (a b : ℝ), k + 1 ≤ nIn F (Set.Icc a b) →
    ∃ ξ ∈ Set.Icc a b, (derivative^[k] F).eval ξ = 0 := by
  induction k with
  | zero => intro F a b h; exact exists_root_of_nIn_pos (p := F) (I := Set.Icc a b) (by omega)
  | succ k ih =>
    intro F a b h
    have h1 := card_Icc_le_derivative F a b
    obtain ⟨ξ, hξ, h⟩ := ih (derivative F) a b (by omega)
    exact ⟨ξ, hξ, by rw [Function.iterate_succ_apply]; exact h⟩

lemma iterate_derivative_monic (R : ℝ[X]) (hR : R.Monic) (x : ℝ) :
    (derivative^[R.natDegree] R).eval x = (R.natDegree.factorial : ℝ) := by
  have hdeg : (derivative^[R.natDegree] R).natDegree ≤ 0 := by
    have := natDegree_iterate_derivative R R.natDegree; omega
  rw [eq_C_of_natDegree_le_zero hdeg, eval_C, coeff_iterate_derivative, zero_add,
    Nat.descFactorial_self, hR.coeff_natDegree, nsmul_eq_mul, mul_one]

lemma abs_prod_map (S : Multiset ℝ) (f : ℝ → ℝ) :
    |(S.map f).prod| = (S.map fun r => |f r|).prod := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih => rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons,
      abs_mul, ih]

lemma prod_map_le_pow (S : Multiset ℝ) (f : ℝ → ℝ) (C : ℝ) (h0 : ∀ r ∈ S, 0 ≤ f r)
    (h : ∀ r ∈ S, f r ≤ C) : (S.map f).prod ≤ C ^ Multiset.card S := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    have ha0 := h0 a (Multiset.mem_cons_self a S)
    have haC := h a (Multiset.mem_cons_self a S)
    have ih' := ih (fun r hr => h0 r (Multiset.mem_cons_of_mem hr))
      (fun r hr => h r (Multiset.mem_cons_of_mem hr))
    have hp0 : 0 ≤ (S.map f).prod := Multiset.prod_nonneg (fun x hx => by
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx; exact h0 r (Multiset.mem_cons_of_mem hr))
    calc f a * (S.map f).prod ≤ C * C ^ Multiset.card S := mul_le_mul haC ih' hp0 (ha0.trans haC)
      _ = C ^ Multiset.card S * C := by ring

/-- **Hermite-type remainder bound.** -/
theorem hermite (p : ℝ[X]) (a b c : ℝ) (hc : c ∈ Set.Icc a b) (k : ℕ)
    (hk : k ≤ nIn p (Set.Icc a b)) :
    ∃ ξ ∈ Set.Icc a b, |p.eval c| * k.factorial ≤ (b - a) ^ k * |(derivative^[k] p).eval ξ| := by
  classical
  by_cases hpc : p.eval c = 0
  · exact ⟨c, hc, by rw [hpc]; simp; exact mul_nonneg (pow_nonneg (by linarith [hc.1, hc.2]) _) (abs_nonneg _)⟩
  have hp : p ≠ 0 := by rintro rfl; simp at hpc
  -- a sub-multiset of `k` roots in `[a, b]`
  set Rt := p.roots.filter (· ∈ Set.Icc a b) with hRt
  have hcard : k ≤ Multiset.card Rt := by rw [nIn_def] at hk; exact hk
  obtain ⟨S, hS⟩ : ∃ S, S ∈ Multiset.powersetCard k Rt := by
    refine Multiset.exists_mem_of_ne_zero ?_
    intro h0
    have := congrArg Multiset.card h0
    rw [Multiset.card_powersetCard, Multiset.card_zero] at this
    exact (Nat.choose_pos hcard).ne' this
  rw [Multiset.mem_powersetCard] at hS
  have hSle : S ≤ p.roots := hS.1.trans (Multiset.filter_le _ _)
  have hSI : ∀ r ∈ S, r ∈ Set.Icc a b := fun r hr =>
    (Multiset.mem_filter.1 (Multiset.mem_of_le hS.1 hr)).2
  set R := (S.map fun r => X - C r).prod with hRdef
  have hRmonic : R.Monic := monic_multiset_prod_of_monic _ _ (fun r _ => monic_X_sub_C r)
  have hRdeg : R.natDegree = k := by
    rw [hRdef, natDegree_multiset_prod_X_sub_C_eq_card, hS.2]
  have hRdvd : R ∣ p := (Multiset.prod_X_sub_C_dvd_iff_le_roots hp S).2 hSle
  have hRc : R.eval c = (S.map fun r => c - r).prod := by
    rw [hRdef, eval_multiset_prod, Multiset.map_map]
    congr 1; refine Multiset.map_congr rfl (fun r _ => ?_); simp
  have hRc_le : |R.eval c| ≤ (b - a) ^ k := by
    rw [hRc, ← hS.2]
    have : ∀ r ∈ S, |c - r| ≤ b - a := by
      intro r hr
      have := hSI r hr
      rw [abs_le]; constructor <;> linarith [hc.1, hc.2, this.1, this.2]
    rw [abs_prod_map]
    exact prod_map_le_pow S _ _ (fun r _ => abs_nonneg _) this
  have hRc0 : R.eval c ≠ 0 := by
    intro h0
    obtain ⟨q, hq⟩ := hRdvd
    apply hpc; rw [hq, eval_mul, h0, zero_mul]
  -- the auxiliary polynomial
  set F := C (R.eval c) * p - C (p.eval c) * R with hF
  have hFk : ∀ ξ, (derivative^[k] F).eval ξ
      = R.eval c * (derivative^[k] p).eval ξ - p.eval c * k.factorial := by
    intro ξ
    rw [hF, iterate_derivative_sub, iterate_derivative_C_mul, iterate_derivative_C_mul, eval_sub,
      eval_mul, eval_mul, eval_C, eval_C, ← hRdeg, iterate_derivative_monic R hRmonic]
  have hroot : ∃ ξ ∈ Set.Icc a b, (derivative^[k] F).eval ξ = 0 := by
    by_cases hF0 : F = 0
    · exact ⟨c, hc, by rw [hF0]; simp⟩
    refine exists_iter_root k F a b ?_
    -- `c ::ₘ S` are roots of `F` in `[a, b]`
    have hdvd : ((c ::ₘ S).map fun r => X - C r).prod ∣ F := by
      rw [Multiset.map_cons, Multiset.prod_cons]
      obtain ⟨G, hG⟩ : R ∣ F := by
        obtain ⟨q, hq⟩ := hRdvd
        exact ⟨C (R.eval c) * q - C (p.eval c), by rw [hF, hq]; ring⟩
      have hGc : G.eval c = 0 := by
        have : F.eval c = 0 := by rw [hF]; simp; ring
        rw [hG, eval_mul] at this
        exact (mul_eq_zero.1 this).resolve_left hRc0
      obtain ⟨H, hH⟩ := dvd_iff_isRoot.2 hGc
      exact ⟨H, by rw [hG, hH]; ring⟩
    have hle := (Multiset.prod_X_sub_C_dvd_iff_le_roots hF0 _).1 hdvd
    have hfilt : (c ::ₘ S) ≤ F.roots.filter (· ∈ Set.Icc a b) := by
      have : (c ::ₘ S).filter (· ∈ Set.Icc a b) = c ::ₘ S := by
        rw [Multiset.filter_eq_self]
        intro r hr
        rcases Multiset.mem_cons.1 hr with h | h
        · rw [h]; exact hc
        · exact hSI r h
      rw [← this]; exact Multiset.filter_le_filter _ hle
    have := Multiset.card_le_card hfilt
    rw [Multiset.card_cons, hS.2] at this
    rw [nIn_def]; exact this
  obtain ⟨ξ, hξ, h0⟩ := hroot
  refine ⟨ξ, hξ, ?_⟩
  rw [hFk] at h0
  have heq : p.eval c * k.factorial = R.eval c * (derivative^[k] p).eval ξ := by linarith
  calc |p.eval c| * k.factorial = |p.eval c * k.factorial| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k.factorial)]
    _ = |R.eval c| * |(derivative^[k] p).eval ξ| := by rw [heq, abs_mul]
    _ ≤ (b - a) ^ k * |(derivative^[k] p).eval ξ| := by gcongr

/-- A sign change gives a root in the open interval. -/
lemma nIn_pos_of_sign {p : ℝ[X]} {a b : ℝ} (hab : a < b) (h : p.eval a * p.eval b < 0) :
    0 < nIn p (Set.Ioo a b) := by
  classical
  have hp : p ≠ 0 := by rintro rfl; simp at h
  have hcont : ContinuousOn (fun x => p.eval x) (Set.Icc a b) := p.continuous.continuousOn
  obtain ⟨r, hr, hr0⟩ : ∃ r ∈ Set.Ioo a b, p.eval r = 0 := by
    rcases lt_or_gt_of_ne (show p.eval a ≠ 0 by intro h0; rw [h0] at h; simp at h) with ha | ha
    · have hb : 0 < p.eval b := by nlinarith
      have := intermediate_value_Ioo hab.le hcont
      exact this ⟨ha, hb⟩
    · have hb : p.eval b < 0 := by nlinarith
      have := intermediate_value_Ioo' hab.le hcont
      exact this ⟨hb, ha⟩
  rw [nIn_def]
  refine Multiset.card_pos_iff_exists_mem.2 ⟨r, ?_⟩
  rw [Multiset.mem_filter, mem_roots hp]
  exact ⟨hr0, hr⟩

/-- One simple root in `(a, b)` and nonzero endpoint values force a sign change. -/
theorem simple_sign {p : ℝ[X]} {a b : ℝ} (hab : a < b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0)
    (h1 : nIn p (Set.Ioo a b) = 1) : p.eval a * p.eval b < 0 := by
  classical
  have hp : p ≠ 0 := nIn_pos_ne_zero (I := Set.Ioo a b) (by omega)
  obtain ⟨r, hr, hr0⟩ := exists_root_of_nIn_pos (by omega : 0 < nIn p (Set.Ioo a b))
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.2 hr0
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq; exact hp hq
  -- `q` has no roots in `[a, b]`
  have hnoq : ∀ x ∈ Set.Icc a b, q.eval x ≠ 0 := by
    intro x hx hqx
    rcases eq_or_lt_of_le hx.1 with h | h
    · apply ha; rw [hq, eval_mul, h, hqx, mul_zero]
    rcases eq_or_lt_of_le hx.2 with h' | h'
    · apply hb; rw [hq, eval_mul, ← h', hqx, mul_zero]
    -- `x` is a root of `q` in `(a, b)`: two roots of `p` there
    have hroots : r ::ₘ x ::ₘ 0 ≤ p.roots := by
      rw [hq, roots_mul (by rw [← hq]; exact hp), roots_X_sub_C]
      exact add_le_add (le_refl _) (by
        rw [Multiset.singleton_le]; exact (mem_roots hq0).2 hqx)
    have : 2 ≤ nIn p (Set.Ioo a b) := by
      rw [nIn_def]
      have hf : (r ::ₘ x ::ₘ 0).filter (· ∈ Set.Ioo a b) = r ::ₘ x ::ₘ 0 := by
        rw [Multiset.filter_eq_self]
        intro y hy
        simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hy
        rcases hy with rfl | rfl
        · exact hr
        · exact ⟨h, h'⟩
      have := Multiset.card_le_card (Multiset.filter_le_filter (· ∈ Set.Ioo a b) hroots)
      rw [hf] at this; simpa using this
    omega
  -- constant sign of `q`
  have hsign : 0 < q.eval a * q.eval b := by
    by_contra hneg
    push Not at hneg
    have hcont : ContinuousOn (fun x => q.eval x) (Set.Icc a b) := q.continuous.continuousOn
    have hqa := hnoq a ⟨le_rfl, hab.le⟩
    have hqb := hnoq b ⟨hab.le, le_rfl⟩
    rcases lt_or_gt_of_ne hqa with h1 | h1
    · have : 0 ≤ q.eval b := by nlinarith
      obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc hab.le hcont ⟨h1.le, this⟩
      exact hnoq x hx hx0
    · have : q.eval b ≤ 0 := by nlinarith
      obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' hab.le hcont ⟨this, h1.le⟩
      exact hnoq x hx hx0
  rw [hq, eval_mul, eval_mul]
  simp only [eval_sub, eval_X, eval_C]
  have h1 : a - r < 0 := by linarith [hr.1]
  have h2 : 0 < b - r := by linarith [hr.2]
  have : (a - r) * (b - r) < 0 := mul_neg_of_neg_of_pos h1 h2
  nlinarith

/-! ### The `±1` polynomial -/

/-- The polynomial `∑ ε_i X^i`. -/
def poly {n : ℕ} (ε : Fin (n + 1) → ℤˣ) : ℝ[X] := ∑ i : Fin (n + 1), C (((ε i : ℤ) : ℝ)) * X ^ (i : ℕ)

lemma poly_eval {n : ℕ} (ε : Fin (n + 1) → ℤˣ) (x : ℝ) :
    (poly ε).eval x = ssum ε (fun i => x ^ (i : ℕ)) := by
  unfold poly ssum
  rw [eval_finsetSum]
  simp

lemma poly_coeff {n : ℕ} (ε : Fin (n + 1) → ℤˣ) (j : ℕ) :
    (poly ε).coeff j = if h : j < n + 1 then (((ε ⟨j, h⟩ : ℤ) : ℝ)) else 0 := by
  unfold poly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp
    · intro b _ hb; rw [if_neg]; · simp
      intro hj; apply hb; ext; simp [hj]
    · simp
  · refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [if_neg]; · simp
    intro hj; apply h; rw [hj]; exact i.2

lemma unit_ne_zero (u : ℤˣ) : ((u : ℤ) : ℝ) ≠ 0 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

lemma poly_ne_zero {n : ℕ} (ε : Fin (n + 1) → ℤˣ) : poly ε ≠ 0 := by
  intro h
  have := poly_coeff ε 0
  rw [h, coeff_zero, dif_pos (by omega)] at this
  exact unit_ne_zero _ this.symm

/-- **No rational roots in `(0, 1)`.** -/
theorem poly_eval_rat_ne_zero {n : ℕ} (ε : Fin (n + 1) → ℤˣ) (q : ℚ) (h0 : 0 < q) (h1 : q < 1) :
    (poly ε).eval (q : ℝ) ≠ 0 := by
  intro hroot
  rw [poly_eval] at hroot
  unfold ssum at hroot
  set p := q.num with hpdef
  set d := (q.den : ℤ) with hddef
  have hd0 : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hq : (q : ℝ) = (p : ℝ) / (q.den : ℝ) := by
    rw [hpdef]; exact_mod_cast (Rat.num_div_den q).symm
  -- clear denominators
  have hint : ∑ i : Fin (n + 1), (ε i : ℤ) * p ^ (i : ℕ) * d ^ (n - i) = 0 := by
    have : ((∑ i : Fin (n + 1), (ε i : ℤ) * p ^ (i : ℕ) * d ^ (n - i) : ℤ) : ℝ)
        = (q.den : ℝ) ^ n * ∑ i : Fin (n + 1), ((ε i : ℤ) : ℝ) * (q : ℝ) ^ (i : ℕ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hq, div_pow]
      have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.2
      have : (q.den : ℝ) ^ n = (q.den : ℝ) ^ (i : ℕ) * (q.den : ℝ) ^ (n - i) := by
        rw [← pow_add]; congr 1; omega
      rw [this]; field_simp; simp [hddef]
    rw [hroot, mul_zero] at this
    exact_mod_cast this
  -- `d` divides the leading term
  have hlast : d ∣ (ε (Fin.last n) : ℤ) * p ^ n := by
    have hsplit := Fin.sum_univ_castSucc (fun i : Fin (n + 1) => (ε i : ℤ) * p ^ (i : ℕ) * d ^ (n - i))
    rw [hint] at hsplit
    simp only [Fin.val_castSucc, Fin.val_last, Nat.sub_self, pow_zero, mul_one] at hsplit
    have : d ∣ ∑ i : Fin n, (ε (Fin.castSucc i) : ℤ) * p ^ (i : ℕ) * d ^ (n - i) := by
      refine Finset.dvd_sum (fun i _ => ?_)
      exact Dvd.dvd.mul_left (dvd_pow_self d (by have := i.2; omega)) _
    have h2 : (ε (Fin.last n) : ℤ) * p ^ n = -(∑ i : Fin n, (ε (Fin.castSucc i) : ℤ) * p ^ (i : ℕ) * d ^ (n - i)) := by
      linarith
    rw [h2]; exact this.neg_right
  have hlast' : d ∣ p ^ n := by
    have hu : IsUnit (ε (Fin.last n) : ℤ) := (ε (Fin.last n)).isUnit
    exact (hu.dvd_mul_left).1 hlast
  have hcop : IsCoprime p d := by
    rw [Int.isCoprime_iff_gcd_eq_one, hpdef, hddef]
    exact q.reduced
  have hunit : IsUnit d := (IsCoprime.pow_left hcop : IsCoprime (p ^ n) d).isUnit_of_dvd' hlast' (dvd_refl d)
  have hd1 : q.den = 1 := by
    rw [Int.isUnit_iff] at hunit
    rcases hunit with h | h
    · have : ((q.den : ℕ) : ℤ) = 1 := by rw [← hddef]; exact h
      exact_mod_cast this
    · have : (0 : ℤ) < d := by rw [hddef]; exact_mod_cast q.den_pos
      omega
  -- then `q` is an integer in `(0, 1)`
  have hqint : q = (q.num : ℚ) := by
    rw [← Rat.num_div_den q, hd1]; simp
  have h0' : (0 : ℚ) < q.num := by rw [← hqint]; exact h0
  have h1' : (q.num : ℚ) < 1 := by rw [← hqint]; exact h1
  have : (0 : ℤ) < q.num := by exact_mod_cast h0'
  have : q.num < 1 := by exact_mod_cast h1'
  omega

end R522

end S_RR1

-- ===== RR2 =====

/-!
# Erdős 522 (real roots), part 2: averages over sign vectors

`EE f` is the average of `f` over `ε : ι → ℤˣ`, and `PP S` the proportion of sign vectors in `S`.
Markov and Chebyshev, second moments of signed sums, a weighted Cauchy–Schwarz bound, and
independence of functions of disjoint coordinate sets.
-/

open Finset Real

noncomputable section S_RR2

namespace R522

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Average over sign vectors. -/
def EE (f : (ι → ℤˣ) → ℝ) : ℝ := (∑ ε, f ε) / 2 ^ Fintype.card ι

open scoped Classical in
/-- Proportion of sign vectors satisfying `S`. -/
def PP (S : (ι → ℤˣ) → Prop) : ℝ := EE fun ε => if S ε then 1 else 0

lemma PP_eq (S : (ι → ℤˣ) → Prop) [DecidablePred S] :
    PP S = EE fun ε => if S ε then (1 : ℝ) else 0 := by
  unfold PP; congr 1; ext ε; split_ifs <;> simp_all

lemma card_signs : (Fintype.card (ι → ℤˣ) : ℝ) = 2 ^ Fintype.card ι := by
  rw [Fintype.card_fun, Fintype.card_units_int]; push_cast; rfl

lemma EE_const (c : ℝ) : EE (ι := ι) (fun _ => c) = c := by
  unfold EE
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_signs]
  field_simp

lemma EE_add (f g : (ι → ℤˣ) → ℝ) : EE (fun ε => f ε + g ε) = EE f + EE g := by
  unfold EE; rw [Finset.sum_add_distrib, add_div]

lemma EE_sub (f g : (ι → ℤˣ) → ℝ) : EE (fun ε => f ε - g ε) = EE f - EE g := by
  unfold EE; rw [Finset.sum_sub_distrib, sub_div]

lemma EE_smul (c : ℝ) (f : (ι → ℤˣ) → ℝ) : EE (fun ε => c * f ε) = c * EE f := by
  unfold EE; rw [← Finset.mul_sum, mul_div_assoc]

lemma EE_sum {κ : Type*} (s : Finset κ) (f : κ → (ι → ℤˣ) → ℝ) :
    EE (fun ε => ∑ k ∈ s, f k ε) = ∑ k ∈ s, EE (f k) := by
  unfold EE; rw [Finset.sum_comm, Finset.sum_div]

lemma EE_mono {f g : (ι → ℤˣ) → ℝ} (h : ∀ ε, f ε ≤ g ε) : EE f ≤ EE g := by
  unfold EE; gcongr with ε; exact h ε

lemma EE_nonneg {f : (ι → ℤˣ) → ℝ} (h : ∀ ε, 0 ≤ f ε) : 0 ≤ EE f := by
  have := EE_mono (f := fun _ => (0 : ℝ)) h
  rwa [EE_const] at this

lemma PP_nonneg (S : (ι → ℤˣ) → Prop) : 0 ≤ PP S := by
  classical
  unfold PP; exact EE_nonneg (fun ε => by split_ifs <;> norm_num)

lemma PP_le_one (S : (ι → ℤˣ) → Prop) : PP S ≤ 1 := by
  classical
  unfold PP
  have := EE_mono (f := fun ε => if S ε then (1 : ℝ) else 0) (g := fun _ => 1)
    (fun ε => by split_ifs <;> norm_num)
  rwa [EE_const] at this

lemma PP_mono {S T : (ι → ℤˣ) → Prop} (h : ∀ ε, S ε → T ε) : PP S ≤ PP T := by
  classical
  unfold PP
  exact EE_mono (fun ε => by
    by_cases hs : S ε
    · rw [if_pos hs, if_pos (h ε hs)]
    · rw [if_neg hs]; split_ifs <;> norm_num)

lemma PP_or_le (S T : (ι → ℤˣ) → Prop) : PP (fun ε => S ε ∨ T ε) ≤ PP S + PP T := by
  classical
  unfold PP
  rw [← EE_add]
  exact EE_mono (fun ε => by split_ifs <;> simp_all)

lemma PP_exists_le {κ : Type*} (s : Finset κ) (S : κ → (ι → ℤˣ) → Prop) :
    PP (fun ε => ∃ k ∈ s, S k ε) ≤ ∑ k ∈ s, PP (S k) := by
  classical
  unfold PP
  rw [← EE_sum]
  refine EE_mono (fun ε => ?_)
  split_ifs with h
  · obtain ⟨k, hk, hS⟩ := h
    calc (1 : ℝ) = if S k ε then 1 else 0 := by rw [if_pos hS]
      _ ≤ ∑ j ∈ s, if S j ε then (1 : ℝ) else 0 :=
          Finset.single_le_sum (f := fun j => if S j ε then (1 : ℝ) else 0)
            (fun j _ => by split_ifs <;> norm_num) hk
  · exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)

lemma PP_compl (S : (ι → ℤˣ) → Prop) : PP (fun ε => ¬ S ε) = 1 - PP S := by
  classical
  unfold PP
  have key : ∀ g : (ι → ℤˣ) → ℝ, (∀ ε, g ε = 1 - (if S ε then 1 else 0)) →
      EE g = 1 - EE (fun ε => if S ε then (1 : ℝ) else 0) := by
    intro g hg
    rw [show g = fun ε => 1 - (if S ε then (1 : ℝ) else 0) from funext hg, EE_sub, EE_const]
  exact key _ (fun ε => by by_cases h : S ε <;> simp [h])

/-- Markov. -/
lemma markov {f : (ι → ℤˣ) → ℝ} (hf : ∀ ε, 0 ≤ f ε) {t : ℝ} (ht : 0 < t) :
    PP (fun ε => t ≤ f ε) ≤ EE f / t := by
  classical
  rw [le_div_iff₀ ht]
  unfold PP
  rw [mul_comm, ← EE_smul]
  exact EE_mono (fun ε => by split_ifs with h <;> nlinarith [hf ε])

/-- Markov with indicators bounded above by a function. -/
lemma PP_le_EE {S : (ι → ℤˣ) → Prop} {f : (ι → ℤˣ) → ℝ} (hf : ∀ ε, 0 ≤ f ε)
    (h : ∀ ε, S ε → 1 ≤ f ε) : PP S ≤ EE f := by
  classical
  unfold PP
  exact EE_mono (fun ε => by split_ifs with hs; exacts [h ε hs, hf ε])

/-- Chebyshev. -/
lemma chebyshev (f : (ι → ℤˣ) → ℝ) {t : ℝ} (ht : 0 < t) :
    PP (fun ε => t ≤ |f ε|) ≤ EE (fun ε => f ε ^ 2) / t ^ 2 := by
  have h := markov (f := fun ε => f ε ^ 2) (fun ε => sq_nonneg _) (pow_pos ht 2)
  refine (PP_mono (fun ε hε => ?_)).trans h
  have : t ^ 2 ≤ |f ε| ^ 2 := pow_le_pow_left₀ ht.le hε 2
  rwa [sq_abs] at this

/-! ### Flips and first moments -/

/-- Flip coordinate `i`. -/
def flipAt (i : ι) (ε : ι → ℤˣ) : ι → ℤˣ := Function.update ε i (-ε i)

lemma flipAt_invol (i : ι) : Function.Involutive (flipAt i) := by
  intro ε; funext j; unfold flipAt
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

lemma sum_flip {M : Type*} [AddCommMonoid M] (i : ι) (f : (ι → ℤˣ) → M) :
    ∑ ε, f (flipAt i ε) = ∑ ε, f ε :=
  Equiv.sum_comp (flipAt_invol i).toPerm f

lemma EE_coord (i : ι) : EE (ι := ι) (fun ε => ((ε i : ℤ) : ℝ)) = 0 := by
  unfold EE
  have h := sum_flip i (fun ε => ((ε i : ℤ) : ℝ))
  simp only [flipAt, Function.update_self, Units.val_neg, Int.cast_neg, Finset.sum_neg_distrib] at h
  have : ∑ ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) = 0 := by linarith
  rw [this, zero_div]

lemma EE_coord_mul (i j : ι) (hij : i ≠ j) :
    EE (ι := ι) (fun ε => ((ε i : ℤ) : ℝ) * ((ε j : ℤ) : ℝ)) = 0 := by
  unfold EE
  have h := sum_flip i (fun ε => ((ε i : ℤ) : ℝ) * ((ε j : ℤ) : ℝ))
  simp only [flipAt, Function.update_self, Function.update_of_ne hij.symm, Units.val_neg,
    Int.cast_neg, neg_mul, Finset.sum_neg_distrib] at h
  have : ∑ ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) * ((ε j : ℤ) : ℝ) = 0 := by linarith
  rw [this, zero_div]

lemma unit_sq (u : ℤˣ) : ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

/-- Second mixed moment of signed sums. -/
lemma EE_ssum_mul (c d : ι → ℝ) :
    EE (fun ε => ssum ε c * ssum ε d) = ∑ i, c i * d i := by
  unfold ssum
  have : ∀ ε : ι → ℤˣ, (∑ i, ((ε i : ℤ) : ℝ) * c i) * (∑ j, ((ε j : ℤ) : ℝ) * d j)
      = ∑ i, ∑ j, (c i * d j) * (((ε i : ℤ) : ℝ) * ((ε j : ℤ) : ℝ)) := by
    intro ε; rw [Finset.sum_mul_sum]; refine Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ => by ring))
  simp_rw [this]
  rw [EE_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [EE_sum, Finset.sum_eq_single i]
  · rw [EE_smul]
    simp_rw [unit_sq]; rw [EE_const, mul_one]
  · intro j _ hj; rw [EE_smul, EE_coord_mul i j (Ne.symm hj), mul_zero]
  · simp

lemma EE_ssum_sq (c : ι → ℝ) : EE (fun ε => ssum ε c ^ 2) = ∑ i, c i ^ 2 := by
  have := EE_ssum_mul c c
  simp_rw [sq]; exact this

/-- Chebyshev for signed sums. -/
lemma cheb_ssum (c : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    PP (fun ε => t ≤ |ssum ε c|) ≤ (∑ i, c i ^ 2) / t ^ 2 := by
  have := chebyshev (fun ε => ssum ε c) ht
  rwa [EE_ssum_sq] at this

/-- Weighted Cauchy–Schwarz: if `E X_j² ≤ μ_j²` then `E (∑ w_j |X_j|)² ≤ (∑ w_j μ_j)²`. -/
lemma EE_wsum_sq {κ : Type*} (s : Finset κ) (w μ : κ → ℝ) (X : κ → (ι → ℤˣ) → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hμ : ∀ k ∈ s, 0 < μ k) (hX : ∀ k ∈ s, EE (fun ε => X k ε ^ 2) ≤ μ k ^ 2) :
    EE (fun ε => (∑ k ∈ s, w k * |X k ε|) ^ 2) ≤ (∑ k ∈ s, w k * μ k) ^ 2 := by
  set W := ∑ k ∈ s, w k * μ k with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun k hk => mul_nonneg (hw k hk) (hμ k hk).le)
  have hpt : ∀ ε, (∑ k ∈ s, w k * |X k ε|) ^ 2 ≤ W * ∑ k ∈ s, w k * (X k ε ^ 2 / μ k) := by
    intro ε
    have := Finset.sum_mul_sq_le_sq_mul_sq s (fun k => √(w k * μ k)) (fun k => √(w k / μ k) * |X k ε|)
    have e1 : ∀ k ∈ s, √(w k * μ k) * (√(w k / μ k) * |X k ε|) = w k * |X k ε| := by
      intro k hk
      rw [← mul_assoc, ← Real.sqrt_mul (mul_nonneg (hw k hk) (hμ k hk).le)]
      have : w k * μ k * (w k / μ k) = w k ^ 2 := by field_simp [(hμ k hk).ne']
      rw [this, Real.sqrt_sq (hw k hk)]
    have e2 : ∀ k ∈ s, √(w k * μ k) ^ 2 = w k * μ k := fun k hk =>
      Real.sq_sqrt (mul_nonneg (hw k hk) (hμ k hk).le)
    have e3 : ∀ k ∈ s, (√(w k / μ k) * |X k ε|) ^ 2 = w k * (X k ε ^ 2 / μ k) := by
      intro k hk
      rw [mul_pow, Real.sq_sqrt (div_nonneg (hw k hk) (hμ k hk).le), sq_abs]; ring
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at this
    exact this
  calc EE (fun ε => (∑ k ∈ s, w k * |X k ε|) ^ 2)
      ≤ EE (fun ε => W * ∑ k ∈ s, w k * (X k ε ^ 2 / μ k)) := EE_mono hpt
    _ = W * ∑ k ∈ s, w k * (EE (fun ε => X k ε ^ 2) / μ k) := by
        rw [EE_smul, EE_sum]; congr 1
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [show (fun ε => w k * (X k ε ^ 2 / μ k)) = (fun ε => (w k / μ k) * X k ε ^ 2) by
          ext ε; ring, EE_smul]; ring
    _ ≤ W * ∑ k ∈ s, w k * (μ k ^ 2 / μ k) := by
        gcongr with k hk
        · exact hw k hk
        · exact (hμ k hk).le
        · exact hX k hk
    _ = W ^ 2 := by
        rw [sq, hW]; congr 1
        refine Finset.sum_congr rfl (fun k hk => ?_)
        field_simp [(hμ k hk).ne']

/-! ### Independence of disjoint coordinate sets -/

/-- `f` only depends on the coordinates in `A`. -/
def DepOn (A : Finset ι) (f : (ι → ℤˣ) → ℝ) : Prop :=
  ∀ ε ε' : ι → ℤˣ, (∀ i ∈ A, ε i = ε' i) → f ε = f ε'

lemma EE_mul_indep (A : Finset ι) (f g : (ι → ℤˣ) → ℝ) (hf : DepOn A f)
    (hg : DepOn Aᶜ g) : EE (fun ε => f ε * g ε) = EE f * EE g := by
  classical
  set p : ι → Prop := fun i => i ∈ A
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => ℤˣ)
  -- glue two partial sign vectors
  let glue : ({i // p i} → ℤˣ) → ({i // ¬ p i} → ℤˣ) → (ι → ℤˣ) := fun α β => e.symm (α, β)
  have hglue1 : ∀ α β, ∀ i (hi : p i), glue α β i = α ⟨i, hi⟩ := by
    intro α β i hi; simp [glue, e, Equiv.piEquivPiSubtypeProd, hi]
  have hglue2 : ∀ α β, ∀ i (hi : ¬ p i), glue α β i = β ⟨i, hi⟩ := by
    intro α β i hi; simp [glue, e, Equiv.piEquivPiSubtypeProd, hi]
  -- choose a reference point
  let β0 : {i // ¬ p i} → ℤˣ := fun _ => 1
  let α0 : {i // p i} → ℤˣ := fun _ => 1
  have hf' : ∀ α β, f (glue α β) = f (glue α β0) := by
    intro α β; apply hf; intro i hi
    rw [hglue1 α β i hi, hglue1 α β0 i hi]
  have hg' : ∀ α β, g (glue α β) = g (glue α0 β) := by
    intro α β; apply hg; intro i hi
    have hi' : ¬ p i := by simpa [p] using hi
    rw [hglue2 α β i hi', hglue2 α0 β i hi']
  have hsum : ∀ F : (ι → ℤˣ) → ℝ, ∑ ε, F ε = ∑ α, ∑ β, F (glue α β) := by
    intro F
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  have hcard : (2 : ℝ) ^ Fintype.card ι
      = (2 : ℝ) ^ Fintype.card {i // p i} * (2 : ℝ) ^ Fintype.card {i // ¬ p i} := by
    rw [← pow_add, Fintype.card_subtype_compl]
    congr 1; have := Fintype.card_subtype_le p; omega
  have hA : ∑ ε, f ε = (∑ α, f (glue α β0)) * 2 ^ Fintype.card {i // ¬ p i} := by
    rw [hsum]; simp_rw [hf']
    rw [Finset.sum_mul]; congr 1; ext α
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    congr 1
    rw [Fintype.card_fun, Fintype.card_units_int]; push_cast; rfl
  have hB : ∑ ε, g ε = (∑ β, g (glue α0 β)) * 2 ^ Fintype.card {i // p i} := by
    rw [hsum, Finset.sum_comm]; simp_rw [hg']
    rw [Finset.sum_mul]; congr 1; ext β
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    congr 1
    rw [Fintype.card_fun, Fintype.card_units_int]; push_cast; rfl
  have hAB : ∑ ε, f ε * g ε = (∑ α, f (glue α β0)) * (∑ β, g (glue α0 β)) := by
    rw [hsum]
    simp_rw [hf', hg']
    rw [Finset.sum_mul_sum]
  unfold EE
  rw [hAB, hA, hB, hcard]
  field_simp

end R522

end S_RR2

-- ===== RR3 =====

/-!
# Erdős 522 (real roots), part 3: a two-point CLT by Fourier inversion

For Schwartz test functions `ψ₁, ψ₂` and unit weight vectors `a, b` with correlation `ρ`,
the sign-vector average of `ψ₁(∑ ε a) ψ₂(∑ ε b)` and the Gaussian average of `ψ₁(Z₁) ψ₂(ρ Z₁ + σ Z₂)`
(`σ² = 1 - ρ²`) are both `∫∫ 𝓕ψ₁ 𝓕ψ₂ · K`, with `K` a cosine product resp. a Gaussian; their
difference is at most `16 (2π)⁴ (M₄ψ₁ M₀ψ₂ ∑ a⁴ + M₀ψ₁ M₄ψ₂ ∑ b⁴)`.
-/

open Finset Real MeasureTheory FourierTransform ProbabilityTheory

noncomputable section S_RR3

namespace R522

lemma schwartz_inv (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    ψ x = ∫ ξ : ℝ, Complex.exp (↑(2 * π * ξ * x) * Complex.I) * 𝓕 (ψ : ℝ → ℂ) ξ := by
  have h := ψ.continuous.fourierInv_fourier_eq ψ.integrable (by
    rw [← SchwartzMap.fourier_coe]; exact (𝓕 ψ).integrable)
  have := congrFun h x
  rw [← this, Real.fourierInv_eq']
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
  congr 1; ext ξ; congr 3; push_cast; ring

lemma fourier_integrable (ψ : SchwartzMap ℝ ℂ) : Integrable (𝓕 (ψ : ℝ → ℂ)) := by
  rw [← SchwartzMap.fourier_coe]; exact (𝓕 ψ).integrable

lemma fourier_continuous (ψ : SchwartzMap ℝ ℂ) : Continuous (𝓕 (ψ : ℝ → ℂ)) := by
  rw [← SchwartzMap.fourier_coe]; exact (𝓕 ψ).continuous

lemma integrable_exp_mul_fourier (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    Integrable (fun ξ : ℝ => Complex.exp (↑(2 * π * ξ * x) * Complex.I) * 𝓕 (ψ : ℝ → ℂ) ξ) := by
  refine (fourier_integrable ψ).bdd_mul (c := 1) (by fun_prop) ?_
  refine Filter.Eventually.of_forall (fun ξ => ?_)
  rw [Complex.norm_exp_ofReal_mul_I]

/-- Fourier moments. -/
def Mom (k : ℕ) (ψ : SchwartzMap ℝ ℂ) : ℝ := ∫ u : ℝ, |u| ^ k * ‖𝓕 (ψ : ℝ → ℂ) u‖

lemma integrable_mom (k : ℕ) (ψ : SchwartzMap ℝ ℂ) :
    Integrable (fun u : ℝ => |u| ^ k * ‖𝓕 (ψ : ℝ → ℂ) u‖) := by
  have := (𝓕 ψ).integrable_pow_mul volume k
  rw [SchwartzMap.fourier_coe] at this
  simpa [Real.norm_eq_abs] using this

lemma mom_nonneg (k : ℕ) (ψ : SchwartzMap ℝ ℂ) : 0 ≤ Mom k ψ :=
  integral_nonneg (fun u => by positivity)

lemma mom_zero (ψ : SchwartzMap ℝ ℂ) : Mom 0 ψ = ∫ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) u‖ := by
  simp [Mom]

/-! ### The sign-vector side -/

lemma sum_units_exp (ξ c : ℝ) :
    ∑ u : ℤˣ, Complex.exp (↑(2 * π * ξ * (((u : ℤ) : ℝ) * c)) * Complex.I)
      = 2 * (Real.cos (2 * π * ξ * c) : ℂ) := by
  rw [show (Finset.univ : Finset ℤˣ) = {1, -1} from by decide]
  rw [Finset.sum_pair (by decide)]
  simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_mul]
  rw [Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

lemma sum_signs_exp {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) (ξ : ℝ) :
    ∑ b : ι → ℤˣ, Complex.exp (↑(2 * π * ξ * ∑ i, ((b i : ℤ) : ℝ) * c i) * Complex.I)
      = ∏ i, 2 * (Real.cos (2 * π * ξ * c i) : ℂ) := by
  have : ∀ b : ι → ℤˣ, Complex.exp (↑(2 * π * ξ * ∑ i, ((b i : ℤ) : ℝ) * c i) * Complex.I)
      = ∏ i, Complex.exp (↑(2 * π * ξ * (((b i : ℤ) : ℝ) * c i)) * Complex.I) := by
    intro b
    rw [← Complex.exp_sum]
    congr 1
    rw [← Finset.sum_mul]
    congr 1
    push_cast
    rw [Finset.mul_sum]
  simp_rw [this]
  rw [← Fintype.prod_sum (fun i (u : ℤˣ) =>
    Complex.exp (↑(2 * π * ξ * (((u : ℤ) : ℝ) * c i)) * Complex.I))]
  simp_rw [sum_units_exp]

/-- **Two-point identity on the sign side.** -/
theorem avg_two {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ₁ ψ₂ : SchwartzMap ℝ ℂ)
    (c d : ι → ℝ) :
    (∑ b : ι → ℤˣ, ψ₁ (ssum b c) * ψ₂ (ssum b d)) / 2 ^ Fintype.card ι
      = ∫ u : ℝ, ∫ v : ℝ, 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v *
          ∏ i, (Real.cos (2 * π * (u * c i + v * d i)) : ℂ) := by
  set F₁ := 𝓕 (ψ₁ : ℝ → ℂ)
  set F₂ := 𝓕 (ψ₂ : ℝ → ℂ)
  have hprod : ∀ x y : ℝ, ψ₁ x * ψ₂ y = ∫ u : ℝ, ∫ v : ℝ,
      Complex.exp (↑(2 * π * u * x) * Complex.I) * Complex.exp (↑(2 * π * v * y) * Complex.I) *
        (F₁ u * F₂ v) := by
    intro x y
    rw [schwartz_inv ψ₁ x, schwartz_inv ψ₂ y, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    simp only; ring
  have hinner : ∀ (x y u : ℝ), Integrable (fun v : ℝ =>
      Complex.exp (↑(2 * π * u * x) * Complex.I) * Complex.exp (↑(2 * π * v * y) * Complex.I) *
        (F₁ u * F₂ v)) := by
    intro x y u
    have := (integrable_exp_mul_fourier ψ₂ y).const_mul
      (Complex.exp (↑(2 * π * u * x) * Complex.I) * F₁ u)
    refine this.congr (Filter.Eventually.of_forall (fun v => ?_))
    simp only; ring
  have hinner_eval : ∀ (x y u : ℝ), ∫ v : ℝ,
      Complex.exp (↑(2 * π * u * x) * Complex.I) * Complex.exp (↑(2 * π * v * y) * Complex.I) *
        (F₁ u * F₂ v) = Complex.exp (↑(2 * π * u * x) * Complex.I) * F₁ u * ψ₂ y := by
    intro x y u
    rw [schwartz_inv ψ₂ y, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    simp only; ring
  have houter : ∀ x y : ℝ, Integrable (fun u : ℝ => ∫ v : ℝ,
      Complex.exp (↑(2 * π * u * x) * Complex.I) * Complex.exp (↑(2 * π * v * y) * Complex.I) *
        (F₁ u * F₂ v)) := by
    intro x y
    simp_rw [hinner_eval x y]
    exact (integrable_exp_mul_fourier ψ₁ x).mul_const _
  simp_rw [hprod]
  rw [← integral_finsetSum _ (fun b _ => houter _ _)]
  rw [div_eq_mul_inv, mul_comm, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  simp only
  rw [← integral_finsetSum _ (fun b _ => hinner _ _ u)]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only
  have hc : ∀ b : ι → ℤˣ, Complex.exp (↑(2 * π * u * ssum b c) * Complex.I) *
      Complex.exp (↑(2 * π * v * ssum b d) * Complex.I)
      = Complex.exp (↑(2 * π * ∑ i, ((b i : ℤ) : ℝ) * (u * c i + v * d i)) * Complex.I) := by
    intro b
    unfold ssum
    rw [← Complex.exp_add]; congr 1
    push_cast
    simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    rw [← add_mul]; congr 1
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [← mul_assoc, hc]
  have hs := sum_signs_exp (fun i => u * c i + v * d i) 1
  simp only [mul_one] at hs
  rw [← Finset.sum_mul, ← Finset.sum_mul, hs, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  field_simp

/-! ### The Gaussian side -/

/-- Fubini for a probability measure. -/
theorem fub_two {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (ψ₁ ψ₂ : SchwartzMap ℝ ℂ) :
    ∫ ω, ψ₁ (X ω) * ψ₂ (Y ω) ∂μ = ∫ u : ℝ, ∫ v : ℝ, 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v *
      ∫ ω, Complex.exp (↑(2 * π * (u * X ω + v * Y ω)) * Complex.I) ∂μ := by
  set F₁ := 𝓕 (ψ₁ : ℝ → ℂ)
  set F₂ := 𝓕 (ψ₂ : ℝ → ℂ)
  have hF₁ := fourier_integrable ψ₁
  have hF₂ := fourier_integrable ψ₂
  have cF₁ := fourier_continuous ψ₁
  have cF₂ := fourier_continuous ψ₂
  obtain ⟨C₂, hC₂⟩ : ∃ C, ∀ y, ‖ψ₂ y‖ ≤ C := ⟨SchwartzMap.seminorm ℝ 0 0 ψ₂, fun y => by
    have := ψ₂.le_seminorm ℝ 0 0 y; simpa [norm_iteratedFDeriv_zero] using this⟩
  -- step 1: expand `ψ₁` and swap
  have step1 : ∀ ω, ψ₁ (X ω) * ψ₂ (Y ω)
      = ∫ u : ℝ, Complex.exp (↑(2 * π * u * X ω) * Complex.I) * F₁ u * ψ₂ (Y ω) := by
    intro ω; rw [schwartz_inv ψ₁, ← integral_mul_const]
  have int1 : Integrable (Function.uncurry fun (ω : Ω) (u : ℝ) =>
      Complex.exp (↑(2 * π * u * X ω) * Complex.I) * F₁ u * ψ₂ (Y ω)) (μ.prod volume) := by
    refine Integrable.mono' ((integrable_const C₂).mul_prod hF₁.norm) ?_ ?_
    · have m1 : Measurable (fun p : Ω × ℝ => (X p.1, p.2, Y p.1)) :=
        (hX.comp measurable_fst).prodMk (measurable_snd.prodMk (hY.comp measurable_fst))
      have c1 : Continuous (fun q : ℝ × ℝ × ℝ =>
          Complex.exp (↑(2 * π * q.2.1 * q.1) * Complex.I) * F₁ q.2.1 * ψ₂ q.2.2) :=
        ((by fun_prop : Continuous fun (q : ℝ × ℝ × ℝ) =>
          Complex.exp (↑(2 * π * q.2.1 * q.1) * Complex.I)).mul (cF₁.comp (by fun_prop))).mul
          (ψ₂.continuous.comp (by fun_prop))
      exact (c1.measurable.comp m1).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun p => ?_)
      simp only [Function.uncurry, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hC₂ _) (norm_nonneg _)
  have hL : ∫ ω, ψ₁ (X ω) * ψ₂ (Y ω) ∂μ
      = ∫ u : ℝ, F₁ u * ∫ ω, Complex.exp (↑(2 * π * u * X ω) * Complex.I) * ψ₂ (Y ω) ∂μ := by
    simp_rw [step1]
    rw [integral_integral_swap int1]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    simp only; ring
  rw [hL]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  simp only
  -- step 2: expand `ψ₂` and swap
  have step2 : ∀ ω, Complex.exp (↑(2 * π * u * X ω) * Complex.I) * ψ₂ (Y ω)
      = ∫ v : ℝ, Complex.exp (↑(2 * π * u * X ω) * Complex.I) *
          Complex.exp (↑(2 * π * v * Y ω) * Complex.I) * F₂ v := by
    intro ω; rw [schwartz_inv ψ₂, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_)); simp only; ring
  have int2 : Integrable (Function.uncurry fun (ω : Ω) (v : ℝ) =>
      Complex.exp (↑(2 * π * u * X ω) * Complex.I) *
          Complex.exp (↑(2 * π * v * Y ω) * Complex.I) * F₂ v) (μ.prod volume) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod hF₂.norm) ?_ ?_
    · have m1 : Measurable (fun p : Ω × ℝ => (X p.1, p.2, Y p.1)) :=
        (hX.comp measurable_fst).prodMk (measurable_snd.prodMk (hY.comp measurable_fst))
      have c1 : Continuous (fun q : ℝ × ℝ × ℝ =>
          Complex.exp (↑(2 * π * u * q.1) * Complex.I) *
            Complex.exp (↑(2 * π * q.2.1 * q.2.2) * Complex.I) * F₂ q.2.1) :=
        (by fun_prop : Continuous fun (q : ℝ × ℝ × ℝ) =>
          Complex.exp (↑(2 * π * u * q.1) * Complex.I) *
            Complex.exp (↑(2 * π * q.2.1 * q.2.2) * Complex.I)).mul (cF₂.comp (by fun_prop))
      exact (c1.measurable.comp m1).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun p => ?_)
      simp only [Function.uncurry, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact le_refl _
  simp_rw [step2]
  rw [integral_integral_swap int2, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  simp only
  rw [show (↑(2 * π * (u * X ω + v * Y ω)) * Complex.I : ℂ)
      = ↑(2 * π * u * X ω) * Complex.I + ↑(2 * π * v * Y ω) * Complex.I by push_cast; ring,
    Complex.exp_add]
  ring

/-- The standard Gaussian. -/
abbrev γ : Measure ℝ := gaussianReal 0 1

lemma gauss_char (t : ℝ) : ∫ x, Complex.exp (↑(t * x) * Complex.I) ∂γ = Complex.exp (-(t ^ 2 / 2 : ℝ)) := by
  have h := charFun_gaussianReal (μ := 0) (v := 1) t
  rw [charFun_apply_real] at h
  rw [show (fun x : ℝ => Complex.exp (↑(t * x) * Complex.I)) = fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I) by
    ext x; push_cast; ring_nf]
  rw [h]; congr 1; push_cast; ring

/-- **Two-point identity on the Gaussian side.** -/
theorem gauss_two (ψ₁ ψ₂ : SchwartzMap ℝ ℂ) (ρ σ : ℝ) :
    ∫ z, ψ₁ z.1 * ψ₂ (ρ * z.1 + σ * z.2) ∂(γ.prod γ)
      = ∫ u : ℝ, ∫ v : ℝ, 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v *
          Complex.exp (-(2 * π ^ 2 * ((u + ρ * v) ^ 2 + σ ^ 2 * v ^ 2) : ℝ)) := by
  rw [fub_two (γ.prod γ) (fun z => z.1) (fun z => ρ * z.1 + σ * z.2) measurable_fst
    (by fun_prop) ψ₁ ψ₂]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only
  congr 1
  have : ∀ z : ℝ × ℝ, Complex.exp (↑(2 * π * (u * z.1 + v * (ρ * z.1 + σ * z.2))) * Complex.I)
      = Complex.exp (↑((2 * π * (u + ρ * v)) * z.1) * Complex.I) *
          Complex.exp (↑((2 * π * σ * v) * z.2) * Complex.I) := by
    intro z; rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [this]
  rw [integral_prod_mul (fun x => Complex.exp (↑((2 * π * (u + ρ * v)) * x) * Complex.I))
    (fun y => Complex.exp (↑((2 * π * σ * v) * y) * Complex.I)), gauss_char, gauss_char,
    ← Complex.exp_add]
  congr 1; push_cast; ring

/-! ### The error -/

lemma cos_exp_err (θ : ℝ) : |Real.cos θ - Real.exp (-(θ ^ 2 / 2))| ≤ 2 * θ ^ 4 := by
  by_cases hθ : |θ| ≤ 1
  · have h1 := Real.cos_bound hθ
    have hy : |-(θ ^ 2 / 2)| ≤ 1 := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
      have : θ ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg θ]
      linarith
    have h2 := Real.abs_exp_sub_one_sub_id_le hy
    have h4 : |θ| ^ 4 = θ ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
    rw [h4] at h1
    have : (-(θ ^ 2 / 2)) ^ 2 = θ ^ 4 / 4 := by ring
    rw [this] at h2
    calc |Real.cos θ - Real.exp (-(θ ^ 2 / 2))|
        = |(Real.cos θ - (1 - θ ^ 2 / 2)) - (Real.exp (-(θ ^ 2 / 2)) - 1 - -(θ ^ 2 / 2))| := by
          congr 1; ring
      _ ≤ |Real.cos θ - (1 - θ ^ 2 / 2)| + |Real.exp (-(θ ^ 2 / 2)) - 1 - -(θ ^ 2 / 2)| :=
          abs_sub _ _
      _ ≤ θ ^ 4 * (5 / 96) + θ ^ 4 / 4 := add_le_add h1 h2
      _ ≤ 2 * θ ^ 4 := by nlinarith [pow_nonneg (sq_nonneg θ) 2]
  · push Not at hθ
    have h1 : 1 ≤ θ ^ 4 := by
      have : 1 ≤ |θ| ^ 4 := one_le_pow₀ hθ.le
      rwa [← abs_pow, abs_of_nonneg (by positivity)] at this
    have hc := Real.abs_cos_le_one θ
    have he : |Real.exp (-(θ ^ 2 / 2))| ≤ 1 := by
      rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg θ])
    calc _ ≤ |Real.cos θ| + |Real.exp (-(θ ^ 2 / 2))| := abs_sub _ _
      _ ≤ 2 := by linarith
      _ ≤ 2 * θ ^ 4 := by linarith

lemma prod_sub_prod_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ) (hx : ∀ i ∈ s, |x i| ≤ 1)
    (hy : ∀ i ∈ s, |y i| ≤ 1) : |∏ i ∈ s, x i - ∏ i ∈ s, y i| ≤ ∑ i ∈ s, |x i - y i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have ih' := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
      (fun i hi => hy i (Finset.mem_insert_of_mem hi))
    have hxa := hx a (Finset.mem_insert_self a s)
    have hPy : |∏ i ∈ s, y i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun i _ => abs_nonneg _)
        (fun i hi => hy i (Finset.mem_insert_of_mem hi))
    calc |x a * ∏ i ∈ s, x i - y a * ∏ i ∈ s, y i|
        = |x a * (∏ i ∈ s, x i - ∏ i ∈ s, y i) + (x a - y a) * ∏ i ∈ s, y i| := by congr 1; ring
      _ ≤ |x a| * |∏ i ∈ s, x i - ∏ i ∈ s, y i| + |x a - y a| * |∏ i ∈ s, y i| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
      _ ≤ 1 * ∑ i ∈ s, |x i - y i| + |x a - y a| * 1 := by
          gcongr
      _ = |x a - y a| + ∑ i ∈ s, |x i - y i| := by ring

lemma sum_fourth_le (s t : ℝ) (a b : ℝ) : (s * a + t * b) ^ 4 ≤ 8 * (s ^ 4 * a ^ 4 + t ^ 4 * b ^ 4) := by
  nlinarith [sq_nonneg (s * a - t * b), sq_nonneg (s * a + t * b), sq_nonneg ((s*a)^2 - (t*b)^2),
    sq_nonneg (s*a), sq_nonneg (t*b), mul_self_nonneg (s * a * (t * b))]

lemma norm_iter_le {k : ℕ} (f : ℝ → ℝ → ℂ) (a b : Fin k → ℝ → ℝ) (ha : ∀ i, Integrable (a i))
    (hb : ∀ i, Integrable (b i)) (h : ∀ u v, ‖f u v‖ ≤ ∑ i, a i u * b i v) :
    ‖∫ u, ∫ v, f u v‖ ≤ ∑ i, (∫ u, a i u) * (∫ v, b i v) := by
  have hin : ∀ u, ‖∫ v, f u v‖ ≤ ∑ i, a i u * ∫ v, b i v := by
    intro u
    refine (norm_integral_le_of_norm_le (g := fun v => ∑ i, a i u * b i v)
      (integrable_finsetSum _ (fun i _ => (hb i).const_mul _))
      (Filter.Eventually.of_forall (h u))).trans (le_of_eq ?_)
    rw [integral_finsetSum _ (fun i _ => (hb i).const_mul _)]
    exact Finset.sum_congr rfl (fun i _ => integral_const_mul _ _)
  refine (norm_integral_le_of_norm_le (g := fun u => ∑ i, a i u * ∫ v, b i v)
    (integrable_finsetSum _ (fun i _ => (ha i).mul_const _))
    (Filter.Eventually.of_forall hin)).trans (le_of_eq ?_)
  rw [integral_finsetSum _ (fun i _ => (ha i).mul_const _)]
  exact Finset.sum_congr rfl (fun i _ => integral_mul_const _ _)

/-- Integrability of a bounded kernel against `𝓕ψ₁ ⊗ 𝓕ψ₂`. -/
lemma int_kernel (ψ₁ ψ₂ : SchwartzMap ℝ ℂ) (K : ℝ → ℝ → ℂ) (hK : Continuous (Function.uncurry K))
    (hK1 : ∀ u v, ‖K u v‖ ≤ 1) :
    Integrable (Function.uncurry fun u v => 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v * K u v)
      (volume.prod volume) := by
  refine Integrable.mono' ((fourier_integrable ψ₁).norm.mul_prod (fourier_integrable ψ₂).norm) ?_ ?_
  · exact (((fourier_continuous ψ₁).comp continuous_fst).mul
      ((fourier_continuous ψ₂).comp continuous_snd) |>.mul hK).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun p => ?_)
    simp only [Function.uncurry, norm_mul]
    have := hK1 p.1 p.2
    calc ‖𝓕 (ψ₁ : ℝ → ℂ) p.1‖ * ‖𝓕 (ψ₂ : ℝ → ℂ) p.2‖ * ‖K p.1 p.2‖
        ≤ ‖𝓕 (ψ₁ : ℝ → ℂ) p.1‖ * ‖𝓕 (ψ₂ : ℝ → ℂ) p.2‖ * 1 := by gcongr
      _ = _ := by ring

lemma int_kernel_u (ψ₁ ψ₂ : SchwartzMap ℝ ℂ) (K : ℝ → ℝ → ℂ) (hK : ∀ u, Continuous (K u))
    (hK1 : ∀ u v, ‖K u v‖ ≤ 1) (u : ℝ) :
    Integrable (fun v => 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v * K u v) := by
  refine Integrable.mono' ((fourier_integrable ψ₂).norm.const_mul ‖𝓕 (ψ₁ : ℝ → ℂ) u‖) ?_ ?_
  · exact ((continuous_const.mul (fourier_continuous ψ₂)).mul (hK u)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun v => ?_)
    simp only [norm_mul]
    have := hK1 u v
    calc ‖𝓕 (ψ₁ : ℝ → ℂ) u‖ * ‖𝓕 (ψ₂ : ℝ → ℂ) v‖ * ‖K u v‖
        ≤ ‖𝓕 (ψ₁ : ℝ → ℂ) u‖ * ‖𝓕 (ψ₂ : ℝ → ℂ) v‖ * 1 := by gcongr
      _ = _ := by ring

/-- The Gaussian kernel. -/
def gk (ρ : ℝ) (u v : ℝ) : ℝ := Real.exp (-(2 * π ^ 2 * (u ^ 2 + 2 * ρ * u * v + v ^ 2)))

/-- The kernel difference. -/
lemma kernel_diff {ι : Type*} [Fintype ι] (a b : ι → ℝ) (ρ : ℝ) (ha : ∑ i, a i ^ 2 = 1)
    (hb : ∑ i, b i ^ 2 = 1) (hab : ∑ i, a i * b i = ρ) (u v : ℝ) :
    |∏ i, Real.cos (2 * π * (u * a i + v * b i)) - gk ρ u v|
      ≤ 16 * (2 * π) ^ 4 * ((∑ i, a i ^ 4) * u ^ 4 + (∑ i, b i ^ 4) * v ^ 4) := by
  have hg : gk ρ u v = ∏ i, Real.exp (-((2 * π * (u * a i + v * b i)) ^ 2 / 2)) := by
    rw [← Real.exp_sum]; unfold gk; congr 1
    rw [Finset.sum_neg_distrib]
    have : ∑ i, (2 * π * (u * a i + v * b i)) ^ 2 / 2
        = 2 * π ^ 2 * (u ^ 2 * ∑ i, a i ^ 2 + 2 * u * v * ∑ i, a i * b i + v ^ 2 * ∑ i, b i ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [this, ha, hb, hab]; ring
  rw [hg]
  refine (prod_sub_prod_le _ _ _ (fun i _ => Real.abs_cos_le_one _) (fun i _ => by
    rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_one_iff.2 (by
      have := sq_nonneg (2 * π * (u * a i + v * b i)); linarith))).trans ?_
  have hpi : (0 : ℝ) ≤ (2 * π) ^ 4 := by positivity
  calc ∑ i, |Real.cos (2 * π * (u * a i + v * b i)) - Real.exp (-((2 * π * (u * a i + v * b i)) ^ 2 / 2))|
      ≤ ∑ i, 2 * (2 * π * (u * a i + v * b i)) ^ 4 :=
        Finset.sum_le_sum (fun i _ => cos_exp_err _)
    _ ≤ ∑ i, 2 * (2 * π) ^ 4 * (8 * (u ^ 4 * a i ^ 4 + v ^ 4 * b i ^ 4)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [show (2 * π * (u * a i + v * b i)) ^ 4 = (2 * π) ^ 4 * (u * a i + v * b i) ^ 4 by ring,
          ← mul_assoc]
        exact mul_le_mul_of_nonneg_left (sum_fourth_le u v (a i) (b i)) (by positivity)
    _ = 16 * (2 * π) ^ 4 * ((∑ i, a i ^ 4) * u ^ 4 + (∑ i, b i ^ 4) * v ^ 4) := by
        rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => by ring)

lemma abs_rho_le {ι : Type*} [Fintype ι] (a b : ι → ℝ) (ρ : ℝ) (ha : ∑ i, a i ^ 2 = 1)
    (hb : ∑ i, b i ^ 2 = 1) (hab : ∑ i, a i * b i = ρ) : ρ ^ 2 ≤ 1 := by
  rw [← hab]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  rw [ha, hb, one_mul] at h2; exact h2

lemma gk_le_one (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1) (u v : ℝ) : |gk ρ u v| ≤ 1 := by
  unfold gk
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
  have : 0 ≤ u ^ 2 + 2 * ρ * u * v + v ^ 2 := by
    nlinarith [sq_nonneg (u + ρ * v), sq_nonneg v]
  positivity

/-- **Two-point CLT.** -/
theorem clt_two {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ₁ ψ₂ : SchwartzMap ℝ ℂ)
    (a b : ι → ℝ) (ρ : ℝ) (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hab : ∑ i, a i * b i = ρ) :
    ‖(∑ ε : ι → ℤˣ, ψ₁ (ssum ε a) * ψ₂ (ssum ε b)) / 2 ^ Fintype.card ι
      - ∫ u : ℝ, ∫ v : ℝ, 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v * (gk ρ u v : ℂ)‖
      ≤ 16 * (2 * π) ^ 4 * (Mom 4 ψ₁ * Mom 0 ψ₂ * ∑ i, a i ^ 4 + Mom 0 ψ₁ * Mom 4 ψ₂ * ∑ i, b i ^ 4) := by
  rw [avg_two]
  have hρ := abs_rho_le a b ρ ha hb hab
  obtain ⟨Kc, hKc⟩ : ∃ K : ℝ → ℝ → ℂ, K = fun u v => ∏ i, (Real.cos (2 * π * (u * a i + v * b i)) : ℂ) :=
    ⟨_, rfl⟩
  obtain ⟨Kg, hKg⟩ : ∃ K : ℝ → ℝ → ℂ, K = fun u v => (gk ρ u v : ℂ) := ⟨_, rfl⟩
  have eC : ∀ u v, (∏ i, (Real.cos (2 * π * (u * a i + v * b i)) : ℂ)) = Kc u v := by
    intro u v; rw [hKc]
  have eG : ∀ u v, ((gk ρ u v : ℝ) : ℂ) = Kg u v := by intro u v; rw [hKg]
  simp_rw [eC, eG]
  have hKc1 : ∀ u v, ‖Kc u v‖ ≤ 1 := by
    intro u v; rw [hKc]; simp only [norm_prod]
    exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hKg1 : ∀ u v, ‖Kg u v‖ ≤ 1 := by
    intro u v; rw [hKg]; simp only [Complex.norm_real, Real.norm_eq_abs]
    exact gk_le_one ρ hρ u v
  have cKc : Continuous (Function.uncurry Kc) := by
    rw [hKc]; exact continuous_finsetProd _ (fun i _ => by fun_prop)
  have cKg : Continuous (Function.uncurry Kg) := by
    rw [hKg]; simp only [gk]; fun_prop
  have hdiff : ∀ u v, ‖Kc u v - Kg u v‖
      ≤ 16 * (2 * π) ^ 4 * ((∑ i, a i ^ 4) * u ^ 4 + (∑ i, b i ^ 4) * v ^ 4) := by
    intro u v
    rw [hKc, hKg]; simp only
    rw [← Complex.ofReal_prod, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact kernel_diff a b ρ ha hb hab u v
  set F₁ := 𝓕 (ψ₁ : ℝ → ℂ)
  set F₂ := 𝓕 (ψ₂ : ℝ → ℂ)
  have iC := int_kernel ψ₁ ψ₂ Kc cKc hKc1
  have iG := int_kernel ψ₁ ψ₂ Kg cKg hKg1
  have iCu := int_kernel_u ψ₁ ψ₂ Kc (fun u => cKc.comp (Continuous.prodMk_right u)) hKc1
  have iGu := int_kernel_u ψ₁ ψ₂ Kg (fun u => cKg.comp (Continuous.prodMk_right u)) hKg1
  have iC' : Integrable (fun u => ∫ v, F₁ u * F₂ v * Kc u v) := iC.integral_prod_left
  have iG' : Integrable (fun u => ∫ v, F₁ u * F₂ v * Kg u v) := iG.integral_prod_left
  rw [← integral_sub iC' iG']
  have : ∀ u, (∫ v, F₁ u * F₂ v * Kc u v) - ∫ v, F₁ u * F₂ v * Kg u v
      = ∫ v, F₁ u * F₂ v * (Kc u v - Kg u v) := by
    intro u; rw [← integral_sub (iCu u) (iGu u)]; congr 1; ext v; ring
  simp_rw [this]
  set A4 := ∑ i, a i ^ 4
  set B4 := ∑ i, b i ^ 4
  set C0 := 16 * (2 * π) ^ 4
  have hA : 0 ≤ A4 := Finset.sum_nonneg (fun i _ => by positivity)
  have hB : 0 ≤ B4 := Finset.sum_nonneg (fun i _ => by positivity)
  have hC0 : 0 ≤ C0 := by positivity
  let fa : Fin 2 → ℝ → ℝ := ![fun u => C0 * A4 * (|u| ^ 4 * ‖F₁ u‖), fun u => C0 * B4 * (|u| ^ 0 * ‖F₁ u‖)]
  let fb : Fin 2 → ℝ → ℝ := ![fun v => |v| ^ 0 * ‖F₂ v‖, fun v => |v| ^ 4 * ‖F₂ v‖]
  have ia : ∀ i, Integrable (fa i) := by
    intro i; fin_cases i
    · exact (integrable_mom 4 ψ₁).const_mul _
    · exact (integrable_mom 0 ψ₁).const_mul _
  have ib : ∀ i, Integrable (fb i) := by
    intro i; fin_cases i
    · exact integrable_mom 0 ψ₂
    · exact integrable_mom 4 ψ₂
  have key := norm_iter_le (k := 2) (fun u v => F₁ u * F₂ v * (Kc u v - Kg u v)) fa fb ia ib (by
    intro u v
    simp only [fa, fb, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, pow_zero, one_mul]
    rw [norm_mul, norm_mul]
    have hu4 : |u| ^ 4 = u ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
    have hv4 : |v| ^ 4 = v ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
    rw [hu4, hv4]
    calc ‖F₁ u‖ * ‖F₂ v‖ * ‖Kc u v - Kg u v‖
        ≤ ‖F₁ u‖ * ‖F₂ v‖ * (C0 * (A4 * u ^ 4 + B4 * v ^ 4)) := by
          gcongr; exact hdiff u v
      _ = _ := by ring)
  refine key.trans (le_of_eq ?_)
  simp only [fa, fb, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [integral_const_mul, integral_const_mul]
  unfold Mom
  ring

end R522

end S_RR3

-- ===== RR4 =====

/-!
# Erdős 522 (real roots), part 4: Gaussian facts

* `wedge`: `(γ ⊗ γ) {z₁ > 0, ρ z₁ + σ z₂ < 0} = arccos ρ / (2π)` (polar coordinates).
* `wedge'`: the opposite wedge has the same measure.
* `law_Y`: `ρ z₁ + σ z₂` is standard Gaussian when `ρ² + σ² = 1`.
* `gauss_strip`, `gauss_tail`: `γ [a, a + w] ≤ w / √(2π)`, `γ {R ≤ |x|} ≤ 1 / R²`.
-/

open Finset Real MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section S_RR4

namespace R522

/-- The standard Gaussian density (as `ℝ≥0∞`). -/
abbrev φ : ℝ → ℝ≥0∞ := gaussianPDF 0 1

lemma γ_eq : γ = volume.withDensity φ := gaussianReal_of_var_ne_zero 0 one_ne_zero

lemma γγ_eq : γ.prod γ = (volume : Measure (ℝ × ℝ)).withDensity (fun z => φ z.1 * φ z.2) := by
  rw [γ_eq, prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
    Measure.volume_eq_prod]

lemma φ_apply (x : ℝ) : φ x = ENNReal.ofReal ((√(2 * π))⁻¹ * Real.exp (-x ^ 2 / 2)) := by
  simp [φ, gaussianPDF, gaussianPDFReal]

lemma φφ_polar (r θ : ℝ) : φ (r * Real.cos θ) * φ (r * Real.sin θ)
    = ENNReal.ofReal ((2 * π)⁻¹ * Real.exp (-r ^ 2 / 2)) := by
  rw [φ_apply, φ_apply, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have h1 : (√(2 * π))⁻¹ * (√(2 * π))⁻¹ = (2 * π)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  have h2 : Real.exp (-(r * Real.cos θ) ^ 2 / 2) * Real.exp (-(r * Real.sin θ) ^ 2 / 2)
      = Real.exp (-r ^ 2 / 2) := by
    rw [← Real.exp_add]; congr 1
    have := Real.sin_sq_add_cos_sq θ
    have : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
      rw [mul_pow, mul_pow, ← mul_add]; nlinarith
    linarith
  calc (√(2 * π))⁻¹ * Real.exp (-(r * Real.cos θ) ^ 2 / 2) * ((√(2 * π))⁻¹ * Real.exp (-(r * Real.sin θ) ^ 2 / 2))
      = ((√(2 * π))⁻¹ * (√(2 * π))⁻¹) * (Real.exp (-(r * Real.cos θ) ^ 2 / 2) *
          Real.exp (-(r * Real.sin θ) ^ 2 / 2)) := by ring
    _ = _ := by rw [h1, h2]

/-- Angular description of the wedge. -/
lemma wedge_angle {ρ : ℝ} (hρ1 : -1 < ρ) (hρ2 : ρ < 1) {r θ : ℝ} (hr : 0 < r)
    (hθ : θ ∈ Set.Ioo (-π) π) :
    (0 < r * Real.cos θ ∧ ρ * (r * Real.cos θ) + √(1 - ρ ^ 2) * (r * Real.sin θ) < 0)
      ↔ θ ∈ Set.Ioo (-(π / 2)) (Real.arccos ρ - π / 2) := by
  set α := Real.arccos ρ with hα
  have hα0 : 0 < α := Real.arccos_pos.2 hρ2
  have hαπ : α < π := Real.arccos_lt_pi.2 hρ1
  have hcos : Real.cos α = ρ := Real.cos_arccos hρ1.le hρ2.le
  have hsin : Real.sin α = √(1 - ρ ^ 2) := Real.sin_arccos ρ
  have hexp : ρ * (r * Real.cos θ) + √(1 - ρ ^ 2) * (r * Real.sin θ) = r * Real.cos (θ - α) := by
    rw [Real.cos_sub, hcos, hsin]; ring
  rw [hexp]
  have hpos : 0 < r * Real.cos θ ↔ θ ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    rw [mul_pos_iff_of_pos_left hr]
    constructor
    · intro h
      by_contra hn
      simp only [Set.mem_Ioo, not_and_or, not_lt] at hn
      rcases hn with h1 | h1
      · have : Real.cos θ ≤ 0 := by
          rw [← Real.cos_neg]
          exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [hθ.1])
        linarith
      · have : Real.cos θ ≤ 0 :=
          Real.cos_nonpos_of_pi_div_two_le_of_le h1 (by linarith [hθ.2])
        linarith
    · intro h; exact Real.cos_pos_of_mem_Ioo h
  rw [hpos, mul_neg_iff]
  simp only [Set.mem_Ioo]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rcases h3 with ⟨_, h3⟩ | ⟨h3, _⟩
    · refine ⟨h1, ?_⟩
      by_contra hn; push Not at hn
      have : 0 ≤ Real.cos (θ - α) := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      linarith
    · linarith
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, by linarith⟩, Or.inl ⟨hr, ?_⟩⟩
    rw [← Real.cos_neg]
    exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)

/-- **The Gaussian wedge.** -/
theorem wedge {ρ : ℝ} (hρ1 : -1 < ρ) (hρ2 : ρ < 1) :
    (γ.prod γ) {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + √(1 - ρ ^ 2) * z.2 < 0}
      = ENNReal.ofReal (Real.arccos ρ / (2 * π)) := by
  set W := {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + √(1 - ρ ^ 2) * z.2 < 0} with hW
  have hWm : MeasurableSet W := by
    apply MeasurableSet.inter
    · exact measurableSet_lt measurable_const measurable_fst
    · exact measurableSet_lt (f := fun z : ℝ × ℝ => ρ * z.1 + √(1 - ρ ^ 2) * z.2)
        (g := fun _ => (0 : ℝ)) (by fun_prop) measurable_const
  rw [γγ_eq, withDensity_apply _ hWm, ← lintegral_indicator hWm,
    ← lintegral_comp_polarCoord_symm]
  set α := Real.arccos ρ
  have hα0 : 0 < α := Real.arccos_pos.2 hρ2
  have hαπ : α < π := Real.arccos_lt_pi.2 hρ1
  -- the integrand on the target
  have hpt : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 •
      W.indicator (fun z => φ z.1 * φ z.2) (polarCoord.symm p)
      = ENNReal.ofReal (p.1 * ((2 * π)⁻¹ * Real.exp (-p.1 ^ 2 / 2))) *
          (Set.Ioo (-(π / 2)) (α - π / 2)).indicator 1 p.2 := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    simp only [Set.mem_Ioi] at hr
    simp only [smul_eq_mul, polarCoord, OpenPartialHomeomorph.coe_mk_symm, PartialEquiv.coe_symm_mk]
    by_cases hin : θ ∈ Set.Ioo (-(π / 2)) (α - π / 2)
    · have hmem : (r * Real.cos θ, r * Real.sin θ) ∈ W := (wedge_angle hρ1 hρ2 hr hθ).2 hin
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hin, Pi.one_apply, mul_one, φφ_polar,
        ← ENNReal.ofReal_mul hr.le]
    · have hmem : (r * Real.cos θ, r * Real.sin θ) ∉ W := fun h => hin ((wedge_angle hρ1 hρ2 hr hθ).1 h)
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hin, mul_zero, mul_zero]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hpt]
  have htarget : polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π := rfl
  rw [htarget, Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [lintegral_prod_mul (f := fun r => ENNReal.ofReal (r * ((2 * π)⁻¹ * Real.exp (-r ^ 2 / 2))))
    (g := (Set.Ioo (-(π / 2)) (α - π / 2)).indicator 1)
    ((ENNReal.measurable_ofReal.comp (by fun_prop)).aemeasurable)
    ((measurable_one.indicator measurableSet_Ioo).aemeasurable)]
  -- radial part
  have hrad : ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r * ((2 * π)⁻¹ * Real.exp (-r ^ 2 / 2)))
      = ENNReal.ofReal ((2 * π)⁻¹) := by
    have hint : IntegrableOn (fun r : ℝ => r * ((2 * π)⁻¹ * Real.exp (-r ^ 2 / 2))) (Set.Ioi 0) := by
      have := (integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).integrableOn (s := Set.Ioi 0)
      refine IntegrableOn.congr_fun (this.const_mul (2 * π)⁻¹) (fun r _ => ?_) measurableSet_Ioi
      ring_nf
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun r hr => by simp only [Pi.zero_apply]; have : (0 : ℝ) < r := hr; positivity))]
    · congr 1
      have hc := integral_mul_cexp_neg_mul_sq (b := (1 / 2 : ℂ)) (by norm_num)
      have : ∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r ^ 2 / 2) = 1 := by
        have h2 : (∫ r in Set.Ioi (0 : ℝ), ((r * Real.exp (-r ^ 2 / 2) : ℝ) : ℂ)) = 1 := by
          rw [show (2 * (1 / 2 : ℂ))⁻¹ = 1 by norm_num] at hc
          rw [← hc]
          refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
          push_cast; congr 2; ring
        rw [integral_complex_ofReal] at h2
        exact_mod_cast h2
      rw [show (fun r : ℝ => r * ((2 * π)⁻¹ * Real.exp (-r ^ 2 / 2)))
          = fun r => (2 * π)⁻¹ * (r * Real.exp (-r ^ 2 / 2)) by ext r; ring,
        integral_const_mul, this, mul_one]
  have hang : ∫⁻ θ in Set.Ioo (-π) π, (Set.Ioo (-(π / 2)) (α - π / 2)).indicator 1 θ
      = ENNReal.ofReal α := by
    rw [lintegral_indicator_one measurableSet_Ioo, Measure.restrict_apply measurableSet_Ioo,
      Set.inter_eq_left.mpr (Set.Ioo_subset_Ioo (by linarith [Real.pi_pos]) (by linarith)),
      Real.volume_Ioo]
    congr 1; ring
  rw [hrad, hang, ← ENNReal.ofReal_mul (by positivity)]
  congr 1; ring

lemma map_neg_γ : γ.map (fun x => -x) = γ := by
  rw [gaussianReal_map_neg, neg_zero]

/-- The opposite wedge. -/
theorem wedge' {ρ : ℝ} (hρ1 : -1 < ρ) (hρ2 : ρ < 1) :
    (γ.prod γ) {z : ℝ × ℝ | z.1 < 0 ∧ 0 < ρ * z.1 + √(1 - ρ ^ 2) * z.2}
      = ENNReal.ofReal (Real.arccos ρ / (2 * π)) := by
  have hW : MeasurableSet {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + √(1 - ρ ^ 2) * z.2 < 0} := by
    apply MeasurableSet.inter
    · exact measurableSet_lt measurable_const measurable_fst
    · exact measurableSet_lt (f := fun z : ℝ × ℝ => ρ * z.1 + √(1 - ρ ^ 2) * z.2)
        (g := fun _ => (0 : ℝ)) (by fun_prop) measurable_const
  have hm : Measurable (Prod.map (fun x : ℝ => -x) (fun x : ℝ => -x)) := by fun_prop
  have hmap : (γ.prod γ).map (Prod.map (fun x : ℝ => -x) (fun x : ℝ => -x)) = γ.prod γ := by
    rw [← Measure.map_prod_map γ γ (by fun_prop) (by fun_prop), map_neg_γ]
  rw [← wedge hρ1 hρ2, ← hmap, Measure.map_apply hm hW]
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Prod.map_fst, Prod.map_snd]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- The law of `ρ z₁ + σ z₂`. -/
theorem law_Y (ρ σ : ℝ) (h : ρ ^ 2 + σ ^ 2 = 1) :
    (γ.prod γ).map (fun z : ℝ × ℝ => ρ * z.1 + σ * z.2) = γ := by
  have e : (fun z : ℝ × ℝ => ρ * z.1 + σ * z.2)
      = (fun p : ℝ × ℝ => p.1 + p.2) ∘ Prod.map (fun x : ℝ => ρ * x) (fun x : ℝ => σ * x) := by
    ext z; rfl
  rw [e, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map γ γ (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_mul]
  change Measure.conv _ _ = _
  rw [gaussianReal_conv_gaussianReal]
  congr 1
  · simp
  · ext; simp [h]

lemma φ_le (x : ℝ) : φ x ≤ ENNReal.ofReal ((√(2 * π))⁻¹) := by
  rw [φ_apply]
  apply ENNReal.ofReal_le_ofReal
  have : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
  have h0 : 0 ≤ (√(2 * π))⁻¹ := by positivity
  nlinarith

/-- Gaussian strips. -/
theorem gauss_strip (a b : ℝ) (hab : a ≤ b) : γ.real (Set.Icc a b) ≤ (b - a) / √(2 * π) := by
  have h1 : γ (Set.Icc a b) ≤ ENNReal.ofReal ((√(2 * π))⁻¹) * ENNReal.ofReal (b - a) := by
    rw [γ_eq, withDensity_apply _ measurableSet_Icc]
    calc ∫⁻ x in Set.Icc a b, φ x ≤ ∫⁻ _x in Set.Icc a b, ENNReal.ofReal ((√(2 * π))⁻¹) :=
          lintegral_mono (fun x => φ_le x)
      _ = _ := by rw [setLIntegral_const, Real.volume_Icc]
  rw [← ENNReal.ofReal_mul (by positivity)] at h1
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  have hba : 0 ≤ (√(2 * π))⁻¹ * (b - a) := mul_nonneg (by positivity) (by linarith)
  rw [ENNReal.toReal_ofReal hba] at this
  rw [measureReal_def]
  calc _ ≤ (√(2 * π))⁻¹ * (b - a) := this
    _ = _ := by ring

/-- Gaussian tails. -/
theorem gauss_tail {R : ℝ} (hR : 0 < R) : γ.real {x | R ≤ |x|} ≤ 1 / R ^ 2 := by
  have h := meas_ge_le_variance_div_sq (μ := γ) (X := id) (memLp_id_gaussianReal 2) hR
  have e1 : ∫ x, id x ∂γ = 0 := integral_id_gaussianReal
  have e2 : Var[id; γ] = 1 := by rw [variance_id_gaussianReal]; simp
  rw [e1, e2] at h
  simp only [id, sub_zero] at h
  rw [measureReal_def]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal (by positivity)] at this

lemma wedge_real {ρ : ℝ} (hρ1 : -1 < ρ) (hρ2 : ρ < 1) :
    (γ.prod γ).real {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + √(1 - ρ ^ 2) * z.2 < 0}
      = Real.arccos ρ / (2 * π) := by
  rw [measureReal_def, wedge hρ1 hρ2, ENNReal.toReal_ofReal]
  have := Real.arccos_nonneg ρ; positivity

lemma wedge'_real {ρ : ℝ} (hρ1 : -1 < ρ) (hρ2 : ρ < 1) :
    (γ.prod γ).real {z : ℝ × ℝ | z.1 < 0 ∧ 0 < ρ * z.1 + √(1 - ρ ^ 2) * z.2}
      = Real.arccos ρ / (2 * π) := by
  rw [measureReal_def, wedge' hρ1 hρ2, ENNReal.toReal_ofReal]
  have := Real.arccos_nonneg ρ; positivity

/-- Strips for the second coordinate. -/
theorem strip_Y (ρ σ : ℝ) (h : ρ ^ 2 + σ ^ 2 = 1) (a b : ℝ) (hab : a ≤ b) :
    (γ.prod γ).real {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc a b} ≤ (b - a) / √(2 * π) := by
  have hm : Measurable (fun z : ℝ × ℝ => ρ * z.1 + σ * z.2) := by fun_prop
  have := map_measureReal_apply hm (μ := γ.prod γ) measurableSet_Icc (s := Set.Icc a b)
  rw [law_Y ρ σ h] at this
  rw [show {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc a b}
      = (fun z : ℝ × ℝ => ρ * z.1 + σ * z.2) ⁻¹' Set.Icc a b from rfl, ← this]
  exact gauss_strip a b hab

theorem strip_X (a b : ℝ) (hab : a ≤ b) :
    (γ.prod γ).real {z : ℝ × ℝ | z.1 ∈ Set.Icc a b} ≤ (b - a) / √(2 * π) := by
  have := strip_Y 1 0 (by norm_num) a b hab
  simpa using this

theorem tail_Y (ρ σ : ℝ) (h : ρ ^ 2 + σ ^ 2 = 1) {R : ℝ} (hR : 0 < R) :
    (γ.prod γ).real {z : ℝ × ℝ | R ≤ |ρ * z.1 + σ * z.2|} ≤ 1 / R ^ 2 := by
  have hm : Measurable (fun z : ℝ × ℝ => ρ * z.1 + σ * z.2) := by fun_prop
  have hs : MeasurableSet {x : ℝ | R ≤ |x|} := measurableSet_le measurable_const (by fun_prop)
  have := map_measureReal_apply hm (μ := γ.prod γ) hs
  rw [law_Y ρ σ h] at this
  rw [show {z : ℝ × ℝ | R ≤ |ρ * z.1 + σ * z.2|}
      = (fun z : ℝ × ℝ => ρ * z.1 + σ * z.2) ⁻¹' {x | R ≤ |x|} from rfl, ← this]
  exact gauss_tail hR

theorem tail_X {R : ℝ} (hR : 0 < R) : (γ.prod γ).real {z : ℝ × ℝ | R ≤ |z.1|} ≤ 1 / R ^ 2 := by
  have := tail_Y 1 0 (by norm_num) hR
  simpa using this

end R522

end S_RR4

-- ===== RR5 =====

/-!
# Erdős 522 (real roots), part 5: quadrant probabilities for signed sums

`quad_up`: `P(∑ εa > 0, ∑ εb < 0) ≤ arccos ρ/(2π) + 2w/√(2π) + 2/R² + C·(∑a⁴ + ∑b⁴)`.
`quad_low`: `P(∑ εa > τ, ∑ εb < -τ) ≥ arccos ρ/(2π) - 2(τ+2w)/√(2π) - 2/R² - C·(∑a⁴ + ∑b⁴)`.
The constants only depend on `(τ, R, w)`.
-/

open Finset Real MeasureTheory FourierTransform ProbabilityTheory

noncomputable section S_RR5

namespace R522

/-- A bump: `1` on `[p, q]`, `0` outside `(p - w, q + w)`. -/
def bb (p q w : ℝ) (hpq : p < q) (hw : 0 < w) : ContDiffBump ((p + q) / 2) :=
  ⟨(q - p) / 2, (q - p) / 2 + w, by linarith, by linarith⟩

lemma bb_one {p q w : ℝ} (hpq : p < q) (hw : 0 < w) {x : ℝ} (hx : x ∈ Set.Icc p q) :
    bb p q w hpq hw x = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [Real.closedBall_eq_Icc]
  simp only [bb, Set.mem_Icc] at hx ⊢
  constructor <;> linarith [hx.1, hx.2]

lemma bb_zero {p q w : ℝ} (hpq : p < q) (hw : 0 < w) {x : ℝ} (hx : x ∉ Set.Ioo (p - w) (q + w)) :
    bb p q w hpq hw x = 0 := by
  apply ContDiffBump.zero_of_le_dist
  simp only [bb, Set.mem_Ioo, not_and_or, not_lt] at hx ⊢
  rw [Real.dist_eq]
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

lemma bb_nonneg (p q w : ℝ) (hpq : p < q) (hw : 0 < w) (x : ℝ) : 0 ≤ bb p q w hpq hw x :=
  ContDiffBump.nonneg _

lemma bb_le_one (p q w : ℝ) (hpq : p < q) (hw : 0 < w) (x : ℝ) : bb p q w hpq hw x ≤ 1 :=
  ContDiffBump.le_one _

/-- The bump as a Schwartz function. -/
def Sb (p q w : ℝ) (hpq : p < q) (hw : 0 < w) : SchwartzMap ℝ ℂ :=
  (((bb p q w hpq hw).hasCompactSupport).comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (bb p q w hpq hw).contDiff)

lemma Sb_apply (p q w : ℝ) (hpq : p < q) (hw : 0 < w) (x : ℝ) :
    Sb p q w hpq hw x = ((bb p q w hpq hw x : ℝ) : ℂ) := rfl

/-- The CLT for bumps, in real form. -/
theorem clt_bb {ι : Type*} [Fintype ι] [DecidableEq ι] {p₁ q₁ w₁ p₂ q₂ w₂ : ℝ}
    (h₁ : p₁ < q₁) (k₁ : 0 < w₁) (h₂ : p₂ < q₂) (k₂ : 0 < w₂)
    (a b : ι → ℝ) (ρ : ℝ) (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hab : ∑ i, a i * b i = ρ) :
    |EE (fun ε => bb p₁ q₁ w₁ h₁ k₁ (ssum ε a) * bb p₂ q₂ w₂ h₂ k₂ (ssum ε b))
      - ∫ z, bb p₁ q₁ w₁ h₁ k₁ z.1 * bb p₂ q₂ w₂ h₂ k₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2) ∂(γ.prod γ)|
      ≤ 16 * (2 * π) ^ 4 * (Mom 4 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 0 (Sb p₂ q₂ w₂ h₂ k₂) * ∑ i, a i ^ 4
          + Mom 0 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 4 (Sb p₂ q₂ w₂ h₂ k₂) * ∑ i, b i ^ 4) := by
  have hρ := abs_rho_le a b ρ ha hb hab
  have h := clt_two (Sb p₁ q₁ w₁ h₁ k₁) (Sb p₂ q₂ w₂ h₂ k₂) a b ρ ha hb hab
  have hσ : √(1 - ρ ^ 2) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by linarith)
  have hG := gauss_two (Sb p₁ q₁ w₁ h₁ k₁) (Sb p₂ q₂ w₂ h₂ k₂) ρ (√(1 - ρ ^ 2))
  have hk : ∀ u v : ℝ, Complex.exp (-(2 * π ^ 2 * ((u + ρ * v) ^ 2 + √(1 - ρ ^ 2) ^ 2 * v ^ 2) : ℝ))
      = (gk ρ u v : ℂ) := by
    intro u v; unfold gk; rw [hσ, Complex.ofReal_exp]; congr 1; push_cast; ring
  simp_rw [hk] at hG
  rw [← hG] at h
  simp only [Sb_apply] at h
  have e1 : (∑ ε : ι → ℤˣ, ((bb p₁ q₁ w₁ h₁ k₁ (ssum ε a) : ℝ) : ℂ) *
      ((bb p₂ q₂ w₂ h₂ k₂ (ssum ε b) : ℝ) : ℂ)) / 2 ^ Fintype.card ι
      = ((EE (fun ε => bb p₁ q₁ w₁ h₁ k₁ (ssum ε a) * bb p₂ q₂ w₂ h₂ k₂ (ssum ε b)) : ℝ) : ℂ) := by
    unfold EE; push_cast; rfl
  have e2 : ∫ z, ((bb p₁ q₁ w₁ h₁ k₁ z.1 : ℝ) : ℂ) *
      ((bb p₂ q₂ w₂ h₂ k₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2) : ℝ) : ℂ) ∂(γ.prod γ)
      = ((∫ z, bb p₁ q₁ w₁ h₁ k₁ z.1 * bb p₂ q₂ w₂ h₂ k₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2)
          ∂(γ.prod γ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; push_cast; rfl
  rw [e1, e2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- Integrals of `[0, 1]`-valued functions vs. measures of sets. -/
lemma integral_le_of_supp {f : ℝ × ℝ → ℝ} (hf : Continuous f) (h0 : ∀ z, 0 ≤ f z)
    (h1 : ∀ z, f z ≤ 1) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (hfA : ∀ z, z ∉ A → f z = 0) :
    ∫ z, f z ∂(γ.prod γ) ≤ (γ.prod γ).real A := by
  rw [← integral_indicator_one hA]
  refine integral_mono (Integrable.mono' (integrable_const (1 : ℝ)) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 z)]; exact h1 z)))
    ((integrable_const (1 : ℝ)).indicator hA) (fun z => ?_)
  by_cases hz : z ∈ A
  · rw [Set.indicator_of_mem hz]; exact h1 z
  · rw [Set.indicator_of_notMem hz, hfA z hz]

lemma integral_ge_of_one {f : ℝ × ℝ → ℝ} (hf : Continuous f) (h0 : ∀ z, 0 ≤ f z)
    (h1 : ∀ z, f z ≤ 1) {B : Set (ℝ × ℝ)} (hB : MeasurableSet B) (hfB : ∀ z, z ∈ B → f z = 1) :
    (γ.prod γ).real B ≤ ∫ z, f z ∂(γ.prod γ) := by
  rw [← integral_indicator_one hB]
  refine integral_mono ((integrable_const (1 : ℝ)).indicator hB)
    (Integrable.mono' (integrable_const (1 : ℝ)) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 z)]; exact h1 z)))
    (fun z => ?_)
  by_cases hz : z ∈ B
  · rw [Set.indicator_of_mem hz, hfB z hz]; rfl
  · rw [Set.indicator_of_notMem hz]; exact h0 z

/-- The constant of the quadrant bounds. -/
def Cq (p₁ q₁ w₁ p₂ q₂ w₂ : ℝ) (h₁ : p₁ < q₁) (k₁ : 0 < w₁) (h₂ : p₂ < q₂) (k₂ : 0 < w₂) : ℝ :=
  16 * (2 * π) ^ 4 * (Mom 4 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 0 (Sb p₂ q₂ w₂ h₂ k₂)
    + Mom 0 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 4 (Sb p₂ q₂ w₂ h₂ k₂))

lemma clt_bb' {ι : Type*} [Fintype ι] [DecidableEq ι] {p₁ q₁ w₁ p₂ q₂ w₂ : ℝ}
    (h₁ : p₁ < q₁) (k₁ : 0 < w₁) (h₂ : p₂ < q₂) (k₂ : 0 < w₂)
    (a b : ι → ℝ) (ρ : ℝ) (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hab : ∑ i, a i * b i = ρ) :
    |EE (fun ε => bb p₁ q₁ w₁ h₁ k₁ (ssum ε a) * bb p₂ q₂ w₂ h₂ k₂ (ssum ε b))
      - ∫ z, bb p₁ q₁ w₁ h₁ k₁ z.1 * bb p₂ q₂ w₂ h₂ k₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2) ∂(γ.prod γ)|
      ≤ Cq p₁ q₁ w₁ p₂ q₂ w₂ h₁ k₁ h₂ k₂ * (∑ i, a i ^ 4 + ∑ i, b i ^ 4) := by
  refine (clt_bb h₁ k₁ h₂ k₂ a b ρ ha hb hab).trans ?_
  unfold Cq
  have m1 := mom_nonneg 4 (Sb p₁ q₁ w₁ h₁ k₁)
  have m2 := mom_nonneg 0 (Sb p₂ q₂ w₂ h₂ k₂)
  have m3 := mom_nonneg 0 (Sb p₁ q₁ w₁ h₁ k₁)
  have m4 := mom_nonneg 4 (Sb p₂ q₂ w₂ h₂ k₂)
  have hA : 0 ≤ ∑ i, a i ^ 4 := Finset.sum_nonneg (fun i _ => by positivity)
  have hB : 0 ≤ ∑ i, b i ^ 4 := Finset.sum_nonneg (fun i _ => by positivity)
  have hc : (0 : ℝ) ≤ 16 * (2 * π) ^ 4 := by positivity
  have key : Mom 4 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 0 (Sb p₂ q₂ w₂ h₂ k₂) * ∑ i, a i ^ 4
      + Mom 0 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 4 (Sb p₂ q₂ w₂ h₂ k₂) * ∑ i, b i ^ 4
      ≤ (Mom 4 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 0 (Sb p₂ q₂ w₂ h₂ k₂)
        + Mom 0 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 4 (Sb p₂ q₂ w₂ h₂ k₂)) * (∑ i, a i ^ 4 + ∑ i, b i ^ 4) := by
    nlinarith [mul_nonneg (mul_nonneg m1 m2) hB, mul_nonneg (mul_nonneg m3 m4) hA]
  calc _ ≤ 16 * (2 * π) ^ 4 * ((Mom 4 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 0 (Sb p₂ q₂ w₂ h₂ k₂)
        + Mom 0 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 4 (Sb p₂ q₂ w₂ h₂ k₂)) * (∑ i, a i ^ 4 + ∑ i, b i ^ 4)) :=
        mul_le_mul_of_nonneg_left key hc
    _ = _ := by ring

/-- **Upper quadrant bound.** -/
theorem quad_up {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℝ) (ρ : ℝ)
    (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1) (hab : ∑ i, a i * b i = ρ)
    (hρ1 : -1 < ρ) (hρ2 : ρ < 1) {R w : ℝ} (hR : 0 < R) (hw : 0 < w) :
    PP (fun ε => 0 < ssum ε a ∧ ssum ε b < 0)
      ≤ Real.arccos ρ / (2 * π) + 2 * w / √(2 * π) + 2 / R ^ 2
        + Cq 0 R w (-R) 0 w hR hw (by linarith) hw * (∑ i, a i ^ 4 + ∑ i, b i ^ 4) := by
  classical
  have hR' : -R < 0 := by linarith
  have hclt := clt_bb' hR hw hR' hw a b ρ ha hb hab
  set f₁ := bb 0 R w hR hw
  set f₂ := bb (-R) 0 w hR' hw
  set σ := √(1 - ρ ^ 2) with hσdef
  have hσ : ρ ^ 2 + σ ^ 2 = 1 := by rw [hσdef, Real.sq_sqrt (by nlinarith)]; ring
  -- pointwise
  have hpt : ∀ ε : ι → ℤˣ, (if 0 < ssum ε a ∧ ssum ε b < 0 then (1 : ℝ) else 0)
      ≤ f₁ (ssum ε a) * f₂ (ssum ε b) + (if R ≤ |ssum ε a| then 1 else 0)
        + (if R ≤ |ssum ε b| then 1 else 0) := by
    intro ε
    have n1 := bb_nonneg 0 R w hR hw (ssum ε a)
    have n2 := bb_nonneg (-R) 0 w (by linarith) hw (ssum ε b)
    split_ifs with h hA hB hB <;> try nlinarith
    push Not at hA hB
    rw [abs_lt] at hA hB
    rw [bb_one hR hw ⟨h.1.le, by linarith⟩, bb_one (by linarith) hw ⟨by linarith, h.2.le⟩]
    norm_num
  have hP : PP (fun ε => 0 < ssum ε a ∧ ssum ε b < 0)
      ≤ EE (fun ε => f₁ (ssum ε a) * f₂ (ssum ε b)) + PP (fun ε => R ≤ |ssum ε a|)
        + PP (fun ε => R ≤ |ssum ε b|) := by
    rw [PP_eq, PP_eq, PP_eq, ← EE_add, ← EE_add]
    exact EE_mono hpt
  have t1 := cheb_ssum a hR
  have t2 := cheb_ssum b hR
  rw [ha] at t1; rw [hb] at t2
  -- the Gaussian integral
  have hint : ∫ z, f₁ z.1 * f₂ (ρ * z.1 + σ * z.2) ∂(γ.prod γ)
      ≤ Real.arccos ρ / (2 * π) + 2 * w / √(2 * π) := by
    set A := {z : ℝ × ℝ | z.1 ∈ Set.Ioo (0 - w) (R + w) ∧ ρ * z.1 + σ * z.2 ∈ Set.Ioo (-R - w) (0 + w)}
    have hA : MeasurableSet A := by
      apply MeasurableSet.inter
      · exact measurableSet_Ioo.preimage measurable_fst
      · exact measurableSet_Ioo.preimage (by fun_prop)
    have h1 := integral_le_of_supp (f := fun z : ℝ × ℝ => f₁ z.1 * f₂ (ρ * z.1 + σ * z.2))
      ((f₁.continuous.comp continuous_fst).mul (f₂.continuous.comp (by fun_prop))) (fun z => mul_nonneg (bb_nonneg _ _ _ _ _ _) (bb_nonneg _ _ _ _ _ _))
      (fun z => mul_le_one₀ (bb_le_one _ _ _ _ _ _) (bb_nonneg _ _ _ _ _ _) (bb_le_one _ _ _ _ _ _))
      hA (fun z hz => by
        simp only [A, Set.mem_ofPred_eq, not_and_or] at hz
        rcases hz with hz | hz
        · rw [bb_zero hR hw hz, zero_mul]
        · rw [bb_zero (by linarith) hw hz, mul_zero])
    refine h1.trans ?_
    have hsub : A ⊆ {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + σ * z.2 < 0} ∪
        {z : ℝ × ℝ | z.1 ∈ Set.Icc (-w) 0} ∪ {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc 0 w} := by
      intro z hz
      simp only [A, Set.mem_ofPred_eq, Set.mem_Ioo] at hz
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_Icc]
      by_cases h1 : 0 < z.1
      · by_cases h2 : ρ * z.1 + σ * z.2 < 0
        · exact Or.inl (Or.inl ⟨h1, h2⟩)
        · exact Or.inr ⟨by linarith, by linarith⟩
      · exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
    calc (γ.prod γ).real A
        ≤ (γ.prod γ).real ({z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + σ * z.2 < 0} ∪
            {z : ℝ × ℝ | z.1 ∈ Set.Icc (-w) 0} ∪ {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc 0 w}) :=
          measureReal_mono hsub
      _ ≤ (γ.prod γ).real {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + σ * z.2 < 0}
          + (γ.prod γ).real {z : ℝ × ℝ | z.1 ∈ Set.Icc (-w) 0}
          + (γ.prod γ).real {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc 0 w} := by
          refine (measureReal_union_le _ _).trans ?_
          gcongr
          exact measureReal_union_le _ _
      _ ≤ Real.arccos ρ / (2 * π) + (0 - -w) / √(2 * π) + (w - 0) / √(2 * π) := by
          gcongr
          · rw [hσdef, wedge_real hρ1 hρ2]
          · exact strip_X (-w) 0 (by linarith)
          · exact strip_Y ρ σ hσ 0 w hw.le
      _ = _ := by ring
  have hc := (abs_le.mp hclt).2
  have final : PP (fun ε => 0 < ssum ε a ∧ ssum ε b < 0)
      ≤ Real.arccos ρ / (2 * π) + 2 * w / √(2 * π) + 2 / R ^ 2
        + Cq 0 R w (-R) 0 w hR hw hR' hw * (∑ i, a i ^ 4 + ∑ i, b i ^ 4) := by
    have e : (2 : ℝ) / R ^ 2 = 1 / R ^ 2 + 1 / R ^ 2 := by ring
    linarith
  exact final

/-- **Lower quadrant bound (with margin `τ`).** -/
theorem quad_low {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℝ) (ρ : ℝ)
    (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1) (hab : ∑ i, a i * b i = ρ)
    (hρ1 : -1 < ρ) (hρ2 : ρ < 1) {τ R w : ℝ} (hτ : 0 ≤ τ) (hw : 0 < w) (hR : τ + 2 * w < R) :
    Real.arccos ρ / (2 * π) - 2 * (τ + 2 * w) / √(2 * π) - 2 / R ^ 2
        - Cq (τ + 2 * w) R w (-R) (-τ - 2 * w) w hR hw (by linarith) hw
          * (∑ i, a i ^ 4 + ∑ i, b i ^ 4)
      ≤ PP (fun ε => τ < ssum ε a ∧ ssum ε b < -τ) := by
  classical
  have hR0 : 0 < R := by linarith
  have hR' : -R < -τ - 2 * w := by linarith
  have hclt := clt_bb' hR hw hR' hw a b ρ ha hb hab
  set f₁ := bb (τ + 2 * w) R w hR hw
  set f₂ := bb (-R) (-τ - 2 * w) w hR' hw
  set σ := √(1 - ρ ^ 2) with hσdef
  have hσ : ρ ^ 2 + σ ^ 2 = 1 := by rw [hσdef, Real.sq_sqrt (by nlinarith)]; ring
  have hpt : ∀ ε : ι → ℤˣ, f₁ (ssum ε a) * f₂ (ssum ε b)
      ≤ if τ < ssum ε a ∧ ssum ε b < -τ then (1 : ℝ) else 0 := by
    intro ε
    split_ifs with h
    · exact mul_le_one₀ (bb_le_one _ _ _ _ _ _) (bb_nonneg _ _ _ _ _ _) (bb_le_one _ _ _ _ _ _)
    · rw [not_and_or, not_lt, not_lt] at h
      rcases h with h | h
      · rw [bb_zero (p := τ + 2 * w) (q := R) (x := ssum ε a) hR hw
          (by simp only [Set.mem_Ioo, not_and_or, not_lt]; left; linarith), zero_mul]
      · rw [bb_zero (p := -R) (q := -τ - 2 * w) (x := ssum ε b) (by linarith) hw
          (by simp only [Set.mem_Ioo, not_and_or, not_lt]; right; linarith), mul_zero]
  have hP : EE (fun ε => f₁ (ssum ε a) * f₂ (ssum ε b))
      ≤ PP (fun ε => τ < ssum ε a ∧ ssum ε b < -τ) := by rw [PP_eq]; exact EE_mono hpt
  have hint : Real.arccos ρ / (2 * π) - 2 * (τ + 2 * w) / √(2 * π) - 2 / R ^ 2
      ≤ ∫ z, f₁ z.1 * f₂ (ρ * z.1 + σ * z.2) ∂(γ.prod γ) := by
    set B := {z : ℝ × ℝ | z.1 ∈ Set.Icc (τ + 2 * w) R ∧ ρ * z.1 + σ * z.2 ∈ Set.Icc (-R) (-τ - 2 * w)}
    have hB : MeasurableSet B := by
      apply MeasurableSet.inter
      · exact measurableSet_Icc.preimage measurable_fst
      · exact measurableSet_Icc.preimage (by fun_prop)
    have h1 := integral_ge_of_one (f := fun z : ℝ × ℝ => f₁ z.1 * f₂ (ρ * z.1 + σ * z.2))
      ((f₁.continuous.comp continuous_fst).mul (f₂.continuous.comp (by fun_prop))) (fun z => mul_nonneg (bb_nonneg _ _ _ _ _ _) (bb_nonneg _ _ _ _ _ _))
      (fun z => mul_le_one₀ (bb_le_one _ _ _ _ _ _) (bb_nonneg _ _ _ _ _ _) (bb_le_one _ _ _ _ _ _))
      hB (fun z hz => by
        simp only [B, Set.mem_ofPred_eq] at hz
        simp only [f₁, f₂]
        rw [bb_one hR hw hz.1, bb_one (by linarith) hw hz.2, mul_one])
    refine le_trans ?_ h1
    have hsub : {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + σ * z.2 < 0} ⊆ B ∪
        {z : ℝ × ℝ | z.1 ∈ Set.Icc 0 (τ + 2 * w)} ∪
        {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc (-τ - 2 * w) 0} ∪ {z : ℝ × ℝ | R ≤ |z.1|} ∪
        {z : ℝ × ℝ | R ≤ |ρ * z.1 + σ * z.2|} := by
      intro z ⟨h1, h2⟩
      simp only [B, Set.mem_union, Set.mem_ofPred_eq, Set.mem_Icc]
      by_cases c1 : z.1 ≤ τ + 2 * w
      · left; left; left; right; exact ⟨h1.le, c1⟩
      by_cases c2 : -τ - 2 * w ≤ ρ * z.1 + σ * z.2
      · left; left; right; exact ⟨c2, h2.le⟩
      by_cases c3 : R ≤ |z.1|
      · left; right; exact c3
      by_cases c4 : R ≤ |ρ * z.1 + σ * z.2|
      · right; exact c4
      left; left; left; left
      push Not at c1 c2 c3 c4
      rw [abs_lt] at c3 c4
      exact ⟨⟨c1.le, c3.2.le⟩, ⟨c4.1.le, c2.le⟩⟩
    have hW := wedge_real hρ1 hρ2
    rw [← hσdef] at hW
    have s1 := strip_X 0 (τ + 2 * w) (by linarith)
    have s2 := strip_Y ρ σ hσ (-τ - 2 * w) 0 (by linarith)
    have t1 := tail_X hR0
    have t2 := tail_Y ρ σ hσ hR0
    have hmono := measureReal_mono (μ := γ.prod γ) hsub
    have u1 := measureReal_union_le (μ := γ.prod γ) (B ∪ {z : ℝ × ℝ | z.1 ∈ Set.Icc 0 (τ + 2 * w)} ∪
        {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc (-τ - 2 * w) 0} ∪ {z : ℝ × ℝ | R ≤ |z.1|})
        {z : ℝ × ℝ | R ≤ |ρ * z.1 + σ * z.2|}
    have u2 := measureReal_union_le (μ := γ.prod γ) (B ∪ {z : ℝ × ℝ | z.1 ∈ Set.Icc 0 (τ + 2 * w)} ∪
        {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc (-τ - 2 * w) 0}) {z : ℝ × ℝ | R ≤ |z.1|}
    have u3 := measureReal_union_le (μ := γ.prod γ) (B ∪ {z : ℝ × ℝ | z.1 ∈ Set.Icc 0 (τ + 2 * w)})
        {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc (-τ - 2 * w) 0}
    have u4 := measureReal_union_le (μ := γ.prod γ) B {z : ℝ × ℝ | z.1 ∈ Set.Icc 0 (τ + 2 * w)}
    have e1 : (τ + 2 * w - 0) / √(2 * π) + (0 - (-τ - 2 * w)) / √(2 * π)
        = 2 * (τ + 2 * w) / √(2 * π) := by ring
    have e2 : 1 / R ^ 2 + 1 / R ^ 2 = 2 / R ^ 2 := by ring
    linarith
  have hc := (abs_le.mp hclt).1
  have final : Real.arccos ρ / (2 * π) - 2 * (τ + 2 * w) / √(2 * π) - 2 / R ^ 2
        - Cq (τ + 2 * w) R w (-R) (-τ - 2 * w) w hR hw hR' hw * (∑ i, a i ^ 4 + ∑ i, b i ^ 4)
      ≤ PP (fun ε => τ < ssum ε a ∧ ssum ε b < -τ) := by linarith
  exact final

end R522

end S_RR5

-- ===== RR6 =====

/-!
# Erdős 522 (real roots), part 6: many roots in a short window are unlikely

For a window `[c, c + h]`, `k` roots there give (Hermite) `|P(c)| ≤ h^k |Hₖ P (ξ)|` for some `ξ`
in the window (`Hₖ` the Hasse derivative), and Taylor expansion at `c` bounds `|Hₖ P|` on the
window by a random variable `Zₖ` with an explicit second moment. With the Littlewood–Offord bound
for `P(c)` this gives `P(N ≥ k) ≤ 1/A² + (2 A hᵏ M + 2)/√#I`.
-/

open Finset Real Polynomial

noncomputable section S_RR6

namespace R522

variable {n : ℕ}

/-- Hasse derivative values are signed sums. -/
lemma hasse_eval (ε : Fin (n + 1) → ℤˣ) (l : ℕ) (c : ℝ) :
    (hasseDeriv l (poly ε)).eval c = ssum ε (fun i => ((i : ℕ).choose l : ℝ) * c ^ ((i : ℕ) - l)) := by
  unfold poly ssum
  rw [map_sum, eval_finsetSum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [C_mul_X_pow_eq_monomial, hasseDeriv_monomial, eval_monomial]
  ring

lemma natDegree_poly_le (ε : Fin (n + 1) → ℤˣ) : (poly ε).natDegree ≤ n := by
  unfold poly
  refine natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  exact Nat.lt_succ_iff.mp i.2

/-- Taylor expansion of a Hasse derivative. -/
lemma hasse_taylor (ε : Fin (n + 1) → ℤˣ) (k : ℕ) (c t : ℝ) :
    (hasseDeriv k (poly ε)).eval (c + t)
      = ∑ i ∈ range (n + 1), ((k + i).choose i : ℝ) * (hasseDeriv (k + i) (poly ε)).eval c * t ^ i := by
  set q := hasseDeriv k (poly ε)
  have hq : q.natDegree < n + 1 := by
    have := natDegree_hasseDeriv_le (poly ε) k
    have := natDegree_poly_le ε
    simp only [q]; omega
  have e1 : q.eval (c + t) = (taylor c q).eval t := by rw [taylor_eval, add_comm]
  rw [e1, eval_eq_sum_range' (by rw [natDegree_taylor]; exact hq)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [taylor_coeff]
  have : hasseDeriv i q = ((i + k).choose i) • hasseDeriv (i + k) (poly ε) := by
    have := congrArg (fun F => F (poly ε)) (hasseDeriv_comp (R := ℝ) i k)
    simpa using this
  rw [this, eval_smul, nsmul_eq_mul, add_comm i k]

/-- The Taylor majorant of `|Hₖ P|` on `[c, c + h]`. -/
def Zk (ε : Fin (n + 1) → ℤˣ) (k : ℕ) (c h : ℝ) : ℝ :=
  ∑ i ∈ range (n + 1), ((k + i).choose i : ℝ) * h ^ i * |(hasseDeriv (k + i) (poly ε)).eval c|

lemma hasse_le_Zk (ε : Fin (n + 1) → ℤˣ) (k : ℕ) {c h ξ : ℝ} (hh : 0 ≤ h)
    (hξ : ξ ∈ Set.Icc c (c + h)) : |(hasseDeriv k (poly ε)).eval ξ| ≤ Zk ε k c h := by
  have ht0 : 0 ≤ ξ - c := by linarith [hξ.1]
  have hth : ξ - c ≤ h := by linarith [hξ.2]
  rw [show ξ = c + (ξ - c) by ring, hasse_taylor]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k + i).choose i : ℝ)),
    abs_of_nonneg (pow_nonneg ht0 i)]
  have : (ξ - c) ^ i ≤ h ^ i := pow_le_pow_left₀ ht0 hth i
  calc ((k + i).choose i : ℝ) * |(hasseDeriv (k + i) (poly ε)).eval c| * (ξ - c) ^ i
      ≤ ((k + i).choose i : ℝ) * |(hasseDeriv (k + i) (poly ε)).eval c| * h ^ i := by gcongr
    _ = _ := by ring

/-- Second moment of `Zₖ`. -/
lemma EE_Zk_sq (k : ℕ) (c h : ℝ) (hh : 0 ≤ h) (μ : ℕ → ℝ) (hμ : ∀ l, 0 < μ l)
    (hD : ∀ l, ∑ i : Fin (n + 1), (((i : ℕ).choose l : ℝ) * c ^ ((i : ℕ) - l)) ^ 2 ≤ μ l ^ 2) :
    EE (fun ε : Fin (n + 1) → ℤˣ => Zk ε k c h ^ 2)
      ≤ (∑ i ∈ range (n + 1), ((k + i).choose i : ℝ) * h ^ i * μ (k + i)) ^ 2 := by
  unfold Zk
  refine EE_wsum_sq (range (n + 1)) (fun i => ((k + i).choose i : ℝ) * h ^ i) (fun i => μ (k + i))
    (fun i ε => (hasseDeriv (k + i) (poly ε)).eval c) (fun i _ => by positivity)
    (fun i _ => hμ _) (fun i _ => ?_)
  simp_rw [hasse_eval]
  rw [EE_ssum_sq]
  exact hD _

/-- Partial negative binomial sums. -/
lemma negbin_le (k N : ℕ) {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    ∑ i ∈ range N, ((i + k).choose k : ℝ) * r ^ i ≤ 1 / (1 - r) ^ (k + 1) := by
  have hs := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) k
    (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  exact sum_le_hasSum _ (fun i _ => by positivity) hs

lemma choose_sq_le (i l : ℕ) : ((i.choose l : ℝ)) ^ 2 ≤ ((2 * i).choose (2 * l) : ℝ) := by
  have h := Nat.add_choose_eq i i (2 * l)
  rw [← two_mul] at h
  have : i.choose l * i.choose l ≤ (2 * i).choose (2 * l) := by
    rw [h]
    have hmem : ((l, l) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (2 * l) :=
      Finset.HasAntidiagonal.mem_antidiagonal.mpr (show l + l = 2 * l by ring)
    exact Finset.single_le_sum (f := fun p : ℕ × ℕ => i.choose p.1 * i.choose p.2)
      (fun _ _ => Nat.zero_le _) hmem
  rw [sq]; exact_mod_cast this

/-- Second moments of Hasse derivatives inside the unit disc. -/
lemma hasse_moment_le (l : ℕ) {c : ℝ} (h0 : 0 ≤ c) (h1 : c < 1) :
    ∑ i : Fin (n + 1), (((i : ℕ).choose l : ℝ) * c ^ ((i : ℕ) - l)) ^ 2 ≤ 1 / (1 - c) ^ (2 * l + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ((i.choose l : ℝ) * c ^ (i - l)) ^ 2)]
  set g : ℕ → ℝ := fun j => ((j + 2 * l).choose (2 * l) : ℝ) * c ^ j
  have hterm : ∀ i ∈ range (n + 1), ((i.choose l : ℝ) * c ^ (i - l)) ^ 2
      ≤ if l ≤ i then g (2 * (i - l)) else 0 := by
    intro i _
    split_ifs with hli
    · simp only [g]
      rw [mul_pow, ← pow_mul, mul_comm (i - l) 2, show 2 * (i - l) + 2 * l = 2 * i by omega]
      exact mul_le_mul_of_nonneg_right (choose_sq_le i l) (by positivity)
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (fun i => 2 * (i - l)) ((range (n + 1)).filter (l ≤ ·)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
    simp only at hxy; omega
  rw [← Finset.sum_image (g := fun i => 2 * (i - l)) (f := g) hinj]
  refine (Finset.sum_le_sum_of_subset_of_nonneg (t := range (2 * n + 1)) ?_ (fun j _ _ => by
    positivity)).trans ?_
  · intro j hj
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hj ⊢
    obtain ⟨i, ⟨hi, _⟩, rfl⟩ := hj; omega
  · have := negbin_le (2 * l) (2 * n + 1) h0 h1
    simpa [g] using this

/-- Second moments of Hasse derivatives, polynomial-degree form. -/
lemma hasse_moment_le' (l : ℕ) {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    ∑ i : Fin (n + 1), (((i : ℕ).choose l : ℝ) * c ^ ((i : ℕ) - l)) ^ 2
      ≤ (n + 1) * ((n : ℝ) ^ l / l.factorial) ^ 2 := by
  have hterm : ∀ i : Fin (n + 1), (((i : ℕ).choose l : ℝ) * c ^ ((i : ℕ) - l)) ^ 2
      ≤ ((n : ℝ) ^ l / l.factorial) ^ 2 := by
    intro i
    have hc : c ^ ((i : ℕ) - l) ≤ 1 := pow_le_one₀ h0 h1
    have hc0 : 0 ≤ c ^ ((i : ℕ) - l) := pow_nonneg h0 _
    have hch : ((i : ℕ).choose l : ℝ) ≤ (n.choose l : ℝ) := by
      exact_mod_cast Nat.choose_le_choose l (Nat.lt_succ_iff.mp i.2)
    have hcp : (n.choose l : ℝ) ≤ (n : ℝ) ^ l / l.factorial := Nat.choose_le_pow_div l n
    have h00 : (0 : ℝ) ≤ ((i : ℕ).choose l : ℝ) := by positivity
    apply pow_le_pow_left₀ (mul_nonneg h00 hc0)
    calc ((i : ℕ).choose l : ℝ) * c ^ ((i : ℕ) - l) ≤ ((i : ℕ).choose l : ℝ) * 1 := by gcongr
      _ ≤ _ := by rw [mul_one]; linarith
  calc _ ≤ ∑ _i : Fin (n + 1), ((n : ℝ) ^ l / l.factorial) ^ 2 := Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by simp

/-- Bernoulli: many weights `c^i` are at least `1/2`. -/
lemma card_big_weights {c : ℝ} (h0 : 0 ≤ c) (h1 : c < 1) :
    min ((n : ℝ) + 1) (1 / (2 * (1 - c))) ≤
      ((univ.filter fun i : Fin (n + 1) => 1 ≤ |2 * c ^ (i : ℕ)|).card : ℝ) := by
  set I := univ.filter fun i : Fin (n + 1) => 1 ≤ |2 * c ^ (i : ℕ)|
  set K := min n (⌊1 / (2 * (1 - c))⌋₊) with hK
  have hsub : (univ.filter fun i : Fin (n + 1) => (i : ℕ) ≤ K)
      ⊆ I := by
    intro i hi
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have hiK : (i : ℝ) ≤ 1 / (2 * (1 - c)) := by
      have : (i : ℕ) ≤ ⌊1 / (2 * (1 - c))⌋₊ := hi.trans (min_le_right _ _)
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by
        have : 0 < 1 - c := by linarith
        positivity))
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ c - 1 by linarith) (i : ℕ)
    rw [show (1 : ℝ) + (c - 1) = c by ring] at hb
    have : (i : ℝ) * (1 - c) ≤ 1 / 2 := by
      have hpos : 0 < 1 - c := by linarith
      rw [le_div_iff₀ (by positivity)] at hiK; linarith
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have hcard : ((univ.filter fun i : Fin (n + 1) => (i : ℕ) ≤ K).card : ℝ) = K + 1 := by
    have : (univ.filter fun i : Fin (n + 1) => (i : ℕ) ≤ K) = (Finset.Iic (⟨K, by omega⟩ : Fin (n + 1))) := by
      ext i; simp [Fin.le_def]
    rw [this, Fin.card_Iic]; push_cast; ring
  have hle : ((univ.filter fun i : Fin (n + 1) => (i : ℕ) ≤ K).card : ℝ) ≤ (I.card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  rw [hcard] at hle
  refine le_trans ?_ hle
  rw [hK]
  rcases le_total n (⌊1 / (2 * (1 - c))⌋₊) with h | h
  · rw [min_eq_left h]; exact min_le_left _ _
  · rw [min_eq_right h]
    have := Nat.lt_floor_add_one (1 / (2 * (1 - c)))
    exact (min_le_right _ _).trans (by push_cast; linarith)

lemma PP_card {ι : Type*} [Fintype ι] [DecidableEq ι] (S : (ι → ℤˣ) → Prop) [DecidablePred S] :
    PP S = ((univ.filter S).card : ℝ) / 2 ^ Fintype.card ι := by
  rw [PP_eq]; unfold EE; rw [Finset.sum_boole]

/-- Littlewood–Offord for `P(c)`. -/
theorem small_ball_eval {c : ℝ} (h0 : 0 ≤ c) (h1 : c < 1) {r : ℝ} (hr : 0 ≤ r) :
    PP (fun ε : Fin (n + 1) → ℤˣ => |(poly ε).eval c| ≤ r)
      ≤ (2 * r + 2) / √(min ((n : ℝ) + 1) (1 / (2 * (1 - c)))) := by
  classical
  set I := univ.filter fun i : Fin (n + 1) => 1 ≤ |2 * c ^ (i : ℕ)|
  have hI := card_big_weights (n := n) h0 h1
  have hmin : 0 < min ((n : ℝ) + 1) (1 / (2 * (1 - c))) := by
    have : 0 < 1 - c := by linarith
    exact lt_min (by positivity) (by positivity)
  have hIne : I.Nonempty := by
    rw [← Finset.card_pos]; exact_mod_cast hmin.trans_le hI
  set a : Fin (n + 1) → ℝ := fun i => 2 * c ^ (i : ℕ)
  set K := ⌈2 * r⌉₊ + 1
  have hcov : ∀ ε : Fin (n + 1) → ℤˣ, |(poly ε).eval c| ≤ r →
      ∃ j ∈ range K, (-2 * r + 2 * j) ≤ ssum ε a ∧ ssum ε a < (-2 * r + 2 * j) + 2 := by
    intro ε hε
    have hs : ssum ε a = 2 * (poly ε).eval c := by
      rw [poly_eval]; unfold ssum; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => by simp only [a]; ring)
    rw [hs]
    set x := 2 * (poly ε).eval c
    have hx : |x| ≤ 2 * r := by simp only [x, abs_mul]; norm_num; linarith
    rw [abs_le] at hx
    refine ⟨⌊(x + 2 * r) / 2⌋₊, ?_, ?_, ?_⟩
    · rw [Finset.mem_range]
      have : ⌊(x + 2 * r) / 2⌋₊ ≤ ⌈2 * r⌉₊ := by
        apply Nat.floor_le_of_le
        calc (x + 2 * r) / 2 ≤ 2 * r := by linarith
          _ ≤ _ := Nat.le_ceil _
      omega
    · have := Nat.floor_le (show 0 ≤ (x + 2 * r) / 2 by linarith)
      linarith
    · have := Nat.lt_floor_add_one ((x + 2 * r) / 2)
      linarith
  have hstep : PP (fun ε : Fin (n + 1) → ℤˣ => |(poly ε).eval c| ≤ r)
      ≤ ∑ j ∈ range K, PP (fun ε : Fin (n + 1) → ℤˣ =>
          (-2 * r + 2 * j) ≤ ssum ε a ∧ ssum ε a < (-2 * r + 2 * j) + 2) :=
    (PP_mono (fun ε hε => hcov ε hε)).trans (PP_exists_le _ _)
  have hone : ∀ j : ℕ, PP (fun ε : Fin (n + 1) → ℤˣ =>
      (-2 * r + 2 * j) ≤ ssum ε a ∧ ssum ε a < (-2 * r + 2 * j) + 2) ≤ 1 / √(I.card) := by
    intro j
    rw [PP_card]
    have hlo := lo_interval a I (fun i hi => (Finset.mem_filter.1 hi).2) hIne (-2 * r + 2 * j)
    have h2 : (0 : ℝ) < 2 ^ Fintype.card (Fin (n + 1)) := by positivity
    rw [div_le_iff₀ h2]
    calc ((univ.filter fun ε : Fin (n + 1) → ℤˣ =>
          (-2 * r + 2 * j) ≤ ssum ε a ∧ ssum ε a < (-2 * r + 2 * j) + 2).card : ℝ)
        ≤ 2 ^ Fintype.card (Fin (n + 1)) / √(I.card) := hlo
      _ = 1 / √(I.card) * 2 ^ Fintype.card (Fin (n + 1)) := by ring
  have hsq : √(min ((n : ℝ) + 1) (1 / (2 * (1 - c)))) ≤ √(I.card) := Real.sqrt_le_sqrt hI
  have hsq0 : 0 < √(min ((n : ℝ) + 1) (1 / (2 * (1 - c)))) := Real.sqrt_pos.2 hmin
  have hK : (K : ℝ) ≤ 2 * r + 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 * r by linarith)
    simp only [K]; push_cast; linarith
  calc _ ≤ ∑ j ∈ range K, PP (fun ε : Fin (n + 1) → ℤˣ =>
          (-2 * r + 2 * j) ≤ ssum ε a ∧ ssum ε a < (-2 * r + 2 * j) + 2) := hstep
    _ ≤ ∑ _j ∈ range K, 1 / √(I.card) := Finset.sum_le_sum (fun j _ => hone j)
    _ = K * (1 / √(I.card)) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (2 * r + 2) * (1 / √(min ((n : ℝ) + 1) (1 / (2 * (1 - c))))) := by
        gcongr
    _ = _ := by ring

lemma iter_eval_hasse (p : ℝ[X]) (k : ℕ) (x : ℝ) :
    (derivative^[k] p).eval x = k.factorial * (hasseDeriv k p).eval x := by
  have := congrFun (factorial_smul_hasseDeriv (R := ℝ) (k := k)) p
  rw [← this]
  simp [nsmul_eq_mul]

/-- **Window tail bound.** -/
theorem win_tail {c h : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (hh : 0 ≤ h) (k : ℕ) (μ : ℕ → ℝ)
    (hμ : ∀ l, 0 < μ l)
    (hD : ∀ l, ∑ i : Fin (n + 1), (((i : ℕ).choose l : ℝ) * c ^ ((i : ℕ) - l)) ^ 2 ≤ μ l ^ 2)
    {A : ℝ} (hA : 0 < A) :
    PP (fun ε : Fin (n + 1) → ℤˣ => k ≤ nIn (poly ε) (Set.Icc c (c + h)))
      ≤ 1 / A ^ 2 + (2 * (A * h ^ k * ∑ i ∈ range (n + 1), ((k + i).choose i : ℝ) * h ^ i * μ (k + i)) + 2)
          / √(min ((n : ℝ) + 1) (1 / (2 * (1 - c)))) := by
  classical
  set M := ∑ i ∈ range (n + 1), ((k + i).choose i : ℝ) * h ^ i * μ (k + i) with hM
  have hM0 : 0 < M := by
    rw [hM, Finset.sum_range_succ']
    have : 0 < ((k + 0).choose 0 : ℝ) * h ^ 0 * μ (k + 0) := by simp [hμ]
    have h2 : 0 ≤ ∑ i ∈ range n, ((k + (i + 1)).choose (i + 1) : ℝ) * h ^ (i + 1) * μ (k + (i + 1)) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (hμ _).le)
    linarith
  have hsub : ∀ ε : Fin (n + 1) → ℤˣ, k ≤ nIn (poly ε) (Set.Icc c (c + h)) →
      A * M ≤ |Zk ε k c h| ∨ |(poly ε).eval c| ≤ A * h ^ k * M := by
    intro ε hk
    obtain ⟨ξ, hξ, hle⟩ := hermite (poly ε) c (c + h) c ⟨le_rfl, by linarith⟩ k hk
    rw [iter_eval_hasse] at hle
    have hkf : (0 : ℝ) < k.factorial := by positivity
    have h1 : |(poly ε).eval c| ≤ h ^ k * |(hasseDeriv k (poly ε)).eval ξ| := by
      rw [abs_mul, abs_of_pos hkf] at hle
      rw [show c + h - c = h by ring] at hle
      nlinarith
    have h2 := hasse_le_Zk ε k hh hξ
    by_cases hz : A * M ≤ |Zk ε k c h|
    · exact Or.inl hz
    · right
      push Not at hz
      have hZ0 : 0 ≤ Zk ε k c h := Finset.sum_nonneg (fun i _ => by positivity)
      rw [abs_of_nonneg hZ0] at hz
      calc |(poly ε).eval c| ≤ h ^ k * |(hasseDeriv k (poly ε)).eval ξ| := h1
        _ ≤ h ^ k * Zk ε k c h := by gcongr
        _ ≤ h ^ k * (A * M) := by gcongr
        _ = A * h ^ k * M := by ring
  have hP1 : PP (fun ε : Fin (n + 1) → ℤˣ => A * M ≤ |Zk ε k c h|) ≤ 1 / A ^ 2 := by
    refine (chebyshev (fun ε => Zk ε k c h) (mul_pos hA hM0)).trans ?_
    have := EE_Zk_sq (n := n) k c h hh μ hμ hD
    rw [← hM] at this
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc EE (fun ε : Fin (n + 1) → ℤˣ => Zk ε k c h ^ 2) * A ^ 2 ≤ M ^ 2 * A ^ 2 := by gcongr
      _ = 1 * (A * M) ^ 2 := by ring
  have hP2 := small_ball_eval (n := n) hc0 hc1 (r := A * h ^ k * M) (by positivity)
  calc PP (fun ε : Fin (n + 1) → ℤˣ => k ≤ nIn (poly ε) (Set.Icc c (c + h)))
      ≤ PP (fun ε : Fin (n + 1) → ℤˣ => A * M ≤ |Zk ε k c h| ∨ |(poly ε).eval c| ≤ A * h ^ k * M) :=
        PP_mono hsub
    _ ≤ _ := (PP_or_le _ _).trans (add_le_add hP1 hP2)

end R522

end S_RR6

-- ===== RR7 =====

/-!
# Erdős 522 (real roots), part 7: sign-change probabilities for a pair of weight vectors

`pair_up`: for weights `w₁, w₂` with correlation `ρ ≥ ρ₀ > 0`,
  `P(⟨ε, w₁⟩ ⟨ε, w₂⟩ < 0) ≤ arccos ρ₀ / π + 4w/√(2π) + 4/R² + 2 C (∑w₁⁴/S₁₁² + ∑w₂⁴/S₂₂²)`.
`pair_low`: for correlation `0 ≤ ρ ≤ ρ₁`, the robust straddle (margin `τ`) has probability at least
  `arccos ρ₁ / π - 4(τ+2w)/√(2π) - 4/R² - 2 C (…)`.
-/

open Finset Real MeasureTheory

noncomputable section S_RR7

namespace R522

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma lagrange (a b : ι → ℝ) :
    ∑ i, ∑ k, (a i * b k - a k * b i) ^ 2 = 2 * ((∑ i, a i ^ 2) * (∑ i, b i ^ 2) - (∑ i, a i * b i) ^ 2) := by
  have key : ∀ i, ∑ k, (a i * b k - a k * b i) ^ 2
      = a i ^ 2 * (∑ k, b k ^ 2) + (∑ k, a k ^ 2) * b i ^ 2 - 2 * (a i * b i) * (∑ k, a k * b k) := by
    intro i
    have e : ∀ k, (a i * b k - a k * b i) ^ 2
        = a i ^ 2 * b k ^ 2 + a k ^ 2 * b i ^ 2 - 2 * (a i * b i) * (a k * b k) := by
      intro k; ring
    simp_rw [e]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      ← Finset.mul_sum]
  simp_rw [key]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← Finset.sum_mul, ← Finset.mul_sum]
  ring

lemma cs_strict (a b : ι → ℝ) (i k : ι) (h : a i * b k ≠ a k * b i) :
    (∑ j, a j * b j) ^ 2 < (∑ j, a j ^ 2) * (∑ j, b j ^ 2) := by
  have hl := lagrange a b
  have hpos : 0 < ∑ i, ∑ k, (a i * b k - a k * b i) ^ 2 := by
    have h1 : 0 < (a i * b k - a k * b i) ^ 2 := by
      have : a i * b k - a k * b i ≠ 0 := sub_ne_zero.mpr h
      positivity
    have h2 : (a i * b k - a k * b i) ^ 2 ≤ ∑ k', (a i * b k' - a k' * b i) ^ 2 :=
      Finset.single_le_sum (f := fun k' => (a i * b k' - a k' * b i) ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ k)
    have h3 : ∑ k', (a i * b k' - a k' * b i) ^ 2 ≤ ∑ i', ∑ k', (a i' * b k' - a k' * b i') ^ 2 :=
      Finset.single_le_sum (f := fun i' => ∑ k', (a i' * b k' - a k' * b i') ^ 2)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i)
    linarith
  linarith

lemma PP_or_eq (S T : (ι → ℤˣ) → Prop) (h : ∀ ε, ¬ (S ε ∧ T ε)) :
    PP (fun ε => S ε ∨ T ε) = PP S + PP T := by
  classical
  rw [PP_eq, PP_eq, PP_eq, ← EE_add]
  congr 1; ext ε
  by_cases hs : S ε <;> by_cases ht : T ε <;> simp_all

lemma ssum_neg (ε : ι → ℤˣ) (a : ι → ℝ) : ssum ε (fun i => -a i) = -ssum ε a := by
  unfold ssum; simp [Finset.sum_neg_distrib]

lemma ssum_smul (ε : ι → ℤˣ) (a : ι → ℝ) (c : ℝ) : ssum ε (fun i => c * a i) = c * ssum ε a := by
  unfold ssum; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => by ring)

/-- Normalization data of a pair of weight vectors. -/
structure PairData (w₁ w₂ : ι → ℝ) where
  S₁ : 0 < ∑ i, w₁ i ^ 2
  S₂ : 0 < ∑ i, w₂ i ^ 2

/-- Normalized weights. -/
def nrm (w : ι → ℝ) : ι → ℝ := fun i => w i / √(∑ j, w j ^ 2)

lemma nrm_sq (w : ι → ℝ) (h : 0 < ∑ i, w i ^ 2) : ∑ i, nrm w i ^ 2 = 1 := by
  unfold nrm
  simp_rw [div_pow, Real.sq_sqrt h.le]
  rw [← Finset.sum_div, div_self h.ne']

lemma nrm_four (w : ι → ℝ) (h : 0 < ∑ i, w i ^ 2) :
    ∑ i, nrm w i ^ 4 = (∑ i, w i ^ 4) / (∑ i, w i ^ 2) ^ 2 := by
  unfold nrm
  have : ∀ i, (w i / √(∑ j, w j ^ 2)) ^ 4 = w i ^ 4 / (∑ j, w j ^ 2) ^ 2 := by
    intro i
    rw [div_pow, show (√(∑ j, w j ^ 2)) ^ 4 = (√(∑ j, w j ^ 2) ^ 2) ^ 2 by ring, Real.sq_sqrt h.le]
  simp_rw [this]; rw [Finset.sum_div]

lemma nrm_corr (w₁ w₂ : ι → ℝ) (h₁ : 0 < ∑ i, w₁ i ^ 2) (h₂ : 0 < ∑ i, w₂ i ^ 2) :
    ∑ i, nrm w₁ i * nrm w₂ i = (∑ i, w₁ i * w₂ i) / √((∑ i, w₁ i ^ 2) * (∑ i, w₂ i ^ 2)) := by
  unfold nrm
  rw [Real.sqrt_mul h₁.le, Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [div_mul_div_comm]

lemma ssum_nrm (ε : ι → ℤˣ) (w : ι → ℝ) (h : 0 < ∑ i, w i ^ 2) :
    ssum ε (nrm w) = ssum ε w / √(∑ i, w i ^ 2) := by
  unfold nrm ssum; rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun i _ => by ring)

lemma nrm_rho_lt (w₁ w₂ : ι → ℝ) (h₁ : 0 < ∑ i, w₁ i ^ 2) (h₂ : 0 < ∑ i, w₂ i ^ 2)
    (hlt : (∑ i, w₁ i * w₂ i) ^ 2 < (∑ i, w₁ i ^ 2) * (∑ i, w₂ i ^ 2)) :
    |∑ i, nrm w₁ i * nrm w₂ i| < 1 := by
  rw [nrm_corr w₁ w₂ h₁ h₂, abs_div, abs_of_pos (Real.sqrt_pos.2 (mul_pos h₁ h₂)),
    div_lt_one (Real.sqrt_pos.2 (mul_pos h₁ h₂))]
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) hlt

/-- Proof-free versions of the constants. -/
def CqU (R w : ℝ) : ℝ :=
  if h : 0 < R ∧ 0 < w then Cq 0 R w (-R) 0 w h.1 h.2 (by linarith [h.1]) h.2 else 0

lemma CqU_eq {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (h' : -R < 0) :
    Cq 0 R w (-R) 0 w hR hw h' hw = CqU R w := by
  rw [CqU, dif_pos ⟨hR, hw⟩]

def CqL (τ R w : ℝ) : ℝ :=
  if h : τ + 2 * w < R ∧ 0 < w then
    Cq (τ + 2 * w) R w (-R) (-τ - 2 * w) w h.1 h.2 (by linarith [h.1]) h.2 else 0

lemma CqL_eq {τ R w : ℝ} (hR : τ + 2 * w < R) (hw : 0 < w) (h' : -R < -τ - 2 * w) :
    Cq (τ + 2 * w) R w (-R) (-τ - 2 * w) w hR hw h' hw = CqL τ R w := by
  rw [CqL, dif_pos ⟨hR, hw⟩]

/-- **Sign-change upper bound for a pair.** -/
theorem pair_up (w₁ w₂ : ι → ℝ) (h₁ : 0 < ∑ i, w₁ i ^ 2) (h₂ : 0 < ∑ i, w₂ i ^ 2)
    (hlt : (∑ i, w₁ i * w₂ i) ^ 2 < (∑ i, w₁ i ^ 2) * (∑ i, w₂ i ^ 2))
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hcorr : ρ₀ * √((∑ i, w₁ i ^ 2) * (∑ i, w₂ i ^ 2)) ≤ ∑ i, w₁ i * w₂ i)
    {R w : ℝ} (hR : 0 < R) (hw : 0 < w) :
    PP (fun ε : ι → ℤˣ => ssum ε w₁ * ssum ε w₂ < 0)
      ≤ Real.arccos ρ₀ / π + 4 * w / √(2 * π) + 4 / R ^ 2
        + 2 * CqU R w
          * ((∑ i, w₁ i ^ 4) / (∑ i, w₁ i ^ 2) ^ 2 + (∑ i, w₂ i ^ 4) / (∑ i, w₂ i ^ 2) ^ 2) := by
  set a := nrm w₁
  set b := nrm w₂
  set ρ := ∑ i, a i * b i with hρ
  have ha := nrm_sq w₁ h₁
  have hb := nrm_sq w₂ h₂
  have hρlt := nrm_rho_lt w₁ w₂ h₁ h₂ hlt
  rw [abs_lt] at hρlt
  have hρge : ρ₀ ≤ ρ := by
    rw [hρ, nrm_corr w₁ w₂ h₁ h₂, le_div_iff₀ (Real.sqrt_pos.2 (mul_pos h₁ h₂))]; exact hcorr
  have hs₁ := Real.sqrt_pos.2 h₁
  have hs₂ := Real.sqrt_pos.2 h₂
  have hevt : ∀ ε : ι → ℤˣ, ssum ε w₁ * ssum ε w₂ < 0 →
      (0 < ssum ε a ∧ ssum ε b < 0) ∨ (0 < ssum ε (fun i => -a i) ∧ ssum ε (fun i => -b i) < 0) := by
    intro ε hε
    rw [ssum_neg, ssum_neg, ssum_nrm ε w₁ h₁, ssum_nrm ε w₂ h₂]
    rcases lt_or_gt_of_ne (show ssum ε w₁ ≠ 0 by intro h0; rw [h0, zero_mul] at hε; exact lt_irrefl _ hε)
      with h | h
    · right
      have : 0 < ssum ε w₂ := by nlinarith
      constructor
      · rw [neg_pos]; exact div_neg_of_neg_of_pos h hs₁
      · rw [neg_lt_zero]; exact div_pos this hs₂
    · left
      have : ssum ε w₂ < 0 := by nlinarith
      exact ⟨div_pos h hs₁, div_neg_of_neg_of_pos this hs₂⟩
  have q1 := quad_up a b ρ ha hb rfl hρlt.1 hρlt.2 hR hw
  have q2 := quad_up (fun i => -a i) (fun i => -b i) ρ (by simpa using ha) (by simpa using hb)
    (by simp [hρ]) hρlt.1 hρlt.2 hR hw
  have e4 : ∀ c : ι → ℝ, ∑ i, (-c i) ^ 4 = ∑ i, c i ^ 4 := fun c =>
    Finset.sum_congr rfl (fun i _ => by ring)
  rw [e4, e4] at q2
  rw [nrm_four w₁ h₁, nrm_four w₂ h₂, CqU_eq hR hw] at q1 q2
  have harc : Real.arccos ρ ≤ Real.arccos ρ₀ := Real.arccos_le_arccos hρge
  have hπ : 0 < π := Real.pi_pos
  calc PP (fun ε : ι → ℤˣ => ssum ε w₁ * ssum ε w₂ < 0)
      ≤ PP (fun ε => (0 < ssum ε a ∧ ssum ε b < 0) ∨
          (0 < ssum ε (fun i => -a i) ∧ ssum ε (fun i => -b i) < 0)) := PP_mono hevt
    _ ≤ _ := PP_or_le _ _
    _ ≤ _ := add_le_add q1 q2
    _ ≤ _ := by
        have : Real.arccos ρ / (2 * π) ≤ Real.arccos ρ₀ / (2 * π) := by gcongr
        have e : Real.arccos ρ₀ / π = Real.arccos ρ₀ / (2 * π) + Real.arccos ρ₀ / (2 * π) := by
          field_simp; ring
        rw [e]
        set X := (∑ i, w₁ i ^ 4) / (∑ i, w₁ i ^ 2) ^ 2 + (∑ i, w₂ i ^ 4) / (∑ i, w₂ i ^ 2) ^ 2
        set T := Real.arccos ρ / (2 * π)
        set T₀ := Real.arccos ρ₀ / (2 * π)
        set u := w / √(2 * π)
        have e1 : 2 * w / √(2 * π) = 2 * u := by simp only [u]; ring
        have e2 : 4 * w / √(2 * π) = 4 * u := by simp only [u]; ring
        have e3 : (4 : ℝ) / R ^ 2 = 2 / R ^ 2 + 2 / R ^ 2 := by ring
        rw [e1, e2, e3]
        nlinarith

/-- **Robust straddle lower bound for a pair.** -/
theorem pair_low (w₁ w₂ : ι → ℝ) (h₁ : 0 < ∑ i, w₁ i ^ 2) (h₂ : 0 < ∑ i, w₂ i ^ 2)
    (hlt : (∑ i, w₁ i * w₂ i) ^ 2 < (∑ i, w₁ i ^ 2) * (∑ i, w₂ i ^ 2))
    (h0 : 0 ≤ ∑ i, w₁ i * w₂ i) {ρ₁ : ℝ}
    (hcorr : ∑ i, w₁ i * w₂ i ≤ ρ₁ * √((∑ i, w₁ i ^ 2) * (∑ i, w₂ i ^ 2)))
    {τ R w : ℝ} (hτ : 0 ≤ τ) (hw : 0 < w) (hR : τ + 2 * w < R) :
    Real.arccos ρ₁ / π - 4 * (τ + 2 * w) / √(2 * π) - 4 / R ^ 2
        - 2 * CqL τ R w
          * ((∑ i, w₁ i ^ 4) / (∑ i, w₁ i ^ 2) ^ 2 + (∑ i, w₂ i ^ 4) / (∑ i, w₂ i ^ 2) ^ 2)
      ≤ PP (fun ε : ι → ℤˣ =>
          (τ * √(∑ i, w₁ i ^ 2) < ssum ε w₁ ∧ ssum ε w₂ < -(τ * √(∑ i, w₂ i ^ 2))) ∨
          (ssum ε w₁ < -(τ * √(∑ i, w₁ i ^ 2)) ∧ τ * √(∑ i, w₂ i ^ 2) < ssum ε w₂)) := by
  set a := nrm w₁
  set b := nrm w₂
  set ρ := ∑ i, a i * b i with hρ
  have ha := nrm_sq w₁ h₁
  have hb := nrm_sq w₂ h₂
  have hρlt := nrm_rho_lt w₁ w₂ h₁ h₂ hlt
  rw [abs_lt] at hρlt
  have hs₁ := Real.sqrt_pos.2 h₁
  have hs₂ := Real.sqrt_pos.2 h₂
  have hρle : ρ ≤ ρ₁ := by
    rw [hρ, nrm_corr w₁ w₂ h₁ h₂, div_le_iff₀ (Real.sqrt_pos.2 (mul_pos h₁ h₂))]; exact hcorr
  have q1 := quad_low a b ρ ha hb rfl hρlt.1 hρlt.2 hτ hw hR
  have q2 := quad_low (fun i => -a i) (fun i => -b i) ρ (by simpa using ha) (by simpa using hb)
    (by simp [hρ]) hρlt.1 hρlt.2 hτ hw hR
  have e4 : ∀ c : ι → ℝ, ∑ i, (-c i) ^ 4 = ∑ i, c i ^ 4 := fun c =>
    Finset.sum_congr rfl (fun i _ => by ring)
  rw [e4, e4] at q2
  rw [nrm_four w₁ h₁, nrm_four w₂ h₂, CqL_eq hR hw] at q1 q2
  have harc : Real.arccos ρ₁ ≤ Real.arccos ρ := Real.arccos_le_arccos hρle
  have hiff1 : ∀ ε : ι → ℤˣ, (τ < ssum ε a ∧ ssum ε b < -τ) ↔
      (τ * √(∑ i, w₁ i ^ 2) < ssum ε w₁ ∧ ssum ε w₂ < -(τ * √(∑ i, w₂ i ^ 2))) := by
    intro ε
    rw [ssum_nrm ε w₁ h₁, ssum_nrm ε w₂ h₂, lt_div_iff₀ hs₁, div_lt_iff₀ hs₂, neg_mul]
  have aux1 : ∀ {X s : ℝ}, 0 < s → (τ < -(X / s) ↔ X < -(τ * s)) := by
    intro X s hs
    rw [← neg_div, lt_div_iff₀ hs]; constructor <;> intro h <;> linarith
  have aux2 : ∀ {Y s : ℝ}, 0 < s → (-(Y / s) < -τ ↔ τ * s < Y) := by
    intro Y s hs
    rw [neg_lt_neg_iff, lt_div_iff₀ hs]
  have hiff2 : ∀ ε : ι → ℤˣ, (τ < ssum ε (fun i => -a i) ∧ ssum ε (fun i => -b i) < -τ) ↔
      (ssum ε w₁ < -(τ * √(∑ i, w₁ i ^ 2)) ∧ τ * √(∑ i, w₂ i ^ 2) < ssum ε w₂) := by
    intro ε
    rw [ssum_neg, ssum_neg, ssum_nrm ε w₁ h₁, ssum_nrm ε w₂ h₂, aux1 hs₁, aux2 hs₂]
  have hdisj : ∀ ε : ι → ℤˣ, ¬ ((τ * √(∑ i, w₁ i ^ 2) < ssum ε w₁ ∧ ssum ε w₂ < -(τ * √(∑ i, w₂ i ^ 2))) ∧
      (ssum ε w₁ < -(τ * √(∑ i, w₁ i ^ 2)) ∧ τ * √(∑ i, w₂ i ^ 2) < ssum ε w₂)) := by
    rintro ε ⟨⟨h1, _⟩, ⟨h3, _⟩⟩
    have : 0 ≤ τ * √(∑ i, w₁ i ^ 2) := by positivity
    linarith
  rw [PP_or_eq _ _ hdisj]
  have p1 : PP (fun ε : ι → ℤˣ => τ < ssum ε a ∧ ssum ε b < -τ)
      = PP (fun ε : ι → ℤˣ => τ * √(∑ i, w₁ i ^ 2) < ssum ε w₁ ∧ ssum ε w₂ < -(τ * √(∑ i, w₂ i ^ 2))) := by
    congr 1; ext ε; exact hiff1 ε
  have p2 : PP (fun ε : ι → ℤˣ => τ < ssum ε (fun i => -a i) ∧ ssum ε (fun i => -b i) < -τ)
      = PP (fun ε : ι → ℤˣ => ssum ε w₁ < -(τ * √(∑ i, w₁ i ^ 2)) ∧ τ * √(∑ i, w₂ i ^ 2) < ssum ε w₂) := by
    congr 1; ext ε; exact hiff2 ε
  rw [← p1, ← p2]
  have hπ : 0 < π := Real.pi_pos
  have : Real.arccos ρ₁ / (2 * π) ≤ Real.arccos ρ / (2 * π) := by gcongr
  have e : Real.arccos ρ₁ / π = Real.arccos ρ₁ / (2 * π) + Real.arccos ρ₁ / (2 * π) := by
    field_simp; ring
  rw [e]
  set X := (∑ i, w₁ i ^ 4) / (∑ i, w₁ i ^ 2) ^ 2 + (∑ i, w₂ i ^ 4) / (∑ i, w₂ i ^ 2) ^ 2
  set u := (τ + 2 * w) / √(2 * π)
  have e1 : 2 * (τ + 2 * w) / √(2 * π) = 2 * u := by simp only [u]; ring
  have e2 : 4 * (τ + 2 * w) / √(2 * π) = 4 * u := by simp only [u]; ring
  have e3 : (4 : ℝ) / R ^ 2 = 2 / R ^ 2 + 2 / R ^ 2 := by ring
  rw [e1] at q1 q2
  rw [e2, e3]
  nlinarith

end R522

end S_RR7

-- ===== RR8 =====

/-!
# Erdős 522 (real roots), part 8: the grid and its correlations

Grid `gx L j = (λʲ - 1)/(λʲ + 1)`, `λ = 1 + 1/L` (so `artanh (gx L j) = j log λ / 2`).
For neighbouring grid points the full-sum correlation is at least `ρ₀ = 2√λ/(1+λ)`, and the block-sum
correlation is at most `ρ₀ / (1 - y^{2M})`.
-/

open Finset Real

noncomputable section S_RR8

namespace R522

/-- The grid ratio. -/
def lam (L : ℕ) : ℝ := 1 + 1 / (L : ℝ)

/-- Grid points. -/
def gx (L j : ℕ) : ℝ := (lam L ^ j - 1) / (lam L ^ j + 1)

/-- The neighbour correlation. -/
def rho0 (L : ℕ) : ℝ := 2 * √(lam L) / (1 + lam L)

variable {L : ℕ}

lemma lam_gt (hL : 1 ≤ L) : 1 < lam L := by
  unfold lam; have : (0 : ℝ) < 1 / (L : ℝ) := by positivity
  linarith

lemma lam_le_two (hL : 1 ≤ L) : lam L ≤ 2 := by
  unfold lam
  have : 1 / (L : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact_mod_cast hL
  linarith

lemma lam_pow_ge_one (hL : 1 ≤ L) (j : ℕ) : 1 ≤ lam L ^ j := one_le_pow₀ (lam_gt hL).le

lemma one_sub_gx (hL : 1 ≤ L) (j : ℕ) : 1 - gx L j = 2 / (lam L ^ j + 1) := by
  have := lam_pow_ge_one hL j
  unfold gx; field_simp; ring

lemma gx_nonneg (hL : 1 ≤ L) (j : ℕ) : 0 ≤ gx L j := by
  have := lam_pow_ge_one hL j
  unfold gx; apply div_nonneg <;> linarith

lemma gx_lt_one (hL : 1 ≤ L) (j : ℕ) : gx L j < 1 := by
  have := lam_pow_ge_one hL j
  unfold gx; rw [div_lt_one (by linarith)]; linarith

lemma gx_pos (hL : 1 ≤ L) {j : ℕ} (hj : 1 ≤ j) : 0 < gx L j := by
  have : 1 < lam L ^ j := one_lt_pow₀ (lam_gt hL) (by omega)
  unfold gx; apply div_pos <;> linarith

lemma gx_lt_succ (hL : 1 ≤ L) (j : ℕ) : gx L j < gx L (j + 1) := by
  have h1 := lam_pow_ge_one hL j
  have h2 : lam L ^ j < lam L ^ (j + 1) := pow_lt_pow_right₀ (lam_gt hL) (by omega)
  have : 1 - gx L (j + 1) < 1 - gx L j := by
    rw [one_sub_gx hL, one_sub_gx hL]
    apply div_lt_div_of_pos_left (by norm_num) (by linarith) (by linarith)
  linarith

lemma gx_mono (hL : 1 ≤ L) {j k : ℕ} (h : j ≤ k) : gx L j ≤ gx L k := by
  induction k with
  | zero => rw [Nat.le_zero.mp h]
  | succ k ih =>
    rcases Nat.of_le_succ h with h | h
    · exact (ih h).trans (gx_lt_succ hL k).le
    · rw [h]

lemma gx_rat (L j : ℕ) : ∃ q : ℚ, (q : ℝ) = gx L j :=
  ⟨((1 + 1 / (L : ℚ)) ^ j - 1) / ((1 + 1 / (L : ℚ)) ^ j + 1), by unfold gx lam; push_cast; rfl⟩

lemma rho0_sq (hL : 1 ≤ L) : rho0 L ^ 2 = 4 * lam L / (1 + lam L) ^ 2 := by
  unfold rho0
  rw [div_pow, mul_pow, Real.sq_sqrt (by linarith [lam_gt hL])]; ring

lemma rho0_pos (hL : 1 ≤ L) : 0 < rho0 L := by
  unfold rho0; have := lam_gt hL; positivity

/-- The exact neighbour identity. -/
lemma grid_identity (hL : 1 ≤ L) (j : ℕ) :
    (1 - gx L j ^ 2) * (1 - gx L (j + 1) ^ 2) = rho0 L ^ 2 * (1 - gx L j * gx L (j + 1)) ^ 2 := by
  rw [rho0_sq hL]
  unfold gx
  set s := lam L ^ j
  have hs : 1 ≤ s := lam_pow_ge_one hL j
  have hl := lam_gt hL
  have ht : lam L ^ (j + 1) = lam L * s := by rw [pow_succ]; ring
  rw [ht]
  field_simp
  ring

/-- `arccos ρ₀ ≤ (λ - 1)/2 = 1/(2L)`. -/
lemma arccos_rho0_le (hL : 1 ≤ L) : Real.arccos (rho0 L) ≤ 1 / (2 * L) := by
  have hl := lam_gt hL
  have hρ := rho0_pos hL
  have h1 : Real.arccos (rho0 L) ≤ Real.tan (Real.arccos (rho0 L)) :=
    Real.le_tan (Real.arccos_nonneg _) (Real.arccos_lt_pi_div_two.2 hρ)
  rw [Real.tan_arccos] at h1
  have h2 : √(1 - rho0 L ^ 2) = (lam L - 1) / (1 + lam L) := by
    rw [rho0_sq hL]
    have : 1 - 4 * lam L / (1 + lam L) ^ 2 = ((lam L - 1) / (1 + lam L)) ^ 2 := by
      field_simp; ring
    rw [this, Real.sqrt_sq (by apply div_nonneg <;> linarith)]
  rw [h2] at h1
  have h3 : (lam L - 1) / (1 + lam L) / rho0 L = (lam L - 1) / (2 * √(lam L)) := by
    unfold rho0; field_simp
  rw [h3] at h1
  have hsq : 1 ≤ √(lam L) := by rw [Real.one_le_sqrt]; linarith
  have h4 : (lam L - 1) / (2 * √(lam L)) ≤ (lam L - 1) / 2 := by
    apply div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
  have h5 : (lam L - 1) / 2 = 1 / (2 * L) := by
    unfold lam; have : (0 : ℝ) < L := by exact_mod_cast hL
    field_simp; ring
  linarith

/-! ### Weight vectors -/

variable {n : ℕ}

/-- Full weights `xⁱ`. -/
def wf (n : ℕ) (x : ℝ) : Fin (n + 1) → ℝ := fun i => x ^ (i : ℕ)

lemma ssum_wf (ε : Fin (n + 1) → ℤˣ) (x : ℝ) : ssum ε (wf n x) = (poly ε).eval x := by
  rw [poly_eval]; rfl

lemma geom_fin (t : ℝ) (ht : t ≠ 1) (N : ℕ) :
    ∑ i : Fin N, t ^ (i : ℕ) = (1 - t ^ N) / (1 - t) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => t ^ i), geom_sum_eq ht]
  have : t - 1 ≠ 0 := sub_ne_zero.mpr ht
  have : 1 - t ≠ 0 := fun h => this (by linarith)
  field_simp; ring

/-- Full-sum correlation at neighbouring grid points. -/
theorem full_corr (hL : 1 ≤ L) (j : ℕ) :
    rho0 L * √((∑ i, wf n (gx L j) i ^ 2) * (∑ i, wf n (gx L (j + 1)) i ^ 2))
      ≤ ∑ i, wf n (gx L j) i * wf n (gx L (j + 1)) i := by
  set x := gx L j
  set y := gx L (j + 1)
  have hx0 := gx_nonneg hL j
  have hx1 := gx_lt_one hL j
  have hy0 := gx_nonneg hL (j + 1)
  have hy1 := gx_lt_one hL (j + 1)
  have hxy1 : x * y < 1 := by nlinarith
  have hxx1 : x * x < 1 := by nlinarith
  have hyy1 : y * y < 1 := by nlinarith
  have exy : ∑ i, wf n x i * wf n y i = (1 - (x * y) ^ (n + 1)) / (1 - x * y) := by
    rw [← geom_fin (x * y) hxy1.ne (n + 1)]
    refine Finset.sum_congr rfl (fun i _ => ?_); unfold wf; rw [mul_pow]
  have exx : ∑ i, wf n x i ^ 2 = (1 - (x * x) ^ (n + 1)) / (1 - x * x) := by
    rw [← geom_fin (x * x) hxx1.ne (n + 1)]
    refine Finset.sum_congr rfl (fun i _ => ?_); unfold wf; rw [mul_pow, sq]
  have eyy : ∑ i, wf n y i ^ 2 = (1 - (y * y) ^ (n + 1)) / (1 - y * y) := by
    rw [← geom_fin (y * y) hyy1.ne (n + 1)]
    refine Finset.sum_congr rfl (fun i _ => ?_); unfold wf; rw [mul_pow, sq]
  set u := x ^ (n + 1)
  set v := y ^ (n + 1)
  have hu0 : 0 ≤ u := pow_nonneg hx0 _
  have hv0 : 0 ≤ v := pow_nonneg hy0 _
  have hu1 : u ≤ 1 := pow_le_one₀ hx0 hx1.le
  have hv1 : v ≤ 1 := pow_le_one₀ hy0 hy1.le
  rw [mul_pow] at exy; rw [mul_pow] at exx eyy
  have hid := grid_identity hL j
  rw [← sq, ← sq] at exx eyy
  rw [show x ^ 2 = x * x by ring] at hid
  have hS : 0 ≤ ∑ i, wf n x i * wf n y i := by
    rw [exy]; apply div_nonneg <;> nlinarith
  have hsq : rho0 L ^ 2 * ((∑ i, wf n x i ^ 2) * (∑ i, wf n y i ^ 2)) ≤ (∑ i, wf n x i * wf n y i) ^ 2 := by
    have hA : 0 < 1 - x * y := by linarith
    have hB : 0 < 1 - x ^ 2 := by nlinarith
    have hC : 0 < 1 - y ^ 2 := by nlinarith
    have hρ0 : rho0 L ≠ 0 := (rho0_pos hL).ne'
    have key : (1 - u ^ 2) * (1 - v ^ 2) ≤ (1 - u * v) ^ 2 := by nlinarith [sq_nonneg (u - v)]
    have hid' : (1 - x ^ 2) * (1 - y ^ 2) = rho0 L ^ 2 * (1 - x * y) ^ 2 := by
      rw [← hid]; ring
    rw [exy, exx, eyy, div_mul_div_comm, hid']
    have e1 : rho0 L ^ 2 * ((1 - u ^ 2) * (1 - v ^ 2) / (rho0 L ^ 2 * (1 - x * y) ^ 2))
        = (1 - u ^ 2) * (1 - v ^ 2) / (1 - x * y) ^ 2 := by
      field_simp
    rw [e1, div_pow]
    exact div_le_div_of_nonneg_right key (by positivity)
  have hρ := rho0_pos hL
  calc rho0 L * √((∑ i, wf n x i ^ 2) * (∑ i, wf n y i ^ 2))
      = √(rho0 L ^ 2 * ((∑ i, wf n x i ^ 2) * (∑ i, wf n y i ^ 2))) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hρ.le]
    _ ≤ √((∑ i, wf n x i * wf n y i) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = _ := Real.sqrt_sq hS

/-! ### Window count and sign-change indicators (shared definitions) -/

/-- Number of grid windows used at degree `n`: `λ^J ≤ n < λ^(J+1)`. -/
def Jn (L n : ℕ) : ℕ := ⌊Real.log n / Real.log (lam L)⌋₊

/-- Sign change of `P` across the window `(gx L j, gx L (j+1))`. -/
def sc (ε : Fin (n + 1) → ℤˣ) (L j : ℕ) : ℝ :=
  if (poly ε).eval (gx L j) * (poly ε).eval (gx L (j + 1)) < 0 then 1 else 0

lemma sc_nonneg (ε : Fin (n + 1) → ℤˣ) (L j : ℕ) : 0 ≤ sc ε L j := by
  unfold sc; split_ifs <;> norm_num

lemma sc_le_one (ε : Fin (n + 1) → ℤˣ) (L j : ℕ) : sc ε L j ≤ 1 := by
  unfold sc; split_ifs <;> norm_num

lemma lam_pow_Jn_le (hL : 1 ≤ L) {n : ℕ} (hn : 1 ≤ n) : lam L ^ Jn L n ≤ n := by
  have hl := lam_gt hL
  have hlog : 0 < Real.log (lam L) := Real.log_pos hl
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.exp_log (pow_pos (by linarith) _), ← Real.exp_log hn', Real.exp_le_exp, Real.log_pow]
  have := Nat.floor_le (show 0 ≤ Real.log n / Real.log (lam L) from
    div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) hlog.le)
  unfold Jn
  calc (⌊Real.log n / Real.log (lam L)⌋₊ : ℝ) * Real.log (lam L)
      ≤ Real.log n / Real.log (lam L) * Real.log (lam L) := by gcongr
    _ = Real.log n := by field_simp

lemma lt_lam_pow_Jn (hL : 1 ≤ L) {n : ℕ} (hn : 1 ≤ n) : (n : ℝ) < lam L ^ (Jn L n + 1) := by
  have hl := lam_gt hL
  have hlog : 0 < Real.log (lam L) := Real.log_pos hl
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.exp_log (pow_pos (by linarith) _), ← Real.exp_log hn', Real.exp_lt_exp, Real.log_pow]
  have := Nat.lt_floor_add_one (Real.log n / Real.log (lam L))
  unfold Jn
  push_cast
  calc Real.log n = Real.log n / Real.log (lam L) * Real.log (lam L) := by field_simp
    _ < (⌊Real.log n / Real.log (lam L)⌋₊ + 1) * Real.log (lam L) := by gcongr

end R522

end S_RR8

-- ===== RR9 =====

/-!
# Erdős 522 (real roots), part 9: window estimates for the upper bound

* `sc_prob_le`: `P(sign change in window j) ≤ 1/(2πL) + 4w/√(2π) + 4/R² + 64 CqU / λʲ`.
* `win_N_tail`: `P(N_j ≥ k) ≤ 1/A² + 6A/(L-1)^k + 4/√(λʲ)` (Hermite + Taylor + Littlewood–Offord).
* `end_tail`: the last window `[gx L J, 1]`.
* `count_le`: pointwise `N ≤ sc + 2 ∑_{k=2}^{T} 1{N ≥ k}` when `N ≤ T`.
* `tail_from_mean`: an upper tail from a mean bound and a lower tail.
-/

open Finset Real Polynomial

noncomputable section S_RR9

namespace R522

variable {n L : ℕ}

lemma sum_wf_sq_lower {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    min ((n : ℝ) + 1) (1 / (4 * (1 - x))) / 2 ≤ ∑ i, wf n x i ^ 2 := by
  classical
  have hx2 : x ^ 2 < 1 := by nlinarith
  have hI := card_big_weights (n := n) (c := x ^ 2) (by positivity) hx2
  set I := univ.filter fun i : Fin (n + 1) => 1 ≤ |2 * (x ^ 2) ^ (i : ℕ)|
  have hmin : min ((n : ℝ) + 1) (1 / (4 * (1 - x))) ≤ min ((n : ℝ) + 1) (1 / (2 * (1 - x ^ 2))) := by
    apply min_le_min_left
    apply one_div_le_one_div_of_le (by nlinarith)
    nlinarith
  have hsum : (I.card : ℝ) / 2 ≤ ∑ i, wf n x i ^ 2 := by
    calc (I.card : ℝ) / 2 = ∑ _i ∈ I, (1 / 2 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ I, wf n x i ^ 2 := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          have := (Finset.mem_filter.1 hi).2
          rw [abs_of_nonneg (by positivity)] at this
          unfold wf; rw [← pow_mul, mul_comm, pow_mul]; linarith
      _ ≤ ∑ i, wf n x i ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => sq_nonneg _)
  linarith

lemma sum_wf_four_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    ∑ i, wf n x i ^ 4 ≤ ∑ i, wf n x i ^ 2 := by
  refine Finset.sum_le_sum (fun i _ => ?_)
  have a0 : 0 ≤ wf n x i := pow_nonneg h0 _
  have a1 : wf n x i ≤ 1 := pow_le_one₀ h0 h1
  have : wf n x i ^ 4 = wf n x i ^ 2 * wf n x i ^ 2 := by ring
  rw [this]
  have : wf n x i ^ 2 ≤ 1 := pow_le_one₀ a0 a1
  nlinarith [sq_nonneg (wf n x i)]

lemma ratio_four_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    (∑ i, wf n x i ^ 4) / (∑ i, wf n x i ^ 2) ^ 2
      ≤ 2 / min ((n : ℝ) + 1) (1 / (4 * (1 - x))) := by
  have hl := sum_wf_sq_lower (n := n) h0 h1
  have hm : 0 < min ((n : ℝ) + 1) (1 / (4 * (1 - x))) :=
    lt_min (by positivity) (by have : 0 < 1 - x := by linarith
                               positivity)
  have hS : 0 < ∑ i, wf n x i ^ 2 := by linarith
  have h4 := sum_wf_four_le (n := n) h0 h1.le
  rw [div_le_div_iff₀ (by positivity) hm]
  nlinarith

/-- **Per-window sign-change probability.** -/
theorem sc_prob_le (hL : 2 ≤ L) (hn : 1 ≤ n) {j : ℕ} (hj : 1 ≤ j) (hjn : lam L ^ j ≤ n)
    {R w : ℝ} (hR : 0 < R) (hw : 0 < w) :
    PP (fun ε : Fin (n + 1) → ℤˣ => (poly ε).eval (gx L j) * (poly ε).eval (gx L (j + 1)) < 0)
      ≤ 1 / (2 * π * L) + 4 * w / √(2 * π) + 4 / R ^ 2 + 2 * CqU R w * (32 / lam L ^ j) := by
  have hL1 : 1 ≤ L := by omega
  set x := gx L j
  set y := gx L (j + 1)
  have hx0 := gx_nonneg hL1 j
  have hx1 := gx_lt_one hL1 j
  have hy0 := gx_nonneg hL1 (j + 1)
  have hy1 := gx_lt_one hL1 (j + 1)
  have hxy : x < y := gx_lt_succ hL1 j
  have hSx := sum_wf_sq_lower (n := n) hx0 hx1
  have hSy := sum_wf_sq_lower (n := n) hy0 hy1
  have hs1 := lam_pow_ge_one hL1 j
  have hmx : (lam L ^ j + 1) / 8 = 1 / (4 * (1 - x)) := by
    rw [one_sub_gx hL1]; field_simp; ring
  have hmy : (lam L ^ (j + 1) + 1) / 8 = 1 / (4 * (1 - y)) := by
    rw [one_sub_gx hL1]; field_simp; ring
  have hpow : lam L ^ j ≤ lam L ^ (j + 1) := pow_le_pow_right₀ (lam_gt hL1).le (by omega)
  have hn' : (lam L ^ j + 1) / 8 ≤ (n : ℝ) + 1 := by linarith
  have hminx : min ((n : ℝ) + 1) (1 / (4 * (1 - x))) = (lam L ^ j + 1) / 8 := by
    rw [← hmx]; exact min_eq_right hn'
  have hminy : (lam L ^ j + 1) / 8 ≤ min ((n : ℝ) + 1) (1 / (4 * (1 - y))) := by
    rw [← hmy]; exact le_min hn' (by linarith)
  have h1 : 0 < ∑ i, wf n x i ^ 2 := by
    have : 0 < min ((n : ℝ) + 1) (1 / (4 * (1 - x))) := by rw [hminx]; positivity
    linarith
  have h2 : 0 < ∑ i, wf n y i ^ 2 := by
    have : 0 < (lam L ^ j + 1) / 8 := by positivity
    linarith
  have hlt : (∑ i, wf n x i * wf n y i) ^ 2 < (∑ i, wf n x i ^ 2) * (∑ i, wf n y i ^ 2) := by
    refine cs_strict (wf n x) (wf n y) ⟨0, by omega⟩ ⟨1, by omega⟩ ?_
    simp only [wf, pow_zero, pow_one, one_mul, mul_one]
    exact (ne_of_lt hxy).symm
  have hcorr := full_corr (n := n) hL1 j
  have hup := pair_up (wf n x) (wf n y) h1 h2 hlt (rho0_pos hL1) hcorr hR hw
  simp only [ssum_wf] at hup
  have hr1 := ratio_four_le (n := n) hx0 hx1
  have hr2 := ratio_four_le (n := n) hy0 hy1
  rw [hminx] at hr1
  have hr2' : 2 / min ((n : ℝ) + 1) (1 / (4 * (1 - y))) ≤ 2 / ((lam L ^ j + 1) / 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hminy
  have hsum : (∑ i, wf n x i ^ 4) / (∑ i, wf n x i ^ 2) ^ 2 + (∑ i, wf n y i ^ 4) / (∑ i, wf n y i ^ 2) ^ 2
      ≤ 32 / lam L ^ j := by
    have : 2 / ((lam L ^ j + 1) / 8) + 2 / ((lam L ^ j + 1) / 8) ≤ 32 / lam L ^ j := by
      have hs0 : 0 < lam L ^ j := by positivity
      have e : 2 / ((lam L ^ j + 1) / 8) + 2 / ((lam L ^ j + 1) / 8) = 32 / (lam L ^ j + 1) := by
        field_simp; ring
      rw [e]
      exact div_le_div_of_nonneg_left (by norm_num) hs0 (by linarith)
    linarith
  have harc := arccos_rho0_le hL1
  have hπ := Real.pi_pos
  have hC : 0 ≤ CqU R w := by
    unfold CqU; rw [dif_pos ⟨hR, hw⟩]; unfold Cq
    have := mom_nonneg 4 (Sb 0 R w hR hw); have := mom_nonneg 0 (Sb (-R) 0 w (by linarith) hw)
    have := mom_nonneg 0 (Sb 0 R w hR hw); have := mom_nonneg 4 (Sb (-R) 0 w (by linarith) hw)
    positivity
  have e1 : Real.arccos (rho0 L) / π ≤ 1 / (2 * π * L) := by
    rw [div_le_iff₀ hπ]
    calc Real.arccos (rho0 L) ≤ 1 / (2 * L) := harc
      _ = 1 / (2 * π * L) * π := by field_simp
  calc _ ≤ _ := hup
    _ ≤ 1 / (2 * π * L) + 4 * w / √(2 * π) + 4 / R ^ 2 + 2 * CqU R w * (32 / lam L ^ j) := by
        have := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 2 * CqU R w)
        linarith

lemma hm_le (hL : 1 ≤ L) (j : ℕ) :
    (gx L (j + 1) - gx L j) / (1 - gx L j) ≤ 1 / L := by
  have hs := lam_pow_ge_one hL j
  have hl := lam_gt hL
  have e1 : gx L (j + 1) - gx L j = (1 - gx L j) - (1 - gx L (j + 1)) := by ring
  rw [e1, one_sub_gx hL, one_sub_gx hL, pow_succ]
  set s := lam L ^ j
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hlam : lam L - 1 = 1 / L := by unfold lam; ring
  have key : (2 / (s + 1) - 2 / (s * lam L + 1)) / (2 / (s + 1))
      = (s * lam L - s) / (s * lam L + 1) := by
    field_simp; ring
  rw [key, ← hlam, div_le_iff₀ (by positivity)]
  have h1 : 0 ≤ lam L - 1 := by linarith
  have h2 : 0 ≤ s * lam L + 1 - s := by nlinarith
  nlinarith [mul_nonneg h1 h2]

lemma geom_ratio_le {x : ℝ} (h0 : 0 ≤ x) {L : ℕ} (hL : 2 ≤ L) (hx : x ≤ 1 / L) (k : ℕ) :
    x ^ k / (1 - x) ^ (k + 1) ≤ 2 / ((L : ℝ) - 1) ^ k := by
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hx1 : x ≤ 1 / 2 := hx.trans (by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
  have h1x : 0 < 1 - x := by linarith
  -- `x / (1 - x) ≤ 1 / (L - 1)` and `1 / (1 - x) ≤ 2`
  have hq : x / (1 - x) ≤ 1 / ((L : ℝ) - 1) := by
    rw [div_le_div_iff₀ h1x (by linarith)]
    have : x * L ≤ 1 := by rw [le_div_iff₀ (by linarith)] at hx; linarith
    nlinarith
  have h2 : 1 / (1 - x) ≤ 2 := by rw [div_le_iff₀ h1x]; linarith
  have e : x ^ k / (1 - x) ^ (k + 1) = (x / (1 - x)) ^ k * (1 / (1 - x)) := by
    rw [div_pow, pow_succ]; field_simp
  rw [e]
  have hq0 : 0 ≤ x / (1 - x) := div_nonneg h0 h1x.le
  have hL1 : (0 : ℝ) < (L : ℝ) - 1 := by linarith
  calc (x / (1 - x)) ^ k * (1 / (1 - x)) ≤ (1 / ((L : ℝ) - 1)) ^ k * 2 :=
        mul_le_mul (pow_le_pow_left₀ hq0 hq k) h2 (by positivity) (by positivity)
    _ = 2 / ((L : ℝ) - 1) ^ k := by rw [div_pow, one_pow]; ring

/-- **Many roots in one window are unlikely.** -/
theorem win_N_tail (hL : 2 ≤ L) {j : ℕ} (hjn : lam L ^ j ≤ n) (k : ℕ) {A : ℝ} (hA : 0 < A) :
    PP (fun ε : Fin (n + 1) → ℤˣ => k ≤ nIn (poly ε) (Set.Icc (gx L j) (gx L (j + 1))))
      ≤ 1 / A ^ 2 + 6 * A / ((L : ℝ) - 1) ^ k + 4 / √(lam L ^ j) := by
  have hL1 : 1 ≤ L := by omega
  set c := gx L j
  set h := gx L (j + 1) - gx L j with hh
  have hc0 := gx_nonneg hL1 j
  have hc1 := gx_lt_one hL1 j
  have hh0 : 0 ≤ h := by have := gx_lt_succ hL1 j; simp only [hh]; linarith
  have hs := lam_pow_ge_one hL1 j
  set m := 1 / (1 - c) with hm
  have h1c : 0 < 1 - c := by linarith
  have hm0 : 0 < m := by positivity
  have hmval : m = (lam L ^ j + 1) / 2 := by rw [hm, one_sub_gx hL1]; field_simp
  set μ : ℕ → ℝ := fun l => m ^ l * √m with hμ
  have hμ0 : ∀ l, 0 < μ l := fun l => by positivity
  have hD : ∀ l, ∑ i : Fin (n + 1), (((i : ℕ).choose l : ℝ) * c ^ ((i : ℕ) - l)) ^ 2 ≤ μ l ^ 2 := by
    intro l
    refine (hasse_moment_le l hc0 hc1).trans (le_of_eq ?_)
    show 1 / (1 - c) ^ (2 * l + 1) = (m ^ l * √m) ^ 2
    rw [mul_pow, Real.sq_sqrt hm0.le, ← pow_mul, ← pow_succ, hm, one_div_pow, mul_comm l 2]
  have hT := win_tail (n := n) hc0 hc1 hh0 k μ hμ0 hD hA
  rw [show c + h = gx L (j + 1) by simp only [c, hh]; ring] at hT
  refine hT.trans ?_
  -- the moment sum
  set r := h / (1 - c) with hr
  have hr0 : 0 ≤ r := div_nonneg hh0 h1c.le
  have hr1 : r ≤ 1 / L := hm_le hL1 j
  have hrlt : r < 1 := hr1.trans_lt (by
    rw [div_lt_one (by exact_mod_cast (show 0 < L by omega))]; exact_mod_cast (show 1 < L by omega))
  have hM : h ^ k * ∑ i ∈ range (n + 1), ((k + i).choose i : ℝ) * h ^ i * μ (k + i)
      ≤ √m * (2 / ((L : ℝ) - 1) ^ k) := by
    have e1 : ∀ i, ((k + i).choose i : ℝ) * h ^ i * μ (k + i)
        = m ^ k * √m * (((i + k).choose k : ℝ) * r ^ i) := by
      intro i
      have hc : (k + i).choose i = (i + k).choose k := by rw [add_comm k i]; exact Nat.choose_symm_add
      simp only [μ, hr, hm]
      rw [hc, pow_add, div_pow (h) (1 - c) i]
      field_simp
      rw [mul_assoc, ← mul_pow, one_div_mul_cancel h1c.ne', one_pow, mul_one]
    simp_rw [e1]
    rw [← Finset.mul_sum]
    have hnb := negbin_le k (n + 1) hr0 hrlt
    have hkm : h ^ k * m ^ k = r ^ k := by
      simp only [hr, hm]; rw [← mul_pow]; congr 1; field_simp
    calc h ^ k * (m ^ k * √m * ∑ i ∈ range (n + 1), ((i + k).choose k : ℝ) * r ^ i)
        = √m * (r ^ k * ∑ i ∈ range (n + 1), ((i + k).choose k : ℝ) * r ^ i) := by
          rw [← hkm]; ring
      _ ≤ √m * (r ^ k * (1 / (1 - r) ^ (k + 1))) := by gcongr
      _ = √m * (r ^ k / (1 - r) ^ (k + 1)) := by ring
      _ ≤ √m * (2 / ((L : ℝ) - 1) ^ k) :=
          mul_le_mul_of_nonneg_left (geom_ratio_le hr0 hL hr1 k) (Real.sqrt_nonneg _)
  -- the small-ball denominator
  have hmin : min ((n : ℝ) + 1) (1 / (2 * (1 - c))) = m / 2 := by
    have : 1 / (2 * (1 - c)) = m / 2 := by rw [hm]; field_simp
    rw [this]; apply min_eq_right; rw [hmval]; linarith
  rw [hmin]
  have hsq : √(m / 2) = √m / √2 := Real.sqrt_div' m (by norm_num)
  rw [hsq]
  have hsm : 0 < √m := Real.sqrt_pos.2 hm0
  have hs2 : (1 : ℝ) < √2 := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs2' : √2 < 3 / 2 := by
    rw [show (3 / 2 : ℝ) = √((3 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hLk : (0 : ℝ) < ((L : ℝ) - 1) ^ k := by
    have : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
    positivity
  have hmlam : √(lam L ^ j) ≤ √2 * √m := by
    rw [← Real.sqrt_mul (by norm_num)]; apply Real.sqrt_le_sqrt; rw [hmval]; linarith
  have hlj : 0 < √(lam L ^ j) := Real.sqrt_pos.2 (by positivity)
  -- assemble
  have key : (2 * (A * (h ^ k * ∑ i ∈ range (n + 1), ((k + i).choose i : ℝ) * h ^ i * μ (k + i))) + 2)
      / (√m / √2) ≤ 6 * A / ((L : ℝ) - 1) ^ k + 4 / √(lam L ^ j) := by
    rw [div_le_iff₀ (by positivity)]
    have hA2 : 2 * (A * (h ^ k * ∑ i ∈ range (n + 1), ((k + i).choose i : ℝ) * h ^ i * μ (k + i)))
        ≤ 2 * (A * (√m * (2 / ((L : ℝ) - 1) ^ k))) := by gcongr
    have t1 : 2 * (A * (√m * (2 / ((L : ℝ) - 1) ^ k))) ≤ 6 * A / ((L : ℝ) - 1) ^ k * (√m / √2) := by
      rw [show 6 * A / ((L : ℝ) - 1) ^ k * (√m / √2) = (6 / √2) * (A * √m / ((L : ℝ) - 1) ^ k) by
        field_simp]
      rw [show 2 * (A * (√m * (2 / ((L : ℝ) - 1) ^ k))) = 4 * (A * √m / ((L : ℝ) - 1) ^ k) by
        field_simp; ring]
      have hpos : 0 ≤ A * √m / ((L : ℝ) - 1) ^ k := by positivity
      have : (4 : ℝ) ≤ 6 / √2 := by rw [le_div_iff₀ (by linarith)]; linarith
      nlinarith
    have t2 : (2 : ℝ) ≤ 4 / √(lam L ^ j) * (√m / √2) := by
      rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right hmlam (Real.sqrt_nonneg 2)
      have h22 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
      have e : √2 * √m * √2 = 2 * √m := by rw [mul_comm (√2) (√m), mul_assoc, h22]; ring
      linarith
    have : (2 * (A * (h ^ k * ∑ i ∈ range (n + 1), ((k + i).choose i : ℝ) * h ^ i * μ (k + i))) + 2)
        = 2 * (A * (h ^ k * ∑ i ∈ range (n + 1), ((k + i).choose i : ℝ) * h ^ i * μ (k + i))) + 2 := rfl
    nlinarith
  have e2 : 2 * (A * h ^ k * ∑ i ∈ range (n + 1), ((k + i).choose i : ℝ) * h ^ i * μ (k + i)) + 2
      = 2 * (A * (h ^ k * ∑ i ∈ range (n + 1), ((k + i).choose i : ℝ) * h ^ i * μ (k + i))) + 2 := by ring
  rw [e2]
  linarith

/-! ### Root counts on unions of intervals -/

lemma nIn_mono (p : ℝ[X]) {I J : Set ℝ} (h : I ⊆ J) : nIn p I ≤ nIn p J := by
  classical
  rw [nIn_def, nIn_def]
  exact Multiset.card_le_card (Multiset.monotone_filter_right _ (fun x hx => h hx))

lemma nIn_union_le (p : ℝ[X]) (I J : Set ℝ) : nIn p (I ∪ J) ≤ nIn p I + nIn p J := by
  classical
  rw [nIn_def, nIn_def, nIn_def]
  have := Multiset.filter_add_filter (· ∈ I) (· ∈ J) p.roots
  have h2 := congrArg Multiset.card this
  rw [Multiset.card_add, Multiset.card_add] at h2
  have : Multiset.card (p.roots.filter (· ∈ I ∪ J)) = Multiset.card (p.roots.filter (fun x => x ∈ I ∨ x ∈ J)) := by
    rfl
  omega

lemma nIn_singleton_zero (p : ℝ[X]) (x : ℝ) (hx : p.eval x ≠ 0) : nIn p {x} = 0 := by
  classical
  rw [nIn_def, Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro y hy hyx
  rw [Set.mem_singleton_iff] at hyx; subst hyx
  have hp : p ≠ 0 := by rintro rfl; simp at hx
  exact hx ((mem_roots hp).1 hy)

lemma grid_eval_ne (hL : 1 ≤ L) {j : ℕ} (hj : 1 ≤ j) (ε : Fin (n + 1) → ℤˣ) :
    (poly ε).eval (gx L j) ≠ 0 := by
  obtain ⟨q, hq⟩ := gx_rat L j
  have h0 : (0 : ℝ) < q := by rw [hq]; exact gx_pos hL hj
  have h1 : (q : ℝ) < 1 := by rw [hq]; exact gx_lt_one hL j
  rw [← hq]
  exact poly_eval_rat_ne_zero ε q (by exact_mod_cast h0) (by exact_mod_cast h1)

/-- Decomposition of `(0, 1)` along the grid. -/
lemma decomp (hL : 1 ≤ L) (ε : Fin (n + 1) → ℤˣ) {j₀ J : ℕ} (hj₀ : 1 ≤ j₀) (hJ : j₀ ≤ J) :
    nIn (poly ε) (Set.Ioo 0 1) ≤ nIn (poly ε) (Set.Ioc 0 (gx L j₀))
      + ∑ j ∈ Ico j₀ J, nIn (poly ε) (Set.Ioo (gx L j) (gx L (j + 1)))
      + nIn (poly ε) (Set.Icc (gx L J) 1) := by
  -- first the part `(0, gx L J]`
  have hstep : ∀ J' : ℕ, j₀ ≤ J' → nIn (poly ε) (Set.Ioc 0 (gx L J')) ≤ nIn (poly ε) (Set.Ioc 0 (gx L j₀))
      + ∑ j ∈ Ico j₀ J', nIn (poly ε) (Set.Ioo (gx L j) (gx L (j + 1))) := by
    intro J' hJ'
    induction J', hJ' using Nat.le_induction with
    | base => simp
    | succ J' hJ' ih =>
      have hsub : Set.Ioc 0 (gx L (J' + 1)) ⊆ (Set.Ioc 0 (gx L J') ∪ Set.Ioo (gx L J') (gx L (J' + 1)))
          ∪ {gx L (J' + 1)} := by
        intro x hx
        by_cases h1 : x ≤ gx L J'
        · left; left; exact ⟨hx.1, h1⟩
        · by_cases h2 : x = gx L (J' + 1)
          · right; exact h2
          · left; right; exact ⟨lt_of_not_ge h1, lt_of_le_of_ne hx.2 h2⟩
      have := (nIn_mono (poly ε) hsub).trans ((nIn_union_le _ _ _).trans (add_le_add
        (nIn_union_le _ _ _) (le_of_eq (nIn_singleton_zero _ _ (grid_eval_ne hL (by omega) ε)))))
      rw [Finset.sum_Ico_succ_top hJ']
      omega
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioc 0 (gx L J) ∪ Set.Icc (gx L J) 1 := by
    intro x hx
    by_cases h : x ≤ gx L J
    · left; exact ⟨hx.1, h⟩
    · right; exact ⟨(lt_of_not_ge h).le, hx.2.le⟩
  have := (nIn_mono (poly ε) hsub).trans (nIn_union_le _ _ _)
  have := hstep J hJ
  omega

/-- Pointwise count: `N ≤ sc + 2 ∑_{k=2}^{T} 1{k ≤ N}` when `N ≤ T`. -/
lemma count_le (hL : 1 ≤ L) {j : ℕ} (hj : 1 ≤ j) (ε : Fin (n + 1) → ℤˣ) (T : ℕ)
    (hT : nIn (poly ε) (Set.Ioo (gx L j) (gx L (j + 1))) ≤ T) :
    (nIn (poly ε) (Set.Ioo (gx L j) (gx L (j + 1))) : ℝ)
      ≤ sc ε L j + 2 * ∑ k ∈ Icc 2 T,
          (if k ≤ nIn (poly ε) (Set.Icc (gx L j) (gx L (j + 1))) then (1 : ℝ) else 0) := by
  set N := nIn (poly ε) (Set.Ioo (gx L j) (gx L (j + 1)))
  set N' := nIn (poly ε) (Set.Icc (gx L j) (gx L (j + 1)))
  have hNN : N ≤ N' := nIn_mono _ Set.Ioo_subset_Icc_self
  have hsum : ∀ M : ℕ, M ≤ T → ((M : ℝ) - 1) ≤ ∑ k ∈ Icc 2 T, (if k ≤ M then (1 : ℝ) else 0) := by
    intro M hM
    rcases Nat.lt_or_ge M 2 with h | h
    · have : (M : ℝ) - 1 ≤ 0 := by
        have : (M : ℝ) ≤ 1 := by exact_mod_cast (show M ≤ 1 by omega)
        linarith
      exact this.trans (Finset.sum_nonneg (fun k _ => by split_ifs <;> norm_num))
    · have hsub : Icc 2 M ⊆ Icc 2 T := Finset.Icc_subset_Icc le_rfl hM
      calc ((M : ℝ) - 1) = ∑ _k ∈ Icc 2 M, (1 : ℝ) := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
            rw [show M + 1 - 2 = M - 1 by omega, Nat.cast_sub (by omega)]
            push_cast; ring
        _ = ∑ k ∈ Icc 2 M, (if k ≤ M then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl (fun k hk => ?_)
            rw [if_pos (Finset.mem_Icc.1 hk).2]
        _ ≤ ∑ k ∈ Icc 2 T, (if k ≤ M then (1 : ℝ) else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by split_ifs <;> norm_num)
  have hmono : ∑ k ∈ Icc 2 T, (if k ≤ N then (1 : ℝ) else 0)
      ≤ ∑ k ∈ Icc 2 T, (if k ≤ N' then (1 : ℝ) else 0) := by
    refine Finset.sum_le_sum (fun k _ => ?_)
    by_cases h : k ≤ N
    · rw [if_pos h, if_pos (h.trans hNN)]
    · rw [if_neg h]; split_ifs <;> norm_num
  have hsc0 := sc_nonneg ε L j
  rcases Nat.lt_or_ge N 2 with h | h
  · interval_cases hN : N
    · simp only [CharP.cast_eq_zero]
      have := Finset.sum_nonneg (s := Icc 2 T) (fun k (_ : k ∈ Icc 2 T) =>
        (by split_ifs <;> norm_num : (0 : ℝ) ≤ if k ≤ N' then 1 else 0))
      linarith
    · -- one simple root: a sign change
      have hsc : sc ε L j = 1 := by
        unfold sc
        rw [if_pos (simple_sign (gx_lt_succ hL j) (grid_eval_ne hL hj ε)
          (grid_eval_ne hL (by omega) ε) hN)]
      have := Finset.sum_nonneg (s := Icc 2 T) (fun k (_ : k ∈ Icc 2 T) =>
        (by split_ifs <;> norm_num : (0 : ℝ) ≤ if k ≤ N' then 1 else 0))
      rw [hsc]; push_cast; linarith
  · have h1 := hsum N hT
    have : (N : ℝ) ≤ 2 * ((N : ℝ) - 1) := by
      have : (2 : ℝ) ≤ N := by exact_mod_cast h
      linarith
    linarith

/-- An upper tail from a mean bound and a lower tail. -/
lemma tail_from_mean {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : (ι → ℤˣ) → ℝ) (hY : ∀ ε, 0 ≤ Y ε)
    {c a ℓ t : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (hℓ : 0 < ℓ) (ht : 0 < t)
    (hmean : EE Y ≤ (c + a) * ℓ) (hlow : PP (fun ε => Y ε ≤ (c - a) * ℓ) ≤ a) :
    PP (fun ε => (c + t) * ℓ ≤ Y ε) ≤ (2 + c) * a / t := by
  classical
  have hpt : ∀ ε, (c - a) * ℓ * (if (c - a) * ℓ < Y ε then 1 else 0)
      + (t + a) * ℓ * (if (c + t) * ℓ ≤ Y ε then 1 else 0) ≤ Y ε := by
    intro ε
    have hca : 0 ≤ (c - a) * ℓ := mul_nonneg (by linarith) hℓ.le
    split_ifs with h1 h2 h2
    · nlinarith
    · nlinarith
    · exfalso; have : (c - a) * ℓ < (c + t) * ℓ := by nlinarith
      linarith
    · simp only [mul_zero, add_zero]; exact hY ε
  have hE := EE_mono hpt
  rw [EE_add, EE_smul, EE_smul, ← PP_eq, ← PP_eq] at hE
  have hc : PP (fun ε => (c - a) * ℓ < Y ε) = 1 - PP (fun ε => Y ε ≤ (c - a) * ℓ) := by
    rw [← PP_compl]; congr 1; ext ε; simp [not_le]
  rw [hc] at hE
  set B := PP (fun ε => (c + t) * ℓ ≤ Y ε)
  set Lo := PP (fun ε => Y ε ≤ (c - a) * ℓ)
  have hB0 : 0 ≤ B := PP_nonneg _
  have key : (t + a) * B ≤ (c + a) - (c - a) * (1 - Lo) := by
    have : (c - a) * ℓ * (1 - Lo) + (t + a) * ℓ * B ≤ (c + a) * ℓ := hE.trans hmean
    have h' : ((c - a) * (1 - Lo) + (t + a) * B) * ℓ ≤ (c + a) * ℓ := by linarith
    have := le_of_mul_le_mul_right h' hℓ
    linarith
  have hLo : Lo ≤ a := hlow
  have : (c + a) - (c - a) * (1 - Lo) ≤ (2 + c) * a := by nlinarith
  rw [le_div_iff₀ ht]
  nlinarith

/-- **The last window.** -/
theorem end_tail (hL : 2 ≤ L) (hn : 1 ≤ n) (k : ℕ) {A : ℝ} (hA : 0 < A) :
    PP (fun ε : Fin (n + 1) → ℤˣ => k ≤ nIn (poly ε) (Set.Icc (gx L (Jn L n)) 1))
      ≤ 1 / A ^ 2 + 8 * A * 4 ^ k * Real.exp 4 / k.factorial + 6 / √n := by
  have hL1 : 1 ≤ L := by omega
  set J := Jn L n
  set c := gx L J
  set h := 1 - c with hh
  have hc0 := gx_nonneg hL1 J
  have hc1 := gx_lt_one hL1 J
  have hh0 : 0 < h := by simp only [hh]; linarith
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlJ := lt_lam_pow_Jn hL1 hn
  have hl2 := lam_le_two hL1
  have hl1 := lam_gt hL1
  have hJ0 : 0 < lam L ^ J := by positivity
  have hval : h = 2 / (lam L ^ J + 1) := by simp only [hh, c]; rw [one_sub_gx hL1]
  have hlJ' : (n : ℝ) / lam L < lam L ^ J := by
    rw [div_lt_iff₀ (by linarith)]; rw [pow_succ] at hlJ; linarith
  have hhn : h * n ≤ 4 := by
    rw [hval, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : (n : ℝ) ≤ lam L * lam L ^ J := by
      have := (div_lt_iff₀ (by linarith : (0 : ℝ) < lam L)).1 hlJ'; linarith
    nlinarith
  set μ : ℕ → ℝ := fun l => √((n : ℝ) + 1) * ((n : ℝ) ^ l / l.factorial) with hμ
  have hμ0 : ∀ l, 0 < μ l := fun l => by positivity
  have hD : ∀ l, ∑ i : Fin (n + 1), (((i : ℕ).choose l : ℝ) * c ^ ((i : ℕ) - l)) ^ 2 ≤ μ l ^ 2 := by
    intro l
    refine (hasse_moment_le' l hc0 hc1.le).trans (le_of_eq ?_)
    simp only [μ, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  have hT := win_tail (n := n) hc0 hc1 hh0.le k μ hμ0 hD hA
  rw [show c + h = 1 by simp only [hh]; ring] at hT
  refine hT.trans ?_
  have hM : h ^ k * ∑ i ∈ range (n + 1), ((k + i).choose i : ℝ) * h ^ i * μ (k + i)
      ≤ √((n : ℝ) + 1) * (4 ^ k * Real.exp 4 / k.factorial) := by
    have e1 : ∀ i, ((k + i).choose i : ℝ) * h ^ i * μ (k + i)
        = √((n : ℝ) + 1) * ((n : ℝ) ^ k / k.factorial) * ((h * n) ^ i / i.factorial) := by
      intro i
      have hf := Nat.choose_mul_factorial_mul_factorial (show i ≤ k + i by omega)
      rw [show k + i - i = k by omega] at hf
      have hf' : ((k + i).choose i : ℝ) * i.factorial * k.factorial = (k + i).factorial := by
        exact_mod_cast hf
      simp only [μ]
      rw [mul_pow, pow_add]
      field_simp
      rw [← hf']; ring
    simp_rw [e1]
    rw [← Finset.mul_sum]
    have hexp := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ h * n) (n + 1)
    have hk : h ^ k * (n : ℝ) ^ k = (h * n) ^ k := by rw [mul_pow]
    have hhk : (h * n) ^ k ≤ 4 ^ k := pow_le_pow_left₀ (by positivity) hhn k
    have he : Real.exp (h * n) ≤ Real.exp 4 := Real.exp_le_exp.2 hhn
    calc h ^ k * (√((n : ℝ) + 1) * ((n : ℝ) ^ k / k.factorial) *
          ∑ i ∈ range (n + 1), (h * n) ^ i / i.factorial)
        = √((n : ℝ) + 1) * ((h * n) ^ k / k.factorial) *
            ∑ i ∈ range (n + 1), (h * n) ^ i / i.factorial := by rw [← hk]; ring
      _ ≤ √((n : ℝ) + 1) * (4 ^ k / k.factorial) * Real.exp 4 := by
          gcongr
          exact hexp.trans he
      _ = _ := by ring
  have hmin : (n : ℝ) / 8 ≤ min ((n : ℝ) + 1) (1 / (2 * (1 - c))) := by
    apply le_min (by linarith)
    rw [show 1 - c = h by simp only [hh], hval]
    rw [show 1 / (2 * (2 / (lam L ^ J + 1))) = (lam L ^ J + 1) / 4 by field_simp; ring]
    have : (n : ℝ) / 2 ≤ (n : ℝ) / lam L := div_le_div_of_nonneg_left (by positivity) (by linarith) hl2
    linarith
  have hsq : √((n : ℝ) / 8) ≤ √(min ((n : ℝ) + 1) (1 / (2 * (1 - c)))) := Real.sqrt_le_sqrt hmin
  have hsq0 : 0 < √((n : ℝ) / 8) := Real.sqrt_pos.2 (by positivity)
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by positivity)
  -- `√(n+1) ≤ 4 √(n/8)` and `2 ≤ 6 √(n/8)/√n`
  have r1 : √((n : ℝ) + 1) ≤ 4 * √((n : ℝ) / 8) := by
    rw [show (4 : ℝ) * √((n : ℝ) / 8) = √(16 * ((n : ℝ) / 8)) by
      rw [Real.sqrt_mul (by norm_num), show √(16 : ℝ) = 4 by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    apply Real.sqrt_le_sqrt; linarith
  have r2 : (2 : ℝ) ≤ 6 / √n * √((n : ℝ) / 8) := by
    rw [Real.sqrt_div' _ (by norm_num), div_mul_div_comm, le_div_iff₀ (by positivity)]
    have h8 : √(8 : ℝ) < 3 := by
      rw [show (3 : ℝ) = √(3 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    nlinarith
  have hfac : (0 : ℝ) < k.factorial := by positivity
  set Q := 4 ^ k * Real.exp 4 / k.factorial
  have hQ0 : 0 ≤ Q := by positivity
  have hnum : 2 * (A * h ^ k * ∑ i ∈ range (n + 1), ((k + i).choose i : ℝ) * h ^ i * μ (k + i)) + 2
      ≤ 2 * (A * (4 * √((n : ℝ) / 8) * Q)) + 2 := by
    have := mul_le_mul_of_nonneg_left hM hA.le
    have h2 : √((n : ℝ) + 1) * Q ≤ 4 * √((n : ℝ) / 8) * Q := mul_le_mul_of_nonneg_right r1 hQ0
    nlinarith
  have hfin : (2 * (A * (4 * √((n : ℝ) / 8) * Q)) + 2) / √((n : ℝ) / 8) ≤ 8 * A * Q + 6 / √n := by
    rw [div_le_iff₀ hsq0]
    nlinarith
  have hQe : 8 * A * Q = 8 * A * 4 ^ k * Real.exp 4 / k.factorial := by simp only [Q]; ring
  calc 1 / A ^ 2 + (2 * (A * h ^ k * ∑ i ∈ range (n + 1), ((k + i).choose i : ℝ) * h ^ i * μ (k + i)) + 2)
        / √(min ((n : ℝ) + 1) (1 / (2 * (1 - c))))
      ≤ 1 / A ^ 2 + (2 * (A * (4 * √((n : ℝ) / 8) * Q)) + 2) / √((n : ℝ) / 8) := by
        gcongr
    _ ≤ 1 / A ^ 2 + (8 * A * Q + 6 / √n) := by gcongr
    _ = _ := by rw [hQe]; ring

end R522

end S_RR9

-- ===== RR10 =====

/-!
# Erdős 522 (real roots), part 10: the upper bound, pieces

* `Jn_le`: `J ≤ (L + 1) log n`.
* `ES_le`: the mean number of grid sign changes.
* `EX_le`: the mean of the multiple-root excess.
* `PG1_le`: some window has more than `T` roots: small.
-/

open Finset Real Polynomial Filter

noncomputable section S_RR10

namespace R522

variable {n L : ℕ}

lemma log_lam_ge (hL : 1 ≤ L) : 1 / ((L : ℝ) + 1) ≤ Real.log (lam L) := by
  have hl := lam_gt hL
  have h := Real.log_le_sub_one_of_pos (inv_pos.2 (by linarith : (0 : ℝ) < lam L))
  rw [Real.log_inv] at h
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have e : (lam L)⁻¹ - 1 = -(1 / ((L : ℝ) + 1)) := by unfold lam; field_simp; ring
  linarith

lemma Jn_le (hL : 1 ≤ L) (hn : 1 ≤ n) : (Jn L n : ℝ) ≤ ((L : ℝ) + 1) * Real.log n := by
  have hlog := log_lam_ge hL
  have hpos : 0 < Real.log (lam L) := Real.log_pos (lam_gt hL)
  have h0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  unfold Jn
  refine (Nat.floor_le (div_nonneg h0 hpos.le)).trans ?_
  rw [div_le_iff₀ hpos]
  have : (1 : ℝ) ≤ ((L : ℝ) + 1) * Real.log (lam L) := by
    rw [div_le_iff₀ (by positivity)] at hlog; linarith
  nlinarith

lemma geom_inv_le (hL : 1 ≤ L) (j₀ J : ℕ) :
    ∑ j ∈ Ico j₀ J, 1 / lam L ^ j ≤ (L : ℝ) + 1 := by
  have hl := lam_gt hL
  have hθ0 : 0 ≤ 1 / lam L := by positivity
  have hθ1 : 1 / lam L < 1 := by rw [div_lt_one (by linarith)]; exact hl
  have := geom_sum_Ico_le_of_lt_one (m := j₀) (n := J) hθ0 hθ1
  simp_rw [one_div_pow] at this
  refine this.trans ?_
  have h1 : 1 / lam L ^ j₀ ≤ 1 := by rw [← one_div_pow]; exact pow_le_one₀ hθ0 hθ1.le
  have h2 : 1 - 1 / lam L = 1 / ((L : ℝ) + 1) := by
    unfold lam; have : (0 : ℝ) < L := by exact_mod_cast hL
    field_simp; ring
  rw [h2]
  rw [div_le_iff₀ (by positivity)]
  have : (0 : ℝ) < L := by exact_mod_cast hL
  calc 1 / lam L ^ j₀ ≤ 1 := h1
    _ = ((L : ℝ) + 1) * (1 / ((L : ℝ) + 1)) := by field_simp

/-- The grid points used by the windows lie below `n`. -/
lemma lam_pow_le_n (hL : 1 ≤ L) (hn : 1 ≤ n) {j : ℕ} (hj : j < Jn L n) : lam L ^ j ≤ n :=
  (pow_le_pow_right₀ (lam_gt hL).le hj.le).trans (lam_pow_Jn_le hL hn)

lemma EE_sc (ε₀ : Unit) (L j : ℕ) :
    EE (fun ε : Fin (n + 1) → ℤˣ => sc ε L j)
      = PP (fun ε : Fin (n + 1) → ℤˣ => (poly ε).eval (gx L j) * (poly ε).eval (gx L (j + 1)) < 0) := by
  rw [PP_eq]; rfl

/-- **Mean number of grid sign changes.** -/
theorem ES_le (hL : 2 ≤ L) (hn : 1 ≤ n) {j₀ : ℕ} (hj₀ : 1 ≤ j₀) :
    EE (fun ε : Fin (n + 1) → ℤˣ => ∑ j ∈ Ico j₀ (Jn L n), sc ε L j)
      ≤ ((L : ℝ) + 1) * Real.log n * (1 / (2 * π * L) + 1 / (L : ℝ) ^ 2)
        + 64 * CqU (4 * L) (1 / (8 * (L : ℝ) ^ 2)) * ((L : ℝ) + 1) := by
  have hL1 : 1 ≤ L := by omega
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL1
  set R : ℝ := 4 * L
  set w : ℝ := 1 / (8 * (L : ℝ) ^ 2)
  have hR : 0 < R := by positivity
  have hw : 0 < w := by positivity
  have hC : 0 ≤ CqU R w := by
    unfold CqU; rw [dif_pos ⟨hR, hw⟩]; unfold Cq
    have := mom_nonneg 4 (Sb 0 R w hR hw); have := mom_nonneg 0 (Sb (-R) 0 w (by linarith) hw)
    have := mom_nonneg 0 (Sb 0 R w hR hw); have := mom_nonneg 4 (Sb (-R) 0 w (by linarith) hw)
    positivity
  have hsmall : 4 * w / √(2 * π) + 4 / R ^ 2 ≤ 1 / (L : ℝ) ^ 2 := by
    have hs : (1 : ℝ) ≤ √(2 * π) := by
      rw [Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
    have h1 : 4 * w / √(2 * π) ≤ 4 * w := div_le_self (by positivity) hs
    have h2 : 4 * w = 1 / (2 * (L : ℝ) ^ 2) := by simp only [w]; field_simp; ring
    have h3 : 4 / R ^ 2 = 1 / (4 * (L : ℝ) ^ 2) := by simp only [R]; field_simp
    have h4 : 1 / (2 * (L : ℝ) ^ 2) + 1 / (4 * (L : ℝ) ^ 2) ≤ 1 / (L : ℝ) ^ 2 := by
      field_simp; nlinarith
    linarith
  rw [EE_sum]
  have hwin : ∀ j ∈ Ico j₀ (Jn L n), EE (fun ε : Fin (n + 1) → ℤˣ => sc ε L j)
      ≤ (1 / (2 * π * L) + 1 / (L : ℝ) ^ 2) + 64 * CqU R w * (1 / lam L ^ j) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [EE_sc ()]
    have := sc_prob_le (n := n) hL hn (by omega) (lam_pow_le_n hL1 hn hj.2) hR hw
    have e : 2 * CqU R w * (32 / lam L ^ j) = 64 * CqU R w * (1 / lam L ^ j) := by ring
    linarith
  refine (Finset.sum_le_sum hwin).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  have hcard : ((Ico j₀ (Jn L n)).card : ℝ) ≤ ((L : ℝ) + 1) * Real.log n := by
    rw [Nat.card_Ico]
    refine le_trans ?_ (Jn_le hL1 hn)
    exact_mod_cast Nat.sub_le _ _
  have hg := geom_inv_le hL1 j₀ (Jn L n)
  have hpos : 0 ≤ 1 / (2 * π * L) + 1 / (L : ℝ) ^ 2 := by positivity
  gcongr

lemma sqrt_pow' {x : ℝ} (hx : 0 ≤ x) (j : ℕ) : √(x ^ j) = √x ^ j := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg x) j), ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt hx]

lemma geom_isqrt_le (hL : 1 ≤ L) (j₀ J : ℕ) :
    ∑ j ∈ Ico j₀ J, 1 / √(lam L ^ j) ≤ 6 * L / √(lam L ^ j₀) := by
  have hl := lam_gt hL
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hsq1 : 1 < √(lam L) := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) hl
  set θ := 1 / √(lam L)
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 := by rw [div_lt_one (by linarith)]; exact hsq1
  have e : ∀ j, 1 / √(lam L ^ j) = θ ^ j := by
    intro j; rw [sqrt_pow' (by linarith), one_div_pow]
  simp_rw [e]
  refine (geom_sum_Ico_le_of_lt_one hθ0 hθ1).trans ?_
  -- `1 - θ ≥ 1/(6L)`
  have hsq2 : √(lam L) ≤ 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith [lam_le_two hL])
  have hk : √(lam L) - 1 ≥ (lam L - 1) / 3 := by
    have h1 : (√(lam L) - 1) * (√(lam L) + 1) = lam L - 1 := by
      rw [show (√(lam L) - 1) * (√(lam L) + 1) = √(lam L) ^ 2 - 1 by ring, Real.sq_sqrt (by linarith)]
    rw [ge_iff_le, div_le_iff₀ (by norm_num)]
    nlinarith
  have hlam1 : lam L - 1 = 1 / L := by unfold lam; ring
  have h1θ : 1 / (6 * L) ≤ 1 - θ := by
    have : 1 - θ = (√(lam L) - 1) / √(lam L) := by simp only [θ]; field_simp
    rw [this, le_div_iff₀ (by linarith)]
    rw [hlam1] at hk
    have : 1 / (6 * (L : ℝ)) * √(lam L) ≤ 1 / (6 * L) * 2 := by gcongr
    have e2 : 1 / (6 * (L : ℝ)) * 2 = 1 / L / 3 := by field_simp; ring
    linarith
  have hpow : θ ^ j₀ = 1 / √(lam L ^ j₀) := (e j₀).symm
  have hinv : 1 / (1 - θ) ≤ 6 * L := by
    rw [div_le_iff₀ (by linarith)]
    have : (6 * (L : ℝ)) * (1 / (6 * L)) = 1 := by field_simp
    nlinarith
  calc θ ^ j₀ / (1 - θ) = θ ^ j₀ * (1 / (1 - θ)) := by ring
    _ ≤ θ ^ j₀ * (6 * L) := by gcongr
    _ = 6 * L / √(lam L ^ j₀) := by rw [hpow]; ring

/-- The cube root used to optimize the window tail bounds. -/
def Bc (L : ℕ) : ℝ := ((L : ℝ) - 1) ^ ((3 : ℕ)⁻¹ : ℝ)

lemma Bc_cube (hL : 1 ≤ L) : Bc L ^ 3 = (L : ℝ) - 1 := by
  unfold Bc
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have : (0 : ℝ) ≤ (L : ℝ) - 1 := by linarith
  exact Real.rpow_inv_natCast_pow this (by norm_num)

lemma Bc_pos (hL : 2 ≤ L) : 0 < Bc L := by
  unfold Bc
  have h1 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have : (0 : ℝ) < (L : ℝ) - 1 := by linarith
  exact Real.rpow_pos_of_pos this _

/-- The excess counted by `count_le`. -/
def Xc (ε : Fin (n + 1) → ℤˣ) (L j₀ T : ℕ) : ℝ :=
  2 * ∑ j ∈ Ico j₀ (Jn L n), ∑ k ∈ Icc 2 T,
    (if k ≤ nIn (poly ε) (Set.Icc (gx L j) (gx L (j + 1))) then (1 : ℝ) else 0)

lemma Xc_nonneg (ε : Fin (n + 1) → ℤˣ) (L j₀ T : ℕ) : 0 ≤ Xc ε L j₀ T := by
  unfold Xc
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => by
    split_ifs <;> norm_num)))

/-- **Mean excess.** -/
theorem EX_le (hL : 2 ≤ L) (hn : 1 ≤ n) (hB : 2 ≤ Bc L ^ 2) (j₀ T : ℕ) :
    EE (fun ε : Fin (n + 1) → ℤˣ => Xc ε L j₀ T)
      ≤ 28 * ((L : ℝ) + 1) * Real.log n / Bc L ^ 4 + 48 * L * T := by
  have hL1 : 1 ≤ L := by omega
  set B := Bc L
  have hB0 : 0 < B := Bc_pos hL
  have hB3 : B ^ 3 = (L : ℝ) - 1 := Bc_cube hL1
  -- per (j, k)
  have hjk : ∀ j ∈ Ico j₀ (Jn L n), ∀ k ∈ Icc 2 T,
      PP (fun ε : Fin (n + 1) → ℤˣ => k ≤ nIn (poly ε) (Set.Icc (gx L j) (gx L (j + 1))))
        ≤ 7 * (1 / B ^ 2) ^ k + 4 / √(lam L ^ j) := by
    intro j hj k hk
    have := win_N_tail (n := n) hL (lam_pow_le_n hL1 hn (Finset.mem_Ico.1 hj).2) k
      (A := B ^ k) (by positivity)
    have e1 : 1 / (B ^ k) ^ 2 = (1 / B ^ 2) ^ k := by rw [one_div_pow, ← pow_mul, ← pow_mul, mul_comm]
    have e2 : 6 * B ^ k / ((L : ℝ) - 1) ^ k = 6 * (1 / B ^ 2) ^ k := by
      rw [← hB3, ← pow_mul, one_div_pow, ← pow_mul]
      field_simp
      ring
    rw [e1, e2] at this
    linarith
  unfold Xc
  rw [EE_smul, EE_sum]
  have hq0 : 0 ≤ 1 / B ^ 2 := by positivity
  have hq : 1 / B ^ 2 ≤ 1 / 2 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hksum : ∑ k ∈ Icc 2 T, 7 * (1 / B ^ 2) ^ k ≤ 14 / B ^ 4 := by
    rw [← Finset.mul_sum]
    have hsub : Icc 2 T ⊆ Ico 2 (T + 1) := by intro k hk; simp at hk ⊢; omega
    have := geom_sum_Ico_le_of_lt_one (m := 2) (n := T + 1) hq0 (by linarith)
    have h2 : ∑ k ∈ Icc 2 T, (1 / B ^ 2) ^ k ≤ ∑ k ∈ Ico 2 (T + 1), (1 / B ^ 2) ^ k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have h3 : (1 / B ^ 2) ^ 2 / (1 - 1 / B ^ 2) ≤ 2 / B ^ 4 := by
      rw [div_le_div_iff₀ (by linarith) (by positivity)]
      rw [one_div_pow, ← pow_mul]
      have : (1 : ℝ) / B ^ 4 * B ^ 4 = 1 := by field_simp
      nlinarith
    calc 7 * ∑ k ∈ Icc 2 T, (1 / B ^ 2) ^ k ≤ 7 * (2 / B ^ 4) := by
          have := h2.trans (this.trans h3); linarith
      _ = 14 / B ^ 4 := by ring
  have hj : ∀ j ∈ Ico j₀ (Jn L n), EE (fun ε : Fin (n + 1) → ℤˣ => ∑ k ∈ Icc 2 T,
      (if k ≤ nIn (poly ε) (Set.Icc (gx L j) (gx L (j + 1))) then (1 : ℝ) else 0))
      ≤ 14 / B ^ 4 + T * (4 / √(lam L ^ j)) := by
    intro j hjm
    rw [EE_sum]
    calc ∑ k ∈ Icc 2 T, EE (fun ε : Fin (n + 1) → ℤˣ =>
          if k ≤ nIn (poly ε) (Set.Icc (gx L j) (gx L (j + 1))) then (1 : ℝ) else 0)
        = ∑ k ∈ Icc 2 T, PP (fun ε : Fin (n + 1) → ℤˣ =>
            k ≤ nIn (poly ε) (Set.Icc (gx L j) (gx L (j + 1)))) := by
          refine Finset.sum_congr rfl (fun k _ => ?_); rw [PP_eq]
      _ ≤ ∑ k ∈ Icc 2 T, (7 * (1 / B ^ 2) ^ k + 4 / √(lam L ^ j)) :=
          Finset.sum_le_sum (fun k hk => hjk j hjm k hk)
      _ ≤ 14 / B ^ 4 + T * (4 / √(lam L ^ j)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          have : ((T + 1 - 2 : ℕ) : ℝ) ≤ T := by exact_mod_cast (show T + 1 - 2 ≤ T by omega)
          have h4 : 0 ≤ 4 / √(lam L ^ j) := by positivity
          nlinarith
  have hsum := Finset.sum_le_sum hj
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hcard : ((Ico j₀ (Jn L n)).card : ℝ) ≤ ((L : ℝ) + 1) * Real.log n := by
    rw [Nat.card_Ico]; exact le_trans (by exact_mod_cast Nat.sub_le _ _) (Jn_le hL1 hn)
  have hg := geom_isqrt_le hL1 j₀ (Jn L n)
  have hgs : ∑ j ∈ Ico j₀ (Jn L n), 1 / √(lam L ^ j) ≤ 6 * L := by
    refine hg.trans ?_
    rw [div_le_iff₀ (Real.sqrt_pos.2 (by have := lam_gt hL1; positivity))]
    have : 1 ≤ √(lam L ^ j₀) := by rw [Real.one_le_sqrt]; exact lam_pow_ge_one hL1 j₀
    have : (0 : ℝ) ≤ 6 * L := by positivity
    nlinarith
  have e4 : ∑ j ∈ Ico j₀ (Jn L n), 4 / √(lam L ^ j) = 4 * ∑ j ∈ Ico j₀ (Jn L n), 1 / √(lam L ^ j) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by ring)
  rw [e4] at hsum
  have hB4 : 0 < B ^ 4 := by positivity
  have hT0 : (0 : ℝ) ≤ T := by positivity
  have h14 : ((Ico j₀ (Jn L n)).card : ℝ) * (14 / B ^ 4) ≤ ((L : ℝ) + 1) * Real.log n * (14 / B ^ 4) :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  have hT4 : (T : ℝ) * (4 * ∑ j ∈ Ico j₀ (Jn L n), 1 / √(lam L ^ j)) ≤ T * (4 * (6 * L)) := by gcongr
  have e5 : 28 * ((L : ℝ) + 1) * Real.log n / B ^ 4 = 2 * (((L : ℝ) + 1) * Real.log n * (14 / B ^ 4)) := by
    ring
  rw [e5]
  nlinarith

/-- **Some window has many roots: unlikely.** -/
theorem PG1_le (hL : 2 ≤ L) (hn : 1 ≤ n) (j₀ T : ℕ) {A : ℝ} (hA : 0 < A) :
    PP (fun ε : Fin (n + 1) → ℤˣ => ∃ j ∈ Ico j₀ (Jn L n),
        T + 1 ≤ nIn (poly ε) (Set.Icc (gx L j) (gx L (j + 1))))
      ≤ ((L : ℝ) + 1) * Real.log n * (1 / A ^ 2 + 6 * A / ((L : ℝ) - 1) ^ (T + 1))
        + 24 * L / √(lam L ^ j₀) := by
  have hL1 : 1 ≤ L := by omega
  refine (PP_exists_le _ _).trans ?_
  have hwin : ∀ j ∈ Ico j₀ (Jn L n), PP (fun ε : Fin (n + 1) → ℤˣ =>
      T + 1 ≤ nIn (poly ε) (Set.Icc (gx L j) (gx L (j + 1))))
      ≤ (1 / A ^ 2 + 6 * A / ((L : ℝ) - 1) ^ (T + 1)) + 4 * (1 / √(lam L ^ j)) := by
    intro j hj
    have := win_N_tail (n := n) hL (lam_pow_le_n hL1 hn (Finset.mem_Ico.1 hj).2) (T + 1) hA
    have e : 4 * (1 / √(lam L ^ j)) = 4 / √(lam L ^ j) := by ring
    linarith
  refine (Finset.sum_le_sum hwin).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  have hcard : ((Ico j₀ (Jn L n)).card : ℝ) ≤ ((L : ℝ) + 1) * Real.log n := by
    rw [Nat.card_Ico]; exact le_trans (by exact_mod_cast Nat.sub_le _ _) (Jn_le hL1 hn)
  have hg := geom_isqrt_le hL1 j₀ (Jn L n)
  have hp : 0 ≤ 1 / A ^ 2 + 6 * A / ((L : ℝ) - 1) ^ (T + 1) := by
    have : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
    positivity
  have e : 24 * (L : ℝ) / √(lam L ^ j₀) = 4 * (6 * L / √(lam L ^ j₀)) := by ring
  rw [e]
  gcongr

end R522

end S_RR10

-- ===== RRB =====

/-!
# Erdős 522 (real roots): the low region

Deterministic bound on the roots of a `±1` polynomial in `(0, r]`: with `0 < r < R < 1`,
`(R / r)^N ≤ 1 / (1 - R)`. Proof by the real Blaschke trick: replacing each factor `X - x` (root
`x ∈ (0, r]`) by `R - (x / R) X` keeps the modulus on the circle `|z| = R`, and the maximum
modulus principle at `0` gives the bound, since `|p(0)| = 1`.
-/

open Finset Real Polynomial

noncomputable section S_RRB

namespace R522

lemma norm_fac (R x : ℝ) (hR : 0 < R) (z : ℂ) (hz : ‖z‖ = R) :
    ‖(R : ℂ) - ((x / R : ℝ) : ℂ) * z‖ = ‖z - (x : ℂ)‖ := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hzz : z * (starRingEnd ℂ) z = (R : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; push_cast; ring
  have h1 : (R : ℂ) - ((x / R : ℝ) : ℂ) * z = (z / R) * ((starRingEnd ℂ) z - x) := by
    have : (z / R) * ((starRingEnd ℂ) z - x) = (z * (starRingEnd ℂ) z) / R - x / R * z := by ring
    rw [this, hzz]; push_cast; field_simp
  rw [h1, norm_mul, norm_div, hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
    div_self hR.ne', one_mul]
  have : (starRingEnd ℂ) z - (x : ℂ) = (starRingEnd ℂ) (z - x) := by simp
  rw [this, Complex.norm_conj]

lemma norm_prod_map (S : Multiset ℝ) (g : ℝ → ℂ) :
    ‖(S.map g).prod‖ = (S.map fun x => ‖g x‖).prod := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih => rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons,
      norm_mul, ih]

lemma norm_prod_fac (S : Multiset ℝ) (R : ℝ) (hR : 0 < R) (z : ℂ) (hz : ‖z‖ = R) :
    ‖(S.map fun x : ℝ => (R : ℂ) - ((x / R : ℝ) : ℂ) * z).prod‖ = ‖(S.map fun x : ℝ => z - (x : ℂ)).prod‖ := by
  rw [norm_prod_map, norm_prod_map]
  congr 1
  exact Multiset.map_congr rfl (fun x _ => norm_fac R x hR z hz)

lemma norm_unit_complex (u : ℤˣ) : ‖(((u : ℤ) : ℝ) : ℂ)‖ = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

lemma geom_le_inv {R : ℝ} (h0 : 0 ≤ R) (h1 : R < 1) (m : ℕ) :
    ∑ i ∈ Finset.range m, R ^ i ≤ 1 / (1 - R) := by
  rw [le_div_iff₀ (by linarith), mul_comm, mul_neg_geom_sum]
  have : 0 ≤ R ^ m := pow_nonneg h0 m
  linarith

/-- **Low-region bound.** -/
theorem low_bound {n : ℕ} (ε : Fin (n + 1) → ℤˣ) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hR : R < 1) : (R / r) ^ nIn (poly ε) (Set.Ioc 0 r) ≤ 1 / (1 - R) := by
  classical
  have hR0 : 0 < R := hr.trans hrR
  have hp := poly_ne_zero ε
  set S := (poly ε).roots.filter (· ∈ Set.Ioc 0 r) with hS
  have hN : nIn (poly ε) (Set.Ioc 0 r) = Multiset.card S := nIn_def _ _
  have hSI : ∀ x ∈ S, x ∈ Set.Ioc 0 r := fun x hx => (Multiset.mem_filter.1 hx).2
  obtain ⟨G, hG⟩ := (Multiset.prod_X_sub_C_dvd_iff_le_roots hp S).2 (Multiset.filter_le _ _)
  set Gc := G.map Complex.ofRealHom
  set pc := (poly ε).map Complex.ofRealHom
  set Qc : ℂ[X] := (S.map fun x : ℝ => C (R : ℂ) - C ((x / R : ℝ) : ℂ) * X).prod * Gc with hQc
  have evp : ∀ z, pc.eval z = (S.map fun x : ℝ => z - (x : ℂ)).prod * Gc.eval z := by
    intro z
    rw [show pc = ((poly ε).map Complex.ofRealHom) from rfl, hG, Polynomial.map_mul,
      Polynomial.map_multiset_prod, Multiset.map_map, eval_mul, eval_multiset_prod, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl (fun x _ => ?_)
    simp
  have evQ : ∀ z, Qc.eval z = (S.map fun x : ℝ => (R : ℂ) - ((x / R : ℝ) : ℂ) * z).prod * Gc.eval z := by
    intro z
    rw [hQc, eval_mul, eval_multiset_prod, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl (fun x _ => ?_)
    simp
  have evsum : ∀ z, pc.eval z = ∑ i : Fin (n + 1), (((ε i : ℤ) : ℝ) : ℂ) * z ^ (i : ℕ) := by
    intro z
    simp only [pc, poly, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X,
      eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rfl
  have hbd : ∀ z : ℂ, ‖z‖ = R → ‖Qc.eval z‖ ≤ 1 / (1 - R) := by
    intro z hz
    rw [evQ, norm_mul, norm_prod_fac S R hR0 z hz, ← norm_mul, ← evp, evsum]
    calc ‖∑ i : Fin (n + 1), (((ε i : ℤ) : ℝ) : ℂ) * z ^ (i : ℕ)‖
        ≤ ∑ i : Fin (n + 1), ‖(((ε i : ℤ) : ℝ) : ℂ) * z ^ (i : ℕ)‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range (n + 1), R ^ i := by
          rw [← Fin.sum_univ_eq_sum_range (fun i => R ^ i)]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [norm_mul, norm_pow, hz, norm_unit_complex, one_mul]
      _ ≤ 1 / (1 - R) := geom_le_inv hR0.le hR _
  have h0 : ‖Qc.eval 0‖ ≤ 1 / (1 - R) := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball (0 : ℂ) R)
      Metric.isBounded_ball (Qc.differentiable.diffContOnCl) (fun z hz => ?_)
      (subset_closure (Metric.mem_ball_self hR0))
    rw [frontier_ball (0 : ℂ) hR0.ne'] at hz
    exact hbd z (by simpa using hz)
  have hp0 : ‖pc.eval 0‖ = 1 := by
    rw [evsum, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, ne_eq, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero, add_zero]
    exact norm_unit_complex _
  -- `‖G(0)‖ ≥ 1 / r^N`
  have hG0 : 1 ≤ r ^ Multiset.card S * ‖Gc.eval 0‖ := by
    rw [← hp0, evp, norm_mul, norm_prod_map]
    gcongr
    refine prod_map_le_pow S _ r (fun x _ => norm_nonneg _) (fun x hx => ?_)
    have := hSI x hx
    rw [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos this.1]
    exact this.2
  have hQ0 : ‖Qc.eval 0‖ = R ^ Multiset.card S * ‖Gc.eval 0‖ := by
    rw [evQ, norm_mul, norm_prod_map]
    congr 1
    have : (S.map fun x : ℝ => ‖(R : ℂ) - ((x / R : ℝ) : ℂ) * 0‖) = S.map fun _ => R := by
      refine Multiset.map_congr rfl (fun x _ => ?_)
      rw [mul_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    rw [this, Multiset.map_const', Multiset.prod_replicate]
  rw [hN, div_pow]
  have hrN : 0 < r ^ Multiset.card S := pow_pos hr _
  calc R ^ Multiset.card S / r ^ Multiset.card S
      ≤ R ^ Multiset.card S * ‖Gc.eval 0‖ := by
        rw [div_le_iff₀ hrN]
        have := mul_le_mul_of_nonneg_left hG0 (pow_nonneg hR0.le (Multiset.card S))
        linarith
    _ = ‖Qc.eval 0‖ := hQ0.symm
    _ ≤ 1 / (1 - R) := h0

/-- Corollary: a bound on the number of roots in `(0, r]`. -/
theorem low_bound_log {n : ℕ} (ε : Fin (n + 1) → ℤˣ) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hR : R < 1) :
    (nIn (poly ε) (Set.Ioc 0 r) : ℝ) ≤ Real.log (1 / (1 - R)) / Real.log (R / r) := by
  have h := low_bound ε hr hrR hR
  have hRr : 1 < R / r := by rw [one_lt_div hr]; exact hrR
  have hl : 0 < Real.log (R / r) := Real.log_pos hRr
  rw [le_div_iff₀ hl, ← Real.log_pow]
  exact Real.log_le_log (pow_pos (by linarith) _) h

end R522

end S_RRB

-- ===== RR11 =====

/-!
# Erdős 522 (real roots), part 11: the upper bound

From the lower bound for grid sign changes (`LowSC`, proved separately) we get
`P(N(0,1) ≥ (1/(2π) + η) log n) ≤ η` eventually.
-/

open Finset Real Polynomial Filter

noncomputable section S_RR11

namespace R522

/-- The lower bound for grid sign changes. -/
def LowSC : Prop := ∀ η : ℝ, 0 < η → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ ja : ℕ, ∀ᶠ n : ℕ in atTop,
  PP (ι := Fin (n + 1)) (fun ε => ∑ j ∈ Ico ja (Jn L n), sc ε L j ≤ (1 / (2 * π) - η) * Real.log n) ≤ η

lemma le_Jn (hL : 1 ≤ L) {n j : ℕ} (hn : 1 ≤ n) (h : lam L ^ j ≤ n) : j ≤ Jn L n := by
  have hl := lam_gt hL
  have hlog : 0 < Real.log (lam L) := Real.log_pos hl
  unfold Jn
  apply Nat.le_floor
  rw [le_div_iff₀ hlog, ← Real.log_pow]
  exact Real.log_le_log (by positivity) h

lemma ev_log_ge (M : ℝ) : ∀ᶠ n : ℕ in atTop, M ≤ Real.log n :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop M

lemma ev_floor_sqrt_log_ge (M : ℕ) : ∀ᶠ n : ℕ in atTop, M ≤ ⌊√(Real.log n)⌋₊ :=
  ((tendsto_nat_floor_atTop).comp (Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually_ge_atTop M

/-- The deterministic low-region bound at a grid point. -/
lemma low_region (hL : 1 ≤ L) {j₀ : ℕ} (hj₀ : 1 ≤ j₀) {n : ℕ} (ε : Fin (n + 1) → ℤˣ) :
    (nIn (poly ε) (Set.Ioc 0 (gx L j₀)) : ℝ)
      ≤ Real.log (1 / (1 - (1 + gx L j₀) / 2)) / Real.log ((1 + gx L j₀) / 2 / gx L j₀) := by
  have h0 := gx_pos hL hj₀
  have h1 := gx_lt_one hL j₀
  exact low_bound_log ε h0 (by linarith) (by linarith)

lemma pi_bounds : (1 : ℝ) / (2 * π) ≤ 1 / 6 := by
  have := Real.pi_gt_three
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith

lemma ev_pow_div_two_pow (C δ : ℝ) (hδ : 0 < δ) :
    ∃ M : ℕ, ∀ m ≥ M, C * ((m : ℝ) + 1) ^ 3 / 2 ^ (m + 1) ≤ δ := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 3 (r := (2 : ℝ)) (by norm_num)
  have h2 : Tendsto (fun m : ℕ => C * (((m + 1 : ℕ) : ℝ) ^ 3 / 2 ^ (m + 1))) atTop (nhds (C * 0)) :=
    (h.comp (tendsto_add_atTop_nat 1)).const_mul C
  rw [mul_zero] at h2
  obtain ⟨M, hM⟩ := (h2.eventually (ge_mem_nhds hδ)).exists_forall_of_atTop
  refine ⟨M, fun m hm => ?_⟩
  have := hM m hm
  simp only [Function.comp, Nat.cast_add, Nat.cast_one] at this
  rw [mul_div_assoc]; exact this

lemma exists_fact_small (δ : ℝ) (hδ : 0 < δ) : ∃ k : ℕ, (4 : ℝ) ^ k / k.factorial ≤ δ := by
  have h := FloorSemiring.tendsto_pow_div_factorial_atTop (4 : ℝ)
  obtain ⟨k, hk⟩ := (h.eventually (ge_mem_nhds hδ)).exists
  exact ⟨k, hk⟩

lemma exists_pow_large (hL : 1 ≤ L) (M : ℝ) : ∃ j : ℕ, M ≤ √(lam L ^ j) := by
  have h : Tendsto (fun j : ℕ => lam L ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (lam_gt hL)
  obtain ⟨j, hj⟩ := ((Real.tendsto_sqrt_atTop.comp h).eventually_ge_atTop M).exists
  exact ⟨j, hj⟩

/-! ### Numeric side lemmas -/

lemma num_ES {L c a : ℝ} (hL : 1 ≤ L) (hc0 : 0 < c) (hc6 : c ≤ 1 / 6) (ha : 0 < a)
    (hLa : 6 / a ≤ L) : (L + 1) * (c / L + 1 / L ^ 2) ≤ c + a / 2 := by
  have hLp : 0 < L := by linarith
  have e1 : (L + 1) * (c / L) = c + c / L := by field_simp
  have e2 : (L + 1) * (1 / L ^ 2) ≤ 2 / L := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hLp]; nlinarith
  have e3 : c / L + 2 / L ≤ a / 2 := by
    rw [← add_div, div_le_iff₀ hLp]
    have : 6 ≤ a * L := by rw [div_le_iff₀ ha] at hLa; linarith
    nlinarith
  nlinarith

lemma num_K {K a ℓ : ℝ} (ha : 0 < a) (h : 2 * |K| / a + 1 ≤ ℓ) : K ≤ a / 2 * ℓ := by
  have h1 : 2 * |K| / a ≤ ℓ := by linarith
  rw [div_le_iff₀ ha] at h1
  have := le_abs_self K
  nlinarith

lemma num_Sb {η c : ℝ} (hη : 0 < η) (hη1 : η < 1) (hc6 : c ≤ 1 / 6) (hc0 : 0 < c) :
    (2 + c) * (η ^ 2 / 40) / (η / 2) ≤ η / 8 := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma num_48 {L η ℓ T : ℝ} (hL : 0 ≤ L) (hη : 0 < η) (hℓ : 0 < ℓ) (hT0 : 0 ≤ T) (hT : T ≤ √ℓ)
    (h : (1536 * L / η ^ 2) ^ 2 + 1 ≤ ℓ) : 48 * L * T ≤ η ^ 2 / 32 * ℓ := by
  have hsq : 1536 * L / η ^ 2 ≤ √ℓ := by
    rw [Real.le_sqrt (by positivity) hℓ.le]; linarith
  have hsl : √ℓ * √ℓ = ℓ := Real.mul_self_sqrt hℓ.le
  have h1 : 1536 * L ≤ η ^ 2 * √ℓ := by rw [div_le_iff₀ (by positivity)] at hsq; linarith
  have h2 : 48 * L * T ≤ 48 * L * √ℓ := by gcongr
  have h3 : 48 * L * √ℓ * 32 ≤ η ^ 2 * √ℓ * √ℓ := by nlinarith [Real.sqrt_nonneg ℓ]
  nlinarith

lemma num_G1 {L ℓ η A K T : ℝ} (hL : 3 ≤ L) (hℓ : 0 < ℓ) (hη : 0 < η) (hT0 : 0 ≤ T)
    (hA : A = √(64 * (L + 1) * ℓ / η)) (hK : K = 6 * (L + 1) * √(64 * (L + 1) / η))
    (hT1 : √ℓ < T + 1) {m : ℕ} (hm : (m : ℝ) = T)
    (hKb : K * (T + 1) ^ 3 / 2 ^ (m + 1) ≤ η / 16) :
    (L + 1) * ℓ * (1 / A ^ 2 + 6 * A / (L - 1) ^ (m + 1)) ≤ η / 64 + η / 16 := by
  have hA0 : 0 < A := by rw [hA]; exact Real.sqrt_pos.2 (by positivity)
  have hA1sq : A ^ 2 = 64 * (L + 1) * ℓ / η := by rw [hA]; exact Real.sq_sqrt (by positivity)
  have t1 : (L + 1) * ℓ * (1 / A ^ 2) = η / 64 := by rw [hA1sq]; field_simp
  have hℓT : ℓ ≤ (T + 1) ^ 2 := by
    have := Real.sq_sqrt hℓ.le
    nlinarith [Real.sqrt_nonneg ℓ]
  have hA1T : A ≤ √(64 * (L + 1) / η) * (T + 1) := by
    rw [hA, show 64 * (L + 1) * ℓ / η = 64 * (L + 1) / η * ℓ by ring, Real.sqrt_mul (by positivity)]
    gcongr
  have hpow : (2 : ℝ) ^ (m + 1) ≤ (L - 1) ^ (m + 1) := pow_le_pow_left₀ (by norm_num) (by linarith) _
  have hnum : (L + 1) * ℓ * (6 * A) ≤ K * (T + 1) ^ 3 := by
    rw [hK]
    have h1 := mul_le_mul hℓT hA1T hA0.le (by positivity)
    have h2 : 0 ≤ √(64 * (L + 1) / η) := Real.sqrt_nonneg _
    nlinarith
  have t2 : (L + 1) * ℓ * (6 * A / (L - 1) ^ (m + 1)) ≤ η / 16 := by
    calc (L + 1) * ℓ * (6 * A / (L - 1) ^ (m + 1)) = (L + 1) * ℓ * (6 * A) / (L - 1) ^ (m + 1) := by ring
      _ ≤ K * (T + 1) ^ 3 / 2 ^ (m + 1) := div_le_div₀ (by rw [hK]; positivity) hnum (by positivity) hpow
      _ ≤ η / 16 := hKb
  rw [mul_add, t1]
  linarith

/-- The per-`n` combination. -/
theorem upper_n {n L j₀ T kₑ : ℕ} (hL : 1 ≤ L) (hj₀ : 1 ≤ j₀) (hJ : j₀ ≤ Jn L n) {η a ℓ : ℝ}
    (hη : 0 < η) (hℓ : ℓ = Real.log n) (hℓ0 : 0 < ℓ) (ha0 : 0 ≤ a) (hac : a ≤ 1 / (2 * π))
    (hSb : (2 + 1 / (2 * π)) * a / (η / 2) ≤ η / 8)
    (hlowS : PP (ι := Fin (n + 1)) (fun ε => ∑ j ∈ Ico j₀ (Jn L n), sc ε L j ≤ (1 / (2 * π) - a) * ℓ) ≤ a)
    (hES : EE (ι := Fin (n + 1)) (fun ε => ∑ j ∈ Ico j₀ (Jn L n), sc ε L j) ≤ (1 / (2 * π) + a) * ℓ)
    (hEX : EE (ι := Fin (n + 1)) (fun ε => Xc ε L j₀ T) ≤ η ^ 2 / 16 * ℓ)
    (hG1 : PP (ι := Fin (n + 1)) (fun ε => ∃ j ∈ Ico j₀ (Jn L n),
        T + 1 ≤ nIn (poly ε) (Set.Icc (gx L j) (gx L (j + 1)))) ≤ 9 * η / 64)
    (hG2 : PP (ι := Fin (n + 1)) (fun ε => kₑ ≤ nIn (poly ε) (Set.Icc (gx L (Jn L n)) 1)) ≤ η / 16)
    (hC : Real.log (1 / (1 - (1 + gx L j₀) / 2)) / Real.log ((1 + gx L j₀) / 2 / gx L j₀) + kₑ
      ≤ η / 4 * ℓ) :
    PP (ι := Fin (n + 1)) (fun ε => (1 / (2 * π) + η) * ℓ ≤ (nIn (poly ε) (Set.Ioo 0 1) : ℝ)) ≤ η := by
  set c := 1 / (2 * π)
  have hc0 : 0 < c := by positivity
  set S : (Fin (n + 1) → ℤˣ) → ℝ := fun ε => ∑ j ∈ Ico j₀ (Jn L n), sc ε L j with hSdef
  set X : (Fin (n + 1) → ℤˣ) → ℝ := fun ε => Xc ε L j₀ T with hXdef
  have hS0 : ∀ ε, 0 ≤ S ε := fun ε => Finset.sum_nonneg (fun j _ => sc_nonneg ε L j)
  have hStail := tail_from_mean S hS0 ha0 hac hℓ0 (t := η / 2) (by linarith) hES hlowS
  have hXtail : PP (fun ε => η / 4 * ℓ ≤ X ε) ≤ η / 4 := by
    refine (markov (f := X) (fun ε => Xc_nonneg ε L j₀ T) (by positivity)).trans ?_
    rw [div_le_iff₀ (by positivity)]
    have : η ^ 2 / 16 * ℓ = η / 4 * (η / 4 * ℓ) := by ring
    linarith
  have hincl : ∀ ε : Fin (n + 1) → ℤˣ, (c + η) * ℓ ≤ (nIn (poly ε) (Set.Ioo 0 1) : ℝ) →
      ((∃ j ∈ Ico j₀ (Jn L n), T + 1 ≤ nIn (poly ε) (Set.Icc (gx L j) (gx L (j + 1)))) ∨
        kₑ ≤ nIn (poly ε) (Set.Icc (gx L (Jn L n)) 1)) ∨
      ((c + η / 2) * ℓ ≤ S ε ∨ η / 4 * ℓ ≤ X ε) := by
    intro ε hN
    by_contra hcon
    simp only [not_or, not_exists, not_and, not_le] at hcon
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hcon
    have hwin : ∀ j ∈ Ico j₀ (Jn L n), (nIn (poly ε) (Set.Ioo (gx L j) (gx L (j + 1))) : ℝ)
        ≤ sc ε L j + 2 * ∑ k ∈ Icc 2 T,
          (if k ≤ nIn (poly ε) (Set.Icc (gx L j) (gx L (j + 1))) then (1 : ℝ) else 0) := by
      intro j hj
      have hjj : 1 ≤ j := le_trans hj₀ (Finset.mem_Ico.1 hj).1
      refine count_le hL hjj ε T ?_
      have := h1 j hj
      exact (nIn_mono _ Set.Ioo_subset_Icc_self).trans (by omega)
    have hsumw := Finset.sum_le_sum hwin
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsumw
    have hdec := decomp hL ε hj₀ hJ
    have hdec' : (nIn (poly ε) (Set.Ioo 0 1) : ℝ) ≤ nIn (poly ε) (Set.Ioc 0 (gx L j₀))
        + ∑ j ∈ Ico j₀ (Jn L n), (nIn (poly ε) (Set.Ioo (gx L j) (gx L (j + 1))) : ℝ)
        + nIn (poly ε) (Set.Icc (gx L (Jn L n)) 1) := by exact_mod_cast hdec
    have hlowr := low_region hL hj₀ ε
    have hend : (nIn (poly ε) (Set.Icc (gx L (Jn L n)) 1) : ℝ) ≤ kₑ := by exact_mod_cast h2.le
    have hX' : X ε = 2 * ∑ j ∈ Ico j₀ (Jn L n), ∑ k ∈ Icc 2 T,
        (if k ≤ nIn (poly ε) (Set.Icc (gx L j) (gx L (j + 1))) then (1 : ℝ) else 0) := rfl
    have hS' : S ε = ∑ j ∈ Ico j₀ (Jn L n), sc ε L j := rfl
    linarith
  calc PP (fun ε : Fin (n + 1) → ℤˣ => (c + η) * ℓ ≤ (nIn (poly ε) (Set.Ioo 0 1) : ℝ))
      ≤ PP (fun ε : Fin (n + 1) → ℤˣ =>
          ((∃ j ∈ Ico j₀ (Jn L n), T + 1 ≤ nIn (poly ε) (Set.Icc (gx L j) (gx L (j + 1)))) ∨
            kₑ ≤ nIn (poly ε) (Set.Icc (gx L (Jn L n)) 1)) ∨
          ((c + η / 2) * ℓ ≤ S ε ∨ η / 4 * ℓ ≤ X ε)) := PP_mono hincl
    _ ≤ (PP (fun ε : Fin (n + 1) → ℤˣ => ∃ j ∈ Ico j₀ (Jn L n),
            T + 1 ≤ nIn (poly ε) (Set.Icc (gx L j) (gx L (j + 1))))
          + PP (fun ε : Fin (n + 1) → ℤˣ => kₑ ≤ nIn (poly ε) (Set.Icc (gx L (Jn L n)) 1)))
        + (PP (fun ε => (c + η / 2) * ℓ ≤ S ε) + PP (fun ε => η / 4 * ℓ ≤ X ε)) :=
        (PP_or_le _ _).trans (add_le_add (PP_or_le _ _) (PP_or_le _ _))
    _ ≤ (9 * η / 64 + η / 16) + (η / 8 + η / 4) := by
        gcongr
        exact hStail.trans hSb
    _ ≤ η := by linarith

lemma num_G2 {η : ℝ} (hη : 0 < η) (hη1 : η < 1) {k : ℕ}
    (hk : (4 : ℝ) ^ k / k.factorial ≤ η / (64 * 8 * (16 / η) * Real.exp 4 * 4)) {n : ℕ}
    (hn : (6 * 64 / η) ^ 2 ≤ n) :
    1 / (16 / η) ^ 2 + 8 * (16 / η) * 4 ^ k * Real.exp 4 / k.factorial + 6 / √n ≤ η / 16 := by
  have hA : 0 < 16 / η := by positivity
  have t1 : 1 / (16 / η) ^ 2 ≤ η / 64 := by
    rw [div_pow, one_div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have t2 : 8 * (16 / η) * 4 ^ k * Real.exp 4 / k.factorial ≤ η / 256 := by
    have : 8 * (16 / η) * 4 ^ k * Real.exp 4 / k.factorial
        = 8 * (16 / η) * Real.exp 4 * (4 ^ k / k.factorial) := by ring
    rw [this]
    calc 8 * (16 / η) * Real.exp 4 * (4 ^ k / k.factorial)
        ≤ 8 * (16 / η) * Real.exp 4 * (η / (64 * 8 * (16 / η) * Real.exp 4 * 4)) := by gcongr
      _ = η / 256 := by field_simp; ring
  have t3 : 6 / √n ≤ η / 64 := by
    have hs : 6 * 64 / η ≤ √n := by rw [Real.le_sqrt (by positivity) (by positivity)]; exact hn
    have hpos : 0 < √(n : ℝ) := lt_of_lt_of_le (by positivity) hs
    rw [div_le_div_iff₀ hpos (by norm_num)]
    rw [div_le_iff₀ hη] at hs
    nlinarith
  linarith

/-- **The upper bound.** -/
theorem upper (hlow : LowSC) (η : ℝ) (hη : 0 < η) : ∀ᶠ n : ℕ in atTop,
    PP (ι := Fin (n + 1)) (fun ε => (1 / (2 * π) + η) * Real.log n ≤ (nIn (poly ε) (Set.Ioo 0 1) : ℝ))
      ≤ η := by
  by_cases hη1 : 1 ≤ η
  · exact Filter.Eventually.of_forall (fun n => (PP_le_one _).trans hη1)
  push Not at hη1
  have hc0 : 0 < 1 / (2 * π) := by positivity
  have hc6 : 1 / (2 * π) ≤ 1 / 6 := pi_bounds
  set a : ℝ := η ^ 2 / 40 with ha
  have ha0 : 0 < a := by positivity
  have hac : a ≤ 1 / (2 * π) := by
    have : a ≤ 1 / 40 := by simp only [ha]; nlinarith
    have : (1 : ℝ) / 40 ≤ 1 / (2 * π) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith [Real.pi_lt_four]
    linarith
  obtain ⟨L₀, hL₀⟩ := hlow a ha0
  set L : ℕ := max L₀ (⌈6 / a⌉₊ + ⌈(2688 / η ^ 2) ^ 3⌉₊ + 10) with hLdef
  have hmax := le_max_right L₀ (⌈6 / a⌉₊ + ⌈(2688 / η ^ 2) ^ 3⌉₊ + 10)
  have hLL₀ : L₀ ≤ L := le_max_left _ _
  have hL10 : 10 ≤ L := by omega
  have hL2 : 2 ≤ L := by omega
  have hL1 : 1 ≤ L := by omega
  have hLr : (10 : ℝ) ≤ L := by exact_mod_cast hL10
  have hLa : 6 / a ≤ L := by
    have h1 := Nat.le_ceil (6 / a)
    have h2 : ⌈6 / a⌉₊ ≤ L := by omega
    exact h1.trans (by exact_mod_cast h2)
  have hLb : (2688 / η ^ 2) ^ 3 ≤ (L : ℝ) - 1 := by
    have h1 := Nat.le_ceil ((2688 / η ^ 2) ^ 3)
    have h2 : ⌈(2688 / η ^ 2) ^ 3⌉₊ + 1 ≤ L := by omega
    have : ((⌈(2688 / η ^ 2) ^ 3⌉₊ : ℕ) : ℝ) + 1 ≤ L := by exact_mod_cast h2
    linarith
  set B := Bc L
  have hB0 : 0 < B := Bc_pos hL2
  have hB3 : B ^ 3 = (L : ℝ) - 1 := Bc_cube hL1
  have hBX : 2688 / η ^ 2 ≤ B := by
    have : (2688 / η ^ 2) ^ 3 ≤ B ^ 3 := by rw [hB3]; exact hLb
    exact le_of_pow_le_pow_left₀ (by norm_num) hB0.le this
  have hB2 : 2 ≤ B ^ 2 := by
    have : (2 : ℝ) ≤ 2688 / η ^ 2 := by rw [le_div_iff₀ (by positivity)]; nlinarith
    nlinarith
  have hLB : 28 * ((L : ℝ) + 1) / B ^ 4 ≤ η ^ 2 / 32 := by
    have h4 : B ^ 4 = ((L : ℝ) - 1) * B := by rw [← hB3]; ring
    rw [h4, div_le_div_iff₀ (by nlinarith) (by norm_num)]
    have : 2688 ≤ η ^ 2 * B := by rw [div_le_iff₀ (by positivity)] at hBX; linarith
    nlinarith
  obtain ⟨j₁, hj₁⟩ := exists_pow_large hL1 (24 * L * 16 / η)
  set j₀ := j₁ + 1
  have hj₀ : 1 ≤ j₀ := by omega
  have hj₀big : 24 * (L : ℝ) / √(lam L ^ j₀) ≤ η / 16 := by
    have hmono : √(lam L ^ j₁) ≤ √(lam L ^ j₀) :=
      Real.sqrt_le_sqrt (pow_le_pow_right₀ (lam_gt hL1).le (by omega))
    have hpos : 0 < √(lam L ^ j₀) := Real.sqrt_pos.2 (by have := lam_gt hL1; positivity)
    rw [div_le_div_iff₀ hpos (by norm_num)]
    have : 24 * L * 16 / η * η = 24 * L * 16 := by field_simp
    nlinarith
  obtain ⟨kₑ, hkₑ⟩ := exists_fact_small (η / (64 * 8 * (16 / η) * Real.exp 4 * 4)) (by positivity)
  set Clow := Real.log (1 / (1 - (1 + gx L j₀) / 2)) / Real.log ((1 + gx L j₀) / 2 / gx L j₀)
  set K₁ := 64 * CqU (4 * L) (1 / (8 * (L : ℝ) ^ 2)) * ((L : ℝ) + 1)
  set K₂ := 6 * ((L : ℝ) + 1) * √(64 * ((L : ℝ) + 1) / η)
  obtain ⟨M₂, hM₂⟩ := ev_pow_div_two_pow K₂ (η / 16) (by positivity)
  filter_upwards [Filter.eventually_ge_atTop 1, Filter.eventually_ge_atTop ⌈lam L ^ j₀⌉₊,
    hL₀ L hLL₀ j₀, ev_log_ge (2 * |K₁| / a + 1), ev_log_ge ((1536 * L / η ^ 2) ^ 2 + 1),
    ev_floor_sqrt_log_ge M₂, ev_log_ge ((Clow + kₑ) * 4 / η + 1),
    Filter.eventually_ge_atTop (⌈(6 * 64 / η) ^ 2⌉₊ + 1)] with n hn1 hnj hlow' hlogK hlogT hT hlogC hnbig
  have hK₁ : 0 ≤ 2 * |K₁| / a := by positivity
  have hℓ0 : 0 < Real.log n := by linarith
  have hJ : j₀ ≤ Jn L n := le_Jn hL1 hn1 ((Nat.le_ceil _).trans (by exact_mod_cast hnj))
  set T := ⌊√(Real.log n)⌋₊ with hTdef
  -- the mean of `S`
  have hES : EE (ι := Fin (n + 1)) (fun ε => ∑ j ∈ Ico j₀ (Jn L n), sc ε L j)
      ≤ (1 / (2 * π) + a) * Real.log n := by
    have h := ES_le (n := n) hL2 hn1 hj₀
    have hnum := num_ES (L := (L : ℝ)) (by linarith) hc0 hc6 ha0 hLa
    have e : 1 / (2 * π * L) = 1 / (2 * π) / L := by field_simp
    rw [e] at h
    have hK := num_K (K := K₁) ha0 hlogK
    have : ((L : ℝ) + 1) * Real.log n * (1 / (2 * π) / L + 1 / (L : ℝ) ^ 2)
        ≤ (1 / (2 * π) + a / 2) * Real.log n := by
      rw [show ((L : ℝ) + 1) * Real.log n * (1 / (2 * π) / L + 1 / (L : ℝ) ^ 2)
          = ((L : ℝ) + 1) * (1 / (2 * π) / L + 1 / (L : ℝ) ^ 2) * Real.log n by ring]
      exact mul_le_mul_of_nonneg_right hnum hℓ0.le
    linarith
  -- the mean of the excess
  have hEX : EE (ι := Fin (n + 1)) (fun ε => Xc ε L j₀ T) ≤ η ^ 2 / 16 * Real.log n := by
    have h := EX_le (n := n) hL2 hn1 hB2 j₀ T
    have h48 := num_48 (L := (L : ℝ)) (T := (T : ℝ)) (by positivity) hη hℓ0 (by positivity)
      (Nat.floor_le (Real.sqrt_nonneg _)) hlogT
    have h28 : 28 * ((L : ℝ) + 1) * Real.log n / B ^ 4 ≤ η ^ 2 / 32 * Real.log n := by
      rw [show 28 * ((L : ℝ) + 1) * Real.log n / B ^ 4 = 28 * ((L : ℝ) + 1) / B ^ 4 * Real.log n by ring]
      exact mul_le_mul_of_nonneg_right hLB hℓ0.le
    linarith
  -- many roots in one window
  have hG1 : PP (ι := Fin (n + 1)) (fun ε => ∃ j ∈ Ico j₀ (Jn L n),
      T + 1 ≤ nIn (poly ε) (Set.Icc (gx L j) (gx L (j + 1)))) ≤ 9 * η / 64 := by
    set A₁ := √(64 * ((L : ℝ) + 1) * Real.log n / η)
    have hA₁ : 0 < A₁ := Real.sqrt_pos.2 (by positivity)
    have h := PG1_le (n := n) hL2 hn1 j₀ T hA₁
    have hnum := num_G1 (L := (L : ℝ)) (ℓ := Real.log n) (η := η) (A := A₁) (K := K₂) (T := (T : ℝ))
      (by linarith) hℓ0 hη (by positivity) rfl rfl (Nat.lt_floor_add_one _) (m := T) rfl (hM₂ T hT)
    linarith
  -- the end window
  have hG2 : PP (ι := Fin (n + 1)) (fun ε => kₑ ≤ nIn (poly ε) (Set.Icc (gx L (Jn L n)) 1)) ≤ η / 16 := by
    have h := end_tail (n := n) hL2 hn1 kₑ (A := 16 / η) (by positivity)
    have hnb : (6 * 64 / η) ^ 2 ≤ n := by
      have := Nat.le_ceil ((6 * 64 / η) ^ 2)
      have : ((⌈(6 * 64 / η) ^ 2⌉₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hnbig
      linarith
    have := num_G2 hη hη1 hkₑ hnb
    linarith
  have hC : Clow + kₑ ≤ η / 4 * Real.log n := by
    have : (Clow + kₑ) * 4 / η ≤ Real.log n := by linarith
    rw [div_le_iff₀ hη] at this; linarith
  exact upper_n hL1 hj₀ hJ hη rfl hℓ0 ha0.le hac (by simpa [ha] using num_Sb hη hη1 hc6 hc0)
    hlow' hES hEX hG1 hG2 hC

end R522

end S_RR11

-- ===== RRT =====

/-!
# Erdős 522 (real roots): symmetries, transfer, final assembly

* `alt`, `rev`: sign-vector symmetries (`x ↦ -x`, `x ↦ 1/x`); `PP` is invariant under equivalences.
* Root bookkeeping with multiplicity: the four interval counts and the total.
* Roots at `±1` are rare (Littlewood–Offord).
-/

open Finset Real Polynomial

noncomputable section S_RRT

namespace R522

/-! ### Equivalences -/

lemma PP_equiv {ι : Type*} [Fintype ι] [DecidableEq ι] (e : (ι → ℤˣ) ≃ (ι → ℤˣ))
    (S : (ι → ℤˣ) → Prop) : PP (fun ε => S (e ε)) = PP S := by
  classical
  unfold PP EE
  congr 1
  exact Equiv.sum_comp e (fun ε => if S ε then (1 : ℝ) else 0)

/-- Reversal of the coefficients. -/
def rev {n : ℕ} (ε : Fin (n + 1) → ℤˣ) : Fin (n + 1) → ℤˣ := fun i => ε (Fin.rev i)

/-- Alternating signs. -/
def alt {n : ℕ} (ε : Fin (n + 1) → ℤˣ) : Fin (n + 1) → ℤˣ := fun i => (-1) ^ (i : ℕ) * ε i

lemma rev_rev {n : ℕ} (ε : Fin (n + 1) → ℤˣ) : rev (rev ε) = ε := by
  funext i; simp [rev]

lemma alt_alt {n : ℕ} (ε : Fin (n + 1) → ℤˣ) : alt (alt ε) = ε := by
  funext i; simp only [alt, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp

def revE (n : ℕ) : (Fin (n + 1) → ℤˣ) ≃ (Fin (n + 1) → ℤˣ) :=
  ⟨rev, rev, rev_rev, rev_rev⟩

def altE (n : ℕ) : (Fin (n + 1) → ℤˣ) ≃ (Fin (n + 1) → ℤˣ) :=
  ⟨alt, alt, alt_alt, alt_alt⟩

/-! ### The polynomial: degree, symmetries -/

lemma poly_natDegree {n : ℕ} (ε : Fin (n + 1) → ℤˣ) : (poly ε).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [poly_coeff, dif_neg (by omega)]
  · rw [poly_coeff, dif_pos (by omega)]
    exact unit_ne_zero _

lemma poly_coeff_zero {n : ℕ} (ε : Fin (n + 1) → ℤˣ) : (poly ε).coeff 0 ≠ 0 := by
  rw [poly_coeff, dif_pos (by omega)]; exact unit_ne_zero _

lemma poly_rev {n : ℕ} (ε : Fin (n + 1) → ℤˣ) : poly (rev ε) = reverse (poly ε) := by
  ext j
  rw [coeff_reverse, poly_natDegree, poly_coeff, poly_coeff]
  by_cases hj : j ≤ n
  · rw [revAt_le hj, dif_pos (by omega), dif_pos (by omega)]
    simp only [rev]
    congr 3
    ext; simp [Fin.val_rev]
  · rw [revAt_eq_self_of_lt (by omega), dif_neg (by omega), dif_neg (by omega)]

lemma poly_alt {n : ℕ} (ε : Fin (n + 1) → ℤˣ) : poly (alt ε) = (poly ε).comp (-X) := by
  apply Polynomial.funext
  intro x
  rw [eval_comp, eval_neg, eval_X, poly_eval, poly_eval]
  unfold ssum alt
  refine Finset.sum_congr rfl (fun i _ => ?_)
  push_cast
  rw [neg_pow]; ring

lemma reverse_X_sub_C (a : ℝ) (ha : a ≠ 0) : reverse (X - C a) = C (-a) * (X - C a⁻¹) := by
  unfold reverse
  rw [natDegree_X_sub_C, reflect_sub, reflect_C]
  rw [show (X : ℝ[X]) = X ^ 1 by rw [pow_one], reflect_monomial, revAt_le (le_refl 1)]
  simp only [Nat.sub_self, pow_zero, pow_one]
  rw [mul_sub, ← C_mul, show -a * a⁻¹ = -1 by field_simp]
  simp only [C_neg, C_1, neg_mul]; ring

lemma reverse_pow' (f : ℝ[X]) (m : ℕ) : reverse (f ^ m) = (reverse f) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero]; unfold reverse; rw [natDegree_one, ← C_1, reflect_C, pow_zero, mul_one]
  | succ m ih => rw [pow_succ, reverse_mul_of_domain, ih, pow_succ]

/-- Multiplicities go up under reversal (at nonzero points). -/
lemma rm_le_rev (p : ℝ[X]) (hp : p ≠ 0) (a : ℝ) (ha : a ≠ 0) :
    rootMultiplicity a p ≤ rootMultiplicity a⁻¹ (reverse p) := by
  obtain ⟨q, hq⟩ := pow_rootMultiplicity_dvd p a
  rw [le_rootMultiplicity_iff (by rwa [Ne, reverse_eq_zero])]
  refine ⟨C ((-a) ^ rootMultiplicity a p) * reverse q, ?_⟩
  conv_lhs => rw [hq]
  rw [reverse_mul_of_domain, reverse_pow', reverse_X_sub_C a ha, mul_pow, ← C_pow]
  ring

/-- Roots under reversal. -/
lemma roots_poly_rev {n : ℕ} (ε : Fin (n + 1) → ℤˣ) :
    (poly (rev ε)).roots = (poly ε).roots.map (fun x => x⁻¹) := by
  have hp := poly_ne_zero ε
  have hq := poly_ne_zero (rev ε)
  have h0p : ¬ (poly ε).IsRoot 0 := by
    rw [IsRoot, ← coeff_zero_eq_eval_zero]; exact poly_coeff_zero ε
  have h0q : ¬ (poly (rev ε)).IsRoot 0 := by
    rw [IsRoot, ← coeff_zero_eq_eval_zero]; exact poly_coeff_zero (rev ε)
  ext b
  rw [count_roots]
  by_cases hb : b = 0
  · subst hb
    rw [rootMultiplicity_eq_zero h0q, eq_comm, Multiset.count_eq_zero]
    intro hmem
    obtain ⟨x, hx, hx0⟩ := Multiset.mem_map.1 hmem
    rw [inv_eq_zero] at hx0
    subst hx0
    exact h0p ((mem_roots hp).1 hx)
  · have hinj : Function.Injective (fun x : ℝ => x⁻¹) := inv_injective
    have e : b = (b⁻¹)⁻¹ := (inv_inv b).symm
    rw [e, Multiset.count_map_eq_count' _ _ hinj, count_roots, inv_inv]
    apply le_antisymm
    · have := rm_le_rev (poly (rev ε)) hq b hb
      rwa [← poly_rev, rev_rev] at this
    · have := rm_le_rev (poly ε) hp b⁻¹ (inv_ne_zero hb)
      rwa [inv_inv, ← poly_rev] at this

lemma roots_poly_alt {n : ℕ} (ε : Fin (n + 1) → ℤˣ) :
    (poly (alt ε)).roots = (poly ε).roots.map (fun x => -x) := by
  rw [poly_alt, roots_comp_neg_X]

lemma nIn_map (p : ℝ[X]) (g : ℝ → ℝ) (q : ℝ[X]) (h : q.roots = p.roots.map g) (I J : Set ℝ)
    (hIJ : ∀ x, g x ∈ I ↔ x ∈ J) : nIn q I = nIn p J := by
  classical
  rw [nIn_def, nIn_def, h, Multiset.filter_map, Multiset.card_map]
  congr 1
  exact Multiset.filter_congr (fun x _ => hIJ x)

lemma nIn_rev {n : ℕ} (ε : Fin (n + 1) → ℤˣ) :
    nIn (poly (rev ε)) (Set.Ioo 0 1) = nIn (poly ε) (Set.Ioi 1) := by
  refine nIn_map _ _ _ (roots_poly_rev ε) _ _ (fun x => ?_)
  simp only [Set.mem_Ioo, Set.mem_Ioi, inv_pos]
  constructor
  · rintro ⟨h1, h2⟩
    exact (inv_lt_one₀ h1).1 h2
  · intro h
    have h0 : 0 < x := by linarith
    exact ⟨h0, (inv_lt_one₀ h0).2 h⟩

lemma nIn_alt {n : ℕ} (ε : Fin (n + 1) → ℤˣ) (I J : Set ℝ) (hIJ : ∀ x, -x ∈ I ↔ x ∈ J) :
    nIn (poly (alt ε)) I = nIn (poly ε) J :=
  nIn_map _ _ _ (roots_poly_alt ε) _ _ hIJ

/-- The four interval counts. -/
lemma nIn_neg_unit {n : ℕ} (ε : Fin (n + 1) → ℤˣ) :
    nIn (poly (alt ε)) (Set.Ioo 0 1) = nIn (poly ε) (Set.Ioo (-1) 0) :=
  nIn_alt ε _ _ (fun x => by simp only [Set.mem_Ioo]; constructor <;> rintro ⟨h1, h2⟩ <;>
    constructor <;> linarith)

lemma nIn_neg_out {n : ℕ} (ε : Fin (n + 1) → ℤˣ) :
    nIn (poly (rev (alt ε))) (Set.Ioo 0 1) = nIn (poly ε) (Set.Iio (-1)) := by
  rw [nIn_rev]
  exact nIn_alt ε _ _ (fun x => by simp only [Set.mem_Ioi, Set.mem_Iio]; constructor <;> intro h <;>
    linarith)

/-- The total, by position. -/
lemma card_split (s : Multiset ℝ) :
    Multiset.card s = Multiset.card (s.filter (· ∈ Set.Ioo 0 1)) + Multiset.card (s.filter (· ∈ Set.Ioi 1))
      + Multiset.card (s.filter (· ∈ Set.Ioo (-1) 0)) + Multiset.card (s.filter (· ∈ Set.Iio (-1)))
      + Multiset.card (s.filter (· ∈ ({1} : Set ℝ))) + Multiset.card (s.filter (· ∈ ({-1} : Set ℝ)))
      + Multiset.card (s.filter (· ∈ ({0} : Set ℝ))) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.filter_cons, Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio, Set.mem_singleton_iff,
      Multiset.card_cons] at ih ⊢
    rcases lt_trichotomy a (-1) with h | h | h
    · rw [if_neg (by intro h'; linarith [h'.1]), if_neg (by intro h'; linarith),
        if_neg (by intro h'; linarith [h'.1]), if_pos h, if_neg (by intro h'; linarith),
        if_neg (by intro h'; linarith), if_neg (by intro h'; linarith)]
      simp only [Multiset.card_add, Multiset.card_singleton, Multiset.card_zero]; omega
    · subst h
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_pos rfl, if_neg (by norm_num)]
      simp only [Multiset.card_add, Multiset.card_singleton, Multiset.card_zero]; omega
    rcases lt_trichotomy a 0 with h' | h' | h'
    · rw [if_neg (by intro h''; linarith [h''.1]), if_neg (by intro h''; linarith),
        if_pos ⟨h, h'⟩, if_neg (by intro h''; linarith), if_neg (by intro h''; linarith),
        if_neg (by intro h''; linarith), if_neg (by intro h''; linarith)]
      simp only [Multiset.card_add, Multiset.card_singleton, Multiset.card_zero]; omega
    · subst h'
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
      simp only [Multiset.card_add, Multiset.card_singleton, Multiset.card_zero]; omega
    rcases lt_trichotomy a 1 with h'' | h'' | h''
    · rw [if_pos ⟨h', h''⟩, if_neg (by intro k; linarith), if_neg (by intro k; linarith [k.2]),
        if_neg (by intro k; linarith), if_neg (by intro k; linarith), if_neg (by intro k; linarith),
        if_neg (by intro k; linarith)]
      simp only [Multiset.card_add, Multiset.card_singleton, Multiset.card_zero]; omega
    · subst h''
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_pos rfl, if_neg (by norm_num), if_neg (by norm_num)]
      simp only [Multiset.card_add, Multiset.card_singleton, Multiset.card_zero]; omega
    · rw [if_neg (by intro k; linarith [k.2]), if_pos h'', if_neg (by intro k; linarith [k.2]),
        if_neg (by intro k; linarith), if_neg (by intro k; linarith), if_neg (by intro k; linarith),
        if_neg (by intro k; linarith)]
      simp only [Multiset.card_add, Multiset.card_singleton, Multiset.card_zero]; omega

lemma nIn_zero_pt {n : ℕ} (ε : Fin (n + 1) → ℤˣ) : nIn (poly ε) ({0} : Set ℝ) = 0 := by
  classical
  rw [nIn_def, Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro x hx hx0
  rw [Set.mem_singleton_iff] at hx0; subst hx0
  rw [mem_roots (poly_ne_zero ε), IsRoot, ← coeff_zero_eq_eval_zero] at hx
  exact poly_coeff_zero ε hx

theorem total_roots {n : ℕ} (ε : Fin (n + 1) → ℤˣ) :
    Multiset.card (poly ε).roots = nIn (poly ε) (Set.Ioo 0 1) + nIn (poly ε) (Set.Ioi 1)
      + nIn (poly ε) (Set.Ioo (-1) 0) + nIn (poly ε) (Set.Iio (-1)) + nIn (poly ε) ({1} : Set ℝ)
      + nIn (poly ε) ({-1} : Set ℝ) := by
  classical
  have h := card_split (poly ε).roots
  have h0 := nIn_zero_pt ε
  simp only [nIn_def] at h0 ⊢
  omega

lemma eval_of_nIn_pt {n : ℕ} (ε : Fin (n + 1) → ℤˣ) (a : ℝ) (h : 0 < nIn (poly ε) ({a} : Set ℝ)) :
    (poly ε).eval a = 0 := by
  obtain ⟨ξ, hξ, h0⟩ := exists_root_of_nIn_pos h
  rw [Set.mem_singleton_iff] at hξ; rwa [hξ] at h0

/-! ### Roots at `±1` are rare -/

lemma PP_card' {ι : Type*} [Fintype ι] [DecidableEq ι] (S : (ι → ℤˣ) → Prop) [DecidablePred S] :
    PP S = ((univ.filter S).card : ℝ) / 2 ^ Fintype.card ι := by
  rw [PP_eq]; unfold EE; rw [Finset.sum_boole]

lemma PP_eval_zero {n : ℕ} (a : Fin (n + 1) → ℝ) (ha : ∀ i, |a i| = 1) :
    PP (fun ε : Fin (n + 1) → ℤˣ => ssum ε a = 0) ≤ 3 / √(n + 1 : ℝ) := by
  classical
  have h := lo_interval a univ (fun i _ => (ha i).ge) univ_nonempty (-1)
  rw [card_univ, Fintype.card_fin] at h
  have hmono : PP (fun ε : Fin (n + 1) → ℤˣ => ssum ε a = 0)
      ≤ PP (fun ε : Fin (n + 1) → ℤˣ => -1 ≤ ssum ε a ∧ ssum ε a < -1 + 2) :=
    PP_mono (fun ε h0 => by rw [h0]; norm_num)
  refine hmono.trans ?_
  rw [PP_card', Fintype.card_fin]
  have hpos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  rw [div_le_iff₀ hpos]
  have hs : (0 : ℝ) < √(n + 1 : ℝ) := Real.sqrt_pos.2 (by positivity)
  calc _ ≤ 2 ^ (n + 1) / √((n + 1 : ℕ) : ℝ) := h
    _ = 1 / √(n + 1 : ℝ) * 2 ^ (n + 1) := by push_cast; ring
    _ ≤ 3 / √(n + 1 : ℝ) * 2 ^ (n + 1) := by gcongr; norm_num

lemma PP_root_one {n : ℕ} :
    PP (fun ε : Fin (n + 1) → ℤˣ => (poly ε).eval 1 = 0) ≤ 3 / √(n + 1 : ℝ) := by
  have := PP_eval_zero (n := n) (fun _ => 1) (fun _ => by simp)
  refine le_trans (le_of_eq ?_) this
  congr 1; ext ε; rw [poly_eval]; simp

lemma PP_root_neg_one {n : ℕ} :
    PP (fun ε : Fin (n + 1) → ℤˣ => (poly ε).eval (-1) = 0) ≤ 3 / √(n + 1 : ℝ) := by
  have := PP_eval_zero (n := n) (fun i => (-1) ^ (i : ℕ)) (fun _ => by simp)
  refine le_trans (le_of_eq ?_) this
  congr 1; ext ε; rw [poly_eval]

/-! ### From the quarter to the total -/

/-- The quarter statement (proved elsewhere). -/
def QuarterStmt : Prop := ∀ η > 0, ∀ᶠ n : ℕ in Filter.atTop,
  PP (ι := Fin (n + 1)) (fun ε => η ≤ |(nIn (poly ε) (Set.Ioo 0 1) : ℝ) / Real.log n - 1 / (2 * π)|) ≤ η

theorem total_conc (hQ : QuarterStmt) : ∀ η > 0, ∀ᶠ n : ℕ in Filter.atTop,
    PP (ι := Fin (n + 1)) (fun ε => η ≤ |(Multiset.card (poly ε).roots : ℝ) / Real.log n - 2 / π|)
      ≤ η := by
  intro η hη
  set η' := η / 6 with hη'
  have hη'0 : 0 < η' := by positivity
  have hsq : ∀ᶠ n : ℕ in Filter.atTop, 3 / √(n + 1 : ℝ) ≤ η' := by
    have ht : Filter.Tendsto (fun n : ℕ => 3 / √(n + 1 : ℝ)) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => √(n + 1 : ℝ)) Filter.atTop Filter.atTop :=
        Real.tendsto_sqrt_atTop.comp (Filter.tendsto_atTop_add_const_right _ 1
          tendsto_natCast_atTop_atTop)
      exact h1.const_div_atTop 3
    exact ht.eventually (ge_mem_nhds hη'0)
  filter_upwards [hQ η' hη'0, hsq] with n hq hs
  set c := 1 / (2 * π)
  set L := Real.log n
  set A : (Fin (n + 1) → ℤˣ) → Prop := fun ε => η' ≤ |(nIn (poly ε) (Set.Ioo 0 1) : ℝ) / L - c|
  have hsub : ∀ ε : Fin (n + 1) → ℤˣ, η ≤ |(Multiset.card (poly ε).roots : ℝ) / L - 2 / π| →
      ((((A ε ∨ A (rev ε)) ∨ A (alt ε)) ∨ A (rev (alt ε))) ∨ (poly ε).eval 1 = 0) ∨
        (poly ε).eval (-1) = 0 := by
    intro ε hε
    by_contra hn
    simp only [not_or] at hn
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hn
    simp only [A, not_le] at h1 h2 h3 h4
    rw [nIn_rev] at h2
    rw [nIn_neg_unit] at h3
    rw [nIn_neg_out] at h4
    have z1 : nIn (poly ε) ({1} : Set ℝ) = 0 := by
      by_contra hz; exact h5 (eval_of_nIn_pt ε 1 (Nat.pos_of_ne_zero hz))
    have z2 : nIn (poly ε) ({-1} : Set ℝ) = 0 := by
      by_contra hz; exact h6 (eval_of_nIn_pt ε (-1) (Nat.pos_of_ne_zero hz))
    rw [total_roots, z1, z2] at hε
    push_cast at hε
    have e : 2 / π = 4 * c := by simp only [c]; field_simp; ring
    rw [e] at hε
    have : |((nIn (poly ε) (Set.Ioo 0 1) : ℝ) + nIn (poly ε) (Set.Ioi 1) + nIn (poly ε) (Set.Ioo (-1) 0)
        + nIn (poly ε) (Set.Iio (-1)) + 0 + 0) / L - 4 * c|
        ≤ |(nIn (poly ε) (Set.Ioo 0 1) : ℝ) / L - c| + |(nIn (poly ε) (Set.Ioi 1) : ℝ) / L - c|
          + |(nIn (poly ε) (Set.Ioo (-1) 0) : ℝ) / L - c| + |(nIn (poly ε) (Set.Iio (-1)) : ℝ) / L - c| := by
      have : ((nIn (poly ε) (Set.Ioo 0 1) : ℝ) + nIn (poly ε) (Set.Ioi 1) + nIn (poly ε) (Set.Ioo (-1) 0)
          + nIn (poly ε) (Set.Iio (-1)) + 0 + 0) / L - 4 * c
          = ((nIn (poly ε) (Set.Ioo 0 1) : ℝ) / L - c) + ((nIn (poly ε) (Set.Ioi 1) : ℝ) / L - c)
            + ((nIn (poly ε) (Set.Ioo (-1) 0) : ℝ) / L - c) + ((nIn (poly ε) (Set.Iio (-1)) : ℝ) / L - c) := by
        ring
      rw [this]
      exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    linarith
  calc PP (fun ε : Fin (n + 1) → ℤˣ => η ≤ |(Multiset.card (poly ε).roots : ℝ) / L - 2 / π|)
      ≤ PP (fun ε : Fin (n + 1) → ℤˣ => ((((A ε ∨ A (rev ε)) ∨ A (alt ε)) ∨ A (rev (alt ε))) ∨
          (poly ε).eval 1 = 0) ∨ (poly ε).eval (-1) = 0) := PP_mono hsub
    _ ≤ PP A + PP (fun ε => A (rev ε)) + PP (fun ε => A (alt ε)) + PP (fun ε => A (rev (alt ε)))
          + PP (fun ε : Fin (n + 1) → ℤˣ => (poly ε).eval 1 = 0)
          + PP (fun ε : Fin (n + 1) → ℤˣ => (poly ε).eval (-1) = 0) := by
        refine (PP_or_le _ _).trans (add_le_add ((PP_or_le _ _).trans (add_le_add
          ((PP_or_le _ _).trans (add_le_add ((PP_or_le _ _).trans
          (add_le_add (PP_or_le _ _) le_rfl)) le_rfl)) le_rfl)) le_rfl)
    _ ≤ η' + η' + η' + η' + η' + η' := by
        have e1 : PP (fun ε => A (rev ε)) = PP A := PP_equiv (revE n) A
        have e2 : PP (fun ε => A (alt ε)) = PP A := PP_equiv (altE n) A
        have e3 : PP (fun ε => A (rev (alt ε))) = PP A :=
          PP_equiv ((altE n).trans (revE n)) A
        rw [e1, e2, e3]
        have := PP_root_one (n := n)
        have := PP_root_neg_one (n := n)
        linarith
    _ = η := by rw [hη']; ring

/-! ### The diagonal argument -/

theorem diagonal (g : ℕ → ℝ → ℝ) (hg : ∀ η > 0, ∀ᶠ n : ℕ in Filter.atTop, g n η ≤ η)
    (hle : ∀ n η, g n η ≤ 1) : ∃ p o : ℕ → ℝ, Filter.Tendsto o Filter.atTop (nhds 0) ∧
      Filter.Tendsto p Filter.atTop (nhds 0) ∧ ∀ n, g n (o n) ≤ p n := by
  classical
  have hex : ∀ k : ℕ, ∃ N, ∀ m ≥ N, g m (1 / (k + 1)) ≤ 1 / (k + 1) := fun k =>
    Filter.eventually_atTop.1 (hg _ (by positivity))
  set N : ℕ → ℕ := fun k => Nat.find (hex k)
  have hN : ∀ k m, N k ≤ m → g m (1 / (k + 1)) ≤ 1 / (k + 1) := fun k m h => Nat.find_spec (hex k) m h
  set kk : ℕ → ℕ := fun n => Nat.findGreatest (fun k => N k ≤ n) n
  have hkk : Filter.Tendsto kk Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 (fun K => Filter.eventually_atTop.2 ⟨max K (N K), fun n hn => ?_⟩)
    exact Nat.le_findGreatest (le_of_max_le_left hn) (le_of_max_le_right hn)
  have hspec : ∀ᶠ n in Filter.atTop, N (kk n) ≤ n := by
    refine Filter.eventually_atTop.2 ⟨N 0, fun n hn => ?_⟩
    exact Nat.findGreatest_spec (P := fun k => N k ≤ n) (Nat.zero_le n) hn
  refine ⟨fun n => if N (kk n) ≤ n then 1 / ((kk n : ℝ) + 1) else 1, fun n => 1 / ((kk n : ℝ) + 1),
    ?_, ?_, fun n => ?_⟩
  · exact (tendsto_one_div_add_atTop_nhds_zero_nat).comp hkk
  · refine ((tendsto_one_div_add_atTop_nhds_zero_nat).comp hkk).congr' ?_
    filter_upwards [hspec] with n hn
    simp [hn]
  · dsimp only
    split_ifs with h
    · exact hN _ _ h
    · exact hle _ _

end R522



namespace R522

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The real value of a sign. -/
def sv (u : ℤˣ) : ℝ := ((u : ℤ) : ℝ)

lemma sv_injective : Function.Injective sv := by
  intro u v h
  unfold sv at h
  exact Units.ext (by exact_mod_cast h)

/-- **Transfer**: probabilities of events of the Kac polynomial are sign-vector proportions. -/
theorem prob_eq_PP {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] (n : ℕ)
    (f : Erdos522.KacCoefficients ({-1, 1} : Set ℝ) Ω) (Q : ℝ[X] → Prop) :
    (ℙ {ω | Q (f.polynomial n ω)}).toReal = PP (ι := Fin (n + 1)) (fun ε => Q (poly ε)) := by
  classical
  have hSm : MeasurableSet ({-1, 1} : Set ℝ) := (Set.toFinite ({-1, 1} : Set ℝ)).measurableSet
  have hcS : (Measure.count : Measure ℝ) ({-1, 1} : Set ℝ) = 2 := by
    rw [Measure.count_apply hSm, Set.encard_pair (by norm_num)]; rfl
  have hcond : ∀ t, MeasurableSet t →
      (ProbabilityTheory.cond (Measure.count : Measure ℝ) ({-1, 1} : Set ℝ)) t = 2⁻¹ * Measure.count (({-1, 1} : Set ℝ) ∩ t) := by
    intro t ht; rw [cond_apply hSm, hcS]
  set X : ℕ → Ω → ℝ := fun i => f i with hX
  have hU : ∀ i, (ℙ : Measure Ω).map (X i) = ProbabilityTheory.cond Measure.count ({-1, 1} : Set ℝ) := fun i => f.h_unif i
  have hAE : ∀ i, AEMeasurable (X i) ℙ := by
    intro i
    apply AEMeasurable.of_map_ne_zero
    rw [hU i]
    intro h0
    have := hcond Set.univ MeasurableSet.univ
    rw [h0, Set.inter_univ, hcS] at this
    simp at this
  have hpt : ∀ i (u : ℤˣ), (ℙ : Measure Ω) (X i ⁻¹' {sv u}) = 2⁻¹ := by
    intro i u
    rw [← Measure.map_apply_of_aemeasurable (hAE i) (measurableSet_singleton _), hU i,
      hcond _ (measurableSet_singleton _)]
    have : ({-1, 1} : Set ℝ) ∩ {sv u} = {sv u} := by
      rw [Set.inter_eq_right, Set.singleton_subset_iff]
      rcases Int.units_eq_one_or u with h | h <;> simp [sv, h]
    rw [this, Measure.count_singleton, mul_one]
  have hbad : ∀ i, (ℙ : Measure Ω) (X i ⁻¹' ({-1, 1} : Set ℝ)ᶜ) = 0 := by
    intro i
    rw [← Measure.map_apply_of_aemeasurable (hAE i) hSm.compl, hU i, hcond _ hSm.compl,
      Set.inter_compl_self, measure_empty, mul_zero]
  -- the events
  set v : (Fin (n + 1) → ℤˣ) → ℕ → ℝ := fun ε i => if h : i < n + 1 then sv (ε ⟨i, h⟩) else 1
  set E : (Fin (n + 1) → ℤˣ) → Set Ω := fun ε => ⋂ i ∈ Finset.range (n + 1), X i ⁻¹' {v ε i}
  have hvsv : ∀ ε (i : Fin (n + 1)), v ε (i : ℕ) = sv (ε i) := by
    intro ε i; simp only [v, dif_pos i.2]
  have hE : ∀ ε, (ℙ : Measure Ω) (E ε) = 2⁻¹ ^ (n + 1) := by
    intro ε
    show (ℙ : Measure Ω) (⋂ i ∈ Finset.range (n + 1), f.toFun i ⁻¹' {v ε i}) = _
    rw [f.h_indep.measure_inter_preimage_eq_mul (Finset.range (n + 1))
      (fun i _ => measurableSet_singleton (v ε i))]
    rw [Finset.prod_congr rfl (fun i hi => by
      have hi' : i < n + 1 := Finset.mem_range.1 hi
      show (ℙ : Measure Ω) (X i ⁻¹' {v ε i}) = 2⁻¹
      simp only [v, dif_pos hi']; exact hpt i _), Finset.prod_const, Finset.card_range]
  set G : Set Ω := ⋂ i ∈ Finset.range (n + 1), X i ⁻¹' ({-1, 1} : Set ℝ)
  have hG : (ℙ : Measure Ω) Gᶜ = 0 := by
    rw [Set.compl_iInter₂]
    refine measure_biUnion_null_iff (Finset.range (n + 1)).countable_toSet |>.2 (fun i _ => ?_)
    rw [← Set.preimage_compl]; exact hbad i
  -- the polynomial on `E ε`
  have hpoly : ∀ ε, ∀ ω ∈ E ε, f.polynomial n ω = poly ε := by
    intro ε ω hω
    simp only [E, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff] at hω
    unfold Erdos522.KacCoefficients.polynomial poly
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← C_mul_X_pow_eq_monomial]
    have := hω i (Finset.mem_range.2 i.2)
    rw [show X i ω = (f i ω) from rfl] at this
    rw [this, hvsv]; rfl
  -- the set identity
  have hset : {ω | Q (f.polynomial n ω)} ∩ G = ⋃ ε ∈ univ.filter (fun ε => Q (poly ε)), E ε := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter,
      Finset.mem_univ, true_and, exists_prop]
    constructor
    · rintro ⟨hq, hg⟩
      simp only [G, Set.mem_iInter, Set.mem_preimage] at hg
      set ε : Fin (n + 1) → ℤˣ := fun i => if X i ω = 1 then 1 else -1
      have hmem : ω ∈ E ε := by
        simp only [E, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
        intro i hi
        have hi' : i < n + 1 := Finset.mem_range.1 hi
        simp only [v, dif_pos hi', ε, sv]
        have h := hg i hi
        rcases h with h | h
        · rw [if_neg (by rw [h]; norm_num)]; simpa using h
        · have h := Set.mem_singleton_iff.1 h
          rw [if_pos h]; simpa using h
      exact ⟨ε, by rwa [← hpoly ε ω hmem], hmem⟩
    · rintro ⟨ε, hq, hω⟩
      refine ⟨by rwa [hpoly ε ω hω], ?_⟩
      simp only [G, Set.mem_iInter, Set.mem_preimage]
      intro i hi
      simp only [E, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff] at hω
      rw [hω i hi]
      have hi' : i < n + 1 := Finset.mem_range.1 hi
      simp only [v, dif_pos hi', sv]
      rcases Int.units_eq_one_or (ε ⟨i, hi'⟩) with h | h <;> simp [h]
  have hmeas : (ℙ : Measure Ω) {ω | Q (f.polynomial n ω)}
      = ∑ ε ∈ univ.filter (fun ε => Q (poly ε)), (ℙ : Measure Ω) (E ε) := by
    rw [← measure_inter_conull hG, hset]
    refine measure_biUnion_finset₀ ?_ (fun ε _ => ?_)
    · intro ε _ ε' _ hne
      apply Disjoint.aedisjoint
      rw [Set.disjoint_left]
      intro ω h1 h2
      apply hne
      funext i
      simp only [E, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
      have := (h1 i (Finset.mem_range.2 i.2)).symm.trans (h2 i (Finset.mem_range.2 i.2))
      rw [hvsv, hvsv] at this
      exact sv_injective this
    · exact NullMeasurableSet.biInter (Finset.range (n + 1)).countable_toSet
        (fun i _ => (hAE i).nullMeasurableSet_preimage (measurableSet_singleton _))
  rw [hmeas, Finset.sum_congr rfl (fun ε _ => hE ε), Finset.sum_const, nsmul_eq_mul, PP_card',
    Fintype.card_fin, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat, inv_pow, div_eq_mul_inv]

/-- **Final assembly.** -/
theorem final_of_quarter (hQ : QuarterStmt) : ∃ p o : ℕ → ℝ,
    Filter.atTop.Tendsto o (nhds 0) ∧ Filter.atTop.Tendsto p (nhds 0) ∧
    ∀ (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (n : ℕ) (_hn : 2 ≤ n) (f : Erdos522.KacCoefficients ({-1, 1} : Set ℝ) Ω),
      (ℙ {ω | |(f.roots n ω).card / (n : ℝ).log - 2 / π| ≥ o n}).toReal ≤ p n := by
  obtain ⟨p, o, ho, hp, hb⟩ := diagonal
    (fun n η => PP (ι := Fin (n + 1))
      (fun ε => η ≤ |(Multiset.card (poly ε).roots : ℝ) / Real.log n - 2 / π|))
    (total_conc hQ) (fun n η => PP_le_one _)
  refine ⟨p, o, ho, hp, fun Ω _ _ n _ f => ?_⟩
  have h := prob_eq_PP n f (fun q => o n ≤ |(Multiset.card q.roots : ℝ) / Real.log n - 2 / π|)
  exact (le_of_eq h).trans (hb n)

end R522

end S_RRT

-- ===== RR12 =====

/-!
# Erdős 522 (real roots), part 12: the quarter statement from the two bounds
-/

open Finset Real Polynomial Filter

noncomputable section S_RR12

namespace R522

variable {n L : ℕ}

lemma nIn_union_disj (p : ℝ[X]) {I J : Set ℝ} (h : Disjoint I J) :
    nIn p (I ∪ J) = nIn p I + nIn p J := by
  classical
  rw [nIn_def, nIn_def, nIn_def]
  have := Multiset.filter_add_filter (· ∈ I) (· ∈ J) p.roots
  have h2 := congrArg Multiset.card this
  rw [Multiset.card_add, Multiset.card_add] at h2
  have h0 : p.roots.filter (fun x => x ∈ I ∧ x ∈ J) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro x _ hx
    exact Set.disjoint_left.1 h hx.1 hx.2
  rw [h0, Multiset.card_zero, add_zero] at h2
  have : Multiset.card (p.roots.filter (· ∈ I ∪ J))
      = Multiset.card (p.roots.filter (fun x => x ∈ I ∨ x ∈ J)) := rfl
  omega

/-- Sign changes on disjoint windows give distinct roots. -/
lemma sc_sum_le (hL : 1 ≤ L) (ε : Fin (n + 1) → ℤˣ) {ja : ℕ} (hja : 1 ≤ ja) (J : ℕ) :
    ∑ j ∈ Ico ja J, sc ε L j ≤ (nIn (poly ε) (Set.Ioo 0 1) : ℝ) := by
  -- windows inside `(gx ja, gx J]`
  have key : ∀ J' : ℕ, ja ≤ J' → ∑ j ∈ Ico ja J', sc ε L j
      ≤ (nIn (poly ε) (Set.Ioc (gx L ja) (gx L J')) : ℝ) := by
    intro J' hJ'
    induction J', hJ' using Nat.le_induction with
    | base => simp
    | succ J' hJ' ih =>
      rw [Finset.sum_Ico_succ_top hJ']
      have hdisj : Disjoint (Set.Ioc (gx L ja) (gx L J')) (Set.Ioo (gx L J') (gx L (J' + 1))) := by
        rw [Set.disjoint_left]; intro x hx hy; exact absurd hy.1 (not_lt.2 hx.2)
      have hsub : Set.Ioc (gx L ja) (gx L J') ∪ Set.Ioo (gx L J') (gx L (J' + 1))
          ⊆ Set.Ioc (gx L ja) (gx L (J' + 1)) := by
        intro x hx
        rcases hx with hx | hx
        · exact ⟨hx.1, hx.2.trans (gx_lt_succ hL J').le⟩
        · exact ⟨lt_of_le_of_lt (gx_mono hL hJ') hx.1, hx.2.le⟩
      have h1 := nIn_mono (poly ε) hsub
      rw [nIn_union_disj _ hdisj] at h1
      have hsc : sc ε L J' ≤ (nIn (poly ε) (Set.Ioo (gx L J') (gx L (J' + 1))) : ℝ) := by
        unfold sc
        split_ifs with h
        · have := nIn_pos_of_sign (gx_lt_succ hL J') h
          exact_mod_cast this
        · positivity
      have : (nIn (poly ε) (Set.Ioc (gx L ja) (gx L J')) : ℝ)
          + nIn (poly ε) (Set.Ioo (gx L J') (gx L (J' + 1)))
          ≤ nIn (poly ε) (Set.Ioc (gx L ja) (gx L (J' + 1))) := by exact_mod_cast h1
      linarith
  rcases le_or_gt ja J with h | h
  · refine (key J h).trans ?_
    have hsub : Set.Ioc (gx L ja) (gx L J) ⊆ Set.Ioo 0 1 := by
      intro x hx
      exact ⟨(gx_pos hL hja).trans hx.1, lt_of_le_of_lt hx.2 (gx_lt_one hL J)⟩
    exact_mod_cast nIn_mono _ hsub
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]; positivity

/-- **The quarter statement.** -/
theorem quarter_of_low (hlow : LowSC) : QuarterStmt := by
  intro η hη
  have hup := upper hlow (η / 2) (by positivity)
  obtain ⟨L₀, hL₀⟩ := hlow (η / 2) (by positivity)
  set L := max L₀ 1
  have hL1 : 1 ≤ L := le_max_right _ _
  filter_upwards [hup, hL₀ L (le_max_left _ _) 1, Filter.eventually_gt_atTop 1] with n hu hl hn
  have hℓ : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  set c := 1 / (2 * π)
  have hincl : ∀ ε : Fin (n + 1) → ℤˣ, η ≤ |(nIn (poly ε) (Set.Ioo 0 1) : ℝ) / Real.log n - c| →
      (c + η / 2) * Real.log n ≤ (nIn (poly ε) (Set.Ioo 0 1) : ℝ) ∨
      ∑ j ∈ Ico 1 (Jn L n), sc ε L j ≤ (c - η / 2) * Real.log n := by
    intro ε h
    have hS := sc_sum_le (n := n) hL1 ε (le_refl 1) (Jn L n)
    rcases le_abs'.1 h with h1 | h1
    · right
      have : (nIn (poly ε) (Set.Ioo 0 1) : ℝ) / Real.log n ≤ c - η := by linarith
      rw [div_le_iff₀ hℓ] at this
      nlinarith
    · left
      have : c + η ≤ (nIn (poly ε) (Set.Ioo 0 1) : ℝ) / Real.log n := by linarith
      rw [le_div_iff₀ hℓ] at this
      nlinarith
  calc PP (fun ε : Fin (n + 1) → ℤˣ => η ≤ |(nIn (poly ε) (Set.Ioo 0 1) : ℝ) / Real.log n - c|)
      ≤ PP (fun ε : Fin (n + 1) → ℤˣ => (c + η / 2) * Real.log n ≤ (nIn (poly ε) (Set.Ioo 0 1) : ℝ) ∨
          ∑ j ∈ Ico 1 (Jn L n), sc ε L j ≤ (c - η / 2) * Real.log n) := PP_mono hincl
    _ ≤ η / 2 + η / 2 := (PP_or_le _ _).trans (add_le_add hu hl)
    _ = η := by ring

end R522

end S_RR12

-- ===== RRL =====

/-!
# Erdős 522 (real roots): the lower bound for the number of sign changes

Fable's route (no martingale). Window `j` gets the coefficient block `B_j = [⌊λʲ/K⌋, ⌊Kλʲ⌋)`.
A robust straddle `X_j` of the block sums at the two endpoints, together with smallness of the
outside sums (`¬ bad_j`), forces a sign change of `P`. `X_j` depends only on `B_j`, `bad_j` only on
`B_jᶜ`; far windows have disjoint blocks, hence `∑ X_j` concentrates (Chebyshev), and `∑ X_j bad_j`
is small (Markov).
-/

open Finset Real

noncomputable section S_RRL

namespace R522

variable {n : ℕ}

/-! ### Block weights -/

/-- Block weights `xⁱ` for `b ≤ i < e`. -/
def wB (n b e : ℕ) (x : ℝ) : Fin (n + 1) → ℝ :=
  fun i => if b ≤ (i : ℕ) ∧ (i : ℕ) < e then x ^ (i : ℕ) else 0

/-- Outside weights. -/
def wO (n b e : ℕ) (x : ℝ) : Fin (n + 1) → ℝ :=
  fun i => if b ≤ (i : ℕ) ∧ (i : ℕ) < e then 0 else x ^ (i : ℕ)

/-- The block as a set of coordinates. -/
def blk (n b e : ℕ) : Finset (Fin (n + 1)) := univ.filter (fun i => b ≤ (i : ℕ) ∧ (i : ℕ) < e)

/-- Geometric block sums. -/
def Gs (n b e : ℕ) (q : ℝ) : ℝ := ∑ i : Fin (n + 1), if b ≤ (i : ℕ) ∧ (i : ℕ) < e then q ^ (i : ℕ) else 0

lemma ssum_split (ε : Fin (n + 1) → ℤˣ) (b e : ℕ) (x : ℝ) :
    (poly ε).eval x = ssum ε (wB n b e x) + ssum ε (wO n b e x) := by
  rw [← ssum_wf]
  unfold ssum wf wB wO
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> ring

lemma ssum_wB_congr (b e : ℕ) (x : ℝ) {ε ε' : Fin (n + 1) → ℤˣ}
    (h : ∀ i ∈ blk n b e, ε i = ε' i) : ssum ε (wB n b e x) = ssum ε' (wB n b e x) := by
  unfold ssum wB
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs with hi
  · rw [h i (by simp [blk, hi])]
  · simp

lemma ssum_wO_congr (b e : ℕ) (x : ℝ) {ε ε' : Fin (n + 1) → ℤˣ}
    (h : ∀ i ∈ (blk n b e)ᶜ, ε i = ε' i) : ssum ε (wO n b e x) = ssum ε' (wO n b e x) := by
  unfold ssum wO
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs with hi
  · simp
  · rw [h i (by simp only [blk, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi)]

lemma sum_wB_sq (b e : ℕ) (x : ℝ) : ∑ i, wB n b e x i ^ 2 = Gs n b e (x ^ 2) := by
  unfold wB Gs; refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp [← pow_mul, mul_comm]

lemma sum_wB_mul (b e : ℕ) (x y : ℝ) : ∑ i, wB n b e x i * wB n b e y i = Gs n b e (x * y) := by
  unfold wB Gs; refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp [mul_pow]

lemma sum_wB_four (b e : ℕ) (x : ℝ) : ∑ i, wB n b e x i ^ 4 = Gs n b e (x ^ 4) := by
  unfold wB Gs; refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp [← pow_mul, mul_comm]

lemma Gs_eq (b e : ℕ) (q : ℝ) (hq : q ≠ 1) (he : e ≤ n + 1) (hbe : b ≤ e) :
    Gs n b e q = q ^ b * (1 - q ^ (e - b)) / (1 - q) := by
  unfold Gs
  rw [Fin.sum_univ_eq_sum_range (fun i => if b ≤ i ∧ i < e then q ^ i else 0) (n + 1),
    ← Finset.sum_filter]
  have : (Finset.range (n + 1)).filter (fun i => b ≤ i ∧ i < e) = Finset.Ico b e := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [this, Finset.sum_Ico_eq_sum_range]
  simp_rw [pow_add]
  rw [← Finset.mul_sum, geom_sum_eq hq]
  have h1 : q - 1 ≠ 0 := sub_ne_zero.mpr hq
  have h2 : 1 - q ≠ 0 := fun h => h1 (by linarith)
  field_simp; ring

lemma Gs_four_le (b e : ℕ) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Gs n b e (x ^ 4) ≤ (x ^ 2) ^ b * Gs n b e (x ^ 2) := by
  unfold Gs
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  split_ifs with hi
  · have hx2 : 0 ≤ x ^ 2 := by positivity
    have hx21 : x ^ 2 ≤ 1 := by nlinarith
    have : (x ^ 2) ^ (i : ℕ) ≤ (x ^ 2) ^ b := pow_le_pow_of_le_one hx2 hx21 hi.1
    have e4 : (x ^ 4) ^ (i : ℕ) = (x ^ 2) ^ (i : ℕ) * (x ^ 2) ^ (i : ℕ) := by
      rw [← mul_pow]; ring_nf
    rw [e4]
    exact mul_le_mul_of_nonneg_right this (pow_nonneg hx2 _)
  · simp

lemma geom_range_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) (m : ℕ) :
    ∑ i ∈ Finset.range m, q ^ i ≤ 1 / (1 - q) := by
  rw [le_div_iff₀ (by linarith), mul_comm, mul_neg_geom_sum]
  have : 0 ≤ q ^ m := pow_nonneg h0 m
  linarith

lemma sum_wO_sq_le (b e : ℕ) {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    ∑ i, wO n b e x i ^ 2 ≤ b + (x ^ 2) ^ e / (1 - x ^ 2) := by
  set q := x ^ 2
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by simp only [q]; nlinarith
  have hpt : ∀ i : Fin (n + 1), wO n b e x i ^ 2
      ≤ (if (i : ℕ) < b then (1 : ℝ) else 0) + (if e ≤ (i : ℕ) then q ^ (i : ℕ) else 0) := by
    intro i
    unfold wO
    have hqi : q ^ (i : ℕ) ≤ 1 := pow_le_one₀ hq0 hq1.le
    have hqi0 : 0 ≤ q ^ (i : ℕ) := pow_nonneg hq0 _
    have esq : (x ^ (i : ℕ)) ^ 2 = q ^ (i : ℕ) := by simp only [q]; rw [← pow_mul, ← pow_mul, mul_comm]
    by_cases hb : b ≤ (i : ℕ) ∧ (i : ℕ) < e
    · rw [if_pos hb]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      split_ifs <;> linarith
    · rw [if_neg hb, esq]
      rw [not_and_or, not_le, not_lt] at hb
      rcases hb with h | h
      · rw [if_pos h]; split_ifs <;> linarith
      · rw [if_pos h]; split_ifs <;> linarith
  calc ∑ i, wO n b e x i ^ 2
      ≤ ∑ i : Fin (n + 1), ((if (i : ℕ) < b then (1 : ℝ) else 0) + (if e ≤ (i : ℕ) then q ^ (i : ℕ) else 0)) :=
        Finset.sum_le_sum (fun i _ => hpt i)
    _ = (∑ i ∈ Finset.range (n + 1), if i < b then (1 : ℝ) else 0)
          + ∑ i ∈ Finset.range (n + 1), (if e ≤ i then q ^ i else 0) := by
        rw [Finset.sum_add_distrib,
          Fin.sum_univ_eq_sum_range (fun i => if i < b then (1 : ℝ) else 0) (n + 1),
          Fin.sum_univ_eq_sum_range (fun i => if e ≤ i then q ^ i else 0) (n + 1)]
    _ ≤ b + q ^ e / (1 - q) := by
        gcongr
        · rw [Finset.sum_boole]
          have : (Finset.range (n + 1)).filter (fun i => i < b) ⊆ Finset.range b := by
            intro i hi; simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢; exact hi.2
          exact_mod_cast (Finset.card_le_card this).trans (by simp)
        · calc ∑ i ∈ Finset.range (n + 1), (if e ≤ i then q ^ i else 0)
              ≤ ∑ i ∈ Finset.range (n + 1 + e), (if e ≤ i then q ^ i else 0) :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
                  (fun i _ _ => by split_ifs <;> positivity)
            _ = ∑ i ∈ Finset.Ico e (n + 1 + e), q ^ i := by
                rw [← Finset.sum_filter]
                congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
            _ = q ^ e * ∑ k ∈ Finset.range (n + 1), q ^ k := by
                rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
                rw [show n + 1 + e - e = n + 1 by omega]
                exact Finset.sum_congr rfl (fun k _ => by rw [pow_add])
            _ ≤ q ^ e * (1 / (1 - q)) := by
                gcongr; exact geom_range_le hq0 hq1 _
            _ = q ^ e / (1 - q) := by ring

/-! ### One block: positivity, fourth moments, outside sums -/

lemma Gs_pos (b e : ℕ) {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (he : e ≤ n + 1) (hbe : b < e) :
    0 < Gs n b e q := by
  rw [Gs_eq b e q h1.ne he hbe.le]
  have : q ^ (e - b) < 1 := pow_lt_one₀ h0.le h1 (by omega)
  have : 0 < q ^ b := pow_pos h0 b
  apply div_pos (by nlinarith) (by linarith)

lemma four_ratio (b e : ℕ) {x δ₀ : ℝ} (h0 : 0 < x) (h1 : x < 1) (he : e ≤ n + 1) (hbe : b < e)
    (hX : (x ^ 2) ^ (e - b) ≤ δ₀) (hδ : δ₀ < 1) :
    Gs n b e (x ^ 4) / Gs n b e (x ^ 2) ^ 2 ≤ (1 - x ^ 2) / (1 - δ₀) := by
  have hq0 : 0 < x ^ 2 := by positivity
  have hq1 : x ^ 2 < 1 := by nlinarith
  have hS := Gs_pos (n := n) b e hq0 hq1 he hbe
  have h4 := Gs_four_le (n := n) b e h0.le h1.le
  rw [div_le_iff₀ (by positivity)]
  have hb := Gs_eq (n := n) b e (x ^ 2) hq1.ne he hbe.le
  set M := e - b
  have hqb : 0 < (x ^ 2) ^ b := pow_pos hq0 b
  have hXn : 0 ≤ (x ^ 2) ^ M := pow_nonneg hq0.le _
  -- `q^b ≤ (1 - q)/(1 - δ₀) · S`
  have key : (x ^ 2) ^ b ≤ (1 - x ^ 2) / (1 - δ₀) * Gs n b e (x ^ 2) := by
    rw [hb, div_mul_div_comm, le_div_iff₀ (by nlinarith)]
    have : (1 - δ₀) * (1 - x ^ 2) ≤ (1 - (x ^ 2) ^ M) * (1 - x ^ 2) := by
      apply mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  calc Gs n b e (x ^ 4) ≤ (x ^ 2) ^ b * Gs n b e (x ^ 2) := h4
    _ ≤ (1 - x ^ 2) / (1 - δ₀) * Gs n b e (x ^ 2) * Gs n b e (x ^ 2) :=
        mul_le_mul_of_nonneg_right key hS.le
    _ = _ := by ring

lemma out_ratio (b e : ℕ) {x δ₀ : ℝ} (h0 : 0 < x) (h1 : x < 1) (he : e ≤ n + 1) (hbe : b < e)
    (hX : (x ^ 2) ^ (e - b) ≤ δ₀) (hδ : δ₀ < 1) :
    (b + (x ^ 2) ^ e / (1 - x ^ 2)) / Gs n b e (x ^ 2)
      ≤ b * (1 - x ^ 2) / ((x ^ 2) ^ b * (1 - δ₀)) + δ₀ / (1 - δ₀) := by
  have hq0 : 0 < x ^ 2 := by positivity
  have hq1 : x ^ 2 < 1 := by nlinarith
  rw [Gs_eq (n := n) b e (x ^ 2) hq1.ne he hbe.le]
  set q := x ^ 2
  set M := e - b
  have hqb : 0 < q ^ b := pow_pos hq0 b
  have hXn : 0 ≤ q ^ M := pow_nonneg hq0.le _
  have hX1 : q ^ M < 1 := lt_of_le_of_lt hX hδ
  have he' : q ^ e = q ^ b * q ^ M := by rw [← pow_add]; congr 1; omega
  have h1q : 0 < 1 - q := by linarith
  have hden : 0 < q ^ b * (1 - q ^ M) / (1 - q) := by apply div_pos (by nlinarith) h1q
  rw [div_le_iff₀ hden]
  have hA : b * (1 - q) / (q ^ b * (1 - δ₀)) * (q ^ b * (1 - q ^ M) / (1 - q)) ≥ b := by
    rw [div_mul_div_comm]
    have hd : 0 < 1 - δ₀ := by linarith
    rw [ge_iff_le, le_div_iff₀ (by positivity)]
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    have : (1 - δ₀) ≤ (1 - q ^ M) := by linarith
    have : b * (q ^ b * (1 - δ₀) * (1 - q)) ≤ b * (q ^ b * (1 - q ^ M) * (1 - q)) := by
      apply mul_le_mul_of_nonneg_left _ hb0
      apply mul_le_mul_of_nonneg_right _ h1q.le
      exact mul_le_mul_of_nonneg_left this hqb.le
    nlinarith
  have hB : q ^ e / (1 - q) ≤ δ₀ / (1 - δ₀) * (q ^ b * (1 - q ^ M) / (1 - q)) := by
    have hd : 0 < 1 - δ₀ := by linarith
    have key : q ^ M ≤ δ₀ * (1 - q ^ M) / (1 - δ₀) := by
      rw [le_div_iff₀ hd]; nlinarith
    have e1 : q ^ e / (1 - q) = q ^ b / (1 - q) * q ^ M := by rw [he']; ring
    have e2 : δ₀ / (1 - δ₀) * (q ^ b * (1 - q ^ M) / (1 - q))
        = q ^ b / (1 - q) * (δ₀ * (1 - q ^ M) / (1 - δ₀)) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left key (by positivity)
  linarith

/-- Block correlation: the lower truncation cancels. -/
lemma blk_corr (b e : ℕ) {x y ρ₀ δ₀ : ℝ} (hx0 : 0 < x) (hxy : x ≤ y) (hy1 : y < 1)
    (hid : (1 - x ^ 2) * (1 - y ^ 2) = ρ₀ ^ 2 * (1 - x * y) ^ 2) (hρ : 0 < ρ₀)
    (he : e ≤ n + 1) (hbe : b < e) (hY : (y ^ 2) ^ (e - b) ≤ δ₀) (hδ : δ₀ < 1) :
    Gs n b e (x * y) ≤ ρ₀ / (1 - δ₀) * √(Gs n b e (x ^ 2) * Gs n b e (y ^ 2)) := by
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hx1 : x < 1 := lt_of_le_of_lt hxy hy1
  have hq1 : x ^ 2 < 1 := by nlinarith
  have hq2 : y ^ 2 < 1 := by nlinarith
  have hr1 : x * y < 1 := by nlinarith
  have hr0 : 0 < x * y := mul_pos hx0 hy0
  set M := e - b
  have hX : (x ^ 2) ^ M ≤ δ₀ :=
    le_trans (pow_le_pow_left₀ (by positivity) (by nlinarith) M) hY
  rw [Gs_eq (n := n) b e _ hr1.ne he hbe.le, Gs_eq (n := n) b e _ hq1.ne he hbe.le,
    Gs_eq (n := n) b e _ hq2.ne he hbe.le]
  set r := x * y
  have hXn : 0 ≤ (x ^ 2) ^ M := by positivity
  have hYn : 0 ≤ (y ^ 2) ^ M := by positivity
  have hrM : (x * y) ^ M ≤ 1 := pow_le_one₀ hr0.le hr1.le
  have hrM0 : 0 ≤ (x * y) ^ M := by positivity
  have hd : 0 < 1 - δ₀ := by linarith
  have hC0 : 0 ≤ r ^ b * (1 - r ^ M) / (1 - r) := by
    apply div_nonneg _ (by linarith); exact mul_nonneg (by positivity) (by linarith)
  -- product of the two variances
  have hprod : (x ^ 2) ^ b * (1 - (x ^ 2) ^ M) / (1 - x ^ 2) * ((y ^ 2) ^ b * (1 - (y ^ 2) ^ M) / (1 - y ^ 2))
      = (r ^ b) ^ 2 * ((1 - (x ^ 2) ^ M) * (1 - (y ^ 2) ^ M)) / (ρ₀ ^ 2 * (1 - r) ^ 2) := by
    rw [div_mul_div_comm, hid]
    congr 1
    have : (x ^ 2) ^ b * (y ^ 2) ^ b = (r ^ b) ^ 2 := by
      simp only [r]; rw [← mul_pow, ← pow_mul, ← mul_pow]; ring_nf
    rw [← this]; ring
  rw [hprod]
  have hsq : √((r ^ b) ^ 2 * ((1 - (x ^ 2) ^ M) * (1 - (y ^ 2) ^ M)) / (ρ₀ ^ 2 * (1 - r) ^ 2))
      = r ^ b / (ρ₀ * (1 - r)) * √((1 - (x ^ 2) ^ M) * (1 - (y ^ 2) ^ M)) := by
    rw [show (r ^ b) ^ 2 * ((1 - (x ^ 2) ^ M) * (1 - (y ^ 2) ^ M)) / (ρ₀ ^ 2 * (1 - r) ^ 2)
        = (r ^ b / (ρ₀ * (1 - r))) ^ 2 * ((1 - (x ^ 2) ^ M) * (1 - (y ^ 2) ^ M)) by
      rw [div_pow, mul_pow]; ring]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by
      apply div_nonneg (by positivity); exact mul_nonneg hρ.le (by linarith))]
  rw [hsq]
  have hs : 1 - δ₀ ≤ √((1 - (x ^ 2) ^ M) * (1 - (y ^ 2) ^ M)) := by
    rw [show 1 - δ₀ = √((1 - δ₀) ^ 2) by rw [Real.sqrt_sq hd.le]]
    apply Real.sqrt_le_sqrt
    rw [sq]; apply mul_le_mul <;> linarith
  have hrb : 0 ≤ r ^ b := by positivity
  have h1r : 0 < 1 - r := by linarith
  calc r ^ b * (1 - r ^ M) / (1 - r) ≤ r ^ b / (1 - r) := by
        apply div_le_div_of_nonneg_right _ h1r.le
        nlinarith
    _ = ρ₀ / (1 - δ₀) * (r ^ b / (ρ₀ * (1 - r)) * (1 - δ₀)) := by
        field_simp
    _ ≤ ρ₀ / (1 - δ₀) * (r ^ b / (ρ₀ * (1 - r)) * √((1 - (x ^ 2) ^ M) * (1 - (y ^ 2) ^ M))) := by
        gcongr

lemma Gs_nonneg (b e : ℕ) {q : ℝ} (h : 0 ≤ q) : 0 ≤ Gs n b e q := by
  unfold Gs; exact Finset.sum_nonneg (fun i _ => by split_ifs <;> positivity)

/-- `arccos` of the inflated correlation. -/
lemma arccos_infl {ρ₀ d δ₀ η₁ : ℝ} (hρ : 0 < ρ₀) (hd : 1 - ρ₀ ^ 2 = d ^ 2) (hd0 : 0 < d)
    (hδ0 : 0 ≤ δ₀) (hδ1 : δ₀ ≤ 1 / 10) (hη0 : 0 ≤ η₁) (hη1 : η₁ ≤ 1 / 2)
    (h3 : 3 * δ₀ ≤ η₁ * d ^ 2) :
    0 ≤ ρ₀ / (1 - δ₀) ∧ ρ₀ / (1 - δ₀) < 1 ∧ (1 - η₁) * d ≤ Real.arccos (ρ₀ / (1 - δ₀)) := by
  have hdd : 0 < 1 - δ₀ := by linarith
  set ρ₁ := ρ₀ / (1 - δ₀)
  have hρ₁ : 0 ≤ ρ₁ := by positivity
  have hρ01 : ρ₀ ^ 2 ≤ 1 := by nlinarith
  have hinv : ρ₁ ^ 2 ≤ ρ₀ ^ 2 * (1 + 3 * δ₀) := by
    simp only [ρ₁]; rw [div_pow, div_le_iff₀ (by positivity)]
    have : 1 ≤ (1 + 3 * δ₀) * (1 - δ₀) ^ 2 := by
      nlinarith [mul_nonneg hδ0 (by linarith : (0:ℝ) ≤ 1 - 5 * δ₀), pow_nonneg hδ0 3]
    nlinarith [sq_nonneg ρ₀]
  have hle : ρ₁ ^ 2 ≤ 1 - d ^ 2 * (1 - η₁) := by nlinarith
  have h1η : 0 < 1 - η₁ := by linarith
  have hpos : 0 < d ^ 2 * (1 - η₁) := mul_pos (pow_pos hd0 2) h1η
  have hlt : ρ₁ < 1 := by nlinarith
  refine ⟨hρ₁, hlt, ?_⟩
  have hsin : Real.sin (Real.arccos ρ₁) ≤ Real.arccos ρ₁ := Real.sin_le (Real.arccos_nonneg _)
  rw [Real.sin_arccos] at hsin
  refine le_trans ?_ hsin
  rw [show (1 - η₁) * d = √(((1 - η₁) * d) ^ 2) by rw [Real.sqrt_sq (by nlinarith)]]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg d]

/-! ### Grid blocks -/

/-- Block start and end for window `j`. -/
def bl (L K j : ℕ) : ℕ := ⌊lam L ^ j / K⌋₊
def bu (L K j : ℕ) : ℕ := ⌊(K : ℝ) * lam L ^ j⌋₊

lemma lam_le_two' {L : ℕ} (hL : 1 ≤ L) : lam L ≤ 2 := lam_le_two hL

lemma CqL_nonneg (τ R w : ℝ) : 0 ≤ CqL τ R w := by
  unfold CqL; split_ifs
  · unfold Cq
    exact mul_nonneg (by positivity) (add_nonneg (mul_nonneg (mom_nonneg _ _) (mom_nonneg _ _))
      (mul_nonneg (mom_nonneg _ _) (mom_nonneg _ _)))
  · exact le_rfl

/-- The grid facts for one window. -/
lemma grid_blk {L K j : ℕ} (hL : 1 ≤ L) (hK : 30 ≤ K) (hn : (K : ℝ) * lam L ^ j ≤ n) :
    bu L K j ≤ n + 1 ∧ bl L K j < bu L K j ∧
    ((gx L (j + 1)) ^ 2) ^ (bu L K j - bl L K j) ≤ 3 / K ∧
    1 - gx L j ^ 2 ≤ 4 / lam L ^ j ∧ 1 - gx L (j + 1) ^ 2 ≤ 4 / lam L ^ j ∧
    (bl L K j : ℝ) ≤ lam L ^ j / K ∧ 1 / 2 ≤ (gx L j ^ 2) ^ bl L K j ∧
    1 / 2 ≤ (gx L (j + 1) ^ 2) ^ bl L K j := by
  set s := lam L ^ j with hs
  have hl := lam_gt hL
  have hl2 := lam_le_two hL
  have hs1 : 1 ≤ s := lam_pow_ge_one hL j
  have hK0 : (30 : ℝ) ≤ K := by exact_mod_cast hK
  have hKp : (0 : ℝ) < K := by linarith
  set x := gx L j
  set y := gx L (j + 1)
  have hx0 := gx_nonneg hL j
  have hx1 := gx_lt_one hL j
  have hy0 := gx_nonneg hL (j + 1)
  have hy1 := gx_lt_one hL (j + 1)
  have h1x : 1 - x = 2 / (s + 1) := one_sub_gx hL j
  have h1y : 1 - y = 2 / (lam L * s + 1) := by
    rw [one_sub_gx hL (j + 1), pow_succ, mul_comm]
  have hx2 : 1 - x ^ 2 ≤ 4 / s := by
    have : 1 - x ^ 2 ≤ 2 * (1 - x) := by nlinarith
    rw [h1x] at this
    refine this.trans ?_
    rw [show 2 * (2 / (s + 1)) = 4 / (s + 1) by ring]
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have hy2 : 1 - y ^ 2 ≤ 4 / s := by
    have : 1 - y ^ 2 ≤ 2 * (1 - y) := by nlinarith
    rw [h1y] at this
    refine this.trans ?_
    rw [show 2 * (2 / (lam L * s + 1)) = 4 / (lam L * s + 1) by ring]
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by nlinarith)
  have hy3 : 2 / (3 * s) ≤ 1 - y ^ 2 := by
    have : 1 - y ≤ 1 - y ^ 2 := by nlinarith
    refine le_trans ?_ this
    rw [h1y]
    exact div_le_div_of_nonneg_left (by norm_num) (by nlinarith) (by nlinarith)
  have hbl : (bl L K j : ℝ) ≤ s / K := Nat.floor_le (by positivity)
  have hbu : (K : ℝ) * s - 1 < bu L K j := Nat.sub_one_lt_floor _
  have hbu' : (bu L K j : ℝ) ≤ K * s := Nat.floor_le (by positivity)
  have hsK : s / K ≤ s := div_le_self (by linarith) (by linarith)
  have hgap : (bl L K j : ℝ) + K * s / 2 ≤ bu L K j := by nlinarith
  have hlt : bl L K j < bu L K j := by
    have : (bl L K j : ℝ) < bu L K j := by nlinarith
    exact_mod_cast this
  have hM : (K : ℝ) * s / 2 ≤ ((bu L K j - bl L K j : ℕ) : ℝ) := by
    rw [Nat.cast_sub hlt.le]; linarith
  refine ⟨?_, hlt, ?_, hx2, hy2, hbl, ?_, ?_⟩
  · have : (bu L K j : ℝ) ≤ n := hbu'.trans hn
    have : bu L K j ≤ n := by exact_mod_cast this
    omega
  · -- `y^{2M} ≤ exp(-M(1-y²)) ≤ exp(-K/3) ≤ 3/K`
    set M := bu L K j - bl L K j
    have e1 : y ^ 2 ≤ Real.exp (-(1 - y ^ 2)) := by
      have := Real.add_one_le_exp (-(1 - y ^ 2)); linarith
    have e2 : (y ^ 2) ^ M ≤ Real.exp (-(1 - y ^ 2)) ^ M := pow_le_pow_left₀ (by positivity) e1 M
    rw [← Real.exp_nat_mul] at e2
    have e3 : (M : ℝ) * (-(1 - y ^ 2)) ≤ -(K / 3) := by
      have : (K : ℝ) * s / 2 * (2 / (3 * s)) = K / 3 := by field_simp
      have h1 : (K : ℝ) * s / 2 * (2 / (3 * s)) ≤ M * (1 - y ^ 2) :=
        mul_le_mul hM hy3 (by positivity) (by positivity)
      linarith
    have e4 : Real.exp (-(K / 3 : ℝ)) ≤ 3 / K := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
      have := Real.add_one_le_exp ((K : ℝ) / 3)
      rw [inv_div]; linarith
    exact e2.trans ((Real.exp_le_exp.2 e3).trans e4)
  · have h := one_add_mul_le_pow (a := x ^ 2 - 1) (by nlinarith) (bl L K j)
    rw [show 1 + (x ^ 2 - 1) = x ^ 2 by ring] at h
    have : (bl L K j : ℝ) * (1 - x ^ 2) ≤ s / K * (4 / s) :=
      mul_le_mul hbl hx2 (by nlinarith) (by positivity)
    have h4 : s / K * (4 / s) = 4 / K := by field_simp
    have : (4 : ℝ) / K ≤ 1 / 2 := by rw [div_le_iff₀ hKp]; linarith
    have e : (bl L K j : ℝ) * (x ^ 2 - 1) = -((bl L K j : ℝ) * (1 - x ^ 2)) := by ring
    linarith
  · have h := one_add_mul_le_pow (a := y ^ 2 - 1) (by nlinarith) (bl L K j)
    rw [show 1 + (y ^ 2 - 1) = y ^ 2 by ring] at h
    have : (bl L K j : ℝ) * (1 - y ^ 2) ≤ s / K * (4 / s) :=
      mul_le_mul hbl hy2 (by nlinarith) (by positivity)
    have h4 : s / K * (4 / s) = 4 / K := by field_simp
    have : (4 : ℝ) / K ≤ 1 / 2 := by rw [div_le_iff₀ hKp]; linarith
    have e : (bl L K j : ℝ) * (y ^ 2 - 1) = -((bl L K j : ℝ) * (1 - y ^ 2)) := by ring
    linarith

lemma one_sub_rho0_sq {L : ℕ} (hL : 1 ≤ L) : 1 - rho0 L ^ 2 = (1 / (2 * L + 1 : ℝ)) ^ 2 := by
  rw [rho0_sq hL]
  unfold lam
  have : (0 : ℝ) < L := by exact_mod_cast hL
  field_simp; ring

/-! ### One window -/

/-- Robust straddle of the block sums at the two endpoints. -/
def Xev (n L K j : ℕ) (τ : ℝ) (ε : Fin (n + 1) → ℤˣ) : Prop :=
  (τ * √(∑ i, wB n (bl L K j) (bu L K j) (gx L j) i ^ 2) < ssum ε (wB n (bl L K j) (bu L K j) (gx L j)) ∧
    ssum ε (wB n (bl L K j) (bu L K j) (gx L (j + 1)))
      < -(τ * √(∑ i, wB n (bl L K j) (bu L K j) (gx L (j + 1)) i ^ 2))) ∨
  (ssum ε (wB n (bl L K j) (bu L K j) (gx L j))
      < -(τ * √(∑ i, wB n (bl L K j) (bu L K j) (gx L j) i ^ 2)) ∧
    τ * √(∑ i, wB n (bl L K j) (bu L K j) (gx L (j + 1)) i ^ 2)
      < ssum ε (wB n (bl L K j) (bu L K j) (gx L (j + 1))))

/-- The outside sums are not small. -/
def bad (n L K j : ℕ) (τ : ℝ) (ε : Fin (n + 1) → ℤˣ) : Prop :=
  τ * √(∑ i, wB n (bl L K j) (bu L K j) (gx L j) i ^ 2) ≤ |ssum ε (wO n (bl L K j) (bu L K j) (gx L j))| ∨
  τ * √(∑ i, wB n (bl L K j) (bu L K j) (gx L (j + 1)) i ^ 2)
    ≤ |ssum ε (wO n (bl L K j) (bu L K j) (gx L (j + 1)))|

/-- A robust straddle with small outside sums is a sign change. -/
lemma sc_of_X {L K j : ℕ} {τ : ℝ} (ε : Fin (n + 1) → ℤˣ) (hX : Xev n L K j τ ε)
    (hb : ¬ bad n L K j τ ε) : sc ε L j = 1 := by
  unfold sc; rw [if_pos]
  unfold bad at hb
  push Not at hb
  obtain ⟨hb1, hb2⟩ := hb
  rw [ssum_split ε (bl L K j) (bu L K j) (gx L j), ssum_split ε (bl L K j) (bu L K j) (gx L (j + 1))]
  rw [abs_lt] at hb1 hb2
  rcases hX with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  · exact mul_neg_of_neg_of_pos (by linarith) (by linarith)

/-- Window lower bound for the robust straddle. -/
theorem win_low {L K j : ℕ} (hL : 1 ≤ L) (hK : 30 ≤ K) (hj : 1 ≤ j)
    (hn : (K : ℝ) * lam L ^ j ≤ n) {τ R w η₁ : ℝ} (hτ : 0 ≤ τ) (hw : 0 < w) (hR : τ + 2 * w < R)
    (hη0 : 0 ≤ η₁) (hη1 : η₁ ≤ 1 / 2) (h3 : 9 / K ≤ η₁ * (1 / (2 * L + 1 : ℝ)) ^ 2) :
    (1 - η₁) * (1 / (2 * L + 1 : ℝ)) / π - 4 * (τ + 2 * w) / √(2 * π) - 4 / R ^ 2
        - 2 * CqL τ R w * (10 / lam L ^ j) ≤ PP (Xev n L K j τ) := by
  obtain ⟨hbn, hlt, hY, hx2, hy2, -, -, -⟩ := grid_blk (n := n) hL hK hn
  set b := bl L K j
  set e := bu L K j
  set x := gx L j
  set y := gx L (j + 1)
  set s := lam L ^ j
  have hs1 : 1 ≤ s := lam_pow_ge_one hL j
  have hx0 : 0 < x := gx_pos hL hj
  have hxy : x ≤ y := (gx_lt_succ hL j).le
  have hy1 : y < 1 := gx_lt_one hL (j + 1)
  have hx1 : x < 1 := gx_lt_one hL j
  have hK0 : (30 : ℝ) ≤ K := by exact_mod_cast hK
  have hKp : (0 : ℝ) < K := by linarith
  set δ₀ : ℝ := 3 / K with hδdef
  have hδ0 : 0 ≤ δ₀ := by positivity
  have hδ1 : δ₀ ≤ 1 / 10 := by rw [hδdef, div_le_iff₀ hKp]; linarith
  have hδ : δ₀ < 1 := by linarith
  have hid := grid_identity hL j
  have hρ := rho0_pos hL
  have hcorr := blk_corr (n := n) b e hx0 hxy hy1 hid hρ hbn hlt hY hδ
  have hd0 : (0 : ℝ) < 1 / (2 * L + 1) := by positivity
  obtain ⟨hρ₁0, hρ₁1, harc⟩ := arccos_infl hρ (one_sub_rho0_sq hL) hd0 hδ0 hδ1 hη0 hη1
    (by rw [hδdef]; linarith [show 3 * (3 / (K : ℝ)) = 9 / K by ring])
  have hX : (x ^ 2) ^ (e - b) ≤ δ₀ :=
    le_trans (pow_le_pow_left₀ (by positivity) (by nlinarith) _) hY
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hSx := Gs_pos (n := n) b e (q := x ^ 2) (by positivity) (by nlinarith) hbn hlt
  have hSy := Gs_pos (n := n) b e (q := y ^ 2) (by positivity) (by nlinarith) hbn hlt
  have hC0 := Gs_nonneg (n := n) b e (q := x * y) (by positivity)
  have hP : 0 < Gs n b e (x ^ 2) * Gs n b e (y ^ 2) := mul_pos hSx hSy
  set ρ₁ := rho0 L / (1 - δ₀) with hρ₁def
  have hsq : √(Gs n b e (x ^ 2) * Gs n b e (y ^ 2)) ^ 2 = Gs n b e (x ^ 2) * Gs n b e (y ^ 2) :=
    Real.sq_sqrt hP.le
  have hlt' : Gs n b e (x * y) ^ 2 < Gs n b e (x ^ 2) * Gs n b e (y ^ 2) := by
    have h1 := pow_le_pow_left₀ hC0 hcorr 2
    rw [mul_pow, hsq] at h1
    have h2 : ρ₁ ^ 2 < 1 := pow_lt_one₀ hρ₁0 hρ₁1 two_ne_zero
    have h3 := mul_lt_mul_of_pos_right h2 hP
    rw [one_mul] at h3
    exact lt_of_le_of_lt h1 h3
  have key := pair_low (wB n b e x) (wB n b e y) (by rw [sum_wB_sq]; exact hSx)
    (by rw [sum_wB_sq]; exact hSy) (by rw [sum_wB_mul, sum_wB_sq, sum_wB_sq]; exact hlt')
    (by rw [sum_wB_mul]; exact hC0) (ρ₁ := ρ₁) (by rw [sum_wB_mul, sum_wB_sq, sum_wB_sq]; exact hcorr)
    hτ hw hR
  have key' : _ ≤ PP (Xev n L K j τ) := key
  have hd9 : (9 : ℝ) / 10 ≤ 1 - δ₀ := by linarith
  have hratio : ∀ z : ℝ, 1 - z ^ 2 ≤ 4 / s → (1 - z ^ 2) / (1 - δ₀) ≤ 5 / s := by
    intro z hz
    rw [div_le_iff₀ (by linarith)]
    have h45 : 4 / s ≤ 5 / s * (9 / 10) := by
      rw [show 5 / s * (9 / 10) = (9 / 2) / s by ring]
      exact div_le_div_of_nonneg_right (by norm_num) (by linarith)
    have := mul_le_mul_of_nonneg_left hd9 (show (0 : ℝ) ≤ 5 / s by positivity)
    linarith
  have r1 : (∑ i, wB n b e x i ^ 4) / (∑ i, wB n b e x i ^ 2) ^ 2 ≤ 5 / s := by
    rw [sum_wB_four, sum_wB_sq]
    exact (four_ratio b e hx0 hx1 hbn hlt hX hδ).trans (hratio x hx2)
  have r2 : (∑ i, wB n b e y i ^ 4) / (∑ i, wB n b e y i ^ 2) ^ 2 ≤ 5 / s := by
    rw [sum_wB_four, sum_wB_sq]
    exact (four_ratio b e hy0 hy1 hbn hlt hY hδ).trans (hratio y hy2)
  have hπ := Real.pi_pos
  have e1 : (1 - η₁) * (1 / (2 * L + 1 : ℝ)) / π ≤ Real.arccos ρ₁ / π :=
    div_le_div_of_nonneg_right harc hπ.le
  have hCq := CqL_nonneg τ R w
  have e2 : 2 * CqL τ R w * ((∑ i, wB n b e x i ^ 4) / (∑ i, wB n b e x i ^ 2) ^ 2
      + (∑ i, wB n b e y i ^ 4) / (∑ i, wB n b e y i ^ 2) ^ 2) ≤ 2 * CqL τ R w * (10 / s) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : (10 : ℝ) / s = 5 / s + 5 / s := by ring
    linarith
  refine le_trans ?_ key'
  linarith

lemma bad_pt (b e : ℕ) {z s K τ : ℝ} (hz0 : 0 < z) (hz1 : z < 1) (hbn : e ≤ n + 1) (hlt : b < e)
    (hK : 30 ≤ K) (hs : 0 < s) (hτ : 0 < τ)
    (hZ : (z ^ 2) ^ (e - b) ≤ 3 / K) (hz2 : 1 - z ^ 2 ≤ 4 / s) (hzb : 1 / 2 ≤ (z ^ 2) ^ b)
    (hbl : (b : ℝ) ≤ s / K) :
    PP (fun ε : Fin (n + 1) → ℤˣ => τ * √(∑ i, wB n b e z i ^ 2) ≤ |ssum ε (wO n b e z)|)
      ≤ 13 / (K * τ ^ 2) := by
  have hKp : 0 < K := by linarith
  have hq0 : 0 < z ^ 2 := by positivity
  have hq1 : z ^ 2 < 1 := by nlinarith
  have hS := Gs_pos (n := n) b e hq0 hq1 hbn hlt
  rw [sum_wB_sq]
  have ht : 0 < τ * √(Gs n b e (z ^ 2)) := mul_pos hτ (Real.sqrt_pos.2 hS)
  refine (cheb_ssum _ ht).trans ?_
  rw [mul_pow, Real.sq_sqrt hS.le]
  have hδ1 : 3 / K < 1 := by rw [div_lt_one hKp]; linarith
  have h1 := out_ratio (n := n) b e hz0 hz1 hbn hlt hZ hδ1
  have h2 := sum_wO_sq_le (n := n) b e hz0.le hz1
  have hd : (9 : ℝ) / 10 ≤ 1 - 3 / K := by
    have : 3 / K ≤ 1 / 10 := by rw [div_le_iff₀ hKp]; linarith
    linarith
  -- first term
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hnum : (b : ℝ) * (1 - z ^ 2) ≤ 4 / K := by
    calc (b : ℝ) * (1 - z ^ 2) ≤ s / K * (4 / s) :=
          mul_le_mul hbl hz2 (by linarith) (by positivity)
      _ = 4 / K := by field_simp
  have hden : (9 : ℝ) / 20 ≤ (z ^ 2) ^ b * (1 - 3 / K) := by
    have := mul_le_mul hzb hd (by norm_num) (by positivity)
    linarith
  have t1 : (b : ℝ) * (1 - z ^ 2) / ((z ^ 2) ^ b * (1 - 3 / K)) ≤ 80 / (9 * K) := by
    rw [div_le_iff₀ (by linarith)]
    have : 80 / (9 * K) * (9 / 20) = 4 / K := by field_simp; ring
    have := mul_le_mul_of_nonneg_left hden (show (0 : ℝ) ≤ 80 / (9 * K) by positivity)
    linarith
  have t2 : 3 / K / (1 - 3 / K) ≤ 10 / (3 * K) := by
    rw [div_le_iff₀ (by linarith)]
    have : 10 / (3 * K) * (9 / 10) = 3 / K := by field_simp; ring
    have := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 10 / (3 * K) by positivity)
    linarith
  have hsum : (∑ i, wO n b e z i ^ 2) / Gs n b e (z ^ 2) ≤ 13 / K := by
    have := div_le_div_of_nonneg_right h2 hS.le
    have e : 80 / (9 * K) + 10 / (3 * K) ≤ 13 / K := by
      rw [show 80 / (9 * K) + 10 / (3 * K) = (110 / 9) / K by field_simp; ring]
      exact div_le_div_of_nonneg_right (by norm_num) hKp.le
    linarith
  rw [show (∑ i, wO n b e z i ^ 2) / (τ ^ 2 * Gs n b e (z ^ 2))
      = ((∑ i, wO n b e z i ^ 2) / Gs n b e (z ^ 2)) / τ ^ 2 by field_simp,
    show 13 / (K * τ ^ 2) = 13 / K / τ ^ 2 by field_simp]
  exact div_le_div_of_nonneg_right hsum (by positivity)

/-- Window bound for the bad event. -/
theorem win_bad {L K j : ℕ} (hL : 1 ≤ L) (hK : 30 ≤ K) (hj : 1 ≤ j)
    (hn : (K : ℝ) * lam L ^ j ≤ n) {τ : ℝ} (hτ : 0 < τ) :
    PP (bad n L K j τ) ≤ 26 / (K * τ ^ 2) := by
  obtain ⟨hbn, hlt, hY, hx2, hy2, hbl, hxb, hyb⟩ := grid_blk (n := n) hL hK hn
  have hx0 : 0 < gx L j := gx_pos hL hj
  have hxy : gx L j ≤ gx L (j + 1) := (gx_lt_succ hL j).le
  have hy1 := gx_lt_one hL (j + 1)
  have hx1 := gx_lt_one hL j
  have hy0 : 0 < gx L (j + 1) := lt_of_lt_of_le hx0 hxy
  have hK' : (30 : ℝ) ≤ K := by exact_mod_cast hK
  have hs : 0 < lam L ^ j := by have := lam_pow_ge_one hL j; linarith
  have hX : (gx L j ^ 2) ^ (bu L K j - bl L K j) ≤ 3 / K :=
    le_trans (pow_le_pow_left₀ (by positivity) (by nlinarith) _) hY
  have p1 := bad_pt (n := n) (bl L K j) (bu L K j) hx0 hx1 hbn hlt hK' hs hτ hX hx2 hxb hbl
  have p2 := bad_pt (n := n) (bl L K j) (bu L K j) hy0 hy1 hbn hlt hK' hs hτ hY hy2 hyb hbl
  refine (PP_or_le _ _).trans ?_
  have : (26 : ℝ) / (K * τ ^ 2) = 13 / (K * τ ^ 2) + 13 / (K * τ ^ 2) := by ring
  linarith

/-- Indicators. -/
def Xi (n L K j : ℕ) (τ : ℝ) (ε : Fin (n + 1) → ℤˣ) : ℝ := by
  classical exact if Xev n L K j τ ε then 1 else 0

def Bi (n L K j : ℕ) (τ : ℝ) (ε : Fin (n + 1) → ℤˣ) : ℝ := by
  classical exact if bad n L K j τ ε then 1 else 0

lemma Xi_dep (L K j : ℕ) (τ : ℝ) : DepOn (blk n (bl L K j) (bu L K j)) (Xi n L K j τ) := by
  intro ε ε' h
  have e1 := ssum_wB_congr (bl L K j) (bu L K j) (gx L j) h
  have e2 := ssum_wB_congr (bl L K j) (bu L K j) (gx L (j + 1)) h
  unfold Xi Xev
  rw [e1, e2]

lemma Bi_dep (L K j : ℕ) (τ : ℝ) : DepOn (blk n (bl L K j) (bu L K j))ᶜ (Bi n L K j τ) := by
  intro ε ε' h
  have e1 := ssum_wO_congr (bl L K j) (bu L K j) (gx L j) h
  have e2 := ssum_wO_congr (bl L K j) (bu L K j) (gx L (j + 1)) h
  unfold Bi bad
  rw [e1, e2]

lemma EE_Xi (L K j : ℕ) (τ : ℝ) : EE (Xi n L K j τ) = PP (Xev n L K j τ) := by
  classical
  rw [PP_eq]; rfl

lemma EE_Bi (L K j : ℕ) (τ : ℝ) : EE (Bi n L K j τ) = PP (bad n L K j τ) := by
  classical
  rw [PP_eq]; rfl

lemma Xi_mem (L K j : ℕ) (τ : ℝ) (ε : Fin (n + 1) → ℤˣ) : 0 ≤ Xi n L K j τ ε ∧ Xi n L K j τ ε ≤ 1 := by
  unfold Xi; split_ifs <;> norm_num

lemma Bi_mem (L K j : ℕ) (τ : ℝ) (ε : Fin (n + 1) → ℤˣ) : 0 ≤ Bi n L K j τ ε ∧ Bi n L K j τ ε ≤ 1 := by
  unfold Bi; split_ifs <;> norm_num

lemma Xi_le_sc (L K j : ℕ) (τ : ℝ) (ε : Fin (n + 1) → ℤˣ) :
    Xi n L K j τ ε - Xi n L K j τ ε * Bi n L K j τ ε ≤ sc ε L j := by
  unfold Xi Bi
  by_cases hX : Xev n L K j τ ε
  · by_cases hb : bad n L K j τ ε
    · simp only [hX, hb, if_true]; have := sc_nonneg ε L j; linarith
    · simp only [hX, hb, if_true, if_false]; rw [sc_of_X ε hX hb]; norm_num
  · simp only [hX, if_false]; have := sc_nonneg ε L j; linarith

/-! ### Concentration of a sum of locally dependent indicators -/

section conc
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma DepOn.mono {A B : Finset ι} {f : (ι → ℤˣ) → ℝ} (h : DepOn A f) (hAB : A ⊆ B) : DepOn B f :=
  fun ε ε' hε => h ε ε' (fun i hi => hε i (hAB hi))

lemma DepOn.sub_const {A : Finset ι} {f : (ι → ℤˣ) → ℝ} (h : DepOn A f) (c : ℝ) :
    DepOn A (fun ε => f ε - c) := fun ε ε' hε => by simp only; rw [h ε ε' hε]

lemma EE_mem {f : (ι → ℤˣ) → ℝ} (h : ∀ ε, 0 ≤ f ε ∧ f ε ≤ 1) : 0 ≤ EE f ∧ EE f ≤ 1 := by
  constructor
  · exact EE_nonneg (fun ε => (h ε).1)
  · have := EE_mono (f := f) (g := fun _ => 1) (fun ε => (h ε).2); rwa [EE_const] at this

/-- **Variance of a sum with dependency range `r`.** -/
theorem var_local (W : Finset ℕ) (r : ℕ) (X : ℕ → (ι → ℤˣ) → ℝ) (A : ℕ → Finset ι)
    (hX : ∀ j ε, 0 ≤ X j ε ∧ X j ε ≤ 1) (hdep : ∀ j, DepOn (A j) (X j))
    (hdisj : ∀ j ∈ W, ∀ j' ∈ W, j + r ≤ j' → A j' ⊆ (A j)ᶜ) :
    EE (fun ε => (∑ j ∈ W, X j ε - ∑ j ∈ W, EE (X j)) ^ 2) ≤ 2 * r * W.card := by
  set Y : ℕ → (ι → ℤˣ) → ℝ := fun j ε => X j ε - EE (X j)
  have hY : ∀ j ε, |Y j ε| ≤ 1 := by
    intro j ε
    have h1 := hX j ε; have h2 := EE_mem (hX j)
    simp only [Y]; rw [abs_le]; constructor <;> linarith
  have hY0 : ∀ j, EE (Y j) = 0 := by
    intro j; simp only [Y]; rw [EE_sub, EE_const]; ring
  have hYdep : ∀ j, DepOn (A j) (Y j) := fun j => (hdep j).sub_const _
  have hfar : ∀ j ∈ W, ∀ j' ∈ W, j + r ≤ j' → EE (fun ε => Y j ε * Y j' ε) = 0 := by
    intro j hj j' hj' h
    rw [EE_mul_indep (A j) (Y j) (Y j') (hYdep j) ((hYdep j').mono (hdisj j hj j' hj' h)), hY0,
      zero_mul]
  have hpair : ∀ j ∈ W, ∀ j' ∈ W, EE (fun ε => Y j ε * Y j' ε)
      ≤ if j < j' + r ∧ j' < j + r then 1 else 0 := by
    intro j hj j' hj'
    by_cases h1 : j + r ≤ j'
    · rw [hfar j hj j' hj' h1, if_neg (by omega)]
    by_cases h2 : j' + r ≤ j
    · have : EE (fun ε => Y j ε * Y j' ε) = EE (fun ε => Y j' ε * Y j ε) := by
        congr 1; ext ε; ring
      rw [this, hfar j' hj' j hj h2, if_neg (by omega)]
    rw [if_pos (by omega)]
    have := EE_mono (f := fun ε => Y j ε * Y j' ε) (g := fun _ => (1 : ℝ)) (fun ε => by
      have := abs_mul (Y j ε) (Y j' ε)
      have h := mul_le_one₀ (hY j ε) (abs_nonneg _) (hY j' ε)
      have := le_abs_self (Y j ε * Y j' ε)
      linarith)
    rwa [EE_const] at this
  have hexp : ∀ ε, (∑ j ∈ W, X j ε - ∑ j ∈ W, EE (X j)) ^ 2
      = ∑ j ∈ W, ∑ j' ∈ W, Y j ε * Y j' ε := by
    intro ε
    rw [← Finset.sum_sub_distrib, sq, Finset.sum_mul_sum]
  simp_rw [hexp]
  rw [EE_sum]
  calc ∑ j ∈ W, EE (fun ε => ∑ j' ∈ W, Y j ε * Y j' ε)
      = ∑ j ∈ W, ∑ j' ∈ W, EE (fun ε => Y j ε * Y j' ε) := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [EE_sum]
    _ ≤ ∑ j ∈ W, ∑ j' ∈ W, (if j < j' + r ∧ j' < j + r then (1 : ℝ) else 0) :=
        Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun j' hj' => hpair j hj j' hj'))
    _ ≤ ∑ _j ∈ W, (2 * r : ℝ) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [Finset.sum_boole]
        have hsub : W.filter (fun j' => j < j' + r ∧ j' < j + r) ⊆ Finset.Ico (j - r) (j + r) := by
          intro j' hj'
          simp only [Finset.mem_filter, Finset.mem_Ico] at hj' ⊢
          omega
        have := Finset.card_le_card hsub
        rw [Nat.card_Ico] at this
        have h2 : j + r - (j - r) ≤ 2 * r := by omega
        exact_mod_cast this.trans h2
    _ = 2 * r * W.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end conc

/-! ### Assembly -/

lemma blk_disj {L K r j j' : ℕ} (hL : 1 ≤ L) (hK : 1 ≤ K) (hr : 2 * (K : ℝ) ^ 2 ≤ lam L ^ r)
    (h : j + r ≤ j') : blk n (bl L K j') (bu L K j') ⊆ (blk n (bl L K j) (bu L K j))ᶜ := by
  have hl := lam_gt hL
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hs1 : 1 ≤ lam L ^ j := lam_pow_ge_one hL j
  have hbu : (bu L K j : ℝ) ≤ K * lam L ^ j := Nat.floor_le (by positivity)
  have hbl : lam L ^ j' / K - 1 < bl L K j' := Nat.sub_one_lt_floor _
  have hpow : lam L ^ j * lam L ^ r ≤ lam L ^ j' := by
    rw [← pow_add]; exact pow_le_pow_right₀ hl.le h
  have h1 : 2 * K * lam L ^ j ≤ lam L ^ j' / K := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hr (show 0 ≤ lam L ^ j by positivity)
    nlinarith
  have hlt : (bu L K j : ℝ) < bl L K j' := by nlinarith
  have hlt' : bu L K j < bl L K j' := by exact_mod_cast hlt
  intro i hi
  simp only [blk, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [blk, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt]
  intro _; omega

lemma sum_inv_lam {L : ℕ} (hL : 1 ≤ L) (a b : ℕ) :
    ∑ j ∈ Finset.Ico a b, 1 / lam L ^ j ≤ L + 1 := by
  have hl := lam_gt hL
  have hq0 : 0 ≤ 1 / lam L := by positivity
  have hq1 : 1 / lam L < 1 := by rw [div_lt_one (by linarith)]; exact hl
  calc ∑ j ∈ Finset.Ico a b, 1 / lam L ^ j ≤ ∑ j ∈ Finset.range b, (1 / lam L) ^ j := by
        rw [show (fun j => 1 / lam L ^ j) = fun j => (1 / lam L) ^ j by ext j; rw [one_div_pow]]
        exact Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => by
          simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢; omega)
          (fun j _ _ => by positivity)
    _ ≤ 1 / (1 - 1 / lam L) := geom_range_le hq0 hq1 b
    _ = L + 1 := by
        unfold lam; have : (0 : ℝ) < L := by exact_mod_cast hL
        field_simp; ring

lemma log_lam_bounds {L : ℕ} (hL : 1 ≤ L) :
    1 / (L + 1 : ℝ) ≤ Real.log (lam L) ∧ Real.log (lam L) ≤ 1 / L := by
  have hl := lam_gt hL
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  constructor
  · have h := Real.log_le_sub_one_of_pos (show 0 < 1 / lam L by positivity)
    rw [Real.log_div (by norm_num) (by linarith), Real.log_one] at h
    have : 1 / lam L - 1 = -(1 / (L + 1 : ℝ)) := by unfold lam; field_simp; ring
    linarith
  · have h := Real.log_le_sub_one_of_pos (show 0 < lam L by linarith)
    unfold lam at h ⊢; linarith

lemma Jn_bounds {L n : ℕ} (hL : 1 ≤ L) (hn : 1 ≤ n) :
    (L : ℝ) * Real.log n - 1 ≤ Jn L n ∧ (Jn L n : ℝ) ≤ (L + 1) * Real.log n := by
  obtain ⟨h1, h2⟩ := log_lam_bounds hL
  have hl := lam_gt hL
  have hlog : 0 < Real.log (lam L) := Real.log_pos hl
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hx : 0 ≤ Real.log n / Real.log (lam L) := div_nonneg hln hlog.le
  have hA : (L : ℝ) * Real.log n ≤ Real.log n / Real.log (lam L) := by
    rw [le_div_iff₀ hlog]
    have : Real.log (lam L) * L ≤ 1 := by rw [le_div_iff₀ hL0] at h2; linarith
    nlinarith
  have hB : Real.log n / Real.log (lam L) ≤ (L + 1) * Real.log n := by
    rw [div_le_iff₀ hlog]
    have : 1 ≤ Real.log (lam L) * (L + 1) := by
      rw [div_le_iff₀ (by positivity)] at h1; linarith
    nlinarith
  constructor
  · have := Nat.lt_floor_add_one (Real.log n / Real.log (lam L))
    unfold Jn; linarith
  · have := Nat.floor_le hx
    unfold Jn; linarith

/-- The constants: for `L ≥ 1/η`, `τ = w = η'/(48L)`, `R = 3 + 8L/η'` (`η' = η/8`). -/
lemma consts {L η : ℝ} (hL : 1 ≤ L) (hη0 : 0 < η) (hη1 : η ≤ 1 / 100) (hLη : 1 / η ≤ L) :
    let η' := η / 8
    let τ := η' / (48 * L)
    let R := 3 + 8 * L / η'
    let d := 1 / (2 * L + 1)
    let p := (1 - η') * d / π
    let e₁ := 4 * (τ + 2 * τ) / √(2 * π) + 4 / R ^ 2
    L * e₁ ≤ η' ∧ 1 / (2 * π) - 2 * η' ≤ L * p ∧ 0 ≤ p - e₁ ∧ p ≤ 1 ∧ τ + 2 * τ < R ∧ 0 < τ := by
  intro η' τ R d p e₁
  have hπ3 := Real.pi_gt_three
  have hπ4 := Real.pi_lt_four
  have hL0 : 0 < L := by linarith
  have hη' : 0 < η' := by positivity
  have hτ : 0 < τ := by positivity
  have hsq : 1 ≤ √(2 * π) := by rw [Real.one_le_sqrt]; linarith
  have hR8 : 8 * L / η' ≤ R := by simp only [R]; linarith
  have h8 : 0 ≤ 8 * L / η' := by positivity
  have hR1 : 1 ≤ R := by simp only [R]; linarith
  have he1a : 4 * (τ + 2 * τ) / √(2 * π) ≤ 12 * τ := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have he1b : 4 / R ^ 2 ≤ η' / (2 * L) := by
    have : 4 / R ^ 2 ≤ 4 / R := by
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith); nlinarith
    refine this.trans ?_
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    have := mul_le_mul_of_nonneg_left hR8 (show (0 : ℝ) ≤ η' by positivity)
    rw [mul_div_cancel₀ _ hη'.ne'] at this
    nlinarith
  have h12 : 12 * τ = η' / (4 * L) := by simp only [τ]; field_simp; ring
  have hLe : L * e₁ ≤ η' := by
    simp only [e₁]
    have : L * (η' / (4 * L) + η' / (2 * L)) = 3 * η' / 4 := by field_simp; ring
    nlinarith
  have hd0 : 0 < d := by positivity
  have hLd : L * d / π ≤ 1 / (2 * π) := by
    simp only [d]; rw [div_le_div_iff₀ (by positivity) (by positivity)]
    field_simp; nlinarith
  have hgap : 1 / (2 * π) - L * d / π ≤ η' := by
    have : 1 / (2 * π) - L * d / π = 1 / (2 * π * (2 * L + 1)) := by
      simp only [d]; field_simp; ring
    rw [this, div_le_iff₀ (by positivity)]
    have hηL : 1 ≤ η * L := by rw [div_le_iff₀ hη0] at hLη; linarith
    simp only [η']; nlinarith
  have hp1 : L * p ≥ L * d / π - η' := by
    simp only [p]
    have : L * ((1 - η') * d / π) = L * d / π - η' * (L * d / π) := by ring
    rw [this]
    have h0 : 0 ≤ L * d / π := by positivity
    have : L * d / π ≤ 1 := hLd.trans (by rw [div_le_one (by positivity)]; linarith)
    nlinarith
  have hpd : p ≤ 1 := by
    simp only [p, d]
    rw [div_le_one (by positivity)]
    have : (1 - η') * (1 / (2 * L + 1)) ≤ 1 := by
      have : 1 / (2 * L + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      have : 0 ≤ 1 / (2 * L + 1) := by positivity
      have : η' ≤ 1 := by simp only [η']; linarith
      nlinarith
    linarith
  have hpe : 0 ≤ p - e₁ := by
    -- `p ≥ 1/(16 L)` and `e₁ ≤ η'/L ≤ 1/(800 L)`
    have hpL : 1 / (16 * L) ≤ p := by
      simp only [p, d]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : η' ≤ 1 / 800 := by simp only [η']; linarith
      field_simp
      have : π * (2 * L + 1) ≤ 12 * L := by nlinarith
      nlinarith
    have heL : e₁ ≤ η' / L := by rw [le_div_iff₀ hL0]; linarith
    have : η' / L ≤ 1 / (16 * L) := by
      rw [div_le_div_iff₀ hL0 (by positivity)]; simp only [η']; nlinarith
    linarith
  have hτ1 : τ ≤ η' := div_le_self hη'.le (by linarith)
  have hη'1 : η' ≤ 1 / 800 := by simp only [η']; linarith
  exact ⟨hLe, by linarith, hpe, hpd, by simp only [R]; linarith, hτ⟩

lemma det_step {Wc lg L C0 p e₁ e₂ η' S Z EZ V t c : ℝ} (hlow : L * lg - C0 ≤ Wc)
    (hpe : 0 ≤ p - e₁) (hp1 : p - e₁ ≤ 1) (hk : c - 3 * η' ≤ L * (p - e₁)) (hlg : 0 < lg)
    (hbig : C0 + e₂ < η' * lg) (hC0 : 0 ≤ C0) (hEZ : Wc * (p - e₁) - e₂ ≤ EZ)
    (ht : t = 2 * η' * lg) (h1 : -t < Z - EZ) (h2 : V < t) (hsc : Z - V ≤ S) :
    (c - 8 * η') * lg < S := by
  have a1 : (L * lg - C0) * (p - e₁) ≤ Wc * (p - e₁) := mul_le_mul_of_nonneg_right hlow hpe
  have a2 : lg * (c - 3 * η') ≤ lg * (L * (p - e₁)) := mul_le_mul_of_nonneg_left hk hlg.le
  have a3 : C0 * (p - e₁) ≤ C0 := mul_le_of_le_one_right hC0 hp1
  have a4 : (L * lg - C0) * (p - e₁) = lg * (L * (p - e₁)) - C0 * (p - e₁) := by ring
  have a5 : (c - 8 * η') * lg = lg * (c - 3 * η') - 5 * (η' * lg) := by ring
  rw [ht] at h1 h2
  linarith

set_option maxHeartbeats 1000000 in
/-- **Lower bound for the number of sign changes** (for small `η`). -/
theorem low_core (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1 / 100) : ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ ja : ℕ,
    ∀ᶠ n : ℕ in Filter.atTop, PP (ι := Fin (n + 1))
      (fun ε => ∑ j ∈ Finset.Ico ja (Jn L n), sc ε L j ≤ (1 / (2 * π) - η) * Real.log n) ≤ η := by
  refine ⟨⌈1 / η⌉₊ + 2, fun L hL ja => ?_⟩
  have hL1 : 1 ≤ L := by omega
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hLη : 1 / η ≤ (L : ℝ) := by
    have h1 := Nat.le_ceil (1 / η)
    have h2 : ((⌈1 / η⌉₊ : ℕ) : ℝ) ≤ L := by exact_mod_cast (by omega : ⌈1 / η⌉₊ ≤ L)
    linarith
  have hc := consts hLr hη0 hη1 hLη
  dsimp only at hc
  obtain ⟨hLe, hLp, hpe, hp1, hτR, hτ⟩ := hc
  set η' := η / 8 with hη'def
  set τ := η' / (48 * (L : ℝ)) with hτdef
  set R := 3 + 8 * (L : ℝ) / η' with hRdef
  set d := 1 / (2 * (L : ℝ) + 1) with hddef
  set p := (1 - η') * d / π with hpdef
  set e₁ := 4 * (τ + 2 * τ) / √(2 * π) + 4 / R ^ 2 with he₁def
  have hη'0 : 0 < η' := by positivity
  have hη'1 : η' ≤ 1 / 2 := by rw [hη'def]; linarith
  have hd0 : 0 < d := by positivity
  -- the block parameter `K`
  set Kr : ℝ := 30 + 9 / (η' * d ^ 2) + 26 * (L + 1) / (τ ^ 2 * η' * η) with hKr
  set K : ℕ := ⌈Kr⌉₊ with hKdef
  have hKK : Kr ≤ K := Nat.le_ceil Kr
  have hA1 : 0 ≤ 9 / (η' * d ^ 2) := by positivity
  have hA2 : 0 ≤ 26 * (L + 1) / (τ ^ 2 * η' * η) := by positivity
  have hK30r : (30 : ℝ) ≤ K := by linarith
  have hK30 : 30 ≤ K := by exact_mod_cast hK30r
  have hKp : (0 : ℝ) < K := by linarith
  have h9 : 9 / (K : ℝ) ≤ η' * (1 / (2 * L + 1 : ℝ)) ^ 2 := by
    rw [div_le_iff₀ hKp]
    have : 9 / (η' * d ^ 2) ≤ K := by linarith
    rw [div_le_iff₀ (by positivity)] at this
    rw [← hddef]; nlinarith
  have hβ : 26 / ((K : ℝ) * τ ^ 2) ≤ η' * η / (L + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 26 * (L + 1) / (τ ^ 2 * η' * η) ≤ K := by linarith
    rw [div_le_iff₀ (by positivity)] at this
    nlinarith
  obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt (2 * (K : ℝ) ^ 2) (lam_gt hL1)
  obtain ⟨r0, hr0⟩ := pow_unbounded_of_one_lt (K : ℝ) (lam_gt hL1)
  set j1 := max ja 1 with hj1
  set C0 : ℝ := 1 + r0 + j1 with hC0
  set e₂ : ℝ := 20 * CqL τ R τ * (L + 1) with he₂
  have hCq := CqL_nonneg τ R τ
  have hC00 : 0 ≤ C0 := by positivity
  have he₂0 : 0 ≤ e₂ := by positivity
  set A0 : ℝ := r * (L + 1) / (η' ^ 2 * η) + (C0 + e₂ + 1) / η' + 1 with hA0
  have hlogev : ∀ᶠ n : ℕ in Filter.atTop, A0 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop A0
  filter_upwards [hlogev, Filter.eventually_ge_atTop 2] with n hlog hn2
  have hn1 : 1 ≤ n := by omega
  have hB1 : 0 ≤ r * (L + 1) / (η' ^ 2 * η) := by positivity
  have hB2 : 0 ≤ (C0 + e₂ + 1) / η' := by positivity
  have hlpos : 0 < Real.log n := by linarith
  set lg := Real.log n with hlg
  set W := Finset.Ico j1 (Jn L n - r0) with hW
  have hl := lam_gt hL1
  have hWj : ∀ j ∈ W, 1 ≤ j ∧ (K : ℝ) * lam L ^ j ≤ n := by
    intro j hj
    rw [hW, Finset.mem_Ico] at hj
    refine ⟨by omega, ?_⟩
    calc (K : ℝ) * lam L ^ j ≤ lam L ^ r0 * lam L ^ j :=
          mul_le_mul_of_nonneg_right hr0.le (by positivity)
      _ = lam L ^ (r0 + j) := by rw [pow_add]
      _ ≤ lam L ^ Jn L n := pow_le_pow_right₀ hl.le (by omega)
      _ ≤ n := lam_pow_Jn_le hL1 hn1
  obtain ⟨hJlo, hJhi⟩ := Jn_bounds (n := n) hL1 hn1
  have hcard_lo : (L : ℝ) * lg - C0 ≤ W.card := by
    rw [hW, Nat.card_Ico]
    have : (Jn L n : ℝ) ≤ ((Jn L n - r0 - j1 : ℕ) : ℝ) + r0 + j1 := by
      exact_mod_cast (by omega : Jn L n ≤ Jn L n - r0 - j1 + r0 + j1)
    rw [hC0]; linarith
  have hcard_hi : (W.card : ℝ) ≤ (L + 1) * lg := by
    have : W.card ≤ Jn L n := by rw [hW, Nat.card_Ico]; omega
    have : (W.card : ℝ) ≤ Jn L n := by exact_mod_cast this
    linarith
  -- expectations
  have hEZ : (W.card : ℝ) * (p - e₁) - e₂ ≤ ∑ j ∈ W, EE (Xi n L K j τ) := by
    have hpw : ∀ j ∈ W, p - e₁ - 20 * CqL τ R τ * (1 / lam L ^ j) ≤ EE (Xi n L K j τ) := by
      intro j hj
      obtain ⟨hj1', hjn⟩ := hWj j hj
      have := win_low (n := n) hL1 hK30 hj1' hjn hτ.le hτ hτR hη'0.le hη'1 h9
      rw [EE_Xi]
      have e : 2 * CqL τ R τ * (10 / lam L ^ j) = 20 * CqL τ R τ * (1 / lam L ^ j) := by ring
      rw [he₁def, hpdef, hddef]
      linarith
    have hs := Finset.sum_le_sum hpw
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hs
    have hinv := sum_inv_lam hL1 j1 (Jn L n - r0)
    rw [← hW] at hinv
    have : 20 * CqL τ R τ * ∑ j ∈ W, 1 / lam L ^ j ≤ e₂ := by
      rw [he₂]; exact mul_le_mul_of_nonneg_left hinv (by positivity)
    linarith
  have hvar := var_local W r (fun j => Xi n L K j τ) (fun j => blk n (bl L K j) (bu L K j))
    (fun j ε => Xi_mem L K j τ ε) (fun j => Xi_dep L K j τ)
    (fun j _ j' _ h => blk_disj (n := n) hL1 (by omega) hr.le h)
  have hEV : EE (fun ε => ∑ j ∈ W, Xi n L K j τ ε * Bi n L K j τ ε) ≤ W.card * (26 / (K * τ ^ 2)) := by
    rw [EE_sum]
    calc ∑ j ∈ W, EE (fun ε => Xi n L K j τ ε * Bi n L K j τ ε)
        ≤ ∑ _j ∈ W, 26 / ((K : ℝ) * τ ^ 2) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          obtain ⟨hj1', hjn⟩ := hWj j hj
          rw [EE_mul_indep _ _ _ (Xi_dep L K j τ) (Bi_dep L K j τ), EE_Bi]
          have hb := win_bad (n := n) hL1 hK30 hj1' hjn hτ
          have hx := EE_mem (fun ε => Xi_mem (n := n) L K j τ ε)
          have hb0 := PP_nonneg (bad n L K j τ)
          nlinarith
      _ = W.card * (26 / (K * τ ^ 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
  set t := 2 * η' * lg with ht
  have ht0 : 0 < t := by positivity
  have hP1 : PP (fun ε : Fin (n + 1) → ℤˣ =>
      t ≤ |∑ j ∈ W, Xi n L K j τ ε - ∑ j ∈ W, EE (Xi n L K j τ)|) ≤ η / 2 := by
    refine (chebyshev _ ht0).trans ?_
    rw [div_le_iff₀ (by positivity)]
    refine hvar.trans ?_
    have hrl : (r : ℝ) * (L + 1) ≤ η * η' ^ 2 * lg := by
      have : r * (L + 1) / (η' ^ 2 * η) ≤ lg := by linarith
      rw [div_le_iff₀ (by positivity)] at this; linarith
    have hr0' : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    calc 2 * (r : ℝ) * W.card ≤ 2 * r * ((L + 1) * lg) := by gcongr
      _ = 2 * (r * (L + 1)) * lg := by ring
      _ ≤ 2 * (η * η' ^ 2 * lg) * lg := by gcongr
      _ = η / 2 * t ^ 2 := by rw [ht]; ring
  have hP2 : PP (fun ε : Fin (n + 1) → ℤˣ => t ≤ ∑ j ∈ W, Xi n L K j τ ε * Bi n L K j τ ε) ≤ η / 2 := by
    refine (markov (fun ε => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (Xi_mem L K j τ ε).1 (Bi_mem L K j τ ε).1)) ht0).trans ?_
    rw [div_le_iff₀ ht0]
    refine hEV.trans ?_
    calc (W.card : ℝ) * (26 / (K * τ ^ 2)) ≤ (L + 1) * lg * (η' * η / (L + 1)) := by
          apply mul_le_mul hcard_hi hβ (by positivity) (by positivity)
      _ = η / 2 * t := by rw [ht]; field_simp
  -- the deterministic step
  have hsub : ∀ ε : Fin (n + 1) → ℤˣ,
      ∑ j ∈ Finset.Ico ja (Jn L n), sc ε L j ≤ (1 / (2 * π) - η) * lg →
      t ≤ |∑ j ∈ W, Xi n L K j τ ε - ∑ j ∈ W, EE (Xi n L K j τ)| ∨
        t ≤ ∑ j ∈ W, Xi n L K j τ ε * Bi n L K j τ ε := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    rw [abs_lt] at h1
    have hsc : ∑ j ∈ W, Xi n L K j τ ε - ∑ j ∈ W, Xi n L K j τ ε * Bi n L K j τ ε
        ≤ ∑ j ∈ Finset.Ico ja (Jn L n), sc ε L j := by
      rw [← Finset.sum_sub_distrib]
      refine (Finset.sum_le_sum (fun j _ => Xi_le_sc L K j τ ε)).trans ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => by
          rw [hW, Finset.mem_Ico] at hj; rw [Finset.mem_Ico]; omega)
        (fun j _ _ => sc_nonneg ε L j)
    have hk : 1 / (2 * π) - 3 * η' ≤ (L : ℝ) * (p - e₁) := by
      have : (L : ℝ) * (p - e₁) = L * p - L * e₁ := by ring
      linarith
    have hp1' : p - e₁ ≤ 1 := by linarith [show 0 ≤ e₁ by positivity]
    have hbig : C0 + e₂ < η' * lg := by
      have : (C0 + e₂ + 1) / η' ≤ lg := by linarith
      rw [div_le_iff₀ hη'0] at this; linarith
    have e8 : η = 8 * η' := by rw [hη'def]; ring
    rw [e8] at hε
    exact absurd hε (not_le.mpr (det_step hcard_lo hpe hp1' hk hlpos hbig hC00 hEZ ht h1.1 h2 hsc))
  calc PP (fun ε : Fin (n + 1) → ℤˣ =>
        ∑ j ∈ Finset.Ico ja (Jn L n), sc ε L j ≤ (1 / (2 * π) - η) * lg)
      ≤ PP (fun ε : Fin (n + 1) → ℤˣ =>
          t ≤ |∑ j ∈ W, Xi n L K j τ ε - ∑ j ∈ W, EE (Xi n L K j τ)| ∨
            t ≤ ∑ j ∈ W, Xi n L K j τ ε * Bi n L K j τ ε) := PP_mono hsub
    _ ≤ _ := PP_or_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add hP1 hP2
    _ = η := by ring

/-- **Lower bound for the number of sign changes.** -/
theorem low_sc (η : ℝ) (hη : 0 < η) : ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ ja : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
    PP (ι := Fin (n + 1))
      (fun ε => ∑ j ∈ Finset.Ico ja (Jn L n), sc ε L j ≤ (1 / (2 * π) - η) * Real.log n) ≤ η := by
  obtain ⟨L₀, h⟩ := low_core (min η (1 / 100)) (lt_min hη (by norm_num)) (min_le_right _ _)
  refine ⟨L₀, fun L hL ja => ?_⟩
  filter_upwards [h L hL ja, Filter.eventually_ge_atTop 1] with n hn hn1
  refine le_trans (PP_mono (fun ε hε => ?_)) (hn.trans (min_le_left _ _))
  refine hε.trans (mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg (by exact_mod_cast hn1)))
  linarith [min_le_left η (1 / 100)]

end R522

end S_RRL

namespace R522

theorem lowSC_holds : LowSC := fun η hη => low_sc η hη

end R522

theorem OMA.solution : type_of% @Erdos522.erdos_522.variants.number_real_roots :=
  R522.final_of_quarter (R522.quarter_of_low R522.lowSC_holds)
