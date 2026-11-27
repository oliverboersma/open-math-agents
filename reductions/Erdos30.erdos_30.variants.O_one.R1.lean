import FormalConjectures.ErdosProblems.«30»

-- Reduction Erdos30.erdos_30.variants.O_one.R1 of Erdős Problem 30 — O one
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

open Filter
open scoped Asymptotics

namespace OMA.R_Erdos30_erdos_30_variants_O_one_R1

/-- Existence: m-mark Sidon sets of length m^2 + O(m), for m with m+1 and m+2 both composite
(the prime cases are covered by Ruzsa's construction, proved below). -/
def H1 : Prop :=
  ∃ c : ℕ, ∀ m : ℕ, ¬ (m + 1).Prime → ¬ (m + 2).Prime →
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (m ^ 2 + c * m) ∧ IsSidon (A : Set ℕ) ∧ A.card = m

/-- Length: any m-element Sidon subset of [1,N] forces m^2 ≤ N + O(m). -/
def H2 : Prop :=
  ∃ c : ℕ, ∀ N m : ℕ,
    (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSidon (A : Set ℕ) ∧ A.card = m) →
      m ^ 2 ≤ N + c * m

theorem fits_iff_le_h (N m : ℕ) : (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSidon (A : Set ℕ) ∧ A.card = m) ↔ m ≤ Erdos30.h N := by
  let candidates := (Finset.Icc 1 N).powerset.filter fun A : Finset ℕ ↦ IsSidon (A : Set ℕ)
  have mem_candidates (A : Finset ℕ) :
      A ∈ candidates ↔ A ⊆ Finset.Icc 1 N ∧ IsSidon (A : Set ℕ) := by
    simp [candidates]
  change (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSidon (A : Set ℕ) ∧ A.card = m) ↔ m ≤ candidates.sup Finset.card
  constructor
  · rintro ⟨A, hA, hS, rfl⟩
    exact Finset.le_sup (f := Finset.card) ((mem_candidates A).2 ⟨hA, hS⟩)
  · intro hm
    have hne : candidates.Nonempty := by
      refine ⟨∅, (mem_candidates ∅).2 ⟨Finset.empty_subset _, ?_⟩⟩
      simp [IsSidon]
    obtain ⟨A, hA, heq⟩ := Finset.exists_mem_eq_sup candidates hne Finset.card
    obtain ⟨B, hBA, hB⟩ := Finset.exists_subset_card_eq (heq ▸ hm)
    have ⟨hAint, hAS⟩ := (mem_candidates A).1 hA
    exact ⟨B, hBA.trans hAint, Set.IsSidon.subset hAS (fun _ hb ↦ hBA hb), hB⟩

theorem h_monotone : Monotone Erdos30.h := by
  intro N M hNM
  obtain ⟨A, hA, hS, hcard⟩ := (fits_iff_le_h N _).2 le_rfl
  exact (fits_iff_le_h M _).1
    ⟨A, hA.trans (Finset.Icc_subset_Icc_right hNM), hS, hcard⟩

theorem h_le_length (N : ℕ) : Erdos30.h N ≤ N := by
  obtain ⟨A, hA, _, hcard⟩ := (fits_iff_le_h N _).2 le_rfl
  rw [← hcard]
  exact (Finset.card_le_card hA).trans_eq (by simp)

theorem sqrt_bracket (N : ℕ) :
    (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) ∧
      Real.sqrt (N : ℝ) < (Nat.sqrt N : ℝ) + 1 := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' N
  · rw [← Nat.cast_one, ← Nat.cast_add]
    apply (Real.sqrt_lt' (by positivity)).2
    exact_mod_cast Nat.lt_succ_sqrt' N

theorem bounded_error_at_squares_iff :
    ((fun N : ℕ ↦ (Erdos30.h N : ℝ) - Real.sqrt (N : ℝ)) =O[atTop] fun _ ↦ (1 : ℝ)) ↔
      ∃ k : ℕ, ∀ m : ℕ, Erdos30.h (m ^ 2) ≤ m + k ∧ m ≤ Erdos30.h (m ^ 2) + k := by
  rw [Asymptotics.isBigO_iff]
  simp only [Real.norm_eq_abs, abs_one, mul_one, abs_sub_le_iff]
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hC
    obtain ⟨k, hk⟩ := exists_nat_ge C
    refine ⟨max k N₀, fun m ↦ ?_⟩
    by_cases hm : N₀ ≤ m ^ 2
    · have hs := hN₀ (m ^ 2) hm
      rw [Nat.cast_pow, Real.sqrt_sq (by positivity : 0 ≤ (m : ℝ))] at hs
      have hk' : C ≤ (↑(max k N₀) : ℝ) :=
        hk.trans (by exact_mod_cast le_max_left k N₀)
      exact ⟨by exact_mod_cast (show (Erdos30.h (m ^ 2) : ℝ) ≤ m + ↑(max k N₀) by linarith [hs.1]),
        by exact_mod_cast (show (m : ℝ) ≤ Erdos30.h (m ^ 2) + ↑(max k N₀) by linarith [hs.2])⟩
    · have hsmall : m ^ 2 ≤ max k N₀ := (Nat.le_of_lt (Nat.lt_of_not_ge hm)).trans (le_max_right _ _)
      have hm_sq : m ≤ m ^ 2 := by simpa [pow_two] using (Nat.le_mul_self m)
      have hh := (h_le_length (m ^ 2)).trans hsmall
      omega
  · rintro ⟨k, hk⟩
    refine ⟨(k : ℝ) + 1, Filter.Eventually.of_forall fun N ↦ ?_⟩
    have hlo := h_monotone (Nat.sqrt_le' N)
    have hhi := h_monotone (Nat.lt_succ_sqrt' N).le
    have hl : Nat.sqrt N ≤ Erdos30.h N + k :=
      (hk (Nat.sqrt N)).2.trans (Nat.add_le_add_right hlo _)
    have hh : Erdos30.h N ≤ (Nat.sqrt N + 1) + k :=
      hhi.trans (hk (Nat.sqrt N + 1)).1
    have hl' : (Nat.sqrt N : ℝ) ≤ (Erdos30.h N : ℝ) + k := by exact_mod_cast hl
    have hh' : (Erdos30.h N : ℝ) ≤ (Nat.sqrt N : ℝ) + 1 + k := by exact_mod_cast hh
    exact ⟨by linarith [(sqrt_bracket N).1], by linarith [(sqrt_bracket N).2]⟩

theorem square_envelope_iff_linear_packing :
    (∃ k : ℕ, ∀ m : ℕ, Erdos30.h (m ^ 2) ≤ m + k ∧ m ≤ Erdos30.h (m ^ 2) + k) ↔
      (∃ c : ℕ, (∀ m : ℕ, (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (m ^ 2 + c * m) ∧ IsSidon (A : Set ℕ) ∧ A.card = m)) ∧
    (∀ N m : ℕ, (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSidon (A : Set ℕ) ∧ A.card = m) → m ^ 2 ≤ N + c * m)) := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨2 * (k + 1) + k ^ 2, ?_, ?_⟩
    · intro m
      by_cases hm : m = 0
      · subst m
        exact ⟨∅, by simp, by simp [IsSidon], by simp⟩
      · have hneed : m ≤ Erdos30.h ((m + k) ^ 2) := by
          have := (hk (m + k)).2
          omega
        have hmul := Nat.le_mul_of_pos_right (k ^ 2) (Nat.pos_of_ne_zero hm)
        have hN : (m + k) ^ 2 ≤ m ^ 2 + (2 * (k + 1) + k ^ 2) * m := by
          nlinarith only [hmul, Nat.zero_le m]
        exact (fits_iff_le_h _ _).2 (hneed.trans (h_monotone hN))
    · intro N m hm
      let t := Nat.sqrt N
      have hfit := (fits_iff_le_h N m).1 hm
      have hsq := h_monotone (Nat.lt_succ_sqrt' N).le
      have hbound : m ≤ t + (k + 1) := by
        have := (hk (t + 1)).1
        change Erdos30.h N ≤ Erdos30.h ((t + 1) ^ 2) at hsq
        omega
      have ht : t ^ 2 ≤ N := Nat.sqrt_le' N
      rcases le_total m t with hmt | htm
      · exact (Nat.pow_le_pow_left hmt 2).trans (ht.trans (Nat.le_add_right _ _))
      · have hm1 := Nat.mul_le_mul_right m hbound
        have hm2 := Nat.mul_le_mul_right t hbound
        have hkt := Nat.mul_le_mul_left (k + 1) htm
        nlinarith only [hm1, hm2, hkt, ht, Nat.zero_le (k ^ 2 * m)]
  · rintro ⟨c, hpack, hlength⟩
    refine ⟨c, fun m ↦ ⟨?_, ?_⟩⟩
    · let a := Erdos30.h (m ^ 2)
      change a ≤ m + c
      have ha : a ^ 2 ≤ m ^ 2 + c * a :=
        hlength (m ^ 2) a ((fits_iff_le_h _ _).2 le_rfl)
      by_contra! h
      have hma : m ≤ a := by omega
      have ha_pos : 0 < a := by omega
      have hmul := Nat.mul_lt_mul_of_pos_right h ha_pos
      have hmul' := Nat.mul_le_mul_left m hma
      nlinarith only [ha, hmul, hmul']
    · by_cases hm : c ≤ m
      · let r := m - c
        have hr : r + c = m := Nat.sub_add_cancel hm
        have hN : r ^ 2 + c * r ≤ m ^ 2 := by
          calc
            r ^ 2 + c * r = (r + c) * r := by ring
            _ = m * r := by rw [hr]
            _ ≤ m ^ 2 := by simpa only [pow_two] using
              (Nat.mul_le_mul_left m (Nat.sub_le m c))
        have hfit := (fits_iff_le_h _ _).1 (hpack r)
        have hrle := hfit.trans (h_monotone hN)
        omega
      · omega

/-- Ruzsa's construction gives the linear packing bound when `m + 1` is prime. -/
theorem fits_before_prime (m : ℕ) (hp : (m + 1).Prime) :
    (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (m ^ 2 + m) ∧ IsSidon (A : Set ℕ) ∧ A.card = m) := by
  have : Fact (m + 1).Prime := ⟨hp⟩
  have hm : m ≠ 0 := by have := hp.two_le; omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (m + 1))ˣ)
  have hg_order : orderOf g = m := by
    rw [hg, Nat.card_eq_fintype_card, ZMod.card_units, Nat.add_sub_cancel]
  let u (i : Fin m) : ZMod (m + 1) := ↑(g ^ i.val : (ZMod (m + 1))ˣ)
  have u_injective : Function.Injective u := by
    intro i j hij
    have hgij : g ^ i.val = g ^ j.val := Units.ext hij
    have hmod := pow_eq_pow_iff_modEq.1 hgij
    rw [hg_order] at hmod
    exact Fin.ext (hmod.eq_of_lt_of_lt i.isLt j.isLt)
  have hcop : Nat.Coprime m (m + 1) := by
    simp [Nat.add_comm m 1, Nat.coprime_add_self_right]
  let r (i : Fin m) : ℕ := (Nat.chineseRemainder hcop i.val (u i).val).val
  have r_index (i : Fin m) : r i ≡ i.val [MOD m] :=
    (Nat.chineseRemainder hcop i.val (u i).val).property.1
  have r_value (i : Fin m) : (r i : ZMod (m + 1)) = u i := by
    have h := (Nat.chineseRemainder hcop i.val (u i).val).property.2
    exact ((ZMod.natCast_eq_natCast_iff ..).2 h).trans (ZMod.natCast_zmod_val _)
  let e : Fin m ↪ ℕ := ⟨fun i ↦ r i + 1, by
    intro i j h
    have hr : r i = r j := Nat.add_right_cancel h
    have hmod := (r_index i).symm.trans (hr.symm ▸ r_index j)
    exact Fin.ext (hmod.eq_of_lt_of_lt i.isLt j.isLt)⟩
  refine ⟨Finset.univ.map e, ?_, ?_, by simp⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 hx
    have hlt : r i < m * (m + 1) :=
      Nat.chineseRemainder_lt_mul hcop i.val (u i).val hm (by omega)
    apply Finset.mem_Icc.2
    change 1 ≤ r i + 1 ∧ r i + 1 ≤ m ^ 2 + m
    exact ⟨by omega, by nlinarith only [hlt]⟩
  · intro a ha b hb c hc d hd habcd
    obtain ⟨ia, _, rfl⟩ := Finset.mem_map.1 ha
    obtain ⟨ib, _, rfl⟩ := Finset.mem_map.1 hb
    obtain ⟨ic, _, rfl⟩ := Finset.mem_map.1 hc
    obtain ⟨id, _, rfl⟩ := Finset.mem_map.1 hd
    change r ia + 1 + (r ic + 1) = r ib + 1 + (r id + 1) at habcd
    have heq : r ia + r ic = r ib + r id := by omega
    have hsum := congrArg (fun n : ℕ ↦ (n : ZMod (m + 1))) heq
    simp only [Nat.cast_add, r_value] at hsum
    have hmod : ia.val + ic.val ≡ ib.val + id.val [MOD m] := by
      have hbd := (r_index ib).add (r_index id)
      rw [← heq] at hbd
      exact ((r_index ia).add (r_index ic)).symm.trans hbd
    have hpow : g ^ (ia.val + ic.val) = g ^ (ib.val + id.val) := by
      apply pow_eq_pow_iff_modEq.2
      rwa [hg_order]
    have hprod : u ia * u ic = u ib * u id := by
      simpa only [u, pow_add, Units.val_mul] using congrArg Units.val hpow
    have hzero : (u ia - u ib) * (u ia - u id) = 0 := by
      calc
        _ = u ia ^ 2 - u ia * (u ib + u id) + u ib * u id := by ring
        _ = 0 := by rw [← hsum, ← hprod]; ring
    rcases mul_eq_zero.mp hzero with hab | had
    · have hab' := sub_eq_zero.mp hab
      have hcd : u ic = u id := by
        rw [hab'] at hsum
        exact add_left_cancel hsum
      exact Or.inl ⟨congrArg e (u_injective hab'), congrArg e (u_injective hcd)⟩
    · have had' := sub_eq_zero.mp had
      have hcb : u ic = u ib := by
        rw [had', add_comm (u ib) (u id)] at hsum
        exact add_left_cancel hsum
      exact Or.inr ⟨congrArg e (u_injective had'), congrArg e (u_injective hcb)⟩

theorem fits_mono {N M m : ℕ} (hf : (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSidon (A : Set ℕ) ∧ A.card = m)) (hNM : N ≤ M) : (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 M ∧ IsSidon (A : Set ℕ) ∧ A.card = m) := by
  obtain ⟨A, hA, hS, hcard⟩ := hf
  exact ⟨A, hA.trans (Finset.Icc_subset_Icc_right hNM), hS, hcard⟩

theorem fits_near_prime (m d : ℕ)
    (hnear : ∃ q : ℕ, (q + 1).Prime ∧ m ≤ q ∧ q ≤ m + d) :
    (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (m ^ 2 + ((d + 1) ^ 2 + d) * m) ∧ IsSidon (A : Set ℕ) ∧ A.card = m) := by
  by_cases hm : m = 0
  · subst m
    exact ⟨∅, by simp, by simp [IsSidon], by simp⟩
  obtain ⟨q, hqp, hmq, hq⟩ := hnear
  have hmul := Nat.le_mul_of_pos_right (d ^ 2 + d) (Nat.pos_of_ne_zero hm)
  have hN : q ^ 2 + q ≤ m ^ 2 + ((d + 1) ^ 2 + d) * m := by
    calc
      _ ≤ (m + d) ^ 2 + (m + d) := Nat.add_le_add (Nat.pow_le_pow_left hq 2) hq
      _ ≤ _ := by nlinarith only [hmul]
  have hqm := (fits_iff_le_h _ _).1 (fits_before_prime q hqp)
  exact fits_mono ((fits_iff_le_h _ _).2 (hmq.trans hqm)) hN

/-- For the existence bound, sizes within a fixed distance below a prime predecessor are covered. -/
theorem linear_packing_iff_away_from_primes (d : ℕ) :
    (∃ c : ℕ, (∀ m : ℕ, (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (m ^ 2 + c * m) ∧ IsSidon (A : Set ℕ) ∧ A.card = m)) ∧
    (∀ N m : ℕ, (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSidon (A : Set ℕ) ∧ A.card = m) → m ^ 2 ≤ N + c * m)) ↔
      ∃ c : ℕ, (∀ m : ℕ, (∀ q : ℕ, m ≤ q → q ≤ m + d → ¬ (q + 1).Prime) →
        (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (m ^ 2 + c * m) ∧ IsSidon (A : Set ℕ) ∧ A.card = m)) ∧
      (∀ N m : ℕ, (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSidon (A : Set ℕ) ∧ A.card = m) → m ^ 2 ≤ N + c * m) := by
  constructor
  · rintro ⟨c, hpack, hlength⟩
    exact ⟨c, fun m _ ↦ hpack m, hlength⟩
  · rintro ⟨c, hpack, hlength⟩
    let D := (d + 1) ^ 2 + d
    have hc : c ≤ max c D := le_max_left _ _
    have hd : D ≤ max c D := le_max_right _ _
    refine ⟨max c D, ?_, fun N m hf ↦ ?_⟩
    · intro m
      by_cases hnear : ∃ q : ℕ, (q + 1).Prime ∧ m ≤ q ∧ q ≤ m + d
      · exact fits_mono (fits_near_prime m d hnear) (Nat.add_le_add_left (Nat.mul_le_mul_right m hd) _)
      · have hfar q hmq hqd hqp : False := hnear ⟨q, hqp, hmq, hqd⟩
        exact fits_mono (hpack m hfar) (Nat.add_le_add_left (Nat.mul_le_mul_right m hc) _)
    · exact (hlength N m hf).trans (Nat.add_le_add_left (Nat.mul_le_mul_right m hc) _)

theorem main : H1 → H2 → type_of% @Erdos30.erdos_30.variants.O_one := by
  rintro ⟨c1, h1⟩ ⟨c2, h2⟩
  apply bounded_error_at_squares_iff.2
  apply square_envelope_iff_linear_packing.2
  apply (linear_packing_iff_away_from_primes 1).2
  refine ⟨max c1 c2, fun m hm ↦ ?_, fun N m hf ↦ ?_⟩
  · have hp1 : ¬ (m + 1).Prime := hm m le_rfl (by omega)
    have hp2 : ¬ (m + 2).Prime := hm (m + 1) (by omega) le_rfl
    exact fits_mono (h1 m hp1 hp2)
      (Nat.add_le_add_left (Nat.mul_le_mul_right m (le_max_left _ _)) _)
  · exact (h2 N m hf).trans (Nat.add_le_add_left (Nat.mul_le_mul_right m (le_max_right _ _)) _)

end OMA.R_Erdos30_erdos_30_variants_O_one_R1
