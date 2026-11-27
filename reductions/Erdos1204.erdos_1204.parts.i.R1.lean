import FormalConjectures.ErdosProblems.«1204»

/-! The admissible prime construction is adapted from laughingbear/erdos-1204-lean
at 89bf18e8bc33, under Apache-2.0. The common translation by the Chinese
remainder theorem is from this repository’s accepted A_lower proof at
dc8eacecf739faca4d4030407ac9507d5b873c2d. The sharp interval sieve
condition and asymptotic equivalence bridge are new. -/
open Erdos1204 Finset Filter
open scoped Topology Classical

/-- Choose a common translate avoiding zero at every small prime. -/
private theorem translate_avoiding (S : Finset ℕ) (hS : IsAdmissible S) (N : ℕ) :
    ∃ t : ℕ, 0 < t ∧ ∀ a ∈ S, ∀ p : ℕ, p.Prime → p ≤ N → ¬p ∣ t + a := by
  classical
  let P := (range (N+1)).filter Nat.Prime
  let r (p : ℕ) : ZMod p := if h : p.Prime then (hS p h).choose else 0
  let b (p : ℕ) : ℕ := (-r p - 1).val
  obtain ⟨u, hu⟩ := Nat.chineseRemainderOfFinset b id P
    (fun p hp => (mem_filter.mp hp).2.ne_zero)
    (fun p hp q hq hpq => (Nat.coprime_primes (mem_filter.mp hp).2 (mem_filter.mp hq).2).2 hpq)
  refine ⟨u + 1, by omega, ?_⟩
  intro a ha p hp hpN hd
  have : Fact p.Prime := ⟨hp⟩
  have hu' : (u : ZMod p) = -r p - 1 := by
    have h := (ZMod.natCast_eq_natCast_iff u (b p) p).2 (hu p (mem_filter.mpr ⟨mem_range.mpr (by omega), hp⟩))
    simpa [b] using h
  have hz := (ZMod.natCast_eq_zero_iff _ _).2 hd
  push_cast at hz
  rw [hu'] at hz
  have ha' : (a : ZMod p) = r p := by linear_combination hz
  exact (hS p hp).choose_spec a ha (by simpa [r, hp] using ha')

namespace OMA.R_Erdos1204_erdos_1204_parts_i_R1

/-- Uniform sharp upper sieve on intervals shorter than (1−ε)k log k. -/
def H1 : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∀ m t : ℕ,
    (m : ℝ) < (1-ε) * k * Real.log k →
      ((Icc 0 m).filter (fun a => ∀ p : ℕ, p.Prime → p ≤ k → ¬ p ∣ t+a)).card < k

/-- There are enough primes just above k for the upper bound construction. -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
    k ≤ ((Ioc k ⌊(1+ε) * k * Real.log k⌋₊).filter Nat.Prime).card

private lemma prime_packet_admissible {S : Finset ℕ} {k : ℕ} (hc : S.card = k)
    (hS : ∀ a ∈ S, k < a ∧ a.Prime) : IsAdmissible S := by
  intro q hq
  by_cases hqk : q ≤ k
  · refine ⟨0, fun a ha h0 => ?_⟩
    have he := (Nat.prime_dvd_prime_iff_eq hq (hS a ha).2).1 ((ZMod.natCast_eq_zero_iff _ _).1 h0)
    have := (hS a ha).1
    omega
  · letI : NeZero q := ⟨hq.ne_zero⟩
    obtain ⟨r,hr⟩ : ∃ r : ZMod q, r ∉ S.image (fun a : ℕ => (a : ZMod q)) := by
      by_contra! hall
      have hsub : (univ : Finset (ZMod q)) ⊆ S.image (fun a : ℕ => (a : ZMod q)) := fun r _ => hall r
      have h := (card_le_card hsub).trans card_image_le
      rw [card_univ, ZMod.card, hc] at h
      omega
    exact ⟨r, fun a ha he => hr (mem_image.mpr ⟨a,ha,he⟩)⟩

theorem main : H1 → H2 → type_of% @Erdos1204.erdos_1204.parts.i := by
  classical
  intro hs hp
  have hpos : ∀ᶠ k : ℕ in atTop, 0 < (k : ℝ) * Real.log k := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with k hk
    have hk' : (1 : ℝ) < k := by exact_mod_cast hk
    exact mul_pos (by linarith) (Real.log_pos hk')
  apply (Asymptotics.isEquivalent_iff_tendsto_one (hpos.mono fun k hk => hk.ne')).2
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hh : 0 < ε/2 := by linarith
  filter_upwards [hs (ε/2) hh, hp (ε/2) hh, hpos] with k hshort hprime hL
  let M := ⌊(1+ε/2) * k * Real.log k⌋₊
  obtain ⟨S,hsub,hcard⟩ := Finset.exists_subset_card_eq hprime
  have hS (a : ℕ) (ha : a ∈ S) : k < a ∧ a.Prime := by
    have hx := mem_filter.mp (hsub ha)
    exact ⟨(mem_Ioc.mp hx.1).1,hx.2⟩
  have hmax (a : ℕ) (ha : a ∈ S) : a ≤ M := (mem_Ioc.mp (mem_filter.mp (hsub ha)).1).2
  have had := prime_packet_admissible hcard hS
  have hA := A_le hcard had hmax
  have hreal : (A k : ℝ) ≤ (1+ε/2) * k * Real.log k := by
    have hn : 0 ≤ (1+ε/2) * ((k : ℝ) * Real.log k) := mul_nonneg (by linarith) hL.le
    exact (show (A k : ℝ) ≤ M by exact_mod_cast hA).trans
      (Nat.floor_le (by linarith [show (1+ε/2) * (k : ℝ) * Real.log k = (1+ε/2) * ((k : ℝ)*Real.log k) by ring]))
  have hne : ({m : ℕ | ∃ T : Finset ℕ, T.card = k ∧ IsAdmissible T ∧ ∀ a ∈ T, a ≤ m}).Nonempty :=
    ⟨M, S, hcard, had, hmax⟩
  obtain ⟨T,hT,hTad,hTM⟩ : ∃ T : Finset ℕ, T.card = k ∧ IsAdmissible T ∧ ∀ a ∈ T, a ≤ A k :=
    Nat.sInf_mem hne
  have hlo : (1-ε/2) * k * Real.log k ≤ (A k : ℝ) := by
    by_contra! h
    obtain ⟨t,_,ht⟩ := translate_avoiding T hTad k
    have hsub' : T ⊆ (Icc 0 (A k)).filter (fun a => ∀ p : ℕ, p.Prime → p ≤ k → ¬p ∣ t+a) :=
      fun a ha => mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,hTM a ha⟩,ht a ha⟩
    have hh' := (card_le_card hsub').trans_lt (hshort _ _ h)
    omega
  change dist ((A k : ℝ) / ((k : ℝ) * Real.log k)) 1 < ε
  rw [Real.dist_eq, abs_lt]
  have hlo' : 1-ε/2 ≤ (A k : ℝ) / ((k : ℝ) * Real.log k) := (le_div_iff₀ hL).2 (by simpa only [mul_assoc] using hlo)
  have hup' : (A k : ℝ) / ((k : ℝ) * Real.log k) ≤ 1+ε/2 := (div_le_iff₀ hL).2 (by simpa only [mul_assoc] using hreal)
  constructor <;> linarith
end OMA.R_Erdos1204_erdos_1204_parts_i_R1
