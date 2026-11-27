import FormalConjectures.ErdosProblems.«848»

/-!
# Finite endpoint reduction for Erdős 848

Between successive arrivals of the residue 7 modulo 25 the extremal
candidate has constant size. A counterexample therefore restricts to
exactly one more than that size and can be moved to the right endpoint.
Neither individual residue class 7 or 18 can contain the resulting set.
The intermediate hypothesis retains only these mixed witnesses.

The count of a residue class uses the Apache-2.0 formalization of Sawhney's
argument by Raymond Jung and contributors, commit
1cc2ac8e9d70516e979733c6ea5c4d2eb652d1f5 of
https://github.com/The-Obstacle-Is-The-Way/erdos-banger .
The small intervals have short finite colouring certificates. The explicit
tail bound quantifies the argument of Sawhney, using the Lean proof above.
A separate complete computational proof is available in A. C. Li's repository
https://github.com/crabsatellite/erdos-848-squarefree-product .
Endpoint reduction and finite-range formulation by @Deldor14.
-/

namespace OMA.R_Erdos848_erdos_848_R2
open Erdos848

lemma card_range_filter_mod25_eq (r : ℕ) (hr : r ≤ 24) (N : ℕ) :
    ((Finset.range N).filter (fun n => n % 25 = r)).card = (N + (24 - r)) / 25 := by
  classical
  have hr_lt : r < 25 := lt_of_le_of_lt hr (by decide : 24 < 25)
  set K : ℕ := (N + (24 - r)) / 25
  have hbij :
      ((Finset.range N).filter (fun n => n % 25 = r)).card = (Finset.range K).card := by
    refine (Finset.card_bij (s := Finset.range K) (t := (Finset.range N).filter (fun n => n % 25 = r))
      (i := fun k _hk => 25 * k + r) ?_ ?_ ?_).symm
    · intro k hk
      have hk' : k < K := by simpa [Finset.mem_range] using hk
      have hk1 : k + 1 ≤ K := Nat.succ_le_iff.2 hk'
      have hmul : 25 * (k + 1) ≤ 25 * K := Nat.mul_le_mul_left 25 hk1
      have hK : 25 * K ≤ N + (24 - r) := by
        simpa [K] using Nat.mul_div_le (N + (24 - r)) 25
      have hmul' : 25 * (k + 1) ≤ N + (24 - r) := le_trans hmul hK
      have hlt : 25 * k + r < N := by omega
      simp [Finset.mem_filter, Finset.mem_range, hlt, Nat.add_mod, hr_lt]
    · intro k₁ _hk₁ k₂ _hk₂ h
      have h' : 25 * k₁ = 25 * k₂ := Nat.add_right_cancel h
      exact Nat.mul_left_cancel (by decide : 0 < 25) h'
    · intro a ha
      have ha' : a < N ∧ a % 25 = r := by
        simpa [Finset.mem_filter, Finset.mem_range] using ha
      have ha_eq : 25 * (a / 25) + r = a := by
        have h := Nat.mod_add_div a 25
        simpa [ha'.2, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
      refine ⟨a / 25, ?_, ?_⟩
      · have hlt : 25 * (a / 25) + r < N := by simpa [ha_eq] using ha'.1
        have hmul : 25 * ((a / 25) + 1) ≤ N + (24 - r) := by omega
        have hle : a / 25 + 1 ≤ K := by
          have hmul' : (a / 25 + 1) * 25 ≤ N + (24 - r) := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
          have := (Nat.le_div_iff_mul_le (k0 := (by decide : 0 < 25))).2 hmul'
          simpa [K] using this
        have hltK : a / 25 < K := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hle
        simpa [Finset.mem_range] using hltK
      · exact ha_eq
  simpa [Finset.card_range, K] using hbij


/-- Finite initial intervals covered by explicit colour certificates. -/
def H1 : Prop := ∀ N : ℕ, N ≤ 20007 → Erdos848For N

/-- Only mixed sets of exactly k+1 points at the remaining endpoints need a squarefree pair. -/
def H2 : Prop := ∀ k : ℕ, 20007 < 25*k+7 → 25*k+7 < 2^4651 →
  ∀ B : Finset ℕ, B ⊆ Finset.range (25*k+7) → B.card = k+1 →
    (∃ a ∈ B, a % 25 ≠ 7) → (∃ b ∈ B, b % 25 ≠ 18) →
    ∃ a ∈ B, ∃ b ∈ B, Squarefree (a*b+1)

/-- An explicit sufficient threshold in the large-interval theorem. -/
def H3 : Prop := ∀ N : ℕ, 2^4651 ≤ N → Erdos848For N

theorem main : H1 → H2 → H3 → type_of% @Erdos848.erdos_848 := by
  intro small mixed large N A sub adm
  classical
  let k := (N+17)/25
  have card₇ (M : ℕ) : (A₇ M).card = (M+17)/25 :=
    card_range_filter_mod25_eq 7 (by decide) M
  rw [card₇]
  change A.card ≤ k
  by_contra! tooMany
  obtain ⟨B, subB, cardB⟩ := Finset.exists_subset_card_eq tooMany
  let M := 25*k+7
  have hNM : N ≤ M := by dsimp [M,k]; omega
  have subM : B ⊆ Finset.range M := fun n hn =>
    Finset.mem_range.mpr ((Finset.mem_range.mp (sub (subB hn))).trans_le hNM)
  have admB : NonSquarefreeProductProp B := fun _ ha _ hb => adm _ (subB ha) _ (subB hb)
  have bad : ¬Erdos848For M := by
    intro h
    have bound := h B subM admB
    rw [card₇,cardB] at bound
    dsimp [M] at bound
    omega
  have low : 20007 < M := lt_of_not_ge (fun h => bad (small M h))
  have high : M < 2^4651 := lt_of_not_ge (fun h => bad (large M h))
  have outside (r : ℕ) (hr : r = 7 ∨ r = 18) : ∃ a ∈ B, a % 25 ≠ r := by
    by_contra! h
    have subset : B ⊆ (Finset.range M).filter (fun n => n%25 = r) :=
      fun a ha => Finset.mem_filter.mpr ⟨subM ha, h a ha⟩
    have b := Finset.card_le_card subset
    rw [cardB, card_range_filter_mod25_eq r (by rcases hr with hr|hr <;> omega)] at b
    dsimp [M] at b
    rcases hr with rfl|rfl <;> omega
  obtain ⟨a,ha,b,hb,hpair⟩ := mixed k low high B subM cardB
    (outside 7 (Or.inl rfl)) (outside 18 (Or.inr rfl))
  exact admB a ha b hb hpair

end OMA.R_Erdos848_erdos_848_R2
