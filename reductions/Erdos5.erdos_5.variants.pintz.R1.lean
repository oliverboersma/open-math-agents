import FormalConjectures.ErdosProblems.«5»
import Mathlib

/-! A finite pattern theorem only for rapidly separated shifts in the unit
interval suffices. If a closed set misses points arbitrarily close to zero
from the right, inductively choose smaller such points so that every positive
difference also stays in the open complement. -/

namespace OMA.R_Erdos5_erdos_5_variants_pintz_R1

open Erdos5 Filter Real Set
open scoped Topology

/-- A weak finite-shift sieve restricted to positive, lacunary shifts below one. -/
def H1 : Prop := ∃ m : ℕ, ∀ β : Fin (m+2) → ℝ, (∀ i, 0 < β i ∧ β i < 1) →
    (∀ i j, i<j → 2*β i < β j) → ∃ i j, i<j ∧ ∃ n : ℕ → ℕ, StrictMono n ∧
    Tendsto (fun k => (primeGap (n k):ℝ) / log (Nat.nth Nat.Prime (n k))) atTop (𝓝 (β j-β i))

/-- Prime and index logarithms are asymptotically equivalent. -/
def H2 : Prop := Tendsto (fun n : ℕ => log (Nat.nth Nat.Prime n) / log n) atTop (𝓝 1)

lemma avoid {S : Set ℝ} (closed : IsClosed S) (miss : ∃ᶠ x in 𝓝[>] (0:ℝ), x ∉ S)
    (m : ℕ) : ∃ β : Fin m → ℝ, (∀ i, 0 < β i ∧ β i < 1 ∧ β i ∉ S) ∧
      ∀ i j, i<j → 2*β i < β j ∧ β j-β i ∉ S := by
  induction m with
  | zero => exact ⟨Fin.elim0,(fun i => Fin.elim0 i),(fun i => Fin.elim0 i)⟩
  | succ m ih =>
    obtain ⟨β,hβ,old⟩ := ih
    have nb (i : Fin m) : ∀ᶠ y in 𝓝[>] (0:ℝ), 2*y < β i ∧ β i-y ∉ S := by
      have h₁ : ∀ᶠ y in 𝓝[>] (0:ℝ), y < β i/2 :=
        nhdsWithin_le_nhds (Iio_mem_nhds (by linarith [(hβ i).1]))
      have h₂ : Tendsto (fun y : ℝ => β i-y) (𝓝[>] 0) (𝓝 (β i)) := by
        have idh : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
        simpa only [sub_zero] using (tendsto_const_nhds (x := β i)).sub idh
      filter_upwards [h₁,h₂ (closed.isOpen_compl.mem_nhds (hβ i).2.2)] with y hy h
      exact ⟨by linarith,h⟩
    have near : ∀ᶠ y in 𝓝[>] (0:ℝ), y ∈ Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
    obtain ⟨y,hy,hy01,hyβ⟩ := (miss.and_eventually (near.and
      (eventually_all.mpr nb))).exists
    refine ⟨Fin.cons y β,?_,?_⟩
    · intro i
      exact Fin.cases ⟨hy01.1,hy01.2,hy⟩ hβ i
    · intro i j
      refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
      · intro h; exact (lt_irrefl _ h).elim
      · intro _; exact hyβ b
      · intro h; exact (Fin.not_lt_zero _ h).elim
      · intro h; exact old a b (Fin.succ_lt_succ_iff.mp h)

theorem main : H1 → H2 → type_of% @Erdos5.erdos_5.variants.pintz := by
  rintro ⟨m,sieve⟩ scale
  by_contra fail
  have miss : ∃ᶠ x in 𝓝[>] (0:ℝ), x ∉ limitPointSet := by
    by_contra! h
    obtain ⟨c,hc,hs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h
    apply fail
    exact ⟨c,hc,by rw [← closure_Ioo hc.ne]; exact isClosed_limitPointSet.closure_subset_iff.mpr hs⟩
  obtain ⟨β,hβ,avoid⟩ := avoid isClosed_limitPointSet miss (m+2)
  obtain ⟨i,j,hij,n,hn,hl⟩ := sieve β (fun i => ⟨(hβ i).1,(hβ i).2.1⟩)
    (fun i j h => (avoid i j h).1)
  apply (avoid i j hij).2
  apply (mem_limitPointSet_iff _).2
  refine ⟨n,hn,?_⟩
  have hh := hl.mul (scale.comp hn.tendsto_atTop)
  rw [mul_one] at hh
  apply hh.congr
  intro k
  have hp : 0 < log (Nat.nth Nat.Prime (n k)) :=
    Real.log_pos (by exact_mod_cast (Nat.prime_nth_prime (n k)).one_lt)
  simp [normalizedGap,div_mul_div_cancel₀,hp.ne']

end OMA.R_Erdos5_erdos_5_variants_pintz_R1
