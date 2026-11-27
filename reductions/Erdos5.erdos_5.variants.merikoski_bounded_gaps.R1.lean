import FormalConjectures.ErdosProblems.«5»
import Mathlib

/-! Long empty intervals allow the construction of a strictly increasing sequence
all of whose positive differences miss a prescribed set. Thus any finite
prime-gap pattern theorem, including the four shifts of Merikoski or the nine
shifts of Banks, Freiberg and Maynard, suffices. -/

namespace OMA.R_Erdos5_erdos_5_variants_merikoski_bounded_gaps_R1

open Filter Set Real Erdos5
open scoped Topology

/-- A finite bound on the size of a family of nonnegative shifts whose differences
all fail to be subsequential limits, with the prime normalization. -/
def H1 : Prop := ∃ m : ℕ, ∀ β : Fin (m+1) → ℝ, (∀ i, 0 ≤ β i) → StrictMono β →
  ∃ i j, i < j ∧ ∃ n : ℕ → ℕ, StrictMono n ∧
    Tendsto (fun k => (primeGap (n k):ℝ) / log (Nat.nth Nat.Prime (n k))) atTop (𝓝 (β j-β i))

/-- Equivalence of the logarithmic prime and index scales. -/
def H2 : Prop := Tendsto (fun n : ℕ => log (Nat.nth Nat.Prime n) / log n) atTop (𝓝 1)

lemma avoid_differences (S : Set ℝ)
    (holes : ∀ C : ℝ, 0 ≤ C → ∃ T : ℝ, 0 ≤ T ∧ ¬ (S ∩ Icc T (T+C)).Nonempty) :
    ∃ b : ℕ → ℝ, StrictMono b ∧ (∀ i,0 ≤ b i) ∧ ∀ i j, i<j → b j-b i ∉ S := by
  classical
  have allholes (y : ℝ) := holes (max y 0 + 1) (by linarith [le_max_right y 0])
  choose T hT hempty using allholes
  let b : ℕ → ℝ := Nat.rec 0 (fun _ x => T x + x + 1)
  have step (i : ℕ) : b (i+1) = T (b i) + b i + 1 := rfl
  have mono : StrictMono b := strictMono_nat_of_lt_succ fun i => by rw [step]; linarith [hT (b i)]
  have pos (i : ℕ) : 0 ≤ b i := by exact mono.monotone (Nat.zero_le i)
  refine ⟨b,mono,pos,?_⟩
  intro i j hij hit
  obtain _|j := j
  · omega
  apply hempty (b j)
  refine ⟨b (j+1)-b i,hit,?_⟩
  have le := mono.monotone (show i≤j by omega)
  rw [step,max_eq_left (pos j)]
  exact ⟨by linarith,by linarith [pos i]⟩

theorem main : H1 → H2 → type_of% @Erdos5.erdos_5.variants.merikoski_bounded_gaps := by
  rintro ⟨m,patterns⟩ scale
  by_contra! holes
  obtain ⟨b,hmono,hpos,avoid⟩ := avoid_differences limitPointSet (by
    intro C hc
    obtain ⟨T,hT,he⟩ := holes C hc
    exact ⟨T,hT,by rw [he]; simp⟩)
  obtain ⟨i,j,hij,n,hn,limit⟩ := patterns (fun i => b i.val) (fun i => hpos i.val)
    (fun i j h => hmono (show i.val < j.val from h))
  apply avoid i.val j.val hij
  apply (mem_limitPointSet_iff _).2
  refine ⟨n,hn,?_⟩
  have h := limit.mul (scale.comp hn.tendsto_atTop)
  rw [mul_one] at h
  apply h.congr
  intro k
  have hp : 0 < log (Nat.nth Nat.Prime (n k)) :=
    Real.log_pos (by exact_mod_cast (Nat.prime_nth_prime (n k)).one_lt)
  simp [normalizedGap,div_mul_div_cancel₀,hp.ne']

end OMA.R_Erdos5_erdos_5_variants_merikoski_bounded_gaps_R1
