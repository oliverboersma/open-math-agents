import FormalConjectures.ErdosProblems.«968»
import Mathlib

/-! Maynard's small gaps theorem supplies arbitrarily late bounded intervals
containing at least three primes. Chebyshev's upper bound supplies the
zero density of the primes. Extracting consecutive primes from each
interval and comparing the two normalized gaps gives the required triples.
Reference: J. Maynard, Small gaps between primes, Ann. of Math. 181 (2015). -/

namespace OMA.R_Erdos968_erdos_968_variants_infinite_decreasingTriples_R1
open Filter Erdos968

def H1 : Prop := ∃ B : ℕ, ∀ X : ℕ, ∃ m ≥ X,
  3 ≤ ((Finset.Icc m (m + B)).filter Nat.Prime).card

def H2 : Prop := ∀ δ : ℝ, 0 < δ →
  ∀ᶠ x : ℕ in atTop, (x.primeCounting : ℝ) < δ * x

-- Converting the ordered elements of the interval to their global
-- prime indices allows the intermediate primes to be taken consecutive.
lemma get_cluster (B X : ℕ) (h : ∀ T : ℕ, ∃ m ≥ T,
    3 ≤ ((Finset.Icc m (m + B)).filter Nat.Prime).card) :
    ∃ i > X, Nat.nth Nat.Prime (i+2) ≤ Nat.nth Nat.Prime i + B := by
  have mono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  obtain ⟨m, hX, hm⟩ := h (Nat.nth Nat.Prime X + 1)
  let s := (Finset.Icc m (m+B)).filter Nat.Prime
  change 3 ≤ s.card at hm
  let f := s.orderEmbOfFin (k := s.card) rfl
  let a : Fin s.card := ⟨0, by omega⟩
  let b : Fin s.card := ⟨1, by omega⟩
  let c : Fin s.card := ⟨2, by omega⟩
  have item (j : Fin s.card) : (m ≤ f j ∧ f j ≤ m+B) ∧ Nat.Prime (f j) := by
    have mem : f j ∈ s := s.orderEmbOfFin_mem rfl j
    exact ⟨Finset.mem_Icc.mp (Finset.mem_filter.mp mem).1, (Finset.mem_filter.mp mem).2⟩
  obtain ⟨i, _, hi⟩ := Nat.exists_lt_card_nth_eq (item a).2
  obtain ⟨j, _, hj⟩ := Nat.exists_lt_card_nth_eq (item b).2
  obtain ⟨k, _, hk⟩ := Nat.exists_lt_card_nth_eq (item c).2
  have ij : i < j := mono.lt_iff_lt.mp (hi.trans_lt ((f.strictMono (show a < b by change (0:ℕ) < 1; decide)).trans_eq hj.symm))
  have jk : j < k := mono.lt_iff_lt.mp (hj.trans_lt ((f.strictMono (show b < c by change (1:ℕ) < 2; decide)).trans_eq hk.symm))
  have xi : X < i := mono.lt_iff_lt.mp (by rw [hi]; exact lt_of_lt_of_le (by omega : Nat.nth Nat.Prime X < m) (item a).1.1)
  refine ⟨i, xi, ?_⟩
  calc
    Nat.nth Nat.Prime (i+2) ≤ Nat.nth Nat.Prime k := mono.monotone (by omega)
    _ = f c := hk
    _ ≤ m + B := (item c).1.2
    _ ≤ Nat.nth Nat.Prime i + B := by rw [hi]; exact Nat.add_le_add_right (item a).1.1 B

lemma eventual_large (h : H2) (B : ℕ) :
    ∀ᶠ n : ℕ in atTop, (B:ℝ)*((n:ℝ)+1) < Nat.nth Nat.Prime n := by
  have pos : 0 < (B:ℝ)+1 := by positivity
  have t := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop
  filter_upwards [t.eventually (h (1/((B:ℝ)+1)) (by positivity))] with n hn
  have pc : (Nat.nth Nat.Prime n).primeCounting = n+1 := by
    change Nat.count Nat.Prime (Nat.nth Nat.Prime n + 1) = n+1
    rw [Nat.count_succ, if_pos (Nat.prime_nth_prime n)]
    exact congrArg (· + 1) (Nat.primeCounting'_nth_eq n)
  rw [pc] at hn
  push_cast at hn
  rw [one_div_mul_eq_div] at hn
  have hh := (lt_div_iff₀ pos).mp hn
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

lemma ratio_step (i B : ℕ) (bound : Nat.nth Nat.Prime (i+1) ≤ Nat.nth Nat.Prime i+B)
    (large : (B:ℝ)*((i:ℝ)+1) < Nat.nth Nat.Prime i) : u (i+1) < u i := by
  unfold u
  push_cast
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  have gap : (Nat.nth Nat.Prime (i+1):ℝ) ≤ Nat.nth Nat.Prime i + (B:ℝ) := by exact_mod_cast bound
  have scaled := mul_le_mul_of_nonneg_right gap (show 0 ≤ (i:ℝ)+1 by positivity)
  linarith only [scaled,large]

theorem main : H1 → H2 → type_of% @Erdos968.erdos_968.variants.infinite_decreasingTriples := by
  rintro ⟨B, clusters⟩ density
  obtain ⟨T, hT⟩ := eventually_atTop.1 (eventual_large density B)
  apply Set.infinite_of_forall_exists_gt
  intro x
  obtain ⟨i, big, small⟩ := get_cluster B (max T x) clusters
  have ti : T ≤ i := (le_max_left T x).trans big.le
  have mono := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
  have h01 := mono (show i ≤ i+1 by omega)
  have h12 := mono (show i+1 ≤ i+2 by omega)
  refine ⟨i, ⟨ratio_step i B (h12.trans small) (hT i ti), ?_⟩, (le_max_right T x).trans_lt big⟩
  exact ratio_step (i+1) B (small.trans (Nat.add_le_add_right h01 B)) (hT (i+1) (by omega))

end OMA.R_Erdos968_erdos_968_variants_infinite_decreasingTriples_R1
