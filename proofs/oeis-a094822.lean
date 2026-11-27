import OMAStatements.S_oeis_a094822
import Mathlib

namespace A094822
open OMA.S_oeis_a094822 Finset

lemma q_succ (n : ℕ) : q (n + 1) = (3 * (n : ℤ) + 1) * q n := by
  unfold q
  rw [Finset.prod_range_succ]
  ring

def D (n : ℕ) : ℤ :=
  ∑ ij ∈ antidiagonal n, (n.choose ij.1 : ℤ) * ((3 : ℤ) ^ ij.2 * q (ij.1 + 1))

def E (n : ℕ) : ℤ :=
  ∑ ij ∈ antidiagonal n, (ij.1 : ℤ) * ((n.choose ij.1 : ℤ) * ((3 : ℤ) ^ ij.2 * q ij.1))

lemma a_eq (n : ℕ) :
    a n = ∑ ij ∈ antidiagonal n, (n.choose ij.1 : ℤ) * ((3 : ℤ) ^ ij.2 * q ij.1) := rfl

lemma a_succ (n : ℕ) : a (n + 1) = 3 * a n + D n := by
  rw [a_eq, a_eq, D]
  rw [Finset.sum_antidiagonal_choose_succ_mul (fun i j => (3 : ℤ) ^ j * q i) n]
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro ij _
    ring
  · apply Finset.sum_congr rfl
    intro ij hij
    have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hc : n.choose ij.2 = n.choose ij.1 := by
      apply Nat.choose_symm_of_eq_add
      omega
    rw [hc]

lemma D_eq (n : ℕ) : D n = a n + 3 * E n := by
  rw [a_eq, D, E, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij _
  rw [q_succ]
  ring

lemma E_succ (m : ℕ) : E (m + 1) = ((m : ℤ) + 1) * D m := by
  rw [E, Finset.Nat.sum_antidiagonal_succ, D, Finset.mul_sum]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro ij _
  have h := Nat.add_one_mul_choose_eq m ij.1
  have h' : ((m : ℤ) + 1) * (m.choose ij.1 : ℤ) =
      ((m + 1).choose (ij.1 + 1) : ℤ) * ((ij.1 : ℤ) + 1) := by
    exact_mod_cast h
  push_cast
  calc ((ij.1 : ℤ) + 1) * (((m + 1).choose (ij.1 + 1) : ℤ) * ((3 : ℤ) ^ ij.2 * q (ij.1 + 1)))
      = (((m + 1).choose (ij.1 + 1) : ℤ) * ((ij.1 : ℤ) + 1)) * ((3 : ℤ) ^ ij.2 * q (ij.1 + 1)) := by
        ring
    _ = (((m : ℤ) + 1) * (m.choose ij.1 : ℤ)) * ((3 : ℤ) ^ ij.2 * q (ij.1 + 1)) := by rw [h']
    _ = ((m : ℤ) + 1) * ((m.choose ij.1 : ℤ) * ((3 : ℤ) ^ ij.2 * q (ij.1 + 1))) := by ring

lemma rec2 (m : ℕ) :
    a (m + 2) = (3 * (m : ℤ) + 7) * a (m + 1) - 9 * ((m : ℤ) + 1) * a m := by
  have h1 := a_succ (m + 1)
  have h2 := a_succ m
  have h3 := D_eq (m + 1)
  have h4 := E_succ m
  have e : m + 1 + 1 = m + 2 := by omega
  rw [e] at h1
  rw [h1, h3, h4]
  have h5 : D m = a (m + 1) - 3 * a m := by linarith
  rw [h5]
  ring

def st (k : ℕ) (n : ℕ) : ZMod k × ZMod k × ZMod k :=
  ((n : ZMod k), ((a n : ℤ) : ZMod k), ((a (n + 1) : ℤ) : ZMod k))

def step (k : ℕ) (s : ZMod k × ZMod k × ZMod k) : ZMod k × ZMod k × ZMod k :=
  (s.1 + 1, s.2.2, (3 * s.1 + 7) * s.2.2 - 9 * (s.1 + 1) * s.2.1)

lemma st_succ (k n : ℕ) : st k (n + 1) = step k (st k n) := by
  unfold st step
  have e : n + 1 + 1 = n + 2 := by omega
  rw [e, rec2 n]
  simp only [Prod.mk.injEq]
  refine ⟨by push_cast; ring, trivial, ?_⟩
  push_cast
  ring

lemma st_shift (k n1 n2 : ℕ) (h : st k n1 = st k n2) (t : ℕ) :
    st k (n1 + t) = st k (n2 + t) := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
    have e1 : n1 + (t + 1) = (n1 + t) + 1 := by omega
    have e2 : n2 + (t + 1) = (n2 + t) + 1 := by omega
    rw [e1, e2, st_succ, st_succ, ih]

lemma periodic (k : ℕ) (hk : 0 < k) : ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n →
    Int.ModEq (k : ℤ) (a (n + p)) (a n) := by
  have hne : NeZero k := ⟨by omega⟩
  obtain ⟨x, y, hxy, hst⟩ := Finite.exists_ne_map_eq_of_infinite (st k)
  have key : ∀ n1 n2 : ℕ, n1 < n2 → st k n1 = st k n2 →
      ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n → Int.ModEq (k : ℤ) (a (n + p)) (a n) := by
    intro n1 n2 hlt he
    refine ⟨n1, n2 - n1, by omega, ?_⟩
    intro n hn
    obtain ⟨t, rfl⟩ : ∃ t, n = n1 + t := ⟨n - n1, by omega⟩
    have hs := st_shift k n1 n2 he t
    have e : n1 + t + (n2 - n1) = n2 + t := by omega
    rw [e]
    have h2 : ((a (n2 + t) : ℤ) : ZMod k) = ((a (n1 + t) : ℤ) : ZMod k) := by
      have := congrArg (fun s => s.2.1) hs
      exact this.symm
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mp h2
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · exact key x y h hst
  · exact key y x h hst.symm

end A094822

theorem OMA.solution : type_of% @OMA.S_oeis_a094822.main := by
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have e1 : m + 2 - 1 = m + 1 := by omega
    have e2 : m + 2 - 2 = m := by omega
    rw [e1, e2, A094822.rec2 m]
    push_cast
    ring
  · intro k hk
    exact A094822.periodic k hk
