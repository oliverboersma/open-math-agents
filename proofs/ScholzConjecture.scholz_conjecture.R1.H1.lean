import OMAReductions.R_ScholzConjecture_scholz_conjecture_R1
import Mathlib

-- Step ScholzConjecture.scholz_conjecture.R1.H1: hypothesis H1 of reduction ScholzConjecture.scholz_conjecture.R1
-- Credit: @ivillar
-- H1: Brauer (1939). If n has an optimal star chain, then l(2^n - 1) ≤ n - 1 + l(n).
-- Proof: follow the star chain a_0 = 1 < ... < a_r = n with a_(i+1) = a_i + a_j.
-- From 2^(a_i) - 1, double a_j times and add 2^(a_j) - 1 (already in the chain),
-- reaching 2^(a_(i+1)) - 1 after a_j + 1 steps; in total (n - 1) + r steps.

namespace OMAScholzH1

theorem one_le_of_mem {L : List ℕ} (h1 : L.head? = some 1) (hp : L.Pairwise (· < ·))
    {x : ℕ} (hx : x ∈ L) : 1 ≤ x := by
  cases L with
  | nil => simp at hx
  | cons a t =>
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_rfl
    · exact le_of_lt ((List.pairwise_cons.mp hp).1 _ hx)

theorem key_identity (b j : ℕ) :
    (2 ^ b - 1) * 2 ^ j + (2 ^ j - 1) = 2 ^ (b + j) - 1 := by
  have hP : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hQ : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  rw [pow_add, Nat.sub_mul, one_mul]
  have : 2 ^ j ≤ 2 ^ b * 2 ^ j := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem key (ys : List ℕ) : ∀ a : ℕ, (ys ++ [a]).head? = some 1 →
    (ys ++ [a]).Pairwise (· < ·) →
    (∀ (i : ℕ) (hi : i + 1 < (ys ++ [a]).length), ∃ j ∈ ys ++ [a],
      (ys ++ [a])[i + 1] = (ys ++ [a])[i] + j) →
    ∃ D : List ℕ, IsAdditionChain D ∧ D.getLast? = some (2 ^ a - 1) ∧
      D.length = a + ys.length ∧ (∀ x ∈ D, x ≤ 2 ^ a - 1) ∧
      ∀ x ∈ ys ++ [a], 2 ^ x - 1 ∈ D := by
  induction ys using List.reverseRecOn with
  | nil =>
    intro a h1 _ _
    simp only [List.nil_append, List.head?_cons, Option.some.injEq] at h1
    subst h1
    refine ⟨[1], by decide, rfl, rfl, by simp, by simp⟩
  | append_singleton zs b ih =>
    intro a h1 hp hs
    have hpos : ∀ x ∈ zs ++ [b] ++ [a], 1 ≤ x := fun x hx => one_le_of_mem h1 hp hx
    have hb1 : 1 ≤ b := hpos b (by simp)
    have hp' : (zs ++ [b]).Pairwise (· < ·) := (List.pairwise_append.mp hp).1
    have hba : b < a := (List.pairwise_append.mp hp).2.2 b (by simp) a (by simp)
    have hleb : ∀ x ∈ zs ++ [b], x ≤ b := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact le_of_lt ((List.pairwise_append.mp hp').2.2 x h b (by simp))
      · simp at h
        omega
    have h1' : (zs ++ [b]).head? = some 1 := by
      cases zs with
      | nil => simpa using h1
      | cons c t => simpa using h1
    have hs' : ∀ (i : ℕ) (hi : i + 1 < (zs ++ [b]).length), ∃ j ∈ zs ++ [b],
        (zs ++ [b])[i + 1] = (zs ++ [b])[i] + j := by
      intro i hi
      have hi2 : i + 1 < (zs ++ [b] ++ [a]).length := by
        simp only [List.length_append, List.length_singleton] at hi ⊢
        omega
      obtain ⟨j, hj, heq⟩ := hs i hi2
      have e1 : (zs ++ [b] ++ [a])[i + 1] = (zs ++ [b])[i + 1] := List.getElem_append_left hi
      have e0 : (zs ++ [b] ++ [a])[i] = (zs ++ [b])[i] :=
        List.getElem_append_left (by omega)
      rw [e1, e0] at heq
      refine ⟨j, ?_, heq⟩
      have hle := hleb _ (List.getElem_mem hi)
      have hpos0 : 1 ≤ (zs ++ [b])[i] := hpos _ (List.mem_append_left _ (List.getElem_mem _))
      rcases List.mem_append.mp hj with h | h
      · exact h
      · simp at h
        omega
    obtain ⟨D, hD, hlast, hlen, hmax, hmem⟩ := ih b h1' hp' hs'
    have hi : zs.length + 1 < (zs ++ [b] ++ [a]).length := by simp
    obtain ⟨j, hj, heq⟩ := hs zs.length hi
    have ea : (zs ++ [b] ++ [a])[zs.length + 1] = a := by simp
    have eb : (zs ++ [b] ++ [a])[zs.length] = b := by simp
    rw [ea, eb] at heq
    have hj1 : 1 ≤ j := by omega
    have hjmem : j ∈ zs ++ [b] := by
      rcases List.mem_append.mp hj with h | h
      · exact h
      · simp at h
        omega
    have hjD : 2 ^ j - 1 ∈ D := hmem j hjmem
    have hbD : 2 ^ b - 1 ∈ D := hmem b (by simp)
    have hP : 1 ≤ 2 ^ b - 1 := by
      have : 2 ≤ 2 ^ b := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb1
      omega
    have hQ : 2 ≤ 2 ^ j := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
    have hid : (2 ^ b - 1) * 2 ^ j + (2 ^ j - 1) = 2 ^ a - 1 := by
      rw [heq]; exact key_identity b j
    let f : ℕ → ℕ := fun t => (2 ^ b - 1) * 2 ^ (t + 1)
    have hf_mono : ∀ s t, s < t → f s < f t := by
      intro s t hst
      exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by norm_num) (by omega)) (by omega)
    have hf_le : ∀ t, t < j → f t ≤ (2 ^ b - 1) * 2 ^ j := by
      intro t ht
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hf_gt : ∀ t, 2 ^ b - 1 < f t := by
      intro t
      have : 2 ≤ 2 ^ (t + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (t + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      show 2 ^ b - 1 < (2 ^ b - 1) * 2 ^ (t + 1)
      nlinarith
    have hf_lt_top : ∀ t, t < j → f t < 2 ^ a - 1 := by
      intro t ht
      have := hf_le t ht
      omega
    have hbtop : 2 ^ b - 1 < 2 ^ a - 1 := by
      have := hf_gt 0
      have := hf_lt_top 0 (by omega)
      omega
    let M : List ℕ := (List.range j).map f
    have hMmem : ∀ x, x ∈ M ↔ ∃ t, t < j ∧ f t = x := by
      intro x
      simp [M]
    refine ⟨D ++ M ++ [2 ^ a - 1], ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · -- head
      have hDne : D ≠ [] := by
        intro h
        rw [h] at hlast
        simp at hlast
      obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hDne
      have := hD.1
      simpa using this
    · -- strictly increasing
      rw [List.pairwise_append, List.pairwise_append]
      refine ⟨⟨hD.2.1, ?_, ?_⟩, by simp, ?_⟩
      · exact List.pairwise_map.mpr ((List.pairwise_lt_range (n := j)).imp
          (fun h => hf_mono _ _ h))
      · intro x hx y hy
        obtain ⟨t, -, rfl⟩ := (hMmem y).mp hy
        have := hmax x hx
        have := hf_gt t
        omega
      · intro x hx y hy
        simp only [List.mem_singleton] at hy
        subst hy
        rcases List.mem_append.mp hx with h | h
        · have := hmax x h
          omega
        · obtain ⟨t, ht, rfl⟩ := (hMmem x).mp h
          exact hf_lt_top t ht
    · -- every entry other than 1 is a sum of two entries
      intro x hx hx1
      rcases List.mem_append.mp hx with h | h
      · rcases List.mem_append.mp h with h | h
        · obtain ⟨y, hy, z, hz, rfl⟩ := hD.2.2 x h hx1
          exact ⟨y, by simp [hy], z, by simp [hz], rfl⟩
        · obtain ⟨t, ht, rfl⟩ := (hMmem x).mp h
          cases t with
          | zero =>
            refine ⟨2 ^ b - 1, by simp [hbD], 2 ^ b - 1, by simp [hbD], ?_⟩
            show (2 ^ b - 1) * 2 ^ (0 + 1) = 2 ^ b - 1 + (2 ^ b - 1)
            ring
          | succ s =>
            have hsM : f s ∈ M := (hMmem _).mpr ⟨s, by omega, rfl⟩
            refine ⟨f s, by simp [hsM], f s, by simp [hsM], ?_⟩
            show (2 ^ b - 1) * 2 ^ (s + 1 + 1) = (2 ^ b - 1) * 2 ^ (s + 1) + (2 ^ b - 1) * 2 ^ (s + 1)
            ring
      · simp only [List.mem_singleton] at h
        subst h
        have hlastM : f (j - 1) ∈ M := (hMmem _).mpr ⟨j - 1, by omega, rfl⟩
        refine ⟨f (j - 1), by simp [hlastM], 2 ^ j - 1, by simp [hjD], ?_⟩
        show 2 ^ a - 1 = (2 ^ b - 1) * 2 ^ (j - 1 + 1) + (2 ^ j - 1)
        rw [Nat.sub_add_cancel hj1, hid]
    · -- last entry
      simp
    · -- length
      simp only [List.length_append, List.length_singleton, M, List.length_map,
        List.length_range, hlen]
      omega
    · -- every entry is at most the last
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · rcases List.mem_append.mp h with h | h
        · have := hmax x h
          omega
        · obtain ⟨t, ht, rfl⟩ := (hMmem x).mp h
          exact le_of_lt (hf_lt_top t ht)
      · simp only [List.mem_singleton] at h
        omega
    · -- the Mersenne numbers of the star chain all occur
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left _ (List.mem_append_left _ (hmem x h))
      · simp only [List.mem_singleton] at h
        subst h
        simp

end OMAScholzH1

theorem OMA.solution : OMA.R_ScholzConjecture_scholz_conjecture_R1.H1 := by
  unfold OMA.R_ScholzConjecture_scholz_conjecture_R1.H1
  intro n hn ⟨cs, hc, hlast, hlen, hstar⟩
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  obtain ⟨D, hD, hDlast, hDlen, -, -⟩ := OMAScholzH1.key ys n hc.1 hc.2.1 hstar
  have hys : ys.length = additionChainLength n := by
    simp only [List.length_append, List.length_singleton] at hlen
    omega
  exact additionChainLength_le D hD hDlast (by rw [hDlen, hys]; omega)
