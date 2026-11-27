import OMAReductions.R_OeisA108129_conjecture_R1

-- PrimeGrid's Riesel table on November 27, 2026 listed 41 coefficients
-- without a known prime. The table partitions the two tasks. A proof of each
-- task must supply its own prime witnesses.
namespace OMA.R_OeisA108129_conjecture_R1_H2_R1

def H1 : Prop := ∀ k : ℕ, k ∈ ([23669, 31859, 38473, 46663, 67117, 74699, 81041, 121889,
      129007, 143047, 161669, 206231, 215443, 226153, 234343, 245561,
      250027, 315929, 319511, 324011, 325123, 327671, 336839, 342847,
      344759, 362609, 363343, 364903, 365159, 368411, 371893, 384539,
      386801, 397027, 409753, 444637, 470173, 474491, 477583, 485557,
      494743] : List ℕ) →
  ∃ m : ℕ, 0 < m ∧ (k * 2 ^ m - 1).Prime

def H2 : Prop := ∀ n : ℕ, 64 ≤ n → n < 254602 →
  (2 * n - 1) ∉ ([23669, 31859, 38473, 46663, 67117, 74699, 81041, 121889,
      129007, 143047, 161669, 206231, 215443, 226153, 234343, 245561,
      250027, 315929, 319511, 324011, 325123, 327671, 336839, 342847,
      344759, 362609, 363343, 364903, 365159, 368411, 371893, 384539,
      386801, 397027, 409753, 444637, 470173, 474491, 477583, 485557,
      494743] : List ℕ) →
  (∀ m : ℕ, 0 < m → m ≤ 512 → ¬ ((2 * n - 1) * 2 ^ m - 1).Prime) →
  ∃ m : ℕ, 512 < m ∧ ((2 * n - 1) * 2 ^ m - 1).Prime

set_option maxHeartbeats 4000000 in
lemma initial_segment (n : ℕ) (hn : 0 < n) (hn64 : n < 64) :
    ∃ m : ℕ, 0 < m ∧ ((2 * n - 1) * 2 ^ m - 1).Prime := by
  interval_cases n
  · exact ⟨2, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨2, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨2, by decide, by norm_num⟩
  · exact ⟨3, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨2, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨4, by decide, by norm_num⟩
  · exact ⟨3, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨4, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨2, by decide, by norm_num⟩
  · exact ⟨2, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨3, by decide, by norm_num⟩
  · exact ⟨2, by decide, by norm_num⟩
  · exact ⟨7, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨4, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨2, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨12, by decide, by norm_num⟩
  · exact ⟨3, by decide, by norm_num⟩
  · exact ⟨2, by decide, by norm_num⟩
  · exact ⟨4, by decide, by norm_num⟩
  · exact ⟨5, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨2, by decide, by norm_num⟩
  · exact ⟨7, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨2, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨3, by decide, by norm_num⟩
  · exact ⟨2, by decide, by norm_num⟩
  · exact ⟨5, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨4, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨3, by decide, by norm_num⟩
  · exact ⟨2, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨10, by decide, by norm_num⟩
  · exact ⟨3, by decide, by norm_num⟩
  · exact ⟨2, by decide, by norm_num⟩
  · exact ⟨10, by decide, by norm_num⟩
  · exact ⟨9, by decide, by norm_num⟩
  · exact ⟨2, by decide, by norm_num⟩
  · exact ⟨8, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨12, by decide, by norm_num⟩
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨2, by decide, by norm_num⟩
  · exact ⟨2, by decide, by norm_num⟩

theorem main : H1 → H2 → OMA.R_OeisA108129_conjecture_R1.H2 := by
  intro hlisted hrest n hn
  have has_prime : ∃ m : ℕ, 0 < m ∧ ((2 * n - 1) * 2 ^ m - 1).Prime := by
    by_contra hnone
    have hn64 : 64 ≤ n := by
      by_contra hsmall
      exact hnone (initial_segment n hn.1 (by omega))
    obtain ⟨m, hm, hp⟩ := hrest n hn64 hn.2
      (fun listed => hnone (hlisted _ listed))
      (fun e he _ hp => hnone ⟨e, he, hp⟩)
    exact hnone ⟨m, by omega, hp⟩
  obtain ⟨m, hm, hp⟩ := has_prime
  have hex : ∃ e : ℕ, e ≠ 0 ∧ ((2 * n - 1) * 2 ^ e - 1).Prime := ⟨m, by omega, hp⟩
  simp only [OeisA108129.a, if_neg (show n ≠ 0 by omega), dif_pos hex]
  omega

end OMA.R_OeisA108129_conjecture_R1_H2_R1
