import OMAReductions.R_SierpinskiNumber_prime_sierpinski_problem_R1

-- The two fixed witnesses are established computationally by PrimeGrid.
namespace OMA.R_SierpinskiNumber_prime_sierpinski_problem_R1_H2_R1

def H1 : Prop := (90527 * 2 ^ 9162167 + 1 : ℕ).Prime

def H2 : Prop := (168451 * 2 ^ 19375200 + 1 : ℕ).Prime

theorem main : H1 → H2 → OMA.R_SierpinskiNumber_prime_sierpinski_problem_R1.H2 := by
  intro h1 h2 k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl
  · exact ⟨9162167, h1⟩
  · exact ⟨19375200, h2⟩

end OMA.R_SierpinskiNumber_prime_sierpinski_problem_R1_H2_R1
