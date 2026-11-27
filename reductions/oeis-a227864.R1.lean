import OMAStatements.S_oeis_a227864

-- Credit: @physbuzz
namespace OMA.R_oeis_a227864_R1
open OMA.S_oeis_a227864

lemma reversed_factor (b p : ℕ) (hp : p.Prime) (small : p < b) : reversal b (b*p) = p := by
  rw [reversal,Nat.digits_base_mul (hp.one_lt.trans small) hp.pos,Nat.digits_of_lt b p hp.ne_zero small]
  simp [Nat.ofDigits_cons]

theorem only_prime_square (n : ℕ) (hn : 2 ≤ n)
    (bad : ¬ ∃ b : ℕ, 2 ≤ b ∧ (reversal b n).Prime) : ∃ p : ℕ, p.Prime ∧ n = p^2 := by
  by_cases prime : n.Prime
  · apply False.elim
    apply bad
    refine ⟨n+1,by omega,?_⟩
    simpa [reversal,Nat.digits_of_lt (n+1) n prime.ne_zero (by omega)] using prime
  · let p := n.minFac
    let b := n/p
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have mult : b*p = n := Nat.div_mul_cancel (Nat.minFac_dvd n)
    have cmp : p ≤ b := Nat.minFac_le_div (by omega) prime
    obtain lt|eq := lt_or_eq_of_le cmp
    · exact False.elim (bad ⟨b, hp.two_le.trans cmp,by rwa [← mult,reversed_factor b p hp lt]⟩)
    · exact ⟨p,hp,by rw [← mult,← eq,pow_two]⟩

lemma four_bad : ¬ ∃ b : ℕ, 2 ≤ b ∧ (reversal b 4).Prime := by
  rintro ⟨b,hb,h⟩
  by_cases big : 4 < b
  · exact (by decide : ¬Nat.Prime 4) (by simpa [reversal,Nat.digits_of_lt b 4 (by decide) big] using h)
  · interval_cases b <;> revert h <;> decide +kernel


/-- In a base between p and p² the square has exactly two digits. -/
lemma two_digit_reversal (p b : ℕ) (hp : 2 ≤ p) (lo : p < b) (hi : b ≤ p^2) :
    reversal b (p^2) = (p^2 % b)*b + p^2/b := by
  have pos : 0 < p^2/b := Nat.div_pos hi (by omega)
  have low : p^2/b < b := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by nlinarith)
  have step := Nat.digits_def' (by omega : 1 < b) (by positivity : 0 < p^2)
  rw [reversal,step,Nat.digits_of_lt b _ (by omega) low]
  simp [Nat.ofDigits_cons,Nat.mul_comm,Nat.add_comm]

/-- A base larger than the square leaves a single composite digit. -/
lemma above_square (p b : ℕ) (hp : 2 ≤ p) (h : p^2 < b) :
    ¬(reversal b (p^2)).Prime := by
  simpa [reversal,Nat.digits_of_lt b (p^2) (by positivity) h]
    using (Nat.Prime.not_prime_pow (x := p) (by decide : 2 ≤ 2))

/-- The finite part asks for base certificates for the odd prime roots up to 2000. -/
def H1 : Prop := ∀ p : ℕ, 3 ≤ p → p ≤ 2000 → p.Prime →
    ∃ b : ℕ, 2 ≤ b ∧ (reversal b (p^2)).Prime

/-- If every two-digit candidate is composite, a large prime square has a witness
among the bases at most its root. Both base ranges are explicit and finite for each p. -/
def H2 : Prop := ∀ p : ℕ, 2000 < p → p.Prime →
    (∀ b : ℕ, p < b → b ≤ p^2 → ¬((p^2%b)*b + p^2/b).Prime) →
    ∃ b : ℕ, 2 ≤ b ∧ b ≤ p ∧ (reversal b (p^2)).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a227864.main := by
  intro small large
  ext n
  change (¬ ∃ b : ℕ, 2 ≤ b ∧ (reversal b n).Prime) ↔ n ∈ ({0,1,4} : Set ℕ)
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · intro bad
    by_cases hn : n < 2
    · omega
    obtain ⟨p,hp,rfl⟩ := only_prime_square n (by omega) bad
    by_cases two : p = 2
    · subst p
      decide
    have odd : 3 ≤ p := by have := hp.two_le; omega
    exfalso
    apply bad
    by_cases bound : p ≤ 2000
    · exact small p odd bound hp
    by_cases existsTwo : ∃ b : ℕ, p < b ∧ b ≤ p^2 ∧ ((p^2%b)*b + p^2/b).Prime
    · obtain ⟨b,lo,hi,w⟩ := existsTwo
      exact ⟨b,by omega,by rwa [two_digit_reversal p b hp.two_le lo hi]⟩
    · have noneTwo : ∀ b : ℕ, p < b → b ≤ p^2 → ¬((p^2%b)*b + p^2/b).Prime :=
        fun b lo hi w => existsTwo ⟨b,lo,hi,w⟩
      obtain ⟨b,hb,_,w⟩ := large p (by omega) hp noneTwo
      exact ⟨b,hb,w⟩
  · rintro (rfl|rfl|rfl)
    · rintro ⟨b,_,w⟩
      exact Nat.not_prime_zero (by simpa [reversal] using w)
    · rintro ⟨b,hb,w⟩
      exact Nat.not_prime_one (by simpa [reversal,Nat.digits_of_lt b 1 (by decide) hb] using w)
    · exact four_bad

end OMA.R_oeis_a227864_R1
