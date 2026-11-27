import OMAStatements.S_oeis_a083137

namespace OMA.S_oeis_a083137

private theorem pal_power {e : ℕ} (he : 0 < e) : palindrome (10^e+1) := by
  obtain ⟨j,hj⟩ : ∃ j, e = 1+j := ⟨e-1, by omega⟩
  have h := Nat.digits_append_zeroes_append_digits (b:=10) (n:=1) (m:=1) (k:=j) (by decide) (by decide)
  have hone : Nat.digits 10 1 = [1] := by decide
  rw [hone] at h
  simp only [List.length_singleton, mul_one] at h
  rw [palindrome, hj, Nat.add_comm (10^(1+j)) 1, ← h]
  simp

-- For any positive b ≤ M the two numbers b and 10^((M+1)!)+1 are coprime.
-- Every prime divisor of b coprime to ten sees the latter number as two.
private theorem avoid (M b : ℕ) (hb : 0 < b) (hbM : b ≤ M) :
    (10^((M+1).factorial)+1).Coprime b := by
  by_contra h
  obtain ⟨p, hp, hx, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have he : (M+1).factorial ≠ 0 := Nat.factorial_ne_zero _
  by_cases hten : p ∣ 10
  · have hpw : p ∣ 10^((M+1).factorial) := hten.trans (dvd_pow_self _ he)
    have := Nat.dvd_sub hx hpw
    simp only [Nat.add_sub_cancel_left] at this
    exact hp.not_dvd_one this
  · have hpm := Nat.le_of_dvd hb hpb
    have hp2 := hp.two_le
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (by omega : 0 < p-1) (by omega : p-1 ≤ M+1)
    have hpw := (Nat.ModEq.pow_card_sub_one_eq_one hp (hp.coprime_iff_not_dvd.mpr hten).symm).pow c
    have heq : 10^((M+1).factorial)+1 ≡ 2 [MOD p] := by
      rw [hc, pow_mul]
      simpa using hpw.add_right 1
    exact hten (((heq.dvd_iff (dvd_refl p)).mp hx).trans (by decide : 2 ∣ 10))

private def good (l : List ℕ) (x : ℕ) : Prop :=
  0 < x ∧ palindrome x ∧ ∀ b ∈ l, b < x ∧ (0 < b → x.Coprime b)

private theorem extend (l : List ℕ) : ∃ x, good l x := by
  let e := (l.sum+1).factorial
  have he : 0 < e := Nat.factorial_pos _
  have hbound : l.sum < 10^e+1 := by
    have h₀ : l.sum+1 ≤ e := Nat.self_le_factorial _
    have h₁ : e < 10^e := Nat.lt_pow_self (by decide)
    omega
  refine ⟨10^e+1, by omega, pal_power he, ?_⟩
  intro b hb
  have hle : b ≤ l.sum := List.le_sum_of_mem hb
  exact ⟨lt_of_le_of_lt hle hbound, fun hbpos => avoid _ _ hbpos hle⟩

private noncomputable def pick (l : List ℕ) : ℕ := by
  classical
  exact Nat.find (extend l)

private theorem spec (l : List ℕ) : good l (pick l) := by
  classical
  exact Nat.find_spec (extend l)

private theorem least (l : List ℕ) {p : ℕ} (hp : good l p) : pick l ≤ p := by
  classical
  exact Nat.find_min' (extend l) hp

private noncomputable def prior : ℕ → List ℕ
  | 0 => []
  | n+1 => pick (prior n) :: prior n

private noncomputable def a (n : ℕ) := pick (prior n)

private theorem in_prior (n x : ℕ) : x ∈ prior n ↔ ∃ i < n, a i = x := by
  induction n with
  | zero => simp [prior]
  | succ n ih =>
    change x ∈ a n :: prior n ↔ _
    rw [List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨i,hi,rfl⟩)
      · exact ⟨n, by omega, rfl⟩
      · exact ⟨i, by omega, rfl⟩
    · rintro ⟨i,hi,rfl⟩
      by_cases h : i = n
      · simp [h]
      · exact Or.inr ⟨i, by omega, rfl⟩

end OMA.S_oeis_a083137

open OMA.S_oeis_a083137 in
theorem OMA.solution : type_of% @OMA.S_oeis_a083137.main := by
  have hpos (i : ℕ) : 0 < a i := (spec (prior i)).1
  refine ⟨a, ?_, ?_⟩
  · have h : good [] 1 := ⟨by decide, by unfold palindrome; decide, by simp⟩
    have hle : a 0 ≤ 1 := least [] h
    have := hpos 0
    omega
  · intro n
    have hs := spec (prior (n+1))
    constructor
    · refine ⟨hs.2.1, ?_⟩
      intro i hi
      have hi' : a i ∈ prior (n+1) := (in_prior _ _).mpr ⟨i,by omega,rfl⟩
      exact ⟨(hs.2.2 _ hi').1,(hs.2.2 _ hi').2 (hpos i)⟩
    · intro p hp
      have h₀ := (hp.2 0 (Nat.zero_le n)).1
      apply least
      refine ⟨by omega, hp.1, ?_⟩
      intro b hb
      obtain ⟨i,hi,rfl⟩ := (in_prior _ _).mp hb
      have hh := hp.2 i (by omega)
      exact ⟨hh.1, fun _ => hh.2⟩
