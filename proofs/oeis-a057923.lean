import OMAStatements.S_oeis_a057923

namespace OMA.A057923Proof

open OMA.S_oeis_a057923

lemma remove_overlap (x y : ℕ) :
    y + Nat.ldiff x y = y ||| x ∧ Nat.ldiff x y ≤ x := by
  induction x using Nat.binaryRec generalizing y with
  | zero => simp [Nat.ldiff]
  | bit a x ih =>
    cases y using Nat.bitCasesOn with
    | bit b y =>
      obtain ⟨h₁, h₂⟩ := ih y
      rw [Nat.ldiff_bit, Nat.lor_bit]
      cases a <;> cases b <;> simp [Nat.bit] <;> omega

lemma least_or_sum (y t : ℕ) : y ||| pick y t = y + pick y t := by
  let z := pick y t
  have hsame : y ||| Nat.ldiff z y = y ||| z := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_or, Nat.testBit_ldiff]
    cases y.testBit i <;> cases z.testBit i <;> rfl
  have hvalid : t < y ||| z := Nat.find_spec (candidate y t)
  have hmin : z ≤ Nat.ldiff z y :=
    Nat.find_min' (candidate y t) (hsame.symm ▸ hvalid)
  have h := remove_overlap z y
  change y ||| z = y + z
  omega

lemma pair_or_sum (n : ℕ) : (pair n).1 ||| (pair n).2 = (pair n).1 + (pair n).2 := by
  cases n with
  | zero => decide
  | succ n => exact least_or_sum _ _

end OMA.A057923Proof

open OMA.S_oeis_a057923 OMA.A057923Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a057923.main := by
  intro n
  let x := (pair n).1
  let y := (pair n).2
  let z := pick y (x ||| y)
  have hlt : x ||| y < y ||| z := Nat.find_spec (candidate y (x ||| y))
  have hxy : x ||| y = x + y := pair_or_sum n
  have hyz : y ||| z = y + z := least_or_sum _ _
  change x < z
  omega
