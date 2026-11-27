import FormalConjectures.Wikipedia.ABC

/-!
# Fixed prime support and a height estimate for split cubics
Credit: @prophetlabs

The roots of T³ - 3XT - Y below are a-b, a+2b, and -2a-b.
The discriminant equation is Y² + 27z² = 4X³, with z=ab(a+b).
H1 is the classical fixed-support S-unit finiteness problem. H2 is the
remaining uniform estimate at large radical for this split cubic family.
-/
namespace OMA.R_ABC_abc_R1

def H1 : Prop :=
  ∀ S : Finset ℕ, {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ p.1.Coprime p.2 ∧
    (p.1 * p.2 * (p.1 + p.2)).primeFactors ⊆ S}.Finite

def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B : ℕ, ∀ (X z : ℕ) (Y : ℤ),
    0 < z → X.Coprime z → B < ABC.radical z →
    Y^2 + 27 * (z : ℤ)^2 = 4 * (X : ℤ)^3 →
    (∃ r s t : ℤ, r + s + t = 0 ∧ r*s + s*t + t*r = -3*(X : ℤ) ∧ r*s*t = Y) →
    2 * (X : ℝ) ≤ ((ABC.radical z : ℝ)^(1 + ε))^2

theorem main : H1 → H2 → type_of% @ABC.abc := by
  intro fixed height ε he
  obtain ⟨B, bound⟩ := height ε he
  apply ((fixed (Finset.range (B+1))).image
    (fun p : ℕ × ℕ => (p.1, p.2, p.1 + p.2))).subset
  rintro ⟨a,b,c⟩ ⟨ha,hb,hc,hpair,hadd,hbad⟩
  subst c
  have hac : a.Coprime (a+b) :=
    hpair (by simp : a ∈ ({a,b,a+b} : Set ℕ)) (by simp) (by omega)
  have hab : a.Coprime b := by
    rwa [add_comm, Nat.coprime_add_self_right] at hac
  let X := a^2 + a*b + b^2
  let z := a*b*(a+b)
  have hx : X.Coprime z := by
    have hxa : X.Coprime a := by
      rw [show X = (a+b)*a + b^2 by dsimp [X]; ring, Nat.coprime_mul_right_add_left]
      exact hab.symm.pow_left _
    have hxb : X.Coprime b := by
      rw [show X = (a+b)*b + a^2 by dsimp [X]; ring, Nat.coprime_mul_right_add_left]
      exact hab.pow_left _
    have hxc : X.Coprime (a+b) := by
      rw [show X = b*(a+b) + a^2 by dsimp [X]; ring, Nat.coprime_mul_right_add_left]
      exact hac.pow_left _
    exact (hxa.mul_right hxb).mul_right hxc
  have hsmall : ABC.radical z ≤ B := by
    by_contra! h
    let r : ℤ := (a:ℤ)-b
    let s : ℤ := a+2*(b:ℤ)
    let t : ℤ := -2*(a:ℤ)-b
    have hbound := bound X z (r*s*t) (by dsimp [z]; positivity) hx h
      (by dsimp [X,z,r,s,t]; push_cast; ring)
      ⟨r,s,t,by dsimp [r,s,t]; ring,by dsimp [r,s,t,X]; push_cast; ring,rfl⟩
    have hc2 : ((a+b : ℕ) : ℝ)^2 ≤ 2*(X:ℝ) := by
      dsimp [X]; push_cast; nlinarith [sq_nonneg (a:ℝ),sq_nonneg (b:ℝ)]
    have hr : 0 ≤ (ABC.radical z : ℝ)^(1+ε) := by positivity
    change (ABC.radical z : ℝ) ^ (1+ε) < ((a+b : ℕ) : ℝ) at hbad
    nlinarith [sq_lt_sq' (by linarith : -((a+b : ℕ):ℝ) < (ABC.radical z:ℝ)^(1+ε)) hbad]
  refine ⟨(a,b), ⟨ha,hb,hab,?_⟩, rfl⟩
  intro p hp
  have hd : p ∣ ABC.radical z := Finset.dvd_prod_of_mem id hp
  have hpos : 0 < ABC.radical z := Finset.prod_pos fun q hq => (Nat.prime_of_mem_primeFactors hq).pos
  exact Finset.mem_range.mpr (by have := Nat.le_of_dvd hpos hd; omega)

end OMA.R_ABC_abc_R1
