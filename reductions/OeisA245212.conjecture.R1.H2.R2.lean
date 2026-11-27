import OMAReductions.R_OeisA245212_conjecture_R1

-- Credit: @anmolspace. OpenAI Codex.
-- The divisor-sum multiplicativity and equality_nat/at_power_product helpers
-- are adapted from DomTheDeveloper, upstream reduction #1376. The exponent
-- inversion and the present reduction follow Anmol Sahu's sparsity manuscript.
namespace OMA.R_OeisA245212_conjecture_R1_H2_R2
open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma
private lemma moment_function :
    ∃ F : ArithmeticFunction ℕ, F.IsMultiplicative ∧
      ∀ n, F n = ∑ d ∈ n.divisors, d*d.divisors.card := by
  refine ⟨(ArithmeticFunction.id.pmul (σ 0))*ArithmeticFunction.zeta,
    (isMultiplicative_id.pmul isMultiplicative_sigma).mul isMultiplicative_zeta, ?_⟩
  intro n
  rw [ArithmeticFunction.mul_zeta_apply]
  simp only [pmul_apply, id_apply, sigma_zero_apply]

private lemma moment_mul (u v : ℕ) (hc : u.Coprime v) :
    (∑ d ∈ (u*v).divisors, d*d.divisors.card) =
      (∑ d ∈ u.divisors, d*d.divisors.card)*(∑ d ∈ v.divisors, d*d.divisors.card) := by
  obtain ⟨F,hF,h⟩ := moment_function
  simpa only [h] using hF.map_mul_of_coprime hc

private lemma moment_at_power (p e : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p^e).divisors, d*d.divisors.card) = ∑ j ∈ range (e+1), p^j*(j+1) := by
  rw [Nat.sum_divisors_prime_pow hp]
  simp only [Nat.divisors_prime_pow hp, card_map, card_range]

private lemma equality_nat (n : ℕ) (hn : n ≠ 0) :
    OeisA245212.a n = (σ 1 n : ℤ) ↔
      (∑ d ∈ n.divisors, d*d.divisors.card) + σ 1 n = 2 * n * n.divisors.card := by
  have hs : (∑ d ∈ n.divisors, d*d.divisors.card) =
      n*n.divisors.card + ∑ d ∈ n.properDivisors, d*d.divisors.card := by
    calc
      _ = ∑ d ∈ insert n n.properDivisors, d*d.divisors.card := by rw [Nat.insert_self_properDivisors hn]
      _ = _ := sum_insert Nat.self_notMem_properDivisors
  rw [hs]
  unfold OeisA245212.a
  constructor
  · intro h
    zify
    linarith
  · intro h
    zify at h
    linarith

private lemma at_power_product (p e b : ℕ) (hp : p.Prime) (hb : b ≠ 0) (hc : p.Coprime b) :
    OeisA245212.a (p^e*b) = (σ 1 (p^e*b) : ℤ) ↔
      (∑ j ∈ range (e+1), ((j+1)*(∑ d ∈ b.divisors, d*d.divisors.card)+σ 1 b)*p^j) =
        (2*b*(e+1)*b.divisors.card)*p^e := by
  have hc' := hc.pow_left e
  rw [equality_nat _ (Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) hb),
    moment_mul _ _ hc', moment_at_power _ _ hp, isMultiplicative_sigma.map_mul_of_coprime hc',
    sigma_apply_prime_pow hp, hc'.card_divisors_mul, Nat.divisors_prime_pow hp, card_map, card_range]
  simp only [mul_one]
  have split : (∑ j ∈ range (e+1), ((j+1)*(∑ d ∈ b.divisors, d*d.divisors.card)+σ 1 b)*p^j) =
      (∑ j ∈ range (e+1), p^j*(j+1))*(∑ d ∈ b.divisors, d*d.divisors.card) +
        (∑ j ∈ range (e+1), p^j)*σ 1 b := by
    rw [sum_mul, sum_mul, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  rw [split]
  ring_nf


private lemma geom2 (k : ℕ) : (∑ j ∈ range (k+1), 2^j) + 1 = 2^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, pow_succ (2:ℕ) (k+1)]; omega

private lemma weighted2 (k : ℕ) : (∑ j ∈ range (k+1), 2^j*(j+1)) = k*2^(k+1)+1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ,ih,pow_succ (2:ℕ) (k+1)]
    ring

private lemma weighted_gt (m : ℕ) (hm : 1 < m) :
    m*m.divisors.card < ∑ d ∈ m.divisors, d*d.divisors.card := by
  have hone := Nat.one_mem_properDivisors_iff_one_lt.mpr hm
  have hrest : 0 < ∑ d ∈ m.properDivisors, d*d.divisors.card :=
    sum_pos' (fun _ _ => Nat.zero_le _) ⟨1,hone,by simp⟩
  calc
    _ < m*m.divisors.card + ∑ d ∈ m.properDivisors, d*d.divisors.card := by omega
    _ = ∑ d ∈ insert m m.properDivisors, d*d.divisors.card := by rw [sum_insert Nat.self_notMem_properDivisors]
    _ = _ := by rw [Nat.insert_self_properDivisors (by omega)]

private lemma pow_gap (k : ℕ) (hk : 1 ≤ k) : k+2 < 2^(k+1) := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => decide
    | succ k =>
      have h := ih (by omega)
      rw [pow_succ (2:ℕ) (k+1+1)]
      omega

private lemma collapse (k m : ℕ) (hk : 1 ≤ k) (ho : Odd m) (hm : 1 < m)
    (heq : OeisA245212.a (2^k*m) = (σ 1 (2^k*m) : ℤ)) :
    let A := m*m.divisors.card
    let F := ∑ d ∈ m.divisors, d*d.divisors.card
    let S := σ 1 m
    let x := A-S
    let y := F-A
    x / y = k ∧ 2^(k+1)*(x-k*y) = x+y := by
  dsimp only
  let A := m*m.divisors.card
  let F := ∑ d ∈ m.divisors, d*d.divisors.card
  let S := σ 1 m
  let x := A-S
  let y := F-A
  change x/y = k ∧ 2^(k+1)*(x-k*y)=x+y
  have hFA : A < F := weighted_gt m hm
  have hSA : S ≤ A := by
    change σ 1 m ≤ m*m.divisors.card
    rw [sigma_one_apply]
    calc
      _ ≤ ∑ _d ∈ m.divisors,m := sum_le_sum fun _ hd => Nat.divisor_le hd
      _ = _ := by simp [mul_comm]
  have hY : 0 < y := Nat.sub_pos_of_lt hFA
  have h1 : A = x+S := (Nat.sub_add_cancel hSA).symm
  have h2 : F = y+A := (Nat.sub_add_cancel hFA.le).symm
  have eqn := (at_power_product 2 k m Nat.prime_two (by omega) (Nat.coprime_two_left.mpr ho)).mp heq
  change (∑ j ∈ range (k+1), ((j+1)*F+S)*2^j) = (2*m*(k+1)*m.divisors.card)*2^k at eqn
  have expand : (∑ j ∈ range (k+1), ((j+1)*F+S)*2^j) =
      (∑ j ∈ range (k+1), 2^j*(j+1))*F + (∑ j ∈ range (k+1),2^j)*S := by
    rw [sum_mul,sum_mul,← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  have rhs : (2*m*(k+1)*m.divisors.card)*2^k=(k+1)*2^(k+1)*A := by
    dsimp [A]; rw [pow_succ]; ring
  rw [expand,weighted2,rhs] at eqn
  have geo := geom2 k
  have bal : 2^(k+1)*x = 2^(k+1)*(k*y) + x+y := by
    rw [h2,h1] at eqn
    nlinarith only [eqn,congrArg (fun n : ℕ => n*S) geo]
  have lo : k*y ≤ x := by
    by_contra! h
    have hlt := Nat.mul_lt_mul_of_pos_left h (by positivity : 0 < 2^(k+1))
    omega
  have hi : x < (k+1)*y := by
    by_contra! h
    have p := pow_gap k hk
    have hh := Nat.mul_le_mul_left (2^(k+1)-1) h
    have hg := Nat.mul_lt_mul_of_pos_right p hY
    have hsub : (2^(k+1)-1)+1=2^(k+1) := Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide))
    nlinarith only [bal,hh,hg,congrArg (fun n : ℕ => n*x) hsub,
      congrArg (fun n : ℕ => n*((k+1)*y)) hsub]
  constructor
  · exact Nat.le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hY).2 hi))
      ((Nat.le_div_iff_mul_le hY).2 lo)
  · rw [Nat.mul_sub]
    omega

/-- Residual single-candidate identity for odd square cofactors. -/
def H1 : Prop :=
  ∀ m : ℕ, Odd m → 1 < m → IsSquare m →
    let A := m*m.divisors.card
    let F := ∑ d ∈ m.divisors, d*d.divisors.card
    let x := A-σ 1 m
    let y := F-A
    let k := x/y
    1 ≤ k → 2^(k+1)*(x-k*y) ≠ x+y

/-- Residual single-candidate identity for odd nonsquare cofactors. -/
def H2 : Prop :=
  ∀ m : ℕ, Odd m → 1 < m → ¬ IsSquare m →
    let A := m*m.divisors.card
    let F := ∑ d ∈ m.divisors, d*d.divisors.card
    let x := A-σ 1 m
    let y := F-A
    let k := x/y
    1 ≤ k → 2^(k+1)*(x-k*y) ≠ x+y

theorem main : H1 → H2 → OMA.R_OeisA245212_conjecture_R1.H2 := by
  intro hs hn k m hk ho hm heq
  obtain ⟨hdiv,hbalance⟩ := collapse k m hk ho hm heq
  by_cases sq : IsSquare m
  · have reduced := hs m ho hm sq
    dsimp only at reduced
    rw [hdiv] at reduced
    exact reduced hk hbalance
  · have reduced := hn m ho hm sq
    dsimp only at reduced
    rw [hdiv] at reduced
    exact reduced hk hbalance

end OMA.R_OeisA245212_conjecture_R1_H2_R2
