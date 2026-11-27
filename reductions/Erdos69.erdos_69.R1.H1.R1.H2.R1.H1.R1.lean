import OMAReductions.R_Erdos69_erdos_69_R1_H1_R1_H2_R1

/-! A finite Chinese remainder count, truncation of a characteristic function, and
a scalar cutoff estimate give the empirical prime-divisibility comparison.
The k-th elementary symmetric remainder is at most the k-th power of the
reciprocal prime mass divided by k factorial. The other error counts residue
classes in a progression and does not grow with its length. -/

open Filter Finset Real
namespace OMA.R_Erdos69_erdos_69_R1_H1_R1_H2_R1_H1_R1

/-- Every simultaneous choice of residues occurs with endpoint discrepancy at most one. -/
def H1 : Prop :=
  ∀ (x Q b : ℕ) (J : Finset ℕ) (h : ℕ → ℤ),
    let N := (Icc (x/2) x).filter fun n => n%Q=b%Q
    0 < Q → (∀ p ∈ J, Nat.Prime p ∧ ¬p ∣ Q) →
    |(((N.filter fun (n : ℕ) => ∀ p ∈ J, (p:ℤ) ∣ (n:ℤ)+h p).card : ℝ) -
      N.card / (∏ p ∈ J, (p:ℝ)))| ≤ 1

/-- Finite truncation at order k for distinct residue classes and unit complex phases. -/
def H2 : Prop :=
  let phase (t : ℝ) := Complex.exp ((2*Real.pi*t : ℝ)*Complex.I)
  ∀ (N P : Finset ℕ) (S : Finset (Finset ℕ × ℕ)) (r : Finset ℕ × ℕ → ℤ)
    (t : Finset ℕ × ℕ → ℝ) (C : ℝ) (k : ℕ), 0 < k → 0 < C →
    (∀ p ∈ P, Nat.Prime p) →
    (∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ p ∈ P, ¬(p:ℤ) ∣ r a - r b) →
    (∑ a ∈ S, ‖phase (t a) - 1‖) ≤ C →
    (∀ J ⊆ P, ∀ h : ℕ → ℤ,
      |(((N.filter fun (n : ℕ) => ∀ p ∈ J, (p:ℤ) ∣ (n:ℤ)+h p).card : ℝ) -
        N.card / (∏ p ∈ J, (p:ℝ)))| ≤ 1) →
    ‖(∑ n ∈ N, phase (∑ a ∈ S, t a *
      ((P.filter fun (p : ℕ) => (p:ℤ) ∣ (n:ℤ)+r a).card : ℝ))) -
      (N.card:ℂ) * ∏ p ∈ P, (1+(∑ a ∈ S, (phase (t a)-1))/(p:ℂ))‖ ≤
      N.card * (2 * (C*(∑ p ∈ P, (1:ℝ)/p))^k / k.factorial) +
        2*((1+C)*(1+(P.card:ℝ)))^k

/-- Uniform cutoff for two scalar error terms. A sufficiently large constant times
log log x works by the factorial bound and Mertens' upper estimate. -/
def H3 : Prop :=
  ∀ C : ℝ, 0 < C → ∀ᶠ x : ℕ in atTop,
    ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ (p:ℝ) ≤ (x:ℝ)^(1/log (log x)^2)) →
    ∃ k : ℕ, 0 < k ∧ 2*(C*(∑ p ∈ P, (1:ℝ)/p))^k / k.factorial < 1/16 ∧
      2*((1+C)*(1+(P.card:ℝ)))^k < Real.sqrt x / 128

theorem main : H1 → H2 → H3 → OMA.R_Erdos69_erdos_69_R1_H1_R1_H2_R1.H1 := by
  intro hcrt hfinite hscale
  intro q hq
  let C : ℝ := 2*Real.pi*q
  have pos : 0 < C := by dsimp [C]; positivity
  filter_upwards [hscale C pos,eventually_ge_atTop 1] with x hcut hx
  dsimp only
  intro Q b S r w P hQ hsize hp hsep hw
  let N := (Icc (x/2) x).filter fun n => n%Q=b%Q
  let phase (t : ℝ) := Complex.exp ((2*Real.pi*t : ℝ)*Complex.I)
  obtain ⟨k,hk,herr,hend⟩ := hcut P (fun p h => ⟨(hp p h).1,(hp p h).2.2⟩)
  have hnorm : (∑ a ∈ S, ‖phase (q*w a)-1‖) ≤ C := by
    calc
      _ ≤ ∑ a ∈ S, C*|w a| := by
        apply sum_le_sum
        intro a _
        have z := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*(q*w a))
        simpa only [phase,mul_comm Complex.I,Real.norm_eq_abs,abs_mul,abs_of_pos Real.pi_pos,
          abs_of_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q),abs_of_pos (by norm_num : (0:ℝ)<2),C,mul_assoc] using z
      _ = C*(∑ a ∈ S, |w a|) := (mul_sum ..).symm
      _ ≤ C := by nlinarith
  have he := hfinite N P S r (fun a => q*w a) C k hk pos (fun p h => (hp p h).1) hsep hnorm
    (fun J hJ h => hcrt x Q b J h hQ (fun p h => ⟨(hp p (hJ h)).1,(hp p (hJ h)).2.1⟩))
  let Z := ∑ n ∈ N, phase (q*∑ a ∈ S, w a * ((P.filter fun (p : ℕ) => (p:ℤ) ∣ (n:ℤ)+r a).card : ℝ))
  let B := ∏ p ∈ P, (1+(∑ a ∈ S, (phase (q*w a)-1))/(p:ℂ))
  have hz : ‖Z - (N.card:ℂ)*B‖ ≤ (N.card:ℝ) *
      (2*(C*(∑ p ∈ P,(1:ℝ)/p))^k/k.factorial) + 2*((1+C)*(1+(P.card:ℝ)))^k := by
    simpa only [Z,B,phase,mul_sum,mul_assoc] using he
  have nx : 0 < (x:ℝ) := by exact_mod_cast (show 0<x by omega)
  change Real.sqrt x ≤ 8*(N.card:ℝ) at hsize
  have nc : 0 < (N.card:ℝ) := by linarith [Real.sqrt_pos.2 nx]
  have hz' := hz.trans_lt (add_lt_add (mul_lt_mul_of_pos_left herr nc) hend)
  have tr := norm_add_le (Z-(N.card:ℂ)*B) ((N.card:ℂ)*B)
  rw [sub_add_cancel,norm_mul,Complex.norm_natCast] at tr
  change ‖Z‖ < (N.card:ℝ)*(‖B‖+1/8)
  nlinarith

end OMA.R_Erdos69_erdos_69_R1_H1_R1_H2_R1_H1_R1

