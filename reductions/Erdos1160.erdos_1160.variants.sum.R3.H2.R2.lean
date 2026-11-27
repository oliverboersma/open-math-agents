import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3

/-!
Fixed-cofactor comparison from automorphism moments and Sylow-core templates.
Credit: @Pasx71, using Codex.

The moment estimate is a weakened form of Su--Xia, Proposition 8.5.
The structural estimate uses their Sylow-core argument, with the elementary
bound floor(log_2 |H|) on the number of generators of a finite quotient H.
For this target the strict inequality q < 2^r leaves an extra dyadic step,
so a saving from an odd first generator is unnecessary.

This file proves an implication. Its counting hypotheses remain separate
proof obligations; it is not an unconditional solution of the root problem.
-/

open Filter Finset CategoryTheory Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R2

/-- A coarse sharp bound for every fixed automorphism moment.
The sigma type counts each group class with weight |Aut(G)|^d. -/
def H1 : Prop :=
  let W := fun d a : ℕ => Nat.card
    ((c : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2^a}) × (Fin d → MulAut c.property.choose))
  ∀ d : ℕ, ∃ C : ℕ, ∀ᶠ a : ℕ in atTop,
    W d a ^ 27 * 2^(9*a^2) ≤ 2^(2*a^3 + 6*d*a^2 + C*a)

/-- For fixed q, finitely many core indices and quotient types suffice.
Writing L = floor(log_2 q), a quotient indexed by d costs at most d
automorphism images, and the corresponding kernel has order 2^(k+L-d).
The fixed quotient counts and central factor sets cost only exponentially
many choices in k. -/
def H2 : Prop :=
  let W := fun d a : ℕ => Nat.card
    ((c : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2^a}) × (Fin d → MulAut c.property.choose))
  ∀ q : ℕ, 0 < q → ∃ R E : ℕ, ∀ᶠ k : ℕ in atTop,
    g (2^k*q) ≤ 2^(E*(k+1)) *
      ∑ d ∈ Finset.range (R+1), W d (k + Nat.log 2 q - d)

/-- The previously formalized Higman lower bound, with quadratic slack. -/
def H3 : Prop :=
  ∀ᶠ m : ℕ in atTop, 2^(2*m^3) ≤ g (2^m)^27 * 2^(13*m^2)

lemma index_le_pow (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hp := Nat.two_pow_pos n
    omega

set_option maxHeartbeats 1000000 in
lemma exponent_budget (a d δ D C E R k m : ℕ)
    (hm : m = a+δ) (hd : d+1 ≤ δ) (hδ : δ ≤ D) (hk : k ≤ a+R)
    (ha : 26*D+C+27+27*E +
      (13*D^2+27*D+27*E*(R+1)+27*(R+1))+1 ≤ a) :
    2*a^3+6*d*a^2+C*a+27*(m+E*(k+1)+R+1)+13*m^2 ≤
      2*m^3+9*a^2 := by
  have hda := Nat.mul_le_mul_right (a^2) (Nat.mul_le_mul_left 6 hd)
  have hδa := Nat.mul_le_mul_right a (Nat.mul_le_mul_left 26 hδ)
  have hδsq := Nat.mul_le_mul_left 13 (Nat.pow_le_pow_left hδ 2)
  have identity :
      2*m^3+9*a^2+26*δ*a+13*δ^2+4*a^2 =
        2*a^3+6*δ*a^2+6*a*δ^2+2*δ^3+13*m^2 := by
    rw [hm]
    ring
  have gap : 2*a^3+6*d*a^2+13*m^2+2*a^2 ≤
      2*m^3+9*a^2+26*D*a+13*D^2 := by
    nlinarith only [identity,hda,hδa,hδsq,Nat.zero_le (a*δ^2),Nat.zero_le (δ^3)]
  have hlinear : 26*D+C+27+27*E ≤ a := by omega
  have hquadratic := Nat.mul_le_mul_right a hlinear
  have hconstant : 13*D^2+27*D+27*E*(R+1)+27*(R+1) ≤ a := by omega
  have hself : a ≤ a^2 := by simpa only [pow_two] using Nat.le_mul_self a
  have hma : m ≤ a+D := by omega
  have hek := Nat.mul_le_mul_left E (show k+1 ≤ a+R+1 by omega)
  have budget : C*a+27*(m+E*(k+1)+R+1)+26*D*a+13*D^2 ≤ 2*a^2 := by
    nlinarith only [hquadratic,hconstant,hself,hma,hek]
  nlinarith only [gap,budget]

lemma compare_moment (N b a m d C z : ℕ)
    (hu : N^27*2^(9*a^2) ≤ 2^(2*a^3+6*d*a^2+C*a))
    (hl : 2^(2*m^3) ≤ b^27*2^(13*m^2))
    (he : 2*a^3+6*d*a^2+C*a+27*z+13*m^2 ≤ 2*m^3+9*a^2) :
    2^z*N ≤ b := by
  apply (Nat.pow_le_pow_iff_left (by decide : 27 ≠ 0)).mp
  apply Nat.le_of_mul_le_mul_right (c := 2^(9*a^2+13*m^2)) _ (Nat.two_pow_pos _)
  calc
    (2^z*N)^27*2^(9*a^2+13*m^2) =
        (N^27*2^(9*a^2))*2^(27*z+13*m^2) := by
      rw [mul_pow,←pow_mul,Nat.mul_comm z 27]
      simp only [pow_add]
      ring
    _ ≤ 2^(2*a^3+6*d*a^2+C*a)*2^(27*z+13*m^2) :=
      Nat.mul_le_mul_right _ hu
    _ = 2^(2*a^3+6*d*a^2+C*a+27*z+13*m^2) := by
      rw [←pow_add]
      congr 1
      omega
    _ ≤ 2^(2*m^3+9*a^2) := Nat.pow_le_pow_right (by decide) he
    _ = 2^(2*m^3)*2^(9*a^2) := pow_add ..
    _ ≤ (b^27*2^(13*m^2))*2^(9*a^2) := Nat.mul_le_mul_right _ hl
    _ = b^27*2^(9*a^2+13*m^2) := by rw [pow_add]; ring

set_option maxHeartbeats 1000000 in
lemma comparison_from_templates (f : ℕ → ℕ) (W : ℕ → ℕ → ℕ)
    (moments : ∀ d : ℕ, ∃ C : ℕ, ∀ᶠ a : ℕ in atTop,
      W d a ^ 27 * 2^(9*a^2) ≤ 2^(2*a^3+6*d*a^2+C*a))
    (templates : ∀ q : ℕ, 0 < q → ∃ R E : ℕ, ∀ᶠ k : ℕ in atTop,
      f (2^k*q) ≤ 2^(E*(k+1)) *
        ∑ d ∈ Finset.range (R+1), W d (k+Nat.log 2 q-d))
    (lower : ∀ᶠ m : ℕ in atTop, 2^(2*m^3) ≤ f (2^m)^27*2^(13*m^2)) :
    ∀ r q : ℕ, 0 < r → 0 < q → q < 2^r → ∀ᶠ k : ℕ in atTop,
      2^(k+r)*f (2^k*q) ≤ f (2^(k+r)) := by
  classical
  intro r q hr hq hqr
  obtain ⟨R,E,ht⟩ := templates q hq
  obtain ⟨K0,hK0⟩ := eventually_atTop.mp ht
  obtain ⟨Klow,hKlow⟩ := eventually_atTop.mp lower
  have moments' : ∀ d : ℕ, ∃ C N : ℕ, ∀ a : ℕ, N ≤ a →
      W d a ^ 27 * 2^(9*a^2) ≤ 2^(2*a^3+6*d*a^2+C*a) := by
    intro d
    obtain ⟨C,hC⟩ := moments d
    obtain ⟨N,hN⟩ := eventually_atTop.mp hC
    exact ⟨C,N,hN⟩
  choose Cs Ns bounds using moments'
  let C := (Finset.range (R+1)).sup Cs
  let N0 := (Finset.range (R+1)).sup Ns
  let L := Nat.log 2 q
  let D := r+R
  let B := 26*D+C+27+27*E
  let T := 13*D^2+27*D+27*E*(R+1)+27*(R+1)
  have hL : L < r := Nat.log_lt_of_lt_pow hq.ne' hqr
  refine eventually_atTop.mpr ⟨K0+Klow+N0+R+B+T+1,fun k hk=>?_⟩
  have hcount := hK0 k (by omega)
  have hlower := hKlow (k+r) (by omega)
  obtain ⟨d,hd,hmax⟩ := (Finset.range (R+1)).exists_max_image
    (fun d=>W d (k+L-d)) (by exact ⟨0,by simp⟩)
  have hdR : d ≤ R := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hd
  let a := k+L-d
  let δ := r-L+d
  let m := k+r
  have had : a+d=k+L := Nat.sub_add_cancel (by omega)
  have hm : m=a+δ := by dsimp only [m,δ];omega
  have hδ : d+1 ≤ δ := by dsimp only [δ];omega
  have hδD : δ ≤ D := by dsimp only [δ,D];omega
  have hka : k ≤ a+R := by omega
  have ha : N0+B+T+1 ≤ a := by omega
  have hCd : Cs d ≤ C := Finset.le_sup hd
  have hNd : Ns d ≤ N0 := Finset.le_sup hd
  have hu : W d a ^ 27 * 2^(9*a^2) ≤ 2^(2*a^3+6*d*a^2+C*a) := by
    apply (bounds d a (by omega)).trans
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.add_le_add_left (Nat.mul_le_mul_right a hCd) _
  have he : 2*a^3+6*d*a^2+C*a+27*(m+E*(k+1)+R+1)+13*m^2 ≤
      2*m^3+9*a^2 := by
    apply exponent_budget a d δ D C E R k m hm hδ hδD hka
    change B+T+1 ≤ a
    omega
  have hcompare := compare_moment (W d a) (f (2^m)) a m d C
    (m+E*(k+1)+R+1) hu hlower he
  have hsum : (∑ j ∈ Finset.range (R+1), W j (k+L-j)) ≤ (R+1)*W d a := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (R+1), W d a := Finset.sum_le_sum hmax
      _ = _ := by simp
  calc
    2^(k+r)*f (2^k*q) ≤ 2^m*(2^(E*(k+1))*((R+1)*W d a)) := by
      apply Nat.mul_le_mul_left _
      exact hcount.trans (Nat.mul_le_mul_left _ hsum)
    _ ≤ 2^m*(2^(E*(k+1))*(2^(R+1)*W d a)) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
        (Nat.mul_le_mul_right _ (index_le_pow (R+1))))
    _ = 2^(m+E*(k+1)+R+1)*W d a := by simp only [pow_add];ring
    _ ≤ _ := hcompare

theorem main : H1 → H2 → H3 → OMA.R_Erdos1160_erdos_1160_variants_sum_R3.H2 := by
  intro moments templates lower
  exact comparison_from_templates g _ moments templates lower

end OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R2
