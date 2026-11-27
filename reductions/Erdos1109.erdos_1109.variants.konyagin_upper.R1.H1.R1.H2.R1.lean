import OMAReductions.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1
import Mathlib

/-! Fourier split for square-modulus collision counts. The zero frequency
gives the main term. All frequencies of reduced denominator at most the square root of N
are separated at scale 1/N. Only primitive fractions for primes above the
fourth root of N and below the balancing cutoff remain. -/
namespace OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1_H2_R1
open Filter Finset Real
open scoped ComplexConjugate Topology

/-- Primitive square-denominator mean square in the critical prime interval. -/
def H1 : Prop := ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Icc 1 N,
  let Z := (A.card:ℝ)
  let X := ⌊(N:ℝ)^(4/15:ℝ)⌋₊
  let P := (range (X+1)).filter Nat.Prime
  (N:ℝ)^(7/15:ℝ) < Z →
  (∑ p ∈ P, ∑ r ∈ (range (p*p)).filter (fun r => N<p^4 ∧ ¬p∣r),
    ‖∑ a ∈ A,(Complex.exp (2*Real.pi*Complex.I/(p*p:ℕ)))^(a*r)‖^2) ≤
    (N:ℝ)^ε*((N:ℝ)*Z+(N:ℝ)^(64/75:ℝ)*Z^(6/5:ℝ))

/-- Ordinary large sieve for reduced prime and small prime-square denominators. -/
def H2 : Prop := ∀ N X : ℕ, 0<N → X*X≤N → ∀ A ⊆ Icc 1 N,
  (∑ p ∈ (range (X+1)).filter Nat.Prime,
    ∑ r ∈ (range (p*p)).filter (fun r => r≠0 ∧ (p^4≤N ∨ p∣r)),
      ‖∑ a ∈ A,(Complex.exp (2*Real.pi*Complex.I/(p*p:ℕ)))^(a*r)‖^2) ≤
    100*(N:ℝ)*A.card


theorem orthogonal {q : ℕ} (hq : 0<q) {z : ℂ} (hz : IsPrimitiveRoot z q) (hu : ‖z‖=1)
    (a b : ℕ) : ∑ r ∈ range q, (conj (z^a)*z^b)^r = if a%q=b%q then (q:ℂ) else 0 := by
  have periodic (i : ℕ) : z^(i%q)=z^i := by
    conv_rhs => rw [←Nat.mod_add_div i q,pow_add,pow_mul,hz.pow_eq_one,one_pow,mul_one]
  have unit (i : ℕ) : conj (z^i)*z^i=1 := by
    rw [mul_comm,Complex.mul_conj',norm_pow,hu]
    simp
  by_cases h : a%q=b%q
  · have hval : z^a=z^b := by rw [←periodic a,←periodic b,h]
    rw [if_pos h,hval,unit]; simp
  · have ne : conj (z^a)*z^b ≠ 1 := by
      intro he
      have zz := congrArg (fun v : ℂ => z^a*v) he
      have ab : z^a=z^b := by
        change z^a*(conj (z^a)*z^b)=z^a*1 at zz
        rw [←mul_assoc,mul_comm (z^a) (conj (z^a)),unit,one_mul,mul_one] at zz
        exact zz.symm
      exact h (hz.pow_inj (Nat.mod_lt _ hq) (Nat.mod_lt _ hq) ((periodic a).trans (ab.trans (periodic b).symm)))
    have one (i : ℕ) : (z^i)^q=1 := by rw [←pow_mul,Nat.mul_comm,pow_mul,hz.pow_eq_one,one_pow]
    have hpow : (conj (z^a)*z^b)^q=1 := by rw [mul_pow,←map_pow,one,one,map_one,mul_one]
    have id := geom_sum_mul (conj (z^a)*z^b) q
    rw [hpow,sub_self,mul_eq_zero] at id
    simpa [h] using id.resolve_right (sub_ne_zero.mpr ne)

theorem parseval (A : Finset ℕ) (q : ℕ) (hq : 0<q) (z : ℂ) (hz : IsPrimitiveRoot z q)
    (hu : ‖z‖=1) :
    (∑ r ∈ range q, ‖∑ a ∈ A,z^(a*r)‖^2) =
      (q:ℝ)*((A ×ˢ A).filter (fun t => t.1%q=t.2%q)).card := by
  classical
  have term (r : ℕ) : ((‖∑ a ∈ A,z^(a*r)‖^2:ℝ):ℂ) =
      ∑ t ∈ A ×ˢ A,(conj (z^t.1)*z^t.2)^r := by
    rw [Complex.sq_norm,Complex.normSq_eq_conj_mul_self,map_sum]
    simp only [Finset.sum_mul,Finset.mul_sum,Finset.sum_product,mul_pow,map_pow,pow_mul]
    exact Finset.sum_comm
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum,term,Complex.ofReal_mul,Complex.ofReal_natCast]
  rw [Finset.sum_comm]
  simp_rw [orthogonal hq hz hu]
  rw [←Finset.sum_filter]
  simp [mul_comm]

theorem collision_le (A : Finset ℕ) (q : ℕ) (hq : 0<q) :
    (q:ℝ)*((A ×ˢ A).filter (fun t => t.1≠t.2 ∧ t.1%q=t.2%q)).card ≤
    ∑ r ∈ range q, ‖∑ a ∈ A,(Complex.exp (2*Real.pi*Complex.I/q))^(a*r)‖^2 := by
  let z := Complex.exp (2*Real.pi*Complex.I/q)
  have hz := Complex.isPrimitiveRoot_exp q hq.ne'
  have hu : ‖z‖=1 := by simp [z,Complex.norm_exp,Complex.div_re,Complex.mul_re,Complex.mul_im]
  rw [parseval A q hq z hz hu]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast Finset.card_le_card (show (A ×ˢ A).filter (fun t => t.1≠t.2 ∧ t.1%q=t.2%q) ⊆
    (A ×ˢ A).filter (fun t => t.1%q=t.2%q) from fun t ht =>
    mem_filter.mpr ⟨(mem_filter.mp ht).1,(mem_filter.mp ht).2.2⟩)


theorem partition (N p : ℕ) (hp : Nat.Prime p) (F : ℕ → ℝ) :
    ∑ r ∈ range (p*p),F r = F 0 +
      (∑ r ∈ (range (p*p)).filter (fun r => N<p^4 ∧ ¬p∣r),F r) +
      ∑ r ∈ (range (p*p)).filter (fun r => r≠0 ∧ (p^4≤N ∨ p∣r)),F r := by
  let S := (range (p*p)).filter (fun r => p^4≤N ∨ p∣r)
  have h0 : 0∈S := mem_filter.mpr ⟨mem_range.mpr (Nat.mul_pos hp.pos hp.pos),Or.inr (dvd_zero p)⟩
  have eq : S.erase 0 = (range (p*p)).filter (fun r => r≠0 ∧ (p^4≤N ∨ p∣r)) := by
    ext r
    simp [S,and_left_comm,and_comm,and_assoc]
  have h := sum_erase_add S F h0
  rw [eq] at h
  have ht := sum_filter_add_sum_filter_not (s:=range (p*p)) (p:=fun r => p^4≤N ∨ p∣r) (f:=F)
  simp only [not_or,not_le] at ht
  change (∑ r ∈ S,F r)+_= _ at ht
  linarith

theorem main : H1 → H2 → OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1.H2 := by
  intro prim im η hη
  have he : 0<η/2 := half_pos hη
  have large : ∀ᶠ N : ℕ in atTop, (101:ℝ)≤(N:ℝ)^(η/2) :=
    ((tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [prim (η/2) he,large,eventually_ge_atTop 1] with N hprim hlarge hn
  intro A hA
  let X := ⌊(N:ℝ)^(4/15:ℝ)⌋₊
  let P := (range (X+1)).filter Nat.Prime
  let F (p r : ℕ) := ‖∑ a ∈ A,(Complex.exp (2*Real.pi*Complex.I/(p*p:ℕ)))^(a*r)‖^2
  let C (p : ℕ) := ((A ×ˢ A).filter (fun t => t.1≠t.2 ∧ t.1%(p*p)=t.2%(p*p))).card
  let Z := (A.card:ℝ)
  let B := (N:ℝ)*Z+(N:ℝ)^(64/75:ℝ)*Z^(6/5:ℝ)
  let R := (N:ℝ)^(η/2)
  change (N:ℝ)^(7/15:ℝ)<Z → _
  intro dense
  have n1 : (1:ℝ)≤N := by exact_mod_cast hn
  have xbound : X*X≤N := by
    have hx : (X:ℝ)≤(N:ℝ)^(4/15:ℝ) := Nat.floor_le (by positivity)
    have h := mul_le_mul hx hx (by positivity) (by positivity)
    rw [←Real.rpow_add (by positivity : (0:ℝ)<N)] at h
    have hle := Real.rpow_le_rpow_of_exponent_le n1 (by norm_num : (4/15:ℝ)+4/15≤1)
    rw [Real.rpow_one] at hle
    exact_mod_cast h.trans hle
  have upper := im N X (by omega) xbound A hA
  have harder := hprim A hA dense
  change (∑ p ∈ P, ∑ r ∈ (range (p*p)).filter (fun r => N<p^4 ∧ ¬p∣r),F p r) ≤ R*B at harder
  change (∑ p ∈ P, ∑ r ∈ (range (p*p)).filter (fun r => r≠0 ∧ (p^4≤N ∨ p∣r)),F p r) ≤ 100*N*Z at upper
  have num (p : ℕ) : F p 0=Z^2 := by simp [F,Z]
  have bound : (∑ p ∈ P, ((p*p:ℕ):ℝ)*C p) ≤ ∑ p ∈ P, ∑ r ∈ range (p*p),F p r :=
    Finset.sum_le_sum (fun p hp => collision_le A _ (Nat.mul_pos (mem_filter.mp hp).2.pos (mem_filter.mp hp).2.pos))
  have parts : (∑ p ∈ P, ∑ r ∈ range (p*p),F p r) = _ := Finset.sum_congr rfl
    (fun p hp => partition N p (mem_filter.mp hp).2 (F p))
  rw [parts] at bound
  simp only [num,Finset.sum_add_distrib,sum_const,nsmul_eq_mul] at bound
  have ratio : (N:ℝ)^η=R*R := by
    change _=(N:ℝ)^(η/2)*(N:ℝ)^(η/2)
    rw [←Real.rpow_add (by positivity : (0:ℝ)<N)]
    ring_nf
  have b0 : 0≤B := by dsimp [B,Z]; positivity
  have nb : (N:ℝ)*Z≤B := le_add_of_nonneg_right (by dsimp [Z]; positivity)
  have coeff : R+100≤R*R := by change 101≤R at hlarge; nlinarith
  change _≤P.card*Z^2+(N:ℝ)^η*B
  rw [ratio]
  linarith [mul_le_mul_of_nonneg_right coeff b0]
end OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1_H2_R1
