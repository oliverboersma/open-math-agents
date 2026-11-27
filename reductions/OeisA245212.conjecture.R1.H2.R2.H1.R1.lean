import OMAReductions.R_OeisA245212_conjecture_R1_H2_R2
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.Ring

/-! Two restrictions on odd square cofactors in A245212.

Credit: @anmolspace. Write the surviving cofactor as a fourth power. Its fourth
root modulo eight prescribes the divisor count of the square root modulo sixteen.
A second condition compares the divisor count with the common 2-power modulus of
the supporting primes. The original fourth-power observation is from Anmol’s earlier handoff.
The multiplicative moment formulas are adapted from DomTheDeveloper’s project PR #1376.
The residual exponent identity is from Anmol Sahu's even-case reduction.
-/

namespace OMA.R_OeisA245212_conjecture_R1_H2_R2_H1_R1
open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

set_option maxRecDepth 40000 in
set_option maxHeartbeats 2000000 in
/-- Every solution of the square-cofactor exponent test obeys two further congruence restrictions. -/
private theorem square_restrictions (m : ℕ) (ho : Odd m) (hm : 1 < m) (hsq : IsSquare m) :
    let A := m*m.divisors.card
    let F := ∑ d ∈ m.divisors, d*d.divisors.card
    let x := A-σ 1 m
    let y := F-A
    let k := x/y
    1 ≤ k → 2^(k+1)*(x-k*y)=x+y →
    ∃ v : ℕ, Odd v ∧ 1 < v ∧ m = v^4 ∧
      (∀ s : ℕ, (∀ p : ℕ, p.Prime → p ∣ v^2 → p ≡ 1 [MOD 2^s]) →
      (v^2).divisors.card ≡ 1 [MOD 2^s]) ∧
      (v^2).divisors.card ≡ (if v%8=3 ∨ v%8=5 then 9 else 1) [MOD 16] := by
  let moment (n : ℕ) := ∑ d ∈ n.divisors, d*d.divisors.card

  have moment_mul {a b : ℕ} (hc : a.Coprime b) : moment (a*b) = moment a * moment b := by
    let F : ArithmeticFunction ℕ := (ArithmeticFunction.id.pmul (σ 0))*ArithmeticFunction.zeta
    have hF : F.IsMultiplicative := (isMultiplicative_id.pmul isMultiplicative_sigma).mul isMultiplicative_zeta
    have h (n : ℕ) : F n = moment n := by
      simp only [F, moment, ArithmeticFunction.mul_zeta_apply, pmul_apply, id_apply, sigma_zero_apply]
    simpa only [h] using hF.map_mul_of_coprime hc

  have triangle (a : ℕ) : ∑ j ∈ range (2*a+1), (j+1) = (2*a+1)*(a+1) := by
    induction a with
    | zero => simp
    | succ a ih =>
      rw [show 2*(a+1)+1 = (2*a+1)+1+1 by omega, sum_range_succ, sum_range_succ, ih]
      ring

  have squareData (u M : ℕ) (hu : u ≠ 0)
      (good : ∀ p : ℕ, p.Prime → p ∣ u → p ≡ 1 [MOD M]) :
      u ≡ 1 [MOD M] ∧ Odd (u^2).divisors.card ∧
      σ 1 (u^2) ≡ (u^2).divisors.card [MOD M] ∧
      moment (u^2) ≡ (u^2).divisors.card * u.divisors.card [MOD M] := by
    induction u using Nat.recOnPosPrimePosCoprime with
    | zero => contradiction
    | one => simp [moment]; rfl
    | prime_pow p a hp ha =>
      have h1 := good p hp (dvd_pow_self p ha.ne')
      have hpow (j : ℕ) : p^j ≡ 1 [MOD M] := by simpa using h1.pow j
      rw [← pow_mul, Nat.mul_comm a 2]
      simp only [Nat.divisors_prime_pow hp, card_map, card_range]
      refine ⟨hpow a, ⟨a, by omega⟩, ?_, ?_⟩
      · rw [sigma_apply_prime_pow hp]
        simpa [mul_one] using (Nat.ModEq.sum (s := range (2*a+1)) (fun j _ ↦ hpow j))
      · dsimp only [moment]; rw [Nat.sum_divisors_prime_pow hp]
        simp only [Nat.divisors_prime_pow hp, card_map, card_range]
        have hsum := Nat.ModEq.sum (s := range (2*a+1)) (fun j _ ↦ (hpow j).mul_right (j+1))
        simpa only [one_mul, triangle] using hsum
    | coprime a b ha hb hc ia ib =>
      obtain ⟨ha1, ha2, ha3, ha4⟩ := ia (by omega) (fun p hp hd ↦ good p hp (dvd_mul_of_dvd_left hd _))
      obtain ⟨hb1, hb2, hb3, hb4⟩ := ib (by omega) (fun p hp hd ↦ good p hp (dvd_mul_of_dvd_right hd _))
      have hc2 : (a^2).Coprime (b^2) := (hc.pow_left 2).pow_right 2
      rw [mul_pow, hc.card_divisors_mul, hc2.card_divisors_mul, moment_mul hc2, isMultiplicative_sigma.map_mul_of_coprime hc2]
      refine ⟨by simpa using ha1.mul hb1, ha2.mul hb2, ha3.mul hb3, ?_⟩
      convert ha4.mul hb4 using 1 <;> ring

  have tau_root_mod (u s : ℕ) (hu : u ≠ 0)
      (good : ∀ p : ℕ, p.Prime → p ∣ u → p ≡ 1 [MOD 2^s]) :
      let m := u^2
      let A := m*m.divisors.card
      let F := ∑ d ∈ m.divisors, d*d.divisors.card
      let x := A-σ 1 m
      let y := F-A
      let k := x/y
      2^(k+1)*(x-k*y) = x+y → u.divisors.card ≡ 1 [MOD 2^s] := by
    let m := u^2
    let C := m.divisors.card
    let A := m*C
    let S := σ 1 m
    let F := moment m
    let x := A-S
    let y := F-A
    let k := x/y
    let T := 2^(k+1)
    change T*(x-k*y) = x+y → _
    intro he
    obtain ⟨h1, ho, hS, hF⟩ := squareData u (2^s) hu good
    have hA : A ≡ C [MOD 2^s] := by simpa [A,m] using (h1.pow 2).mul_right C
    have hSA : S ≤ A := by
      change σ 1 m ≤ m*m.divisors.card
      rw [sigma_one_apply]
      calc
        _ ≤ ∑ _d ∈ m.divisors, m := sum_le_sum fun _ hd ↦ Nat.divisor_le hd
        _ = _ := by simp [mul_comm]
    have hAF : A ≤ F := by
      have hm : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_refl _, pow_ne_zero 2 hu⟩
      exact single_le_sum (f := fun d : ℕ ↦ d*d.divisors.card) (fun _ _ ↦ Nat.zero_le _) hm
    have hx : 2^s ∣ x := (Nat.modEq_iff_dvd' hSA).mp (hS.trans hA.symm)
    have hle : k*y ≤ x := Nat.div_mul_le_self _ _
    have hb := congrArg (fun z : ℕ ↦ T*z) (Nat.sub_add_cancel hle)
    simp only [Nat.mul_add, he] at hb
    have hall : 2^s ∣ x + (T*k+1)*y := by
      have d := dvd_mul_of_dvd_right hx T
      rw [← hb] at d
      rw [show x + (T*k+1)*y = (x+y) + T*(k*y) by ring]
      exact d
    have ht : Odd (T*k+1) := ⟨2^k*k, by dsimp [T]; rw [pow_succ]; ring⟩
    have hy : 2^s ∣ y := ((Nat.coprime_two_left.mpr ht).pow_left s).dvd_of_dvd_mul_left ((Nat.dvd_add_iff_right hx).mpr hall)
    have heq : A ≡ F [MOD 2^s] := (Nat.modEq_iff_dvd' hAF).mpr hy
    apply Nat.ModEq.cancel_left_of_coprime ((Nat.coprime_two_left.mpr ho).pow_left s)
    simpa only [mul_one] using hF.symm.trans (heq.symm.trans hA)

  let balanced (m : ℕ) : Prop :=
    let A := m*m.divisors.card
    let F := ∑ d ∈ m.divisors, d*d.divisors.card
    let x := A-σ 1 m
    let y := F-A
    let k := x/y
    2^(k+1)*(x-k*y) = x+y

  let admissible (u : ℕ) : Prop :=
    ∀ s : ℕ, (∀ p : ℕ, p.Prime → p ∣ u → p ≡ 1 [MOD 2^s]) → u.divisors.card ≡ 1 [MOD 2^s]

  have admissible_of_balance {u : ℕ} (hu : u ≠ 0) (h : balanced (u^2)) : admissible u :=
    fun s hs ↦ tau_root_mod u s hu hs h

  have square_of_odd_divisor_count (n : ℕ) (h : Odd n.divisors.card) : IsSquare n := by
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => exact ⟨0,by simp⟩
    | one => exact ⟨1,by simp⟩
    | prime_pow p a hp ha =>
      rw [Nat.divisors_prime_pow hp, card_map, card_range, Nat.odd_iff] at h
      refine ⟨p^(a/2), ?_⟩
      rw [← pow_add]
      congr 1
      omega
    | coprime a b ha hb hc ia ib =>
      rw [hc.card_divisors_mul] at h
      exact (ia (h.of_dvd_nat (dvd_mul_right _ _))).mul (ib (h.of_dvd_nat (dvd_mul_left _ _)))

  have fourth_power {u : ℕ} (hu : Odd u) (hb : balanced (u^2)) : IsSquare u := by
    apply square_of_odd_divisor_count
    have h := admissible_of_balance hu.pos.ne' hb 1 (fun p _ hpu ↦ by
      simpa only [pow_one] using (show p ≡ 1 [MOD 2] from Nat.odd_iff.mp (hu.of_dvd_nat hpu)))
    exact Nat.odd_iff.mpr (by simpa [Nat.ModEq] using h)

  let twist (u : ℕ) := if u%8=3 ∨ u%8=5 then 9 else 1

  let geomBlock (p : ℕ) := p + p^2 + p^3 + p^4
  let weightBlock (p : ℕ) := 2*p + 3*p^2 + 4*p^3 + 5*p^4

  have twist_congr {u v : ℕ} (h : u ≡ v [MOD 8]) : twist u = twist v := by
    unfold twist
    rw [show u%8=v%8 from h]

  have twist_mul {u v : ℕ} (hu : Odd u) (hv : Odd v) :
      twist (u*v) ≡ twist u * twist v [MOD 16] := by
    have tab : ∀ a b : Fin 8, a.val%2=1 → b.val%2=1 → twist (a.val*b.val) ≡ twist a.val*twist b.val [MOD 16] := by dsimp only [twist]; decide +kernel
    let a : Fin 8 := ⟨u%8, Nat.mod_lt _ (by decide)⟩
    let b : Fin 8 := ⟨v%8, Nat.mod_lt _ (by decide)⟩
    have ea : u ≡ a.val [MOD 8] := (Nat.mod_modEq u 8).symm
    have eb : v ≡ b.val [MOD 8] := (Nat.mod_modEq v 8).symm
    rw [twist_congr (ea.mul eb), twist_congr ea, twist_congr eb]
    exact tab a b (by dsimp [a]; have := Nat.odd_iff.mp hu; omega) (by dsimp [b]; have := Nat.odd_iff.mp hv; omega)

  have geomBlock_congr {a b M : ℕ} (h : a ≡ b [MOD M]) : geomBlock a ≡ geomBlock b [MOD M] :=
    ((h.add (h.pow 2)).add (h.pow 3)).add (h.pow 4)

  have weightBlock_congr {a b M : ℕ} (h : a ≡ b [MOD M]) : weightBlock a ≡ weightBlock b [MOD M] :=
    (((h.mul_left 2).add ((h.pow 2).mul_left 3)).add ((h.pow 3).mul_left 4)).add ((h.pow 4).mul_left 5)

  have block_values {p : ℕ} (hp : Odd p) : p^4 ≡ 1 [MOD 16] ∧ 4 ∣ geomBlock p := by
    have tab : ∀ p : Fin 16, p.val%2=1 → p.val^4 ≡ 1 [MOD 16] ∧ 4 ∣ geomBlock p.val := by dsimp only [geomBlock]; decide +kernel
    let a : Fin 16 := ⟨p%16, Nat.mod_lt _ (by decide)⟩
    have h : p ≡ a.val [MOD 16] := (Nat.mod_modEq p 16).symm
    obtain ⟨h1,h2⟩ := tab a (by dsimp [a]; have := Nat.odd_iff.mp hp; omega)
    refine ⟨(h.pow 4).trans h1, ?_⟩
    have pair : geomBlock p ≡ geomBlock a.val [MOD 4] := (geomBlock_congr h).of_dvd (by decide)
    exact (Nat.modEq_zero_iff_dvd.mp (pair.trans (Nat.modEq_zero_iff_dvd.mpr h2)))

  have sum_blocks {p : ℕ} (hp : Odd p) (a : ℕ) :
      (∑ j ∈ range (4*a+1), p^j) ≡ 1+a*geomBlock p [MOD 16] ∧
      (∑ j ∈ range (4*a+1), p^j*(j+1)) ≡ 1+a*weightBlock p [MOD 16] := by
    obtain ⟨hp4,hg⟩ := block_values hp
    induction a with
    | zero => simp <;> rfl
    | succ a ih =>
      have hp4a : p^(4*a) ≡ 1 [MOD 16] := by simpa only [pow_mul,one_pow] using hp4.pow a
      have len : 4*(a+1)+1 = 4*a+1+1+1+1+1 := by omega
      have hS : (∑ i ∈ range (4*(a+1)+1), p^i) = (∑ i ∈ range (4*a+1), p^i) + p^(4*a)*geomBlock p := by
        rw [len,sum_range_succ,sum_range_succ,sum_range_succ,sum_range_succ]
        simp only [pow_succ,geomBlock]; ring
      have hF : (∑ i ∈ range (4*(a+1)+1), p^i*(i+1)) = (∑ i ∈ range (4*a+1), p^i*(i+1)) +
          p^(4*a)*(weightBlock p + 4*a*geomBlock p) := by
        rw [len,sum_range_succ,sum_range_succ,sum_range_succ,sum_range_succ]
        simp only [pow_succ,geomBlock,weightBlock]; ring
      have hz : 4*a*geomBlock p ≡ 0 [MOD 16] := by
        apply Nat.modEq_zero_iff_dvd.mpr
        obtain ⟨c,hc⟩ := hg
        exact ⟨a*c, by rw [hc]; ring⟩
      have w : weightBlock p + 4*a*geomBlock p ≡ weightBlock p [MOD 16] := by simpa using hz.add_left (weightBlock p)
      rw [hS,hF]
      constructor
      · convert ih.1.add (hp4a.mul_right (geomBlock p)) using 1 <;> ring
      · convert ih.2.add (hp4a.mul w) using 1 <;> ring

  have block_identity {p : ℕ} (hp : Odd p) (a : ℕ) :
      1+a*weightBlock p ≡ (1+a*geomBlock p)*(2*a+1)*twist (p^a) [MOD 16] := by
    have table : ∀ p a : Fin 16, p.val%2=1 →
        1+a.val*weightBlock p.val ≡ (1+a.val*geomBlock p.val)*(2*a.val+1)*twist (p.val^a.val) [MOD 16] := by dsimp only [twist,weightBlock,geomBlock]; decide +kernel
    let t : Fin 16 := ⟨p%16, Nat.mod_lt _ (by decide)⟩
    let b : Fin 16 := ⟨a%16, Nat.mod_lt _ (by decide)⟩
    have ep : p ≡ t.val [MOD 16] := (Nat.mod_modEq p 16).symm
    have ea : a ≡ b.val [MOD 16] := (Nat.mod_modEq a 16).symm
    have hp16 : p^16 ≡ 1 [MOD 16] := by simpa only [← pow_mul, one_pow] using (block_values hp).1.pow 4
    have ex : p^a ≡ t.val^b.val [MOD 16] := by
      have e : p^a = p^(a%16)*(p^16)^(a/16) := by rw [← pow_mul,← pow_add,Nat.mod_add_div]
      rw [e]
      simpa only [one_pow,mul_one] using (ep.pow b.val).mul (hp16.pow (a/16))
    rw [twist_congr (ex.of_dvd (by decide))]
    have lhs := (ea.mul (weightBlock_congr ep)).add_left 1
    have rhs := (((ea.mul (geomBlock_congr ep)).add_left 1).mul ((ea.mul_left 2).add_right 1)).mul_right (twist (t.val^b.val))
    exact lhs.trans ((table t b (by dsimp [t]; have := Nat.odd_iff.mp hp; omega)).trans rhs.symm)

  have fourthData (v : ℕ) (hv : Odd v) :
      v^4 ≡ 1 [MOD 4] ∧ (v^4).divisors.card ≡ 1 [MOD 4] ∧ σ 1 (v^4) ≡ 1 [MOD 4] ∧
      moment (v^4) ≡ σ 1 (v^4)*(v^2).divisors.card*twist v [MOD 16] := by
    induction v using Nat.recOnPosPrimePosCoprime with
    | zero => have := hv.pos; omega
    | one => simp [moment,twist,Nat.ModEq]
    | prime_pow p a hp ha =>
      have hpo := hv.of_dvd_nat (dvd_pow_self p ha.ne')
      obtain ⟨hs,hf⟩ := sum_blocks hpo a
      have e4 : (p^a)^4 = p^(4*a) := by rw [← pow_mul, Nat.mul_comm a 4]
      have e2 : (p^a)^2 = p^(2*a) := by rw [← pow_mul, Nat.mul_comm a 2]
      rw [e4,e2]
      simp only [Nat.divisors_prime_pow hp,card_map,card_range,sigma_apply_prime_pow hp,mul_one]
      have pv : p^(4*a) ≡ 1 [MOD 4] := by simpa only [pow_mul, one_pow] using ((block_values hpo).1.pow a).of_dvd (by decide : 4 ∣ 16)
      have gs : 1+a*geomBlock p ≡ 1 [MOD 4] := by
        have h : a*geomBlock p ≡ 0 [MOD 4] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right (block_values hpo).2 _)
        simpa only [add_zero] using h.add_left 1
      refine ⟨pv, by simp [Nat.ModEq], (hs.of_dvd (by decide)).trans gs, ?_⟩
      dsimp only [moment]; rw [Nat.sum_divisors_prime_pow hp]
      simp only [Nat.divisors_prime_pow hp,card_map,card_range]
      exact (hf.trans (block_identity hpo a)).trans ((hs.symm.mul_right (2*a+1)).mul_right (twist (p^a)))
    | coprime a b ha hb hc ia ib =>
      have oa := hv.of_dvd_nat (dvd_mul_right a b)
      have ob := hv.of_dvd_nat (dvd_mul_left b a)
      obtain ⟨pa,ca,sa,fa⟩ := ia oa
      obtain ⟨pb,cb,sb,fb⟩ := ib ob
      have h4 : (a^4).Coprime (b^4) := (hc.pow_left 4).pow_right 4
      have h2 : (a^2).Coprime (b^2) := (hc.pow_left 2).pow_right 2
      rw [mul_pow, mul_pow, h4.card_divisors_mul, h2.card_divisors_mul, isMultiplicative_sigma.map_mul_of_coprime h4, moment_mul h4]
      refine ⟨by simpa using pa.mul pb,by simpa using ca.mul cb,by simpa using sa.mul sb,?_⟩
      apply (fa.mul fb).trans
      convert (twist_mul oa ob).symm.mul_left ((σ 1 (a^4)*σ 1 (b^4))*((a^2).divisors.card*(b^2).divisors.card)) using 1 <;> ring

  have fourth_root_mod_sixteen (v : ℕ) (hv : Odd v) :
      let m := v^4
      let A := m*m.divisors.card
      let F := ∑ d ∈ m.divisors, d*d.divisors.card
      let x := A-σ 1 m
      let y := F-A
      let k := x/y
      1 ≤ k → 2^(k+1)*(x-k*y) = x+y → (v^2).divisors.card ≡ twist v [MOD 16] := by
    let m := v^4
    let A := m*m.divisors.card
    let S := σ 1 m
    let F := moment m
    let x := A-S
    let y := F-A
    let k := x/y
    change 1 ≤ k → 2^(k+1)*(x-k*y) = x+y → _
    intro hk hb
    obtain ⟨hm,hc,hs,hf⟩ := fourthData v hv
    have ha : A ≡ 1 [MOD 4] := by simpa using hm.mul hc
    have hx : 4 ∣ x := (hs.trans ha.symm).dvd'
    have ht : 4 ∣ 2^(k+1) := pow_dvd_pow 2 (by omega : 2 ≤ k+1)
    have l4 : 4 ∣ x+y := hb ▸ dvd_mul_of_dvd_left ht _
    have hy : 4 ∣ y := (Nat.dvd_add_iff_right hx).mpr l4
    have hdiff : 4 ∣ x-k*y := Nat.dvd_sub hx (dvd_mul_of_dvd_right hy _)
    have l16 : 16 ∣ x+y := hb ▸ Nat.mul_dvd_mul ht hdiff
    have hsa : S ≤ A := by
      dsimp [S,A]; rw [sigma_one_apply]
      calc
        _ ≤ ∑ _d ∈ m.divisors, m := sum_le_sum fun _ hd ↦ Nat.divisor_le hd
        _ = _ := by simp [mul_comm]
    have haf : A ≤ F := single_le_sum (f := fun d : ℕ ↦ d*d.divisors.card) (fun _ _ ↦ Nat.zero_le _)
      (Nat.mem_divisors.mpr ⟨dvd_refl _,pow_ne_zero 4 hv.pos.ne'⟩)
    have hxy : x+y=F-S := by dsimp [x,y]; omega
    rw [hxy] at l16
    have heq := (Nat.modEq_iff_dvd' (hsa.trans haf)).mpr l16
    have so : Odd S := Nat.odd_iff.mpr (by have h := hs.of_dvd (by decide : 2∣4); exact h)
    have hcancel : (v^2).divisors.card*twist v ≡ 1 [MOD 16] := by
      apply Nat.ModEq.cancel_left_of_coprime ((Nat.coprime_two_left.mpr so).pow_left 4)
      simpa only [mul_one, mul_assoc] using hf.symm.trans heq.symm
    have htw : twist v*twist v ≡ 1 [MOD 16] := by unfold twist; split <;> decide
    exact (by simpa only [mul_assoc,mul_one] using ((htw.mul_left (v^2).divisors.card).symm.trans (by simpa [mul_assoc] using hcancel.mul_right (twist v))))
  obtain ⟨u,rfl⟩ := hsq.exists_sq
  dsimp only
  intro hk hb
  change balanced (u^2) at hb
  have huo := ho.of_dvd_nat (dvd_pow_self u (by decide : 2 ≠ 0))
  obtain ⟨v,rfl⟩ := (fourth_power huo hb).exists_sq
  have hv := huo.of_dvd_nat (dvd_pow_self v (by decide : 2 ≠ 0))
  have he : (v^2)^2=v^4 := by ring
  have hbig : 1 < v := by
    by_contra! h
    rcases (show v = 0 ∨ v = 1 by omega) with rfl|rfl <;> simp at hm
  have admiss := admissible_of_balance huo.pos.ne' hb
  rw [he] at hk hb
  exact ⟨v,hv,hbig,he,admiss,fourth_root_mod_sixteen v hv hk hb⟩

/-- Squarefree fourth roots have all positive cofactor exponents equal to four. -/
def H1 : Prop := ∀ v : ℕ, Odd v → 1 < v → Squarefree v →
    (∀ s : ℕ, (∀ p : ℕ, p.Prime → p ∣ v^2 → p ≡ 1 [MOD 2^s]) →
      (v^2).divisors.card ≡ 1 [MOD 2^s]) →
    (v^2).divisors.card ≡ (if v%8=3 ∨ v%8=5 then 9 else 1) [MOD 16] →
    let m := v^4
    let A := m*m.divisors.card
    let F := ∑ d ∈ m.divisors, d*d.divisors.card
    let x := A-σ 1 m
    let y := F-A
    let k := x/y
    1 ≤ k → 2^(k+1)*(x-k*y) ≠ x+y

/-- Nonsquarefree fourth roots have at least one cofactor exponent of eight or more. -/
def H2 : Prop := ∀ v : ℕ, Odd v → 1 < v → ¬ Squarefree v →
    (∀ s : ℕ, (∀ p : ℕ, p.Prime → p ∣ v^2 → p ≡ 1 [MOD 2^s]) →
      (v^2).divisors.card ≡ 1 [MOD 2^s]) →
    (v^2).divisors.card ≡ (if v%8=3 ∨ v%8=5 then 9 else 1) [MOD 16] →
    let m := v^4
    let A := m*m.divisors.card
    let F := ∑ d ∈ m.divisors, d*d.divisors.card
    let x := A-σ 1 m
    let y := F-A
    let k := x/y
    1 ≤ k → 2^(k+1)*(x-k*y) ≠ x+y

theorem main : H1 → H2 → OMA.R_OeisA245212_conjecture_R1_H2_R2.H1 := by
  intro hfree hrepeated m ho hm hsq
  dsimp only
  intro hk hb
  obtain ⟨v,hv,hbig,rfl,hsupp,hmod⟩ := square_restrictions m ho hm hsq hk hb
  by_cases hsf : Squarefree v
  · exact hfree v hv hbig hsf hsupp hmod hk hb
  · exact hrepeated v hv hbig hsf hsupp hmod hk hb

end OMA.R_OeisA245212_conjecture_R1_H2_R2_H1_R1
