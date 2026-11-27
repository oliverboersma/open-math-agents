import FormalConjectures.ErdosProblems.«307»
import Mathlib

/-!
Clear denominators in the coprime variant. Any witness is automatically cross-coprime.
At most 58 prime denominators cannot raise the combined reciprocal sum to two.
For each possible prime denominator, compare the gain over its reciprocal square.
The remaining square sum is bounded by telescoping on the two prime residues modulo six.
-/

open Finset

namespace OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R2

def H1 : Prop :=
  ∃ P Q : Finset ℕ, 1 < P.card ∧ 1 < Q.card ∧ Disjoint P Q ∧
    (∀ a ∈ P ∪ Q, 2 ≤ a) ∧ Set.Pairwise ((P ∪ Q : Finset ℕ) : Set ℕ) Nat.Coprime ∧
    59 ≤ ((P ∪ Q).filter Nat.Prime).card ∧
    (∑ a ∈ P, ∏ x ∈ P.erase a,x) * (∑ b ∈ Q, ∏ y ∈ Q.erase b,y) =
      (∏ a ∈ P,a) * (∏ b ∈ Q,b)

def H2 : Prop :=
  ∀ P Q : Finset ℕ, (∀ a ∈ P, 2 ≤ a) → (∀ b ∈ Q, 2 ≤ b) →
    (((∑ a ∈ P, ∏ x ∈ P.erase a,x) * (∑ b ∈ Q, ∏ y ∈ Q.erase b,y) =
        (∏ a ∈ P,a) * (∏ b ∈ Q,b)) ↔
      ((∑ a ∈ P,(a : ℚ)⁻¹) * (∑ b ∈ Q,(b : ℚ)⁻¹) = 1))

section Proof

private theorem prime_image_data {A : Finset ℕ}
    (hA : ∀ a ∈ A, 2 ≤ a) (hCop : Set.Pairwise (A : Set ℕ) Nat.Coprime) :
    (Set.InjOn Nat.minFac (A : Set ℕ)) ∧ ∀ p ∈ A.image Nat.minFac, p.Prime := by
  constructor
  · intro x hx y hy he
    by_contra hn
    have hp := Nat.minFac_prime (show x ≠ 1 by have := hA x hx; omega)
    have hd := (hCop hx hy hn).gcd_eq_one
    have hOne : x.minFac ∣ 1 := hd ▸ Nat.dvd_gcd (Nat.minFac_dvd x) (he ▸ Nat.minFac_dvd y)
    exact hp.not_dvd_one hOne
  · intro p hp
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hp
    exact Nat.minFac_prime (show a ≠ 1 by have := hA a ha; omega)

private theorem cofactor_sum_eq (A : Finset ℕ) (hA : ∀ a ∈ A, 2 ≤ a) :
    (∏ a ∈ A,(a : ℚ)) * (∑ a ∈ A,(1 : ℚ)/a) =
      (↑(∑ a ∈ A, ∏ x ∈ A.erase a,x) : ℚ) := by
  rw [mul_sum,Nat.cast_sum]
  apply sum_congr rfl
  intro a ha
  rw [Nat.cast_prod,← mul_prod_erase A (fun x : ℕ => (x : ℚ)) ha]
  have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by have := hA a ha; omega)
  field_simp

private theorem prime_not_dvd_cofactor_sum {A : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hA : Set.Pairwise (A : Set ℕ) Nat.Coprime)
    (hd : p ∣ ∏ a ∈ A,a) : ¬ p ∣ ∑ a ∈ A, ∏ x ∈ A.erase a,x := by
  obtain ⟨a,ha,hpa⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
  have hterm : ¬ p ∣ ∏ x ∈ A.erase a,x := by
    intro h
    obtain ⟨b,hb,hpb⟩ := (hp.prime.dvd_finsetProd_iff id).mp h
    obtain ⟨hne,hbA⟩ := mem_erase.mp hb
    exact hp.not_dvd_one ((hA ha hbA hne.symm).gcd_eq_one ▸ Nat.dvd_gcd hpa hpb)
  have hrest : p ∣ ∑ b ∈ A.erase a, ∏ x ∈ A.erase b,x := dvd_sum (by
    intro b hb
    exact hpa.trans (dvd_prod_of_mem id (mem_erase.mpr ⟨(mem_erase.mp hb).1.symm,ha⟩)))
  intro h
  rw [← add_sum_erase A _ ha] at h
  apply hterm
  simpa using Nat.dvd_sub h hrest

private theorem solution_cross_coprime (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, 2 ≤ p) (hQ : ∀ q ∈ Q, 2 ≤ q)
    (hPc : Set.Pairwise (P : Set ℕ) Nat.Coprime) (hQc : Set.Pairwise (Q : Set ℕ) Nat.Coprime)
    (hEq : (∑ a ∈ P,(1 : ℚ)/a) * (∑ b ∈ Q,(1 : ℚ)/b) = 1) :
    ∀ a ∈ P, ∀ b ∈ Q, a.Coprime b := by
  let M := ∏ a ∈ P,a
  let N := ∏ b ∈ Q,b
  let M' := ∑ a ∈ P, ∏ x ∈ P.erase a,x
  let N' := ∑ b ∈ Q, ∏ x ∈ Q.erase b,x
  have hNat : M'*N' = M*N := by
    have hRat : (M' : ℚ)*(N' : ℚ) = (M : ℚ)*(N : ℚ) := calc
      _ = ((M : ℚ) * ∑ a ∈ P,(1 : ℚ)/a) * ((N : ℚ) * ∑ b ∈ Q,(1 : ℚ)/b) := by
        have h1 := cofactor_sum_eq P hP
        have h2 := cofactor_sum_eq Q hQ
        simp only [M,N,M',N',Nat.cast_prod]
        rw [h1,h2]
      _ = ((M : ℚ)*(N : ℚ)) * ((∑ a ∈ P,(1 : ℚ)/a) * (∑ b ∈ Q,(1 : ℚ)/b)) := by ring
      _ = _ := by rw [hEq,mul_one]
    exact_mod_cast hRat
  intro a ha b hb
  by_contra hn
  have hne : a.gcd b ≠ 1 := hn
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd hne
  have hpM : p ∣ M := (hpd.trans (Nat.gcd_dvd_left a b)).trans (dvd_prod_of_mem id ha)
  have hpN : p ∣ N := (hpd.trans (Nat.gcd_dvd_right a b)).trans (dvd_prod_of_mem id hb)
  have hprod : p ∣ M'*N' := hNat ▸ dvd_mul_of_dvd_left hpM N
  rcases (hp.dvd_mul.mp hprod) with h|h
  · exact prime_not_dvd_cofactor_sum hp hPc hpM h
  · exact prime_not_dvd_cofactor_sum hp hQc hpN h

private theorem solution_union_data (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, 2 ≤ p) (hQ : ∀ q ∈ Q, 2 ≤ q)
    (hPc : Set.Pairwise (P : Set ℕ) Nat.Coprime) (hQc : Set.Pairwise (Q : Set ℕ) Nat.Coprime)
    (hEq : (∑ a ∈ P,(1 : ℚ)/a) * (∑ b ∈ Q,(1 : ℚ)/b) = 1) :
    Disjoint P Q ∧ (∀ a ∈ P ∪ Q, 2 ≤ a) ∧
    Set.Pairwise ((P ∪ Q : Finset ℕ) : Set ℕ) Nat.Coprime ∧
    (2 : ℚ) ≤ ∑ a ∈ P ∪ Q,(1 : ℚ)/a := by
  have hCross := solution_cross_coprime P Q hP hQ hPc hQc hEq
  have hDisj : Disjoint P Q := disjoint_left.mpr (by
    intro a ha hb
    have hc := (hCross a ha a hb).gcd_eq_one
    rw [Nat.gcd_self] at hc
    have := hP a ha
    omega)
  have hG : Set.Pairwise ((P ∪ Q : Finset ℕ) : Set ℕ) Nat.Coprime := by
    intro a ha b hb hne
    rcases mem_union.mp ha with ha|ha <;> rcases mem_union.mp hb with hb|hb
    · exact hPc ha hb hne
    · exact hCross a ha b hb
    · exact (hCross b hb a ha).symm
    · exact hQc ha hb hne
  have h2 : (2 : ℚ) ≤ ∑ a ∈ P ∪ Q,(1 : ℚ)/a := by
    rw [sum_union hDisj]
    let x := ∑ a ∈ P,(1 : ℚ)/a
    let y := ∑ a ∈ Q,(1 : ℚ)/a
    have hx : 0 ≤ x := sum_nonneg (fun a _ => by positivity)
    have hy : 0 ≤ y := sum_nonneg (fun a _ => by positivity)
    change x*y = 1 at hEq
    change 2 ≤ x+y
    by_contra! hlt
    have hProd' := mul_pos (show 0 < x+y+2 by linarith) (show 0 < 2-(x+y) by linarith)
    nlinarith [sq_nonneg (x-y)]
  exact ⟨hDisj,fun a ha => (mem_union.mp ha).elim (hP a) (hQ a),hG,h2⟩

private theorem small_primes_cut : ((range 277).filter Nat.Prime) = (range 272).filter Nat.Prime := by
  decide +kernel

private theorem gain_antitone {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (fun p : ℕ => (1 : ℚ)/p - ((1 : ℚ)/p)^2) b ≤ (fun p : ℕ => (1 : ℚ)/p - ((1 : ℚ)/p)^2) a := by
  have ha0 : (0 : ℚ) < a := by exact_mod_cast (show 0 < a by omega)
  have hb0 : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by omega)
  have hlow : (1 : ℚ)/b ≤ 1/a := one_div_le_one_div_of_le ha0 (by exact_mod_cast hab)
  have hhalf : (1 : ℚ)/a ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast ha)
  dsimp only
  nlinarith [mul_nonneg (sub_nonneg.mpr hlow)
    (show (0 : ℚ) ≤ 1 - ((1 : ℚ)/a + 1/b) by linarith)]

private theorem gain_nonneg {a : ℕ} (ha : 2 ≤ a) : 0 ≤ (fun p : ℕ => (1 : ℚ)/p - ((1 : ℚ)/p)^2) a := by
  have hhalf : (1 : ℚ)/a ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast ha)
  dsimp only
  nlinarith [mul_nonneg (show 0 ≤ (1 : ℚ)/a by positivity)
    (show (0 : ℚ) ≤ 1 - (1 : ℚ)/a by linarith)]

set_option maxHeartbeats 800000 in
private theorem gain_sum_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hCard : S.card ≤ 58) :
    (∑ p ∈ S, (fun p : ℕ => (1 : ℚ)/p - ((1 : ℚ)/p)^2) p) ≤ ∑ p ∈ ((range 277).filter Nat.Prime), (fun p : ℕ => (1 : ℚ)/p - ((1 : ℚ)/p)^2) p := by
  let T := S.filter (· < 272)
  let g (p : ℕ) := (fun p : ℕ => (1 : ℚ)/p - ((1 : ℚ)/p)^2) p - (fun p : ℕ => (1 : ℚ)/p - ((1 : ℚ)/p)^2) 271
  have hSmall : T ⊆ ((range 277).filter Nat.Prime) := by
    intro p hp
    obtain ⟨hpS,hpL⟩ := mem_filter.mp hp
    rw [small_primes_cut]
    exact mem_filter.mpr ⟨mem_range.mpr hpL,hS _ hpS⟩
  have hP (p : ℕ) (hp : p ∈ ((range 277).filter Nat.Prime)) : 0 ≤ g p := by
    rw [small_primes_cut] at hp
    obtain ⟨hpR,hpP⟩ := mem_filter.mp hp
    exact sub_nonneg.mpr (gain_antitone hpP.two_le (by have := mem_range.mp hpR; omega))
  have hCard' : (S.card : ℚ) ≤ 58 := by exact_mod_cast hCard
  have hCardSmall : ((range 277).filter Nat.Prime).card = 58 := by decide +kernel
  calc
    _ ≤ ∑ p ∈ S, ((if p < 272 then g p else 0) + (fun p : ℕ => (1 : ℚ)/p - ((1 : ℚ)/p)^2) 271) := by
      apply sum_le_sum
      intro p hp
      by_cases h : p < 272
      · simp only [h,if_true,g]
        linarith
      · simp only [h,if_false,zero_add]
        exact gain_antitone (by decide) (by omega)
    _ = (∑ p ∈ T, g p) + (S.card : ℚ)*(fun p : ℕ => (1 : ℚ)/p - ((1 : ℚ)/p)^2) 271 := by
      rw [sum_add_distrib,← sum_filter,sum_const,nsmul_eq_mul]
    _ ≤ (∑ p ∈ ((range 277).filter Nat.Prime), g p) + 58*(fun p : ℕ => (1 : ℚ)/p - ((1 : ℚ)/p)^2) 271 := by
      exact add_le_add (sum_le_sum_of_subset_of_nonneg hSmall (fun p hp _ => hP p hp))
        (mul_le_mul_of_nonneg_right hCard' (gain_nonneg (by decide)))
    _ = _ := by rw [show (∑ p ∈ ((range 277).filter Nat.Prime), g p) =
        ∑ p ∈ ((range 277).filter Nat.Prime), ((fun p : ℕ => (1 : ℚ)/p - ((1 : ℚ)/p)^2) p - (fun p : ℕ => (1 : ℚ)/p - ((1 : ℚ)/p)^2) 271) by rfl,
        sum_sub_distrib,sum_const,nsmul_eq_mul,hCardSmall]
                norm_num


private theorem tail_square_bound (e : ℕ) {N : ℕ} (hN : 46 ≤ N) :
    (∑ j ∈ Ico 46 N, (fun p : ℕ => ((1 : ℚ)/p)^2) (6*j+e-1)) ≤
      (1 : ℚ)/(6*(6*45+e-1 : ℕ)) - 1/(6*(6*(N-1)+e-1 : ℕ)) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [sum_Ico_succ_top hn]
    simp only [Nat.add_sub_cancel]
    let x : ℚ := (6*n+e-1 : ℕ)
    let y : ℚ := (6*(n-1)+e-1 : ℕ)
    have hx : 0 < x := by
      dsimp [x]
      exact_mod_cast (show 0 < 6*n+e-1 by omega)
    have hy : 0 < y := by
      dsimp [y]
      exact_mod_cast (show 0 < 6*(n-1)+e-1 by omega)
    have hxy : x = y + 6 := by
      change (↑(6*n+e-1 : ℕ) : ℚ) = ↑(6*(n-1)+e-1 : ℕ) + 6
      exact_mod_cast (show 6*n+e-1 = (6*(n-1)+e-1)+6 by omega)
    have hStep : (fun p : ℕ => ((1 : ℚ)/p)^2) (6*n+e-1) ≤ (1 : ℚ)/(6*y) - 1/(6*x) := by
      change ((1 : ℚ)/x)^2 ≤ 1/(6*y) - 1/(6*x)
      rw [div_pow,one_pow,pow_two]
      calc
        _ ≤ (1 : ℚ)/(y*x) := one_div_le_one_div_of_le (mul_pos hy hx)
          (mul_le_mul_of_nonneg_right (by linarith) hx.le)
        _ = _ := by field_simp [hx.ne',hy.ne']; linarith
    push_cast at ih ⊢
    change (∑ j ∈ Ico 46 n, (fun p : ℕ => ((1 : ℚ)/p)^2) (6*j+e-1)) ≤
      (1 : ℚ)/(6*(6*45+e-1 : ℕ)) - 1/(6*y) at ih
    change (∑ j ∈ Ico 46 n, (fun p : ℕ => ((1 : ℚ)/p)^2) (6*j+e-1)) +
      (fun p : ℕ => ((1 : ℚ)/p)^2) (6*n+e-1) ≤ (1 : ℚ)/(6*(6*45+e-1 : ℕ)) - 1/(6*x)
    linarith

private theorem large_prime_residue {p : ℕ} (hp : p.Prime) (hLarge : 277 ≤ p) :
    p%6 = 1 ∨ p%6 = 5 := by
  have h2 : ¬ 2 ∣ p := fun h => by
    rcases hp.eq_one_or_self_of_dvd 2 h with h'|h' <;> omega
  have h3 : ¬ 3 ∣ p := fun h => by
    rcases hp.eq_one_or_self_of_dvd 3 h with h'|h' <;> omega
  omega

private theorem progression_bound (U : Finset ℕ) (e : ℕ)
    (hU : ∀ p ∈ U, 46 ≤ (p+1)/6 ∧ p = 6*((p+1)/6)+e-1) :
    (∑ p ∈ U, (fun p : ℕ => ((1 : ℚ)/p)^2) p) ≤ (1 : ℚ)/(6*(6*45+e-1 : ℕ)) := by
  let j (p : ℕ) := (p+1)/6
  let V := U.image j
  let N := max 46 (V.sup id + 1)
  have hN : 46 ≤ N := le_max_left _ _
  have hInj : Set.InjOn j (U : Set ℕ) := by
    intro a ha b hb h
    exact (hU a ha).2.trans ((congrArg (fun n => 6*n+e-1) h).trans (hU b hb).2.symm)
  have hSub : V ⊆ Ico 46 N := by
    intro i hi
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hi
    exact mem_Ico.mpr ⟨(hU p hp).1,
      (Nat.lt_succ_of_le (le_sup (f := id) hi)).trans_le (le_max_right _ _)⟩
  calc
    _ = ∑ p ∈ U, (fun p : ℕ => ((1 : ℚ)/p)^2) (6*j p+e-1) :=
      sum_congr rfl (fun p hp => congrArg (fun p : ℕ => ((1 : ℚ)/p)^2) (hU p hp).2)
    _ = ∑ i ∈ V, (fun p : ℕ => ((1 : ℚ)/p)^2) (6*i+e-1) :=
      (sum_image (f := fun i => (fun p : ℕ => ((1 : ℚ)/p)^2) (6*i+e-1)) hInj).symm
    _ ≤ ∑ i ∈ Ico 46 N, (fun p : ℕ => ((1 : ℚ)/p)^2) (6*i+e-1) :=
      sum_le_sum_of_subset_of_nonneg hSub (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := (tail_square_bound e hN).trans (sub_le_self _ (by positivity))

set_option maxHeartbeats 500000 in
private theorem square_sum_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ p ∈ S, (fun p : ℕ => ((1 : ℚ)/p)^2) p) ≤
      (∑ p ∈ ((range 277).filter Nat.Prime), (fun p : ℕ => ((1 : ℚ)/p)^2) p) + (1/(6*269)+1/(6*271) : ℚ) := by
  let U := S.filter fun p => ¬p < 277
  have hLow : S.filter (· < 277) ⊆ ((range 277).filter Nat.Prime) := by
    intro p hp
    obtain ⟨hs,hl⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr hl,hS _ hs⟩
  have hHigh : (∑ p ∈ U, (fun p : ℕ => ((1 : ℚ)/p)^2) p) ≤ (1/(6*269)+1/(6*271) : ℚ) := by
    rw [← sum_filter_add_sum_filter_not _ (fun p => p%6 = 5)]
    apply add_le_add
    · have hBound := progression_bound (U.filter fun p => p%6 = 5) 0 (by
        intro p hp
        obtain ⟨hu,hm⟩ := mem_filter.mp hp
        have hLarge := (mem_filter.mp hu).2
        omega)
      norm_num at hBound ⊢
      exact hBound
    · have hBound := progression_bound (U.filter fun p => ¬p%6 = 5) 2 (by
        intro p hp
        obtain ⟨hu,hm⟩ := mem_filter.mp hp
        obtain ⟨hs,hLarge⟩ := mem_filter.mp hu
        have hp1 := (large_prime_residue (hS _ hs) (by omega)).resolve_right hm
        omega)
      norm_num at hBound ⊢
      exact hBound
  rw [← sum_filter_add_sum_filter_not _ (· < 277)]
  exact add_le_add (sum_le_sum_of_subset_of_nonneg hLow (fun _ _ _ => sq_nonneg _)) hHigh

private theorem sum_58_primes :
    (∑ p ∈ ((range 277).filter Nat.Prime), (1 : ℚ)/p) + (1/(6*269)+1/(6*271) : ℚ) < 2 := by
  let ps : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271]
  have hPrimes : ((range 277).filter Nat.Prime) = ps.toFinset := by decide +kernel
  rw [hPrimes,List.sum_toFinset _ (by decide +kernel : ps.Nodup)]
  decide +kernel

/-- Even an unbounded number of composite denominators cannot make up for
having at most 58 prime denominators. -/
theorem prime_cardinality (A : Finset ℕ) (hA : ∀ a ∈ A, 2 ≤ a)
    (hCop : Set.Pairwise (A : Set ℕ) Nat.Coprime)
    (hSum : 2 ≤ ∑ a ∈ A, (1 : ℚ)/a) : 59 ≤ (A.filter Nat.Prime).card := by
  by_contra! h
  let P := A.filter Nat.Prime
  obtain ⟨hInj,hPrime⟩ := prime_image_data hA hCop
  have hC : ∀ a ∈ A, ((1 : ℚ)/a) ≤ (fun p : ℕ => ((1 : ℚ)/p)^2) a.minFac +
      (if a.Prime then (fun p : ℕ => (1 : ℚ)/p - ((1 : ℚ)/p)^2) a else 0) := by
    intro a ha
    by_cases hp : a.Prime
    · rw [if_pos hp,hp.minFac_eq]
      dsimp only
      ring_nf
      rfl
    · rw [if_neg hp,add_zero]
      change (1 : ℚ)/a ≤ ((1 : ℚ)/a.minFac)^2
      rw [div_pow,one_pow]
      have hp0 : 0 < a.minFac := (Nat.minFac_prime (show a ≠ 1 by have := hA a ha; omega)).pos
      exact one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.minFac_sq_le_self (by have := hA a ha; omega) hp)
  have hUpper :=
    calc
      _ ≤ ∑ a ∈ A, ((fun p : ℕ => ((1 : ℚ)/p)^2) a.minFac + if a.Prime then (fun p : ℕ => (1 : ℚ)/p - ((1 : ℚ)/p)^2) a else 0) :=
        sum_le_sum hC
      _ = (∑ a ∈ A.image Nat.minFac, (fun p : ℕ => ((1 : ℚ)/p)^2) a) + ∑ a ∈ P, (fun p : ℕ => (1 : ℚ)/p - ((1 : ℚ)/p)^2) a := by
        rw [sum_add_distrib,← sum_filter,← sum_image (f := (fun p : ℕ => ((1 : ℚ)/p)^2)) hInj]
      _ ≤ ((∑ a ∈ ((range 277).filter Nat.Prime), (fun p : ℕ => ((1 : ℚ)/p)^2) a) + (1/(6*269)+1/(6*271) : ℚ)) +
          ∑ a ∈ ((range 277).filter Nat.Prime), (fun p : ℕ => (1 : ℚ)/p - ((1 : ℚ)/p)^2) a :=
        add_le_add (square_sum_bound _ hPrime)
          (gain_sum_bound P (fun p hp => (mem_filter.mp hp).2) (by change P.card < 59 at h; omega))
      _ = (∑ a ∈ ((range 277).filter Nat.Prime), (1 : ℚ)/a) + (1/(6*269)+1/(6*271) : ℚ) := by
        rw [add_right_comm,← sum_add_distrib]
        congr 1
        apply sum_congr rfl
        intro a _
        ring
  linarith [sum_58_primes]


private theorem positive_denominators (A : Finset ℕ) (hCard : 1 < A.card)
    (hOne : 1 ∉ A) (hCop : Set.Pairwise (A : Set ℕ) Nat.Coprime) :
    ∀ a ∈ A, 2 ≤ a := by
  intro a ha
  by_contra! hn
  have haz : a = 0 := by
    have h1 : a ≠ 1 := fun h => hOne (h ▸ ha)
    omega
  subst a
  have hNot : ¬A ⊆ ({0} : Finset ℕ) := by
    intro h
    have hh := card_le_card h
    simpa using (not_le_of_gt hCard) hh
  obtain ⟨b,hb,hbz⟩ := not_subset.mp hNot
  have hbne : b ≠ 0 := by simpa using hbz
  have hGcd := (hCop ha hb hbne.symm).gcd_eq_one
  rw [Nat.gcd_zero_left] at hGcd
  exact hOne (hGcd ▸ hb)

theorem cofactor_product_equivalence : H2 := by
  intro P Q hp hq
  let M := ∏ a ∈ P,(a : ℚ)
  let N := ∏ b ∈ Q,(b : ℚ)
  let U := ∑ a ∈ P,(1 : ℚ)/a
  let V := ∑ b ∈ Q,(1 : ℚ)/b
  have hM : 0 < M := prod_pos (fun a ha => by exact_mod_cast (show 0 < a by have := hp a ha; omega))
  have hN : 0 < N := prod_pos (fun b hb => by exact_mod_cast (show 0 < b by have := hq b hb; omega))
  have hleft := cofactor_sum_eq P hp
  have hright := cofactor_sum_eq Q hq
  rw [← Nat.cast_inj (R := ℚ),Nat.cast_mul,Nat.cast_mul,← hleft,← hright]
  simp only [Nat.cast_prod]
  change (M*U)*(N*V) = M*N ↔ _
  have he : (M*U)*(N*V) = (M*N)*(U*V) := by ring
  rw [he]
  simp only [← one_div]
  change (M*N)*(U*V) = M*N ↔ U*V = 1
  constructor
  · intro h
    exact mul_left_cancel₀ (mul_pos hM hN).ne' (h.trans (mul_one _).symm)
  · intro h
    rw [h,mul_one]

theorem main : H1 → H2 → type_of% @Erdos307.erdos_307.variants.coprime_one_notMem := by
  rintro ⟨P,Q,hP,hQ,hD,hMin,hCop,_,hInt⟩ h
  have hPl (p : ℕ) (hp : p ∈ P) := hMin p (mem_union_left Q hp)
  have hQl (q : ℕ) (hq : q ∈ Q) := hMin q (mem_union_right P hq)
  refine ⟨P,Q,?_,?_,hP,hQ,hCop.mono subset_union_left,hCop.mono subset_union_right,
    ((h P Q hPl hQl).mp hInt).symm⟩
  · intro hz
    have := hPl 0 (mem_inter.mp hz).1
    omega
  · intro hOne
    have := hMin 1 hOne
    omega

theorem converse :
    (type_of% @Erdos307.erdos_307.variants.coprime_one_notMem) → H1 := by
  rintro ⟨P,Q,_,hOne,hP,hQ,hPc,hQc,hRs⟩
  have hP0 := positive_denominators P hP (notMem_mono subset_union_left hOne) hPc
  have hQ0 := positive_denominators Q hQ (notMem_mono subset_union_right hOne) hQc
  obtain ⟨hD,hMin,hCop,hSum⟩ := solution_union_data P Q hP0 hQ0 hPc hQc
    (by simpa only [one_div] using hRs.symm)
  exact ⟨P,Q,hP,hQ,hD,hMin,hCop,prime_cardinality _ hMin hCop hSum,
    (cofactor_product_equivalence P Q hP0 hQ0).mpr hRs.symm⟩

end Proof

end OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R2
