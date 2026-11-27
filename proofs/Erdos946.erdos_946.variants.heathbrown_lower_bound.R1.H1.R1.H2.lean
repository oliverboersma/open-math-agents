import OMAReductions.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1

/-! Heath-Brown's sieve in prescribed prime-power progressions. -/
namespace OMA.HeathCRT946
open Finset

private theorem affine_zero {h k m : ℕ} (mp : 0 < m) (cop : k.Coprime m) :
    ∃ t : ℕ, m ∣ k*t+h := by
  let _ : NeZero m := ⟨mp.ne'⟩
  refine ⟨(-(k:ZMod m)⁻¹ * (h:ZMod m)).val, (ZMod.natCast_eq_zero_iff _ _).mp ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  rw [neg_mul, mul_neg, ←mul_assoc,ZMod.coe_mul_inv_eq_one _ cop]
  ring

/-- Divide the seven linear forms by prescribed, mutually coprime prime powers
on a single common arithmetic progression. The resulting forms are pairwise
nonproportional and have no fixed prime divisor in their product. -/
theorem forms (a q e : Fin 7 → ℕ) (mono : StrictMono a) (ap : ∀ i, 0<a i)
    (qi : Function.Injective q) (qp : ∀ i, (q i).Prime) (aq : ∀ i j, a i<q j) :
    ∃ h M : ℕ, ∃ s c : Fin 7 → ℕ, 0<M ∧ (∀ i, 0<s i) ∧
      (∀ i t, q i^e i * (s i*t+c i) = a i*(h+M*t)+1) ∧
      (∀ i j, i≠j → s i*c j ≠ s j*c i) ∧
      ∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬p∣s i*t+c i := by
  classical
  let b (i : Fin 7) := q i ^ e i
  have bp (i) : 0<b i := pow_pos (qp i).pos _
  have cop (i j) : (a i).Coprime (b j) := by
    apply Nat.Coprime.pow_right
    exact ((qp j).coprime_iff_not_dvd.mpr (fun dv =>
      (aq i j).not_ge (Nat.le_of_dvd (ap i) dv))).symm
  have pair (i j) (ne:i≠j) : (b i).Coprime (b j) := by
    exact (((Nat.coprime_primes (qp i) (qp j)).mpr (fun eq => ne (qi eq))).pow_left _).pow_right _
  choose res resprop using (fun i => affine_zero (h:=1) (bp i) (cop i i))
  let h := Nat.chineseRemainderOfFinset res b univ (fun i _ => (bp i).ne')
    (fun i _ j _ ne => pair i j ne)
  have dv (i) : b i∣a i*h.val+1 := by
    have u := ((h.property i (mem_univ _)).mul_left (a i)).add_right 1
    exact (Nat.modEq_zero_iff_dvd.mp (u.trans (Nat.modEq_zero_iff_dvd.mpr (resprop i))))
  let M := ∏ i, b i
  let rem (i : Fin 7) := ∏ j∈univ.erase i,b j
  have prod (i) : b i*rem i=M := mul_prod_erase _ _ (mem_univ _)
  have mp : 0<M := prod_pos fun i _ => bp i
  let s (i : Fin 7) := a i*rem i
  let c (i : Fin 7) := (a i*h.val+1)/b i
  have sp (i) : 0<s i := Nat.mul_pos (ap i) (prod_pos fun j _ => bp j)
  have sc (i) : b i*s i=a i*M := by
    change b i*(a i*rem i)=a i*M
    rw [←prod i]; ring
  have cc (i) : b i*c i=a i*h.val+1 := Nat.mul_div_cancel' (dv i)
  have form (i t) : b i*(s i*t+c i)=a i*(h.val+M*t)+1 := by
    rw [Nat.mul_add,←Nat.mul_assoc,sc,cc]; ring
  refine ⟨h.val,M,s,c,mp,sp,form,?_,?_⟩
  · intro i j ne eq
    have he : (b i*s i)*(b j*c j)=(b j*s j)*(b i*c i) := by
      calc
        _ = (b i*b j)*(s i*c j) := by ring
        _ = (b i*b j)*(s j*c i) := by rw [eq]
        _ = _ := by ring
    rw [sc,sc,cc,cc] at he
    have hmul : a i*M=a j*M := by nlinarith only [he]
    exact ne (mono.injective (Nat.eq_of_mul_eq_mul_right mp hmul))
  · intro p pp
    by_cases ∃ j, p∣b j
    · obtain ⟨j,pj⟩ := ‹∃ j, p∣b j›
      have eqp : p=q j := (Nat.prime_dvd_prime_iff_eq pp (qp j)).mp (pp.dvd_of_dvd_pow pj)
      have others (i) (ne:i≠j) (t) : ¬p∣s i*t+c i := by
        intro divides
        have pi : p∣a i*(h.val+M*t)+1 := form i t ▸ dvd_mul_of_dvd_right divides _
        have pj' : p∣a j*(h.val+M*t)+1 := form j t ▸ dvd_mul_of_dvd_left pj _
        have ei : (a i:ZMod p)*(h.val+M*t)+1 = 0 := by
          exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr pi
        have ej : (a j:ZMod p)*(h.val+M*t)+1 = 0 := by
          exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr pj'
        have eq : (a i : ZMod p) = a j := by
          linear_combination (a i:ZMod p)*ej-(a j:ZMod p)*ei
        have small (k) : a k < p := eqp ▸ aq k j
        have eql := (ZMod.natCast_eq_natCast_iff' _ _ _).mp eq
        rw [Nat.mod_eq_of_lt (small i),Nat.mod_eq_of_lt (small j)] at eql
        exact ne (mono.injective eql)
      have slope : ¬p∣s j := by
        have ar : p.Coprime (a j) := pp.coprime_iff_not_dvd.mpr (fun dvd =>
          (aq j j).not_ge (eqp ▸ Nat.le_of_dvd (ap j) dvd))
        have pr : p.Coprime (rem j) := by
          apply Nat.Coprime.prod_right
          intro k hk
          apply Nat.Coprime.pow_right
          rw [eqp]
          apply (Nat.coprime_primes (qp j) (qp k)).mpr
          exact fun e => (ne_of_mem_erase hk) (qi e).symm
        exact (pp.coprime_iff_not_dvd).mp (ar.mul_right pr)
      by_cases hit : p∣c j
      · refine ⟨1,fun i => ?_⟩
        by_cases ij:i=j
        · subst i
          simpa only [Nat.mul_one] using (fun v : p∣s j+c j => slope ((Nat.dvd_add_iff_left hit).mpr v))
        · exact others _ ij _
      · refine ⟨0,fun i => ?_⟩
        by_cases ij:i=j
        · simpa only [ij,Nat.mul_zero,Nat.zero_add] using hit
        · exact others _ ij _
    · rename_i none
      have pm : p.Coprime M := Nat.Coprime.prod_right fun i _ =>
        pp.coprime_iff_not_dvd.mpr (fun dv => none ⟨i,dv⟩)
      obtain ⟨t,tgood⟩ := affine_zero (h:=h.val) pp.pos pm.symm
      refine ⟨t,fun i bad => ?_⟩
      have pt : p∣a i*(h.val+M*t) := dvd_mul_of_dvd_right (Nat.add_comm _ _ ▸ tgood) _
      have left : p∣a i*(h.val+M*t)+1 := form i t ▸ dvd_mul_of_dvd_right bad _
      exact pp.not_dvd_one ((Nat.dvd_add_iff_right pt).mpr left)

end OMA.HeathCRT946

theorem OMA.solution : OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1.H2 := OMA.HeathCRT946.forms
