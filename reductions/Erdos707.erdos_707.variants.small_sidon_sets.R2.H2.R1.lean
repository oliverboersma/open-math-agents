import OMAReductions.R_Erdos707_erdos_707_variants_small_sidon_sets_R2
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_Erdos707_erdos_707_variants_small_sidon_sets_R2_H2_R1
open Finset
open scoped Classical

lemma geom {w : ℂ} {d : ℕ} (hp : w^d=1) (hn : w≠1) : ∑ j ∈ range d, w^j = 0 := by
  have h := geom_sum_mul w d
  rw [hp,sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hn)

lemma four {d : ℕ} (hd : 0 < d) {w : ℂ} (prim : IsPrimitiveRoot w d) (S : Finset ℕ) :
    (∑ j ∈ (range d).erase 0, ∑ e ∈ S, (w^j)^e) =
      (d:ℂ)*((S.filter (d ∣ ·)).card:ℕ) - S.card := by
  have ch (e : ℕ) : ∑ j ∈ range d, (w^j)^e = if d∣e then (d:ℂ) else 0 := by
    simp_rw [← pow_mul, mul_comm _ e,pow_mul]
    by_cases h : d ∣ e
    · simp [if_pos h,(prim.pow_eq_one_iff_dvd _).mpr h]
    · rw [if_neg h]
      apply geom _ ((prim.pow_eq_one_iff_dvd _).not.mpr h)
      rw [← pow_mul,mul_comm,pow_mul,prim.pow_eq_one,one_pow]
  have total : (∑ j ∈ range d, ∑ e ∈ S, (w^j)^e) = (d:ℂ)*((S.filter (d∣·)).card:ℕ) := by
    rw [sum_comm]
    simp_rw [ch]
    rw [← sum_filter]; simp [mul_comm]
  have id := sum_erase_add (range d) (fun j => ∑ e ∈ S, (w^j)^e) (mem_range.mpr hd)
  rw [total] at id
  simpa using eq_sub_of_add_eq id

lemma shiftZero {m k : ℕ} {S : Finset ℕ} (inside : S ⊆ range m)
    (hs : ∀ e ∈ S, (e+k)%m ∈ S) {w : ℂ} (h : w^m=1) (hn : w^k≠1) :
    ∑ e ∈ S, w^e = 0 := by
  let f (e : ℕ) := (e+k)%m
  have inj : Set.InjOn f S := fun a ha b hb eq =>
    (Nat.ModEq.add_right_cancel' k eq).eq_of_lt_of_lt (mem_range.mp (inside ha)) (mem_range.mp (inside hb))
  have im : S.image f = S := Finset.eq_of_subset_of_card_le (by
    intro x hx; obtain ⟨e,he,rfl⟩ := mem_image.mp hx; exact hs e he) (by rw [card_image_of_injOn inj])
  have eq (e : ℕ) : w^(f e) = w^e*w^k := by
    rw [← pow_add]
    have hdiv := Nat.mod_add_div (e+k) m
    calc w^(f e) = w^((e+k)%m)* (w^m)^((e+k)/m) := by simp [f,h]
         _ = _ := by rw [← pow_mul,← pow_add,hdiv]
  have hh : ∑ e ∈ S, w^e = (∑ e ∈ S, w^e) * w^k := calc
    _ = ∑ e ∈ S.image f, w^e := by rw [im]
    _ = _ := by rw [sum_image inj]; simp_rw [eq]; rw [sum_mul]
  exact (mul_eq_zero.mp (show (∑ e ∈ S, w^e)*(w^k-1)=0 by rw [mul_sub,← hh,mul_one,sub_self])).resolve_right (sub_ne_zero.mpr hn)

lemma disc {m d k B : ℕ} (hd : d ∈ m.divisors) (S : Finset ℕ) (inside : S ⊆ range m)
    (hs : ∀ e ∈ S, (e+k)%m ∈ S)
    (hb : ∀ w : ℂ, w^m=1 → w≠1 → w^k=1 → ‖∑ e ∈ S, w^e‖ ≤ B) :
    |(m:ℤ)*((S.filter (d∣·)).card:ℤ) - (S.card:ℤ)*(((range m).filter (d∣·)).card:ℤ)| ≤ (m*B:ℕ) := by
  obtain ⟨hm,h0⟩ := Nat.mem_divisors.mp hd
  have dp : 0 < d := Nat.pos_of_dvd_of_pos hm (Nat.pos_of_ne_zero h0)
  let w := Complex.exp (2*Real.pi*Complex.I/d)
  have prim : IsPrimitiveRoot w d := Complex.isPrimitiveRoot_exp d dp.ne'
  let J := (range d).erase 0
  have ht (j : ℕ) (hj : j ∈ J) : (w^j)^m=1 ∧ w^j≠1 := by
    have ⟨nz,lt⟩ := mem_erase.mp hj
    refine ⟨?_,fun e => nz (Nat.eq_zero_of_dvd_of_lt ((prim.pow_eq_one_iff_dvd _).mp e) (mem_range.mp lt))⟩
    rw [← pow_mul,mul_comm,pow_mul,(prim.pow_eq_one_iff_dvd _).mpr hm,one_pow]
  have hfull := four dp prim (range m)
  have ef : ∑ j ∈ J, ∑ e ∈ range m, (w^j)^e = 0 := sum_eq_zero fun j hj => geom (ht j hj).1 (ht j hj).2
  rw [show (range d).erase 0 = J from rfl,ef,card_range] at hfull
  have hfull' : d*((range m).filter (d∣·)).card = m := by exact_mod_cast (sub_eq_zero.mp hfull.symm)
  have bn (j : ℕ) (hj : j ∈ J) : ‖∑ e ∈ S, (w^j)^e‖ ≤ B := by
    by_cases hk : (w^j)^k=1
    · exact hb _ (ht j hj).1 (ht j hj).2 hk
    · rw [shiftZero inside hs (ht j hj).1 hk,norm_zero]; positivity
  have est : ‖∑ j ∈ J, ∑ e ∈ S, (w^j)^e‖ ≤ (d:ℝ)*B := calc
    _ ≤ ∑ j ∈ J, ‖∑ e ∈ S, (w^j)^e‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ J, (B:ℝ) := sum_le_sum bn
    _ ≤ _ := by simp only [sum_const,nsmul_eq_mul]; gcongr; exact_mod_cast (card_le_card (erase_subset 0 (range d))).trans_eq (card_range d)
  change ‖∑ j ∈ (range d).erase 0, _‖ ≤ _ at est
  rw [four dp prim S] at est
  have ir : |(d:ℤ)*((S.filter (d∣·)).card:ℤ) - S.card| ≤ (d:ℤ)*B := by
    apply (Int.cast_le (R := ℝ)).mp
    rw [Int.cast_abs,← Real.norm_eq_abs,← Complex.norm_real]
    push_cast
    exact est
  obtain ⟨t,eq⟩ := hm
  have tc : t = ((range m).filter (d∣·)).card := Nat.eq_of_mul_eq_mul_left dp (eq.symm.trans hfull'.symm)
  have rr := mul_le_mul_of_nonneg_left ir (Int.natCast_nonneg t)
  rw [show (t:ℤ)*|_| = |(t:ℤ)*((d:ℤ)*((S.filter (d∣·)).card:ℤ) - S.card)| by rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg t)]] at rr
  push_cast
  rw [← tc, eq]
  push_cast
  simpa only [mul_sub,mul_assoc,mul_comm,mul_left_comm] using rr

/- For characters of the projective multiplicative group, the eigenvalue
bound for the covering curve in Will Sawin's MathOverflow answer 501999
gives a square-root estimate on one representative per scalar orbit. -/
def H1 : Prop := ∀ u v : ℕ, 0 < u → u < v → v ≠ 2*u → ∃ C N : ℕ,
  ∀ (F K : Type) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K] (g : K),
    Module.finrank F K = 3 → (Nat.card F).Prime → N ≤ Nat.card F →
    IsPrimitiveRoot g (Nat.card K - 1) →
    let q := Nat.card F
    let k := q^2+q+1
    let T := (range k).filter (fun e =>
      (¬ ∃ c : F, (g^e)^(u.gcd v) = algebraMap F K c) ∧
      ∃ s t : F, (g^e)^v = algebraMap F K s + algebraMap F K t * (g^e)^u)
    ∀ w : ℂ, w^k=1 → w≠1 → ‖∑ e ∈ T, w^e‖ ≤ (C*(q.sqrt+1):ℕ)

/- The candidate predicate descends to projective points. -/
def H2 : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra F K] (u v : ℕ) (x : K) (c : F), c ≠ 0 →
  let P (x : K) := (¬ ∃ a : F, x^(u.gcd v) = algebraMap F K a) ∧
      ∃ s t : F, x^v = algebraMap F K s + algebraMap F K t * x^u
  P (x*algebraMap F K c) ↔ P x

lemma blocks (f : ℕ → ℂ) {k : ℕ} (per : ∀ e, f (k+e) = f e) (t : ℕ) :
    ∑ e ∈ range (t*k), f e = (t:ℂ)*∑ e ∈ range k, f e := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.succ_mul,Nat.add_comm (t*k),sum_range_add]
    simp_rw [per,ih]
    push_cast; ring

theorem main : H1 → H2 → OMA.R_Erdos707_erdos_707_variants_small_sidon_sets_R2.H2 := by
  classical
  intro bound scale u v hu huv hv
  obtain ⟨C,N,bd⟩ := bound u v hu huv hv
  refine ⟨C,N,?_⟩
  intro F K _ _ _ _ _ g deg prime large prim
  let q := Nat.card F
  let m := Nat.card K - 1
  let k := q^2+q+1
  let P (x : K) := (¬ ∃ c : F, x^(u.gcd v) = algebraMap F K c) ∧
      ∃ s t : F, x^v = algebraMap F K s + algebraMap F K t * x^u
  let S := (range m).filter (fun e => P (g^e))
  let T := (range k).filter (fun e => P (g^e))
  have hq : 1 < q := prime.one_lt
  have mk : m = (q-1)*k := by
    dsimp [m,k,q]
    rw [Module.natCard_eq_pow_finrank (K := F) (V := K),deg]
    exact OMA.R_Erdos707_erdos_707_variants_small_sidon_sets_R2.OMA707Singer.cube_sub_one _ hq.le
  have pm : 0 < m := Nat.sub_pos_of_lt Finite.one_lt_card
  have gz : g ≠ 0 := by
    intro eq; have hh := prim.pow_eq_one
    change g^m=1 at hh
    simp [eq,zero_pow pm.ne'] at hh
  obtain ⟨c,hc⟩ : ∃ c : F, algebraMap F K c = g^k := by
    apply OMA.R_Erdos707_erdos_707_variants_small_sidon_sets_R2.OMA707Singer.mem_range_of_pow_card_eq
    change (g^k)^q = g^k
    conv_lhs => rw [← Nat.sub_add_cancel hq.le,pow_succ,← pow_mul,mul_comm k,← mk,prim.pow_eq_one,one_mul]
  have cz : c ≠ 0 := fun e => pow_ne_zero k gz (by simpa [e] using hc.symm)
  have per (e : ℕ) : P (g^(k+e)) ↔ P (g^e) := by
    rw [add_comm,pow_add,← hc]
    exact scale F K u v _ c cz
  have reduced (e : ℕ) : g^(e%m) = g^e := by rw [show m=orderOf g from prim.eq_orderOf,pow_mod_orderOf]
  dsimp only
  intro d hd
  change |(m:ℤ)*((S.filter (d∣·)).card:ℤ) - (S.card:ℤ)*(((range m).filter (d∣·)).card:ℤ)| ≤ _
  have ds := disc (k := k) (B := C*q*(q.sqrt+1)) hd S (filter_subset _ _) (fun e he => by
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (Nat.mod_lt _ pm),?_⟩
    rw [reduced,add_comm]; exact (per e).mpr (mem_filter.mp he).2)
  have err := ds (by
    intro w wm wn wk
    have small := bd F K g deg prime large prim w wk wn
    change ‖∑ e ∈ T, w^e‖ ≤ (C*(q.sqrt+1):ℕ) at small
    let f (e : ℕ) : ℂ := if P (g^e) then w^e else 0
    have fp (e : ℕ) : f (k+e) = f e := by
      by_cases hp : P (g^e)
      · simp only [f,if_pos hp,if_pos ((per e).mpr hp),pow_add,wk,one_mul]
      · simp only [f,if_neg hp,if_neg ((per e).not.mpr hp)]
    have eq : ∑ e ∈ S, w^e = ((q-1:ℕ):ℂ) * ∑ e ∈ T, w^e := by
      simp only [S,T,sum_filter]
      rw [mk]
      exact blocks f fp _
    rw [eq,norm_mul,Complex.norm_natCast]
    calc _ ≤ ((q:ℝ))*(C*(q.sqrt+1):ℕ) := mul_le_mul (by exact_mod_cast Nat.sub_le q 1) small (norm_nonneg _) (by positivity)
         _ = _ := by push_cast; ring)
  convert err using 1 <;> push_cast <;> ring

end OMA.R_Erdos707_erdos_707_variants_small_sidon_sets_R2_H2_R1
