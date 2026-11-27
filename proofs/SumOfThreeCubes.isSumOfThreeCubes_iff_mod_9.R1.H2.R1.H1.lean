import OMAReductions.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1_H2_R1
import Mathlib

/-! A finite-field cube sum with a nonzero coordinate. -/

namespace ThreeCubesLocal

open Finset Polynomial
open scoped Pointwise

private theorem cube_fiber (p : ℕ) [Fact p.Prime] (s : Finset (ZMod p)) (a : ZMod p) :
    (s.filter fun x => x ^ 3 = a).card ≤ 3 := by
  let f : (ZMod p)[X] := X ^ 3 - C a
  have hef : f ≠ 0 := X_pow_sub_C_ne_zero (by decide : 0 < 3) a
  calc
    _ ≤ f.roots.toFinset.card := by
      apply Finset.card_le_card
      intro x hx
      have h := (Finset.mem_filter.mp hx).2
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hef).mpr (by simp [f, h]))
    _ ≤ f.roots.card := Multiset.toFinset_card_le _
    _ ≤ 3 := card_roots_X_pow_sub_C (by decide) a

private theorem cube_sum (p : ℕ) (hp : p.Prime) (v : ZMod p) :
    ∃ x y z : ZMod p, x ≠ 0 ∧ x^3+y^3+z^3=v := by
  let : Fact p.Prime := ⟨hp⟩
  classical
  by_cases hv : v = 0
  · refine ⟨1,-1,0,one_ne_zero,?_⟩
    rw [hv]
    ring
  let V : Finset (ZMod p) := univ.erase 0
  let S := V.image (fun x => x^3)
  have hV : V.card = p-1 := by simp [V, ZMod.card]
  have hsize : p-1 ≤ S.card * 3 := by
    by_contra! h
    rw [← hV] at h
    obtain ⟨a,_,ha⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (fun x hx => Finset.mem_image_of_mem (fun x : ZMod p => x^3) hx) h
    exact (not_lt_of_ge (cube_fiber p V a)) ha
  have hs0 : 0 ∉ S := by
    intro hm
    obtain ⟨x,hx,hz⟩ := Finset.mem_image.mp hm
    exact (Finset.mem_erase.mp hx).1 ((pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hz)
  let A := insert 0 S
  have hc : A.card = S.card + 1 := Finset.card_insert_of_notMem hs0
  have hn : A.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  have h2 := ZMod.cauchy_davenport hp hn hn
  have h3 := ZMod.cauchy_davenport hp (Finset.Nonempty.add hn hn) hn
  have H : ((A+A)+A).card ≥ p := by
    have hAc : 1 ≤ A.card := hn.card_pos
    have hbound : 3*A.card ≥ p+2 := by have := hp.two_le; omega
    omega
  have hall : (A+A)+A = (univ : Finset (ZMod p)) := by
    apply Finset.eq_univ_of_card
    have hu : ((A+A)+A).card ≤ Fintype.card (ZMod p) := Finset.card_le_univ _
    rw [ZMod.card] at hu ⊢
    omega
  have acube (a : ZMod p) (ha : a ∈ A) : ∃ u : ZMod p, u^3=a := by
    rcases Finset.mem_insert.mp ha with rfl | hs
    · exact ⟨0, by simp⟩
    · obtain ⟨u,_,hu⟩ := Finset.mem_image.mp hs
      exact ⟨u,hu⟩
  have hmem : v ∈ (A+A)+A := by simp [hall]
  obtain ⟨d,hd,c,hc',he⟩ := Finset.mem_add.mp hmem
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.mem_add.mp hd
  obtain ⟨x,hx⟩ := acube a ha
  obtain ⟨y,hy⟩ := acube b hb
  obtain ⟨z,hz⟩ := acube c hc'
  have hxyz : x^3+y^3+z^3=v := by rw [hx,hy,hz,hab,he]
  by_cases hx0 : x = 0
  · by_cases hy0 : y = 0
    · have hz0 : z ≠ 0 := by
        rintro rfl
        exact hv (by simpa [hx0,hy0] using hxyz.symm)
      exact ⟨z,x,y,hz0,by linear_combination hxyz⟩
    · exact ⟨y,x,z,hy0,by linear_combination hxyz⟩
  · exact ⟨x,y,z,hx0,hxyz⟩

private def repr (n : ℤ) (m : ℕ) : Prop :=
  ∃ x y z : ZMod m, (n : ZMod m) = x^3+y^3+z^3

private theorem combine (n : ℤ) (hp : ∀ p k : ℕ, p.Prime → repr n (p^k)) :
    ∀ m : ℕ, 0 < m → repr n m := by
  intro m
  induction m using Nat.recOnPrimeCoprime with
  | zero => omega
  | prime_pow p k hprime => exact fun _ => hp p k hprime
  | coprime a b ha hb hab ia ib =>
    intro _
    obtain ⟨x,y,z,hxyz⟩ := ia (by omega)
    obtain ⟨X,Y,Z,hXYZ⟩ := ib (by omega)
    let e := ZMod.chineseRemainder hab
    refine ⟨e.symm (x,X),e.symm (y,Y),e.symm (z,Z),e.injective ?_⟩
    simp only [map_add, map_pow, map_intCast, RingEquiv.apply_symm_apply]
    exact Prod.ext hxyz hXYZ

private theorem lift_residue (p k : ℕ) (hp : p.Prime) (n a b c r w : ℤ)
    (ha : (a : ZMod p) ≠ 0) (hw : (w : ZMod p) ≠ 0)
    (hr : (p : ℤ) ∣ r) (hlin : 3*r = (p : ℤ)^k*w)
    (hquad : (p : ℤ)^(k+1) ∣ 3*r^2) (hcube : (p : ℤ)^(k+1) ∣ r^3)
    (hdvd : (p : ℤ)^k ∣ n - (a^3+b^3+c^3)) :
    ∃ A : ℤ, (A : ZMod p) ≠ 0 ∧ (p : ℤ)^(k+1) ∣ n - (A^3+b^3+c^3) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨d,hd⟩ := hdvd
  have hden : (w : ZMod p)*(a : ZMod p)^2 ≠ 0 := mul_ne_zero hw (pow_ne_zero _ ha)
  obtain ⟨u,hu⟩ := ZMod.natCast_zmod_surjective ((d : ZMod p) / ((w : ZMod p)*(a : ZMod p)^2))
  have hmod : (p : ℤ) ∣ d-w*a^2*(u : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hu, mul_comm ((w : ZMod p)*(a : ZMod p)^2), div_mul_cancel₀ _ hden, sub_self]
  refine ⟨a+r*(u : ℤ), ?_, ?_⟩
  · have hr0 := (ZMod.intCast_zmod_eq_zero_iff_dvd r p).mpr hr
    simpa [Int.cast_add, Int.cast_mul, hr0] using ha
  · have h₁ : (p : ℤ)^(k+1) ∣ (p : ℤ)^k * (d-w*a^2*(u : ℤ)) := by
      rw [pow_succ]
      exact mul_dvd_mul_left _ hmod
    have h₂ := dvd_mul_of_dvd_left hquad (a*(u : ℤ)^2)
    have h₃ := dvd_mul_of_dvd_left hcube ((u : ℤ)^3)
    have he : n - ((a+r*(u : ℤ))^3+b^3+c^3) =
        (p : ℤ)^k * (d-w*a^2*(u : ℤ)) - (3*r^2)*(a*(u : ℤ)^2) - r^3*(u : ℤ)^3 := by
      calc
        _ = (n-(a^3+b^3+c^3)) - (3*r)*(a^2*(u : ℤ)) - (3*r^2)*(a*(u : ℤ)^2) - r^3*(u : ℤ)^3 := by ring
        _ = _ := by rw [hd,hlin]; ring
    rw [he]
    exact Int.dvd_sub (Int.dvd_sub h₁ h₂) h₃

private theorem repr_of_dvd (n a b c : ℤ) (m : ℕ)
    (h : (m : ℤ) ∣ n - (a^3+b^3+c^3)) : repr n m := by
  refine ⟨a,b,c,?_⟩
  have h' := (ZMod.intCast_eq_intCast_iff_dvd_sub (a^3+b^3+c^3) n m).mpr h
  push_cast at h'
  exact h'.symm

private theorem base_prime (p : ℕ) (hp : p.Prime) (n : ℤ) :
    ∃ a b c : ℤ, (a : ZMod p) ≠ 0 ∧ (p : ℤ) ∣ n - (a^3+b^3+c^3) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x,y,z,hx,hxyz⟩ := cube_sum p hp (n : ZMod p)
  obtain ⟨a,ha⟩ := ZMod.natCast_zmod_surjective x
  obtain ⟨b,hb⟩ := ZMod.natCast_zmod_surjective y
  obtain ⟨c,hc⟩ := ZMod.natCast_zmod_surjective z
  refine ⟨a,b,c,by simpa [Int.cast_natCast,ha] using hx,?_⟩
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub ((a : ℤ)^3+(b : ℤ)^3+(c : ℤ)^3) n p).mp
  push_cast
  rwa [ha,hb,hc]

private theorem lifted_prime (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) (n : ℤ) (k : ℕ) :
    ∃ a b c : ℤ, (a : ZMod p) ≠ 0 ∧ (p : ℤ)^(k+1) ∣ n - (a^3+b^3+c^3) := by
  let : Fact p.Prime := ⟨hp⟩
  have h3 : ((3 : ℤ) : ZMod p) ≠ 0 := by
    intro hh
    have hdv := (ZMod.intCast_zmod_eq_zero_iff_dvd 3 p).mp hh
    have hnat : p ∣ 3 := by exact_mod_cast hdv
    rcases (Nat.dvd_prime Nat.prime_three).mp hnat with he | he
    · exact hp.ne_one he
    · exact hp3 he
  induction k with
  | zero => simpa using base_prime p hp n
  | succ k ih =>
    obtain ⟨a,b,c,ha,hdvd⟩ := ih
    let r := (p : ℤ)^(k+1)
    have hr : (p : ℤ) ∣ r := by dsimp [r]; rw [pow_succ]; exact dvd_mul_left _ _
    have hlin : 3*r = (p : ℤ)^(k+1)*3 := mul_comm _ _
    have hquad : (p : ℤ)^(k+1+1) ∣ 3*r^2 := by
      unfold r
      rw [← pow_mul]
      exact dvd_mul_of_dvd_right (pow_dvd_pow _ (by omega)) _
    have hcube : (p : ℤ)^(k+1+1) ∣ r^3 := by
      unfold r
      rw [← pow_mul]
      exact pow_dvd_pow _ (by omega)
    obtain ⟨A,hA,hAd⟩ := lift_residue p (k+1) hp n a b c r 3 ha h3 hr hlin hquad hcube hdvd
    exact ⟨A,b,c,hA,hAd⟩

private def digit (a : Fin 3) : ℤ := (a.val : ℤ)-1

private theorem base_three_table : ∀ j : Fin 9, j ≠ 4 → j ≠ 5 →
    ∃ a b c : Fin 3, (digit a : ZMod 3) ≠ 0 ∧
      (digit a : ZMod 9)^3+(digit b : ZMod 9)^3+(digit c : ZMod 9)^3=(j.val : ZMod 9) := by
  decide +kernel

private theorem base_three (n : ℤ) (hn : ¬ (n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9])) :
    ∃ a b c : ℤ, (a : ZMod 3) ≠ 0 ∧ (3 : ℤ)^2 ∣ n - (a^3+b^3+c^3) := by
  have h₀ := Int.emod_nonneg n (by decide : (9 : ℤ) ≠ 0)
  have h₉ := Int.emod_lt_of_pos n (by decide : (0 : ℤ) < 9)
  let j : Fin 9 := ⟨(n%9).toNat, by omega⟩
  have hj : (j.val : ℤ) = n%9 := Int.toNat_of_nonneg h₀
  have hjn : (j.val : ZMod 9) = (n : ZMod 9) := by
    rw [← Int.cast_natCast, hj]
    exact ZMod.intCast_mod n 9
  have h4 : j ≠ 4 := by
    intro he
    apply hn
    left
    apply (ZMod.intCast_eq_intCast_iff n 4 9).mp
    simpa [he] using hjn.symm
  have h5 : j ≠ 5 := by
    intro he
    apply hn
    right
    apply (ZMod.intCast_eq_intCast_iff n 5 9).mp
    simpa [he] using hjn.symm
  obtain ⟨a,b,c,ha,habc⟩ := base_three_table j h4 h5
  refine ⟨digit a,digit b,digit c,ha,?_⟩
  change (9 : ℤ) ∣ n - (digit a^3+digit b^3+digit c^3)
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub (digit a^3+digit b^3+digit c^3) n 9).mp
  push_cast
  exact habc.trans hjn

private theorem lifted_three (n : ℤ) (hn : ¬ (n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9])) (k : ℕ) :
    ∃ a b c : ℤ, (a : ZMod 3) ≠ 0 ∧ (3 : ℤ)^(k+2) ∣ n - (a^3+b^3+c^3) := by
  induction k with
  | zero => exact base_three n hn
  | succ k ih =>
    obtain ⟨a,b,c,ha,hdvd⟩ := ih
    let r := (3 : ℤ)^(k+1)
    have hr : (3 : ℤ) ∣ r := by dsimp [r]; rw [pow_succ]; exact dvd_mul_left _ _
    have hlin : 3*r = (3 : ℤ)^(k+2)*1 := by
      simpa only [r, mul_one] using (pow_succ' (3 : ℤ) (k+1)).symm
    have hquad : (3 : ℤ)^(k+2+1) ∣ 3*r^2 := by
      unfold r
      rw [← pow_mul, ← pow_succ']
      exact pow_dvd_pow _ (by omega)
    have hcube : (3 : ℤ)^(k+2+1) ∣ r^3 := by
      unfold r
      rw [← pow_mul]
      exact pow_dvd_pow _ (by omega)
    obtain ⟨A,hA,hAd⟩ := lift_residue 3 (k+2) Nat.prime_three n a b c r 1 ha (by decide)
      hr hlin hquad hcube hdvd
    exact ⟨A,b,c,hA,hAd⟩

private theorem forbidden_table : ∀ x y z : ZMod 9,
    x^3+y^3+z^3 ≠ 4 ∧ x^3+y^3+z^3 ≠ 5 := by decide +kernel

theorem main (n : ℤ) :
    (∀ m : ℕ, 0 < m → repr n m) ↔ ¬ (n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9]) := by
  constructor
  · intro hn hbad
    obtain ⟨x,y,z,hxyz⟩ := hn 9 (by decide)
    obtain ⟨h4,h5⟩ := forbidden_table x y z
    rcases hbad with hh | hh
    · exact h4 (hxyz.symm.trans ((ZMod.intCast_eq_intCast_iff n 4 9).mpr hh))
    · exact h5 (hxyz.symm.trans ((ZMod.intCast_eq_intCast_iff n 5 9).mpr hh))
  · intro hn
    apply combine n
    intro p k hp
    rcases k with _ | k
    · rw [pow_zero]
      exact ⟨0,0,0,Subsingleton.elim _ _⟩
    by_cases hp3 : p=3
    · subst p
      rcases k with _ | k
      · obtain ⟨a,b,c,_,h⟩ := base_three n hn
        apply repr_of_dvd n a b c
        have h' : (3 : ℤ)^1 ∣ n - (a^3+b^3+c^3) :=
          (pow_dvd_pow _ (by decide : 1 ≤ 2)).trans h
        simpa using h'
      · obtain ⟨a,b,c,_,h⟩ := lifted_three n hn k
        exact repr_of_dvd n a b c _ (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using h)
    · obtain ⟨a,b,c,_,h⟩ := lifted_prime p hp hp3 n k
      exact repr_of_dvd n a b c _ (by simpa only [Nat.cast_pow] using h)

end ThreeCubesLocal

theorem OMA.solution : OMA.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1_H2_R1.H1 :=
  ThreeCubesLocal.main