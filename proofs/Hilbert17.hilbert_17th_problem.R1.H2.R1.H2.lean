import OMAReductions.R_Hilbert17_hilbert_17th_problem_R1_H2_R1
import Mathlib
/- The preordering argument and odd irreducible factor lemma adapt work of
Florent Schaffhauser and Artie Khovanov in artie2000/real_closed_field,
RealClosedField/Algebra/Order/Ring/Ordering/Extend.lean and RealClosedField/Upstream.lean,
revision 24ec7b819140a17848e88e7d6decde198a140918. Used under Apache-2.0.
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Copyright (c) 2025 Artie Khovanov. All rights reserved. -/

open Polynomial
namespace LocalReal17

lemma order_preordering {F : Type} [Field F] (P : RingPreordering F) :
    ∃ (_ : LinearOrder F) (_ : IsStrictOrderedRing F), ∀ z ∈ P, 0 ≤ z := by
  classical
  let good (B : Subsemiring F) := (∀ x : F, x*x ∈ B) ∧ -1 ∉ B
  have chain : ∀ c ⊆ {B | good B}, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ B ∈ {B | good B}, ∀ u ∈ c, u ≤ B := by
    intro c hc hdir y hy
    letI : Nonempty c := ⟨⟨y,hy⟩⟩
    let B := ⨆ u : c, u.val
    have mem (x : F) : x ∈ B ↔ ∃ u : c, x ∈ u.val :=
      Subsemiring.mem_iSup_of_directed hdir.directedOn.directed_val
    refine ⟨B,⟨fun x => (mem _).mpr ⟨⟨y,hy⟩,(hc hy).1 x⟩,?_⟩,fun u hu => le_iSup (fun v : c => v.val) ⟨u,hu⟩⟩
    intro h
    obtain ⟨u,hu⟩ := (mem _).mp h
    exact (hc u.property).2 hu
  obtain ⟨B,hPB,hB⟩ := zorn_le_nonempty₀ {B | good B} chain P.toSubsemiring
    ⟨P.mul_self_mem,P.neg_one_notMem⟩
  let M := RingPreordering.mk' (B : Set F) B.add_mem B.mul_mem hB.prop.1 hB.prop.2
  have total (a : F) : a ∈ B ∨ -a ∈ B := by
    by_cases ha : -a ∈ B
    · exact Or.inr ha
    let T := Subsemiring.closure (insert a (B : Set F))
    have inc : B ≤ T := fun x hx => Subsemiring.subset_closure (Set.mem_insert_of_mem _ hx)
    have repr {x : F} (hx : x ∈ T) : ∃ u ∈ B, ∃ v ∈ B, x = u+a*v := by
      induction hx using Subsemiring.closure_induction with
      | mem x hx =>
        rcases hx with rfl|hx
        · exact ⟨0,B.zero_mem,1,B.one_mem,by ring⟩
        · exact ⟨x,hx,0,B.zero_mem,by ring⟩
      | zero => exact ⟨0,B.zero_mem,0,B.zero_mem,by ring⟩
      | one => exact ⟨1,B.one_mem,0,B.zero_mem,by ring⟩
      | add x y _ _ hx hy =>
        obtain ⟨u,hu,v,hv,rfl⟩ := hx
        obtain ⟨s,hs,t,ht,rfl⟩ := hy
        exact ⟨u+s,B.add_mem hu hs,v+t,B.add_mem hv ht,by ring⟩
      | mul x y _ _ hx hy =>
        obtain ⟨u,hu,v,hv,rfl⟩ := hx
        obtain ⟨s,hs,t,ht,rfl⟩ := hy
        exact ⟨u*s + a*a*(v*t),B.add_mem (B.mul_mem hu hs) (B.mul_mem (hB.prop.1 a) (B.mul_mem hv ht)),
          u*t+s*v,B.add_mem (B.mul_mem hu ht) (B.mul_mem hs hv),by ring⟩
    have proper : -1 ∉ T := by
      intro h
      obtain ⟨u,hu,v,hv,e⟩ := repr h
      by_cases h0 : v = 0
      · have hu' : (-1 : F) = u := by simpa [h0] using e
        exact hB.prop.2 (hu' ▸ hu)
      · have eq : -a = (1+u)*v⁻¹ := by field_simp; linear_combination e
        exact ha (eq ▸ B.mul_mem (B.add_mem B.one_mem hu) (RingPreordering.inv_mem (P := M) hv))
    exact Or.inl <| hB.le_of_ge ⟨fun x => inc (hB.prop.1 x),proper⟩ inc
      (Subsemiring.subset_closure (Set.mem_insert a _))
  let C : RingCone F := ⟨B,fun hx hn => M.eq_zero_of_mem_of_neg_mem hx hn⟩
  letI : HasMemOrNegMem C := ⟨total⟩
  letI : LinearOrder F := .mkOfAddGroupCone C
  letI : IsOrderedRing F := IsOrderedRing.mkOfCone C
  refine ⟨inferInstance,inferInstance,fun z hz => ?_⟩
  change z-0 ∈ B
  simpa using hPB hz

lemma odd_factor {F : Type} [Field F] {f : F[X]} (hf : Odd f.natDegree) :
    ∃ g : F[X], Odd g.natDegree ∧ g.Monic ∧ Irreducible g ∧ g ∣ f := by
  induction h : f.natDegree using Nat.strong_induction_on generalizing f with | h n ih =>
    have hu : ¬ IsUnit f := not_isUnit_of_natDegree_pos _ (Odd.pos hf)
    rcases exists_monic_irreducible_factor f hu with ⟨g,gm,gi,gd⟩
    by_cases ho : Odd g.natDegree
    · exact ⟨g,ho,gm,gi,gd⟩
    · rcases gd with ⟨k,rfl⟩
      have ke : k ≠ 0 := by rintro rfl; simp at hf
      have deg := natDegree_mul gi.ne_zero ke
      have kg : Odd k.natDegree := by grind
      obtain ⟨p,hp,pm,pi,pd⟩ := ih k.natDegree (by have := gi.natDegree_pos; omega) kg rfl
      exact ⟨p,hp,pm,pi,dvd_trans pd (dvd_mul_left ..)⟩

lemma pos_even_add {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {p q : F[X]} (hp : 0 < p.leadingCoeff) (hq : 0 < q.leadingCoeff)
    (he : Even p.natDegree) (hf : Even q.natDegree) :
    0 < (p+q).leadingCoeff ∧ Even (p+q).natDegree := by
  rcases lt_trichotomy p.degree q.degree with h|h|h
  · simpa [leadingCoeff_add_of_degree_lt h,natDegree_add_eq_right_of_degree_lt h] using And.intro hq hf
  · have hn := (add_pos hp hq).ne'
    have hd : (p+q).degree = p.degree := by rw [degree_add_eq_of_leadingCoeff_add_ne_zero hn,h,max_self]
    exact ⟨by rw [leadingCoeff_add_of_degree_eq h hn]; exact add_pos hp hq,
      by rwa [natDegree,hd]⟩
  · simpa [leadingCoeff_add_of_degree_lt' h,natDegree_add_eq_left_of_degree_lt h] using And.intro hp he

lemma lift_positive {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {f : F[X]} (hf : f.Monic) (hi : Irreducible f) {s : AdjoinRoot f} (hs : IsSumSq s) :
    ∃ p : F[X], AdjoinRoot.mk f p = 1+s ∧ 0 < p.leadingCoeff ∧ Even p.natDegree ∧
      p.natDegree < 2*f.natDegree ∧
      ∀ (E : Type) [Field E] [LinearOrder E] [IsStrictOrderedRing E] [Algebra F E]
        (r : E), 0 < p.aeval r := by
  have hn := hi.natDegree_pos
  induction hs with
  | zero =>
    refine ⟨1,by simp,by simp,by simp,by simp; omega,?_⟩
    intro E _ _ _ _ r; simp
  | @sq_add y s _ ih =>
    obtain ⟨p,hp,hc,he,hd,hpos⟩ := ih
    obtain ⟨b,hb⟩ := AdjoinRoot.mk_surjective (g := f) y
    let t := b %ₘ f
    have hdeg : t.natDegree < f.natDegree := natDegree_modByMonic_lt b hf (fun e => hi.not_isUnit (e ▸ isUnit_one))
    have ht : AdjoinRoot.mk f t = y := by
      rw [← hb]; simpa [t] using AdjoinRoot.mk_leftInverse hf (AdjoinRoot.mk f b)
    refine ⟨t*t+p,by rw [map_add,map_mul,ht,hp]; ring,?_,?_,?_,?_⟩
    · by_cases hz : t = 0
      · simpa [hz] using hc
      · exact (pos_even_add (p := t*t) (by rw [leadingCoeff_mul]; exact mul_self_pos.mpr (leadingCoeff_ne_zero.mpr hz)) hc
          (by rw [natDegree_mul hz hz]; exact Even.add_self _) he).1
    · by_cases hz : t = 0
      · simpa [hz] using he
      · exact (pos_even_add (p := t*t) (by rw [leadingCoeff_mul]; exact mul_self_pos.mpr (leadingCoeff_ne_zero.mpr hz)) hc
          (by rw [natDegree_mul hz hz]; exact Even.add_self _) he).2
    · apply lt_of_le_of_lt (natDegree_add_le ..)
      exact max_lt (by have := natDegree_mul_le (p := t) (q := t); omega) hd
    · intro E _ _ _ _ r
      simpa only [map_add,map_mul] using add_pos_of_nonneg_of_pos (mul_self_nonneg (t.aeval r)) (hpos E r)

lemma odd_extension (order : ∀ {E : Type} [Field E] (P : RingPreordering E),
    ∃ (_ : LinearOrder E) (_ : IsStrictOrderedRing E), ∀ z ∈ P, 0 ≤ z)
    {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (sq : ∀ a : F, 0 ≤ a → IsSquare a) (f : F[X]) (hf : Odd f.natDegree) :
    ∃ (E : Type) (_ : Field E) (_ : LinearOrder E) (_ : IsStrictOrderedRing E)
      (_ : Algebra F E) (_ : Algebra.IsAlgebraic F E),
      (∀ x : F, 0 ≤ x → 0 ≤ algebraMap F E x) ∧ ∃ y : E, f.aeval y = 0 := by
  classical
  induction n : f.natDegree using Nat.strong_induction_on generalizing f with | h n ih =>
    obtain ⟨g,go,gm,gi,gd⟩ := odd_factor hf
    have fne : f ≠ 0 := by rintro rfl; simp at hf
    have gle := natDegree_le_of_dvd gd fne
    letI : Fact (Irreducible g) := ⟨gi⟩
    have proper : ¬ IsSumSq (-1 : AdjoinRoot g) := by
      intro hs
      obtain ⟨p,hp,hc,he,hd,hpos⟩ := lift_positive gm gi hs
      obtain ⟨q,hq⟩ := AdjoinRoot.mk_eq_zero.mp (show AdjoinRoot.mk g p = 0 by simpa using hp)
      have pne : p ≠ 0 := by intro h; simp [h] at hc
      have qne : q ≠ 0 := by rintro rfl; simp_all
      have ds : p.natDegree = g.natDegree + q.natDegree := by rw [hq,natDegree_mul gi.ne_zero qne]
      have qo : Odd q.natDegree := by grind
      obtain ⟨E,_,_,_,_,_,_,r,hr⟩ := ih q.natDegree (by omega) q qo rfl
      have hz : p.aeval r = 0 := by rw [hq,map_mul,hr,mul_zero]
      exact (hpos E r).ne' hz
    let P := RingPreordering.mk' {z : AdjoinRoot g | IsSumSq z}
      (fun h k => IsSumSq.add h k) (fun h k => IsSumSq.mul h k) IsSumSq.mul_self proper
    obtain ⟨lo,strict,hP⟩ := order P
    letI : Module.Finite F (AdjoinRoot g) := Module.Finite.of_basis (AdjoinRoot.powerBasis gi.ne_zero).basis
    refine ⟨AdjoinRoot g,inferInstance,lo,strict,inferInstance,inferInstance,?_,AdjoinRoot.root g,?_⟩
    · intro x hx
      obtain ⟨r,hr⟩ := sq x hx
      rw [hr,map_mul]
      exact mul_self_nonneg _
    · rw [AdjoinRoot.aeval_eq]
      exact AdjoinRoot.mk_eq_zero.mpr gd


end LocalReal17

theorem OMA.solution : OMA.R_Hilbert17_hilbert_17th_problem_R1_H2_R1.H2 :=
  LocalReal17.odd_extension LocalReal17.order_preordering

