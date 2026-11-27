import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1
import Mathlib

/-! Quantitative circle bounds and the algebraicity of large-circle configurations. -/

section
/- An elementary one-atom inequality for multiplication by a finite set. -/
open scoped Pointwise
namespace Erdos1082Atom
variable {G : Type*} [CommGroup G] [DecidableEq G]
private lemma translate_mem (a x : G) (X : Finset G) (hx : x∈X) : a*x∈({a} : Finset G)*X :=
  Finset.mem_mul.mpr ⟨a,by simp,x,hx,rfl⟩

lemma atom (S : Finset G) (hS : S.Nonempty) :
    ∃ (H : Subgroup G) (T : Finset G), (H:Set G)=T ∧
       (T*S).card + S.card ≤ T.card+(S/S).card := by
  classical
  let f := fun X : Finset G => (X*S).card-X.card
  have fadd (X : Finset G) : f X+X.card=(X*S).card := Nat.sub_add_cancel (Finset.card_le_card_mul_right hS)
  let P := fun n : ℕ => ∃ X : Finset G, X.Nonempty ∧ f X=n
  have hP : ∃ n, P n := ⟨f S,S,hS,rfl⟩
  let m := Nat.find hP
  have hleast (X : Finset G) (hX : X.Nonempty) : m≤f X := Nat.find_min' hP ⟨X,hX,rfl⟩
  let Q := fun n : ℕ => ∃ X : Finset G, X.Nonempty ∧ f X=m ∧ X.card=n
  have hQ : ∃ n,Q n := by obtain ⟨X,hX,he⟩ := Nat.find_spec hP; exact ⟨_,X,hX,he,rfl⟩
  obtain ⟨U,hU,hu,hu'⟩ := Nat.find_spec hQ
  have hmin (X : Finset G) (hX : X.Nonempty) (hf : f X=m) : U.card≤X.card :=
    hu' ▸ Nat.find_min' hQ ⟨X,hX,hf,rfl⟩
  have ftr (a : G) (X : Finset G) : f (({a} : Finset G)*X)=f X := by
    dsimp [f]; rw [mul_assoc,Finset.card_singleton_mul,Finset.card_singleton_mul]
  obtain ⟨a,ha⟩ := hU
  let T := ({a⁻¹} : Finset G)*U
  have h1 : 1∈T := by simpa [T] using translate_mem a⁻¹ a U ha
  have hT : T.Nonempty := ⟨1,h1⟩
  have hTc : T.card=U.card := Finset.card_singleton_mul _ _
  have hTf : f T=m := (ftr a⁻¹ U).trans hu
  have tr (x : G) (hx : x∈T) : ({x} : Finset G)*T=T := by
    let Y := ({x} : Finset G)*T
    have hxy : x∈Y := by simpa [Y] using translate_mem x 1 T h1
    have hi : (T∩Y).Nonempty := ⟨x,Finset.mem_inter.mpr ⟨hx,hxy⟩⟩
    have hun : (T∪Y).Nonempty := hT.mono Finset.subset_union_left
    have hc : ((T∩Y)*S).card≤((T*S)∩(Y*S)).card := Finset.card_le_card Finset.inter_mul_subset
    have cf := Finset.card_union_add_card_inter (T*S) (Y*S)
    have cU := Finset.card_union_add_card_inter T Y
    rw [← Finset.union_mul] at cf
    have cfT := fadd T
    have cfY := fadd Y
    have cfI := fadd (T∩Y)
    have cfU := fadd (T∪Y)
    have hcmp := hleast (T∪Y) hun
    have hcmp' := hleast (T∩Y) hi
    have hYf : f Y=m := (ftr x T).trans hTf
    have hIf : f (T∩Y)=m := by omega
    have cc := hmin (T∩Y) hi hIf
    have eqI : T∩Y=T := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have sub : T⊆Y := by
      intro v hv
      have hv' : v∈T∩Y := by rwa [eqI]
      exact (Finset.mem_inter.mp hv').2
    exact (Finset.eq_of_subset_of_card_le sub (Finset.card_singleton_mul x T).le).symm
  let H : Subgroup G := {
    carrier := T
    one_mem' := h1
    mul_mem' := by
      intro x y hx hy; change x*y∈T; rw [← tr x hx]; exact translate_mem x y T hy
    inv_mem' := by
      intro x hx
      have e : 1∈({x} : Finset G)*T := (tr x hx).symm ▸ h1
      obtain ⟨v,hv,w,hw,he⟩ := Finset.mem_mul.mp e
      have hv' : v=x := Finset.mem_singleton.mp hv
      rw [hv'] at he
      have he' : x⁻¹=w := by calc x⁻¹=x⁻¹*1 := by simp
                                _=x⁻¹*(x*w) := by rw [he]
                                _=w := by simp
      exact he' ▸ hw }
  refine ⟨H,T,rfl,?_⟩
  have hcmp := hleast S⁻¹ (by obtain ⟨v,hv⟩:=hS; exact ⟨v⁻¹,by simpa using hv⟩)
  have hv := fadd S⁻¹
  have hTadd := fadd T
  rw [Finset.card_inv, mul_comm, ← div_eq_mul_inv] at hv
  omega
end Erdos1082Atom
end

section
/- Quotient fibers in a small quotient set and their difference fibers. -/
open scoped Pointwise
open Classical
noncomputable section
namespace Erdos1082Atom
variable {G : Type*} [CommGroup G] [DecidableEq G]

lemma fiber_lower (S T : Finset G) (H : Subgroup G) (hHT : (H:Set G)=T)
    (hnum : (T*S).card+S.card≤T.card+(S/S).card) (a : G) (ha : a∈S) :
    2*S.card≤(S/S).card+(S.filter fun z => (QuotientGroup.mk' H) z=(QuotientGroup.mk' H) a).card := by
  classical
  let φ := QuotientGroup.mk' H
  let C := ({a}:Finset G)*T
  have memH {x:G} : x∈H ↔ x∈T := by change x∈(H:Set G) ↔ _; rw [hHT]; rfl
  have subS : S⊆T*S := by
    intro s hs
    exact Finset.mem_mul.mpr ⟨1,memH.mp H.one_mem,s,hs,one_mul s⟩
  have subC : C⊆T*S := by
    intro z hz
    obtain ⟨w,hw,t,ht,rfl⟩ := Finset.mem_mul.mp hz
    have ew := Finset.mem_singleton.mp hw
    exact Finset.mem_mul.mpr ⟨t,ht,a,ha,by rw [ew,mul_comm]⟩
  have subdiff : C\S ⊆ (T*S)\S := by
    intro w hw
    exact Finset.mem_sdiff.mpr ⟨subC (Finset.mem_sdiff.mp hw).1,(Finset.mem_sdiff.mp hw).2⟩
  have subF : C∩S⊆S.filter (fun z => φ z=φ a) := by
    intro z hz
    obtain ⟨hC,hS⟩ := Finset.mem_inter.mp hz
    obtain ⟨w,hw,t,ht,rfl⟩ := Finset.mem_mul.mp hC
    have ew := Finset.mem_singleton.mp hw
    have hom : φ t=1 := (QuotientGroup.eq_one_iff t).mpr (memH.mpr ht)
    exact Finset.mem_filter.mpr ⟨hS,by rw [map_mul,ew,hom,mul_one]⟩
  have cD := Finset.card_le_card subdiff
  have cF := Finset.card_le_card subF
  have eqD := Finset.card_sdiff_add_card_eq_card subS
  have eqC := Finset.card_sdiff_add_card_inter C S
  have cardC : C.card=T.card := Finset.card_singleton_mul _ _
  change 2*S.card≤(S/S).card+(S.filter fun z => φ z=φ a).card
  omega

lemma div_fiber_lower (S T : Finset G) (H : Subgroup G) (hHT : (H:Set G)=T)
    (hnum : (T*S).card+S.card≤T.card+(S/S).card) (v : G) (hv : v∈S/S) :
    2*S.card≤(S/S).card+((S/S).filter fun z => (QuotientGroup.mk' H) z=(QuotientGroup.mk' H) v).card := by
  classical
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_div.mp hv
  let φ := QuotientGroup.mk' H
  let F := S.filter fun z => φ z=φ a
  let D := (S/S).filter fun z => φ z=φ (a/b)
  have sub : F.image (·/b)⊆D := by
    intro q hq; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hx,he⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_div.mpr ⟨x,hx,b,hb,rfl⟩,?_⟩
    change φ (x/b)=φ (a/b)
    rw [map_div,map_div,he]
  have cF := Finset.card_image_of_injective F (div_left_injective (b:=b))
  have ce := Finset.card_le_card sub
  have lb := fiber_lower S T H hHT hnum a ha
  change 2*S.card≤(S/S).card+F.card at lb
  change 2*S.card≤(S/S).card+D.card
  omega

lemma cover_weights (S : Finset G) (hS : S.Nonempty) :
    ∃ (H : Subgroup G) (T : Finset G), (H:Set G)=T ∧
      (S.image (QuotientGroup.mk' H)).card*(2*S.card-(S/S).card)≤S.card ∧
      ((S/S).image (QuotientGroup.mk' H)).card*(2*S.card-(S/S).card)≤(S/S).card := by
  classical
  obtain ⟨H,T,hHT,hnum⟩ := atom S hS
  refine ⟨H,T,hHT,?_⟩
  let φ := QuotientGroup.mk' H
  let δ := 2*S.card-(S/S).card
  have count (U : Finset G) (h : ∀a∈U, 2*S.card≤(S/S).card+(U.filter fun z => φ z=φ a).card) :
      (U.image φ).card*δ≤U.card := by
    calc
      _ = ∑ _ ∈ U.image φ, δ := by simp
      _ ≤ ∑ v ∈ U.image φ, (U.filter fun z => φ z=v).card := by
        apply Finset.sum_le_sum
        intro v hv
        obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
        have hh := h a ha
        dsimp [δ]; omega
      _ = U.card := (Finset.card_eq_sum_card_image φ U).symm
  exact ⟨count S (fiber_lower S T H hHT hnum),count (S/S) (div_fiber_lower S T H hHT hnum)⟩
end Erdos1082Atom
end
end

section
open Polynomial OMA.R_Erdos1082_erdos_1082_parts_i_R1

namespace Erdos1082GeneralCurve

lemma normalized_trace_poly {L : Type*} [Field L] (u v k h : L) :
    ∀ m : ℕ, ∃ P : Polynomial L, P.natDegree≤2*m ∧ P.coeff 0=(if m=0 then 2 else u^m) ∧
      P.coeff 1=(m:L)*u^(m-1)*k ∧ ∀ z w : L, z≠0 → w≠0 → w+h/w=u/z+v*z+k →
        P.eval z=z^m*(w^m+(h/w)^m)
  | 0 => by refine ⟨C 2,by simp,by simp,by simp,?_⟩; intro z w hz hw he; simp; ring
  | 1 => by
    let F : Polynomial L := C u+C k*X+C v*X^2
    refine ⟨F,by dsimp [F]; compute_degree,by simp [F,mul_coeff_zero],
      by simp [F,mul_coeff_one,coeff_X_pow],?_⟩
    intro z w hz hw he
    simp only [F,eval_add,eval_mul,eval_C,eval_X,eval_pow,pow_one]
    rw [he]; field_simp [hz]; ring
  | n+2 => by
    obtain ⟨P,hP,P₀,P₁,hPv⟩ := normalized_trace_poly u v k h n
    obtain ⟨Q,hQ,Q₀,Q₁,hQv⟩ := normalized_trace_poly u v k h (n+1)
    let F : Polynomial L := C u+C k*X+C v*X^2
    have hF : F.natDegree≤2 := by dsimp [F]; compute_degree
    have F₀ : F.coeff 0=u := by simp [F,mul_coeff_zero]
    have F₁ : F.coeff 1=k := by simp [F,mul_coeff_one,coeff_X_pow]
    let R := F*Q-C h*X^2*P
    refine ⟨R,?_,?_,?_,?_⟩
    · have h₁ := (natDegree_mul_le (p:=F) (q:=Q)).trans (Nat.add_le_add hF hQ)
      have hc : (C h*(X:Polynomial L)^2).natDegree≤2 := by compute_degree
      have h₂ := (natDegree_mul_le (p:=C h*X^2) (q:=P)).trans (Nat.add_le_add hc hP)
      exact (natDegree_sub_le ..).trans (max_le (by omega) (by omega))
    · simp only [R,coeff_sub,mul_coeff_zero,F₀,Q₀,Nat.add_eq_zero_iff,Nat.succ_ne_self, and_false,if_false]
      simp [coeff_X_pow,pow_succ]; ring
    · simp only [R,coeff_sub,mul_coeff_one,mul_coeff_zero,F₀,F₁,Q₀,Q₁]
      simp [coeff_X_pow,pow_succ]; ring
    · intro z w hz hw he
      simp only [R,eval_sub,eval_mul,eval_C,eval_pow,eval_X,hPv _ _ hz hw he,hQv _ _ hz hw he]
      have hFe : F.eval z=(w+h/w)*z := by
        simp only [F,eval_add,eval_mul,eval_C,eval_X,eval_pow]
        rw [he]; field_simp [hz]; ring
      rw [hFe]
      have hprod : w*(h/w)=h := by field_simp
      calc
        _ = z^(n+2)*((w+h/w)*(w^(n+1)+(h/w)^(n+1))-(w*(h/w))*(w^n+(h/w)^n)) := by rw [hprod]; ring
        _ = _ := by ring


set_option maxHeartbeats 1100000 in
lemma power_trace_bound {L : Type*} [Field L] [CharZero L] (S : Finset L)
    (m : ℕ) (hm : 2 ≤ m) (u v k h U V K H : L) (hu : u≠0) (hk : k≠0) (hh : h≠0) (hH : H≠0)
    (hs : ∀ z∈S, z≠0 ∧ ∃ w : L, w≠0 ∧ w+h/w=u/z+v*z+k ∧
      w^m+H/w^m=U/z^m+V*z^m+K) : S.card≤4*m := by
  classical
  obtain ⟨P,hP,P₀,P₁,heval⟩ := normalized_trace_poly u v k h m
  have hm0 : m≠0 := by omega
  have hm1 : m≠1 := by omega
  have h2m0 : 2*m≠0 := by omega
  have h2m1 : 2*m≠1 := by omega
  rw [if_neg hm0] at P₀
  let α := u^m
  let β := (m:L)*u^(m-1)*k
  have hα : α≠0 := pow_ne_zero _ hu
  have hβ : β≠0 := mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr hm0) (pow_ne_zero _ hu)) hk
  let a := U-α
  let δ := H-h^m
  let B : Polynomial L := C U+C K*X^m+C V*X^(2*m)-P
  have B₀ : B.coeff 0=a := by simp [B,a,α,P₀,coeff_C_mul,coeff_X_pow,hm0,h2m0,Ne.symm hm0,Ne.symm h2m0]
  have B₁ : B.coeff 1= -β := by simp [B,β,P₁,coeff_C_mul,coeff_X_pow,hm1,h2m1,Ne.symm hm1,Ne.symm h2m1]
  have hB : B.natDegree≤2*m := by
    dsimp only [B]
    compute_degree <;> omega
  have hB₀ : B≠0 := by intro he; rw [he,coeff_zero] at B₁; exact hβ (neg_eq_zero.mp B₁.symm)
  let R : Polynomial L := C δ*B*P-C (δ^2)*X^(2*m)-C (h^m)*B^2
  have hR : R.natDegree≤4*m := by
    dsimp only [R]
    compute_degree <;> omega
  have hR₀ : R.coeff 0=δ*a*α-h^m*a^2 := by
    simp only [R,coeff_sub,mul_coeff_zero,coeff_C_zero,coeff_X_pow,B₀,P₀,pow_two]
    simp [α,mul_coeff_zero,B₀,h2m0,hm0,Ne.symm h2m0]
  have hR₁ : R.coeff 1=δ*(a*β-β*α)+2*h^m*a*β := by
    simp only [R,pow_two,coeff_sub,mul_coeff_one,mul_coeff_zero,coeff_C,coeff_X_pow,B₀,B₁,P₀,P₁,Ne.symm h2m1,Ne.symm h2m0,if_false,if_true,one_ne_zero,zero_ne_one]
    dsimp only [α,β]; ring
  have hne : R≠0 := by
    intro hzero
    by_cases hd : δ=0
    · have hp : C (h^m)*B^2≠0 := mul_ne_zero (C_ne_zero.mpr (pow_ne_zero _ hh)) (pow_ne_zero _ hB₀)
      simp [R,hd,hh,hB₀] at hzero
    rw [hzero,coeff_zero] at hR₀ hR₁
    by_cases ha : a=0
    · rw [ha] at hR₁
      have hz : δ*β*α=0 := by linear_combination hR₁
      exact (mul_ne_zero (mul_ne_zero hd hβ) hα) hz
    have ht : δ*α=h^m*a := by
      apply (mul_left_inj' ha).mp
      linear_combination -hR₀
    have he : a*β*H=0 := by
      dsimp only [δ] at hR₁ ht
      linear_combination -hR₁+β*ht
    exact (mul_ne_zero (mul_ne_zero ha hβ) hH) he
  have hsub : S⊆R.roots.toFinset := by
    intro z hz
    obtain ⟨hz,w,hw,hl,hm'⟩ := hs z hz
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots hne).mpr
    have hz' := pow_ne_zero m hz
    have hw' := pow_ne_zero m hw
    have hPe := heval z w hz hw hl
    have hBe : B.eval z=z^m*(δ/w^m) := by
      simp only [B,eval_sub,eval_add,eval_mul,eval_C,eval_pow,eval_X,hPe]
      have he : U+K*z^m+V*z^(2*m)=z^m*(w^m+H/w^m) := by rw [hm',show 2*m=m+m by omega,pow_add]; field_simp [hz']; ring
      rw [he,div_pow]
      dsimp only [δ]; field_simp [hw']; ring
    change R.eval z=0
    simp only [R,eval_sub,eval_mul,eval_C,eval_X,eval_pow,hBe,hPe,div_pow]
    rw [show 2*m=m+m by omega,pow_add]
    dsimp only [δ]; field_simp [hw']; ring
  exact (Finset.card_le_card hsub).trans <| (Multiset.toFinset_card_le _).trans <| (card_roots' R).trans hR


lemma coprime_laurent_points (T : Finset Circle) (H : Subgroup Circle) (hT : (H:Set Circle)=T)
    (m : ℕ) (hm2 : 2 ≤ m) (hcop : m.Coprime T.card) (a b k c d : ℂ) (ha : a≠0) (hk : k≠0) (hc : c≠0) (hd : d≠0)
    (S : Finset Circle) (hST : S⊆T)
    (hm : ∀ z∈S, ∃ w∈T, c*(w:ℂ)+d/(w:ℂ)=a/(z:ℂ)+b*(z:ℂ)+k) : S.card≤4*m := by
  classical
  by_cases he : T.card=0
  · have := Finset.card_le_card hST; omega
  let : NeZero T.card := ⟨he⟩
  obtain ⟨K,hroots,σ,hσ⟩ := automorphism_on_roots T.card m hcop
  have hmem (z : Circle) (hz : z∈T) : (z:ℂ)∈K := hroots _ (finite_subgroup_root _ _ hT z hz)
  let M : Finset ℂ := {a,k,c,d}
  have hn (v : M) : v.1≠0 := by
    have ht := v.2
    simp only [M,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with he|he|he|he <;> rw [he] <;> assumption
  obtain ⟨F,hF⟩ := Module.exists_dual_forall_apply_ne_zero (K:=K) (fun v : M => v.1) hn
  have hfa : F a≠0 := hF ⟨a,by simp [M]⟩
  have hfk : F k≠0 := hF ⟨k,by simp [M]⟩
  have hfc : F c≠0 := hF ⟨c,by simp [M]⟩
  have hfd : F d≠0 := hF ⟨d,by simp [M]⟩
  let u := F a/F c
  let v := F b/F c
  let κ := F k/F c
  let h := F d/F c
  have hu : u≠0 := div_ne_zero hfa hfc
  have hk' : κ≠0 := div_ne_zero hfk hfc
  have hh : h≠0 := div_ne_zero hfd hfc
  let lift (z : S) : K := ⟨(z.1:ℂ),hmem _ (hST z.2)⟩
  let P := S.attach.image lift
  have hlift : Function.Injective lift := fun _ _ he => Subtype.ext (Circle.coe_injective (congrArg ((↑):K→ℂ) he))
  have hsize : P.card=S.card := by dsimp only [P]; rw [Finset.card_image_of_injective _ hlift,Finset.card_attach]
  rw [←hsize]
  apply power_trace_bound P m hm2 u v κ h (σ u) (σ v) (σ κ) (σ h) hu hk' hh ((_root_.map_ne_zero _).mpr hh)
  intro z hz
  obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨w,hw,he⟩ := hm z.1 z.2
  let W : K := ⟨(w:ℂ),hmem _ hw⟩
  have hrz : (lift z)^T.card=1 := Subtype.ext (finite_subgroup_root _ _ hT z.1 (hST z.2))
  have hrw : W^T.card=1 := Subtype.ext (finite_subgroup_root _ _ hT w hw)
  have hz0 : lift z≠0 := fun hh => Circle.coe_ne_zero z.1 (congrArg ((↑):K→ℂ) hh)
  have hw0 : W≠0 := fun hh => Circle.coe_ne_zero w (congrArg ((↑):K→ℂ) hh)
  have he' : W • c + W⁻¹ • d = (lift z)⁻¹ • a + lift z • b+k := by
    change (w:ℂ)*c+(w:ℂ)⁻¹*d=(z.1:ℂ)⁻¹*a+(z.1:ℂ)*b+k
    simpa only [div_eq_mul_inv,mul_comm] using he
  have lin := congrArg F he'
  simp only [map_add,LinearMap.map_smul,smul_eq_mul] at lin
  have eqn : W+h/W = u/lift z+v*lift z+κ := by
    dsimp only [h,u,v,κ]
    field_simp [hfc,hw0,hz0] at lin ⊢
    linear_combination lin
  refine ⟨hz0,W,hw0,eqn,?_⟩
  simpa only [map_add,map_mul,map_div₀,hσ (lift z) hrz,hσ W hrw] using congrArg σ eqn

lemma orbit_norm (c p : ℂ) (z : Circle) :
    ((‖c+p*(z:ℂ)‖^2:ℝ):ℂ) = (Complex.normSq c:ℂ)+(Complex.normSq p:ℂ)+
        (starRingEnd ℂ c*p)*(z:ℂ)+(c*starRingEnd ℂ p)/(z:ℂ) := by
  rw [Complex.sq_norm,Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_conj_mul_self,
    map_add,map_mul,←Circle.coe_inv_eq_conj,Circle.coe_inv]
  field_simp [Circle.coe_ne_zero z]
  ring


lemma orbit_fiber_card (T : Finset Circle) (c p : ℂ) (hc : c≠0) (hp : p≠0) (r : ℝ) :
    (T.filter fun z : Circle => ‖c+p*(z:ℂ)‖=r).card ≤ 2 := by
  classical
  let q := -c/p
  apply (Finset.card_le_card (t := T.filter fun z : Circle => dist q (z:ℂ)=r/‖p‖) ?_).trans
    (circle_fibers T q (div_ne_zero (neg_ne_zero.mpr hc) hp) _)
  intro z hz
  obtain ⟨hz,he⟩ := Finset.mem_filter.mp hz
  refine Finset.mem_filter.mpr ⟨hz,?_⟩
  have heq : q-(z:ℂ) = -(c+p*(z:ℂ))/p := by dsimp [q]; field_simp; ring
  rw [dist_eq_norm,heq,norm_div,norm_neg,he]

lemma orbit_image_size (S : Finset Circle) (c p : ℂ) (hc : c≠0) (hp : p≠0) :
    S.card ≤ 2*(S.image fun z : Circle => ‖c+p*(z:ℂ)‖).card := by
  classical
  by_contra! h
  obtain ⟨r,_,hr⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (fun z (hz : z∈S) => Finset.mem_image_of_mem (fun z : Circle => ‖c+p*(z:ℂ)‖) hz)
    (show (S.image fun z : Circle => ‖c+p*(z:ℂ)‖).card*2<S.card by omega)
  exact (not_lt_of_ge (orbit_fiber_card S c p hc hp r)) hr



lemma unconditional_orbit_intersection (T : Finset Circle) (H : Subgroup Circle) (hT : (H:Set Circle)=T)
    (m : ℕ) (hm : 2 ≤ m) (hcop : m.Coprime T.card) (c p q : ℂ) (hc : c≠0) (hp : p≠0) (hq : q≠0) (hn : ‖p‖≠‖q‖) :
    (T.filter fun z : Circle => ‖c+p*(z:ℂ)‖∈T.image (fun w : Circle => ‖c+q*(w:ℂ)‖)).card≤4*m := by
  classical
  have hnorm : (Complex.normSq p:ℂ)≠(Complex.normSq q:ℂ) := by
    intro he
    have hh := Complex.ofReal_injective he
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at hh
    exact hn (by nlinarith [norm_nonneg p,norm_nonneg q])
  apply coprime_laurent_points T H hT m hm hcop (c*starRingEnd ℂ p) (starRingEnd ℂ c*p)
    ((Complex.normSq p:ℂ)-(Complex.normSq q:ℂ)) (starRingEnd ℂ c*q) (c*starRingEnd ℂ q)
    (mul_ne_zero hc ((_root_.map_ne_zero _).mpr hp)) (sub_ne_zero.mpr hnorm)
    (mul_ne_zero ((_root_.map_ne_zero _).mpr hc) hq) (mul_ne_zero hc ((_root_.map_ne_zero _).mpr hq))
    _ (Finset.filter_subset _ _)
  intro z hz
  obtain ⟨w,hw,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hz).2
  refine ⟨w,hw,?_⟩
  have hh := congrArg (fun t : ℝ => ((t^2:ℝ):ℂ)) he
  rw [orbit_norm,orbit_norm] at hh
  linear_combination hh


lemma count_few_overlaps {ι α β : Type*} (I : Finset ι) (S : Finset α) (f : ι→α→β) (m : ℕ)
    [DecidableEq ι] [DecidableEq β]
    (hf : ∀ i∈I, ∀ W⊆S, W.card≤2*(W.image (f i)).card)
    (hc : ∀ i∈I, ∀ j∈I, i≠j → (S.filter fun x => f i x∈S.image (f j)).card≤4*m) :
    I.card*S.card+(2*m)*I.card≤2*(I.biUnion fun i => S.image (f i)).card+(2*m)*I.card*I.card := by
  classical
  let D (J : Finset ι) := J.biUnion fun i => S.image (f i)
  suffices hall : ∀ J⊆I, J.card*S.card+(2*m)*J.card≤2*(D J).card+(2*m)*J.card*J.card from hall I (Finset.Subset.refl _)
  intro J
  induction J using Finset.induction_on with
  | empty => simp [D]
  | @insert i J hi ih =>
    intro hJI
    have hiI := hJI (Finset.mem_insert_self _ _)
    have hJI' : J⊆I := (Finset.subset_insert _ _).trans hJI
    have ih' := ih hJI'
    let W := S.filter fun x => f i x∉D J
    let Q (j : ι) := S.filter fun x => f i x∈S.image (f j)
    have hsub : (S.filter fun x => f i x∈D J)⊆J.biUnion Q := by
      intro x hx
      obtain ⟨hx,hx'⟩ := Finset.mem_filter.mp hx
      obtain ⟨j,hj,hj'⟩ := Finset.mem_biUnion.mp hx'
      exact Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_filter.mpr ⟨hx,hj'⟩⟩
    have hbound : (J.biUnion Q).card≤J.card*(4*m) := by
      calc
        _ ≤ ∑ j∈J,(Q j).card := Finset.card_biUnion_le
        _ ≤ ∑ _∈J,(4*m) := Finset.sum_le_sum (fun j hj => hc i hiI j (hJI' hj) (fun h => hi (h ▸ hj)))
        _ = _ := by simp
    have hmatched := (Finset.card_le_card hsub).trans hbound
    have hrem := Finset.card_filter_add_card_filter_not (s:=S) (fun x => f i x∈D J)
    change (S.filter fun x => f i x∈D J).card+W.card=S.card at hrem
    have hf' := hf i hiI W (Finset.filter_subset _ _)
    have hd : Disjoint (W.image (f i)) (D J) := Finset.disjoint_left.mpr (by
      intro y hy hd
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hx).2 hd)
    have hsub' : W.image (f i) ∪ D J ⊆ D (insert i J) := by
      change _ ⊆ (insert i J).biUnion _
      rw [Finset.biUnion_insert]
      exact Finset.union_subset_union_left (Finset.image_subset_image (Finset.filter_subset _ _))
    have hc' := Finset.card_le_card hsub'
    rw [Finset.card_union_of_disjoint hd] at hc'
    rw [Finset.card_insert_of_notMem hi]
    nlinarith


lemma regular_radial_bound (T : Finset Circle) (H : Subgroup Circle) (hT : (H:Set Circle)=T)
    (m : ℕ) (hm2 : 2 ≤ m) (hcop : m.Coprime T.card) (A P : Finset ℂ) (hPA : P⊆A) (hTA : ∀ z∈T, (z:ℂ)∈A)
    (hp : ∀ p∈P, p≠0 ∧ ‖p‖≠1) (hr : Set.InjOn (fun p : ℂ => ‖p‖) (P:Set ℂ)) :
    P.card*T.card+(2*m)*P.card≤2*distinctDistances A+(2*m)*P.card*P.card := by
  classical
  let f (p : ℂ) (z : Circle) := ‖(-1:ℂ)+p*(z:ℂ)‖
  have hsum := count_few_overlaps P T f m
    (fun p he W _ => orbit_image_size W (-1) p (by norm_num) (hp p he).1)
    (fun p hp' q hq hne => unconditional_orbit_intersection T H hT m hm2 hcop (-1) p q (by norm_num)
      (hp p hp').1 (hp q hq).1 (fun h => hne (hr hp' hq h)))
  have hs : (P.biUnion fun p => T.image (f p)) ⊆ distanceSet A := by
    intro r hr
    obtain ⟨p,hp',hr⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hr
    have hm (z : Circle) : z∈H ↔ z∈T := by change z∈(H:Set Circle) ↔ _; rw [hT]; rfl
    have hzA := hTA z⁻¹ ((hm _).mp (H.inv_mem ((hm _).mpr hz)))
    have hne : p≠(z⁻¹:Circle) := fun he => (hp p hp').2 (by rw [he,Circle.norm_coe])
    refine Finset.mem_image.mpr ⟨(p,((z⁻¹:Circle):ℂ)),Finset.mem_offDiag.mpr ⟨hPA hp',hzA,hne⟩,?_⟩
    change dist p ((z⁻¹:Circle):ℂ)=f p z
    rw [dist_eq_norm,Circle.coe_inv]
    have he : (-1:ℂ)+p*(z:ℂ)=(p-(z:ℂ)⁻¹)*(z:ℂ) := by field_simp [Circle.coe_ne_zero z]; ring
    dsimp only [f]
    rw [he,norm_mul,Circle.norm_coe,mul_one]
  have hb := Finset.card_le_card hs
  change P.card*T.card+(2*m)*P.card≤2*(distanceSet A).card+(2*m)*P.card*P.card
  omega



end Erdos1082GeneralCurve

namespace Erdos1082Uniform

lemma zero_poly_of_points {L : Type*} [Field L] (S : Finset L) (n : ℕ) (P : Polynomial L)
    (hsize : n<S.card) (hdeg : P.natDegree≤n) (hz : ∀ z∈S,P.eval z=0) : P=0 := by
  classical
  by_contra hn
  have hsub : S⊆P.roots.toFinset := fun z he => Multiset.mem_toFinset.mpr ((mem_roots hn).mpr (hz z he))
  have hh := (Finset.card_le_card hsub).trans <| (Multiset.toFinset_card_le _).trans <| (card_roots' P).trans hdeg
  omega

lemma linear_trace_rigidity {L : Type*} [Field L] [CharZero L] (S : Finset L) (hsz : 4<S.card)
    (u v k h U V K H : L) (hu : u≠0) (hv : v≠0) (hk : k≠0)
    (hs : ∀ z∈S, z≠0 ∧ ∃ w : L, w≠0 ∧ w+h/w=u/z+v*z+k ∧ w+H/w=U/z+V*z+K) :
    H=h ∧ U=u ∧ V=v ∧ K=k := by
  classical
  let a := U-u
  let b := V-v
  let c := K-k
  let δ := H-h
  have eqs (z : L) (hz : z∈S) : z≠0 ∧ ∃ w : L, w≠0 ∧ w+h/w=u/z+v*z+k ∧ a/z+b*z+c=δ/w := by
    obtain ⟨hz,w,hw,h₁,h₂⟩ := hs z hz
    refine ⟨hz,w,hw,h₁,?_⟩
    dsimp only [a,b,c,δ]; linear_combination h₁ - h₂
  by_cases hd : δ=0
  · let P : Polynomial L := C a+C c*X+C b*X^2
    have hp := zero_poly_of_points S 2 P (by omega) (by dsimp [P]; compute_degree) (by
      intro z hz
      obtain ⟨hz,w,hw,_,he⟩ := eqs z hz
      rw [hd,zero_div] at he
      simp only [P,eval_add,eval_C,eval_mul,eval_X,eval_pow]
      field_simp [hz] at he
      linear_combination he)
    have h₀ := congrArg (fun Q : Polynomial L => Q.coeff 0) hp
    have h₁ := congrArg (fun Q : Polynomial L => Q.coeff 1) hp
    have h₂ := congrArg (fun Q : Polynomial L => Q.coeff 2) hp
    simp only [P,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C,coeff_zero] at h₀ h₁ h₂
    norm_num at h₀ h₁ h₂
    exact ⟨sub_eq_zero.mp hd,sub_eq_zero.mp h₀,sub_eq_zero.mp h₂,sub_eq_zero.mp h₁⟩
  let A := δ*u-h*a
  let B := δ*v-h*b
  let Cc := δ*k-h*c
  let Q : Polynomial L := C (a*A)+C (a*Cc+c*A)*X+C (a*B+b*A+c*Cc-δ^2)*X^2+
    C (b*Cc+c*B)*X^3+C (b*B)*X^4
  have hQ := zero_poly_of_points S 4 Q hsz (by dsimp [Q]; compute_degree) (by
    intro z hz
    obtain ⟨hz,w,hw,he,hdw⟩ := eqs z hz
    have other : A/z+B*z+Cc=δ*w := by
      calc
        _=δ*(u/z+v*z+k)-h*(a/z+b*z+c) := by dsimp only [A,B,Cc] <;> ring
        _=_ := by rw [←he,hdw] <;> ring
    have prod : (a/z+b*z+c)*(A/z+B*z+Cc)=δ^2 := by rw [hdw,other]; field_simp [hw] <;> ring
    simp only [Q,eval_add,eval_mul,eval_C,eval_X,eval_pow]
    field_simp [hz] at prod
    linear_combination prod)
  have e₀ := congrArg (fun Q : Polynomial L => Q.coeff 0) hQ
  have e₁ := congrArg (fun Q : Polynomial L => Q.coeff 1) hQ
  have e₂ := congrArg (fun Q : Polynomial L => Q.coeff 2) hQ
  have e₃ := congrArg (fun Q : Polynomial L => Q.coeff 3) hQ
  have e₄ := congrArg (fun Q : Polynomial L => Q.coeff 4) hQ
  simp only [Q,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C,coeff_zero] at e₀ e₁ e₂ e₃ e₄
  norm_num at e₀ e₁ e₂ e₃ e₄
  have neq (x y z : L) (hx : x≠0) (he : z=δ*x-h*y) : z+h*y≠0 := by rw [he]; simpa using mul_ne_zero hd hx
  have ha := neq u a A hu rfl
  have hb := neq v b B hv rfl
  have hcc := neq k c Cc hk rfl
  have splitrow (a A c Cc : L) (zero : a*A=0) (lin : a*Cc+c*A=0) (hn : A+h*a≠0) :
      (a=0 ∧ c=0) ∨ (A=0 ∧ Cc=0) := by
    rcases mul_eq_zero.mp zero with ha|hA
    · left
      have hA' : A≠0 := by simpa [ha] using hn
      have hc : c*A=0 := by simpa [ha] using lin
      exact ⟨ha,(mul_eq_zero.mp hc).resolve_right hA'⟩
    · right
      have ha' : a≠0 := fun he => hn (by simp [hA,he])
      have hc : a*Cc=0 := by simpa [hA] using lin
      exact ⟨hA,(mul_eq_zero.mp hc).resolve_left ha'⟩
  exfalso
  rcases splitrow a A c Cc (mul_eq_zero.mpr e₀) e₁ ha with ⟨h₁,h₂⟩|⟨h₁,h₂⟩ <;>
    rcases splitrow b B c Cc (mul_eq_zero.mpr e₄) e₃ hb with ⟨h₃,h₄⟩|⟨h₃,h₄⟩ <;>
    simp_all [h₁,h₂,h₃,h₄]


lemma projected_nonzero_relation {ι : Type*} [Fintype ι] (K : IntermediateField ℚ ℂ) (z w : ι→K)
    (a b k c d : ℂ) (ha : a≠0) (hb : b≠0) (hk : k≠0) (hc : c≠0) (hd : d≠0)
    (hnzw : ∀ i, z i≠0 ∧ w i≠0)
    (he : ∀ i, c*(w i:ℂ)+d/(w i:ℂ)=a/(z i:ℂ)+b*(z i:ℂ)+k)
    (hgood : ∀ i, a/(z i:ℂ)+b*(z i:ℂ)≠0 ∧ a/(z i:ℂ)+b*(z i:ℂ)+k≠0) :
    ∃ u v κ h : K, u≠0 ∧ v≠0 ∧ κ≠0 ∧ h≠0 ∧ ∀ i,
      w i+h/w i=u/z i+v*z i+κ ∧ u/z i+v*z i≠0 ∧ u/z i+v*z i+κ≠0 := by
  classical
  let X (i : ι) := a/(z i:ℂ)+b*(z i:ℂ)
  let M : Finset ℂ := ({a,b,k,c,d} ∪ Finset.univ.image X ∪ Finset.univ.image (fun i => X i+k)).erase 0
  obtain ⟨F,hF⟩ := Module.exists_dual_forall_apply_ne_zero (K:=K) (fun x : M => x.1)
    (fun x => (Finset.mem_erase.mp x.2).1)
  have hfa : F a≠0 := hF ⟨a,by simp [M,ha]⟩
  have hfb : F b≠0 := hF ⟨b,by simp [M,hb]⟩
  have hfk : F k≠0 := hF ⟨k,by simp [M,hk]⟩
  have hfc : F c≠0 := hF ⟨c,by simp [M,hc]⟩
  have hfd : F d≠0 := hF ⟨d,by simp [M,hd]⟩
  let u := F a/F c
  let v := F b/F c
  let κ := F k/F c
  let h := F d/F c
  refine ⟨u,v,κ,h,div_ne_zero hfa hfc,div_ne_zero hfb hfc,div_ne_zero hfk hfc,div_ne_zero hfd hfc,?_⟩
  intro i
  obtain ⟨hz,hw⟩ := hnzw i
  have hfx : F (X i)≠0 := hF ⟨X i,Finset.mem_erase.mpr ⟨(hgood i).1,
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem X (Finset.mem_univ i)))⟩⟩
  have hfy : F (X i+k)≠0 := hF ⟨X i+k,Finset.mem_erase.mpr ⟨(hgood i).2,
    Finset.mem_union_right _ (Finset.mem_image_of_mem (fun j => X j+k) (Finset.mem_univ i))⟩⟩
  have heX : X i = (z i)⁻¹ • a + z i • b := by
    change a/(z i:ℂ)+b*(z i:ℂ)=(z i:ℂ)⁻¹*a+(z i:ℂ)*b
    simp only [div_eq_mul_inv,mul_comm]
  have hlin : F (X i) = F c*(u/z i+v*z i) := by
    rw [heX,map_add,LinearMap.map_smul,LinearMap.map_smul,smul_eq_mul,smul_eq_mul]
    dsimp only [u,v]
    field_simp [hfc,hz] <;> ring
  have hlin' : F (X i+k)=F c*(u/z i+v*z i+κ) := by
    rw [map_add,hlin]
    dsimp only [κ]; field_simp [hfc] <;> ring
  have heY : X i+k = w i • c+(w i)⁻¹ • d := by
    change a/(z i:ℂ)+b*(z i:ℂ)+k=(w i:ℂ)*c+(w i:ℂ)⁻¹*d
    simpa only [div_eq_mul_inv,mul_comm] using (he i).symm
  have hrel : w i+h/w i=u/z i+v*z i+κ := by
    apply (mul_right_inj' hfc).mp
    rw [←hlin',heY,map_add,LinearMap.map_smul,LinearMap.map_smul,smul_eq_mul,smul_eq_mul]
    dsimp only [h]; field_simp [hfc,hw] <;> ring
  exact ⟨hrel,fun e => hfx (by rw [hlin,e,mul_zero]),fun e => hfy (by rw [hlin',e,mul_zero])⟩


lemma signed_conjugate {L : Type*} [Field L] (σ : L→+*L) (z w u v k h e f : L) (m : ℕ)
    (he : e=1 ∨ e= -1) (hf : f=1 ∨ f= -1) (hz : σ z=e*z^m) (hw : σ w=f*w^m)
    (hrel : w+h/w=u/z+v*z+k) :
    w^m+σ h/w^m=(f*e*σ u)/z^m+(f*e*σ v)*z^m+f*σ k := by
  have hh := congrArg σ hrel
  simp only [map_add,map_mul,map_div₀,hz,hw] at hh
  rcases he with rfl|rfl <;> rcases hf with rfl|rfl <;> simp at hh ⊢ <;>
    first | linear_combination hh | linear_combination -hh

lemma unique_sign_pattern {L : Type*} [Field L] [CharZero L] (b d : Bool×Bool)
    (x k y K : L) (hx : x≠0) (hy : x+k≠0) (hk : k≠0)
    (h₁ : x=(if b.2 then 1 else -1)*(if b.1 then 1 else -1)*y)
    (h₂ : k=(if b.2 then 1 else -1)*K)
    (h₃ : x+k=(if d.2 then 1 else -1)*(if d.1 then 1 else -1)*y+(if d.2 then 1 else -1)*K) : b=d := by
  rcases b with ⟨b,c⟩
  rcases d with ⟨d,e⟩
  cases b <;> cases c <;> cases d <;> cases e <;> first | rfl | skip
  all_goals
    exfalso
    simp only [Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul,mul_one,neg_neg,neg_mul,mul_neg] at h₁ h₂ h₃
    subst x
    subst k
    first
    | apply hx; linear_combination (1/2)*h₃
    | apply hx; linear_combination -(1/2)*h₃
    | apply hy; linear_combination (1/2)*h₃
    | apply hy; linear_combination -(1/2)*h₃
    | apply hk; linear_combination (1/2)*h₃
    | apply hk; linear_combination -(1/2)*h₃

lemma projected_data {ι : Type*} [Fintype ι] (n r : ℕ) [NeZero n] (hcop : r.Coprime n)
    (z w : ι→ℂ) (iz : Function.Injective z) (hz : ∀ i, (z i)^n=1) (hw : ∀ i,(w i)^n=1)
    (a b k c d : ℂ) (ha : a≠0) (hb : b≠0) (hk : k≠0) (hc : c≠0) (hd : d≠0)
    (he : ∀ i, c*w i+d/w i=a/z i+b*z i+k)
    (hg : ∀ i, a/z i+b*z i≠0 ∧ a/z i+b*z i+k≠0) :
    ∃ (K : IntermediateField ℚ ℂ) (σ : K→+*K) (Z W : ι→K) (U V C D : K),
      Function.Injective Z ∧ U≠0 ∧ V≠0 ∧ C≠0 ∧ D≠0 ∧ ∀ i,
        (Z i:ℂ)=z i ∧ (W i:ℂ)=w i ∧ Z i≠0 ∧ W i≠0 ∧ Z i^n=1 ∧ W i^n=1 ∧
        σ (Z i)=(Z i)^r ∧ σ (W i)=(W i)^r ∧
        W i+D/W i=U/Z i+V*Z i+C ∧ U/Z i+V*Z i≠0 ∧ U/Z i+V*Z i+C≠0 := by
  classical
  obtain ⟨K,hK,σ,hσ⟩ := automorphism_on_roots n r hcop
  let Z (i : ι) : K := ⟨z i,hK _ (hz i)⟩
  let W (i : ι) : K := ⟨w i,hK _ (hw i)⟩
  have zroot (i : ι) : Z i^n=1 := Subtype.ext (hz i)
  have wroot (i : ι) : W i^n=1 := Subtype.ext (hw i)
  have hzw (i : ι) : Z i≠0 ∧ W i≠0 := by
    refine ⟨fun he => ?_,fun he => ?_⟩
    · have hh := zroot i; simp [he,NeZero.ne n] at hh
    · have hh := wroot i; simp [he,NeZero.ne n] at hh
  obtain ⟨U,V,C,D,hU,hV,hC,hD,hs⟩ := projected_nonzero_relation K Z W a b k c d ha hb hk hc hd hzw he hg
  refine ⟨K,σ,Z,W,U,V,C,D,(fun _ _ h => iz (congrArg ((↑):K→ℂ) h)),hU,hV,hC,hD,?_⟩
  intro i
  exact ⟨rfl,rfl,(hzw i).1,(hzw i).2,zroot i,wroot i,hσ _ (zroot i),hσ _ (wroot i),hs i⟩


set_option maxHeartbeats 2400000 in
lemma nonexceptional_torsion {ι : Type*} [Fintype ι] (n : ℕ) (hn : 0<n)
    (z w : ι→ℂ) (iz : Function.Injective z) (hz : ∀ i,z i^n=1) (hw : ∀ i,w i^n=1)
    (a b k c d : ℂ) (ha : a≠0) (hb : b≠0) (hk : k≠0) (hc : c≠0) (hd : d≠0)
    (he : ∀ i,c*w i+d/w i=a/z i+b*z i+k) (hg : ∀ i,a/z i+b*z i≠0 ∧ a/z i+b*z i+k≠0) :
    Fintype.card ι≤32 := by
  classical
  induction n using Nat.strong_induction_on generalizing z w a b k c d with
  | h n ih =>
    by_contra! hbig
    let : NeZero n := ⟨by omega⟩
    by_cases heven : Even n
    · obtain ⟨m,hm⟩ := heven
      have hn2 : n=2*m := by omega
      let r := if Even m then 1 else 2
      have hcop : (m+r).Coprime n := by
        rw [hn2,Nat.coprime_mul_iff_right]
        by_cases hme : Even m
        · rw [show r=1 by simp [r,hme]]
          constructor
          · rw [Nat.coprime_two_right]; obtain ⟨j,hj⟩ := hme; exact ⟨j,by omega⟩
          · rw [Nat.add_comm,Nat.coprime_add_self_left]; simp
        · rw [show r=2 by simp [r,hme]]
          have ho : Odd m := Nat.not_even_iff_odd.mp hme
          constructor
          · rw [Nat.coprime_two_right]; obtain ⟨j,hj⟩ := ho; exact ⟨j+1,by omega⟩
          · rw [Nat.add_comm,Nat.coprime_add_self_left,Nat.coprime_two_left]; exact ho
      obtain ⟨K,σ,Z,W,U,V,C,D,iZ,hU,hV,hC,hD,data⟩ := projected_data n (m+r) hcop z w iz hz hw a b k c d ha hb hk hc hd he hg
      let eps (b : Bool) : K := if b then 1 else -1
      let cls (i : ι) := (decide (Z i^m=1),decide (W i^m=1))
      have epssign (b : Bool) : eps b=1 ∨ eps b= -1 := by cases b <;> simp [eps]
      have power (x : K) (hx : x^n=1) : x^m=eps (decide (x^m=1)) := by
        have hh : (x^m)^2=1 := by rwa [←pow_mul,Nat.mul_comm,←hn2]
        rcases sq_eq_one_iff.mp hh with he|he <;> simp [he,eps]
      have eqZ (i : ι) : Z i^m=eps (cls i).1 := power _ (data i).2.2.2.2.1
      have eqW (i : ι) : W i^m=eps (cls i).2 := power _ (data i).2.2.2.2.2.1
      have signrel (i : ι) : W i^r+σ D/W i^r =
          (eps (cls i).2*eps (cls i).1*σ U)/Z i^r+(eps (cls i).2*eps (cls i).1*σ V)*Z i^r+eps (cls i).2*σ C := by
        obtain ⟨_,_,_,_,_,_,hσz,hσw,hrel,_,_⟩ := data i
        apply signed_conjugate σ _ _ _ _ _ _ _ _ _ (epssign _) (epssign _) _ _ hrel
        · rw [hσz,pow_add,eqZ]
        · rw [hσw,pow_add,eqW]
      obtain ⟨B,_,hB⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (s:=Finset.univ) (fun i (_ : i∈(Finset.univ:Finset ι)) => Finset.mem_univ (cls i))
        (show (Finset.univ:Finset (Bool×Bool)).card*8<(Finset.univ:Finset ι).card by simpa using hbig)
      let I := Finset.univ.filter (fun i => cls i=B)
      let S := I.image Z
      have hsize : 8<S.card := by simpa [S,I,Finset.card_image_of_injective _ iZ] using hB
      let U' := eps B.2*eps B.1*σ U
      let V' := eps B.2*eps B.1*σ V
      let C' := eps B.2*σ C
      have hmatches (x : K) (hx : x∈S) : x≠0 ∧ ∃ y : K, y≠0 ∧ y+D/y=U/x+V*x+C ∧ y^r+σ D/y^r=U'/x^r+V'*x^r+C' := by
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨_,_,hz',hw',_,_,_,_,hh,_,_⟩ := data i
        exact ⟨hz',W i,hw',hh,by simpa only [U',V',C',(Finset.mem_filter.mp hi).2] using signrel i⟩
      by_cases hme : Even m
      · have hr : r=1 := by simp [r,hme]
        have hrig := linear_trace_rigidity S (by omega) U V C D U' V' C' (σ D) hU hV hC
          (fun x hx => by simpa [hr] using hmatches x hx)
        obtain ⟨hD',hU',hV',hC'⟩ := hrig
        have hclass (i : ι) : B=cls i := by
          obtain ⟨_,_,_,_,_,_,_,_,hrel,hx,hy⟩ := data i
          let X := U/Z i+V*Z i
          let Y := (σ U)/Z i+(σ V)*Z i
          apply unique_sign_pattern B (cls i) X C Y (σ C) hx hy hC
          · change U/Z i+V*Z i=eps B.2*eps B.1*((σ U)/Z i+(σ V)*Z i)
            calc
              _=U'/Z i+V'*Z i := by rw [hU',hV']
              _=_ := by dsimp only [U',V']; ring
          · exact hC'.symm
          · change X+C=eps (cls i).2*eps (cls i).1*Y+eps (cls i).2*σ C
            dsimp only [X,Y]
            have hh := signrel i
            rw [hr,pow_one,pow_one,hD',hrel] at hh
            linear_combination hh
        obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp (show 0<Fintype.card ι by omega)
        have cz (i : ι) : z i^m=z i₀^m := by
          have hh := (eqZ i).trans ((congrArg (fun b : Bool×Bool => eps b.1) ((hclass i).symm.trans (hclass i₀))).trans (eqZ i₀).symm)
          simpa only [IntermediateField.coe_pow,(data i).1,(data i₀).1] using congrArg ((↑):K→ℂ) hh
        have cw (i : ι) : w i^m=w i₀^m := by
          have hh := (eqW i).trans ((congrArg (fun b : Bool×Bool => eps b.2) ((hclass i).symm.trans (hclass i₀))).trans (eqW i₀).symm)
          simpa only [IntermediateField.coe_pow,(data i).2.1,(data i₀).2.1] using congrArg ((↑):K→ℂ) hh
        have zne (i : ι) : z i≠0 := by intro hh; have h := hz i; simp [hh,NeZero.ne n] at h
        have wne (i : ι) : w i≠0 := by intro hh; have h := hw i; simp [hh,NeZero.ne n] at h
        let z' (i : ι) := z i/z i₀
        let w' (i : ι) := w i/w i₀
        have hx (i : ι) : (a/z i₀)/z' i+(b*z i₀)*z' i=a/z i+b*z i := by
          dsimp only [z']; field_simp [zne i,zne i₀] <;> ring
        have hy (i : ι) : (c*w i₀)*w' i+(d/w i₀)/w' i=c*w i+d/w i := by
          dsimp only [w']; field_simp [wne i,wne i₀] <;> ring
        apply (not_lt_of_ge (ih m (by omega) (by omega) z' w'
          (fun _ _ h => iz ((div_left_inj' (zne i₀)).mp h))
          (fun i => by dsimp only [z']; rw [div_pow,cz i,div_self (pow_ne_zero _ (zne i₀))])
          (fun i => by dsimp only [w']; rw [div_pow,cw i,div_self (pow_ne_zero _ (wne i₀))])
          (a/z i₀) (b*z i₀) k (c*w i₀) (d/w i₀) (div_ne_zero ha (zne i₀)) (mul_ne_zero hb (zne i₀))
          hk (mul_ne_zero hc (wne i₀)) (div_ne_zero hd (wne i₀))
          (fun i => by rw [hx,hy,he]) (fun i => by rw [hx]; exact hg i))) hbig
      · have hr : r=2 := by simp [r,hme]
        have hbound := Erdos1082GeneralCurve.power_trace_bound S 2 (by decide) U V C D U' V' C' (σ D)
          hU hC hD ((_root_.map_ne_zero _).mpr hD) (fun x hx => by simpa [hr] using hmatches x hx)
        omega
    · have hcop := (Nat.not_even_iff_odd.mp heven).coprime_two_left
      obtain ⟨K,σ,Z,W,U,V,C,D,iZ,hU,hV,hC,hD,data⟩ := projected_data n 2 hcop z w iz hz hw a b k c d ha hb hk hc hd he hg
      let S := Finset.univ.image Z
      have hsize : S.card=Fintype.card ι := by simp [S,Finset.card_image_of_injective _ iZ]
      have hbound := Erdos1082GeneralCurve.power_trace_bound S 2 (by decide) U V C D (σ U) (σ V) (σ C) (σ D)
        hU hC hD ((_root_.map_ne_zero _).mpr hD) (by
          intro x hx
          obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨_,_,hz,hw,_,_,hσz,hσw,he,_,_⟩ := data i
          exact ⟨hz,W i,hw,he,by simpa only [map_add,map_div₀,map_mul,hσz,hσw] using congrArg σ he⟩)
      omega


lemma all_torsion_points (T : Finset Circle) (H : Subgroup Circle) (hT : (H:Set Circle)=T)
    (a b k c d : ℂ) (ha : a≠0) (hb : b≠0) (hk : k≠0) (hc : c≠0) (hd : d≠0)
    (S : Finset Circle) (hST : S⊆T) (hm : ∀ z∈S,∃ w∈T,c*(w:ℂ)+d/(w:ℂ)=a/(z:ℂ)+b*(z:ℂ)+k) :
    S.card≤36 := by
  classical
  by_cases hn : T.card=0
  · have := Finset.card_le_card hST; omega
  let X (z : Circle) := a/(z:ℂ)+b*(z:ℂ)
  let F (r : ℂ) := S.filter fun z => X z=r
  have few (r : ℂ) : (F r).card≤2 := by
    let P : Polynomial ℂ := C a-C r*Polynomial.X+C b*Polynomial.X^2
    have hp : P≠0 := by intro he; have h := congrArg (fun Q : Polynomial ℂ => Q.coeff 0) he; simpa [P,mul_coeff_zero,ha] using h
    have deg : P.natDegree≤2 := by dsimp [P]; compute_degree
    let J := (F r).image (fun z : Circle => (z:ℂ))
    have hsub : J⊆P.roots.toFinset := by
      intro z hz
      obtain ⟨z,hzF,rfl⟩ := Finset.mem_image.mp hz
      have he := (Finset.mem_filter.mp hzF).2
      change a/(z:ℂ)+b*(z:ℂ)=r at he
      apply Multiset.mem_toFinset.mpr
      apply (mem_roots hp).mpr
      change P.eval (z:ℂ)=0
      simp only [P,eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_pow]
      field_simp [Circle.coe_ne_zero z] at he
      linear_combination he
    have hj := (Finset.card_le_card hsub).trans <| (Multiset.toFinset_card_le _).trans <| (card_roots' P).trans deg
    have hi : Function.Injective (fun z : Circle => (z:ℂ)) := Circle.coe_injective
    have hcard : J.card=(F r).card := Finset.card_image_of_injective (F r) hi
    exact (le_of_eq hcard.symm).trans hj
  let G := S.filter fun z => X z≠0 ∧ X z+k≠0
  have hsub : S⊆G∪F 0∪F (-k) := by
    intro z hz
    by_cases h : X z=0
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,h⟩))
    by_cases h' : X z+k=0
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,eq_neg_of_add_eq_zero_left h'⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz,h,h'⟩))
  have wit (j : G) := hm j.1 (Finset.mem_filter.mp j.2).1
  let w (j : G) := (wit j).choose
  have hG := nonexceptional_torsion T.card (by omega) (fun j : G => (j.1:ℂ)) (fun j => (w j:ℂ))
    (fun _ _ he => Subtype.ext (Circle.coe_injective he)) (fun j => finite_subgroup_root _ _ hT _ (hST (Finset.mem_filter.mp j.2).1))
    (fun j => finite_subgroup_root _ _ hT _ (wit j).choose_spec.1) a b k c d ha hb hk hc hd
    (fun j => (wit j).choose_spec.2) (fun j => (Finset.mem_filter.mp j.2).2)
  rw [Fintype.card_coe] at hG
  have h := Finset.card_le_card hsub
  have := Finset.card_union_le (G∪F 0) (F (-k))
  have := Finset.card_union_le G (F 0)
  have := few 0; have := few (-k); omega


lemma orbit_norm (c p : ℂ) (z : Circle) :
    ((‖c+p*(z:ℂ)‖^2:ℝ):ℂ) = (Complex.normSq c:ℂ)+(Complex.normSq p:ℂ)+
        (starRingEnd ℂ c*p)*(z:ℂ)+(c*starRingEnd ℂ p)/(z:ℂ) := by
  rw [Complex.sq_norm,Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_conj_mul_self,
    map_add,map_mul,←Circle.coe_inv_eq_conj,Circle.coe_inv]
  field_simp [Circle.coe_ne_zero z]
  ring


lemma orbit_fiber_card (T : Finset Circle) (c p : ℂ) (hc : c≠0) (hp : p≠0) (r : ℝ) :
    (T.filter fun z : Circle => ‖c+p*(z:ℂ)‖=r).card ≤ 2 := by
  classical
  let q := -c/p
  apply (Finset.card_le_card (t := T.filter fun z : Circle => dist q (z:ℂ)=r/‖p‖) ?_).trans
    (circle_fibers T q (div_ne_zero (neg_ne_zero.mpr hc) hp) _)
  intro z hz
  obtain ⟨hz,he⟩ := Finset.mem_filter.mp hz
  refine Finset.mem_filter.mpr ⟨hz,?_⟩
  have heq : q-(z:ℂ) = -(c+p*(z:ℂ))/p := by dsimp [q]; field_simp; ring
  rw [dist_eq_norm,heq,norm_div,norm_neg,he]

lemma orbit_image_size (S : Finset Circle) (c p : ℂ) (hc : c≠0) (hp : p≠0) :
    S.card ≤ 2*(S.image fun z : Circle => ‖c+p*(z:ℂ)‖).card := by
  classical
  by_contra! h
  obtain ⟨r,_,hr⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (fun z (hz : z∈S) => Finset.mem_image_of_mem (fun z : Circle => ‖c+p*(z:ℂ)‖) hz)
    (show (S.image fun z : Circle => ‖c+p*(z:ℂ)‖).card*2<S.card by omega)
  exact (not_lt_of_ge (orbit_fiber_card S c p hc hp r)) hr



lemma uniform_orbit_intersection (T : Finset Circle) (H : Subgroup Circle) (hT : (H:Set Circle)=T)
    (c p q : ℂ) (hc : c≠0) (hp : p≠0) (hq : q≠0) (hn : ‖p‖≠‖q‖) :
    (T.filter fun z : Circle => ‖c+p*(z:ℂ)‖∈T.image (fun w : Circle => ‖c+q*(w:ℂ)‖)).card≤36 := by
  classical
  have hnorm : (Complex.normSq p:ℂ)≠(Complex.normSq q:ℂ) := by
    intro he
    have hh := Complex.ofReal_injective he
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at hh
    exact hn (by nlinarith [norm_nonneg p,norm_nonneg q])
  apply all_torsion_points T H hT (c*starRingEnd ℂ p) (starRingEnd ℂ c*p)
    ((Complex.normSq p:ℂ)-(Complex.normSq q:ℂ)) (starRingEnd ℂ c*q) (c*starRingEnd ℂ q)
    (mul_ne_zero hc ((_root_.map_ne_zero _).mpr hp)) (mul_ne_zero ((_root_.map_ne_zero _).mpr hc) hp) (sub_ne_zero.mpr hnorm)
    (mul_ne_zero ((_root_.map_ne_zero _).mpr hc) hq) (mul_ne_zero hc ((_root_.map_ne_zero _).mpr hq))
    _ (Finset.filter_subset _ _)
  intro z hz
  obtain ⟨w,hw,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hz).2
  refine ⟨w,hw,?_⟩
  have hh := congrArg (fun t : ℝ => ((t^2:ℝ):ℂ)) he
  rw [orbit_norm,orbit_norm] at hh
  linear_combination hh


end Erdos1082Uniform
end

section
namespace Erdos1082Threshold
lemma interpolate (b E t : ℝ) (hb : 0<b) (ht : 0≤t) (hmax : t≤b-E)
    (h : (E+t)*(b-t)^2 ≤36*b*(b+t)) : E≤36 ∨ E^2≤36*(2*b-E) := by
  by_contra! hn
  let L := b-E
  let p (u : ℝ) := (E+u)*(b-u)^2 - 36*b*(b+u)
  have hp₀ : 0<p 0 := by
    have : 0<b^2*(E-36) := mul_pos (sq_pos_of_pos hb) (by linarith [hn.1])
    dsimp [p]
    linarith only [this, (by ring : (E+0)*(b-0)^2-36*b*(b+0)=b^2*(E-36))]
  have hpL : 0<p L := by
    have : 0<b*(E^2-36*(2*b-E)) := mul_pos hb (by linarith [hn.2])
    dsimp [p,L]
    linarith only [this,(by ring : (E+(b-E))*(b-(b-E))^2-36*b*(b+(b-E))= b*(E^2-36*(2*b-E)))]
  have hL : t≤L := hmax
  have hbt : 0≤b-t := by dsimp [L] at hL; linarith [hn.1]
  have hpt : p t≤0 := sub_nonpos.mpr h
  have hL₀ : 0≤L := ht.trans hL
  rcases eq_or_lt_of_le ht with e|ht'
  · rw [← e] at hpt
    linarith
  have hi : L*p t-(L-t)*p 0-t*p L=L*t*(L-t)*(b-t) := by dsimp [p,L]; ring
  have h₁ := mul_nonneg (sub_nonneg.mpr hL) hp₀.le
  have h₂ := mul_pos ht' hpL
  have h₃ := mul_nonpos_of_nonneg_of_nonpos hL₀ hpt
  have h₄ := mul_nonneg (mul_nonneg (mul_nonneg hL₀ ht) (sub_nonneg.mpr hL)) hbt
  linarith only [hi,h₁,h₂,h₃,h₄]
end Erdos1082Threshold

namespace Erdos1082Threshold
lemma count_threshold (N b d k l : ℕ) (hb : 0<b) (hd : b≤d) (hN : d≤N)
    (hk : k*(2*b-d)≤b) (hl : l*(2*b-d)≤d) (hg : b+d≤N+36*k*l) :
    2*b≤N+36 ∨ (2*b-N)^2≤36*N := by
  by_cases he : 2*b≤N+36
  · exact Or.inl he
  right
  have hdb : d≤2*b := by omega
  have hNb : N≤2*b := by omega
  have hk' : (k:ℝ)*(2*(b:ℝ)-(d:ℝ))≤(b:ℝ) := by
    have hr : ((k*(2*b-d):ℕ):ℝ)≤(b:ℝ) := by exact_mod_cast hk
    push_cast [Nat.cast_sub hdb] at hr
    exact hr
  have hl' : (l:ℝ)*(2*(b:ℝ)-(d:ℝ))≤(d:ℝ) := by
    have hr : ((l*(2*b-d):ℕ):ℝ)≤(d:ℝ) := by exact_mod_cast hl
    push_cast [Nat.cast_sub hdb] at hr
    exact hr
  have hg' : (b:ℝ)+d≤N+36*k*l := by exact_mod_cast hg
  have hd' : (b:ℝ)≤d := by exact_mod_cast hd
  have hN' : (d:ℝ)≤N := by exact_mod_cast hN
  have hdb' : (d:ℝ)≤2*b := by exact_mod_cast hdb
  have hb' : (0:ℝ)<b := by exact_mod_cast hb
  have hne : (N:ℝ)+36<2*b := by exact_mod_cast (Nat.lt_of_not_ge he)
  let t := (d:ℝ)-(b:ℝ)
  let E := 2*(b:ℝ)-(N:ℝ)
  let δ := 2*(b:ℝ)-(d:ℝ)
  have δ₀ : 0≤δ := sub_nonneg.mpr hdb'
  have core : ((b:ℝ)+d-N)*δ^2 ≤ 36*b*d := by
    calc
      _ ≤ (36*(k:ℝ)*l)*δ^2 := by gcongr; linarith only [hg']
      _ = 36*((k:ℝ)*δ)*((l:ℝ)*δ) := by ring
      _ ≤ _ := by gcongr
  have hh := interpolate (b:ℝ) E t hb' (sub_nonneg.mpr hd') (by dsimp [t,E]; linarith) (by
    dsimp [t,E,δ] at *
    convert core using 1 <;> ring)
  have hres : (2*(b:ℝ)-(N:ℝ))^2≤36*N := by dsimp [E] at hh; rcases hh with h|h <;> linarith
  have res : (((2*b-N)^2:ℕ):ℝ)≤((36*N:ℕ):ℝ) := by
    push_cast [Nat.cast_sub hNb]
    exact hres
  exact_mod_cast res
end Erdos1082Threshold
end

section
/- Intersections between distances from an external point and chords of a circle subset. -/
open Classical
open scoped Pointwise
noncomputable section
namespace Erdos1082Cover

lemma chord_eq (x y : Circle) : dist x y=‖(-1:ℂ)+((x/y:Circle):ℂ)‖ := by
  change dist (x:ℂ) (y:ℂ)=‖(-1:ℂ)+(x:ℂ)/(y:ℂ)‖
  rw [dist_eq_norm,add_comm,← sub_eq_add_neg,div_sub_one (Circle.coe_ne_zero y),norm_div,Circle.norm_coe,div_one]

lemma off_eq (p : ℂ) (z a : Circle) :
    dist p (z:ℂ)=‖(-1:ℂ)+(p/(a:ℂ))*((a/z:Circle):ℂ)‖ := by
  change dist p (z:ℂ)=‖(-1:ℂ)+(p/(a:ℂ))*((a:ℂ)/(z:ℂ))‖
  have e : p/(a:ℂ)*((a:ℂ)/(z:ℂ))=p/(z:ℂ) := by field_simp
  rw [e,add_comm,← sub_eq_add_neg,div_sub_one (Circle.coe_ne_zero z),dist_eq_norm,norm_div,Circle.norm_coe,div_one]

lemma pair_overlap (S T : Finset Circle) (H : Subgroup Circle) (hHT : (H:Set Circle)=T)
    (p : ℂ) (hp : p≠0) (hn : ‖p‖≠1) (a b : Circle) :
    (S.filter fun z : Circle => (QuotientGroup.mk' H) z=(QuotientGroup.mk' H) a ∧
      ∃ w∈S/S, (QuotientGroup.mk' H) w=(QuotientGroup.mk' H) b ∧
        dist p (z:ℂ)=‖(-1:ℂ)+(w:ℂ)‖).card ≤ 36 := by
  classical
  let φ := QuotientGroup.mk' H
  let U := S.filter fun z : Circle => φ z=φ a ∧ ∃w∈S/S, φ w=φ b ∧ dist p (z:ℂ)=‖(-1:ℂ)+(w:ℂ)‖
  let V := T.filter fun z : Circle => ‖(-1:ℂ)+(p/(a:ℂ))*(z:ℂ)‖∈T.image (fun w : Circle => ‖(-1:ℂ)+(b:ℂ)*(w:ℂ)‖)
  have divT {x y : Circle} (he : φ x=φ y) : x/y∈T := by
    have hh : x/y∈H := QuotientGroup.eq_iff_div_mem.mp he
    change x/y∈(H:Set Circle) at hh
    rwa [hHT] at hh
  have hsub : U.image (fun z=>a/z)⊆V := by
    intro u hu
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨_,he,w,_,hw,eq⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨divT he.symm,Finset.mem_image.mpr ⟨w/b,divT hw,?_⟩⟩
    rw [← off_eq,eq]
    change ‖(-1:ℂ)+(b:ℂ)*((w:ℂ)/(b:ℂ))‖=‖(-1:ℂ)+(w:ℂ)‖
    rw [mul_div_cancel₀ _ (Circle.coe_ne_zero b)]
  have hu := Finset.card_image_of_injective U (div_right_injective (b:=a))
  have vv : V.card≤36 := Erdos1082Uniform.uniform_orbit_intersection T H hHT (-1) (p/(a:ℂ)) b
    (by norm_num) (div_ne_zero hp (Circle.coe_ne_zero a)) (Circle.coe_ne_zero b)
    (by simpa [norm_div,Circle.norm_coe] using hn)
  have le := Finset.card_le_card hsub
  change U.card≤36
  omega


lemma combined_overlap (S T : Finset Circle) (H : Subgroup Circle) (hHT : (H:Set Circle)=T)
    (p : ℂ) (hp : p≠0) (hn : ‖p‖≠1) :
    (S.filter fun z : Circle => dist p (z:ℂ)∈distanceSet S).card ≤
      36*(S.image (QuotientGroup.mk' H)).card*((S/S).image (QuotientGroup.mk' H)).card := by
  classical
  let φ := QuotientGroup.mk' H
  let I := (S.image φ).product ((S/S).image φ)
  let U := fun ij : (Circle ⧸ H) × (Circle ⧸ H) => S.filter fun z : Circle =>
    φ z=ij.1 ∧ ∃ w∈S/S, φ w=ij.2 ∧ dist p (z:ℂ)=‖(-1:ℂ)+(w:ℂ)‖
  have sub : (S.filter fun z : Circle => dist p (z:ℂ)∈distanceSet S) ⊆ I.biUnion U := by
    intro z hz
    obtain ⟨hz,hd⟩ := Finset.mem_filter.mp hz
    obtain ⟨⟨x,y⟩,he,ed⟩ := Finset.mem_image.mp hd
    obtain ⟨hx,hy,_⟩ := Finset.mem_offDiag.mp he
    have hw : x/y∈S/S := Finset.mem_div.mpr ⟨x,hx,y,hy,rfl⟩
    refine Finset.mem_biUnion.mpr ⟨(φ z,φ (x/y)),Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem φ hz,Finset.mem_image_of_mem φ hw⟩,?_⟩
    exact Finset.mem_filter.mpr ⟨hz,rfl,x/y,hw,rfl,ed.symm.trans (chord_eq x y)⟩
  have cardU (ij) (hh : ij∈I) : (U ij).card≤36 := by
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hh
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hi
    obtain ⟨y,_,hy⟩ := Finset.mem_image.mp hj
    dsimp only [U]
    rw [← hx, ← hy]
    exact pair_overlap S T H hHT p hp hn x y
  calc
    _ ≤ (I.biUnion U).card := Finset.card_le_card sub
    _ ≤ ∑ ij∈I, (U ij).card := Finset.card_biUnion_le
    _ ≤ ∑ _∈I, 36 := Finset.sum_le_sum cardU
    _ = _ := by simp [I,φ]; ring

lemma circle_geometry (A : Finset ℂ) (S T : Finset Circle) (H : Subgroup Circle)
    (hHT : (H:Set Circle)=T) (hSA : ∀z∈S, (z:ℂ)∈A)
    (p : ℂ) (hpA : p∈A) (hp : p≠0) (hn : ‖p‖≠1) :
    (S/S).card+S.card≤2*distinctDistances A+1+
    36*(S.image (QuotientGroup.mk' H)).card*((S/S).image (QuotientGroup.mk' H)).card := by
  classical
  let U := S.filter fun z : Circle => dist p (z:ℂ)∉distanceSet S
  let V := S.filter fun z : Circle => dist p (z:ℂ)∈distanceSet S
  let D := distanceSet A\distanceSet S
  have SA : distanceSet S⊆distanceSet A := by
    intro d hd
    obtain ⟨⟨x,y⟩,hpair,eq⟩ := Finset.mem_image.mp hd
    obtain ⟨hx,hy,he⟩ := Finset.mem_offDiag.mp hpair
    exact Finset.mem_image.mpr ⟨((x:ℂ),(y:ℂ)),Finset.mem_offDiag.mpr ⟨hSA x hx,hSA y hy,Circle.coe_injective.ne he⟩,eq⟩
  have hmap (z : Circle) (hz : z∈U) : dist p (z:ℂ)∈D := by
    obtain ⟨hz,hz'⟩ := Finset.mem_filter.mp hz
    have he : p≠(z:ℂ) := fun eq => hn (eq ▸ Circle.norm_coe z)
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨(p,(z:ℂ)),Finset.mem_offDiag.mpr ⟨hpA,hSA z hz,he⟩,rfl⟩,hz'⟩
  have ub : U.card≤2*D.card := by
    by_contra! h
    obtain ⟨d,_,hd⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmap
      (show D.card*2<U.card by omega)
    exact (not_lt_of_ge (OMA.R_Erdos1082_erdos_1082_parts_i_R1.circle_fibers U p hp d)) hd
  have hh := combined_overlap S T H hHT p hp hn
  have hsum : V.card+U.card=S.card := Finset.card_filter_add_card_filter_not _
  have hD := Finset.card_sdiff_add_card_eq_card SA
  have hS := OMA.R_Erdos1082_erdos_1082_parts_i_R1.circle_quotient_card S
  change V.card≤_ at hh
  change D.card+(distanceSet S).card=(distanceSet A).card at hD
  change (S/S).card≤2*(distanceSet S).card+1 at hS
  change (S/S).card+S.card≤2*(distanceSet A).card+1+_
  omega
end Erdos1082Cover
end
end

section
/- A circle-count restriction for critical distinct-distance configurations. -/
open Classical EuclideanGeometry
open scoped Pointwise
noncomputable section
namespace Erdos1082Cover
open OMA.R_Erdos1082_erdos_1082_parts_i_R1

lemma unit_threshold (A : Finset ℂ) (S : Finset Circle) (hs : S.Nonempty)
    (hSA : ∀z∈S, (z:ℂ)∈A) (p : ℂ) (hpA : p∈A) (hp : p≠0) (hn : ‖p‖≠1) (N : ℕ)
    (hN : 2*distinctDistances A+1≤N) :
    2*S.card≤N+36 ∨ (2*S.card-N)^2≤36*N := by
  classical
  obtain ⟨H,T,hHT,hk,hl⟩ := Erdos1082Atom.cover_weights S hs
  have hh := circle_geometry A S T H hHT hSA p hpA hp hn
  have SA : distanceSet S⊆distanceSet A := by
    intro d hd
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hx,hy,he⟩ := Finset.mem_offDiag.mp hxy
    exact Finset.mem_image.mpr ⟨((x:ℂ),(y:ℂ)),Finset.mem_offDiag.mpr ⟨hSA x hx,hSA y hy,Circle.coe_injective.ne he⟩,rfl⟩
  have hDist : distinctDistances S≤distinctDistances A := Finset.card_le_card SA
  exact Erdos1082Threshold.count_threshold N S.card (S/S).card _ _ (Finset.card_pos.mpr hs)
    Finset.card_le_card_div_self (by have := circle_quotient_card S; omega) hk hl (by omega)

lemma planar_threshold (A B : Finset ℝ²) (c p : ℝ²) (r : ℝ) (hBA : B⊆A) (hcard : 2<B.card)
    (hC : ∀x∈B, dist x c=r) (hp : p∈A) (hpc : p≠c) (hpr : dist p c≠r) :
    let N := 2*distinctDistances A+1
    2*B.card≤N+36 ∨ (2*B.card-N)^2≤36*N := by
  classical
  have hsub : ¬ B ⊆ {c} := by
    intro h; have hh : B.card ≤ 1 := (Finset.card_le_card h).trans_eq (Finset.card_singleton c); omega
  obtain ⟨x,hx,hxc⟩ := Finset.not_subset.mp hsub
  have hr : 0 < r := (dist_pos.mpr (show x ≠ c by simpa using hxc)).trans_eq (hC x hx)
  let E := Complex.orthonormalBasisOneI.repr.symm
  let F (x : ℝ²) := E (x-c) / (r : ℂ)
  have hdist (x y : ℝ²) : dist (F x) (F y) = dist x y / r := by
    rw [dist_eq_norm]; dsimp only [F]
    rw [←sub_div,norm_div,←map_sub,E.norm_map,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,
      show (x-c)-(y-c) = x-y by abel,dist_eq_norm]
  have hFc : F c = 0 := by simp [F]
  have hnorm (x : ℝ²) : ‖F x‖ = dist x c / r := by rw [←dist_zero_right,← hFc,hdist]
  have hinj : Function.Injective F := by
    intro x y h
    have hxy := hdist x y
    rw [h,dist_self] at hxy
    exact dist_eq_zero.mp ((div_eq_zero_iff.mp hxy.symm).resolve_right hr.ne')
  let G (x : B) : Circle := ⟨F x.1, mem_sphere_zero_iff_norm.mpr (by rw [hnorm,hC _ x.2,div_self hr.ne'])⟩
  let S := B.attach.image G
  let D := (distanceSet A).image (· / r)
  have hG : Function.Injective G := by
    intro u v h
    exact Subtype.ext (hinj (congrArg ((↑) : Circle → ℂ) h))
  have hSc : S.card = B.card := by dsimp [S]; rw [Finset.card_image_of_injective _ hG,Finset.card_attach]
  have hDc : D.card = distinctDistances A := by
    apply Finset.card_image_of_injective
    exact fun _ _ h => (div_left_inj' hr.ne').mp h
  let A' := A.image F
  have hs : S.Nonempty := Finset.card_pos.mp (by omega)
  have SA (z : Circle) (hz : z∈S) : (z:ℂ)∈A' := by
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image_of_mem F (hBA x.2)
  have hpA : F p∈A' := Finset.mem_image_of_mem F hp
  have hDsub : distanceSet A'⊆D := by
    intro d hd
    obtain ⟨⟨x,y⟩,hpair,heq⟩ := Finset.mem_image.mp hd
    obtain ⟨hx,hy,he⟩ := Finset.mem_offDiag.mp hpair
    obtain ⟨x,hxA,ex⟩ := Finset.mem_image.mp hx
    obtain ⟨y,hyA,ey⟩ := Finset.mem_image.mp hy
    change F x=_ at ex
    change F y=_ at ey
    change dist _ _=d at heq
    rw [← ex, ← ey] at heq
    change _≠_ at he
    rw [← ex, ← ey] at he
    have exy : x≠y := fun e => he (congrArg F e)
    exact Finset.mem_image.mpr ⟨dist x y,dist_mem hxA hyA exy,(hdist x y).symm.trans heq⟩
  have hdistA : distinctDistances A'≤distinctDistances A := (Finset.card_le_card hDsub).trans_eq hDc
  have hh := unit_threshold A' S hs SA (F p) hpA
    (fun he => hpc (hinj (he.trans hFc.symm)))
    (by rw [hnorm]; exact fun he => hpr ((div_eq_one_iff_eq hr.ne').mp he)) (2*distinctDistances A+1) (by omega)
  simpa [hSc] using hh

theorem critical_circle_threshold (A : Finset ℝ²) (hn : NonTrilinear (A:Set ℝ²))
    (hA : A.card=2*distinctDistances A+2) (c : ℝ²) (r : ℝ) :
    let b := (A.filter fun x => dist x c=r).card
    let N := A.card-1
    2*b≤N+36 ∨ (2*b-N)^2≤36*N := by
  classical
  let B := A.filter fun x => dist x c=r
  change 2*B.card≤A.card-1+36 ∨ (2*B.card-(A.card-1))^2≤36*(A.card-1)
  by_cases hcard : 2<B.card
  · by_cases hex : ∃p∈A, p≠c ∧ dist p c≠r
    · obtain ⟨p,hp,hpc,hpr⟩ := hex
      have ee : A.card-1=2*distinctDistances A+1 := by omega
      rw [ee]
      exact planar_threshold A B c p r (Finset.filter_subset _ _) hcard
        (fun x hx => (Finset.mem_filter.mp hx).2) hp hpc hpr
    · have hh := all_but_one_concyclic A c r hn c (by
        intro x hx
        by_contra he
        exact hex ⟨x,Finset.mem_of_mem_erase hx,Finset.ne_of_mem_erase hx,he⟩)
      omega
  · left; omega

end Erdos1082Cover
end
end

section
/- A set with a small ratio set has minimal doubling in every torsion-free image. -/
open Classical
open scoped Pointwise
noncomputable section
namespace Erdos1082Projection
variable {G K : Type*} [CommGroup G] [CommGroup K]

def levels (U : Finset G) (φ : G →* K) (j : ℕ) : Finset K :=
  (U.image φ).filter fun q => j < (U.filter fun z => φ z=q).card

lemma level_count_bound (U : Finset G) (φ : G→*K) (R : ℕ) (h : ∀q∈U.image φ, (U.filter fun z => φ z=q).card≤R) :
    ∑ j ∈ Finset.range R,(levels U φ j).card=U.card := by
  classical
  calc
    _ = ∑ j∈Finset.range R, ∑ q∈U.image φ, if j<(U.filter fun z => φ z=q).card then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      simp [levels,Finset.sum_boole]
    _ = ∑ q∈U.image φ, ∑ j∈Finset.range R, if j<(U.filter fun z => φ z=q).card then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ q∈U.image φ, (U.filter fun z => φ z=q).card := by
      apply Finset.sum_congr rfl
      intro q hq
      let d := (U.filter fun z => φ z=q).card
      have hd : d≤R := h q hq
      have e : (Finset.range R).filter (fun j => j<d)=Finset.range d := by
        ext j; simp only [Finset.mem_filter,Finset.mem_range]; omega
      change (∑ j∈Finset.range R, if j<d then 1 else 0)=d
      rw [Finset.sum_boole,e,Finset.card_range]; rfl
    _ = _ := (Finset.card_eq_sum_card_image φ U).symm

lemma level_count (U : Finset G) (φ : G→*K) (R : ℕ) (h : U.card≤R) :
    ∑ j ∈ Finset.range R,(levels U φ j).card=U.card :=
  level_count_bound U φ R (fun _ _ => (Finset.card_le_card (Finset.filter_subset _ _)).trans h)

lemma levels_partial (U : Finset G) (φ : G→*K) (R : ℕ) :
    ∑ j∈Finset.range R,(levels U φ j).card≤U.card := by
  have hh := level_count U φ (R+U.card) (by omega)
  rw [Finset.sum_range_add] at hh
  omega

lemma level_div (S : Finset G) (φ : G→*K) (j : ℕ) :
    levels S φ j/S.image φ ⊆ levels (S/S) φ j := by
  classical
  intro q hq
  obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_div.mp hq
  obtain ⟨v,hvS,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hu,ht⟩ := Finset.mem_filter.mp hu
  obtain ⟨u,huS,rfl⟩ := Finset.mem_image.mp hu
  let F := S.filter fun z => φ z=φ u
  let D := (S/S).filter fun z => φ z=φ u/φ v
  have hsub : F.image (·/v)⊆D := by
    intro a ha; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hx,he⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_div.mpr ⟨x,hx,v,hvS,rfl⟩,by rw [map_div,he]⟩
  have cc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (div_left_injective (b:=v))] at cc
  have ex : u/v ∈S/S := Finset.mem_div.mpr ⟨u,huS,v,hvS,rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨u/v,ex,map_div φ u v⟩,lt_of_lt_of_le ht cc⟩

theorem projected_doubling (S : Finset G) (φ : G→*K) [IsMulTorsionFree K]
    (hd : (S/S).card<2*S.card) :
    ((S.image φ)/(S.image φ)).card+1=2*(S.image φ).card := by
  classical
  let P := S.image φ
  have hs : S.Nonempty := Finset.card_pos.mp (by omega)
  have hP : P.Nonempty := hs.image φ
  have cd (A B : Finset K) (hA : A.Nonempty) (hB : B.Nonempty) :
      A.card+B.card-1≤(A/B).card := by
    simpa only [div_eq_mul_inv,Finset.card_inv] using cauchy_davenport_of_isMulTorsionFree hA
      (show B⁻¹.Nonempty from by obtain ⟨x,hx⟩:=hB; exact ⟨x⁻¹,by simpa using hx⟩)
  have hmin := cd P P hP hP
  change (P/P).card+1=2*P.card
  by_contra he
  have hbad : 2*P.card≤(P/P).card := by omega
  let R := S.card+(S/S).card
  have level (j : ℕ) : 2*(levels S φ j).card≤(levels (S/S) φ j).card := by
    let L := levels S φ j
    have hsub : L⊆P := Finset.filter_subset _ _
    have upper := Finset.card_le_card (level_div S φ j)
    change (L/P).card≤_ at upper
    by_cases h : L=P
    · change 2*L.card≤_
      rw [h] at upper ⊢
      omega
    by_cases he : L.Nonempty
    · have lt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,h⟩)
      have hh := cd L P he hP
      change 2*L.card≤_
      omega
    · have ez := Finset.not_nonempty_iff_eq_empty.mp he
      simp [← show L=levels S φ j from rfl,ez]
  have add := Finset.sum_le_sum (s:=Finset.range R) fun i _ => level i
  rw [← Finset.mul_sum,level_count S φ R (by dsimp [R]; omega),level_count (S/S) φ R (by dsimp [R]; omega)] at add
  omega
end Erdos1082Projection
end
end

section
/- A fiber bound for a set whose ratio set has minimal size in a torsion-free group. -/
open Classical
open scoped Pointwise
noncomputable section
namespace Erdos1082Projection
variable {G K : Type*} [CommGroup G] [CommGroup K] [IsMulTorsionFree G] [IsMulTorsionFree K]

private lemma cd {L : Type*} [CommGroup L] [IsMulTorsionFree L] (X Y : Finset L)
    (hx : X.Nonempty) (hy : Y.Nonempty) : X.card+Y.card-1≤(X/Y).card := by
  simpa only [div_eq_mul_inv,Finset.card_inv] using cauchy_davenport_of_isMulTorsionFree hx
    (show Y⁻¹.Nonempty from by obtain ⟨y,hy⟩:=hy; exact ⟨y⁻¹,by simpa using hy⟩)

lemma dimension_count (S : Finset G) (φ : G→*K) (a : K) (ha : a∈S.image φ)
    (hmax : ∀q∈S.image φ, (S.filter fun z => φ z=q).card≤(S.filter fun z => φ z=a).card) :
    let s := (S.image φ).card
    let M := (S.filter fun z => φ z=a).card
    2*S.card+M*(s-1)≤(S/S).card+s := by
  classical
  let P := S.image φ
  let F := fun q:K => S.filter fun z => φ z=q
  let M := (F a).card
  let D := S/S
  let A := fun i => (levels S φ i).card
  let B := fun i => (levels D φ i).card
  have Fne {x} (hx : x∈P) : (F x).Nonempty := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨z,Finset.mem_filter.mpr ⟨hz,rfl⟩⟩
  have hM : 0<M := Finset.card_pos.mpr (Fne ha)
  have hP : P.Nonempty := ⟨a,ha⟩
  have hPpos := Finset.card_pos.mpr hP
  have hSum : ∑i∈Finset.range M,A i=S.card := level_count_bound S φ M hmax
  have h0 : levels S φ 0=P := by
    apply Finset.Subset.antisymm (Finset.filter_subset _ _)
    intro q hq
    exact Finset.mem_filter.mpr ⟨hq,Finset.card_pos.mpr (Fne hq)⟩
  have hfirst (j : ℕ) (hj : j<M) : A j+(P.card-1)≤B j := by
    have ne : (levels S φ j).Nonempty := ⟨a,Finset.mem_filter.mpr ⟨ha,hj⟩⟩
    have h := cd (levels S φ j) P ne hP
    have hh := Finset.card_le_card (level_div S φ j)
    change (levels S φ j/P).card≤B j at hh
    dsimp [A]; omega
  have hsecond (j : ℕ) : A (j+1)≤B (M+j) := by
    let X := levels S φ (j+1)
    have sub : X.image (·/a) ⊆ levels D φ (M+j) := by
      intro q hq
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hx,hxcard⟩ := Finset.mem_filter.mp hx
      have non := Fne hx
      have ca := cd (F x) (F a) non (Fne ha)
      have into : F x/F a⊆D.filter (fun z => φ z=x/a) := by
        intro z hz; obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_div.mp hz
        obtain ⟨hu,eu⟩ := Finset.mem_filter.mp hu
        obtain ⟨hv,ev⟩ := Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_div.mpr ⟨u,hu,v,hv,rfl⟩,by rw [map_div,eu,ev]⟩
      have le := Finset.card_le_card into
      have cnt : M+j<(D.filter fun z => φ z=x/a).card := by
        change j+1<(F x).card at hxcard
        change _+M-1≤_ at ca
        omega
      have hf := Finset.card_pos.mp (lt_of_le_of_lt (by omega : 0≤M+j) cnt)
      obtain ⟨w,hw⟩ := hf
      obtain ⟨hw,he⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨w,hw,he⟩,cnt⟩
    have le := Finset.card_le_card sub
    rwa [Finset.card_image_of_injective _ (div_left_injective (b:=a))] at le
  have sum₁ := Finset.sum_le_sum (s:=Finset.range M) (fun j hj => hfirst j (Finset.mem_range.mp hj))
  rw [Finset.sum_add_distrib,hSum,Finset.sum_const,Finset.card_range,smul_eq_mul] at sum₁
  have sum₂ := Finset.sum_le_sum (s:=Finset.range (M-1)) fun j _ => hsecond j
  have tail : (∑ j∈Finset.range (M-1),A (j+1))+P.card=S.card := by
    have e : M-1+1=M := by omega
    have hh := Finset.sum_range_succ' A (M-1)
    rw [e,hSum] at hh
    have hh₀ : A 0=P.card := congrArg Finset.card h0
    omega
  have total := levels_partial D φ (M+(M-1))
  change (∑e∈Finset.range (M+(M-1)),B e)≤D.card at total
  rw [Finset.sum_range_add] at total
  change 2*S.card+M*(P.card-1)≤D.card+P.card
  omega
end Erdos1082Projection
end
end

section
/- A finite set with fewer than twice as many ratios has rational rank at most one modulo torsion. -/
open Classical
open scoped Pointwise
noncomputable section
namespace Erdos1082Projection
variable {G K : Type*} [CommGroup G] [CommGroup K]

lemma collapse_of_collision [IsMulTorsionFree G] [IsMulTorsionFree K]
    (S : Finset G) (φ : G→*K) (hc : (S/S).card+1=2*S.card)
    {x y : G} (hx : x∈S) (hy : y∈S) (hne : x≠y) (he : φ x=φ y) :
    ∀u∈S, ∀v∈S, φ u=φ v := by
  classical
  let P := S.image φ
  let F := fun q : K => S.filter fun z => φ z=q
  have ne : P.Nonempty := ⟨φ x,Finset.mem_image_of_mem φ hx⟩
  obtain ⟨a,ha,hmax⟩ := Finset.exists_max_image P (fun q => (F q).card) ne
  have co := dimension_count S φ a ha hmax
  change 2*S.card+(F a).card*(P.card-1)≤(S/S).card+P.card at co
  have two : 2≤(F a).card := by
    have xy : ({x,y}:Finset G)⊆F (φ x) := by
      intro z hz
      rcases Finset.mem_insert.mp hz with e|e
      · subst z; exact Finset.mem_filter.mpr ⟨hx,rfl⟩
      · have eq := Finset.mem_singleton.mp e
        subst z; exact Finset.mem_filter.mpr ⟨hy,he.symm⟩
    have hh := Finset.card_le_card xy
    rw [Finset.card_pair hne] at hh
    exact hh.trans (hmax _ (Finset.mem_image_of_mem φ hx))
  have one : P.card≤1 := by
    have hh := Nat.mul_le_mul_right (P.card-1) two
    omega
  intro u hu v hv
  exact Finset.card_le_one.mp one _ (Finset.mem_image_of_mem φ hu) _ (Finset.mem_image_of_mem φ hv)

theorem dependent_ratios (S : Finset G) (hd : (S/S).card<2*S.card) {x : G}
    (hx : x∈S/S) (hn : ¬IsOfFinOrder x) (y : G) (hy : y∈S/S) :
    ∃ n : ℕ, 0<n ∧ ∃ z : ℤ, IsOfFinOrder (y^n/x^z) := by
  classical
  let K := G ⧸ CommGroup.torsion G
  letI : DecidableEq K := Classical.decEq K
  let φ : G →* K := QuotientGroup.mk' (CommGroup.torsion G)
  let L := K ⧸ Subgroup.zpowers (φ x)
  let η : K →* L := QuotientGroup.mk' (Subgroup.zpowers (φ x))
  let τ := QuotientGroup.mk' (CommGroup.torsion L)
  let ψ := τ.comp η
  let P := S.image φ
  have hm := projected_doubling S φ hd
  have hx1 : φ x≠1 := fun h => hn ((QuotientGroup.eq_one_iff x).mp h)
  have hηx : η (φ x)=1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
  obtain ⟨u,hu,v,hv,ex⟩ := Finset.mem_div.mp hx
  have hxφ : φ u/φ v=φ x := (map_div φ u v).symm.trans (congrArg φ ex)
  have hne : φ u≠φ v := by intro e; rw [e,div_self'] at hxφ; exact hx1 hxφ.symm
  have hψ : ψ (φ u)=ψ (φ v) := by
    apply div_eq_one.mp
    rw [← map_div,hxφ]
    simp [ψ,hηx]
  have same := collapse_of_collision P ψ (by simpa [P,K] using hm) (Finset.mem_image_of_mem φ hu) (Finset.mem_image_of_mem φ hv) hne hψ
  obtain ⟨u,hu,v,hv,ey⟩ := Finset.mem_div.mp hy
  have hxφ' : φ u/φ v=φ y := (map_div φ u v).symm.trans (congrArg φ ey)
  have hyone : ψ (φ y)=1 := by
    rw [← hxφ',map_div,same _ (Finset.mem_image_of_mem φ hu) _ (Finset.mem_image_of_mem φ hv),div_self']
  have hyt : IsOfFinOrder (η (φ y)) := (QuotientGroup.eq_one_iff _).mp hyone
  obtain ⟨n,hn',hp⟩ := hyt.exists_pow_eq_one
  have hmemp : (φ y)^n∈Subgroup.zpowers (φ x) := (QuotientGroup.eq_one_iff _).mp (by
    change η ((φ y)^n)=1; rw [map_pow,hp])
  obtain ⟨z,ez⟩ := hmemp
  change (φ x)^z=(φ y)^n at ez
  refine ⟨n,hn',z,?_⟩
  change y^n/x^z∈CommGroup.torsion G
  apply (QuotientGroup.eq_one_iff _).mp
  change φ (y^n/x^z)=1
  rw [map_div,map_pow,map_zpow,ez,div_self']
end Erdos1082Projection
end
end

section
/- A half-size circle in a critical configuration is contained in one cyclic direction modulo roots of unity. -/
open Classical EuclideanGeometry
open scoped Pointwise
noncomputable section
namespace Erdos1082Projection
variable {G : Type*} [CommGroup G]

private lemma extend_rel (y x:G) (n m:ℕ) (z:ℤ) (h : IsOfFinOrder (y^n/x^z)) :
    IsOfFinOrder (y^(n*m)/x^(z*(m:ℤ))) := by
  have hh := h.pow (n:=m)
  rwa [div_pow,← pow_mul,← zpow_natCast (x^z),← zpow_mul] at hh

lemma common_den (U : Finset G) (x : G)
    (h : ∀y∈U, ∃ n : ℕ, 0<n ∧ ∃ z : ℤ, IsOfFinOrder (y^n/x^z)) :
    ∃ n : ℕ, 0<n ∧ ∀y∈U, ∃ z : ℤ, IsOfFinOrder (y^n/x^z) := by
  classical
  induction U using Finset.induction_on with
  | empty => exact ⟨1,one_pos,by simp⟩
  | @insert a U _ ih =>
    obtain ⟨n,hn,z,hz⟩ := h a (Finset.mem_insert_self ..)
    obtain ⟨m,hm,hh⟩ := ih (fun y hy => h y (Finset.mem_insert_of_mem hy))
    refine ⟨n*m,Nat.mul_pos hn hm,?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl|hy
    · exact ⟨_,extend_rel _ _ n m z hz⟩
    obtain ⟨w,hw⟩ := hh y hy
    exact ⟨_,Nat.mul_comm m n ▸ extend_rel _ _ m n w hw⟩

theorem circle_rank_one (S : Finset Circle) (hd : (S/S).card<2*S.card) :
    ∃ g : Circle, ∀y∈S/S, ∃ z : ℤ, IsOfFinOrder (y/g^z) := by
  classical
  by_cases he : ∃x∈S/S, ¬IsOfFinOrder x
  · obtain ⟨x,hx,hn⟩ := he
    obtain ⟨n,hN,hrel⟩ := common_den (S/S) x (dependent_ratios S hd hx hn)
    obtain ⟨θ,hθ⟩ := Circle.exp_surjective x
    let g := Circle.exp (θ/(n:ℝ))
    have eg : g^n=x := by
      dsimp [g]; rw [← Circle.exp_nsmul,nsmul_eq_mul,mul_div_cancel₀ _ (by exact_mod_cast hN.ne'),hθ]
    refine ⟨g,?_⟩
    intro y hy
    obtain ⟨z,hz⟩ := hrel y hy
    refine ⟨z,IsOfFinOrder.of_pow (n:=n) ?_ hN.ne'⟩
    have ez : (g^z)^n=(g^n)^z := by rw [← zpow_natCast (g^z),← zpow_natCast g n,← zpow_mul,← zpow_mul,Int.mul_comm]
    rwa [div_pow,ez,eg]
  · refine ⟨1,?_⟩
    intro y hy
    refine ⟨0,?_⟩
    simpa using (show IsOfFinOrder y from by by_contra hn; exact he ⟨y,hy,hn⟩)

theorem half_circle_rank (A : Finset ℂ) (S : Finset Circle)
    (inc : ∀z∈S,(z:ℂ)∈A) (hsize : 2*distinctDistances A+1<2*S.card) :
    ∃g : Circle, ∀y∈S/S, ∃z : ℤ, IsOfFinOrder (y/g^z) := by
  apply circle_rank_one
  have sub : distanceSet S⊆distanceSet A := by
    intro d hd
    obtain ⟨⟨a,b⟩,hp,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨ha,hb,he⟩ := Finset.mem_offDiag.mp hp
    exact Finset.mem_image.mpr ⟨((a:ℂ),(b:ℂ)),Finset.mem_offDiag.mpr ⟨inc a ha,inc b hb,Circle.coe_injective.ne he⟩,rfl⟩
  have hD : distinctDistances S≤distinctDistances A := Finset.card_le_card sub
  have hd := OMA.R_Erdos1082_erdos_1082_parts_i_R1.circle_quotient_card S
  omega
end Erdos1082Projection
end
end

section
/- Simultaneous specialization of finitely many rational functions at roots of unity. -/
open Filter Polynomial Classical
noncomputable section
namespace Erdos1082Specialize
variable {K : Type} [Field K] (f : K→+*ℂ)

lemma polynomial_nonzero {p : K[X]} (hp : p≠0) :
    ∀ᶠ a in cofinite, p.eval₂ f a≠0 := by
  classical
  let Q := p.map f
  have hQ : Q≠0 := (Polynomial.map_ne_zero_iff f.injective).mpr hp
  have hh := (Q.roots.toFinset.finite_toSet).eventually_cofinite_notMem
  filter_upwards [hh] with a ha
  intro h
  apply ha
  exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ).mpr (by
    change (p.map f).eval a=0
    rwa [Polynomial.eval_map]))

lemma denominator (u : RatFunc K) : ∀ᶠ a in cofinite, u.denom.eval₂ f a≠0 :=
  polynomial_nonzero f (RatFunc.denom_ne_zero u)

lemma nonzero {u : RatFunc K} (hu : u≠0) : ∀ᶠ a in cofinite, RatFunc.eval f a u≠0 := by
  filter_upwards [denominator f u,polynomial_nonzero f (RatFunc.num_ne_zero hu)] with a hd hn
  exact div_ne_zero hn hd

lemma ev_add (u v : RatFunc K) : ∀ᶠ a in cofinite,
    RatFunc.eval f a (u+v)=RatFunc.eval f a u+RatFunc.eval f a v := by
  filter_upwards [denominator f u,denominator f v] with a hu hv
  exact RatFunc.eval_add f a hu hv

lemma ev_mul (u v : RatFunc K) : ∀ᶠ a in cofinite,
    RatFunc.eval f a (u*v)=RatFunc.eval f a u*RatFunc.eval f a v := by
  filter_upwards [denominator f u,denominator f v] with a hu hv
  exact RatFunc.eval_mul f a hu hv

lemma ev_inv (u : RatFunc K) : ∀ᶠ a in cofinite,
    RatFunc.eval f a u⁻¹=(RatFunc.eval f a u)⁻¹ := by
  by_cases h : u=0
  · simp [h]
  filter_upwards [ev_mul f u⁻¹ u,nonzero f h] with a he hn
  rw [inv_mul_cancel₀ h,RatFunc.eval_one] at he
  calc
    _ = 1/(RatFunc.eval f a u) := (eq_div_iff hn).mpr he.symm
    _ = _ := one_div _

lemma ev_div (u v : RatFunc K) : ∀ᶠ a in cofinite,
    RatFunc.eval f a (u/v)=RatFunc.eval f a u/RatFunc.eval f a v := by
  filter_upwards [ev_mul f u v⁻¹,ev_inv f v] with a hm hi
  rwa [div_eq_mul_inv,div_eq_mul_inv,← hi]

lemma ev_pow (u : RatFunc K) (n : ℕ) : ∀ᶠ a in cofinite,
    RatFunc.eval f a (u^n)=RatFunc.eval f a u^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    filter_upwards [ih,ev_mul f (u^n) u] with a hn hm
    rw [pow_succ,pow_succ,hm,hn]

lemma ev_zpow (u : RatFunc K) (m : ℤ) : ∀ᶠ a in cofinite,
    RatFunc.eval f a (u^m)=RatFunc.eval f a u^m := by
  cases m with
  | ofNat n => simpa using ev_pow f u n
  | negSucc n =>
    filter_upwards [ev_pow f u (n+1),ev_inv f (u^(n+1))] with a hp hi
    simpa only [zpow_negSucc,←hp] using hi

lemma ev_monomial (t : K) (m : ℤ) : ∀ᶠ a in cofinite,
    RatFunc.eval f a (RatFunc.C t*RatFunc.X^m)=f t*a^m := by
  filter_upwards [ev_zpow f (RatFunc.X:RatFunc K) m,ev_mul f (RatFunc.C t) (RatFunc.X^m)] with a hp hm
  rw [hm,hp,RatFunc.eval_C,RatFunc.eval_X]

lemma ev_ne {u v : RatFunc K} (h : u≠v) :
    ∀ᶠ a in cofinite, RatFunc.eval f a u≠RatFunc.eval f a v := by
  filter_upwards [ev_add f (u-v) v,nonzero f (sub_ne_zero.mpr h)] with a ha hn
  rw [sub_add_cancel] at ha
  intro he
  exact hn (by linear_combination he - ha)

end Erdos1082Specialize
end
end

section
/- Algebraic specialization of rank-one distance-curve incidences. -/
open Filter Classical
open scoped Pointwise
noncomputable section
namespace Erdos1082Specialize

lemma proj_relation {L : Type} [Field L] [Infinite L] (σ : L→+*ℂ) {ι : Type*}
    (Z W : ι→L) (a b k c d : ℂ) (ha : a≠0) (hb : b≠0) (hk : k≠0) (hc : c≠0) (hd : d≠0)
    (he : ∀i, c*σ (W i)+d/σ (W i)=a/σ (Z i)+b*σ (Z i)+k) :
    ∃ A B K C D : L, A≠0 ∧ B≠0 ∧ K≠0 ∧ C≠0 ∧ D≠0 ∧
    ∀i, C*W i+D/W i=A/Z i+B*Z i+K := by
  classical
  letI := σ.toAlgebra
  let M : Finset ℂ := ({a,b,k,c,d} : Finset ℂ).erase 0
  obtain ⟨F,hF⟩ := Module.exists_dual_forall_apply_ne_zero (K:=L) (fun q : M => q.1)
    (fun q => (Finset.mem_erase.mp q.2).1)
  have mf (x : ℂ) (r : L) : F (x*σ r)=F x*r := by
    rw [mul_comm x]; change F (r • x)=_; rw [F.map_smul,smul_eq_mul,mul_comm]
  have df (x : ℂ) (r : L) : F (x/σ r)=F x/r := by
    rw [div_eq_mul_inv,← map_inv₀,mf,div_eq_mul_inv]
  refine ⟨F a,F b,F k,F c,F d,hF ⟨a,by simp [M,ha]⟩,hF ⟨b,by simp [M,hb]⟩,
    hF ⟨k,by simp [M,hk]⟩,hF ⟨c,by simp [M,hc]⟩,hF ⟨d,by simp [M,hd]⟩,?_⟩
  intro i
  simpa only [map_add,mf,df] using congrArg F (he i)

lemma exists_torsion_eventually {P : ℂ→Prop} (h : ∀ᶠ ξ in cofinite,P ξ) :
    ∃ ξ : Circle, IsOfFinOrder ξ ∧ P (ξ:ℂ) := by
  let root (n : ℕ) := Complex.exp (2*Real.pi*Complex.I/(n+1:ℕ))
  have primitive (n : ℕ) : IsPrimitiveRoot (root n) (n+1) := Complex.isPrimitiveRoot_exp _ (by omega)
  have inj : Function.Injective root := by
    intro m n he
    have em := (primitive m).eq_orderOf
    have en := (primitive n).eq_orderOf
    rw [he] at em
    omega
  have he : ∀ᶠ n in cofinite, P (root n) := inj.tendsto_cofinite h
  obtain ⟨n,hn⟩ := he.exists
  let ξ : Circle := ⟨root n,mem_sphere_zero_iff_norm.mpr ((primitive n).norm'_eq_one (by omega))⟩
  refine ⟨ξ,?_,hn⟩
  apply isOfFinOrder_iff_pow_eq_one.mpr
  exact ⟨n+1,by omega,Subtype.ext (by change root n^(n+1)=1; exact (primitive n).pow_eq_one)⟩

lemma torsion_incidence {ι : Type*} [Fintype ι] (Z W : ι→Circle) (iz : Function.Injective Z)
    (hz : ∀i, IsOfFinOrder (Z i)) (hw : ∀i, IsOfFinOrder (W i))
    (a b k c d : ℂ) (ha : a≠0) (hb : b≠0) (hk : k≠0) (hc : c≠0) (hd : d≠0)
    (he : ∀i, c*(W i:ℂ)+d/(W i:ℂ)=a/(Z i:ℂ)+b*(Z i:ℂ)+k) : Fintype.card ι≤36 := by
  classical
  let Q := Finset.univ.image Z ∪ Finset.univ.image W
  have finite (q : Circle) (hq : q∈Q) : IsOfFinOrder q := by
    rcases Finset.mem_union.mp hq with h|h
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h; exact hz i
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h; exact hw i
  let n := ∏ q∈Q, orderOf q
  have hn : 0<n := Finset.prod_pos (fun q hq => (finite q hq).orderOf_pos)
  let H := (powMonoidHom (α:=Circle) n).ker
  have heH (z : Circle) : z∈H ↔ z^n=1 := Iff.rfl
  have inc : (Q:Set Circle)⊆(H:Set Circle) := by
    intro q hq
    exact (heH q).mpr (orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_prod_of_mem orderOf hq))
  have hfin : (H:Set Circle).Finite := by
    have hh := (Polynomial.nthRoots n (1:ℂ)).toFinset.finite_toSet
    apply (hh.preimage Circle.coe_injective.injOn).subset
    intro z hz
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_nthRoots hn).mpr
    exact congrArg ((↑):Circle→ℂ) ((heH z).mp hz)
  let T := hfin.toFinset
  have hT : (H:Set Circle)=T := hfin.coe_toFinset.symm
  have memT (q : Circle) (hq : q∈Q) : q∈T := hfin.mem_toFinset.mpr (inc hq)
  have bound := Erdos1082Uniform.all_torsion_points T H hT a b k c d ha hb hk hc hd
    (Finset.univ.image Z) (fun q hq => memT q (Finset.mem_union_left _ hq)) (by
      intro z h
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
      exact ⟨W i,memT _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))),he i⟩)
  simpa [Finset.card_image_of_injective _ iz] using bound
end Erdos1082Specialize
end
end

section
/- The uniform torsion-point bound specializes to one transcendental parameter. -/
open Filter Classical
noncomputable section
namespace Erdos1082Specialize

lemma row_eval {K : Type} [Field K] (f : K→+*ℂ) (Z W A B K₀ C D : RatFunc K)
   (he : C*W+D/W=A/Z+B*Z+K₀) :
    ∀ᶠ x in cofinite, RatFunc.eval f x C*RatFunc.eval f x W+RatFunc.eval f x D/RatFunc.eval f x W=
    RatFunc.eval f x A/RatFunc.eval f x Z+RatFunc.eval f x B*RatFunc.eval f x Z+RatFunc.eval f x K₀ := by
  filter_upwards [ev_add f (C*W) (D/W),ev_mul f C W,ev_div f D W,
    ev_add f (A/Z+B*Z) K₀,ev_add f (A/Z) (B*Z),ev_div f A Z,ev_mul f B Z] with x e₁ e₂ e₃ e₄ e₅ e₆ e₇
  rw [←e₂,←e₃,←e₁,←e₆,←e₇,←e₅,←e₄,he]

theorem monomial_curve {K : Type} [Field K] [Infinite K] (f : K→+*ℂ) (σ : RatFunc K→+*ℂ)
    {ι : Type*} [Fintype ι] (U V : ι→K) (u v : ι→Circle) (r s : ι→ℤ)
    (hu : ∀i, f (U i)=(u i:ℂ)) (hv : ∀i, f (V i)=(v i:ℂ))
    (hut : ∀i, IsOfFinOrder (u i)) (hvt : ∀i, IsOfFinOrder (v i))
    (a b k c d : ℂ) (ha : a≠0) (hb : b≠0) (hk : k≠0) (hc : c≠0) (hd : d≠0) :
    let Z := fun i => RatFunc.C (U i)*RatFunc.X^(r i)
    let W := fun i => RatFunc.C (V i)*RatFunc.X^(s i)
    Function.Injective (fun i => σ (Z i)) →
    (∀i, c*σ (W i)+d/σ (W i)=a/σ (Z i)+b*σ (Z i)+k) → Fintype.card ι≤36 := by
  classical
  intro Z W iz he
  letI : Infinite (RatFunc K) := Infinite.of_injective (RatFunc.C : K→+*RatFunc K) (RatFunc.C : K→+*RatFunc K).injective
  obtain ⟨A,B,K₀,C,D,hA,hB,hK,hC,hD,hrow⟩ := proj_relation σ Z W a b k c d ha hb hk hc hd he
  have eZ : ∀ᶠ x in cofinite, ∀i,RatFunc.eval f x (Z i)=(u i:ℂ)*x^(r i) :=
    eventually_all.mpr (fun i => by simpa [Z,hu i] using ev_monomial f (U i) (r i))
  have eW : ∀ᶠ x in cofinite, ∀i,RatFunc.eval f x (W i)=(v i:ℂ)*x^(s i) :=
    eventually_all.mpr (fun i => by simpa [W,hv i] using ev_monomial f (V i) (s i))
  have eR := eventually_all.mpr (fun i => row_eval f (Z i) (W i) A B K₀ C D (hrow i))
  have eI : ∀ᶠ x in cofinite, Function.Injective (fun i => RatFunc.eval f x (Z i)) := by
    apply eventually_all.mpr; intro i
    apply eventually_all.mpr; intro j
    by_cases e : i=j
    · exact Eventually.of_forall fun _ _ => e
    have e' : Z i≠Z j := fun h => e (iz (congrArg σ h))
    filter_upwards [ev_ne f e'] with x hx
    exact fun hh => (hx hh).elim
  have all := (nonzero f hA).and ((nonzero f hB).and ((nonzero f hK).and ((nonzero f hC).and
    ((nonzero f hD).and (eZ.and (eW.and (eR.and eI)))))))
  obtain ⟨ξ,hξ,hA,hB,hK,hC,hD,hZ,hW,hR,hI⟩ := exists_torsion_eventually all
  let X := fun i => u i*ξ^(r i)
  let Y := fun i => v i*ξ^(s i)
  have ex (i) : (X i:ℂ)=RatFunc.eval f (ξ:ℂ) (Z i) := by
    rw [hZ]; dsimp only [X]; rw [Circle.coe_mul,Circle.coe_zpow]
  have ey (i) : (Y i:ℂ)=RatFunc.eval f (ξ:ℂ) (W i) := by
    rw [hW]; dsimp only [Y]; rw [Circle.coe_mul,Circle.coe_zpow]
  have iX : Function.Injective X := by
    intro i j h; apply hI; exact (ex i).symm.trans ((congrArg ((↑):Circle→ℂ) h).trans (ex j))
  exact torsion_incidence X Y iX
    (fun i => (CommGroup.torsion Circle).mul_mem (hut i) ((CommGroup.torsion Circle).zpow_mem hξ _))
    (fun i => (CommGroup.torsion Circle).mul_mem (hvt i) ((CommGroup.torsion Circle).zpow_mem hξ _))
    _ _ _ _ _ hA hB hK hC hD (fun i => by simpa only [ey,ex] using hR i)

end Erdos1082Specialize
end
end

section
/- A rank-one curve with a transcendental circle generator has at most 36 projected incidences. -/
open Classical Polynomial
open scoped Pointwise
noncomputable section
namespace Erdos1082Specialize

lemma torsion_algebraic {z : Circle} (h : IsOfFinOrder z) : IsAlgebraic ℚ (z:ℂ) := by
  obtain ⟨n,hn,he⟩ := h.exists_pow_eq_one
  refine ⟨Polynomial.X^n-Polynomial.C 1,Polynomial.X_pow_sub_C_ne_zero hn 1,?_⟩
  have eq : (z:ℂ)^n=1 := congrArg ((↑):Circle→ℂ) he
  simp [eq]

theorem transcendental_curve {ι : Type*} [Fintype ι] (g : Circle) (hg : Transcendental ℚ (g:ℂ))
    (Z W : ι→Circle) (iz : Function.Injective Z)
    (hz : ∀i,∃j : ℤ, IsOfFinOrder (Z i/g^j)) (hw : ∀i,∃j : ℤ, IsOfFinOrder (W i/g^j))
    (a b k c d : ℂ) (ha : a≠0) (hb : b≠0) (hk : k≠0) (hc : c≠0) (hd : d≠0)
    (he : ∀i, c*(W i:ℂ)+d/(W i:ℂ)=a/(Z i:ℂ)+b*(Z i:ℂ)+k) : Fintype.card ι≤36 := by
  classical
  let K := algebraicClosure ℚ ℂ
  let f : K→+*ℂ := K.val.toRingHom
  let E := RatFunc.algEquivOfTranscendental (g:ℂ) hg.algebraicClosure
  let S := IntermediateField.adjoin K {(g:ℂ)}
  let σ : RatFunc K →+*ℂ := S.val.toRingHom.comp E.toRingHom
  have sC (q : K) : σ (RatFunc.C q)=f q := congrArg ((↑):S→ℂ) (E.commutes q)
  have sX : σ RatFunc.X=(g:ℂ) := RatFunc.algEquivOfTranscendental_X (g:ℂ) hg.algebraicClosure
  choose r hr using hz
  choose s hs using hw
  let u := fun i => Z i/g^(r i)
  let v := fun i => W i/g^(s i)
  let U := fun i => (⟨(u i:ℂ),mem_algebraicClosure_iff.mpr (torsion_algebraic (hr i))⟩:K)
  let V := fun i => (⟨(v i:ℂ),mem_algebraicClosure_iff.mpr (torsion_algebraic (hs i))⟩:K)
  have ez (i) : σ (RatFunc.C (U i)*RatFunc.X^(r i))=(Z i:ℂ) := by
    rw [map_mul,map_zpow₀,sC,sX]
    change (((Z i/g^(r i):Circle):ℂ))*(g:ℂ)^(r i)=(Z i:ℂ)
    rw [Circle.coe_div,Circle.coe_zpow,div_mul_cancel₀ _ (zpow_ne_zero _ (Circle.coe_ne_zero g))]
  have ew (i) : σ (RatFunc.C (V i)*RatFunc.X^(s i))=(W i:ℂ) := by
    rw [map_mul,map_zpow₀,sC,sX]
    change (((W i/g^(s i):Circle):ℂ))*(g:ℂ)^(s i)=(W i:ℂ)
    rw [Circle.coe_div,Circle.coe_zpow,div_mul_cancel₀ _ (zpow_ne_zero _ (Circle.coe_ne_zero g))]
  apply monomial_curve f σ U V u v r s (fun _ => rfl) (fun _ => rfl) hr hs a b k c d ha hb hk hc hd
  · intro i j e; exact iz (Circle.coe_injective ((ez i).symm.trans (e.trans (ez j))))
  · intro i; simpa only [ew,ez] using he i

end Erdos1082Specialize
end
end

section
/- The ratios of a sufficiently large circle in a critical configuration are algebraic. -/
open Classical
open scoped Pointwise
noncomputable section
namespace Erdos1082Cover

lemma match_count (A : Finset ℂ) (S : Finset Circle) (hSA : ∀z∈S,(z:ℂ)∈A)
    (p : ℂ) (hpA : p∈A) (hp : p≠0) (hn : ‖p‖≠1) :
    2*S.card≤2*distinctDistances A+1+(S.filter fun z : Circle => dist p (z:ℂ)∈distanceSet S).card := by
  classical
  let U := S.filter fun z : Circle => dist p (z:ℂ)∉distanceSet S
  let V := S.filter fun z : Circle => dist p (z:ℂ)∈distanceSet S
  let D := distanceSet A\distanceSet S
  have SA : distanceSet S⊆distanceSet A := by
    intro d hd
    obtain ⟨⟨x,y⟩,hpair,eq⟩ := Finset.mem_image.mp hd
    obtain ⟨hx,hy,he⟩ := Finset.mem_offDiag.mp hpair
    exact Finset.mem_image.mpr ⟨((x:ℂ),(y:ℂ)),Finset.mem_offDiag.mpr ⟨hSA x hx,hSA y hy,Circle.coe_injective.ne he⟩,eq⟩
  have hmap (z : Circle) (hz : z∈U) : dist p (z:ℂ)∈D := by
    obtain ⟨hz,hz'⟩ := Finset.mem_filter.mp hz
    have he : p≠(z:ℂ) := fun eq => hn (eq ▸ Circle.norm_coe z)
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨(p,(z:ℂ)),Finset.mem_offDiag.mpr ⟨hpA,hSA z hz,he⟩,rfl⟩,hz'⟩
  have ub : U.card≤2*D.card := by
    by_contra! h
    obtain ⟨d,_,hd⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmap
      (show D.card*2<U.card by omega)
    exact (not_lt_of_ge (OMA.R_Erdos1082_erdos_1082_parts_i_R1.circle_fibers U p hp d)) hd
  have hsum : V.card+U.card=S.card := Finset.card_filter_add_card_filter_not _
  have hD := Finset.card_sdiff_add_card_eq_card SA
  have hS := OMA.R_Erdos1082_erdos_1082_parts_i_R1.circle_quotient_card S
  change D.card+(distanceSet S).card=(distanceSet A).card at hD
  change (S/S).card≤2*(distanceSet S).card+1 at hS
  have d := Finset.card_le_card_div_self (s:=S)
  change 2*S.card≤2*(distanceSet A).card+1+V.card
  omega

lemma transcendental_norm_bound {ι : Type*} [Fintype ι] (g : Circle) (hg : Transcendental ℚ (g:ℂ))
    (Z W : ι→Circle) (iz : Function.Injective Z)
    (hZ : ∀i, ∃j : ℤ,IsOfFinOrder (Z i/g^j)) (hW : ∀i, ∃j : ℤ,IsOfFinOrder (W i/g^j))
    (c p q : ℂ) (hc : c≠0) (hp : p≠0) (hq : q≠0) (hn : ‖p‖≠‖q‖)
    (he : ∀i, ‖c+q*(W i:ℂ)‖=‖c+p*(Z i:ℂ)‖) : Fintype.card ι≤36 := by
  have hnorm : (Complex.normSq p:ℂ)≠(Complex.normSq q:ℂ) := by
    intro he
    have hh := Complex.ofReal_injective he
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at hh
    exact hn (by nlinarith [norm_nonneg p,norm_nonneg q])
  apply Erdos1082Specialize.transcendental_curve g hg Z W iz hZ hW (c*starRingEnd ℂ p) (starRingEnd ℂ c*p)
    ((Complex.normSq p:ℂ)-(Complex.normSq q:ℂ)) (starRingEnd ℂ c*q) (c*starRingEnd ℂ q)
    (mul_ne_zero hc ((_root_.map_ne_zero _).mpr hp)) (mul_ne_zero ((_root_.map_ne_zero _).mpr hc) hp) (sub_ne_zero.mpr hnorm)
    (mul_ne_zero ((_root_.map_ne_zero _).mpr hc) hq) (mul_ne_zero hc ((_root_.map_ne_zero _).mpr hq))
  intro i
  have hh := congrArg (fun t : ℝ => ((t^2:ℝ):ℂ)) (he i)
  rw [Erdos1082Uniform.orbit_norm,Erdos1082Uniform.orbit_norm] at hh
  linear_combination hh

theorem rich_ratios_algebraic (A : Finset ℂ) (S : Finset Circle)
    (hSA : ∀z∈S,(z:ℂ)∈A) (p : ℂ) (hpA : p∈A) (hp : p≠0) (hn : ‖p‖≠1)
    (hsize : 2*distinctDistances A+37<2*S.card) :
    ∀w∈S/S, IsAlgebraic ℚ (w:ℂ) := by
  classical
  let V := S.filter fun z : Circle => dist p (z:ℂ)∈distanceSet S
  have count := match_count A S hSA p hpA hp hn
  change 2*S.card≤2*distinctDistances A+1+V.card at count
  have hV : 36<V.card := by omega
  obtain ⟨g,hg⟩ := Erdos1082Projection.half_circle_rank A S hSA (by omega)
  by_cases alg : IsAlgebraic ℚ (g:ℂ)
  · intro w hw
    obtain ⟨j,hj⟩ := hg w hw
    have hrat := Erdos1082Specialize.torsion_algebraic hj
    let K := algebraicClosure ℚ ℂ
    have h₁ : (((w/g^j:Circle):ℂ))∈K := mem_algebraicClosure_iff.mpr hrat
    have h₂ : (g:ℂ)^j∈K := K.toSubfield.zpow_mem (mem_algebraicClosure_iff.mpr alg) j
    apply mem_algebraicClosure_iff.mp
    have hh := K.mul_mem h₁ h₂
    rwa [Circle.coe_div,Circle.coe_zpow,div_mul_cancel₀ _ (zpow_ne_zero _ (Circle.coe_ne_zero g))] at hh
  exfalso
  have ne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a,ha⟩ := ne
  let Z := fun z : V => a/z.1
  have zr (z : V) : Z z∈S/S := Finset.mem_div.mpr ⟨a,ha,z.1,(Finset.mem_filter.mp z.2).1,rfl⟩
  have wit (z : V) : ∃w∈S/S, ‖(-1:ℂ)+(w:ℂ)‖=dist p (z.1:ℂ) := by
    obtain ⟨⟨x,y⟩,hpair,eq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp z.2).2
    obtain ⟨hx,hy,_⟩ := Finset.mem_offDiag.mp hpair
    exact ⟨x/y,Finset.mem_div.mpr ⟨x,hx,y,hy,rfl⟩,(chord_eq x y).symm.trans eq⟩
  choose W hw he using wit
  have iz : Function.Injective Z := fun _ _ h => Subtype.ext (div_right_injective (b:=a) h)
  have hlim := transcendental_norm_bound g alg Z W iz (fun i => hg _ (zr i)) (fun i => hg _ (hw i))
    (-1) (p/(a:ℂ)) 1 (by norm_num) (div_ne_zero hp (Circle.coe_ne_zero a)) one_ne_zero
    (by simpa [norm_div,Circle.norm_coe] using hn) (fun i => by
      rw [one_mul,he i]; exact off_eq p i.1 a)
  rw [Fintype.card_coe] at hlim
  omega
end Erdos1082Cover
end
end

section
/- Reconstruct a normalized point using three internal chord lengths. -/
open Classical
open scoped Pointwise
noncomputable section
namespace Erdos1082Cover
lemma match_count_external (A : Finset ℂ) (S : Finset Circle) (hSA : ∀z∈S,(z:ℂ)∈A)
    (p : ℂ) (hpA : p∈A) (hp : p≠0) (hn : ∀z∈S, p≠(z:ℂ)) :
    2*S.card≤2*distinctDistances A+1+(S.filter fun z : Circle => dist p (z:ℂ)∈distanceSet S).card := by
  classical
  let U := S.filter fun z : Circle => dist p (z:ℂ)∉distanceSet S
  let V := S.filter fun z : Circle => dist p (z:ℂ)∈distanceSet S
  let D := distanceSet A\distanceSet S
  have SA : distanceSet S⊆distanceSet A := by
    intro d hd
    obtain ⟨⟨x,y⟩,hpair,eq⟩ := Finset.mem_image.mp hd
    obtain ⟨hx,hy,he⟩ := Finset.mem_offDiag.mp hpair
    exact Finset.mem_image.mpr ⟨((x:ℂ),(y:ℂ)),Finset.mem_offDiag.mpr ⟨hSA x hx,hSA y hy,Circle.coe_injective.ne he⟩,eq⟩
  have hmap (z : Circle) (hz : z∈U) : dist p (z:ℂ)∈D := by
    obtain ⟨hz,hz'⟩ := Finset.mem_filter.mp hz
    have he : p≠(z:ℂ) := hn z hz
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨(p,(z:ℂ)),Finset.mem_offDiag.mpr ⟨hpA,hSA z hz,he⟩,rfl⟩,hz'⟩
  have ub : U.card≤2*D.card := by
    by_contra! h
    obtain ⟨d,_,hd⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmap
      (show D.card*2<U.card by omega)
    exact (not_lt_of_ge (OMA.R_Erdos1082_erdos_1082_parts_i_R1.circle_fibers U p hp d)) hd
  have hsum : V.card+U.card=S.card := Finset.card_filter_add_card_filter_not _
  have hD := Finset.card_sdiff_add_card_eq_card SA
  have hS := OMA.R_Erdos1082_erdos_1082_parts_i_R1.circle_quotient_card S
  change D.card+(distanceSet S).card=(distanceSet A).card at hD
  change (S/S).card≤2*(distanceSet S).card+1 at hS
  have d := Finset.card_le_card_div_self (s:=S)
  change 2*S.card≤2*(distanceSet A).card+1+V.card
  omega

lemma norm_form (p : ℂ) (z a : Circle) :
    ((dist p (z:ℂ)^2:ℝ):ℂ)=1+(Complex.normSq (p/(a:ℂ)):ℂ)
      -(p/(a:ℂ))/((z/a:Circle):ℂ)-(starRingEnd ℂ (p/(a:ℂ)))*((z/a:Circle):ℂ) := by
  let q := p/(a:ℂ)
  rw [off_eq p z a,Erdos1082Uniform.orbit_norm]
  change (Complex.normSq (-1):ℂ)+(Complex.normSq q:ℂ)+(starRingEnd ℂ (-1)*q)*((a:ℂ)/(z:ℂ))+
    (-1*starRingEnd ℂ q)/((a:ℂ)/(z:ℂ))=1+(Complex.normSq q:ℂ)-q/((z:ℂ)/(a:ℂ))-
    (starRingEnd ℂ q)*((z:ℂ)/(a:ℂ))
  simp only [map_neg,map_one,Complex.normSq_neg,Complex.normSq_one,Complex.ofReal_one]
  field_simp [Circle.coe_ne_zero a,Circle.coe_ne_zero z]
  <;> ring

lemma recover_three (K : IntermediateField ℚ ℂ) (p q M a b c u v w : ℂ)
    (ha : a∈K) (hb : b∈K) (hc : c∈K) (hu : u∈K) (hv : v∈K) (hw : w∈K)
    (ha0 : a≠0) (hb0 : b≠0) (hc0 : c≠0) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (eu : u=M-p/a-q*a) (ev : v=M-p/b-q*b) (ew : w=M-p/c-q*c) : p∈K := by
  let L := (u-v)/(b-a)-(u-w)/(c-a)
  have hL : L∈K := K.sub_mem (K.div_mem (K.sub_mem hu hv) (K.sub_mem hb ha))
    (K.div_mem (K.sub_mem hu hw) (K.sub_mem hc ha))
  have eq : p=L*a*b*c/(b-c) := by
    dsimp [L]; rw [eu,ev,ew]
    field_simp [ha0,hb0,hc0,sub_ne_zero.mpr hab.symm,sub_ne_zero.mpr hac.symm,sub_ne_zero.mpr hbc]
    <;> ring
  rw [eq]
  exact K.div_mem (K.mul_mem (K.mul_mem (K.mul_mem hL ha) hb) hc) (K.sub_mem hb hc)

lemma chord_squared (x y : Circle) :
    ((dist x y^2:ℝ):ℂ)=2-((x/y:Circle):ℂ)-((x/y:Circle):ℂ)⁻¹ := by
  have h := Erdos1082Uniform.orbit_norm (-1) 1 (x/y)
  rw [chord_eq]
  let t : ℂ := (x/y:Circle)
  change ((‖(-1:ℂ)+t‖^2:ℝ):ℂ)=2-t-t⁻¹
  change ((‖(-1:ℂ)+1*t‖^2:ℝ):ℂ)=(Complex.normSq (-1):ℂ)+(Complex.normSq 1:ℂ)+
    (starRingEnd ℂ (-1)*1)*t+(-1*starRingEnd ℂ 1)/t at h
  simp only [one_mul,mul_one,Complex.normSq_neg,Complex.normSq_one,Complex.ofReal_one,map_neg,map_one] at h
  rw [h]
  ring

lemma coordinates_in_field (A : Finset ℂ) (S : Finset Circle)
    (hSA : ∀z∈S,(z:ℂ)∈A) (K : IntermediateField ℚ ℂ)
    (ratio : ∀w∈S/S,(w:ℂ)∈K) (hsize : 2*distinctDistances A+3<2*S.card)
    (a : Circle) (ha : a∈S) : ∀p∈A,p/(a:ℂ)∈K := by
  classical
  have zr (z : Circle) (hz : z∈S) : ((z/a:Circle):ℂ)∈K :=
    ratio _ (Finset.mem_div.mpr ⟨z,hz,a,ha,rfl⟩)
  have ds (d : ℝ) (hd : d∈distanceSet S) : ((d^2:ℝ):ℂ)∈K := by
    obtain ⟨⟨x,y⟩,hp,e⟩ := Finset.mem_image.mp hd
    obtain ⟨hx,hy,_⟩ := Finset.mem_offDiag.mp hp
    have h := ratio _ (Finset.mem_div.mpr ⟨x,hx,y,hy,rfl⟩)
    change dist x y=d at e
    rw [←e,chord_squared]
    exact K.sub_mem (K.sub_mem (by exact_mod_cast K.natCast_mem 2) h) (K.inv_mem h)
  intro p hp
  by_cases hzero : p=0
  · simp [hzero]
  by_cases hmem : ∃z∈S,p=(z:ℂ)
  · obtain ⟨z,hz,rfl⟩ := hmem; exact zr z hz
  have hn (z : Circle) (hz : z∈S) : p≠(z:ℂ) := fun e => hmem ⟨z,hz,e⟩
  let V := S.filter fun z : Circle => dist p (z:ℂ)∈distanceSet S
  have count := match_count_external A S hSA p hp hzero hn
  change 2*S.card≤2*distinctDistances A+1+V.card at count
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := Finset.two_lt_card_iff.mp (show 2<V.card by omega)
  have neq {x y : Circle} (h:x≠y) : ((x/a:Circle):ℂ)≠((y/a:Circle):ℂ) :=
    fun e => h ((div_left_injective (b:=a)) (Circle.coe_injective e))
  have anchor {z : Circle} (hz : z∈V) : ((z/a:Circle):ℂ)∈K := zr _ (Finset.mem_filter.mp hz).1
  have length {z : Circle} (hz : z∈V) : ((dist p (z:ℂ)^2:ℝ):ℂ)∈K := ds _ (Finset.mem_filter.mp hz).2
  exact recover_three K _ _ _ _ _ _ _ _ _
    (anchor hx) (anchor hy) (anchor hz) (length hx) (length hy) (length hz)
    (Circle.coe_ne_zero _) (Circle.coe_ne_zero _) (Circle.coe_ne_zero _) (neq hxy) (neq hxz) (neq hyz)
    (norm_form p x a) (norm_form p y a) (norm_form p z a)

theorem rich_coordinates_algebraic (A : Finset ℂ) (S : Finset Circle)
    (hSA : ∀z∈S,(z:ℂ)∈A) (p : ℂ) (hpA : p∈A) (hp : p≠0) (hn : ‖p‖≠1)
    (hsize : 2*distinctDistances A+37<2*S.card) (a : Circle) (ha : a∈S) :
    ∀x∈A, IsAlgebraic ℚ (x/(a:ℂ)) := by
  have h := rich_ratios_algebraic A S hSA p hpA hp hn hsize
  have coord := coordinates_in_field A S hSA (algebraicClosure ℚ ℂ)
    (fun w hw => mem_algebraicClosure_iff.mpr (h w hw)) (by omega) a ha
  exact fun x hx => mem_algebraicClosure_iff.mp (coord x hx)
end Erdos1082Cover
end
end

section
/- A large circle forces an algebraic realization of the entire critical planar configuration by similarity. -/
open Classical EuclideanGeometry
noncomputable section
namespace Erdos1082Cover
open OMA.R_Erdos1082_erdos_1082_parts_i_R1

theorem planar_algebraic (A B : Finset ℝ²) (c p : ℝ²) (r : ℝ) (hBA : B⊆A)
    (hsize : 2*distinctDistances A+37<2*B.card)
    (hC : ∀x∈B,dist x c=r) (hp : p∈A) (hpc : p≠c) (hpr : dist p c≠r) :
    ∃ f : ℝ²→ℂ, ∃ s : ℝ, 0<s ∧ (∀x y,dist (f x) (f y)=s*dist x y) ∧
      ∀x∈A,IsAlgebraic ℚ (f x) := by
  classical
  have hcard : 2<B.card := by omega
  have hsub : ¬ B ⊆ {c} := by
    intro h; have hh : B.card ≤ 1 := (Finset.card_le_card h).trans_eq (Finset.card_singleton c); omega
  obtain ⟨x,hx,hxc⟩ := Finset.not_subset.mp hsub
  have hr : 0 < r := (dist_pos.mpr (show x ≠ c by simpa using hxc)).trans_eq (hC x hx)
  let E := Complex.orthonormalBasisOneI.repr.symm
  let F (x : ℝ²) := E (x-c) / (r : ℂ)
  have hdist (x y : ℝ²) : dist (F x) (F y) = dist x y / r := by
    rw [dist_eq_norm]; dsimp only [F]
    rw [←sub_div,norm_div,←map_sub,E.norm_map,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,
      show (x-c)-(y-c) = x-y by abel,dist_eq_norm]
  have hFc : F c = 0 := by simp [F]
  have hnorm (x : ℝ²) : ‖F x‖ = dist x c / r := by rw [←dist_zero_right,← hFc,hdist]
  have hinj : Function.Injective F := by
    intro x y h
    have hxy := hdist x y
    rw [h,dist_self] at hxy
    exact dist_eq_zero.mp ((div_eq_zero_iff.mp hxy.symm).resolve_right hr.ne')
  let G (x : B) : Circle := ⟨F x.1, mem_sphere_zero_iff_norm.mpr (by rw [hnorm,hC _ x.2,div_self hr.ne'])⟩
  let S := B.attach.image G
  let D := (distanceSet A).image (· / r)
  have hG : Function.Injective G := by
    intro u v h
    exact Subtype.ext (hinj (congrArg ((↑) : Circle → ℂ) h))
  have hSc : S.card = B.card := by dsimp [S]; rw [Finset.card_image_of_injective _ hG,Finset.card_attach]
  have hDc : D.card = distinctDistances A := by
    apply Finset.card_image_of_injective
    exact fun _ _ h => (div_left_inj' hr.ne').mp h
  let A' := A.image F
  have hs : S.Nonempty := Finset.card_pos.mp (by omega)
  have SA (z : Circle) (hz : z∈S) : (z:ℂ)∈A' := by
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image_of_mem F (hBA x.2)
  have hpA : F p∈A' := Finset.mem_image_of_mem F hp
  have hDsub : distanceSet A'⊆D := by
    intro d hd
    obtain ⟨⟨x,y⟩,hpair,heq⟩ := Finset.mem_image.mp hd
    obtain ⟨hx,hy,he⟩ := Finset.mem_offDiag.mp hpair
    obtain ⟨x,hxA,ex⟩ := Finset.mem_image.mp hx
    obtain ⟨y,hyA,ey⟩ := Finset.mem_image.mp hy
    change F x=_ at ex
    change F y=_ at ey
    change dist _ _=d at heq
    rw [← ex, ← ey] at heq
    change _≠_ at he
    rw [← ex, ← ey] at he
    have exy : x≠y := fun e => he (congrArg F e)
    exact Finset.mem_image.mpr ⟨dist x y,dist_mem hxA hyA exy,(hdist x y).symm.trans heq⟩
  have hdistA : distinctDistances A'≤distinctDistances A := (Finset.card_le_card hDsub).trans_eq hDc
  obtain ⟨a,ha⟩ := hs
  have alg := rich_coordinates_algebraic A' S SA (F p) hpA
    (fun he => hpc (hinj (he.trans hFc.symm)))
    (by rw [hnorm]; exact fun he => hpr ((div_eq_one_iff_eq hr.ne').mp he))
    (by omega) a ha
  refine ⟨fun x => F x/(a:ℂ),r⁻¹,inv_pos.mpr hr,?_,fun x hx => alg _ (Finset.mem_image_of_mem F hx)⟩
  intro x y
  rw [dist_eq_norm,←sub_div,norm_div,Circle.norm_coe,div_one,←dist_eq_norm,hdist,div_eq_inv_mul]

theorem critical_algebraic_or_circle_bound (A : Finset ℝ²) (hn : NonTrilinear (A:Set ℝ²))
    (hA : A.card=2*distinctDistances A+2) :
    (∀c : ℝ²,∀r : ℝ, 2*(A.filter fun x => dist x c=r).card≤A.card+35) ∨
    (∃f : ℝ²→ℂ,∃s : ℝ, 0<s ∧ (∀x y,dist (f x) (f y)=s*dist x y) ∧ ∀x∈A, IsAlgebraic ℚ (f x)) := by
  classical
  by_cases h : ∀c : ℝ²,∀r : ℝ,2*(A.filter fun x => dist x c=r).card≤A.card+35
  · exact Or.inl h
  right
  push_neg at h
  obtain ⟨c,r,hB⟩ := h
  let B := A.filter fun x => dist x c=r
  by_cases hex : ∃p∈A,p≠c ∧ dist p c≠r
  · obtain ⟨p,hp,hpc,hpr⟩ := hex
    apply planar_algebraic A B c p r (Finset.filter_subset _ _) (by change A.card+35<2*B.card at hB; omega)
    · exact fun x hx => (Finset.mem_filter.mp hx).2
    · exact hp
    · exact hpc
    · exact hpr
  · have hh := all_but_one_concyclic A c r hn c (by
      intro x hx
      by_contra he
      exact hex ⟨x,Finset.mem_of_mem_erase hx,Finset.ne_of_mem_erase hx,he⟩)
    omega
end Erdos1082Cover
end
end

section
/- Fiber weights for a torsion-free quotient of a small-doubling set. -/
open Classical
open scoped Pointwise
noncomputable section
namespace Erdos1082Atom

lemma image_weights {G K:Type*} [CommGroup G] [CommGroup K] [IsMulTorsionFree K]
    (S : Finset G) (hS : S.Nonempty) (φ : G →* K) :
    (S.image φ).card*(2*S.card-(S/S).card)≤S.card ∧
      ((S/S).image φ).card*(2*S.card-(S/S).card)≤(S/S).card := by
  classical
  obtain ⟨H,T,hT,hk,hl⟩ := cover_weights S hS
  have hfinite : (H:Set G).Finite := hT ▸ T.finite_toSet
  letI : Finite H := hfinite.to_subtype
  have hker : H≤φ.ker := by
    intro x hx
    have hh := isOfFinOrder_of_finite (⟨x,hx⟩:H)
    obtain ⟨n,hn,he⟩ := hh.exists_pow_eq_one
    have e : x^n=1 := congrArg ((↑):H→G) he
    have hh' : IsOfFinOrder (φ x) := isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,by rw [←map_pow,e,map_one]⟩
    exact hh'.eq_one'
  let χ := QuotientGroup.lift H φ hker
  have bound (U : Finset G) : (U.image φ).card≤(U.image (QuotientGroup.mk' H)).card := by
    have eq : U.image φ=(U.image (QuotientGroup.mk' H)).image χ := by
      rw [Finset.image_image]
      rfl
    rw [eq]; exact Finset.card_image_le
  exact ⟨(Nat.mul_le_mul_right _ (bound S)).trans hk,(Nat.mul_le_mul_right _ (bound (S/S))).trans hl⟩

end Erdos1082Atom
end
end

section
/- Every point of a half-size circle has many circle neighbors at rational angles. -/
open Classical EuclideanGeometry
open scoped Pointwise
noncomputable section
namespace Erdos1082Atom
variable {G : Type*} [CommGroup G]

theorem torsion_neighbors (S : Finset G) {a : G} (ha:a∈S) :
    2*S.card≤(S/S).card+(S.filter (fun z => IsOfFinOrder (z/a))).card := by
  classical
  obtain ⟨H,T,hHT,hnum⟩ := atom S ⟨a,ha⟩
  have lb := fiber_lower S T H hHT hnum a ha
  have hfinite : (H:Set G).Finite := hHT ▸ T.finite_toSet
  letI : Finite H := hfinite.to_subtype
  have inc : S.filter (fun z => (QuotientGroup.mk' H) z=(QuotientGroup.mk' H) a)⊆
      S.filter (fun z => IsOfFinOrder (z/a)) := by
    intro z hz
    obtain ⟨hz,he⟩ := Finset.mem_filter.mp hz
    have h : z/a∈H := QuotientGroup.eq_iff_div_mem.mp he
    have hh := isOfFinOrder_of_finite (⟨z/a,h⟩:H)
    obtain ⟨n,hn,e⟩ := hh.exists_pow_eq_one
    exact Finset.mem_filter.mpr ⟨hz,isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,congrArg ((↑):H→G) e⟩⟩
  exact lb.trans (Nat.add_le_add_left (Finset.card_le_card inc) _)

theorem circle_torsion_neighbors (A : Finset ℂ) (S : Finset Circle) (hSA : ∀z∈S,(z:ℂ)∈A)
    {a : Circle} (ha:a∈S) : 2*S.card≤2*distinctDistances A+1+
    (S.filter fun z => IsOfFinOrder (z/a)).card := by
  classical
  have sub : distanceSet S⊆distanceSet A := by
    intro d hd
    obtain ⟨⟨x,y⟩,hpair,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hx,hy,hxy⟩ := Finset.mem_offDiag.mp hpair
    exact Finset.mem_image.mpr ⟨((x:ℂ),(y:ℂ)),Finset.mem_offDiag.mpr ⟨hSA x hx,hSA y hy,Circle.coe_injective.ne hxy⟩,rfl⟩
  have hD : distinctDistances S≤distinctDistances A := Finset.card_le_card sub
  have hh := torsion_neighbors S ha
  have hq := OMA.R_Erdos1082_erdos_1082_parts_i_R1.circle_quotient_card S
  omega
end Erdos1082Atom
end
end

section
/- Rational squared chords allow at most six roots-of-unity neighbors. -/
open Classical
open scoped Pointwise
noncomputable section
namespace Erdos1082Cover
lemma torsion_integral {z:Circle} (h : IsOfFinOrder z) : IsIntegral ℤ (z:ℂ) := by
  obtain ⟨n,hn,he⟩ := h.exists_pow_eq_one
  apply IsIntegral.of_pow hn
  have eq : (z:ℂ)^n=1 := congrArg ((↑):Circle→ℂ) he
  exact eq ▸ isIntegral_one

lemma ration_trace_orders (z : Circle) (hn : IsOfFinOrder z) (h : ∃q:ℚ,(z:ℂ)+(z:ℂ)⁻¹=(q:ℂ)) :
    z^4=1 ∨ z^6=1 := by
  have hi : IsIntegral ℤ ((z:ℂ)+(z:ℂ)⁻¹) :=
    (torsion_integral hn).add (torsion_integral ((CommGroup.torsion Circle).inv_mem hn) : IsIntegral ℤ (((z⁻¹:Circle):ℂ)))
  obtain ⟨m,hm⟩ := hi.exists_int_iff_exists_rat.mp h
  have r := congrArg Complex.re hm
  rw [Complex.add_re,←Circle.coe_inv,Circle.coe_inv_eq_conj,Complex.conj_re,Complex.intCast_re] at r
  have hh := Complex.abs_re_le_norm (z:ℂ)
  rw [Circle.norm_coe,abs_le] at hh
  have low : (-2 : ℝ) ≤ (m:ℝ) := by linarith [hh.1]
  have high : (m:ℝ) ≤ 2 := by linarith [hh.2]
  have l : (-2 : ℤ) ≤ m := by exact_mod_cast low
  have ubd : m ≤ 2 := by exact_mod_cast high
  have hs : (z:ℂ)^2+1=(m:ℂ)*(z:ℂ) := by
    have eq := congrArg (fun w : ℂ => w*(z:ℂ)) hm
    simpa [add_mul,Circle.coe_ne_zero,pow_two] using eq
  let u := (z:ℂ)
  have fourth (he : u^4=1) : z^4=1 := Subtype.ext he
  have sixth (he : u^6=1) : z^6=1 := Subtype.ext he
  change u^2+1=(m:ℂ)*u at hs
  interval_cases m
  · have fac : (u+1)^2=0 := by linear_combination hs
    have eu : u=-1 := eq_neg_of_add_eq_zero_left ((pow_eq_zero_iff (by decide)).mp fac)
    exact Or.inl (fourth (by rw [eu]; norm_num))
  · exact Or.inr (sixth (by linear_combination (u-1)*(u^3+1)*hs))
  · exact Or.inl (fourth (by linear_combination (u^2-1)*hs))
  · exact Or.inr (sixth (by linear_combination (u+1)*(u^3-1)*hs))
  · have fac : (u-1)^2=0 := by linear_combination hs
    have eu : u=1 := sub_eq_zero.mp ((pow_eq_zero_iff (by decide)).mp fac)
    exact Or.inl (fourth (by rw [eu]; norm_num))

lemma rational_chord_order {x y : Circle} (ht : IsOfFinOrder (x/y))
    (hq : ∃q:ℚ,dist x y^2=(q:ℝ)) : (x/y)^4=1 ∨ (x/y)^6=1 := by
  obtain ⟨q,eq⟩ := hq
  apply ration_trace_orders _ ht
  refine ⟨2-q,?_⟩
  have h := chord_squared x y
  rw [eq] at h
  push_cast at h ⊢
  linear_combination h

lemma nth_card (U : Finset Circle) {n : ℕ} (hn:0<n) (h : ∀z∈U,z^n=1) : U.card≤n := by
  classical
  let V := U.image (fun z : Circle => (z:ℂ))
  have sub : V⊆(Polynomial.nthRoots n (1:ℂ)).toFinset := by
    intro z hz; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_nthRoots hn).mpr (congrArg ((↑):Circle→ℂ) (h w hw)))
  have le := (Finset.card_le_card sub).trans (Multiset.toFinset_card_le _)
  have eq : V.card=U.card := Finset.card_image_of_injective _ Circle.coe_injective
  exact eq ▸ le.trans (Polynomial.card_nthRoots _ _)

lemma rational_torsion_neighbors (S : Finset Circle)
    (hr : ∀x∈S,∀y∈S,∃q:ℚ,dist x y^2=(q:ℝ)) {a:Circle} (ha:a∈S) :
    (S.filter fun z => IsOfFinOrder (z/a)).card≤6 := by
  classical
  let F := S.filter fun z => IsOfFinOrder (z/a)
  let U := F.image (·/a)
  have card : U.card=F.card := Finset.card_image_of_injective _ (div_left_injective (b:=a))
  have one : (1:Circle)∈U := Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,by simp⟩,div_self' a⟩
  have rel (x : Circle) (hx : x∈U) (y : Circle) (hy : y∈U) : (x/y)^4=1 ∨ (x/y)^6=1 := by
    obtain ⟨x,hxF,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y,hyF,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxS,xt⟩ := Finset.mem_filter.mp hxF
    obtain ⟨hyS,yt⟩ := Finset.mem_filter.mp hyF
    have nt := (CommGroup.torsion Circle).div_mem xt yt
    rw [div_div_div_cancel_right] at nt ⊢
    exact rational_chord_order nt (hr x hxS y hyS)
  have ord (u : Circle) (hu:u∈U) : u^4=1 ∨ u^6=1 := by simpa using rel u hu 1 one
  change F.card≤6
  rw [←card]
  by_cases h : ∀u∈U,u^6=1
  · exact nth_card U (by decide) h
  push_neg at h
  obtain ⟨x,hx,hx6⟩ := h
  have hx4 := (ord x hx).resolve_right hx6
  apply (nth_card U (n:=4) (by decide) ?_).trans (by decide)
  intro y hy
  rcases ord y hy with hh|hh
  · exact hh
  rcases rel x hx y hy with xy|xy
  · rw [div_pow,div_eq_one,hx4] at xy; exact xy.symm
  · rw [div_pow,div_eq_one,hh] at xy; exact (hx6 xy).elim

theorem rational_circle_bound (A : Finset ℂ) (S : Finset Circle) (hSA : ∀z∈S,(z:ℂ)∈A)
    (hr : ∀x∈S,∀y∈S,∃q:ℚ,dist x y^2=(q:ℝ)) :
    2*S.card≤2*distinctDistances A+7 := by
  classical
  by_cases h : S.Nonempty
  · obtain ⟨a,ha⟩ := h
    have h₁ := Erdos1082Atom.circle_torsion_neighbors A S hSA ha
    have h₂ := rational_torsion_neighbors S hr ha
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp h]
end Erdos1082Cover
end
end

section
/- Any three distinct points determine the rational square scale of their circumradius. -/
open Classical
noncomputable section
namespace Erdos1082Cover

lemma triangle_chords (x y z : Circle) :
    let A := dist x y^2
    let B := dist x z^2
    let C := dist y z^2
    4*A*B-(A+B-C)^2=A*B*C := by
  intro A B C
  have ea := chord_squared x y
  have eb := chord_squared x z
  have ec := chord_squared y z
  have hh : (4:ℂ)*(A:ℂ)*(B:ℂ)-((A:ℂ)+(B:ℂ)-(C:ℂ))^2=(A:ℂ)*(B:ℂ)*(C:ℂ) := by
    dsimp only [A,B,C]
    rw [ea,eb,ec]
    simp only [Circle.coe_div]
    field_simp [Circle.coe_ne_zero x,Circle.coe_ne_zero y,Circle.coe_ne_zero z]
    <;> ring
  exact_mod_cast hh

lemma rationalize_chords (S : Finset Circle) (hn : 2<S.card) (s : ℝ) (hs : 0<s)
    (h : ∀x∈S,∀y∈S,∃q:ℚ,dist x y^2=s*q) :
    ∀x∈S,∀y∈S,∃q:ℚ,dist x y^2=(q:ℝ) := by
  classical
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := Finset.two_lt_card_iff.mp hn
  obtain ⟨u,hu⟩ := h x hx y hy
  obtain ⟨v,hv⟩ := h x hx z hz
  obtain ⟨w,hw⟩ := h y hy z hz
  have h₁ : (u:ℝ)≠0 := by intro he; rw [he,mul_zero] at hu; exact (sq_pos_of_pos (dist_pos.mpr hxy)).ne' hu
  have h₂ : (v:ℝ)≠0 := by intro he; rw [he,mul_zero] at hv; exact (sq_pos_of_pos (dist_pos.mpr hxz)).ne' hv
  have h₃ : (w:ℝ)≠0 := by intro he; rw [he,mul_zero] at hw; exact (sq_pos_of_pos (dist_pos.mpr hyz)).ne' hw
  have eq := triangle_chords x y z
  change 4*dist x y^2*dist x z^2-(dist x y^2+dist x z^2-dist y z^2)^2=dist x y^2*dist x z^2*dist y z^2 at eq
  rw [hu,hv,hw] at eq
  let q : ℚ := (4*u*v-(u+v-w)^2)/(u*v*w)
  have sq : s=(q:ℝ) := by
    dsimp [q]; push_cast
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero h₁ h₂) h₃)).mpr
    apply mul_left_cancel₀ (pow_ne_zero 2 hs.ne')
    linear_combination -eq
  intro a ha b hb
  obtain ⟨j,hj⟩ := h a ha b hb
  refine ⟨q*j,?_⟩
  rw [Rat.cast_mul,←sq,hj]
end Erdos1082Cover
end
end

section
/- A critical configuration with commensurable squared distances has at most n/2+2 points on any circle. -/
open Classical EuclideanGeometry
noncomputable section
namespace Erdos1082Cover
open OMA.R_Erdos1082_erdos_1082_parts_i_R1

theorem scaled_rational_circle (A B : Finset ℝ²) (c : ℝ²) (r s : ℝ) (hspos : 0<s)
    (hBA : B⊆A) (hC : ∀x∈B,dist x c=r) (hQ : ∀x∈B,∀y∈B,∃q:ℚ,dist x y^2=s*q) :
    2*B.card≤2*distinctDistances A+7 := by
  classical
  by_cases hcard : 2<B.card
  swap
  · omega
  have hsub : ¬ B ⊆ {c} := by
    intro h; have hh : B.card ≤ 1 := (Finset.card_le_card h).trans_eq (Finset.card_singleton c); omega
  obtain ⟨x,hx,hxc⟩ := Finset.not_subset.mp hsub
  have hr : 0 < r := (dist_pos.mpr (show x ≠ c by simpa using hxc)).trans_eq (hC x hx)
  let E := Complex.orthonormalBasisOneI.repr.symm
  let F (x : ℝ²) := E (x-c) / (r : ℂ)
  have hdist (x y : ℝ²) : dist (F x) (F y) = dist x y / r := by
    rw [dist_eq_norm]; dsimp only [F]
    rw [←sub_div,norm_div,←map_sub,E.norm_map,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,
      show (x-c)-(y-c) = x-y by abel,dist_eq_norm]
  have hFc : F c = 0 := by simp [F]
  have hnorm (x : ℝ²) : ‖F x‖ = dist x c / r := by rw [←dist_zero_right,← hFc,hdist]
  have hinj : Function.Injective F := by
    intro x y h
    have hxy := hdist x y
    rw [h,dist_self] at hxy
    exact dist_eq_zero.mp ((div_eq_zero_iff.mp hxy.symm).resolve_right hr.ne')
  let G (x : B) : Circle := ⟨F x.1, mem_sphere_zero_iff_norm.mpr (by rw [hnorm,hC _ x.2,div_self hr.ne'])⟩
  let S := B.attach.image G
  let D := (distanceSet A).image (· / r)
  have hG : Function.Injective G := by
    intro u v h
    exact Subtype.ext (hinj (congrArg ((↑) : Circle → ℂ) h))
  have hSc : S.card = B.card := by dsimp [S]; rw [Finset.card_image_of_injective _ hG,Finset.card_attach]
  have hDc : D.card = distinctDistances A := by
    apply Finset.card_image_of_injective
    exact fun _ _ h => (div_left_inj' hr.ne').mp h
  let A' := A.image F
  have hs : S.Nonempty := Finset.card_pos.mp (by omega)
  have SA (z : Circle) (hz : z∈S) : (z:ℂ)∈A' := by
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image_of_mem F (hBA x.2)
  have hDsub : distanceSet A'⊆D := by
    intro d hd
    obtain ⟨⟨x,y⟩,hpair,heq⟩ := Finset.mem_image.mp hd
    obtain ⟨hx,hy,he⟩ := Finset.mem_offDiag.mp hpair
    obtain ⟨x,hxA,ex⟩ := Finset.mem_image.mp hx
    obtain ⟨y,hyA,ey⟩ := Finset.mem_image.mp hy
    change F x=_ at ex
    change F y=_ at ey
    change dist _ _=d at heq
    rw [← ex, ← ey] at heq
    change _≠_ at he
    rw [← ex, ← ey] at he
    have exy : x≠y := fun e => he (congrArg F e)
    exact Finset.mem_image.mpr ⟨dist x y,dist_mem hxA hyA exy,(hdist x y).symm.trans heq⟩
  have hdistA : distinctDistances A'≤distinctDistances A := (Finset.card_le_card hDsub).trans_eq hDc
  have scal (x : Circle) (hx:x∈S) (y : Circle) (hy:y∈S) : ∃q : ℚ,dist x y^2=(s/r^2)*q := by
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨q,hq⟩ := hQ _ u.2 _ v.2
    refine ⟨q,?_⟩
    change dist (F u.1) (F v.1)^2=_
    rw [hdist,div_pow,hq]
    ring
  have hrat := rationalize_chords S (by omega) (s/r^2) (div_pos hspos (sq_pos_of_pos hr)) scal
  have bound := rational_circle_bound A' S SA hrat
  omega

theorem critical_rational_circle_bound (A : Finset ℝ²) (hA : A.card=2*distinctDistances A+2)
    (s : ℝ) (hs : 0<s) (h : ∀x∈A,∀y∈A,∃q:ℚ,dist x y^2=s*q) (c : ℝ²) (r : ℝ) :
    (A.filter fun x => dist x c=r).card≤A.card/2+2 := by
  classical
  let B := A.filter fun x => dist x c=r
  have sub : B⊆A := Finset.filter_subset _ _
  have bound := scaled_rational_circle A B c r s hs sub (fun x hx => (Finset.mem_filter.mp hx).2)
    (fun x hx y hy => h x (sub hx) y (sub hy))
  change B.card≤A.card/2+2
  omega
end Erdos1082Cover
end
end

open EuclideanGeometry

theorem OMA.solution : OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1.H1 := by
  intro A hn hcard
  refine ⟨Erdos1082Cover.critical_circle_threshold A hn hcard,
    Erdos1082Cover.critical_algebraic_or_circle_bound A hn hcard,?_⟩
  rintro ⟨s,hs,hq⟩
  exact Erdos1082Cover.critical_rational_circle_bound A hcard s hs hq
