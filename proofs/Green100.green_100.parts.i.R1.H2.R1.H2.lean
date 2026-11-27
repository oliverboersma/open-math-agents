import OMAReductions.R_Green100_green_100_parts_i_R1_H2_R1
import Mathlib
open Finset Module LinearMap Submodule
namespace Sofic100
noncomputable section
variable {K G V : Type} [Field K] [Group G]

def column (θ:G→Equiv.Perm V) (x:MonoidAlgebra K G) (i:V) : V→₀K :=
  Finsupp.lmapDomain K K (fun g => θ g i) x.coeff

def op (θ:G→Equiv.Perm V) (x:MonoidAlgebra K G) : Module.End K (V→₀K) :=
  Finsupp.linearCombination K (column θ x)

lemma op_single (θ:G→Equiv.Perm V) (x:MonoidAlgebra K G) (i:V) (a:K) :
    op θ x (.single i a)=a • column θ x i := Finsupp.linearCombination_single ..

lemma col_sum (θ:G→Equiv.Perm V) (x:MonoidAlgebra K G) (i:V) :
    column θ x i=∑ g∈x.coeff.support,Finsupp.single (θ g i) (x.coeff g) := rfl

lemma product (θ:G→Equiv.Perm V) (a b:MonoidAlgebra K G) (i:V)
    (hm:∀ g∈a.coeff.support,∀ h∈b.coeff.support,θ (g*h) i=θ g (θ h i)) :
    op θ a (column θ b i)=column θ (a*b) i := by
  classical
  rw [col_sum,map_sum]
  conv_rhs => rw [column,MonoidAlgebra.mul_def]
  simp only [Finsupp.sum,MonoidAlgebra.coeff_sum,map_sum,MonoidAlgebra.coeff_single,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [op_single,col_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [hm g hg h hh,Finsupp.smul_single,smul_eq_mul,mul_comm]

lemma reverse_rank {W:Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (A B:Module.End K W) : finrank K (range (B.comp A - LinearMap.id))=
      finrank K (range (A.comp B - LinearMap.id)) := by
  let D := B.comp A - LinearMap.id
  let E := A.comp B - LinearMap.id
  have hd (v:ker D) : B (A v.val)=v.val := sub_eq_zero.mp v.property
  have he (v:ker E) : A (B v.val)=v.val := sub_eq_zero.mp v.property
  let e : ker D ≃ₗ[K] ker E := {
    toFun := fun v => ⟨A v.val,show A (B (A v.val))-A v.val=0 by rw [hd,sub_self]⟩
    invFun := fun v => ⟨B v.val,show B (A (B v.val))-B v.val=0 by rw [he,sub_self]⟩
    left_inv := fun v => Subtype.ext (hd v)
    right_inv := fun v => Subtype.ext (he v)
    map_add' := fun _ _ => Subtype.ext (map_add ..)
    map_smul' := fun _ _ => Subtype.ext (map_smul ..) }
  have eq := e.finrank_eq
  change finrank K (range D)=finrank K (range E)
  have h := D.finrank_range_add_finrank_ker
  have j := E.finrank_range_add_finrank_ker
  omega

lemma obstruction {n:ℕ} (U:Finset (Fin n)) (A B:Module.End K (Fin n →₀ K))
    (S:Fin n → Fin n →₀ K) (m:ℕ) (j:Equiv.Perm (Fin n))
    (left:∀ i∈U,A (B (Finsupp.single i 1))=Finsupp.single i 1)
    (right:∀ i∈U,B (A (Finsupp.single i 1))-Finsupp.single i 1=S i)
    (sparse:∀ i∈U,(S i).support.card ≤ m) (hit:∀ i∈U,j i∈(S i).support) :
    n≤(m+1)*(n-U.card) := by
  classical
  let E := A.comp B-LinearMap.id
  let D := B.comp A-LinearMap.id
  have rkle : U.card≤finrank K (ker E) := by
    let v (i:U) : ker E := ⟨Finsupp.single i.val 1,sub_eq_zero.mpr (left _ i.prop)⟩
    have lin : LinearIndependent K v := by
      apply LinearIndependent.of_comp (ker E).subtype
      exact (Finsupp.linearIndependent_single_one (ι:=Fin n) (R:=K)).comp Subtype.val (Subtype.val_injective)
    simpa only [Fintype.card_coe] using lin.fintype_card_le_finrank
  have ambient : finrank K (Fin n →₀ K)=n := by simp
  have bound : finrank K (range D)≤n-U.card := by
    have rr:=reverse_rank A B
    change finrank K (range D)=finrank K (range E) at rr
    have rn:=E.finrank_range_add_finrank_ker
    omega
  let s:Set (Fin n →₀ K) := S '' (U:Set (Fin n))
  obtain ⟨T,sub,count,spanT,_⟩ := Submodule.exists_finset_span_eq_linearIndepOn K s
  have spanle : span K s ≤ range D := by
    apply span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    exact ⟨Finsupp.single i 1,right i hi⟩
  have tc : T.card≤n-U.card := count.trans_le ((Submodule.finrank_mono spanle).trans bound)
  let Z := T.biUnion Finsupp.support
  have covers : span K s ≤ Finsupp.supported K K (Z:Set (Fin n)) := by
    rw [←spanT]
    apply span_le.mpr
    intro v hv
    exact (Finsupp.mem_supported K v).mpr (fun k hk => Finset.mem_biUnion.mpr ⟨v,hv,hk⟩)
  have ucover : U.image j ⊆ Z := by
    rintro _ hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact (Finsupp.mem_supported K _).mp (covers (Submodule.subset_span (show S i∈s from ⟨i,hi,rfl⟩))) (hit i hi)
  have cb : Z.card ≤ T.card*m := Finset.card_biUnion_le_card_mul _ _ _ (by
    intro v hv; rcases sub hv with ⟨i,hi,rfl⟩; exact sparse i hi)
  have ub := (Finset.card_le_card ucover).trans (cb.trans (Nat.mul_le_mul_right m tc))
  rw [Finset.card_image_of_injective _ j.injective] at ub
  have un : U.card≤n := by simpa using Finset.card_le_univ U
  rw [Nat.add_mul,one_mul,Nat.mul_comm m]
  omega

set_option maxHeartbeats 900000 in
lemma main (K G:Type) [Field K] [Fintype K] [Group G] (a b:MonoidAlgebra K G)
    (ab:a*b=1) (ba:b*a≠1) : ∃ (F:Finset G) (k:ℕ), ∀ (n:ℕ)
    (θ:G→Equiv.Perm (Fin n)) (U:Finset (Fin n)), (∀ i∈U, θ 1 i=i ∧
      Set.InjOn (fun g => θ g i) F ∧ ∀ g∈F,∀ h∈F,θ (g*h) i=θ g (θ h i)) → n≤k*(n-U.card) := by
  classical
  let c := b*a-1
  have cn : c.coeff≠0 := by
    intro h
    apply ba; apply sub_eq_zero.mp
    exact MonoidAlgebra.coeff_injective h
  obtain ⟨g,hg⟩ := Finsupp.support_nonempty_iff.mpr cn
  let F := a.coeff.support ∪ b.coeff.support ∪ c.coeff.support
  refine ⟨F,c.coeff.support.card+1,?_⟩
  intro n θ U approx
  have ha : a.coeff.support ⊆ F := fun _ h => mem_union_left _ (mem_union_left _ h)
  have hb : b.coeff.support ⊆ F := fun _ h => mem_union_left _ (mem_union_right _ h)
  have hc : c.coeff.support ⊆ F := fun _ h => mem_union_right _ h
  have one (i:Fin n) (hi:i∈U) : column θ (1:MonoidAlgebra K G) i=Finsupp.single i 1 := by
    simp [column,MonoidAlgebra.one_def,(approx i hi).1]
  apply obstruction U (op θ a) (op θ b) (column θ c) _ (θ g)
  · intro i hi
    rw [op_single,one_smul,product θ a b i (fun g hg h hh => (approx i hi).2.2 g (ha hg) h (hb hh)),ab,one i hi]
  · intro i hi
    rw [op_single,one_smul,product θ b a i (fun g hg h hh => (approx i hi).2.2 g (hb hg) h (ha hh)),←one i hi]
    simp only [column,c,MonoidAlgebra.coeff_sub,map_sub]
  · intro i _
    exact (Finset.card_le_card Finsupp.mapDomain_support).trans Finset.card_image_le
  · intro i hi
    change θ g i ∈ (Finsupp.mapDomain (fun h => θ h i) c.coeff).support
    rw [Finsupp.mapDomain_support_of_injOn c.coeff ((approx i hi).2.1.mono hc)]
    exact Finset.mem_image_of_mem _ hg
end
end Sofic100


theorem OMA.solution : OMA.R_Green100_green_100_parts_i_R1_H2_R1.H2 := Sofic100.main
