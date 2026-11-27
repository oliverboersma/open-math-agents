import FormalConjectures.ErdosProblems.«690»
import Mathlib

/-! Wang and Crapis, A Complete Answer to Erdős Problem 690, Lemmas 3.1 and
3.2. Pointing one element of a subset gives the two-sided sign test for
consecutive prime densities. The numerical and large-prime-gap estimates
are isolated from the exact density calculation. -/
namespace OMA.R_Erdos690_erdos_690_variants_large_k_R1

open Finset Filter Erdos690
open scoped Classical

/-- CRT gives the elementary symmetric polynomial formula for the density. -/
def H1 : Prop :=
  let w := fun p : ℕ => 1/((p:ℝ)-1)
  let B := fun p : ℕ => ∏ x ∈ Nat.primesBelow p, (1-1/(x:ℝ))
  let E := fun (p l : ℕ) => ∑ T ∈ (Nat.primesBelow p).powersetCard l, ∏ x ∈ T,w x
  ∀ k p : ℕ, p.Prime → (kthPrimeFactorSet (k+1) p).HasDensity (B p*E p k/p)

/-- An early large gap and a later small gap, with reciprocal prime weight
bounds. The condition for the large gap discards any r of the earlier weights. -/
def H2 : Prop :=
  let w := fun p : ℕ => 1/((p:ℝ)-1)
  ∀ r : ℕ, 19 ≤ r → ∃ p q u v : ℕ,
    p.Prime ∧ q.Prime ∧ u.Prime ∧ v.Prime ∧ p<q ∧ q≤u ∧ u<v ∧
    Nat.primesBelow q = insert p (Nat.primesBelow p) ∧
    Nat.primesBelow v = insert u (Nat.primesBelow u) ∧
    r≤(Nat.primesBelow p).card ∧ r≤(Nat.primesBelow u).card ∧
    (∀ T ∈ (Nat.primesBelow p).powersetCard r,
      (r:ℝ)+1 < ((q:ℝ)+1-p)*(∑ x ∈ Nat.primesBelow p \ T,w x)) ∧
    ((v:ℝ)+1-u)*(∑ x ∈ Nat.primesBelow u,w x)<(r:ℝ)+1

lemma pointed (S : Finset ℕ) (w : ℕ → ℝ) (r : ℕ) :
    ((r:ℝ)+1)*(∑ U ∈ S.powersetCard (r+1),∏ x ∈ U,w x) =
      ∑ T ∈ S.powersetCard r,(∏ x ∈ T,w x)*(∑ x ∈ S \ T,w x) := by
  rw [mul_sum]
  simp only [mul_sum]
  calc
    _ = ∑ U ∈ S.powersetCard (r+1), ∑ _x ∈ U,∏ z ∈ U,w z := by
      apply sum_congr rfl
      intro U hU
      simp [((mem_powersetCard.mp hU).2)]
    _ = _ := by
      rw [sum_sigma',sum_sigma']
      apply sum_bij (fun z _ => Sigma.mk (z.1.erase z.2) z.2)
      · rintro ⟨U,x⟩ hu
        obtain ⟨hU,hx⟩ := mem_sigma.mp hu
        obtain ⟨sub,card⟩ := mem_powersetCard.mp hU
        exact mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨(erase_subset ..).trans sub,
          by simp [card_erase_of_mem hx,card]⟩,mem_sdiff.mpr ⟨sub hx,by simp⟩⟩
      · rintro ⟨U,x⟩ hu ⟨V,y⟩ hv he
        have xy : x=y := congrArg (fun z : (Σ _ : Finset ℕ, ℕ) => z.2) he
        subst y
        have uv : U.erase x=V.erase x := congrArg Sigma.fst he
        have hx := (mem_sigma.mp hu).2
        have hy := (mem_sigma.mp hv).2
        have eq := congrArg (insert x) uv
        rw [insert_erase hx,insert_erase hy] at eq
        change U=V at eq
        subst V
        rfl
      · rintro ⟨T,x⟩ ht
        obtain ⟨hT,hx⟩ := mem_sigma.mp ht
        obtain ⟨xs,xt⟩ := mem_sdiff.mp hx
        obtain ⟨sub,ct⟩ := mem_powersetCard.mp hT
        refine ⟨⟨insert x T,x⟩,mem_sigma.mpr ⟨mem_powersetCard.mpr
          ⟨insert_subset xs sub,by simp [xt,ct]⟩,mem_insert_self ..⟩,?_⟩
        simp [xt]
      · rintro ⟨U,x⟩ hu
        exact (prod_erase_mul U w (mem_sigma.mp hu).2).symm

lemma addWeight (S : Finset ℕ) (w : ℕ → ℝ) {p : ℕ} (hp : p∉S) (r : ℕ) :
    (∑ U ∈ (insert p S).powersetCard (r+1),∏ x ∈ U,w x) =
      (∑ U ∈ S.powersetCard (r+1),∏ x ∈ U,w x) +
        w p * ∑ T ∈ S.powersetCard r,∏ x ∈ T,w x := by
  have missing (t : ℕ) (T : Finset ℕ) (hT : T∈S.powersetCard t) : p∉T :=
    fun h => hp ((mem_powersetCard.mp hT).1 h)
  rw [powersetCard_succ_insert hp,sum_union]
  · congr 1
    rw [sum_image,mul_sum]
    · exact sum_congr rfl fun T hT => prod_insert (missing r T hT)
    · intro T ht U hu e
      simpa [missing r T ht,missing r U hu] using congrArg (fun V : Finset ℕ => V.erase p) e
  · rw [disjoint_left]
    intro T ht hu
    obtain ⟨U,_,rfl⟩ := mem_image.mp hu
    exact missing _ _ ht (mem_insert_self ..)

lemma weightsComparison (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ x∈S,0<w x)
    (r : ℕ) (hr : r≤S.card) (g : ℝ) (hg : 0<g) :
    let E := fun n => ∑ T ∈ S.powersetCard n,∏ x ∈ T,w x
    ((∀ T∈S.powersetCard r,(r:ℝ)+1<g*∑ x∈S\T,w x) → E r < g*E (r+1)) ∧
    (g*(∑ x∈S,w x)<(r:ℝ)+1 → g*E (r+1)<E r) := by
  intro E
  have pos (T : Finset ℕ) (hT : T∈S.powersetCard r) : 0<∏ x∈T,w x :=
    prod_pos fun x hx => hw x ((mem_powersetCard.mp hT).1 hx)
  have eq := pointed S w r
  change ((r:ℝ)+1)*E (r+1)=_ at eq
  have rpos : 0<(r:ℝ)+1 := by positivity
  have ne := powersetCard_nonempty.mpr hr
  have a : ((r:ℝ)+1)*E r=∑ T∈S.powersetCard r,((∏ x∈T,w x)*((r:ℝ)+1)) := by
    dsimp [E];rw [←sum_mul,mul_comm]
  have b : ((r:ℝ)+1)*(g*E (r+1)) =
      ∑ T∈S.powersetCard r,(∏ x∈T,w x)*(g*∑ x∈S\T,w x) := by
    rw [mul_left_comm,eq,mul_sum]
    exact sum_congr rfl fun _ _ => by ring
  constructor
  · intro h
    apply lt_of_mul_lt_mul_left _ rpos.le
    rw [a,b]
    exact sum_lt_sum_of_nonempty ne fun T ht => mul_lt_mul_of_pos_left (h T ht) (pos T ht)
  · intro h
    apply lt_of_mul_lt_mul_left _ rpos.le
    rw [a,b]
    apply sum_lt_sum_of_nonempty ne
    intro T ht
    have le : (∑ x∈S\T,w x) ≤ ∑ x∈S,w x :=
      sum_le_sum_of_subset_of_nonneg sdiff_subset (fun x hx _ => (hw x hx).le)
    exact mul_lt_mul_of_pos_left ((mul_le_mul_of_nonneg_left le hg.le).trans_lt h) (pos T ht)

lemma primeGapSign (p q r : ℕ) (pp : p.Prime) (pq : p<q)
    (step : Nat.primesBelow q=insert p (Nat.primesBelow p)) :
    let w := fun p : ℕ => 1/((p:ℝ)-1)
    let B := fun p : ℕ => ∏ x ∈ Nat.primesBelow p, (1-1/(x:ℝ))
    let E := fun (p l : ℕ) => ∑ T ∈ (Nat.primesBelow p).powersetCard l, ∏ x ∈ T,w x
    let D := fun x => B x*E x (r+1)/x
    (p:ℝ)*q*(D q-D p) = B p*(E p r-((q:ℝ)+1-p)*E p (r+1)) := by
  intro w B E D
  have hp : p∉Nat.primesBelow p := by simp [Nat.primesBelow]
  have eb : E q (r+1) = E p (r+1)+w p*E p r := by
    dsimp [E];rw [step];exact addWeight _ w hp r
  have bb : B q = (1-1/(p:ℝ))*B p := by dsimp [B];rw [step,prod_insert hp]
  have pp' : (1:ℝ)<p := by exact_mod_cast pp.one_lt
  have p0 : (p:ℝ)≠0 := by linarith
  have q0 : (q:ℝ)≠0 := by exact_mod_cast (show q≠0 by omega)
  dsimp only [D]
  rw [eb,bb]
  dsimp only [w]
  field_simp [p0,q0,sub_ne_zero.mpr pp'.ne']
  <;> ring

theorem main : H1 → H2 → type_of% @Erdos690.erdos_690.variants.large_k := by
  classical
  intro density gaps ⟨k,hk,uni⟩
  obtain ⟨r,rfl⟩ : ∃ r : ℕ,k=r+2 := ⟨k-2,by omega⟩
  let w := fun p : ℕ => 1/((p:ℝ)-1)
  let B := fun p : ℕ => ∏ x ∈ Nat.primesBelow p, (1-1/(x:ℝ))
  let E := fun (p l : ℕ) => ∑ T ∈ (Nat.primesBelow p).powersetCard l, ∏ x ∈ T,w x
  let D := fun x => B x*E x (r+1)/x
  obtain ⟨m,pm,inc,dec⟩ := uni D (fun p hp => density (r+1) p hp)
  obtain ⟨p,q,u,v,pp,qp,up,vp,pq,qu,uv,pstep,ustep,pr,ur,wide,narrow⟩ := gaps r (by omega)
  have wp {x t : ℕ} (hx : x∈Nat.primesBelow t) : 0<w x := by
    have px := (mem_filter.mp hx).2
    have xx : (1:ℝ)<x := by exact_mod_cast px.one_lt
    dsimp [w];positivity
  have base (x : ℕ) : 0<B x := by
    apply prod_pos
    intro t ht
    have one : (1:ℝ)<t := by exact_mod_cast (mem_filter.mp ht).2.one_lt
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr one)
  have gpos {i j : ℕ} (h : i<j) : 0<((j:ℝ)+1-i) := by
    have h' : (i:ℝ)<j := by exact_mod_cast h
    linarith
  have d1 := (weightsComparison _ w (fun _ hx => wp hx) r pr _ (gpos pq)).1 wide
  have d2 := (weightsComparison _ w (fun _ hx => wp hx) r ur _ (gpos uv)).2 narrow
  change E p r < ((q:ℝ)+1-p)*E p (r+1) at d1
  change ((v:ℝ)+1-u)*E u (r+1) < E u r at d2
  have e1 := primeGapSign p q r pp pq pstep
  have e2 := primeGapSign u v r up uv ustep
  change (p:ℝ)*q*(D q-D p)=B p*(E p r-((q:ℝ)+1-p)*E p (r+1)) at e1
  change (u:ℝ)*v*(D v-D u)=B u*(E u r-((v:ℝ)+1-u)*E u (r+1)) at e2
  have descent : D q < D p := by
    by_contra! h
    linarith only [e1,mul_neg_of_pos_of_neg (base p) (sub_neg.mpr d1),
      mul_nonneg (by positivity : 0≤(p:ℝ)*q) (sub_nonneg.mpr h)]
  have ascent : D u < D v := by
    by_contra! h
    linarith only [e2,mul_pos (base u) (sub_pos.mpr d2),
      mul_nonpos_of_nonneg_of_nonpos (by positivity : 0≤(u:ℝ)*v) (sub_nonpos.mpr h)]
  by_cases hm : q ≤ m
  · exact descent.not_ge (inc p q pp qp pq.le hm)
  · exact ascent.not_ge (dec u v up vp (by omega) uv.le)

end OMA.R_Erdos690_erdos_690_variants_large_k_R1

