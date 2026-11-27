import FormalConjectures.ErdosProblems.«829»

/-! # Mahler's lower bound for positive sums of two cubes

K. Mahler, *On the lattice points on curves of genus 1* (1935), Theorem 6.
We give a rational, effective argument in the spirit of the height estimates in J. H. Silverman,
*Taxicabs and sums of two cubes* (1993). On the Mordell curve y²=x³−48, the point
(73/9,595/27) has infinite order by a parity argument. Projective addition bounds the
coordinate heights of its multiples. Three explicit alternatives (identity or one of two
translations, after reflection) cover the real locus by positive cube representations.
The cover has bounded multiplicity; clearing all denominators gives the fourth-root
logarithmic estimate for natural cubes, with no equidistribution hypothesis. -/

/- On the cubic y²=x³−48 the point (73/9,595/27) has infinite order.
Successive doubles of its integral projective representative have odd Y
and acquire exactly three further factors of two in Z. -/
namespace OMA.MordellPoint829
open WeierstrassCurve Projective
open scoped WeierstrassCurve.Projective

def E (K : Type*) [CommRing K] : WeierstrassCurve.Projective K := ⟨0,0,0,0,-48⟩

abbrev Vec (K : Type*) := Fin 3 → K
def castV (K : Type*) [CommRing K] (v : Vec ℤ) : Vec K := fun i => v i
def base : Vec ℤ := ![219,595,27]

theorem map_E (K : Type*) [CommRing K] : (E ℤ).map (Int.castRingHom K)=E K := by
  ext <;> simp [E,WeierstrassCurve.map]

theorem cast_dbl (K : Type*) [CommRing K] (v : Vec ℤ) :
    castV K ((E ℤ).dblXYZ v)=(E K).dblXYZ (castV K v) := by
  rw [← map_E K]
  exact (map_dblXYZ (Int.castRingHom K) v).symm

theorem cast_add (K : Type*) [CommRing K] (v w : Vec ℤ) :
    castV K ((E ℤ).addXYZ v w)=(E K).addXYZ (castV K v) (castV K w) := by
  rw [← map_E K]
  exact (map_addXYZ (Int.castRingHom K) v w).symm

theorem valid : (E ℚ).Nonsingular (castV ℚ base) := by
  rw [nonsingular_iff,equation_iff]
  norm_num [E,castV,base,show (![219,595,27]:Vec ℤ) 2=27 from rfl]

def R : (E ℚ).Point := ⟨(nonsingularLift_iff _).mpr valid⟩

private noncomputable def twice : ℕ → Vec ℤ
  | 0 => base
  | n+1 => (E ℤ).dblXYZ (twice n)

private theorem multiple (n:ℕ) :
    ((2^n:ℕ) • R).point = ⟦castV ℚ (twice n)⟧ := by
  induction n with
  | zero => simp [twice,R]
  | succ n ih =>
    rw [pow_succ,mul_nsmul,two_nsmul,Point.add_point,ih,addMap_eq,add_self]
    exact congrArg Quotient.mk'' (cast_dbl ℚ _).symm

private theorem y_odd (v:Vec ℤ) (h : Odd (v 1)) : Odd ((E ℤ).dblXYZ v 1) := by
  change Odd ((E ℤ).dblY v)
  simp [dblY,negDblY,negY,E]
  obtain ⟨k,hk⟩ := h
  rw [hk]
  apply Int.odd_iff.mpr
  norm_num [Int.add_emod,Int.sub_emod,Int.mul_emod]
  exact Int.odd_iff.mp (show Odd (2*k+1 : ℤ) from ⟨k,rfl⟩).pow

private theorem z_double (v:Vec ℤ) : (E ℤ).dblXYZ v 2=8*v 2*(v 1)^3 := by
  change (E ℤ).dblZ v=_
  simp [dblZ,negY,E]
  ring

private theorem parity (n:ℕ) : Odd (twice n 1) ∧ ∃a:ℤ,Odd a ∧ twice n 2=8^n*a := by
  induction n with
  | zero => exact ⟨by decide,27,by decide,by decide⟩
  | succ n ih =>
    obtain ⟨oy,a,oa,za⟩ := ih
    refine ⟨y_odd _ oy,a*(twice n 1)^3,oa.mul (oy.pow),?_⟩
    rw [twice,z_double,za,pow_succ]
    ring

private theorem unequal {n m:ℕ} (lt:n < m) :
    (2^n:ℕ) • R ≠ (2^m:ℕ) • R := by
  intro eq
  have coords := congrArg Point.point eq
  rw [multiple,multiple] at coords
  have rel := Y_eq_of_equiv (Quotient.exact coords)
  simp only [castV] at rel
  have cross : twice n 1*twice m 2=twice m 1*twice n 2 := by exact_mod_cast rel
  obtain ⟨yn,a,oa,za⟩ := parity n
  obtain ⟨ym,b,ob,zb⟩ := parity m
  rw [za,zb] at cross
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le' (Nat.succ_le_of_lt lt)
  rw [pow_add,pow_succ] at cross
  have key : 8^n*((twice n 1)*8^k*8*b) = 8^n*((twice (k+(n+1)) 1)*a) := by
    linear_combination cross
  have h := mul_left_cancel₀ (by positivity : (8:ℤ)^n≠0) key
  have even : Even (twice (k+(n+1)) 1*a) := by rw [←h];exact ⟨twice n 1*8^k*4*b,by ring⟩
  exact (Int.not_even_iff_odd.mpr (ym.mul oa)) even

/-- Distinct natural multiples give distinct rational points. -/
theorem multiples_injective : Function.Injective (fun n:ℕ => n • R) := by
  apply injective_nsmul_iff_not_isOfFinAddOrder.mpr
  intro h
  let f (j:ℕ) : Fin (addOrderOf R) := ⟨2^j % addOrderOf R,Nat.mod_lt _ h.addOrderOf_pos⟩
  obtain ⟨n,m,ne,eq⟩ := Finite.exists_ne_map_eq_of_infinite f
  have sm : (2^n:ℕ) • R = (2^m:ℕ) • R := nsmul_inj_mod.mpr (congrArg Fin.val eq)
  obtain lt|lt := lt_or_gt_of_ne ne
  · exact unequal lt sm
  · exact unequal lt sm.symm

end OMA.MordellPoint829

/- Quartic homogeneous projective formulas and balanced binary addition
bound the integer representatives of the first K multiples on y²=x³−48. -/
namespace OMA.Height829
open WeierstrassCurve Projective OMA.MordellPoint829
open scoped WeierstrassCurve.Projective

private theorem quartic {V:Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
    (f:V→Vec ℝ) (hc:Continuous f) (hom:∀s:ℝ,∀p:V,f (s • p)=s^4 • f p) :
    ∃M:ℕ,∀r:ℝ,0<r → ∀p:V,‖p‖≤r → ‖f p‖≤(M:ℝ)*r^4 := by
  obtain ⟨K,hK⟩ := (isCompact_closedBall (0:V) 1).bddAbove_image hc.norm.continuousOn
  obtain ⟨M,hM⟩ := exists_nat_gt K
  refine ⟨M,?_⟩
  intro r hr p hp
  have ins : r⁻¹ • p ∈ Metric.closedBall (0:V) 1 := by
    rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    simpa [hr.ne'] using mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hr.le)
  have bb := (hK (Set.mem_image_of_mem _ ins)).trans hM.le
  have eq : f p=r^4 • f (r⁻¹ • p) := by rw [←hom,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  rw [eq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),mul_comm]
  exact mul_le_mul_of_nonneg_right bb (by positivity)

private theorem continuous_dbl : Continuous ((E ℝ).dblXYZ) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [dblXYZ,dblX,dblY,negDblY,dblZ,negY,E,
    Matrix.cons_val_two] <;> fun_prop

private theorem continuous_add : Continuous (fun p:Vec ℝ×Vec ℝ => (E ℝ).addXYZ p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [addXYZ,addX,addY,negAddY,addZ,negY,E,
    Matrix.cons_val_two] <;> fun_prop

private theorem coord_le (p:Vec ℤ) (L:ℕ) :
    (∀i,(p i).natAbs≤L) ↔ ‖castV ℝ p‖≤L := by
  rw [pi_norm_le_iff_of_nonneg (Nat.cast_nonneg L)]
  constructor <;> intro h i <;> specialize h i
  · change |(p i:ℝ)| ≤ (L:ℝ)
    rw [←Int.cast_abs,←Nat.cast_natAbs]
    exact_mod_cast h
  · change |(p i:ℝ)| ≤ (L:ℝ) at h
    rw [←Int.cast_abs,←Nat.cast_natAbs] at h
    exact_mod_cast h

/-- A uniform quartic coefficient bound for the two applicable addition laws. -/
private theorem coefficient_bound :
    ∃ B:ℕ,595≤B ∧ ∀H:ℕ,0<H → ∀p q:Vec ℤ, (∀i,(p i).natAbs≤H) →
      (∀i,(q i).natAbs≤H) → (∀i,((E ℤ).dblXYZ p i).natAbs≤B*H^4) ∧
        (∀i,((E ℤ).addXYZ p q i).natAbs≤B*H^4) := by
  obtain ⟨M,md⟩ := quartic _ continuous_dbl fun s p => dblXYZ_smul p s
  obtain ⟨N,ma⟩ := quartic _ continuous_add (fun s p => by
    change (E ℝ).addXYZ (s • p.1) (s • p.2)=s^4 • (E ℝ).addXYZ p.1 p.2
    rw [addXYZ_smul]
    congr 1
    ring)
  let B:=595+M+N
  refine ⟨B,by dsimp [B];omega,?_⟩
  intro H hH p q hp hq
  have pp := (coord_le p H).mp hp
  have qq := (coord_le q H).mp hq
  have hR : (0:ℝ)<H := by exact_mod_cast hH
  have pd := md H hR (castV ℝ p) pp
  have pa := ma H hR (castV ℝ p,castV ℝ q) (by exact max_le pp qq)
  constructor
  · apply (coord_le _ _).mpr
    rw [cast_dbl]
    push_cast
    exact pd.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (show M≤B by dsimp [B];omega))
      (by positivity))
  · apply (coord_le _ _).mpr
    rw [cast_add]
    push_cast
    exact pa.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (show N≤B by dsimp [B];omega))
      (by positivity))

private def Represents (A:(E ℚ).Point) (p:Vec ℤ) : Prop :=
  A.point=⟦castV ℚ p⟧

private lemma combine {B H:ℕ}
    (form : ∀p q:Vec ℤ, (∀i,(p i).natAbs≤H) → (∀i,(q i).natAbs≤H) →
      (∀i,((E ℤ).dblXYZ p i).natAbs≤B*H^4) ∧ (∀i,((E ℤ).addXYZ p q i).natAbs≤B*H^4))
    {A C:(E ℚ).Point} {p q:Vec ℤ} (ap:Represents A p) (cq:Represents C q)
    (pb:∀i,(p i).natAbs≤H) (qb:∀i,(q i).natAbs≤H) :
    ∃v:Vec ℤ,Represents (A+C) v ∧ ∀i,(v i).natAbs≤B*H^4 := by
  obtain ⟨db,ab⟩ := form p q pb qb
  by_cases h : castV ℚ p ≈ castV ℚ q
  · refine ⟨(E ℤ).dblXYZ p,?_,db⟩
    unfold Represents at *
    rw [Point.add_point,ap,cq,addMap_eq,add_of_equiv h,cast_dbl]
  · refine ⟨(E ℤ).addXYZ p q,?_,ab⟩
    unfold Represents at *
    rw [Point.add_point,ap,cq,addMap_eq,add_of_not_equiv h,cast_add]

private lemma balanced (n:ℕ) (hn:0<n) : 1+4*(4*(n/2)^3+1) ≤ 4*n^3+1 := by
  let j:=n/2
  change 1+4*(4*j^3+1)≤4*n^3+1
  have h : 2*j≤n := by dsimp [j];omega
  have hp := Nat.pow_le_pow_left h 3
  by_cases hj:j=0
  · have h1 : n=1 := by dsimp [j] at hj;omega
    rw [hj,h1]
    decide
  · have jp : 1≤j^3 := Nat.one_le_pow _ _ (by omega)
    nlinarith

private theorem multiple_bounds :
    ∃ B:ℕ, 1<B ∧ ∀n:ℕ,∃v:Vec ℤ,Represents ((n+1) • R) v ∧
      ∀i,(v i).natAbs≤B^(4*n^3+1) := by
  obtain ⟨B,bB,form⟩ := coefficient_bound
  refine ⟨B,by omega,?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases zero : n=0
    · subst n
      refine ⟨base,by simp [Represents,R],?_⟩
      intro i
      have b : (base i).natAbs≤595 := by fin_cases i <;> decide
      simpa using b.trans bB
    let i:=(n-1)/2
    let j:=n/2
    have ij : i≤j := by dsimp [i,j];omega
    obtain ⟨p,ap,pb⟩ := ih i (by dsimp [i];omega)
    obtain ⟨q,cq,qb⟩ := ih j (by dsimp [j];omega)
    let H:=B^(4*j^3+1)
    have grow : B^(4*i^3+1)≤H := by
      apply Nat.pow_le_pow_right (by omega)
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ij _)) _
    have hp : 0<H := Nat.pow_pos (by omega)
    obtain ⟨v,rep,coords⟩ := combine (form H hp) ap cq (fun i => (pb i).trans grow) qb
    have parts : (i+1)+(j+1)=n+1 := by dsimp [i,j];omega
    rw [←add_nsmul,parts] at rep
    refine ⟨v,rep,fun i => (coords i).trans ?_⟩
    change B * (B^(4*j^3+1))^4 ≤ B^(4*n^3+1)
    rw [←pow_mul,←pow_succ']
    apply Nat.pow_le_pow_right (by omega)
    have b := balanced n (by omega)
    dsimp [j]
    omega

private def coord (p:Vec ℤ) : ℚ×ℚ := ((p 0:ℚ)/p 2,(p 1:ℚ)/p 2)

private theorem finite_coord {n:ℕ} {p:Vec ℤ} (hp:Represents ((n+1) • R) p) :
    p 2≠0 ∧ (coord p).2^2=(coord p).1^3-48 := by
  have valid : (E ℚ).Nonsingular (castV ℚ p) := (nonsingularLift_iff _).mp
    (hp ▸ ((n+1) • R).nonsingular)
  have nz : castV ℚ p 2≠0 := by
    intro no
    have eq : (n+1) • R=(0:ℕ) • R := by
      apply Point.ext
      rw [zero_nsmul,Point.zero_point,hp]
      exact Quotient.sound (equiv_zero_of_Z_eq_zero valid no)
    have := multiples_injective eq
    omega
  refine ⟨by simpa [castV] using nz,?_⟩
  have e := (equation_iff _).mp valid.1
  simp only [E,zero_mul,add_zero] at e
  change ((castV ℚ p 1)/(castV ℚ p 2))^2=((castV ℚ p 0)/(castV ℚ p 2))^3-48
  field_simp
  linear_combination e

private theorem injective_coord {n m:ℕ} {p q:Vec ℤ}
    (hp:Represents ((n+1) • R) p) (hq:Represents ((m+1) • R) q) (eq:coord p=coord q) : n=m := by
  have pn : castV ℚ p 2≠0 := by
    change (p 2:ℚ)≠0
    exact_mod_cast (finite_coord hp).1
  have qn : castV ℚ q 2≠0 := by
    change (q 2:ℚ)≠0
    exact_mod_cast (finite_coord hq).1
  have a := congrArg Prod.fst eq
  have b := congrArg Prod.snd eq
  have cl : ((n+1) • R) = (m+1) • R := by
    apply Point.ext
    rw [hp,hq,Quotient.sound (equiv_some_of_Z_ne_zero pn),Quotient.sound (equiv_some_of_Z_ne_zero qn)]
    change ⟦![(coord p).1,(coord p).2,1]⟧=⟦![(coord q).1,(coord q).2,1]⟧
    rw [a,b]
  exact Nat.succ.inj (multiples_injective cl)

private theorem reduced {a d:ℤ} (nz:d≠0) :
    max (((a:ℚ)/d).num.natAbs) (((a:ℚ)/d).den) ≤ max a.natAbs d.natAbs := by
  obtain ⟨k,ka,kd⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den a nz
  have kn : k≠0 := by intro h;rw [h,zero_mul] at kd;exact nz kd
  have kp : 1≤k.natAbs := Int.natAbs_pos.mpr kn
  have na := congrArg Int.natAbs ka
  have nd := congrArg Int.natAbs kd
  rw [Int.natAbs_mul] at na nd
  rw [Int.natAbs_natCast] at nd
  apply max_le_max
  · calc _ = 1*(((a:ℚ)/d).num.natAbs) := (one_mul _).symm
         _ ≤ _ := (Nat.mul_le_mul_right _ kp).trans_eq na.symm
  · calc _ = 1*(((a:ℚ)/d).den) := (one_mul _).symm
         _ ≤ _ := (Nat.mul_le_mul_right _ kp).trans_eq nd.symm

/-- A fixed integral cubic has arbitrarily many distinct rational solutions
of bounded reduced numerator and denominator. -/
theorem points : ∃ B:ℕ, 1<B ∧ ∀K:ℕ,0<K → ∃f:Fin K→ℚ×ℚ,Function.Injective f ∧
    ∀i, (f i).2^2=(f i).1^3-48 ∧
      max (f i).1.num.natAbs (f i).1.den ≤ B^(K^3) ∧
      max (f i).2.num.natAbs (f i).2.den ≤ B^(K^3) := by
  obtain ⟨B,bB,source⟩ := multiple_bounds
  refine ⟨B^5,one_lt_pow₀ bB (by decide),?_⟩
  intro K hK
  choose v reps bounds using source
  refine ⟨fun i => coord (v i.val),fun i j eq => Fin.ext (injective_coord (reps _) (reps _) eq),?_⟩
  intro i
  have ⟨nz,onE⟩ := finite_coord (reps i.val)
  have hb (j) : (v i.val j).natAbs ≤ (B^5)^(K^3) := by
    apply (bounds i.val j).trans
    rw [←pow_mul]
    apply Nat.pow_le_pow_right bB.le
    have a := Nat.pow_le_pow_left i.isLt.le 3
    have b : 1≤K^3 := Nat.one_le_pow _ _ hK
    omega
  exact ⟨onE,(reduced (a:=v i.val 0) nz).trans (max_le (hb 0) (hb 2)),
    (reduced (a:=v i.val 1) nz).trans (max_le (hb 1) (hb 2))⟩

end OMA.Height829

/- Clearing all denominators of a finite family of rational points converts cubic height
bounds into Mahler's fourth-root logarithmic lower bound for ordered cube representations. -/

namespace OMA.Mahler829
open Filter AdditiveCombinatorics

private theorem clear {D : ℕ} (a : ℚ) (ha : 0 ≤ a) (hd : a.den ∣ D) :
    ∃ u : ℕ, (u : ℚ) = D * a := by
  obtain ⟨e, rfl⟩ := hd
  refine ⟨a.num.toNat * e, ?_⟩
  have hz : ((a.num.toNat : ℕ) : ℚ) = (a.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr ha)
  have hn := (div_eq_iff (by exact_mod_cast a.den_ne_zero : (a.den : ℚ) ≠ 0)).mp a.num_div_den
  push_cast
  rw [hz, hn]
  ring

private theorem reps {K D : ℕ} (hD : 0 < D) (p : Fin K → ℚ × ℚ) (hp : Function.Injective p)
    (h : ∀ i, 0 ≤ (p i).1 ∧ 0 ≤ (p i).2 ∧ (p i).1^3 + (p i).2^3 = 9 ∧
      (p i).1.den ∣ D ∧ (p i).2.den ∣ D) :
    K ≤ sumRep Erdos829.cubes (9 * D^3) := by
  classical
  choose u hu using fun i => clear (p i).1 (h i).1 (h i).2.2.2.1
  choose v hv using fun i => clear (p i).2 (h i).2.1 (h i).2.2.2.2
  let f (i : Fin K) : ℕ × ℕ := ((u i)^3,(v i)^3)
  have fsum (i : Fin K) : (f i).1 + (f i).2 = 9 * D^3 := by
    change (u i)^3 + (v i)^3 = 9 * D^3
    have hh : (u i : ℚ)^3 + (v i : ℚ)^3 = 9 * (D : ℚ)^3 := by
      rw [hu, hv, mul_pow, mul_pow, ← mul_add, (h i).2.2.1, mul_comm]
    exact_mod_cast hh
  have inj : Function.Injective f := by
    intro i j hij
    have h₁ : (u i)^3 = (u j)^3 := congrArg Prod.fst hij
    have h₂ : (v i)^3 = (v j)^3 := congrArg Prod.snd hij
    have h₁' : (u i : ℚ) = (u j : ℚ) := by exact_mod_cast (Nat.pow_left_injective (by decide : 3 ≠ 0) h₁)
    have h₂' : (v i : ℚ) = (v j : ℚ) := by exact_mod_cast (Nat.pow_left_injective (by decide : 3 ≠ 0) h₂)
    rw [hu, hu] at h₁'
    rw [hv, hv] at h₂'
    have nz : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    exact hp (Prod.ext (mul_left_cancel₀ nz h₁') (mul_left_cancel₀ nz h₂'))
  rw [sumRep_def]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    (Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin K))) f
      (t := (Finset.HasAntidiagonal.antidiagonal (9 * D^3)).filter fun q =>
        q.1 ∈ Erdos829.cubes ∧ q.2 ∈ Erdos829.cubes)
      (fun i _ => Finset.mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr (fsum i),
        ⟨u i, rfl⟩, ⟨v i, rfl⟩⟩) (fun _ _ _ _ hh => inj hh))

private theorem find {K B : ℕ} (hk : 0 < K) (hb : 2 ≤ B)
    (p : Fin K → ℚ × ℚ) (hp : Function.Injective p)
    (h : ∀ i, 0 ≤ (p i).1 ∧ 0 ≤ (p i).2 ∧ (p i).1^3 + (p i).2^3 = 9 ∧
      (p i).1.den ≤ B^(K^3) ∧ (p i).2.den ≤ B^(K^3)) :
    ∃ n : ℕ, K ≤ n ∧ n ≤ B^(13*K^4) ∧ K ≤ sumRep Erdos829.cubes n := by
  let H := B^(K^3)
  let m (i : Fin K) := (p i).1.den * (p i).2.den
  let D := H * ∏ i, m i
  have hH : 0 < H := pow_pos (by omega : 0 < B) _
  have hprod : 0 < ∏ i, m i := Finset.prod_pos fun i _ => Nat.mul_pos (p i).1.den_pos (p i).2.den_pos
  have hD : 0 < D := Nat.mul_pos hH hprod
  have kH : K ≤ H := calc
    K ≤ 2^K := K.lt_two_pow_self.le
    _ ≤ B^K := Nat.pow_le_pow_left hb _
    _ ≤ H := Nat.pow_le_pow_right (by omega) (Nat.le_self_pow (by decide : 3 ≠ 0) K)
  have KD : K ≤ D := kH.trans (Nat.le_mul_of_pos_right _ hprod)
  refine ⟨9*D^3, ?_, ?_, reps hD p hp ?_⟩
  · exact KD.trans ((Nat.le_self_pow (by decide : 3 ≠ 0) D).trans (Nat.le_mul_of_pos_left _ (by decide)))
  · have hh : ∏ i, m i ≤ (H*H)^K := by
      simpa using (Finset.prod_le_prod' (s := (Finset.univ : Finset (Fin K)))
        (g := fun _ => H*H) (fun i _ => Nat.mul_le_mul (h i).2.2.2.1 (h i).2.2.2.2))
    have hb₉ : 9 ≤ B^4 := by
      exact le_trans (by decide : 9 ≤ 2^4) (Nat.pow_le_pow_left hb _)
    calc
      9 * D^3 ≤ B^4 * (H*(H*H)^K)^3 := Nat.mul_le_mul hb₉ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hh) _)
      _ = B^(4+(K^3)*(1+2*K)*3) := by
        dsimp [H]
        simp only [pow_add, pow_one, pow_mul, pow_two]
      _ ≤ B^(13*K^4) := by
        apply Nat.pow_le_pow_right (by omega)
        have hk4 : 1 ≤ K^4 := Nat.one_le_pow _ _ hk
        have h34 : K^3 ≤ K^4 := Nat.pow_le_pow_right hk (by decide)
        nlinarith
  · intro i
    have hd : m i ∣ D := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) H
    exact ⟨(h i).1, (h i).2.1, (h i).2.2.1,
      dvd_trans (dvd_mul_right ..) hd, dvd_trans (dvd_mul_left ..) hd⟩

theorem lower (B : ℕ) (hB : 2 ≤ B)
    (pts : ∀ K : ℕ, 0 < K → ∃ p : Fin K → ℚ × ℚ, Function.Injective p ∧
      ∀ i, 0 ≤ (p i).1 ∧ 0 ≤ (p i).2 ∧ (p i).1^3 + (p i).2^3 = 9 ∧
        (p i).1.den ≤ B^(K^3) ∧ (p i).2.den ≤ B^(K^3)) :
    ∃ C > (0 : ℝ), ∃ᶠ n : ℕ in atTop,
      C * (Real.log n)^(1/4 : ℝ) ≤ (sumRep Erdos829.cubes n : ℝ) := by
  have hlog : 0 < Real.log B := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  let M : ℝ := 13 * Real.log B
  have hM : 0 < M := mul_pos (by norm_num) hlog
  refine ⟨(M^(1/4 : ℝ))⁻¹, by positivity, frequently_atTop.2 ?_⟩
  intro t
  let K := t+1
  have hk : 0 < K := Nat.succ_pos _
  obtain ⟨p, hp, h⟩ := pts K hk
  obtain ⟨n, hkn, hb, hr⟩ := find hk hB p hp h
  refine ⟨n, by omega, ?_⟩
  have hn : (0:ℝ) < n := by exact_mod_cast (hk.trans_le hkn)
  have hl := Real.log_le_log hn (show (n:ℝ) ≤ (B:ℝ)^(13*K^4) by exact_mod_cast hb)
  rw [Real.log_pow] at hl
  have hl' : Real.log n ≤ M*(K:ℝ)^4 := by
    push_cast at hl
    dsimp [M]
    linarith
  have hroot := Real.rpow_le_rpow (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) hl' (by norm_num : (0:ℝ) ≤ 1/4)
  rw [Real.mul_rpow hM.le (by positivity), ← Real.rpow_natCast_mul (by positivity : 0 ≤ (K:ℝ))] at hroot
  norm_num at hroot
  calc
    (M^(1/4 : ℝ))⁻¹ * (Real.log n)^(1/4 : ℝ) ≤ K := by
      rw [inv_mul_eq_div]
      exact (div_le_iff₀ (Real.rpow_pos_of_pos hM _)).2 (by simpa [mul_comm] using hroot)
    _ ≤ (sumRep Erdos829.cubes n : ℝ) := by exact_mod_cast hr

end OMA.Mahler829

/- A finite translation cover of y²=x³−48. No real uniformization is needed
to turn points of controlled height into positive rational cube pairs. -/
namespace OMA.Map829

abbrev Pair := ℚ × ℚ
def On (p : Pair) : Prop := p.2^2 = p.1^3-48
def slope (a b : ℚ) (p : Pair) := (p.2-b)/(p.1-a)
def chord (a b : ℚ) (p : Pair) : Pair :=
  let m := slope a b p
  let u := m^2-p.1-a
  (u, m*(a-u)-b)

private theorem chord_data {a b : ℚ} {p : Pair} (E : On p) (F : b^2=a^3-48)
    (ne : p.1≠a) :
    let m := slope a b p
    let q := chord a b p
    m*(p.1-a) = p.2-b ∧
      2*b*m = (a-q.1)*(p.1-a)+3*a^2 ∧ On q := by
  rcases p with ⟨x,y⟩
  change y^2=x^3-48 at E
  change x≠a at ne
  let m := (y-b)/(x-a)
  let u := m^2-x-a
  change m*(x-a) = y-b ∧ 2*b*m=(a-u)*(x-a)+3*a^2 ∧ (m*(a-u)-b)^2=u^3-48
  have L : m*(x-a)=y-b := div_mul_cancel₀ _ (sub_ne_zero.mpr ne)
  have K : m^2*(x-a)+2*b*m=x^2+a*x+a^2 := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr ne)
    linear_combination (m*(x-a)+b+y)*L + E - F
  have T : 2*b*m=(a-u)*(x-a)+3*a^2 := by dsimp [u]; linear_combination K
  refine ⟨L,T,?_⟩
  dsimp [u]
  linear_combination (m^2-x-2*a)*K + F

theorem chord_on {a b : ℚ} {p : Pair} (E : On p) (F : b^2=a^3-48)
    (ne : p.1≠a) : On (chord a b p) := (chord_data E F ne).2.2

/-- Translation by a fixed point is injective where the affine slope is defined. -/
theorem chord_inj {a b : ℚ} (F : b^2=a^3-48) (bn : b ≠ 0) {p r : Pair}
    (hp : On p) (hr : On r) (pne : p.1≠a) (rne : r.1≠a)
    (eqn : chord a b p=chord a b r) : p=r := by
  let u := (chord a b p).1
  obtain ⟨lp,tp,_⟩ := chord_data hp F pne
  obtain ⟨lr,tr,_⟩ := chord_data hr F rne
  have fx := congrArg Prod.fst eqn
  have fy := congrArg Prod.snd eqn
  change slope a b p*(a-(chord a b p).1)-b=slope a b r*(a-(chord a b r).1)-b at fy
  rw [← fx] at fy tr
  have same : slope a b p=slope a b r := by
    by_cases h : (chord a b p).1=a
    · rw [h, sub_self, zero_mul, zero_add] at tp tr
      exact mul_left_cancel₀ (mul_ne_zero (by norm_num) bn) (tp.trans tr.symm)
    · exact mul_right_cancel₀ (sub_ne_zero.mpr (Ne.symm h)) (sub_left_inj.mp fy)
  change (slope a b p)^2-p.1-a=(slope a b r)^2-r.1-a at fx
  rw [same] at fx lp
  have px : p.1 = r.1 := by linarith
  rw [px] at lp
  exact Prod.ext px (by linarith)

/-- On the middle band translate by (28,148); on the outer band use (4,4). -/
theorem middle {x y : ℚ} (E : y^2=x^3-48) (yn : 0≤y) (low : 11/2≤x) (hi : x≤12) :
    (chord 28 148 (x,y)).1 ≤ 11/2 := by
  have lo : 0≤x-11/2 := by linarith
  have hi' : 0≤12-x := by linarith
  have cert : 0≤592^2*(x^3-48)-(45*x^2+2184*x-8816)^2 := by
    calc
      0 ≤ ((331482375*(12-x)^4 + 2094163200*(x-11/2)*(12-x)^3 +
        3073728000*(x-11/2)^2*(12-x)^2 + 1671397376*(x-11/2)^3*(12-x) +
        302514176*(x-11/2)^4)/28561:ℚ) := by positivity
      _ = _ := by ring
  have linear : 45*x^2+2184*x-8816 ≤ 592*y := by
    by_contra! h
    have bad := mul_self_lt_mul_self (by positivity : 0 ≤ 592*y) h
    nlinarith only [cert,E,bad]
  change ((y-148)/(x-28))^2-x-28 ≤ 11/2
  rw [div_pow]
  have sqp : 0<(x-28)^2 := sq_pos_of_ne_zero (by linarith)
  rw [sub_le_iff_le_add,sub_le_iff_le_add,div_le_iff₀ sqp]
  nlinarith only [linear,E]

theorem outer {x y : ℚ} (E : y^2=x^3-48) (yn : 0≤y) (low : 12≤x) :
    (chord 4 4 (x,y)).1 ≤ 11/2 := by
  have h : 0≤x-12 := by linarith
  have cert : 0 ≤ (x^3-48) - (4*x-8)^2 := by
    calc
      0 ≤ (x-12)^3 + 20*(x-12)^2+112*(x-12)+80 := by positivity
      _ = _ := by ring
  have lin : 4*x-8 ≤ y := by
    by_contra! bad
    nlinarith only [cert,E,mul_self_lt_mul_self yn bad]
  have D : 0≤3*x^2-56*x+240 := by
    calc
      0 ≤ 3*(x-12)^2+16*(x-12) := by positivity
      _ = _ := by ring
  change ((y-4)/(x-4))^2-x-4 ≤ 11/2
  rw [div_pow,sub_le_iff_le_add,sub_le_iff_le_add,div_le_iff₀ (sq_pos_of_ne_zero (by linarith : x-4≠0))]
  nlinarith only [E,lin,D]

end OMA.Map829

/- Injectivity on the six sign-and-translation classes of the finite cover. -/

namespace OMA.Select829

open OMA.Map829

def normal (p : Pair) : Pair := (p.1, |p.2|)
def band (x : ℚ) : Fin 3 := if x ≤ 11/2 then 0 else if x ≤ 12 then 1 else 2
def shift (t : Fin 3) (p : Pair) : Pair :=
  if t=0 then p else if t=1 then chord 28 148 p else chord 4 4 p
def recenter (p : Pair) := shift (band p.1) (normal p)
def cubesOf (p : Pair) : Pair := ((12+p.2)/(2*p.1),(12-p.2)/(2*p.1))
def output (p : Pair) := cubesOf (recenter p)
def tag (p : Pair) : Bool × Fin 3 := (decide (0≤p.2),band p.1)

private theorem positive_x {p : Pair} (E : On p) : 0<p.1 := by
  by_contra! h
  have nonpos : p.1^3 ≤ 0 := by
    rw [pow_succ]; exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) h
  change p.2^2 = p.1^3-48 at E
  linarith [sq_nonneg p.2]

private theorem normal_on {p : Pair} (E : On p) : On (normal p) := by
  simpa [On, normal, sq_abs] using E

theorem cover {p : Pair} (E : On p) : On (recenter p) ∧ (recenter p).1 ≤ 11/2 := by
  have h := normal_on E
  by_cases l : p.1≤11/2
  · simpa [recenter,band,shift,l,normal] using And.intro h l
  by_cases u : p.1≤12
  · have ne : (normal p).1 ≠ 28 := by change p.1≠28; linarith
    have on := (chord_on (a:=28) (b:=148) h (by norm_num) ne)
    have le := middle h (abs_nonneg p.2) (le_of_not_ge l) u
    simpa [recenter,band,shift,l,u,normal] using And.intro on le
  · have ne : (normal p).1 ≠ 4 := by change p.1≠4; linarith
    have on := (chord_on (a:=4) (b:=4) h (by norm_num) ne)
    have le := outer h (abs_nonneg p.2) (le_of_not_ge u)
    simpa [recenter,band,shift,l,u,normal] using And.intro on le

private theorem cubes_pos {p : Pair} (E : On p) (small : p.1≤11/2) :
    0≤(cubesOf p).1 ∧ 0≤(cubesOf p).2 ∧
      (cubesOf p).1^3+(cubesOf p).2^3=9 := by
  have h := positive_x E
  have bound := pow_le_pow_left₀ h.le small 3
  change p.2^2=p.1^3-48 at E
  have low : 0≤12+p.2 := by nlinarith [sq_nonneg (p.2+12)]
  have hi : 0≤12-p.2 := by nlinarith [sq_nonneg (p.2-12)]
  refine ⟨div_nonneg low (by positivity),div_nonneg hi (by positivity),?_⟩
  change ((12+p.2)/(2*p.1))^3+((12-p.2)/(2*p.1))^3=9
  field_simp [h.ne']
  linear_combination 72*E

theorem output_correct {p : Pair} (E : On p) :
    0≤(output p).1 ∧ 0≤(output p).2 ∧ (output p).1^3+(output p).2^3=9 :=
  cubes_pos (cover E).1 (cover E).2

private theorem cubes_inj {p r : Pair} (hp : On p) (hr : On r)
    (eqn : cubesOf p = cubesOf r) : p=r := by
  have hp' := (positive_x hp).ne'
  have hr' := (positive_x hr).ne'
  have a := congrArg Prod.fst eqn
  have b := congrArg Prod.snd eqn
  change (12+p.2)/(2*p.1)=(12+r.2)/(2*r.1) at a
  change (12-p.2)/(2*p.1)=(12-r.2)/(2*r.1) at b
  field_simp [hp',hr'] at a b
  have px : p.1=r.1 := by linarith
  rw [px] at a
  exact Prod.ext px (by apply mul_right_cancel₀ hr'; linarith)

private theorem normal_inj {p r : Pair} (sg : decide (0≤p.2) = decide (0≤r.2))
    (eqn : normal p=normal r) : p=r := by
  have y : |p.2|=|r.2| := congrArg Prod.snd eqn
  have x : (normal p).1 = (normal r).1 := congrArg Prod.fst eqn
  refine Prod.ext x ?_
  by_cases hp : 0≤p.2 <;> by_cases hr : 0≤r.2 <;> simp_all [abs_of_nonneg,abs_of_neg]

private theorem range_middle {x : ℚ} (s : band x=1) : x≤12 := by
  by_contra! h
  simp [band,show ¬x≤11/2 by linarith,not_le.mpr h] at s

private theorem range_outer {x : ℚ} (s : band x=2) : 12<x := by
  by_contra! h
  by_cases hh : x≤11/2 <;> simp [band,hh,h] at s

theorem unique {p r : Pair} (hp : On p) (hr : On r)
    (st : tag p = tag r) (eqn : output p=output r) : p=r := by
  have s : band p.1 = band r.1 := congrArg Prod.snd st
  have sg : decide (0≤p.2) = decide (0≤r.2) := congrArg Prod.fst st
  have sh := cubes_inj (cover hp).1 (cover hr).1 eqn
  change shift (band p.1) (normal p) = shift (band r.1) (normal r) at sh
  apply normal_inj sg
  have cases : band p.1=0 ∨ band p.1=1 ∨ band p.1=2 := by omega
  rcases cases with h|h|h
  · simpa [h,s.symm,shift] using sh
  · apply chord_inj (a:=28) (b:=148) (by norm_num) (by norm_num) (normal_on hp) (normal_on hr)
    · change p.1≠28; linarith [range_middle h]
    · change r.1≠28; linarith [range_middle (s.symm.trans h)]
    · simpa [h,s.symm,shift] using sh
  · apply chord_inj (a:=4) (b:=4) (by norm_num) (by norm_num) (normal_on hp) (normal_on hr)
    · change p.1≠4; linarith [range_outer h]
    · change r.1≠4; linarith [range_outer (s.symm.trans h)]
    · simpa [h,s.symm,shift] using sh

end OMA.Select829

/- Uniform height control for the three rational maps from the Mordell curve to the
sum-of-cubes equation. All estimates also hold at the poles, with Lean's total division. -/
namespace OMA.HeightMap829

private abbrev H (q : ℚ) := max q.num.natAbs q.den
private abbrev Bdd (T d : ℕ) (q : ℚ) := H q ≤ T^d

private lemma mulH (q r : ℚ) : H (q*r) ≤ H q * H r := by
  have h := Height.mulHeight₁_mul_le q r
  simp only [Rat.mulHeight₁_eq_max] at h
  exact_mod_cast h

private lemma addH (q r : ℚ) : H (q+r) ≤ 2 * H q * H r := by
  have h := Height.mulHeight₁_add_le q r
  have wt : Height.totalWeight ℚ = 1 := by simp [NumberField.totalWeight_eq_finrank]
  simp only [wt, pow_one, Rat.mulHeight₁_eq_max] at h
  exact_mod_cast h

private lemma subH (q r : ℚ) : H (q-r) ≤ 2 * H q * H r := by
  have h := Height.mulHeight₁_sub_le q r
  have wt : Height.totalWeight ℚ = 1 := by simp [NumberField.totalWeight_eq_finrank]
  simp only [wt, pow_one, Rat.mulHeight₁_eq_max] at h
  exact_mod_cast h

private lemma invH (q : ℚ) : H q⁻¹ = H q := by
  have h := Height.mulHeight₁_inv q
  simp only [Rat.mulHeight₁_eq_max] at h
  exact_mod_cast h

private lemma bmul {T d e : ℕ} {q r : ℚ} (hq : Bdd T d q) (hr : Bdd T e r) :
    Bdd T (d+e) (q*r) := by
  simpa only [Bdd, pow_add] using (mulH q r).trans (Nat.mul_le_mul hq hr)

private lemma bdiv {T d e : ℕ} {q r : ℚ} (hq : Bdd T d q) (hr : Bdd T e r) :
    Bdd T (d+e) (q/r) := by
  rw [div_eq_mul_inv]
  apply bmul hq
  simpa only [Bdd, invH] using hr

private lemma bsum {T d e : ℕ} {q r : ℚ} (hT : 2 ≤ T)
    (hq : Bdd T d q) (hr : Bdd T e r) :
    Bdd T (1+d+e) (q+r) ∧ Bdd T (1+d+e) (q-r) := by
  have h := Nat.mul_le_mul (Nat.mul_le_mul hT hq) hr
  simpa only [Bdd, pow_add, pow_one] using And.intro ((addH q r).trans h) ((subH q r).trans h)

private lemma widen {T d e : ℕ} {q : ℚ} (hT : 2 ≤ T) (h : Bdd T d q) (he : d ≤ e) :
    Bdd T e q := h.trans (Nat.pow_le_pow_right (by omega) he)

private lemma chordB {T : ℕ} (hT : 2 ≤ T) {x y a b : ℚ}
    (hx : Bdd T 1 x) (hy : Bdd T 1 y) (ha : Bdd T 8 a) (hb : Bdd T 8 b) :
    Bdd T 51 (Map829.chord a b (x,y)).1 ∧ Bdd T 89 (Map829.chord a b (x,y)).2 := by
  let m := (y-b)/(x-a)
  let u := m^2-x-a
  have hm : Bdd T 20 m := bdiv (bsum hT hy hb).2 (bsum hT hx ha).2
  have hm2 : Bdd T 40 (m^2) := by simpa only [sq] using bmul hm hm
  have hu : Bdd T 51 u := (bsum hT (bsum hT hm2 hx).2 ha).2
  exact ⟨hu, (bsum hT (bmul hm (bsum hT ha hu).2) hb).2⟩

theorem bound {T : ℕ} (hT : 2 ≤ T) {x y : ℚ}
    (hx : max x.num.natAbs x.den ≤ T) (hy : max y.num.natAbs y.den ≤ T)
    {q : Map829.Pair} (hq : q = (x, |y|) ∨ q = Map829.chord 4 4 (x, |y|) ∨
      q = Map829.chord 28 148 (x, |y|)) :
    ((12+q.2)/(2*q.1)).den ≤ T^157 ∧ ((12-q.2)/(2*q.1)).den ≤ T^157 := by
  have const {a : ℚ} (h : H a ≤ 2^8) : Bdd T 8 a := h.trans (Nat.pow_le_pow_left hT _)
  have bx : Bdd T 1 x := by simpa [Bdd] using hx
  have by' : Bdd T 1 |y| := by
    rcases abs_choice y with e|e
    · simpa [Bdd, e] using hy
    · simpa [Bdd, e, H] using hy
  obtain ⟨hu, hv⟩ : Bdd T 51 q.1 ∧ Bdd T 89 q.2 := by
    rcases hq with rfl|rfl|rfl
    · exact ⟨widen hT bx (by decide), widen hT by' (by decide)⟩
    · exact chordB hT bx by' (const (by decide)) (const (by decide))
    · exact chordB hT bx by' (const (by decide)) (const (by decide))
  have den := bmul (const (a := 2) (by decide)) hu
  have hh := bsum hT (const (a := 12) (by decide)) hv
  exact ⟨(le_max_right ..).trans (bdiv hh.1 den), (le_max_right ..).trans (bdiv hh.2 den)⟩

end OMA.HeightMap829

/- A finite coloring by sign and translation passes a positive proportion of
the rational points to distinct nonnegative rational cube representations. -/
namespace OMA.Bridge829
open OMA.Map829 OMA.Select829

theorem finish
    (source : ∃ B : ℕ, 2 ≤ B ∧ ∀ k : ℕ, 0 < k → ∃ p : Fin k → Pair,
      Function.Injective p ∧ ∀ i, On (p i) ∧
        max (p i).1.num.natAbs (p i).1.den ≤ B^(k^3) ∧
        max (p i).2.num.natAbs (p i).2.den ≤ B^(k^3))
    (height : ∀ {T : ℕ}, 2≤T → ∀ {p : Pair},
      max p.1.num.natAbs p.1.den ≤ T → max p.2.num.natAbs p.2.den ≤ T →
      (output p).1.den ≤ T^157 ∧ (output p).2.den ≤ T^157) :
    type_of% @Erdos829.variants.mahler := by
  classical
  obtain ⟨B,b,src⟩ := source
  refine OMA.Mahler829.lower (B^33912) ((Nat.le_pow (by norm_num)).trans' b) ?_
  intro k hk
  obtain ⟨p,inj,good⟩ := src (6*k) (by omega)
  let vals := Finset.univ.image fun i => output (p i)
  let f (i : Fin (6*k)) : (Bool × Fin 3) × ↥vals :=
    (tag (p i),⟨output (p i),Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
  have fi : Function.Injective f := by
    intro i j eqn
    apply inj
    have tags := congrArg Prod.fst eqn
    have outs := congrArg (fun a : (Bool×Fin 3)×↥vals => a.2.val) eqn
    exact unique (good i).1 (good j).1 tags outs
  have size := Fintype.card_le_of_injective f fi
  simp only [Fintype.card_fin,Fintype.card_prod,Fintype.card_bool,Fintype.card_coe] at size
  have sk : k ≤ Fintype.card ↥vals := by rw [Fintype.card_coe]; omega
  let e : Fin k ↪ ↥vals := (Fin.castLEEmb sk).trans (Fintype.equivFin ↥vals).symm.toEmbedding
  refine ⟨fun i => (e i).val, (Subtype.val_injective.comp e.injective),?_⟩
  intro i
  obtain ⟨j,_,eqn⟩ := Finset.mem_image.mp (e i).property
  change output (p j) = (e i).val at eqn
  dsimp only
  rw [←eqn]
  have hc := output_correct (good j).1
  have hp := height (T:=B^((6*k)^3)) ((Nat.le_pow (by positivity)).trans' b)
    (good j).2.1 (good j).2.2
  have he : (B^((6*k)^3))^157=(B^33912)^(k^3) := by
    rw [←pow_mul,←pow_mul]; congr 1; ring
  rw [he] at hp
  exact ⟨hc.1,hc.2.1,hc.2.2,hp⟩

end OMA.Bridge829

/- The rational translations all have fixed degree, uniformly in the height of the input. -/
namespace OMA.Mahler829

theorem height_finish (source : ∃ B : ℕ, 2 ≤ B ∧ ∀ k : ℕ, 0<k → ∃ p : Fin k → Map829.Pair,
    Function.Injective p ∧ ∀ i, Map829.On (p i) ∧
    max (p i).1.num.natAbs (p i).1.den ≤ B^(k^3) ∧
    max (p i).2.num.natAbs (p i).2.den ≤ B^(k^3)) : type_of% @Erdos829.variants.mahler := by
  apply OMA.Bridge829.finish source
  intro T hT p hx hy
  apply HeightMap829.bound hT hx hy (q:=Select829.recenter p)
  unfold Select829.recenter Select829.shift
  split_ifs <;> simp [Select829.normal]

end OMA.Mahler829

theorem OMA.solution : type_of% @Erdos829.variants.mahler := OMA.Mahler829.height_finish OMA.Height829.points
