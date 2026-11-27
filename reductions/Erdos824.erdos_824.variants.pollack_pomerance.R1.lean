import FormalConjectures.ErdosProblems.«824»
import Mathlib

/-!
A finite version of the common-factor cancellation in §6 of Pollack and Pomerance,
Some problems of Erdős on the sum-of-divisors function (2016).
For pairs from one fixed divisor-sum fiber, a large intersection is encoded
by one member, a subset of that member and the new primes of the second.
For small intersections, removing the common primes leaves a coprime pair,
and the removed set is the only ambiguity.
-/

open Filter Finset Erdos824
open scoped ArithmeticFunction.sigma
namespace OMA.R_Erdos824_erdos_824_variants_pollack_pomerance_R1

private theorem small_sets (P : Finset ℕ) (t : ℕ) :
    (P.powerset.filter (fun S => S.card ≤ t)).card ≤ (P.card+1)^t := by
  induction t with
  | zero =>
    have hi : P.powerset.filter (fun S => S.card ≤ 0) ⊆ ({∅} : Finset (Finset ℕ)) := by
      intro S hs
      exact mem_singleton.mpr (card_eq_zero.mp (Nat.eq_zero_of_le_zero (mem_filter.mp hs).2))
    simpa using card_le_card hi
  | succ t ih =>
    let F := P.powerset.filter (fun S => S.card ≤ t)
    let U := P.powerset.filter (fun S => S.card ≤ t+1)
    have incl : U ⊆ F ∪ (P ×ˢ F).image (fun w : ℕ × Finset ℕ => insert w.1 w.2) := by
      intro S hS
      obtain ⟨hsub,hsize⟩ := Finset.mem_filter.mp hS
      have hsp := mem_powerset.mp hsub
      by_cases hs : S.card ≤ t
      · exact mem_union_left _ (mem_filter.mpr ⟨hsub,hs⟩)
      · obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
        refine mem_union_right _ (mem_image.mpr ⟨(p,S.erase p),mem_product.mpr ⟨hsp hp,?_⟩,
          Finset.insert_erase hp⟩)
        exact mem_filter.mpr ⟨mem_powerset.mpr ((erase_subset p S).trans hsp),
          by rw [card_erase_of_mem hp]; omega⟩
    calc U.card ≤ _ := card_le_card incl
         _ ≤ F.card + ((P ×ˢ F).image _).card := card_union_le _ _
         _ ≤ F.card + (P ×ˢ F).card := Nat.add_le_add_left card_image_le _
         _ = (P.card+1)*F.card := by rw [card_product]; ring
         _ ≤ (P.card+1)*(P.card+1)^t := Nat.mul_le_mul_left _ ih
         _ = _ := (pow_succ' _ _).symm

private theorem primes_of_product {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    (∏ p ∈ S,p).primeFactors = S := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert p S hp ih =>
    have h := hS p (mem_insert_self ..)
    have hr : ∀ q ∈ S, Nat.Prime q := fun q hq => hS q (mem_insert_of_mem hq)
    rw [prod_insert hp,Nat.primeFactors_mul h.ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun q hq => (hr q hq).ne_zero)), ih hr, h.primeFactors]
    simp

private theorem cancel_count (x d : ℕ) (P : Finset ℕ) (F : Finset (Finset ℕ)) (s : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hF : F ⊆ P.powersetCard (3*d))
    (hs : ∀ S ∈ F, σ 1 (∏ p ∈ S,p) = s) (hx : ∀ S ∈ F, (∏ p ∈ S,p) < x) :
    F.card^2 ≤ F.card*(2^(3*d))*(P.card+1)^(2*d) + (2*h x+1)*(P.card+1)^d := by
  classical
  let val (S : Finset ℕ) := ∏ p ∈ S,p
  let small (t : ℕ) := P.powerset.filter (fun S => S.card ≤ t)
  let pairs := F ×ˢ F
  let bad := pairs.filter (fun z => d < (z.1 ∩ z.2).card)
  let good := pairs.filter (fun z => (z.1 ∩ z.2).card ≤ d)
  have struc (S : Finset ℕ) (h : S ∈ F) := mem_powersetCard.mp (hF h)
  have primes {S : Finset ℕ} (h : S ⊆ P) : ∀ p ∈ S, Nat.Prime p := fun p hp => hP _ (h hp)
  have pos {S : Finset ℕ} (h : S ⊆ P) : 0 < val S := Finset.prod_pos (fun p hp => (hP _ (h hp)).pos)
  have vsplit (A B : Finset ℕ) : val (A \ B)*val (A ∩ B) = val A := by
    dsimp only [val]
    rw [← prod_union (disjoint_sdiff_inter _ _), sdiff_union_inter]
  have cop {S T : Finset ℕ} (hS : S ⊆ P) (hT : T ⊆ P) (hdis : Disjoint S T) :
      (val S).Coprime (val T) := by
    exact Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq =>
      (Nat.coprime_primes (hP _ (hS hp)) (hP _ (hT hq))).mpr
        (fun e => Finset.disjoint_left.mp hdis hp (e ▸ hq))
  have valinj {S T : Finset ℕ} (hS : S ⊆ P) (hT : T ⊆ P) (he : val S = val T) : S=T := by
    exact (primes_of_product (primes hS)).symm.trans
      ((congrArg Nat.primeFactors he).trans (primes_of_product (primes hT)))
  have hbad : bad.card ≤ F.card*(2^(3*d))*(P.card+1)^(2*d) := by
    let C := F.sigma (fun S => S.powerset ×ˢ small (2*d))
    have hb : bad.card ≤ C.card := by
      apply card_le_card_of_injOn
        (fun z : Finset ℕ × Finset ℕ => (⟨z.1,z.1 ∩ z.2,z.2 \ z.1⟩ : Σ _ : Finset ℕ, Finset ℕ × Finset ℕ))
      · rintro ⟨S,T⟩ hz
        obtain ⟨h,hI⟩ := mem_filter.mp hz
        obtain ⟨hS,hT⟩ := mem_product.mp h
        have hsize := card_sdiff_add_card_inter T S
        rw [inter_comm T S] at hsize
        have hTcard := (struc T hT).2
        change d < (S∩T).card at hI
        exact mem_sigma.mpr ⟨hS, mem_product.mpr ⟨mem_powerset.mpr inter_subset_left,
          mem_filter.mpr ⟨mem_powerset.mpr (sdiff_subset.trans (struc T hT).1),by change (T\S).card ≤ 2*d; omega⟩⟩⟩
      · rintro ⟨S,T⟩ _ ⟨U,V⟩ _ he
        have hS := congrArg Sigma.fst he
        have hdata := congrArg (fun w : Σ _ : Finset ℕ, Finset ℕ × Finset ℕ => w.2) he
        change S=U at hS
        subst U
        obtain ⟨h1,h2⟩ := Prod.mk.inj hdata
        have hT : T = V := by
          calc T = (T\S) ∪ (S∩T) := by rw [inter_comm S T,sdiff_union_inter]
               _ = (V\S) ∪ (S∩V) := by rw [h1,h2]
               _ = V := by rw [inter_comm S V,sdiff_union_inter]
        rw [hT]
    have hcard : C.card = F.card*(2^(3*d))*(small (2*d)).card := by
      dsimp only [C]
      rw [card_sigma]
      calc _ = ∑ _S ∈ F, (2^(3*d))*(small (2*d)).card := by
                apply sum_congr rfl; intro S hS; rw [card_product,card_powerset,(struc S hS).2]
           _ = _ := by simp [mul_assoc]
    rw [hcard] at hb
    exact hb.trans (Nat.mul_le_mul_left _ (small_sets _ _))
  let out := ((Ico 1 x) ×ˢ (Ico 1 x)).filter (fun z : ℕ × ℕ =>
    z.1 < z.2 ∧ z.1.Coprime z.2 ∧ σ 1 z.1 = σ 1 z.2)
  let allPairs := (out ∪ out.image Prod.swap) ∪ {(1,1)}
  have htotal : allPairs.card ≤ 2*h x+1 := by
    have ha := card_union_le (out ∪ out.image Prod.swap) ({(1,1)} : Finset (ℕ × ℕ))
    have hb := card_union_le out (out.image Prod.swap)
    have hc : (out.image Prod.swap).card ≤ out.card := card_image_le
    have he : out.card = h x := rfl
    simp only [card_singleton] at ha
    dsimp only [allPairs]
    omega
  have hg : good.card ≤ (2*h x+1)*(P.card+1)^d := by
    have hg' : good.card ≤ (allPairs ×ˢ small d).card := by
      apply card_le_card_of_injOn (fun z : Finset ℕ × Finset ℕ =>
        ((val (z.1\z.2),val (z.2\z.1)),z.1∩z.2))
      · rintro ⟨S,T⟩ hz
        obtain ⟨h,hI⟩ := mem_filter.mp hz
        obtain ⟨hS,hT⟩ := mem_product.mp h
        have hsP := (struc S hS).1
        have htP := (struc T hT).1
        have hU : S\T ⊆ P := sdiff_subset.trans hsP
        have hV : T\S ⊆ P := sdiff_subset.trans htP
        have hD : S∩T ⊆ P := inter_subset_left.trans hsP
        have hc := cop hU hV (by
          rw [Finset.disjoint_left]; intro a ha hb; exact (mem_sdiff.mp ha).2 (mem_sdiff.mp hb).1)
        have hU' := cop hU hD (disjoint_sdiff_inter _ _)
        have hV' := cop hV hD (by rw [inter_comm]; exact disjoint_sdiff_inter _ _)
        have htv : val (T\S)*val (S∩T) = val T := by rw [inter_comm]; exact vsplit T S
        have he : σ 1 (val (S\T)) = σ 1 (val (T\S)) := by
          apply Nat.eq_of_mul_eq_mul_right (ArithmeticFunction.sigma_pos 1 _ (pos hD).ne')
          rw [← ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hU',
            ← ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hV',vsplit S T,htv]
          exact (hs S hS).trans (hs T hT).symm
        have ub : val (S\T) ∈ Ico 1 x := mem_Ico.mpr ⟨pos hU,
          (Nat.le_mul_of_pos_right _ (pos hD)).trans_lt (by rw [vsplit]; exact hx S hS)⟩
        have vb : val (T\S) ∈ Ico 1 x := mem_Ico.mpr ⟨pos hV,
          (Nat.le_mul_of_pos_right _ (pos hD)).trans_lt (by rw [htv]; exact hx T hT)⟩
        refine mem_product.mpr ⟨?_,mem_filter.mpr ⟨mem_powerset.mpr hD,hI⟩⟩
        rcases lt_trichotomy (val (S\T)) (val (T\S)) with hlt|eq|hgt
        · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_product.mpr ⟨ub,vb⟩,hlt,hc,he⟩))
        · have hone : val (T\S) = 1 := by simpa [eq] using hc
          exact mem_union_right _ (mem_singleton.mpr (Prod.ext (eq.trans hone) hone))
        · exact mem_union_left _ (mem_union_right _ (mem_image.mpr
            ⟨(val (T\S),val (S\T)),mem_filter.mpr ⟨mem_product.mpr ⟨vb,ub⟩,hgt,hc.symm,he.symm⟩,rfl⟩))
      · rintro ⟨S,T⟩ hz ⟨U,V⟩ hw eq
        have h1 := mem_product.mp (mem_filter.mp hz).1
        have h2 := mem_product.mp (mem_filter.mp hw).1
        obtain ⟨hv,hd⟩ := Prod.mk.inj eq
        obtain ⟨ha,hb⟩ := Prod.mk.inj hv
        have hs := valinj (sdiff_subset.trans (struc S h1.1).1) (sdiff_subset.trans (struc U h2.1).1) ha
        have ht := valinj (sdiff_subset.trans (struc T h1.2).1) (sdiff_subset.trans (struc V h2.2).1) hb
        apply Prod.ext
        · calc S = (S\T) ∪ (S∩T) := (sdiff_union_inter _ _).symm
               _ = (U\V) ∪ (U∩V) := by rw [hs,hd]
               _ = U := sdiff_union_inter _ _
        · calc T = (T\S) ∪ (S∩T) := by rw [inter_comm S T,sdiff_union_inter]
               _ = (V\U) ∪ (U∩V) := by rw [ht,hd]
               _ = V := by rw [inter_comm U V,sdiff_union_inter]
    rw [card_product] at hg'
    exact hg'.trans (Nat.mul_le_mul htotal (small_sets P d))
  have cover : pairs ⊆ bad ∪ good := by
    intro z hz
    by_cases hI : d < (z.1∩z.2).card
    · exact mem_union_left _ (mem_filter.mpr ⟨hz,hI⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hz,by omega⟩)
  have hcard := (card_le_card cover).trans (card_union_le bad good)
  change (F ×ˢ F).card ≤ _ at hcard
  rw [card_product, ← sq] at hcard
  exact hcard.trans (Nat.add_le_add hbad hg)

/-- Encode each smooth integer by the bounded list of its prime exponents. -/
private theorem smooth_values (N b : ℕ) :
    ((Icc 1 N).filter (fun u => ∀ q ∈ u.primeFactors, q ≤ b)).card ≤
      (Nat.log 2 N+2)^(b+1) := by
  classical
  let L := Nat.log 2 N+2
  have hL : 0 < L := by dsimp [L]; omega
  let code (u : ℕ) (i : Fin (b+1)) : Fin L := ⟨u.factorization i % L,Nat.mod_lt _ hL⟩
  have bound (u p : ℕ) (hu : u ≤ N) : u.factorization p < L := by
    by_cases pp : p.Prime
    · have he : u ≤ p^(Nat.log 2 N+1) :=
        hu.trans ((Nat.lt_pow_succ_log_self (by decide : 1 < 2) N).le.trans
          (Nat.pow_le_pow_left pp.two_le _))
      have hf := Nat.factorization_le_of_le_pow he
      dsimp only [L]
      omega
    · rwa [Nat.factorization_eq_zero_of_not_prime u pp]
  let V := (Icc 1 N).filter (fun u => ∀ q ∈ u.primeFactors, q ≤ b)
  have hc : V.card ≤ (univ : Finset (Fin (b+1) → Fin L)).card := by
    apply card_le_card_of_injOn code (fun _ _ => mem_univ _)
    intro u hu v hv eq
    obtain ⟨hu,huf⟩ := mem_filter.mp hu
    obtain ⟨hv,hvf⟩ := mem_filter.mp hv
    obtain ⟨hu0,huN⟩ := mem_Icc.mp hu
    obtain ⟨hv0,hvN⟩ := mem_Icc.mp hv
    apply Nat.eq_of_factorization_eq (by omega) (by omega)
    intro p
    by_cases hpb : p ≤ b
    · let i : Fin (b+1) := ⟨p,by omega⟩
      have hh := congrArg Fin.val (congrFun eq i)
      change u.factorization p % L = v.factorization p % L at hh
      simpa only [Nat.mod_eq_of_lt (bound u p huN),Nat.mod_eq_of_lt (bound v p hvN)] using hh
    · have hpu : p ∉ u.factorization.support := fun hm => hpb (huf p hm)
      have hpv : p ∉ v.factorization.support := fun hm => hpb (hvf p hm)
      rw [Finsupp.notMem_support_iff.mp hpu,Finsupp.notMem_support_iff.mp hpv]
  simpa [V,L] using hc

/-- A fixed smooth-successor estimate, weaker than the exponent in Baker and Harman. -/
def H1 : Prop := ∀ᶠ y : ℕ in atTop, ∃ P : Finset ℕ, y^129 ≤ P.card^10 ∧
  ∀ p ∈ P, p.Prime ∧ p ≤ y^13 ∧ ∀ q ∈ (p+1).primeFactors, q ≤ y^4

/-- Numerical scale selection. M is the required size of a single divisor-sum fiber.
All quantities here are ordinary integers, independent of the primes themselves. -/
def H2 : Prop := ∀ K Y : ℕ, ∀ᶠ x : ℕ in atTop, ∃ y d : ℕ, Y ≤ y ∧ y^4 ≤ Nat.log 2 x ∧
  (y^13)^(3*d) < x ∧ ∀ n : ℕ, n ≤ y^13 → y^129 ≤ n^10 → ∃ M : ℕ,
    ((Nat.log 2 (x^2)+2)^(y^4+1))*M ≤ n.choose (3*d) ∧
      2*2^(3*d)*(n+1)^(2*d) < M ∧ 2*(2*K*x+1)*(n+1)^d < M^2

theorem main : H1 → H2 → type_of% @Erdos824.erdos_824.variants.pollack_pomerance := by
  classical
  intro supply scales
  obtain ⟨Y,hY⟩ := eventually_atTop.1 supply
  apply tendsto_atTop.2
  intro b
  obtain ⟨K,hK⟩ := exists_nat_ge b
  filter_upwards [scales K Y, eventually_ge_atTop 2] with x hsc hx
  obtain ⟨y,d,hy,hlog,hxsize,hC⟩ := hsc
  obtain ⟨P,hsupply,hP⟩ := hY y hy
  have hp : ∀ p ∈ P, Nat.Prime p := fun p h => (hP p h).1
  have hN : P.card ≤ y^13 := by
    have hi : P ⊆ Icc 1 (y^13) := fun p h => mem_Icc.mpr ⟨(hp p h).pos,(hP p h).2.1⟩
    simpa using card_le_card hi
  obtain ⟨M,hM,hbig1,hbig2⟩ := hC _ hN hsupply
  let T := P.powersetCard (3*d)
  let V := (Icc 1 (x^2)).filter (fun u => ∀ q ∈ u.primeFactors, q ≤ y^4)
  have hbound := smooth_values (x^2) (y^4)
  let g (S : Finset ℕ) := σ 1 (∏ p ∈ S,p)
  have size (S : Finset ℕ) (hS : S ∈ T) : (∏ p ∈ S,p) < x := by
    obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hS
    refine lt_of_le_of_lt (Finset.prod_le_prod' (g := fun _ : ℕ => y^13) (fun p h => (hP p (hsub h)).2.1)) ?_
    simpa [hcard] using hxsize
  have maps (S : Finset ℕ) (hS : S ∈ T) : g S ∈ V := by
    obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hS
    have hsig : g S = ∏ p ∈ S,(p+1) := by
      dsimp only [g]
      rw [ArithmeticFunction.isMultiplicative_sigma.map_prod_of_prime S (fun p h => hp p (hsub h))]
      apply prod_congr rfl
      intro p h
      simpa [Finset.sum_range_succ,add_comm] using
        (ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) (hp p (hsub h)))
    rw [hsig]
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Finset.prod_pos (fun p _ => Nat.succ_pos p),?_⟩,?_⟩
    · calc (∏ p ∈ S,(p+1)) ≤ ∏ p ∈ S,p^2 := Finset.prod_le_prod' (fun p h => by
             have hh := (hp p (hsub h)).two_le
             nlinarith [Nat.mul_le_mul_left p hh])
           _ = (∏ p ∈ S,p)^2 := Finset.prod_pow _ _ _
           _ ≤ x^2 := Nat.pow_le_pow_left (size S hS).le _
    · intro q hq
      obtain ⟨p,hpS,hd⟩ := (Nat.prime_of_mem_primeFactors hq).prime.dvd_finsetProd_iff
        (fun p : ℕ => p+1) |>.mp (Nat.dvd_of_mem_primeFactors hq)
      exact (hP p (hsub hpS)).2.2 q (Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primeFactors hq,hd,Nat.succ_ne_zero _⟩)
  have hV : V.Nonempty := ⟨1,mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl,Nat.succ_le_of_lt
    (pow_pos (show 0<x by omega) 2)⟩,by simp⟩⟩
  have hm : V.card*M ≤ T.card := by
    rw [show T.card = P.card.choose (3*d) from card_powersetCard _ _]
    exact (Nat.mul_le_mul_right M hbound).trans hM
  obtain ⟨s,_,hfib⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to maps hV hm
  let F := T.filter (fun S => g S = s)
  have hF : M ≤ F.card := hfib
  have hh := cancel_count x d P F s hp (Finset.filter_subset _ _)
    (fun S h => (mem_filter.mp h).2) (fun S h => size S (mem_filter.mp h).1)
  have hlarge : K*x < h x := by
    by_contra! ha
    have h1 : 2*(2^(3*d)*(P.card+1)^(2*d)) < F.card := by simpa only [mul_assoc] using hbig1.trans_le hF
    have h2 : 2*((2*h x+1)*(P.card+1)^d) < F.card^2 := by
      have hmul := Nat.mul_le_mul_right ((P.card+1)^d) (show 2*h x+1 ≤ 2*K*x+1 by simpa only [mul_assoc] using Nat.add_le_add_right (Nat.mul_le_mul_left 2 ha) 1)
      nlinarith only [hmul,hbig2,Nat.pow_le_pow_left hF 2]
    have hfpos : 0 < F.card := by omega
    have h3 := Nat.mul_lt_mul_of_pos_left h1 hfpos
    nlinarith only [hh,h2,h3]
  exact hK.trans ((le_div_iff₀ (by exact_mod_cast (show 0 < x by omega))).mpr
    (by exact_mod_cast hlarge.le))

end OMA.R_Erdos824_erdos_824_variants_pollack_pomerance_R1
