import OMAReductions.R_Erdos308_erdos_308_variants_croot_R1_H1_R1
import Mathlib

/-!
# Cheap cancellation of the small and medium prime powers

Adapted the lcm-grid divisibility observations from @marcusbuffett
in open-math-agents PR 5072. The cancellation argument follows
Ernest S. Croot III, On some questions of Erdős and Graham about Egyptian
fractions. In a small layer, removing one denominator costs at most the
difference of the reciprocals of the two lcm values. In a medium layer of
index i = p^k, an inverse-residue pigeonhole argument supplies at most two
denominators of size at least i²/16. Their cost is dominated by a telescoping
tail starting at a constant multiple of log N.
Credit: @marcusbuffett.
-/

section
open Finset Nat
open scoped Classical
namespace Egyptian

lemma ongrid {m i : ℕ} (hm : 0 < m) (hmi : m ≤ i) : m ∣ lcmUpto i :=
  Finset.dvd_lcm (f := id) (mem_Icc.mpr ⟨hm,hmi⟩)

lemma unchanged {i : ℕ} (hi : 1 < i) (h : ¬ IsPrimePow i) :
    lcmUpto i = lcmUpto (i-1) := by
  have nz : i ≠ 0 := by omega
  have last : i ∣ lcmUpto (i-1) := by
    apply (Nat.factorization_prime_le_iff_dvd nz (lcmUpto_ne_zero _)).mp
    intro p hp
    apply (hp.pow_dvd_iff_le_factorization (lcmUpto_ne_zero _)).mp
    have hd := (hp.pow_dvd_iff_le_factorization nz).mpr (le_refl (i.factorization p))
    apply ongrid (pow_pos hp.pos _)
    have hl := Nat.le_of_dvd (by omega : 0 < i) hd
    by_contra! hf
    have eq : p ^ i.factorization p = i := by omega
    have he : 0 < i.factorization p := by
      by_contra! e
      simp [Nat.eq_zero_of_le_zero e] at eq
      omega
    exact h ((isPrimePow_nat_iff _).mpr ⟨p,_,hp,he,eq⟩)
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro n hn
    obtain ⟨hn,hle⟩ := mem_Icc.mp hn
    by_cases e : n = i
    · simpa [e] using last
    · exact ongrid (m := n) hn (by omega)
  · apply Finset.lcm_dvd
    intro n hn
    exact ongrid (m := n) (mem_Icc.mp hn).1 (by have := (mem_Icc.mp hn).2; omega)

lemma complement {i : ℕ} (hi : IsPrimePow i) :
    i.Coprime (lcmUpto i / i) := by
  obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff _).mp hi
  apply (hp.coprime_iff_not_dvd.mpr ?_).pow_left
  have hi := pow_pos hp.pos k
  have dvd := ongrid hi le_rfl
  have nz : lcmUpto (p^k) / p^k ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (lcmUpto_pos _) dvd) hi)
  intro h
  have hf := hp.factorization_pos_of_dvd nz h
  rw [Nat.factorization_div dvd] at hf
  simpa [Finsupp.coe_tsub, factorization_lcmUpto _ hp, Nat.log_pow hp.one_lt, hp.factorization_pow] using hf

end Egyptian

namespace Mid308
abbrev J := Nat.lcmUpto
def layer (N i : ℕ) := (Icc 1 N).filter fun n => n∣J i ∧ ¬n∣J (i-1)
def desc (N i : ℕ) (c : ℚ) : Prop := ∀ z : ℤ, ∃ V ⊆ layer N i,
  (∑ n ∈ V,(1:ℚ)/n) ≤ c ∧ ∃ b : ℤ, (b:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V,(1:ℚ)/n

lemma pp_not_prev {p k i : ℕ} (hp : p.Prime) (hk : 0<k) (eqi : p^k=i) :
    ¬i∣J (i-1) := by
  have hi := (isPrimePow_nat_iff _).mpr ⟨p,k,hp,hk,eqi⟩ |>.one_lt
  intro h
  have h' := (hp.pow_dvd_iff_le_factorization (lcmUpto_ne_zero (i-1))).mp (eqi ▸ h : p^k∣J (i-1))
  rw [factorization_lcmUpto _ hp] at h'
  have lt := Nat.log_lt_of_lt_pow (b:=p) (x:=k) (y:=i-1) (by omega) (by omega)
  omega

lemma jump {p k i : ℕ} (hp : p.Prime) (hk : 0<k) (eqi : p^k=i) :
    J i = p*J (i-1) := by
  have hi := (isPrimePow_nat_iff _).mpr ⟨p,k,hp,hk,eqi⟩ |>.one_lt
  have on := Egyptian.ongrid (m:=i) (by omega) le_rfl
  have d1 : J (i-1) ∣ J i := by
    apply Finset.lcm_dvd
    intro a ha
    change a ∣ J i
    exact Egyptian.ongrid (mem_Icc.mp ha).1 (by have := (mem_Icc.mp ha).2;omega)
  obtain ⟨g,hg⟩ := d1
  have div : J i ∣ p*J (i-1) := by
    apply Finset.lcm_dvd
    intro a ha
    obtain ⟨hl,hu⟩ := mem_Icc.mp ha
    by_cases e : a=i
    · subst a
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      have hlo := pow_pos hp.pos j
      have hlt : p^j < i := by rw [←eqi,pow_succ]; nlinarith [Nat.mul_le_mul_left (p^j) hp.two_le]
      have hdiv := Egyptian.ongrid hlo (show p^j ≤ i-1 by omega)
      simpa [←eqi,pow_succ, Nat.mul_comm] using Nat.mul_dvd_mul_left p hdiv
    · exact dvd_trans (Egyptian.ongrid hl (show a ≤ i-1 by omega)) (dvd_mul_left _ _)
  have hgdiv : g∣p := by
    rw [hg, Nat.mul_comm p] at div
    exact (Nat.mul_dvd_mul_iff_left (lcmUpto_pos _)).mp div
  rcases (Nat.dvd_prime hp).mp hgdiv with he | he
  · simp only [he,mul_one] at hg
    exact False.elim (pp_not_prev hp hk eqi (hg ▸ on))
  · rw [hg,he,Nat.mul_comm]

lemma empty_step {N i : ℕ} (hi : 1 < i) (h : ¬IsPrimePow i) :
    desc N i 0 := by
  intro z
  exact ⟨∅,empty_subset _,by simp,z,by simp [Egyptian.unchanged hi h]⟩

/-- Cancel a numerator modulo the new prime when passing between the two lcm grids. -/
lemma descent {p i : ℕ} (hp : p.Prime) (hj : J i=p*J (i-1)) (z : ℤ)
    (V : Finset ℕ) (hV : ∀ n ∈ V, 0<n ∧ n∣J i)
    (hz : ((z:ZMod p) - ∑ n ∈ V, ((J i/n:ℕ):ZMod p))=0) :
    ∃ b : ℤ, (b:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V,(1:ℚ)/n := by
  have hh : (((z - ∑ n ∈ V, ((J i/n:ℕ):ℤ)):ℤ):ZMod p)=0 := by simpa only [Int.cast_sub,Int.cast_sum,Int.cast_natCast] using hz
  obtain ⟨b,hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hh
  refine ⟨b,?_⟩
  have rat (n : ℕ) (hn : n∈V) : (1:ℚ)/n = ((J i/n:ℕ):ℚ)/J i := by
    apply (div_eq_div_iff (by exact_mod_cast (hV n hn).1.ne') (by exact_mod_cast lcmUpto_ne_zero i)).mpr
    rw [one_mul]; exact_mod_cast (Nat.div_mul_cancel (hV n hn).2).symm
  rw [sum_congr rfl rat, ←sum_div, ←sub_div]
  have er : (z:ℚ) - ∑ n ∈ V, ((J i/n:ℕ):ℚ) = (p:ℚ)*b := by simpa only [Int.cast_sub,Int.cast_sum,Int.cast_natCast,Int.cast_mul] using congrArg (Int.cast : ℤ → ℚ) hb
  rw [er,hj,Nat.cast_mul]
  field_simp [show (p:ℚ) ≠ 0 by exact_mod_cast hp.ne_zero] <;> ring

lemma small {N i : ℕ} (hi : 1 < i) (hN : J i≤N) :
    desc N i ((1:ℚ)/J (i-1)-1/J i) := by
  by_cases pow : IsPrimePow i
  · obtain ⟨p,k,hp,hk,eqi⟩ := (isPrimePow_nat_iff _).mp pow
    letI : Fact p.Prime := ⟨hp⟩
    have hj := jump hp hk eqi
    have p_le : p ≤ i := by rw [←eqi]; exact Nat.le_self_pow hk.ne' _
    intro z
    let u := (z:ZMod p).val
    have hu : u<p := ZMod.val_lt _
    have hval : (u:ZMod p) = z := ZMod.natCast_zmod_val _
    have hj' : (J i:ℚ)=(p:ℚ)*J (i-1) := by exact_mod_cast hj
    have hcost : (1:ℚ)/J (i-1)-1/J i = ((p:ℚ)-1)/J i := by
      rw [hj']; field_simp [show (p:ℚ) ≠ 0 by exact_mod_cast hp.ne_zero, show (J (i-1):ℚ) ≠ 0 by exact_mod_cast lcmUpto_ne_zero _] <;> ring
    rw [hcost]
    by_cases hz : u=0
    · refine ⟨∅,empty_subset _,?_,descent hp hj z ∅ (by simp) (by simpa [hz] using hval.symm)⟩
      simp only [sum_empty]; apply div_nonneg (sub_nonneg.mpr (by exact_mod_cast hp.one_le)) (by positivity)
    · have hdu := Egyptian.ongrid (show 0<u by omega) (show u ≤ i-1 by omega)
      let n := J i/u
      have du : u∣J i := dvd_trans hdu (hj ▸ dvd_mul_left _ _)
      have hnu : n*u=J i := Nat.div_mul_cancel du
      have hn : 0<n := Nat.div_pos (Nat.le_of_dvd (lcmUpto_pos _) du) (by omega)
      have hnJ : n∣J i := ⟨u,hnu.symm⟩
      have hnot : ¬n∣J (i-1) := by
        intro hd
        obtain ⟨v,hv⟩ := hd
        have eq : n*u=n*(p*v) := by rw [hnu,hj,hv];ring
        have e := Nat.eq_of_mul_eq_mul_left hn eq
        exact ((Nat.le_of_dvd (show 0<u by omega) (show p∣u from ⟨v,e⟩))).not_gt hu
      have hmem : n∈layer N i := mem_filter.mpr
        ⟨mem_Icc.mpr ⟨hn,(Nat.le_of_dvd (lcmUpto_pos _) hnJ).trans hN⟩,hnJ,hnot⟩
      have inv : J i/n=u := by rw [←hnu];simp [hn.ne']
      refine ⟨{n},singleton_subset_iff.mpr hmem,?_,descent hp hj z {n} (by simpa using And.intro hn hnJ) ?_⟩
      · simp only [sum_singleton]
        have mass : (1:ℚ)/n = u/J i := by
          apply (div_eq_div_iff (by exact_mod_cast hn.ne') (by exact_mod_cast lcmUpto_ne_zero i)).mpr
          rw [one_mul];exact_mod_cast (show J i=u*n by simpa [Nat.mul_comm] using hnu.symm)
        rw [mass]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have h' : (u:ℚ)+1 ≤ p := by exact_mod_cast hu
        linarith
      · simp [inv,hval]
  · simpa [Egyptian.unchanged hi pow] using empty_step (N:=N) hi pow
end Mid308
end

section
open Finset Nat
open scoped Classical
namespace Mid308

/-- Every residue modulo p is a sum of at most two distinct inverse residues
whose positive representatives are at least p/16. -/
lemma residues {p : ℕ} (hp : p.Prime) (w : ZMod p) :
    ∃ U : Finset ℕ, U.card ≤ 2 ∧ (∀ u ∈ U, 0<u ∧ u<p ∧ p≤16*u) ∧
      (∑ u ∈ U, (u:ZMod p)⁻¹) = w := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hw : w=0
  · exact ⟨∅,by simp,by simp,by simpa using hw.symm⟩
  by_cases hs : p≤16
  · let u := (w⁻¹).val
    have hu : (u:ZMod p) = w⁻¹ := ZMod.natCast_zmod_val _
    have hu0 : 0<u := by
      by_contra! h
      have h' : u=0 := by omega
      simp [h'] at hu
      exact hw hu.symm
    refine ⟨{u},by simp,?_,by simp [hu]⟩
    simpa using And.intro hu0 (And.intro (ZMod.val_lt (w⁻¹)) (show p≤16*u by omega))
  let B := Ico (p/16+1) p
  let f : ℕ → ZMod p := fun u => (u:ZMod p)⁻¹
  have ib : Set.InjOn f (B : Set ℕ) := by
    intro u hu v hv hh
    have hvv := congrArg ZMod.val (inv_injective hh : (u:ZMod p)=v)
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_Ico.mp hu).2,Nat.mod_eq_of_lt (mem_Ico.mp hv).2] using hvv
  let S := B.image f
  have sc : S.card = p-(p/16+1) := by
    rw [show S = B.image f by rfl,Finset.card_image_of_injOn ib]; exact Nat.card_Ico _ _
  let T := S.erase (w/2)
  let g : ZMod p → ZMod p := fun u => w-u
  have gc : (T.image g).card=T.card := card_image_of_injective _ (by intro u v h;exact sub_right_injective h)
  have nd : ¬Disjoint T (T.image g) := by
    intro dis
    have cnt := (T ∪ T.image g).card_le_univ
    rw [card_union_of_disjoint dis,gc,ZMod.card] at cnt
    have hh : S.card ≤ T.card+1 := by
      by_cases h : w/2∈S
      · simp [T,card_erase_of_mem h];have := card_pos.mpr ⟨_,h⟩;omega
      · simp [T,h]
    omega
  obtain ⟨u,hu,hg⟩ := not_disjoint_iff.mp nd
  obtain ⟨v,hv,hev⟩ := mem_image.mp hg
  obtain ⟨hne,huS⟩ := mem_erase.mp hu
  have hvS := (mem_erase.mp hv).2
  have hp2 : (2:ZMod p)≠0 := by
    have hn := ZMod.natCast_eq_zero_iff (a:=2) (b:=p)
    change ((2:ℕ):ZMod p)≠0
    intro hh
    have := Nat.le_of_dvd (by decide : 0<2) (hn.mp hh)
    omega
  have huv : u≠v := by
    intro e
    apply hne
    apply (eq_div_iff hp2).mpr
    dsimp [g] at hev
    rw [←e] at hev
    linear_combination -hev
  obtain ⟨a,ha,ea⟩ := mem_image.mp huS
  obtain ⟨b,hb,eb⟩ := mem_image.mp hvS
  have hab : a≠b := fun e => huv (by simpa [←ea,←eb,e])
  have good {n : ℕ} (hn : n∈B) : 0<n ∧ n<p ∧ p≤16*n := by
    obtain ⟨h0,hp⟩ := mem_Ico.mp hn
    omega
  refine ⟨{a,b},by simp [hab],?_,?_⟩
  · intro n hn
    rcases mem_insert.mp hn with rfl | hn
    · exact good ha
    · exact (mem_singleton.mp hn) ▸ good hb
  · rw [sum_insert (by simpa using hab),sum_singleton]
    change f a+f b=w
    rw [ea,eb,←hev];simp [g]
end Mid308
end

section
open Finset Nat
open scoped Classical
namespace Mid308

lemma medium {N i : ℕ} (hi : 1 < i) (hn : i*i≤N) : desc N i (32 / (i:ℚ)^2) := by
  classical
  by_cases hpow : IsPrimePow i
  · obtain ⟨p,k,hp,hk,eqi⟩ := (isPrimePow_nat_iff _).mp hpow
    letI : Fact p.Prime := ⟨hp⟩
    have hi0 : 0 < i := by omega
    have pi : p∣i := eqi ▸ dvd_pow_self p hk.ne'
    have ple := Nat.le_of_dvd hi0 pi
    let D := J i/i
    have di : i*D=J i := Nat.mul_div_cancel' (Egyptian.ongrid hi0 le_rfl)
    have cop := Egyptian.complement hpow
    have pD : p.Coprime D := cop.coprime_dvd_left pi
    have dp : (D:ZMod p)≠0 := fun e => hp.coprime_iff_not_dvd.mp pD ((ZMod.natCast_eq_zero_iff _ _).mp e)
    intro z
    obtain ⟨U,hcard,hU,hsum⟩ := residues hp ((z:ZMod p)*(D:ZMod p)⁻¹)
    let m (u : ℕ) := i-p+u
    let g (u : ℕ) := i*m u
    let V := U.image g
    have inj : Function.Injective g := by intro a b e; have hh := Nat.eq_of_mul_eq_mul_left hi0 e; exact Nat.add_left_cancel hh
    have castm (u : ℕ) : (m u : ZMod p)=(u:ZMod p) := by
      dsimp [m]; rw [Nat.cast_add,Nat.cast_sub ple,(ZMod.natCast_eq_zero_iff _ _).mpr pi,ZMod.natCast_self]; ring
    have facts (u : ℕ) (hu : u∈U) : 0 < m u ∧ m u ≤ i ∧ i.Coprime (m u) ∧ i≤16*m u := by
      obtain ⟨u0,up,hu'⟩ := hU u hu
      have mc : p.Coprime (m u) := hp.coprime_iff_not_dvd.mpr (by
        intro h
        have := (ZMod.natCast_eq_zero_iff _ _).mpr h
        rw [castm] at this
        exact up.not_ge (Nat.le_of_dvd u0 ((ZMod.natCast_eq_zero_iff _ _).mp this)))
      refine ⟨by dsimp [m];omega,by dsimp [m];omega,eqi ▸ mc.pow_left k,by dsimp [m];omega⟩
    have dvd (u : ℕ) (hu : u∈U) : g u∣J i := by
      obtain ⟨hm,hmi,hcop,-⟩ := facts u hu
      exact hcop.mul_dvd_of_dvd_of_dvd (Egyptian.ongrid hi0 le_rfl) (Egyptian.ongrid hm hmi)
    have on (u : ℕ) (hu : u∈U) : g u∈layer N i := by
      obtain ⟨hm,hmi,-,-⟩ := facts u hu
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hi0 hm,(Nat.mul_le_mul_left i hmi).trans hn⟩,dvd u hu,?_⟩
      intro h
      exact pp_not_prev hp hk eqi (dvd_trans (dvd_mul_right i (m u)) h)
    have sub : V ⊆ layer N i := by simpa [V,image_subset_iff] using on
    refine ⟨V,sub,?_,descent hp (jump hp hk eqi) z V (fun n h => ⟨(mem_Icc.mp (mem_filter.mp (sub h)).1).1,(mem_filter.mp (sub h)).2.1⟩) ?_⟩
    · have each (u : ℕ) (hu : u∈U) : (1:ℚ)/g u ≤ 16/(i:ℚ)^2 := by
        obtain ⟨hm,-,-,bound⟩ := facts u hu
        have i0 : (0:ℚ) < i := by exact_mod_cast hi0
        have m0 : (0:ℚ) < m u := by exact_mod_cast hm
        dsimp only [g]; rw [Nat.cast_mul, div_le_div_iff₀ (mul_pos i0 m0) (by positivity)]
        have := mul_le_mul_of_nonneg_left (show (i:ℚ)≤16*(m u:ℚ) by exact_mod_cast bound) i0.le
        nlinarith
      dsimp only [V]; rw [sum_image (fun _ _ _ _ h => inj h)]
      calc
        _ ≤ ∑ _u ∈ U, (16:ℚ)/(i:ℚ)^2 := sum_le_sum each
        _ = (U.card:ℚ)*(16/(i:ℚ)^2) := by simp
        _ ≤ 2*(16/(i:ℚ)^2) := by gcongr;exact_mod_cast hcard
        _ = _ := by ring
    · dsimp only [V]; rw [sum_image (fun _ _ _ _ h => inj h)]
      have coef (u : ℕ) (hu : u∈U) : ((J i/g u : ℕ):ZMod p) = (D:ZMod p)*(u:ZMod p)⁻¹ := by
        have um := hU u hu
        have un : (u:ZMod p)≠0 := fun h => um.2.1.not_ge (Nat.le_of_dvd um.1 ((ZMod.natCast_eq_zero_iff _ _).mp h))
        apply (eq_mul_inv_iff_mul_eq₀ un).mpr
        rw [←castm u,←Nat.cast_mul]
        apply congrArg (Nat.cast : ℕ → ZMod p)
        apply Nat.eq_of_mul_eq_mul_left hi0
        calc
          _ = (J i/g u)*(g u) := by dsimp [g];ring
          _ = J i := Nat.div_mul_cancel (dvd u hu)
          _ = _ := di.symm
      rw [sum_congr rfl coef,←mul_sum,hsum]
      field_simp <;> ring
  · have zero := empty_step (N:=N) hi hpow
    intro z
    obtain ⟨V,hV,bound,hz⟩ := zero z
    exact ⟨V,hV,bound.trans (by positivity),hz⟩
end Mid308
end

section
open Finset Filter Real
open scoped Classical
namespace Mid308

lemma lcm_small {i N : ℕ} (hn : 0<N) (hi : (i:ℝ) ≤ log N/10) : J i ≤ N := by
  have bound := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α:=ℝ) i)
  rw [Chebyshev.psi_eq_log_lcmUpto] at bound
  have h4 := Real.log_le_sub_one_of_pos (show (0:ℝ)<4 by norm_num)
  have h : log (J i:ℝ) ≤ log N := by
    change log (J i : ℝ) ≤ _ at bound
    nlinarith [mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg (α:=ℝ) i)]
  exact_mod_cast (Real.log_le_log_iff (by exact_mod_cast Nat.lcmUpto_pos i) (by exact_mod_cast hn)).mp h

def F (L j : ℕ) : ℚ := 1/(J (min L j):ℚ) + 32/(max L j:ℕ)

lemma telescope (L m : ℕ) (hm : 1 ≤ m) :
    ∑ i ∈ Ioc 1 m, (F L (i-1)-F L i) = F L 1-F L m := by
  induction m,hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hs : Ioc 1 (m+1) = insert (m+1) (Ioc 1 m) := by ext j;simp;omega
    rw [hs,sum_insert (by simp), Nat.add_one_sub_one,ih];ring

lemma total : OMA.R_Erdos308_erdos_308_variants_croot_R1_H1_R1.H2 := by
  intro ε hε
  have ht : Tendsto (fun N : ℕ => log (N:ℝ)) atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll := (tendsto_log_atTop.comp ht).eventually_ge_atTop (640/ε+1)
  filter_upwards [ht.eventually_ge_atTop 40,hll,eventually_ge_atTop 2] with N hlog hlarge hN
  change 40 ≤ log (N:ℝ) at hlog
  change 640/ε+1 ≤ log (log N) at hlarge
  let L := ⌊log N/10⌋₊
  have hln := Nat.lt_floor_add_one (log (N:ℝ)/10)
  change log (N:ℝ)/10 < (L:ℝ)+1 at hln
  have hL0 : (0:ℝ)<L := by linarith
  have hL : 1≤L := by exact_mod_cast hL0
  have hs : 1≤N.sqrt := (Nat.sqrt_pos.mpr (by omega))
  refine ⟨fun i => F L (i-1)-F L i,?_,?_⟩
  · dsimp only
    rw [telescope L _ hs]
    have hf : 0≤F L N.sqrt := by dsimp [F]; positivity
    have hF : F L 1 = 1+32/(L:ℚ) := by simp [F, min_eq_right hL,max_eq_left hL,J,Nat.lcmUpto]
    have hn := sub_le_self (F L 1) hf
    rw [hF] at hn
    have hr : ((F L 1 - F L N.sqrt:ℚ):ℝ) ≤ 1+32/(L:ℝ) := by
      calc
        _ ≤ ((1+32/(L:ℚ):ℚ):ℝ) := (Rat.cast_le (K:=ℝ)).mpr (hF ▸ hn)
        _ = _ := by push_cast; rfl
    apply hr.trans
    apply add_le_add_right
    have hpos : 0<log (N:ℝ) := by linarith
    have big : 640≤ε*log (log N) := by
      have := (div_le_iff₀ hε).mp (show 640/ε ≤ log (log N) by linarith)
      linarith
    have one : 1≤log (log N) := by
      have hh : 0≤640/ε := by positivity
      linarith
    have big2 : 640≤ε*(log (log N))^2 := by nlinarith [mul_le_mul_of_nonneg_right one (show 0≤ε*log (log N) by linarith)]
    rw [div_le_div_iff₀ hL0 hpos]
    nlinarith only [mul_le_mul_of_nonneg_right big2 hL0.le,hln,hlog]
  · intro i hi z
    dsimp only
    obtain ⟨hil,hiu⟩ := mem_Ioc.mp hi
    by_cases h : i≤L
    · have il : (i:ℝ)≤log N/10 := (Nat.cast_le.mpr h).trans (Nat.floor_le (by linarith))
      have hJ := lcm_small (N:=N) (by omega) il
      have e : F L (i-1)-F L i = (1:ℚ)/J (i-1)-1/J i := by
        simp only [F,min_eq_right h,max_eq_left h,min_eq_right (show i-1≤L by omega),max_eq_left (show i-1≤L by omega)]
        ring
      rw [e];exact small hil hJ z
    · obtain ⟨V,hV,hc,hcan⟩ := medium hil (le_trans (Nat.mul_self_le_mul_self hiu) (Nat.sqrt_le N)) z
      refine ⟨V,hV,hc.trans ?_,hcan⟩
      simp only [F,min_eq_left (show L ≤ i-1 by omega),max_eq_right (show L ≤ i-1 by omega),
        min_eq_left (show L ≤ i by omega),max_eq_right (show L ≤ i by omega)]
      rw [Nat.cast_sub (by omega : 1 ≤ i),Nat.cast_one]
      have ip : (1:ℚ) < i := by exact_mod_cast hil
      rw [add_sub_add_left_eq_sub]
      have ip0 : (0:ℚ) < i := by linarith
      have ip1 : (0:ℚ)<(i:ℚ)-1 := by linarith
      rw [div_sub_div _ _ ip1.ne' ip0.ne', div_le_div_iff₀ (by positivity) (mul_pos ip1 ip0)]
      nlinarith
end Mid308
theorem OMA.solution : OMA.R_Erdos308_erdos_308_variants_croot_R1_H1_R1.H2 := Mid308.total
end
