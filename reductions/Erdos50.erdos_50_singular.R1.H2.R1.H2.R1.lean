import OMAReductions.R_Erdos50_erdos_50_singular_R1_H2_R1
import Mathlib

/-! A block of fresh primes supplies an isolated divisor with a fixed positive
probability. Repeating on coprime periods makes the probability of missing
every block geometrically small. The first input is a Bernoulli estimate for
prime intervals. The second converts prime patterns to residue classes. -/
namespace OMA.R_Erdos50_erdos_50_singular_R1_H2_R1_H2_R1

open Finset Filter
open scoped Classical

/-- Uniform positive mass of small nonempty products followed by a prime-free interval. -/
def H1 : Prop :=
  ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∀ b : ℕ, 2 ≤ b → ∃ y : ℕ, b ≤ y ∧
    (∏ p ∈ (range (b+1)).filter Nat.Prime, p) ≤ y ∧
    let Q := (Finset.Ioc b (y^20)).filter Nat.Prime
    η ≤ ∑ T ∈ Q.powerset.filter (fun T => T.Nonempty ∧
      (∀ p ∈ T, p ≤ y) ∧ (∏ p ∈ T, p) ≤ y^4),
      (∏ p ∈ T, 1/(p:ℝ)) * ∏ p ∈ Q \ T, (1-1/(p:ℝ))

/-- CRT gives the exact frequency of any finite collection of prime patterns. -/
def H2 : Prop :=
  ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → ∀ R : Finset ℕ → Prop,
    let q := ∏ p ∈ Q, p
    (((range q).filter (fun n => R (Q.filter (· ∣ n)))).card : ℝ) / q =
      ∑ T ∈ Q.powerset.filter R, (∏ p ∈ T, 1/(p:ℝ)) * ∏ p ∈ Q \ T, (1-1/(p:ℝ))

lemma crt_upper {m q : ℕ} (hc : m.Coprime q) (A B : Finset ℕ) :
    ((range (m*q)).filter (fun n => n%m ∈ A ∧ n%q ∈ B)).card ≤ A.card * B.card := by
  rw [← card_product]
  apply card_le_card_of_injOn (fun n : ℕ => (n%m,n%q))
  · intro n hn
    exact mem_product.mpr (mem_filter.mp hn).2
  · intro u hu v hv h
    have eq := (Nat.modEq_and_modEq_iff_modEq_mul hc).1
      ⟨show u ≡ v [MOD m] from congrArg Prod.fst h, show u ≡ v [MOD q] from congrArg Prod.snd h⟩
    exact eq.eq_of_lt_of_lt (mem_range.mp (mem_filter.mp hu).1) (mem_range.mp (mem_filter.mp hv).1)

lemma periodic_upper (m N : ℕ) (A : Finset ℕ) :
    ((range N).filter (fun n => n%m ∈ A)).card ≤ (N/m+1)*A.card := by
  calc
    _ ≤ ((range (N/m+1)) ×ˢ A).card := by
      apply card_le_card_of_injOn (fun n : ℕ => (n/m,n%m))
      · intro n hn
        obtain ⟨hn,ha⟩ := mem_filter.mp hn
        exact mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp hn).le)),ha⟩
      · intro u _ v _ h
        have h₁ : u/m=v/m := congrArg Prod.fst h
        have h₂ : u%m=v%m := congrArg Prod.snd h
        calc
          u = u%m + m*(u/m) := (Nat.mod_add_div ..).symm
          _ = v%m + m*(v/m) := by rw [h₁,h₂]
          _ = v := Nat.mod_add_div ..
    _ = _ := by simp

lemma amplify (P : ℕ → ℕ → Prop) (mono : ∀ D E, D ≤ E → ∀ n, P D n → P E n)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (blocks : ∀ m : ℕ, 0 < m → ∃ q : ℕ, 0 < q ∧ m.Coprime q ∧
      ∃ B ⊆ range q, η*q ≤ (B.card:ℝ) ∧ ∃ D, ∀ n : ℕ, 0 < n → n%q ∈ B → P D n) :
    ∀ ε : ℝ, 0<ε → ∃ D, ∀ᶠ N : ℕ in atTop,
      (1-ε)*N ≤ (((range N).filter (P D)).card:ℝ) := by
  classical
  have iter (j : ℕ) : ∃ m : ℕ, 0 < m ∧ ∃ A : Finset ℕ,
      (A.card:ℝ) ≤ (1-η)^j*m ∧ ∃ D, ∀ n : ℕ, 0 < n → n%m ∉ A → P D n := by
    induction j with
    | zero =>
      refine ⟨1,by decide,{0},by simp,0,?_⟩
      intro n _ h
      exact h (by simp [Nat.mod_one]) |>.elim
    | succ j ih =>
      obtain ⟨m,hm,A,hA,D,hD⟩ := ih
      obtain ⟨q,hq,hc,B,hsub,hB,E,hE⟩ := blocks m hm
      let C := (range (m*q)).filter fun n => n%m ∈ A ∧ n%q ∈ range q \ B
      have hcomp : ((range q \ B).card : ℝ) ≤ (1-η)*q := by
        rw [card_sdiff_of_subset hsub,card_range,Nat.cast_sub (by simpa using card_le_card hsub)]
        linarith
      refine ⟨m*q,Nat.mul_pos hm hq,C,?_,max D E,?_⟩
      · have e : C.card ≤ A.card * (range q \ B).card := crt_upper hc A _
        calc
          (C.card:ℝ) ≤ (A.card:ℝ)*((range q \ B).card:ℝ) := by exact_mod_cast e
          _ ≤ ((1-η)^j*m)*((1-η)*q) := mul_le_mul hA hcomp (by positivity)
            (mul_nonneg (pow_nonneg (by linarith) _) (Nat.cast_nonneg _))
          _ = _ := by rw [pow_succ,Nat.cast_mul]; ring
      · intro n hn hnC
        by_cases ha : n%m ∈ A
        · apply mono E _ (le_max_right ..) n
          apply hE n hn
          by_contra hb
          apply hnC
          apply mem_filter.mpr
          refine ⟨mem_range.mpr (Nat.mod_lt _ (Nat.mul_pos hm hq)),?_⟩
          rw [Nat.mod_mod_of_dvd _ (dvd_mul_right m q),Nat.mod_mod_of_dvd _ (dvd_mul_left q m)]
          exact ⟨ha,mem_sdiff.mpr ⟨mem_range.mpr (Nat.mod_lt _ hq),hb⟩⟩
        · exact mono D _ (le_max_left ..) n (hD n hn ha)
  intro ε hε
  obtain ⟨j,hj⟩ := exists_pow_lt_of_lt_one (by positivity : 0<ε/2) (by linarith : 1-η<1)
  obtain ⟨m,hm,A,hA,D,hD⟩ := iter j
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt ((2*((A.card:ℝ)+1))/ε)
  refine ⟨D,?_⟩
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hN' : (N₀:ℝ)≤N := by exact_mod_cast hN
  have err : (A.card:ℝ)+1 ≤ ε/2*N := by
    have e := (div_lt_iff₀ hε).mp hN₀
    nlinarith [mul_le_mul_of_nonneg_right hN' hε.le]
  let F := (range N).filter fun n => n%m ∈ A
  let G := (range N).filter (P D)
  have sub : range N ⊆ insert 0 (F ∪ G) := by
    intro n hn
    by_cases h0 : n=0
    · simp [h0]
    apply mem_insert_of_mem
    by_cases hb : n%m∈A
    · exact mem_union_left _ (mem_filter.mpr ⟨hn,hb⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hn,hD n (Nat.pos_of_ne_zero h0) hb⟩)
  have cnt : N ≤ F.card + G.card + 1 := by
    have v := (card_le_card sub).trans (card_insert_le ..)
    simp only [card_range] at v
    have := card_union_le F G
    omega
  have bound : (F.card:ℝ) ≤ ε/2*N + A.card := by
    have e := periodic_upper m N A
    have hdiv : (N/m:ℕ)*m ≤ N := Nat.div_mul_le_self _ _
    have nd : ((N/m:ℕ):ℝ)*m ≤ N := by exact_mod_cast hdiv
    have hA' := hA.trans (mul_le_mul_of_nonneg_right hj.le (Nat.cast_nonneg _))
    calc
      _ ≤ (((N/m:ℕ):ℝ)+1)*A.card := by exact_mod_cast e
      _ = ((N/m:ℕ):ℝ)*A.card + A.card := by ring
      _ ≤ ((N/m:ℕ):ℝ)*(ε/2*m) + A.card := by gcongr
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left nd (by positivity : 0≤ε/2)]
  have cnt' : (N:ℝ) ≤ F.card+G.card+1 := by exact_mod_cast cnt
  change _ ≤ (G.card:ℝ)
  linarith

theorem main : H1 → H2 → OMA.R_Erdos50_erdos_50_singular_R1_H2_R1.H2 := by
  intro windows crt K
  classical
  let P (D n : ℕ) := ∃ d ∈ Finset.Ioc K D, n ≠ 0 ∧
    (((range (d^4+1)).filter Nat.Prime).filter (· ∣ n)) = d.primeFactors
  obtain ⟨η,hη,hη1,win⟩ := windows
  apply amplify P (fun D E h n ⟨d,hd,hi⟩ =>
    ⟨d, mem_Ioc.mpr ⟨(mem_Ioc.mp hd).1,(mem_Ioc.mp hd).2.trans h⟩,hi⟩) hη hη1
  intro m hm
  let b := max (max K m) 2
  have hbm : m ≤ b := (le_max_right K m).trans (le_max_left ..)
  have hbK : K ≤ b := (le_max_left K m).trans (le_max_left ..)
  obtain ⟨y,hby,hprim,hw⟩ := win b (le_max_right ..)
  let Q := (Finset.Ioc b (y^20)).filter Nat.Prime
  let q := ∏ p ∈ Q, p
  have primes (p) (hp : p∈Q) : Nat.Prime p := (mem_filter.mp hp).2
  have hq : 0<q := prod_pos fun p hp => (primes p hp).pos
  have hc : m.Coprime q := Nat.Coprime.prod_right fun p hp =>
    ((primes p hp).coprime_iff_not_dvd.mpr (fun h =>
      (mem_Ioc.mp (mem_filter.mp hp).1).1.not_ge ((Nat.le_of_dvd hm h).trans hbm))).symm
  let R (T : Finset ℕ) := T.Nonempty ∧ (∀ p ∈ T, p≤y) ∧ (∏ p ∈ T,p)≤y^4
  let B := (range q).filter (fun n => R (Q.filter (· ∣ n)))
  have hcf := crt Q primes R
  dsimp only at hcf
  have hmB : η*q ≤ (B.card:ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast hq : (0:ℝ)<q)).mp
    apply hw.trans
    convert! hcf.symm.le using 1
    · apply sum_congr _ (fun _ _ => rfl)
      ext T
      simp only [mem_filter,Q,R]
    · apply congrArg₂ (fun (A : Finset ℕ) (z : ℕ) => (A.card:ℝ)/z) _ rfl
      ext n
      simp only [B,q,mem_filter]
  refine ⟨q,hq,hc,B,filter_subset ..,hmB,y^5,?_⟩
  intro n hn hb
  let T := Q.filter (· ∣ n)
  have eq : Q.filter (· ∣ n%q) = T := by
    apply filter_congr
    intro p hp
    exact Nat.dvd_mod_iff (show p ∣ q from dvd_prod_of_mem id hp)
  obtain ⟨hT,hyT,hprod⟩ : R T := eq ▸ (mem_filter.mp hb).2
  let S := ((range (b+1)).filter Nat.Prime).filter (· ∣ n)
  have hs (p) (hp : p∈S) : Nat.Prime p := (mem_filter.mp (mem_filter.mp hp).1).2
  have ht (p) (hp : p∈T) : Nat.Prime p := primes p (mem_filter.mp hp).1
  have ds : Disjoint S T := by
    apply disjoint_left.mpr
    intro p hp ht'
    have := mem_range.mp (mem_filter.mp (mem_filter.mp hp).1).1
    have := (mem_Ioc.mp (mem_filter.mp (mem_filter.mp ht').1).1).1
    omega
  let d := ∏ p ∈ S ∪ T, p
  have hdp : 0 < d := prod_pos fun p hp => (mem_union.mp hp).elim (fun h => (hs p h).pos) (fun h => (ht p h).pos)
  have hfac : d.primeFactors = S ∪ T := Nat.primeFactors_prod fun p hp => (mem_union.mp hp).elim (hs p) (ht p)
  have small : (∏ p ∈ S,p) ≤ y := by
    apply le_trans _ hprim
    exact Nat.le_of_dvd (prod_pos fun p hp => (mem_filter.mp hp).2.pos)
      (prod_dvd_prod_of_subset _ _ id (filter_subset ..))
  have hdy : d ≤ y^5 := by
    dsimp [d]
    rw [prod_union ds]
    exact (Nat.mul_le_mul small hprod).trans_eq (by ring)
  obtain ⟨p,hp⟩ := hT
  have hpd : p ∣ d := dvd_prod_of_mem _ (mem_union_right S hp)
  have hbp := (mem_Ioc.mp (mem_filter.mp (mem_filter.mp hp).1).1).1
  refine ⟨d,mem_Ioc.mpr ⟨hbK.trans_lt (hbp.trans_le (Nat.le_of_dvd hdp hpd)),hdy⟩,hn.ne',?_⟩
  rw [hfac]
  have hd4 : d^4 ≤ y^20 := by simpa [←pow_mul] using Nat.pow_le_pow_left hdy 4
  ext p
  constructor
  · intro hp
    obtain ⟨⟨hp4,prime⟩,divides⟩ := mem_filter.mp hp |>.imp_left mem_filter.mp
    by_cases hb' : p≤b
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega),prime⟩,divides⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ioc.mpr
        ⟨by omega,(Nat.le_of_lt_succ (mem_range.mp hp4)).trans hd4⟩,prime⟩,divides⟩)
  · intro hp
    have hdiv : p∣d := dvd_prod_of_mem _ hp
    have hlow : d ≤ d^4 := Nat.le_self_pow (by decide) d
    obtain h | h := mem_union.mp hp
    · exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by have := Nat.le_of_dvd hdp hdiv; omega),hs p h⟩,(mem_filter.mp h).2⟩
    · exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by have := Nat.le_of_dvd hdp hdiv; omega),ht p h⟩,(mem_filter.mp h).2⟩

end OMA.R_Erdos50_erdos_50_singular_R1_H2_R1_H2_R1
