import FormalConjectures.ErdosProblems.«393»
import Mathlib

/-! Bui, Pratt and Zaharescu, Power savings for counting solutions to
polynomial-factorial equations, section 3. Translating the factors of
the minimizing factorization gives a finite collection of split monic
polynomials. Centering their roots kills the subleading coefficient.
We combine the close-triple estimate with packing and dyadic summation. -/

namespace OMA.R_Erdos393_erdos_393_variants_bui_pratt_zaharescu_R1
open Finset Filter Asymptotics Real Erdos393
open scoped Classical

private lemma pattern {n m : ℕ} (hn : 2≤n) (hm : f n=m) :
    ∃ T ∈ (Icc 0 m).powerset, 2≤T.card ∧ ∃ a : ℕ, ∏ i∈T, (a+i) = n.factorial := by
  let D := {w : ℕ | 1≤w ∧ ∃ a : ℕ, ∃ s⊆Icc a (a+w), a∈s ∧ a+w∈s ∧ ∏ i∈s,i=n.factorial}
  have nonempty : D.Nonempty := by
    refine ⟨n-1,by omega,1,Ico 1 (n+1),?_,?_,?_,prod_Ico_id_eq_factorial n⟩
    · intro i hi
      have h := mem_Ico.mp hi
      exact mem_Icc.mpr ⟨h.1,by omega⟩
    · simp
      omega
    · apply mem_Ico.mpr
      omega
  have mem : m∈D := hm ▸ Nat.sInf_mem nonempty
  obtain ⟨m1,a,s,hs,ha,hb,hprod⟩ := mem
  let T := s.image (fun i => i-a)
  have lea (i:ℕ) (hi:i∈s) := (mem_Icc.mp (hs hi)).1
  have inj : Set.InjOn (fun i : ℕ => i-a) ↑s := by
    intro i hi j hj e
    dsimp at e
    have := lea i hi
    have := lea j hj
    omega
  refine ⟨T,mem_powerset.mpr ?_,?_,a,?_⟩
  · intro i hi
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
    exact mem_Icc.mpr ⟨Nat.zero_le _,by have := (mem_Icc.mp (hs hj)).2; omega⟩
  · have h := Finset.one_lt_card.mpr ⟨a,ha,a+m,hb,by omega⟩
    rw [show T.card=s.card from Finset.card_image_of_injOn inj]
    omega
  · dsimp only [T]
    rw [prod_image inj]
    exact (prod_congr rfl (fun i hi => show a+(i-a)=i by have := lea i hi; omega)).trans hprod

private lemma center {a n : ℕ} (T : Finset ℕ) (h : ∏ i∈T, (a+i) = n.factorial) :
    ∃ y : ℕ, (T.card:ℤ)^T.card*(n.factorial:ℤ) =
      ∏ i∈T, ((y:ℤ)+(T.card:ℤ)*i-(∑ j∈T,(j:ℤ))) := by
  refine ⟨T.card*a+∑ j∈T,j,?_⟩
  have hi : ∏ i∈T, ((a:ℤ)+(i:ℤ))=(n.factorial:ℤ) := by exact_mod_cast h
  push_cast
  rw [←hi,←prod_const (s:=T) (T.card:ℤ),←prod_mul_distrib]
  exact prod_congr rfl fun _ _ => by ring

private lemma dyadic {P:ℕ→Prop} {c α:ℝ} (hc:0≤c) (hα:0<α)
    (hb:∀ N : ℕ, 1≤N → (((Ico N (2*N)).filter P).card:ℝ)≤c*(N:ℝ)^α) :
    ∃ D:ℝ, 0≤D ∧ ∀ N:ℕ, 1≤N → (((range (N+1)).filter P).card:ℝ)≤D*(N:ℝ)^α := by
  let q := (2:ℝ)^α
  have hq : 1<q := Real.one_lt_rpow (by norm_num) hα
  let d := 1+c/(q-1)
  have d1 : 1≤d := by dsimp [d]; linarith [div_nonneg hc (sub_nonneg.mpr hq.le)]
  have step : d+c≤d*q := by
    have e := div_mul_cancel₀ c (sub_ne_zero.mpr hq.ne')
    dsimp [d]
    linarith
  have powbd (j:ℕ) : (((range (2^j)).filter P).card:ℝ) ≤ d*q^j := by
    induction j with
    | zero =>
      simp only [pow_zero,mul_one]
      have h := card_filter_le (range 1) P
      exact (by exact_mod_cast (h.trans_eq (card_range _)) : (((range 1).filter P).card:ℝ) ≤ 1).trans d1
    | succ j ih =>
      let L := 2^j
      have sub : (range (2^(j+1))).filter P ⊆ (range L).filter P ∪ (Ico L (2*L)).filter P := by
        intro n hn
        obtain ⟨lt,pr⟩ := mem_filter.mp hn
        have he := mem_range.mp lt
        rw [pow_succ,Nat.mul_comm] at he
        by_cases h:n<L
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr h,pr⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨mem_Ico.mpr ⟨Nat.le_of_not_gt h,he⟩,pr⟩)
      have ub := (card_le_card sub).trans (card_union_le ..)
      have e : (L:ℝ)^α=q^j := by
        dsimp [L,q]
        rw [Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul_natCast (by norm_num)]
      have lo := hb L (by dsimp [L]; exact Nat.one_le_pow _ _ (by decide))
      rw [e] at lo
      have bd := add_le_add ih lo
      have final := mul_le_mul_of_nonneg_right step (show 0≤q^j by positivity)
      have up : (((range (2^(j+1))).filter P).card:ℝ) ≤ ((range L).filter P).card+(((Ico L (2*L)).filter P).card:ℝ) := by exact_mod_cast ub
      rw [show d*q^(j+1) = d*q*q^j by ring]
      change (((range L).filter P).card:ℝ) + _ ≤ _ at bd
      nlinarith only [up,bd,final]
  refine ⟨d*q,mul_nonneg (zero_le_one.trans d1) (zero_le_one.trans hq.le),?_⟩
  intro N hN
  let j := Nat.log 2 N
  have lt := Nat.lt_pow_succ_log_self (by decide : 1<2) N
  have lower := Nat.pow_log_le_self 2 (by omega : N≠0)
  have low : q^j≤(N:ℝ)^α := by
    have e : (((2:ℕ)^j:ℕ):ℝ)^α=q^j := by
      dsimp [q]
      rw [Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul_natCast (by norm_num)]
    rw [←e]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast lower) hα.le
  have incl : (range (N+1)).filter P ⊆ (range (2^(j+1))).filter P := by
    apply filter_subset_filter
    apply range_mono
    exact lt
  have e := (Nat.cast_le (α:=ℝ)).mpr (card_le_card incl)
  have h := e.trans (powbd (j+1))
  rw [pow_succ] at h
  exact h.trans (by rw [mul_right_comm d, mul_assoc]; gcongr)

-- The close-triple estimate of BPZ Proposition 3.2, summed over its
-- O(log N) shorter intervals, specialized to centered split polynomials.
def H1 : Prop := ∀ T : Finset ℕ, 2≤T.card →
  let good (n:ℕ) := ∃ y : ℕ, (T.card:ℤ)^T.card*(n.factorial:ℤ) =
    ∏ i∈T, ((y:ℤ)+(T.card:ℤ)*i-(∑ j∈T,(j:ℤ)))
  ∃ C:ℝ, 0<C ∧ ∀ N : ℕ, 1≤N →
    let M := ⌊(N:ℝ)^(1/34:ℝ)⌋₊
    ∀ u v : ℕ, 0<u → u<v → v≤M → T.card∣u → T.card∣v →
    (((Ico N (2*N)).filter (fun n => v≤n ∧ good n ∧ good (n-u) ∧ good (n-v))).card:ℝ) ≤ C*N/(M:ℝ)^3

-- Short bins contain at most two exceptional points per residue, followed
-- by anchors of two distinct backwards differences in that residue.
def H2 : Prop := ∀ r N M : ℕ, 2≤r → 0<M → ∀ S⊆Ico N (2*N), ∀ K:ℝ, 0≤K →
  (∀ u v:ℕ, 0<u → u<v → v≤M → r∣u → r∣v →
    ((S.filter (fun n => v≤n ∧ n-u∈S ∧ n-v∈S)).card:ℝ) ≤ K) →
  (S.card:ℝ) ≤ (2*(r:ℝ)+1)*((N:ℝ)/M+2+(M:ℝ)^2*K)

theorem main : H1 → H2 → type_of% @Erdos393.erdos_393.variants.bui_pratt_zaharescu := by
  intro triples pack m
  let U := (Icc 0 m).powerset.filter (fun T => 2≤T.card)
  let P (T:Finset ℕ) (n:ℕ) := ∃ y : ℕ, (T.card:ℤ)^T.card*(n.factorial:ℤ) =
    ∏ i∈T, ((y:ℤ)+(T.card:ℤ)*i-(∑ j∈T,(j:ℤ)))
  have bound (T:Finset ℕ) (ht:T∈U) : ∃ D:ℝ, 0≤D ∧ ∀ N:ℕ, 1≤N →
      (((range (N+1)).filter (P T)).card:ℝ)≤D*(N:ℝ)^(33/34:ℝ) := by
    have t2 := (mem_filter.mp ht).2
    obtain ⟨C,cp,tr⟩ := triples T t2
    let c := (2*(T.card:ℝ)+1)*(4+2*C)
    apply dyadic (c:=c) (by dsimp [c]; positivity) (by norm_num)
    intro N hN
    let z := (N:ℝ)^(1/34:ℝ)
    let M := ⌊z⌋₊
    have n1 : 1≤(N:ℝ) := by exact_mod_cast hN
    have z1 : 1≤z := Real.one_le_rpow n1 (by norm_num)
    have m1 : 0<M := Nat.floor_pos.mpr z1
    have mp : 0<(M:ℝ) := by exact_mod_cast m1
    have zM : z ≤ 2*(M:ℝ) := by have h := Nat.lt_floor_add_one z; change z < (M:ℝ)+1 at h; linarith [show 1≤(M:ℝ) by exact_mod_cast m1]
    let W := (N:ℝ)^(33/34:ℝ)
    have wz : W*z=N := by dsimp [W,z]; rw [←Real.rpow_add (by positivity)]; norm_num
    have w1 : 1≤W := Real.one_le_rpow n1 (by norm_num)
    have div : (N:ℝ)/M≤2*W := (div_le_iff₀ mp).mpr (by nlinarith only [wz,mul_le_mul_of_nonneg_left zM (show 0≤W by linarith)])
    let S := (Ico N (2*N)).filter (P T)
    have h := pack T.card N M t2 m1 S (filter_subset ..) (C*N/(M:ℝ)^3) (by positivity) (by
      intro u v up uv vm du dv
      apply le_trans _ (tr N hN u v up uv vm du dv)
      apply Nat.cast_le.mpr
      apply card_le_card
      intro n hn
      obtain ⟨hS,hv,hu,hw⟩ := mem_filter.mp hn
      exact mem_filter.mpr ⟨(mem_filter.mp hS).1,hv,(mem_filter.mp hS).2,(mem_filter.mp hu).2,(mem_filter.mp hw).2⟩)
    have eq : (M:ℝ)^2*(C*N/(M:ℝ)^3) = C*((N:ℝ)/M) := by field_simp <;> ring
    rw [eq] at h
    exact h.trans (by
      dsimp only [c]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      change _ ≤ (4+2*C)*W
      nlinarith only [div,w1,mul_le_mul_of_nonneg_left div cp.le])
  choose D d0 bd using bound
  let E := ∑ T∈U.attach, D T.1 T.2
  refine IsBigO.of_bound (2+E) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have eq : {n : ℕ | f n=m} ∩ Set.Iic N = ↑((range (N+1)).filter (fun n => f n=m)) := by ext n; simp; omega
  rw [eq,Set.ncard_coe_finset]
  have incl : (range (N+1)).filter (fun n => f n=m) ⊆ range 2 ∪
      U.attach.biUnion (fun T => (range (N+1)).filter (P T.1)) := by
    intro n hn
    obtain ⟨rng,hf⟩ := mem_filter.mp hn
    by_cases small:n<2
    · exact mem_union_left _ (mem_range.mpr small)
    obtain ⟨T,hT,t2,a,he⟩ := pattern (by omega) hf
    let x : {T // T∈U} := ⟨T,mem_filter.mpr ⟨hT,t2⟩⟩
    exact mem_union_right _ (mem_biUnion.mpr ⟨x,mem_attach _ _,mem_filter.mpr ⟨rng,center T he⟩⟩)
  have h := (card_le_card incl).trans (card_union_le ..)
  have h' := h.trans (Nat.add_le_add_left card_biUnion_le _)
  simp only [card_range] at h'
  have e : (((range (N+1)).filter (fun n => f n=m)).card:ℝ) ≤ 2+∑ T∈U.attach, (((range (N+1)).filter (P T.1)).card:ℝ) := by exact_mod_cast h'
  have su := sum_le_sum (s:=U.attach) (fun T _ => bd T.1 T.2 N hN)
  rw [←sum_mul] at su
  have w1 := Real.one_le_rpow (by exact_mod_cast hN : 1≤(N:ℝ)) (by norm_num : (0:ℝ)≤33/34)
  simp only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) ((range (N+1)).filter (fun n => f n=m)).card),abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
  dsimp only [E]
  linarith only [e,su,w1]

end OMA.R_Erdos393_erdos_393_variants_bui_pratt_zaharescu_R1
