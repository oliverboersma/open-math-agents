import OMAReductions.R_Erdos338_erdos_338_variants_squares_R1_H2_R1
import Mathlib

/-! Repeated coordinates in a representation by four squares leave a ternary
form. We prove the count is sublinear for every integer, including even ones.
The odd binary-form and divisor estimates below are from Marcus Buffett’s
Erdős 338 proof (PR 3526), including its credits to Matt Dorman and OpenAI.
The reduction is Marcus Buffett’s PR 2731. -/

open Finset Filter

namespace RepeatedFourSquares

private def ones (M : ℕ) [NeZero M] := (univ : Finset (ZMod M)).filter (fun z => z^2=1)

private lemma ones_card (M : ℕ) (hM : 0 < M) (ho : Odd M) [NeZero M] :
    (ones M).card ≤ M.divisors.card ^ 2 := by
  let A (z : ZMod M) := M.gcd (z.val+1)
  let B (z : ZMod M) := M.gcd (z.val+(M-1))
  have key (z : ZMod M) (hz : z ∈ ones M) : M ∣ A z * B z := by
    apply Nat.dvd_gcd_mul_gcd_iff_dvd_mul.mpr
    apply (ZMod.natCast_eq_zero_iff _ M).mp
    have ht : ((M-1 : ℕ) : ZMod M) = -1 := by rw [Nat.cast_sub (by omega), ZMod.natCast_self]; simp
    simp only [Nat.cast_mul, Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one, ht]
    have h := (mem_filter.mp hz).2
    linear_combination h
  have cop (z : ZMod M) : (A z).Coprime (B z) := by
    let g := (A z).gcd (B z)
    have ga : g ∣ A z := Nat.gcd_dvd_left _ _
    have gb : g ∣ B z := Nat.gcd_dvd_right _ _
    have gm : g ∣ M := ga.trans (Nat.gcd_dvd_left _ _)
    have gp : g ∣ z.val+1 := ga.trans (Nat.gcd_dvd_right _ _)
    have gn : g ∣ z.val+(M-1) := gb.trans (Nat.gcd_dvd_right _ _)
    have two : g ∣ 2 := by
      have h := Nat.dvd_sub (dvd_add gp gm) gn
      rwa [show z.val+1+M - (z.val+(M-1)) = 2 by omega] at h
    have h := Nat.dvd_gcd gm two
    change g = 1
    rw [show M.gcd 2 = 1 from Nat.coprime_two_right.mpr ho] at h
    exact Nat.eq_one_of_dvd_one h
  have hi : (ones M).card ≤ (M.divisors ×ˢ M.divisors).card := by
    apply Finset.card_le_card_of_injOn (fun z => (A z,B z))
    · intro z _
      exact mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _,hM.ne'⟩,
        Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _,hM.ne'⟩⟩
    · intro z hz w hw e
      have ea : A z = A w := congrArg Prod.fst e
      have eb : B z = B w := congrArg Prod.snd e
      have aux (k c : ℕ) (hz' : k ∣ z.val+c) (hw' : k ∣ w.val+c) : z.val ≡ w.val [MOD k] :=
        (Nat.ModEq.refl c).add_right_cancel
          ((Nat.modEq_zero_iff_dvd.mpr hz').trans (Nat.modEq_zero_iff_dvd.mpr hw').symm)
      have ha := aux (A z) 1 (Nat.gcd_dvd_right _ _) (ea ▸ Nat.gcd_dvd_right _ _)
      have hb := aux (B z) (M-1) (Nat.gcd_dvd_right _ _) (eb ▸ Nat.gcd_dvd_right _ _)
      have hm := Nat.ModEq.of_dvd (key z hz) ((Nat.modEq_and_modEq_iff_modEq_mul (cop z)).mp ⟨ha,hb⟩)
      exact ZMod.val_injective M (hm.eq_of_lt_of_lt z.val_lt w.val_lt)
  simpa [pow_two] using hi

private def reps (M : ℕ) := (((range (M+1)) ×ˢ (range (M+1))).filter
  (fun v : ℕ × ℕ => v.1^2 + 2*v.2^2=M))

private def prim (M : ℕ) := (reps M).filter fun v => v.1.Coprime v.2

private lemma form_of_mem {M : ℕ} {p : ℕ × ℕ} (hp : p ∈ reps M) :
    p.1^2 + 2*p.2^2=M := (mem_filter.mp hp).2

private lemma y_unit {M : ℕ} {p : ℕ × ℕ} (hp : p ∈ prim M) : p.2.Coprime M := by
  obtain ⟨hr,hc⟩ := mem_filter.mp hp
  rw [← form_of_mem hr, show 2*p.2^2 = (2*p.2)*p.2 by ring, Nat.coprime_add_mul_right_right]
  exact hc.symm.pow_right 2

private def slope (M : ℕ) (p : ℕ × ℕ) : ZMod M := p.1 * (p.2 : ZMod M)⁻¹

private lemma slope_mul {M : ℕ} {p : ℕ × ℕ} (hp : p ∈ prim M) :
    slope M p * p.2 = p.1 := by
  have h := ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime _ _).mpr (y_unit hp))
  dsimp [slope]
  rw [mul_assoc, mul_comm _ (p.2 : ZMod M), h, mul_one]

private lemma slope_sq {M : ℕ} {p : ℕ × ℕ} (hp : p ∈ prim M) :
    (slope M p)^2 = -2 := by
  have hu := (ZMod.isUnit_iff_coprime _ _).mpr (y_unit hp)
  apply (hu.pow 2).mul_left_inj.mp
  have h := congrArg (fun n : ℕ => (n : ZMod M)) (form_of_mem (mem_filter.mp hp).1)
  push_cast at h
  rw [ZMod.natCast_self] at h
  rw [← mul_pow, slope_mul hp]
  linear_combination h

private lemma slope_inj (M : ℕ) (hM : 0 < M) : Set.InjOn (slope M) (prim M) := by
  intro p hp q hq e
  have fp := form_of_mem (mem_filter.mp hp).1
  have fq := form_of_mem (mem_filter.mp hq).1
  have bound {a b c d : ℕ} (ha : a^2+2*b^2=M) (hc : c^2+2*d^2=M) : a*d < M := by
    have hds : d^2 < M := by nlinarith only [hc,hM,Nat.zero_le (c^2),Nat.zero_le (d^2)]
    nlinarith only [ha,hds,Nat.zero_le (b^2),sq_nonneg ((a:ℤ)-d)]
  have hm : (p.1*q.2 : ℕ) ≡ q.1*p.2 [MOD M] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ M).mp
    push_cast
    rw [← slope_mul hp, ← slope_mul hq, e]
    ring
  have he := hm.eq_of_lt_of_lt (bound fp fq) (bound fq fp)
  have hh : M*q.2^2=M*p.2^2 := by
    calc
      M*q.2^2 = (p.1*q.2)^2 + 2*p.2^2*q.2^2 := by rw [← fp]; ring
      _ = (q.1*p.2)^2 + 2*p.2^2*q.2^2 := by rw [he]
      _ = M*p.2^2 := by rw [← fq]; ring
  have h2 := Nat.eq_of_mul_eq_mul_left hM hh
  apply Prod.ext <;> nlinarith only [h2, fp, fq]

private lemma prim_bound (M : ℕ) (hM : 0 < M) (ho : Odd M) :
    (prim M).card ≤ M.divisors.card^2 := by
  let : NeZero M := ⟨hM.ne'⟩
  by_cases hn : (prim M).Nonempty
  · obtain ⟨p,hp⟩ := hn
    have htwo : IsUnit (2 : ZMod M) := by
      simpa only [Nat.cast_ofNat] using (ZMod.isUnit_iff_coprime 2 M).mpr (Nat.coprime_two_left.mpr ho)
    have hr : IsUnit (slope M p) := by
      have h : IsUnit ((slope M p)^2) := (slope_sq hp).symm ▸ htwo.neg
      simpa using h
    obtain ⟨u,hu⟩ := hr
    refine (Finset.card_le_card_of_injOn (t := ones M) (fun q => slope M q * (↑(u⁻¹) : ZMod M)) ?_ ?_).trans (ones_card M hM ho)
    · intro q hq
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      rw [mul_pow, slope_sq hq, ← slope_sq hp, ← hu, ← mul_pow]
      simp
    · intro q hq r hr eq
      exact slope_inj M hM hq hr ((u⁻¹).isUnit.mul_left_inj.mp eq)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]


private def common (p : ℕ × ℕ) := p.1.gcd p.2
private def normalize (g : ℕ) (p : ℕ × ℕ) := (p.1/g,p.2/g)

private lemma rescale (p : ℕ × ℕ) : common p * (normalize (common p) p).1 = p.1 ∧
    common p * (normalize (common p) p).2 = p.2 := by
  constructor <;> rw [mul_comm]
  · exact Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  · exact Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)

private lemma scale_form {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ reps N) :
    (common p)^2 * ((normalize (common p) p).1^2 + 2*(normalize (common p) p).2^2) = N := by
  calc
    _ = (common p * (normalize (common p) p).1)^2 +
        2*(common p * (normalize (common p) p).2)^2 := by ring
    _ = _ := by rw [(rescale p).1, (rescale p).2, form_of_mem hp]

private lemma rep_count (N : ℕ) (hn : 0 < N) (ho : Odd N) :
    (reps N).card ≤ N.divisors.card^3 := by
  have inDiv {p : ℕ × ℕ} (hp : p ∈ reps N) : common p ∈ N.divisors := by
    apply Nat.mem_divisors.mpr
    refine ⟨?_, hn.ne'⟩
    have h := scale_form hp
    rw [← h]
    exact (dvd_pow_self _ (by decide : 2 ≠ 0)).trans (dvd_mul_right _ _)
  suffices hs : (reps N).card ≤ N.divisors.card^2 * N.divisors.card by
    simpa [pow_succ] using hs
  apply Finset.card_le_mul_card_image_of_maps_to (f := common) (fun p hp => inDiv hp)
  intro g hg
  have gpos := Nat.pos_of_mem_divisors hg
  let S := (reps N).filter (fun p => common p = g)
  change S.card ≤ _
  by_cases hne : S.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
  obtain ⟨p,hp⟩ := hne
  have factor {v : ℕ × ℕ} (hv : v ∈ S) :
      g^2 * ((normalize g v).1^2 + 2*(normalize g v).2^2) = N := by
    obtain ⟨hr,hg⟩ := mem_filter.mp hv
    simpa only [← hg] using scale_form hr
  let M := (normalize g p).1^2 + 2*(normalize g p).2^2
  have gp : g^2*M = N := factor hp
  have hM : 0 < M := by
    by_contra! h
    have hz : M = 0 := by omega
    rw [hz, mul_zero] at gp
    omega
  have hdiv : M ∣ N := gp ▸ dvd_mul_left _ _
  have oddM : Odd M := (Nat.odd_mul.mp (gp.symm ▸ ho)).2
  have normed {v : ℕ × ℕ} (hv : v ∈ S) : normalize g v ∈ prim M := by
    have eq := Nat.eq_of_mul_eq_mul_left (pow_pos gpos 2) ((factor hv).trans gp.symm)
    apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr ?_, mem_range.mpr ?_⟩, eq⟩,?_⟩
    · nlinarith only [eq, Nat.le_mul_self (normalize g v).1, Nat.zero_le ((normalize g v).2^2)]
    · nlinarith only [eq, Nat.le_mul_self (normalize g v).2, Nat.zero_le ((normalize g v).1^2)]
    · have e := (mem_filter.mp hv).2
      change (v.1/g).Coprime (v.2/g)
      rw [← e]
      exact Nat.coprime_div_gcd_div_gcd (show 0 < common v by rw [e]; exact gpos)
  have inj : Set.InjOn (normalize g) S := by
    intro v hv w hw e
    have ev := (mem_filter.mp hv).2
    have ew := (mem_filter.mp hw).2
    have rv := rescale v
    have rw' := rescale w
    rw [ev] at rv
    rw [ew] at rw'
    rw [e] at rv
    exact Prod.ext (rv.1.symm.trans rw'.1) (rv.2.symm.trans rw'.2)
  exact (Finset.card_le_card_of_injOn (normalize g) (fun _ hv => normed hv) inj).trans
    ((prim_bound M hM oddM).trans (Nat.pow_le_pow_left (Finset.card_le_card
      (Nat.divisors_subset_of_dvd hn.ne' hdiv)) 2))

-- These two divisor estimates are adapted from @mattdorman, open-math-agents
-- commit 31c7aaa8a168df5860b5e00b8ec84bb8a9d104d0, based on OpenAI math
-- commit adc7f1241b42e322a6451854ab7e4b4c146bf78a under Apache-2.0.
private theorem succ_le_geometric (r : ℝ) (hr : 1 < r) (a : ℕ) :
    (a : ℝ) + 1 ≤ (1 + (r - 1)⁻¹) * r ^ a := by
  have h₁ := a.cast_le_pow_div_sub hr
  have h₂ : (1 : ℝ) ≤ r ^ a := one_le_pow₀ hr.le
  calc
    (a : ℝ) + 1 ≤ r ^ a / (r - 1) + r ^ a := add_le_add h₁ h₂
    _ = (1 + (r - 1)⁻¹) * r ^ a := by ring

private theorem divisors_card_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  let r : ℝ := (2 : ℝ) ^ ε
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hε
  let c : ℝ := 1 + (r - 1)⁻¹
  have hc : 1 ≤ c := by
    have hh : 0 ≤ (r - 1)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hr.le)
    dsimp [c]
    linarith
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have ht : Tendsto (fun p : ℕ => (p : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2 : ℝ)))
  refine ⟨c ^ N, pow_pos hc0 _, ?_⟩
  intro n
  by_cases hn : n = 0
  · simp [hn, Real.zero_rpow hε.ne']
  have hfactor (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p : ℝ) + 1 ≤
        (if p < N then c else 1) * ((p : ℝ) ^ ε) ^ n.factorization p := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hsmall : p < N
    · rw [if_pos hsmall]
      exact (succ_le_geometric r hr _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hp2 hε.le) _)
        hc0.le)
    · rw [if_neg hsmall, one_mul]
      have hh : (n.factorization p : ℝ) + 1 ≤ (2 : ℝ) ^ n.factorization p := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := n.factorization p))
      exact hh.trans (pow_le_pow_left₀ (by norm_num) (hN p (Nat.le_of_not_gt hsmall)) _)
  have hconstant : (∏ p ∈ n.primeFactors, if p < N then c else 1) ≤ c ^ N := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, mul_one, Finset.prod_const]
    apply pow_le_pow_right₀ hc
    exact (Finset.card_le_card (show n.primeFactors.filter (fun p => p < N) ⊆
      Finset.range N from fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)).trans
        (by rw [Finset.card_range])
  have hpowers : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p) =
      (n : ℝ) ^ ε := by
    simp_rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _) ε,
      mul_comm ε, Real.rpow_natCast_mul (Nat.cast_nonneg _) _ ε]
    rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hn]
      push_cast
      rfl
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < N then c else 1) * ((p : ℝ) ^ ε) ^ n.factorization p :=
      Finset.prod_le_prod (fun p _ => by positivity) hfactor
    _ = (∏ p ∈ n.primeFactors, if p < N then c else 1) * (n : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, hpowers]
    _ ≤ c ^ N * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hconstant (by positivity)


/-- If the norm is even, dividing by two interchanges the roles of the coordinates. -/
private lemma halve (k : ℕ) : (reps (2*k)).card ≤ (reps k).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => (p.2, p.1 / 2))
  · rintro ⟨a,b⟩ h
    have hform : a^2 + 2*b^2 = 2*k := form_of_mem h
    have ha : Even a := by simpa [Nat.even_pow] using (show Even (a^2) from ⟨k-b^2, by omega⟩)
    obtain ⟨t, rfl⟩ := ha
    have heq : b^2 + 2*t^2 = k := by nlinarith only [hform]
    have hb := Nat.le_self_pow (by decide : 2 ≠ 0) b
    have ht := Nat.le_self_pow (by decide : 2 ≠ 0) t
    change (b, (t+t)/2) ∈ reps k
    simp only [reps, mem_filter, mem_product, mem_range]
    simpa [show (t+t)/2 = t by omega] using
      (show (b < k+1 ∧ t < k+1) ∧ b^2+2*t^2=k from ⟨⟨by omega,by omega⟩,heq⟩)
  · rintro ⟨a,b⟩ h ⟨c,d⟩ h' eq
    have e := form_of_mem h
    have e' := form_of_mem h'
    have bd : b = d := congrArg Prod.fst eq
    subst d
    change a^2 + 2*b^2 = 2*k at e
    change c^2 + 2*b^2 = 2*k at e'
    have : a = c := by nlinarith only [e,e']
    simp [this]

private lemma all_rep_count (N : ℕ) (hn : 0 < N) :
    (reps N).card ≤ N.divisors.card ^ 3 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    rcases Nat.even_or_odd N with ⟨k,hk⟩ | oddN
    · have e : N = 2*k := by omega
      have hd : k ∣ N := ⟨2, by omega⟩
      rw [e] at hn ⊢
      exact (halve k).trans ((ih k (by omega) (by omega)).trans
        (Nat.pow_le_pow_left (Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' (e ▸ hd))) 3))
    · exact rep_count N hn oddN

private def arrange {α : Type*} (x y z : α) : Fin 6 → Fin 4 → α :=
  ![![x,x,y,z], ![x,y,x,z], ![x,y,z,x], ![y,x,x,z], ![y,x,z,x], ![y,z,x,x]]

private lemma classify {α : Type*} (v : Fin 4 → α) (hn : ¬ Function.Injective v) :
    ∃ (j : Fin 6) (x y z : α), v = arrange x y z j := by
  classical
  have h : v 0 = v 1 ∨ v 0 = v 2 ∨ v 0 = v 3 ∨ v 1 = v 2 ∨ v 1 = v 3 ∨ v 2 = v 3 := by
    by_contra! h
    apply hn
    intro a b e
    fin_cases a <;> fin_cases b <;> simp_all
  rcases h with h|h|h|h|h|h
  · refine ⟨0, v 0, v 2, v 3, ?_⟩
    funext i; fin_cases i <;> simp [arrange,h]
  · refine ⟨1, v 0, v 1, v 3, ?_⟩
    funext i; fin_cases i <;> simp [arrange,h]
  · refine ⟨2, v 0, v 1, v 2, ?_⟩
    funext i; fin_cases i <;> simp [arrange,h]
  · refine ⟨3, v 1, v 0, v 3, ?_⟩
    funext i; fin_cases i <;> simp [arrange,h]
  · refine ⟨4, v 1, v 0, v 2, ?_⟩
    funext i; fin_cases i <;> simp [arrange,h]
  · refine ⟨5, v 2, v 0, v 1, ?_⟩
    funext i; fin_cases i <;> simp [arrange,h]

/-- Ordered representations of m by four natural squares with a repeated coordinate. -/
def repeatedRepresentations (m : ℕ) := (((univ : Finset (Fin 4 → Fin (m+1))).filter
    fun v => ∑ i, ((v i : ℕ)^2) = m).filter fun v => ¬ Function.Injective v)

private lemma count (m : ℕ) : (repeatedRepresentations m).card ≤
    6 * ∑ z ∈ range (m.sqrt+1), (reps (m-z^2)).card := by
  classical
  let s := (range (m.sqrt+1)).sigma (fun z => reps (m-z^2))
  let D := (univ : Finset (Fin 6)) ×ˢ s
  let f (d : Fin 6 × (Σ _ : ℕ, ℕ × ℕ)) : Fin 4 → Fin (m+1) :=
    arrange (Fin.ofNat _ d.2.2.2) (Fin.ofNat _ d.2.2.1) (Fin.ofNat _ d.2.1) d.1
  have cover : repeatedRepresentations m ⊆ D.image f := by
    intro v hv
    obtain ⟨hs,hn⟩ := mem_filter.mp hv
    have hvsum := (mem_filter.mp hs).2
    obtain ⟨j,x,y,z,rfl⟩ := classify v hn
    have he : (z : ℕ)^2 + (y : ℕ)^2 + 2*(x : ℕ)^2 = m := by
      apply Eq.trans _ hvsum
      fin_cases j <;> simp [arrange, Fin.sum_univ_succ] <;> ring
    have hx := Nat.le_self_pow (by decide : 2 ≠ 0) (x : ℕ)
    have hy := Nat.le_self_pow (by decide : 2 ≠ 0) (y : ℕ)
    have hz : (z : ℕ) ≤ m.sqrt := Nat.le_sqrt'.mpr (by omega)
    refine mem_image.mpr ⟨(j, ⟨(z : ℕ), (y,x)⟩), mem_product.mpr ⟨mem_univ _, ?_⟩, ?_⟩
    · apply mem_sigma.mpr
      change (z : ℕ) ∈ range (m.sqrt+1) ∧ ((y : ℕ), (x : ℕ)) ∈ reps (m-(z : ℕ)^2)
      simp only [reps, mem_filter, mem_product, mem_range]
      exact ⟨by omega, ⟨by omega, by omega⟩, by omega⟩
    · simp [f, Fin.ofNat_eq_cast]
  calc
    _ ≤ (D.image f).card := card_le_card cover
    _ ≤ D.card := card_image_le
    _ = _ := by simp [D,s,card_sigma]

/-- Uniform in the parity of the represented integer. -/
theorem card_repeatedRepresentations_le (ε : ℝ) (hε : 0 < ε) : ∃ C > (0 : ℝ), ∀ m : ℕ, 1 ≤ m →
    ((repeatedRepresentations m).card : ℝ) ≤ C * (m : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨D,hD,hτ⟩ := divisors_card_le_rpow (ε / 3) (by positivity)
  let B := max 1 (D^3)
  have hB : (1 : ℝ) ≤ B := le_max_left _ _
  refine ⟨12*B, by positivity, ?_⟩
  intro m hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have uniform (N : ℕ) (hle : N ≤ m) : ((reps N).card : ℝ) ≤ B * (m : ℝ)^ε := by
    rcases N.eq_zero_or_pos with rfl | hN
    · have hzero : (reps 0).card = 1 := by decide
      rw [hzero, Nat.cast_one]
      exact one_le_mul_of_one_le_of_one_le hB (Real.one_le_rpow hm1 hε.le)
    · calc
        ((reps N).card : ℝ) ≤ (N.divisors.card : ℝ)^3 := by exact_mod_cast all_rep_count N hN
        _ ≤ (D * (N : ℝ) ^ (ε / 3))^3 := pow_le_pow_left₀ (by positivity) (hτ N) _
        _ = D^3 * (N : ℝ)^ε := by
          rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
          congr 2
          push_cast
          ring
        _ ≤ B * (m : ℝ)^ε := mul_le_mul (le_max_right _ _)
          (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hle) hε.le) (by positivity) (by linarith)
  have hs : (m.sqrt : ℝ) ≤ (m : ℝ)^(1/2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast (Nat.le_sqrt'.mp (le_refl m.sqrt))
  have hs1 := Real.one_le_rpow hm1 (show (0 : ℝ) ≤ 1/2 by norm_num)
  have hc : ((repeatedRepresentations m).card : ℝ) ≤ 6 * ∑ z ∈ range (m.sqrt+1), ((reps (m-z^2)).card : ℝ) := by
    exact_mod_cast count m
  calc
    _ ≤ _ := hc
    _ ≤ 6 * ∑ _z ∈ range (m.sqrt+1), (B * (m : ℝ)^ε) := by
      gcongr with z hz
      exact uniform _ (Nat.sub_le _ _)
    _ = 6 * ((m.sqrt : ℝ)+1) * (B * (m : ℝ)^ε) := by simp; ring
    _ ≤ 6 * (2 * (m : ℝ)^(1/2 : ℝ)) * (B * (m : ℝ)^ε) := by
      gcongr; linarith
    _ = 12 * B * (m : ℝ)^(1/2 + ε) := by rw [Real.rpow_add (by linarith : 0 < (m : ℝ))]; ring

end RepeatedFourSquares

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_squares_R1_H2_R1.H2 := by
  obtain ⟨C,hC,hbound⟩ := RepeatedFourSquares.card_repeatedRepresentations_le (1/4) (by norm_num)
  have grows : Tendsto (fun m : ℕ => (m : ℝ)^(1/4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, grows.eventually (eventually_gt_atTop (2*C))] with m hm hg
  intro _
  have hp : 0 < (m : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have hu := hbound m hm
  have he : (m : ℝ)^(1/2 + 1/4 : ℝ) * (m : ℝ)^(1/4 : ℝ) = m := by
    rw [← Real.rpow_add hp]; norm_num
  have hsmall := mul_lt_mul_of_pos_left hg (Real.rpow_pos_of_pos hp (1/2 + 1/4))
  change 2 * (RepeatedFourSquares.repeatedRepresentations m).card < m
  exact_mod_cast (show 2 * ((RepeatedFourSquares.repeatedRepresentations m).card : ℝ) < m by nlinarith only [hu, he, hsmall])
