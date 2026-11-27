import FormalConjectures.ErdosProblems.«830»
import Mathlib.Data.Nat.Periodic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.BigOperators.Field

/-!
# Proof that the amicable numbers have asymptotic density zero (Erdős Problem 830)

Proves `Erdos830.erdos_830.variants.erdos` following Erdős, *On amicable numbers* (1955),
pp. 109–111:
- `R1`: reduction to divisibility of `σ 1 n`, large-divisor tail bound, and right continuity
  of the abundancy ratio distribution at `2`.
- `H1`: every fixed positive integer divides `σ 1 n` almost everywhere (prime-class sieve).
- `H2`: large-divisor tail contribution is small in density.
- `H3`: Davenport's right-continuity / anti-concentration bound for `σ(n)/n` near `2`.
-/

namespace OMA.Erdos830Solution

namespace R1

open scoped ArithmeticFunction.sigma Classical
open Finset Filter Erdos830 Asymptotics

/-- Every fixed positive integer divides the divisor sum almost everywhere (Erdős, Lemma 2). -/
def H1 : Prop := ∀ m : ℕ, 0 < m → ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
  (((Icc 1 N).filter (fun n => ¬ m ∣ σ 1 n)).card:ℝ) ≤ ε*N

/-- The contribution from divisors above B is small in density (Erdős, Lemma 3). -/
def H2 : Prop := ∀ η ε : ℝ, 0<η → 0<ε → ∃ B : ℕ, ∀ᶠ N : ℕ in atTop,
  (((Icc 1 N).filter (fun n => η ≤ ((σ 1 n : ℝ)/n) - (∑ d ∈ n.divisors.filter (· ≤ B), (1:ℝ)/d))).card:ℝ) ≤ ε*N

/-- Right continuity at 2 of the distribution of the abundancy ratio (Davenport). -/
def H3 : Prop := ∀ ε : ℝ, 0<ε → ∃ η : ℝ, 0<η ∧ ∀ᶠ N : ℕ in atTop,
  (((Icc 1 N).filter (fun n => 2 < ((σ 1 n : ℝ)/n) ∧ ((σ 1 n : ℝ)/n) ≤ 2+η)).card:ℝ) ≤ ε*N

lemma ratio_eq {n : ℕ} (hn : 0<n) : ((σ 1 n : ℝ)/n) = ∑ d ∈ n.divisors, (1:ℝ)/d := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [ArithmeticFunction.sigma_one_apply,Nat.cast_sum,← Nat.sum_div_divisors n (fun d => (d:ℝ)),Finset.sum_div]
  apply sum_congr rfl; intro d hd
  have hd' : (d:ℝ)≠0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd']
  field_simp

lemma compare {a b B : ℕ} (hb : 0<b) (ham : IsAmicable a b) (hfac : B.factorial ∣ σ 1 a) :
    (∑ d ∈ a.divisors.filter (· ≤ B), (1:ℝ)/d) ≤ (σ 1 b : ℝ)/b := by
  rw [ratio_eq hb]
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
  intro d hd
  obtain ⟨hd,hB⟩ := mem_filter.mp hd
  have hda := Nat.dvd_of_mem_divisors hd
  have h := (Nat.dvd_factorial (Nat.pos_of_mem_divisors hd) hB).trans hfac
  rw [ham.left] at h
  exact Nat.mem_divisors.mpr ⟨(Nat.dvd_add_iff_right hda).mpr h,hb.ne'⟩

theorem main : H1 → H2 → H3 → type_of% @Erdos830.erdos_830.variants.erdos := by
  intro h1 h2 h3
  let ratio (n : ℕ) : ℝ := (σ 1 n : ℝ)/n
  let partialRatio (B n : ℕ) : ℝ := ∑ d ∈ n.divisors.filter (· ≤ B), (1:ℝ)/d
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  have hδ : 0 < ε/3 := by positivity
  obtain ⟨η,hη,hnear⟩ := h3 _ hδ
  obtain ⟨B,htail⟩ := h2 η _ hη hδ
  have hbad := h1 B.factorial (Nat.factorial_pos _) _ hδ
  filter_upwards [tendsto_nat_floor_atTop.eventually (hbad.and (htail.and hnear)),eventually_ge_atTop (0:ℝ)] with x hx hx0
  let N := ⌊x⌋₊
  let P := ((Icc 1 N) ×ˢ (Icc 1 N)).filter fun q : ℕ × ℕ => q.1 ≤ q.2 ∧ IsAmicable q.1 q.2
  let E := (Icc 1 N).filter (fun n => ¬ B.factorial ∣ σ 1 n)
  let F := (Icc 1 N).filter (fun n => η ≤ ratio n - partialRatio B n)
  let G := (Icc 1 N).filter (fun n => 2 < ratio n ∧ ratio n ≤ 2+η)
  have maps : Set.MapsTo Prod.fst (P:Set (ℕ×ℕ)) (↑((E∪F)∪G):Set ℕ) := by
    rintro ⟨a,b⟩ hab
    obtain ⟨hm,hle,ham⟩ := mem_filter.mp hab
    obtain ⟨ha,hb⟩ := mem_product.mp hm
    by_cases hbad' : ¬ B.factorial ∣ σ 1 a
    · exact mem_union_left _ (mem_union_left _ (show a ∈ E by simpa only [E,mem_filter] using And.intro ha hbad'))
    by_cases hf : η ≤ ratio a - partialRatio B a
    · exact mem_union_left _ (mem_union_right _ (show a ∈ F by simpa only [F,mem_filter] using And.intro ha hf))
    apply mem_union_right _ (show a ∈ G from ?_)
    simp only [G,mem_filter]; refine ⟨ha,?_⟩
    have hapos := (mem_Icc.mp ha).1
    have hbpos := (mem_Icc.mp hb).1
    have hlt : a<b := lt_of_le_of_ne hle ham.ne
    have ha' : 0<(a:ℝ) := by exact_mod_cast hapos
    have hb' : 0<(b:ℝ) := by exact_mod_cast hbpos
    have hab' : (a:ℝ)<b := by exact_mod_cast hlt
    have hcmp : partialRatio B a ≤ ratio b := compare hbpos ham (not_not.mp hbad')
    have hupper : ratio b ≤ 2 := by
      dsimp only [ratio]
      rw [div_le_iff₀ hb',ham.right,Nat.cast_add]; linarith
    refine ⟨?_,by linarith [lt_of_not_ge hf]⟩
    dsimp only [ratio]
    rw [lt_div_iff₀ ha',ham.left,Nat.cast_add]; linarith
  have inj : Set.InjOn Prod.fst (P:Set (ℕ×ℕ)) := by
    rintro ⟨a,b⟩ hab ⟨a',b'⟩ hab' he
    change a=a' at he
    subst a'
    have h := (mem_filter.mp hab).2.2.left
    have h' := (mem_filter.mp hab').2.2.left
    exact Prod.ext rfl (Nat.add_left_cancel (h.symm.trans h'))
  have hbound := (card_le_card_of_injOn Prod.fst maps inj).trans (card_union_le _ _)
  have hnat : P.card ≤ E.card+F.card+G.card := hbound.trans (Nat.add_le_add_right (card_union_le _ _) _)
  rcases hx with ⟨he,hf,hg⟩
  change (E.card:ℝ) ≤ ε/3*N at he
  change (F.card:ℝ) ≤ ε/3*N at hf
  change (G.card:ℝ) ≤ ε/3*N at hg
  change ‖(P.card:ℝ)‖ ≤ ε*‖x‖
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg hx0]
  have hr : (P.card:ℝ) ≤ E.card+F.card+G.card := by exact_mod_cast hnat
  have hn : (N:ℝ)≤x := Nat.floor_le hx0
  nlinarith only [hr,he,hf,hg,mul_le_mul_of_nonneg_left hn hε.le]

end R1

section H1Section

open Filter Finset ArithmeticFunction
open scoped Topology BigOperators ArithmeticFunction.sigma

namespace AmicableDivisibility

lemma periodic_hasDensity {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hd : 0 < d) (hp : Function.Periodic p d) :
    {n : ℕ | p n}.HasDensity (Nat.count p d / (d : ℝ)) := by
  classical
  let count := Nat.count p
  let density : ℝ := (count d : ℝ) / (d : ℝ)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdensity : 0 ≤ density := div_nonneg (Nat.cast_nonneg _) hd'.le
  have hdensity_le : density ≤ 1 := by
    apply (div_le_one hd').mpr
    exact_mod_cast Nat.count_le (p := p) (n := d)
  have hshift (n : ℕ) : Nat.count (fun i ↦ p (i + d)) n = count n := by
    change Nat.count (fun i ↦ p (i + d)) n = Nat.count p n
    simp only [Nat.count_eq_card_filter_range]
    congr 1
    ext i
    simp only [Finset.mem_filter, hp i]
  have hblocks (q r : ℕ) : count (q * d + r) = q * count d + count r := by
    induction q with
    | zero => simp
    | succ q ih =>
      change Nat.count p ((q + 1) * d + r) = (q + 1) * count d + count r
      rw [Nat.succ_mul, add_right_comm (q * d) d r, Nat.count_add', hshift]
      change count (q * d + r) + count d = (q + 1) * count d + count r
      rw [ih, Nat.succ_mul, add_right_comm]
  have hncard (n : ℕ) : ({m : ℕ | p m} ∩ Set.Iio n).ncard = count n := by
    rw [show {m : ℕ | p m} ∩ Set.Iio n =
        (↑((Finset.range n).filter p) : Set ℕ) by ext m; simp [and_comm],
      Set.ncard_coe_finset, ← Nat.count_eq_card_filter_range]
  have herr : ∀ᶠ n : ℕ in atTop, |(count n : ℝ) / (n : ℝ) - density| ≤ (d : ℝ) / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    let r := n % d
    let q := n / d
    have hsplit : q * d + r = n := by simpa [q, r, mul_comm] using Nat.div_add_mod n d
    have hcount : q * count d + count r = count n := (hblocks q r).symm.trans (congrArg count hsplit)
    have hsplit' : (q : ℝ) * (d : ℝ) + (r : ℝ) = (n : ℝ) := by exact_mod_cast hsplit
    have hcount' : (q : ℝ) * (count d : ℝ) + (count r : ℝ) = (count n : ℝ) := by
      exact_mod_cast hcount
    have hd_mul : (d : ℝ) * density = (count d : ℝ) :=
      mul_div_cancel₀ _ hd'.ne'
    have hn' : (0 : ℝ) < n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn).bot_lt
    have hr : (r : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Nat.mod_lt n hd).le
    have hcount_r : (count r : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.count_le (p := p)
    have herror : (count n : ℝ) / (n : ℝ) - density =
        ((count r : ℝ) - (r : ℝ) * density) / (n : ℝ) := by
      apply (eq_div_iff hn'.ne').mpr
      calc
        _ = (count n : ℝ) - (n : ℝ) * density := by field_simp
        _ = _ := by rw [← hcount', ← hsplit', add_mul, mul_assoc, hd_mul]; ring
    rw [herror, abs_div, abs_of_pos hn']
    apply div_le_div_of_nonneg_right _ hn'.le
    apply abs_le.mpr
    constructor
    · have h := mul_le_mul_of_nonneg_left hdensity_le (Nat.cast_nonneg r)
      linarith [Nat.cast_nonneg (α := ℝ) (count r)]
    · have h := mul_nonneg (Nat.cast_nonneg (α := ℝ) r) hdensity
      linarith
  have ht : Tendsto (fun n : ℕ ↦ (count n : ℝ) / (n : ℝ) - density) atTop (𝓝 0) := by
    have hu := tendsto_const_div_atTop_nhds_zero_nat (d : ℝ)
    have hl : Tendsto (fun n : ℕ ↦ -((d : ℝ) / n)) atTop (𝓝 0) := by
      simpa only [neg_zero] using hu.neg
    refine hl.squeeze' hu ?_ ?_
    · exact herr.mono fun n hn ↦ (abs_le.mp hn).1
    · exact herr.mono fun n hn ↦ (abs_le.mp hn).2
  simpa [Set.HasDensity, Set.partialDensity, hncard, density, count] using ht.add_const density

noncomputable def residues (m : ℕ) (P : ZMod m → Prop) : ℕ :=
  Nat.card {x : ZMod m // P x}

lemma density_of_residues {m : ℕ} (hm : 0 < m) (P : ZMod m → Prop) :
    {n : ℕ | P (n : ZMod m)}.HasDensity (residues m P / (m : ℝ)) := by
  classical
  have : NeZero m := ⟨hm.ne'⟩
  have hper : Function.Periodic (fun n : ℕ => P (n : ZMod m)) m := by
    intro n
    change P ((↑(n + m) : ZMod m)) = P (n : ZMod m)
    rw [Nat.cast_add, ZMod.natCast_self, add_zero]
  have hc : Nat.count (fun n : ℕ => P (n : ZMod m)) m = residues m P := by
    rw [Nat.count_eq_card_filter_range, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    refine
      { toFun := fun x => ⟨(x.val : ZMod m), (Finset.mem_filter.mp x.property).2⟩
        invFun := fun x => ⟨x.val.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
          (ZMod.val_lt x.val), by simpa only [ZMod.natCast_zmod_val] using x.property⟩⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro x
      apply Subtype.ext
      exact ZMod.val_natCast_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp x.property).1)
    · intro x
      apply Subtype.ext
      exact ZMod.natCast_zmod_val x.val
  simpa only [hc] using periodic_hasDensity hm hper

lemma residue_system (S : Finset ℕ) (d : ℕ → ℕ) (hd : ∀ i ∈ S, 0 < d i)
    (hcop : (S : Set ℕ).Pairwise fun i j => (d i).Coprime (d j))
    (P : (i : ℕ) → ZMod (d i) → Prop) :
    ∃ R : ZMod (∏ i ∈ S, d i) → Prop,
      (∀ n : ℕ, R (n : ZMod (∏ i ∈ S, d i)) ↔ ∀ i ∈ S, P i (n : ZMod (d i))) ∧
      residues _ R = ∏ i ∈ S, residues (d i) (P i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => True, by simp, ?_⟩
    simp [residues]
  | @insert i S hi ih =>
    have hdi := hd i (Finset.mem_insert_self _ _)
    have hds : ∀ j ∈ S, 0 < d j := fun j hj => hd j (Finset.mem_insert_of_mem hj)
    have hcs : (S : Set ℕ).Pairwise (fun i j => (d i).Coprime (d j)) :=
      hcop.mono fun _ hj => Finset.mem_insert_of_mem hj
    obtain ⟨RS, hRS, hcRS⟩ := ih hds hcs
    rw [Finset.prod_insert hi]
    have hci : (d i).Coprime (∏ j ∈ S, d j) := Nat.Coprime.prod_right fun j hj =>
      hcop (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj)
        (fun h => hi (h.symm ▸ hj))
    let e := ZMod.chineseRemainder hci
    refine ⟨fun x => P i (e x).1 ∧ RS (e x).2, ?_, ?_⟩
    · intro n
      change (P i (e (↑n)).1 ∧ RS (e (↑n)).2) ↔ _
      simp only [map_natCast, Prod.fst_natCast, Prod.snd_natCast, hRS, Finset.forall_mem_insert]
    · rw [Finset.prod_insert hi, ← hcRS]
      unfold residues
      rw [← Nat.card_prod]
      apply Nat.card_congr
      exact
        { toFun := fun x => (⟨(e x.val).1, x.property.1⟩, ⟨(e x.val).2, x.property.2⟩)
          invFun := fun x => ⟨e.symm (x.1.val, x.2.val), by simpa only [e.apply_symm_apply]
            using ⟨x.1.property, x.2.property⟩⟩
          left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
          right_inv := fun x => Prod.ext
            (Subtype.ext (congrArg Prod.fst (e.apply_symm_apply _)))
            (Subtype.ext (congrArg Prod.snd (e.apply_symm_apply _))) }

lemma density_system (S : Finset ℕ) (d : ℕ → ℕ) (hd : ∀ i ∈ S, 0 < d i)
    (hcop : (S : Set ℕ).Pairwise fun i j => (d i).Coprime (d j))
    (P : (i : ℕ) → ZMod (d i) → Prop) :
    {n : ℕ | ∀ i ∈ S, P i (n : ZMod (d i))}.HasDensity
      (∏ i ∈ S, residues (d i) (P i) / (d i : ℝ)) := by
  obtain ⟨R, he, hR⟩ := residue_system S d hd hcop P
  have hpos : 0 < ∏ i ∈ S, d i := Finset.prod_pos hd
  have h := density_of_residues hpos R
  rw [show {n : ℕ | R (n : ZMod (∏ i ∈ S, d i))} =
      {n : ℕ | ∀ i ∈ S, P i (n : ZMod (d i))} by ext n; exact he n,
    hR, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib] at h
  exact h

open ArithmeticFunction in
lemma not_summable_primes_class {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) :
    ¬ Summable (fun p : ℕ => if p.Prime ∧ (p : ZMod q) = a then (1 : ℝ) / p else 0) := by
  classical
  intro hsum
  let c := vonMangoldt.residueClass a
  let g (t : ℝ) (n : ℕ) := (t - 1) * (c n / (n : ℝ) ^ t)
  let bound (n : ℕ) :=
    (if n.Prime ∧ (n : ZMod q) = a then (1 : ℝ) / n else 0) +
      (if n.Prime then 0 else c n) / n
  have hb : Summable bound := hsum.add (vonMangoldt.summable_residueClass_non_primes_div a)
  have hnear : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), t ∈ Set.Ioc (1 : ℝ) 2 := by
    have h₁ : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), 1 < t := self_mem_nhdsWithin
    have h₂ : ∀ᶠ t : ℝ in 𝓝 (1 : ℝ), t < 2 := Iio_mem_nhds (by norm_num)
    exact (h₁.and (h₂.filter_mono nhdsWithin_le_nhds)).mono fun _ h => ⟨h.1, h.2.le⟩
  have ht : Tendsto (fun t : ℝ => ∑' n, g t n) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have H : Tendsto (fun t : ℝ => ∑' n, g t n) (𝓝[>] (1 : ℝ))
        (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
      refine tendsto_tsum_of_dominated_convergence hb (fun n => ?_) (hnear.mono fun t ht n => ?_)
      · have hc : ContinuousAt (fun t : ℝ => g t n) 1 := by
          by_cases hn : n = 0
          · simpa [g, c, hn] using
              (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) (1 : ℝ))
          · exact (continuousAt_id.sub continuousAt_const).mul
              (continuousAt_const.div
                (Real.continuousAt_const_rpow (by exact_mod_cast hn))
                (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _).ne')
        have he : g 1 n = 0 := by simp [g]
        rw [← he]
        exact hc.continuousWithinAt
      · have h0 : 0 ≤ g t n := mul_nonneg (sub_nonneg.mpr ht.1.le)
          (div_nonneg (vonMangoldt.residueClass_nonneg a n)
            (Real.rpow_nonneg (Nat.cast_nonneg n) t))
        rw [Real.norm_of_nonneg h0]
        by_cases hn0 : n = 0
        · simp [g, c, bound, hn0]
        have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
        by_cases hp : n.Prime
        · by_cases hclass : (n : ZMod q) = a
          · have hc : c n = Real.log n := by
              simp [c, vonMangoldt.residueClass, hclass, vonMangoldt_apply_prime hp]
            simp only [g, hc, bound, hp, hclass, and_self, if_true, zero_div, add_zero]
            rw [← mul_div_assoc]
            have hden : (n : ℝ) ^ t = (n : ℝ) ^ (t - 1) * n := by
              calc
                _ = (n : ℝ) ^ ((t - 1) + 1) := by ring_nf
                _ = _ := by rw [Real.rpow_add hn, Real.rpow_one]
            rw [hden, div_mul_eq_div_div]
            apply div_le_div_of_nonneg_right _ hn.le
            apply (div_le_one (Real.rpow_pos_of_pos hn _)).mpr
            rw [Real.rpow_def_of_pos hn, mul_comm (Real.log n)]
            exact (le_add_of_nonneg_right (by norm_num : 0 ≤ (1 : ℝ))).trans
              (Real.add_one_le_exp _)
          · simp [g, bound, c, vonMangoldt.residueClass, hp, hclass]
        · simp only [bound, hp, false_and, if_false, zero_add]
          have hden : (n : ℝ) ≤ (n : ℝ) ^ t := calc
            (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 ht.1.le
          exact (mul_le_of_le_one_left
            (div_nonneg (vonMangoldt.residueClass_nonneg a n) (Real.rpow_nonneg hn.le _))
            (by linarith [ht.2])).trans
            (div_le_div_of_nonneg_left (vonMangoldt.residueClass_nonneg a n) hn hden)
    simpa only [tsum_zero] using H
  obtain ⟨C, hC⟩ := vonMangoldt.LSeries_residueClass_lower_bound ha
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ),
      (q.totient : ℝ)⁻¹ - C * (t - 1) ≤ ∑' n, g t n := by
    filter_upwards [hnear] with t ht
    simp only [g, tsum_mul_left]
    have hc := mul_le_mul_of_nonneg_left (hC ht) (sub_nonneg.mpr ht.1.le)
    have he : (t - 1) * ((q.totient : ℝ)⁻¹ / (t - 1)) = (q.totient : ℝ)⁻¹ := by
      field_simp [sub_ne_zero.mpr ht.1.ne']
    rw [mul_sub, he] at hc
    simpa only [mul_comm C] using hc
  have hlim : Tendsto (fun t : ℝ => (q.totient : ℝ)⁻¹ - C * (t - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℝ)⁻¹)) := by
    have hcont : ContinuousAt (fun t : ℝ => (q.totient : ℝ)⁻¹ - C * (t - 1)) 1 :=
      continuousAt_const.sub (continuousAt_const.mul (continuousAt_id.sub continuousAt_const))
    have hh : Tendsto (fun t : ℝ => (q.totient : ℝ)⁻¹ - C * (t - 1))
        (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℝ)⁻¹ - C * (1 - 1))) :=
      hcont.continuousWithinAt
    simpa only [sub_self, mul_zero, sub_zero] using hh
  have hnonpos := le_of_tendsto_of_tendsto hlim ht hbound
  have hpos : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr q.pos_of_neZero
  exact (inv_pos.mpr hpos).not_ge hnonpos

lemma small_product {P : ℕ → Prop} [DecidablePred P] {w : ℕ → ℝ}
    (hw : ∀ p, 0 ≤ w p) (hw1 : ∀ p, w p ≤ 1)
    (hs : ¬ Summable (fun p => if P p then w p else 0)) {ε : ℝ} (he : 0 < ε) :
    ∃ S : Finset ℕ, (∀ p ∈ S, P p) ∧ (∏ p ∈ S, (1 - w p)) < ε := by
  have hd := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => by split_ifs <;> simp [hw])).mp hs
  obtain ⟨N, hN⟩ := (eventually_atTop.mp ((tendsto_atTop.mp hd) (1 - Real.log ε)))
  let S := (Finset.range N).filter P
  have hsum : 1 - Real.log ε ≤ ∑ p ∈ S, w p := by
    simpa only [S, Finset.sum_filter] using hN N le_rfl
  refine ⟨S, fun p hp => (Finset.mem_filter.mp hp).2, ?_⟩
  calc
    _ ≤ ∏ p ∈ S, Real.exp (-w p) :=
      Finset.prod_le_prod (fun p _ => sub_nonneg.mpr (hw1 p)) fun p _ => by
        simpa only [neg_add_eq_sub] using Real.add_one_le_exp (-w p)
    _ = Real.exp (-∑ p ∈ S, w p) := by rw [← Real.exp_sum, Finset.sum_neg_distrib]
    _ < ε := by
      rw [← Real.exp_log he, Real.exp_lt_exp]
      linarith

noncomputable def hit (p : ℕ) : Finset (ZMod (p ^ 2)) := by
  classical
  exact (Finset.Ico 1 p).image fun k => ((p * k : ℕ) : ZMod (p ^ 2))

lemma mem_hit {p n : ℕ} (hp : p.Prime) :
    (n : ZMod (p ^ 2)) ∈ hit p ↔ p ∣ n ∧ ¬ p ^ 2 ∣ n := by
  classical
  have hpos : 0 < p ^ 2 := pow_pos hp.pos _
  have hdiv : p ∣ p ^ 2 := dvd_pow_self p (by decide)
  change _ ∈ Finset.image (fun k : ℕ => ((p * k : ℕ) : ZMod (p ^ 2))) (.Ico 1 p) ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨k, hk, he⟩
    obtain ⟨hk₁, hk₂⟩ := Finset.mem_Ico.mp hk
    have hlt : p * k < p ^ 2 := by rw [pow_two]; exact Nat.mul_lt_mul_of_pos_left hk₂ hp.pos
    have hr : n % p ^ 2 = p * k :=
      ((ZMod.natCast_eq_natCast_iff' _ _ _).mp he.symm).trans (Nat.mod_eq_of_lt hlt)
    refine ⟨(Nat.dvd_mod_iff hdiv).mp ⟨k, hr⟩, ?_⟩
    intro h
    rw [Nat.mod_eq_zero_of_dvd h] at hr
    exact (Nat.mul_pos hp.pos (by omega : 0 < k)).ne' hr.symm
  · rintro ⟨hd, hn⟩
    obtain ⟨k, hk⟩ := (Nat.dvd_mod_iff hdiv).mpr hd
    have hlt := Nat.mod_lt n hpos
    rw [hk, pow_two] at hlt
    have hk₂ := lt_of_mul_lt_mul_left' hlt
    have hk₁ : 1 ≤ k := by
      by_contra! H
      have : k = 0 := by omega
      exact hn (Nat.dvd_of_mod_eq_zero (by simpa [this] using hk))
    refine ⟨k, Finset.mem_Ico.mpr ⟨hk₁, hk₂⟩, ?_⟩
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
      ((Nat.mod_eq_of_lt (hk ▸ Nat.mod_lt n hpos)).trans hk.symm)

lemma residues_avoids_hit (p : ℕ) (hp : p.Prime) :
    residues (p ^ 2) (fun x => x ∉ hit p) / ((p ^ 2 : ℕ) : ℝ) =
      1 - (p - 1 : ℕ) / (p : ℝ) ^ 2 := by
  classical
  have : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hc : (hit p).card = p - 1 := by
    change ((Finset.Ico 1 p).image (fun k => ((p * k : ℕ) : ZMod (p ^ 2)))).card = _
    rw [Finset.card_image_of_injOn, Nat.card_Ico]
    intro i hi j hj he
    have hlt (k : ℕ) (hk : k ∈ Finset.Ico 1 p) : p * k < p ^ 2 := by
      rw [pow_two]
      exact Nat.mul_lt_mul_of_pos_left (Finset.mem_Ico.mp hk).2 hp.pos
    have hv := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt (hlt i hi), ZMod.val_natCast_of_lt (hlt j hj)] at hv
    exact Nat.eq_of_mul_eq_mul_left hp.pos hv
  simp only [residues, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_coe,
    ZMod.card, hc]
  have hlt : p - 1 ≤ p ^ 2 := (Nat.sub_le _ _).trans (by rw [pow_two]; exact Nat.le_mul_self _)
  have hpos : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity [hp.pos]
  rw [Nat.cast_sub hlt, Nat.cast_pow, sub_div, div_self hpos.ne']

lemma divisor_of_sigma {n p q : ℕ} (hp : p.Prime) (hclass : (p : ZMod q) = -1)
    (hd : p ∣ n) (hn : ¬ p ^ 2 ∣ n) : q ∣ σ 1 n := by
  obtain ⟨k, rfl⟩ := hd
  have hpk : p.Coprime k := hp.coprime_iff_not_dvd.mpr (fun ⟨j, hj⟩ =>
    hn ⟨j, by rw [hj, pow_two, mul_assoc]⟩)
  have hpr : σ 1 p = 1 + p := by
    simpa [Finset.sum_range_succ] using sigma_one_apply_prime_pow (i := 1) hp
  have hq : q ∣ 1 + p := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simp [hclass]
  rw [isMultiplicative_sigma.map_mul_of_coprime hpk, hpr]
  exact dvd_mul_of_dvd_left hq _

lemma density_small_sieve {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ (p : ZMod q) = a) ∧
      ∃ ρ : ℝ, ρ < ε ∧ {n : ℕ | ∀ p ∈ S, (n : ZMod (p ^ 2)) ∉ hit p}.HasDensity ρ := by
  classical
  let w (p : ℕ) := (p - 1 : ℕ) / (p : ℝ) ^ 2
  have hw₀ (p : ℕ) : 0 ≤ w p := by dsimp [w]; positivity
  have hw₁ (p : ℕ) : w p ≤ 1 := by
    apply div_le_one_of_le₀ _ (sq_nonneg _)
    exact_mod_cast ((Nat.sub_le p 1).trans (by rw [pow_two]; exact Nat.le_mul_self _))
  let P (p : ℕ) := p.Prime ∧ (p : ZMod q) = a
  have hsum : ¬ Summable (fun p : ℕ => if P p then w p else 0) := by
    intro h
    apply not_summable_primes_class a ha
    refine (h.mul_left 2).of_nonneg_of_le (fun n => by split_ifs <;> positivity) fun n => ?_
    change (if P n then (1 : ℝ) / n else 0) ≤ 2 * if P n then w n else 0
    by_cases hn : P n
    · simp only [hn, if_true, w]
      have hp := hn.1.two_le
      have hp' : (2 : ℝ) ≤ n := by exact_mod_cast hp
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      field_simp
      nlinarith
    · simp [hn]
  obtain ⟨S, hS, hs⟩ := small_product hw₀ hw₁ hsum hε
  refine ⟨S, hS, _, hs, ?_⟩
  have hd : ∀ p ∈ S, 0 < p ^ 2 := fun p hp => pow_pos (hS p hp).1.pos _
  have hc : (S : Set ℕ).Pairwise (fun p r => (p ^ 2).Coprime (r ^ 2)) := by
    intro p hp r hr hpr
    exact Nat.Coprime.pow _ _ (((hS p hp).1.coprime_iff_not_dvd).mpr fun hd =>
      hpr (((Nat.dvd_prime (hS r hr).1).mp hd).resolve_left (hS p hp).1.ne_one))
  have hD := density_system S (fun p => p ^ 2) hd hc (fun p x => x ∉ hit p)
  convert hD using 1
  exact Finset.prod_congr rfl fun p hp => (residues_avoids_hit p (hS p hp).1).symm

noncomputable def countSet (A : Set ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (· ∈ A)

lemma mem_countSet {n N : ℕ} {A : Set ℕ} :
    n ∈ countSet A N ↔ n < N ∧ n ∈ A := by
  classical
  simp [countSet]

lemma partial_density_count (A : Set ℕ) (N : ℕ) :
    A.partialDensity Set.univ N = (countSet A N).card / (N : ℝ) := by
  rw [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  congr 1
  rw [show A ∩ Set.Iio N = (↑(countSet A N) : Set ℕ) by
    ext k; simp [mem_countSet, and_comm], Set.ncard_coe_finset]

end AmicableDivisibility

theorem h1_proof : R1.H1 := by
  classical
  intro m hm ε hε
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨S, hS, ρ, hρ, hD⟩ := AmicableDivisibility.density_small_sieve (-1 : ZMod m) (by simp)
    (show 0 < ε / 2 by positivity)
  let D : Set ℕ := {n | ∀ p ∈ S, (n : ZMod (p ^ 2)) ∉ AmicableDivisibility.hit p}
  have hsmall : ∀ᶠ N in atTop, D.partialDensity Set.univ N < ε / 2 :=
    hD.eventually_lt tendsto_const_nhds hρ
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    rw [tendsto_atTop_atTop]
    exact fun b => ⟨b, fun n hn => by omega⟩
  filter_upwards [hshift.eventually hsmall, eventually_ge_atTop 1] with N hN hN₀
  have hcover : ((Icc 1 N).filter (fun n => ¬ m ∣ σ 1 n)) ⊆ AmicableDivisibility.countSet D (N + 1) := by
    intro n hn
    obtain ⟨hinterval, hbad⟩ := mem_filter.mp hn
    refine AmicableDivisibility.mem_countSet.mpr ⟨Nat.lt_succ_of_le (mem_Icc.mp hinterval).2, ?_⟩
    intro p hp hhit
    obtain ⟨hd, hnd⟩ := (AmicableDivisibility.mem_hit (hS p hp).1).mp hhit
    exact hbad (AmicableDivisibility.divisor_of_sigma (hS p hp).1 (hS p hp).2 hd hnd)
  have hc : ((((Icc 1 N).filter (fun n => ¬ m ∣ σ 1 n)).card : ℕ) : ℝ) ≤
      (AmicableDivisibility.countSet D (N + 1)).card := by
    exact_mod_cast Finset.card_le_card hcover
  rw [AmicableDivisibility.partial_density_count] at hN
  have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < ((N + 1 : ℕ) : ℝ))).mp hN
  have hn : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast (show N + 1 ≤ 2 * N by omega)
  calc
    _ ≤ ((AmicableDivisibility.countSet D (N + 1)).card : ℝ) := hc
    _ ≤ (ε / 2) * ((N + 1 : ℕ) : ℝ) := h.le
    _ ≤ (ε / 2) * (2 * (N : ℝ)) := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = ε * N := by ring

end H1Section

section H2Section

open Filter Finset R1
open scoped ArithmeticFunction.sigma

private theorem divisor_tail_eq {n B : ℕ} (hn : 0 < n) :
    (σ 1 n : ℝ) / n - (∑ d ∈ n.divisors.filter (· ≤ B), (1 : ℝ) / d) =
      ∑ d ∈ n.divisors.filter (B < ·), (1 : ℝ) / d := by
  classical
  rw [ratio_eq hn]
  have h := sum_filter_add_sum_filter_not (s := n.divisors) (p := (· ≤ B)) (fun d => (1 : ℝ) / d)
  simp only [not_le] at h
  linarith only [h]

private theorem card_multiples_le (N d : ℕ) (hd : 0 < d) :
    ((Icc 1 N).filter (d ∣ ·)).card ≤ N / d := by
  have hmap : Set.MapsTo (· / d) (↑((Icc 1 N).filter (d ∣ ·)) : Set ℕ)
      (↑(Icc 1 (N / d)) : Set ℕ) := by
    intro n hn
    obtain ⟨hm, hdiv⟩ := mem_filter.mp (mem_coe.mp hn)
    obtain ⟨hn₁, hn₂⟩ := mem_Icc.mp hm
    apply mem_coe.mpr (mem_Icc.mpr ⟨?_, Nat.div_le_div_right hn₂⟩)
    exact (Nat.le_div_iff_mul_le hd).mpr (by simpa using Nat.le_of_dvd (by omega) hdiv)
  have hinj : Set.InjOn (· / d) (↑((Icc 1 N).filter (d ∣ ·)) : Set ℕ) := by
    intro n hn m hm h
    change n / d = m / d at h
    rw [← Nat.div_mul_cancel (mem_filter.mp (mem_coe.mp hn)).2,
      ← Nat.div_mul_cancel (mem_filter.mp (mem_coe.mp hm)).2, h]
  simpa using card_le_card_of_injOn (· / d) hmap hinj

private theorem recip_square_interval {B N : ℕ} (hB : 0 < B) (hBN : B ≤ N) :
    ∑ d ∈ Icc (B + 1) N, (1 : ℝ) / (d : ℝ)^2 ≤ 1 / B - 1 / N := by
  induction N, hBN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hI : Icc (B + 1) (n + 1) = insert (n + 1) (Icc (B + 1) n) := by
      ext d
      simp only [mem_Icc, mem_insert]
      omega
    rw [hI, sum_insert (by simp)]
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hstep : (1 : ℝ) / ((n : ℝ) + 1)^2 ≤ 1 / n - 1 / ((n : ℝ) + 1) := by
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      field_simp
      nlinarith only [hn']
    push_cast
    linarith only [ih, hstep]

theorem h2_proof : R1.H2 := by
  classical
  intro η ε hη hε
  obtain ⟨B, hB⟩ := exists_nat_gt (max 1 (1 / (ε * η)))
  have hBr : (0 : ℝ) < B := zero_lt_one.trans ((le_max_left _ _).trans_lt hB)
  have hB0 : 0 < B := by exact_mod_cast hBr
  have hsmall : (1 : ℝ) / B ≤ ε * η := by
    apply (div_le_iff₀ hBr).mpr
    have h := (div_lt_iff₀ (mul_pos hε hη)).mp ((le_max_right _ _).trans_lt hB)
    linarith only [h]
  refine ⟨B, ?_⟩
  filter_upwards [eventually_ge_atTop B] with N hBN
  let T : ℕ → ℝ := fun n => ∑ d ∈ n.divisors.filter (B < ·), (1 : ℝ) / d
  let S : Finset ℕ := (Icc 1 N).filter
    (fun n => η ≤ (σ 1 n : ℝ) / n - (∑ d ∈ n.divisors.filter (· ≤ B), (1 : ℝ) / d))
  have hTail : ∀ n ∈ Icc 1 N, T n =
      ∑ d ∈ Icc (B + 1) N, if d ∣ n then (1 : ℝ) / d else 0 := by
    intro n hn
    obtain ⟨hn₁, hn₂⟩ := mem_Icc.mp hn
    rw [← sum_filter]
    dsimp only [T]
    congr 1
    ext d
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, _⟩, hBd⟩
      exact ⟨⟨by omega, (Nat.le_of_dvd (by omega) hd).trans hn₂⟩, hd⟩
    · rintro ⟨⟨hBd, _⟩, hd⟩
      exact ⟨⟨hd, by omega⟩, by omega⟩
  have hContrib (d : ℕ) (hd : d ∈ Icc (B + 1) N) :
      (∑ n ∈ Icc 1 N, if d ∣ n then (1 : ℝ) / d else 0) ≤
        (N : ℝ) * ((1 : ℝ) / (d : ℝ)^2) := by
    have hd₀ : 0 < d := by have := (mem_Icc.mp hd).1; omega
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd₀
    have hmultiples : ((((Icc 1 N).filter (d ∣ ·)).card : ℕ) : ℝ) ≤ (N : ℝ) / d := by
      apply (le_div_iff₀ hd').mpr
      exact_mod_cast (Nat.mul_le_mul_right d (card_multiples_le N d hd₀)).trans (Nat.div_mul_le_self N d)
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    calc
      _ ≤ ((N : ℝ) / d) * (1 / (d : ℝ)) := mul_le_mul_of_nonneg_right hmultiples (by positivity)
      _ = _ := by ring
  change (S.card : ℝ) ≤ ε * N
  apply (mul_le_mul_iff_right₀ hη).mp
  calc
    η * (S.card : ℝ) = ∑ _ ∈ S, η := by simp [nsmul_eq_mul, mul_comm]
    _ ≤ ∑ n ∈ S, T n := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hmem, hlarge⟩ := mem_filter.mp hn
      rw [divisor_tail_eq (show 0 < n by have := (mem_Icc.mp hmem).1; omega)] at hlarge
      exact hlarge
    _ ≤ ∑ n ∈ Icc 1 N, T n :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by dsimp [T]; positivity)
    _ = ∑ d ∈ Icc (B + 1) N, ∑ n ∈ Icc 1 N, if d ∣ n then (1 : ℝ) / d else 0 := by
      rw [sum_comm]
      exact sum_congr rfl hTail
    _ ≤ ∑ d ∈ Icc (B + 1) N, (N : ℝ) * ((1 : ℝ) / (d : ℝ)^2) := sum_le_sum hContrib
    _ ≤ (N : ℝ) * (1 / (B : ℝ)) := by
      rw [← mul_sum]
      have h := recip_square_interval hB0 hBN
      have hnonneg : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith only [h, hnonneg]) (Nat.cast_nonneg N)
    _ ≤ η * (ε * N) := by
      calc
        _ ≤ (N : ℝ) * (ε * η) := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg _)
        _ = _ := by ring

end H2Section

section H3Section

open Finset Filter
open scoped ArithmeticFunction.sigma

namespace E830

private def numerator (S T : Finset ℕ) : ℕ := ∏ p ∈ S, if p ∈ T then p+1 else p

private theorem numerator_inj (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 2 < p)
    {T U : Finset ℕ} (heq : numerator S T = numerator S U) :
    ∀ p ∈ S, p ∈ T ↔ p ∈ U := by
  classical
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert p S hlt ih =>
    have hp := hS p (mem_insert_self ..)
    have hs : ∀ q ∈ S, q.Prime ∧ 2 < q := fun q h => hS q (mem_insert_of_mem h)
    have hpS : p ∉ S := fun h => (lt_irrefl p) (hlt p h)
    have hn (A : Finset ℕ) : ¬ p ∣ numerator S A := by
      rw [numerator, Prime.dvd_finsetProd_iff hp.1.prime]
      rintro ⟨q, hq, hd⟩
      have hqodd := (hs q hq).1.eq_two_or_odd.resolve_left (by have := (hs q hq).2; omega)
      have hpodd := hp.1.eq_two_or_odd.resolve_left (by omega)
      have hqle := hlt q hq
      have hb : 0 < (if q ∈ A then q+1 else q) ∧ (if q ∈ A then q+1 else q) < p := by
        split <;> omega
      exact (not_le_of_gt hb.2) (Nat.le_of_dvd hb.1 hd)
    simp only [numerator, prod_insert hpS] at heq
    have hpd (A : Finset ℕ) : (p ∣ (if p ∈ A then p+1 else p) * numerator S A) ↔ p ∉ A := by
      rw [hp.1.dvd_mul, or_iff_left (hn A)]
      split_ifs with hA
      · simp only [hA, not_true_eq_false, iff_false]
        exact fun hd => hp.1.not_dvd_one ((Nat.dvd_add_iff_right (dvd_refl p)).mpr hd)
      · simp [hA]
    have harg : p ∉ T ↔ p ∉ U := (hpd T).symm.trans (heq ▸ hpd U)
    have hmem : p ∈ T ↔ p ∈ U := not_iff_not.mp harg
    have ht : (if p ∈ T then p+1 else p) = (if p ∈ U then p+1 else p) := if_congr hmem rfl rfl
    have hpos : 0 < (if p ∈ T then p+1 else p) := by split <;> have := hp.1.pos <;> omega
    change (if p ∈ T then p+1 else p) * numerator S T =
      (if p ∈ U then p+1 else p) * numerator S U at heq
    rw [← ht] at heq
    have hrest := ih hs (Nat.eq_of_mul_eq_mul_left hpos heq)
    intro q hq
    rcases mem_insert.mp hq with rfl | hq
    · exact hmem
    · exact hrest q hq

private noncomputable def primeRatio (S T : Finset ℕ) : ℝ :=
  ∏ p ∈ S, (if p ∈ T then (p+1 : ℝ) / p else 1)

private theorem primeRatio_quot (S T : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    primeRatio S T = (numerator S T : ℝ) / ((∏ p ∈ S, p : ℕ) : ℝ) := by
  rw [primeRatio,numerator,Nat.cast_prod,Nat.cast_prod,← prod_div_distrib]
  apply prod_congr rfl
  intro p hp
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast (hS p hp).ne_zero
  split_ifs <;> simp [hp0]

private theorem primeRatio_sep (S T U : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 2 < p)
    (hdiff : ∃ p ∈ S, ¬ (p ∈ T ↔ p ∈ U)) :
    ((∏ p ∈ S, p : ℕ) : ℝ)⁻¹ ≤ |primeRatio S T - primeRatio S U| := by
  have hpos : 0 < (∏ p ∈ S, p : ℕ) := Finset.prod_pos fun p h => (hS p h).1.pos
  have hposR : (0:ℝ) < ((∏ p ∈ S, p : ℕ) : ℝ) := by exact_mod_cast hpos
  have hn : numerator S T ≠ numerator S U := fun h => by
    obtain ⟨p,hp,hne⟩ := hdiff
    exact hne (numerator_inj S hS h p hp)
  simp only [primeRatio_quot _ _ (fun p hp => (hS p hp).1), ← sub_div, abs_div,
    abs_of_pos hposR, ← one_div]
  apply div_le_div_of_nonneg_right _ hposR.le
  rcases lt_or_gt_of_ne hn with h | h
  · have ha : (numerator S T : ℝ) + 1 ≤ numerator S U := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have ha : (numerator S U : ℝ) + 1 ≤ numerator S T := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith

private noncomputable def ratio (n : ℕ) : ℝ := (σ 1 n : ℝ) / n

private theorem ratio_divisors {n : ℕ} (hn : 0 < n) :
    ratio n = ∑ d ∈ n.divisors, (1:ℝ)/d := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [ratio, ArithmeticFunction.sigma_one_apply, Nat.cast_sum,
    ← Nat.sum_div_divisors n (fun d => (d:ℝ)), Finset.sum_div]
  apply sum_congr rfl
  intro d hd
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd']
  field_simp

private theorem ratio_ge_one {n : ℕ} (hn : 0 < n) : 1 ≤ ratio n := by
  rw [ratio_divisors hn]
  have hmem : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n,hn.ne'⟩
  simpa using (single_le_sum (f := fun d : ℕ => (1:ℝ)/d) (fun d _ => by positivity) hmem)

private theorem ratio_mul {m n : ℕ} (hc : m.Coprime n) :
    ratio (m*n) = ratio m * ratio n := by
  rw [ratio, ratio, ratio, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc,
    Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm]

private theorem gcd_mul_of_coprime {n a b : ℕ} (hc : a.Coprime b) :
    n.gcd (a*b) = n.gcd a * n.gcd b := by
  apply dvd_antisymm (Nat.gcd_mul_right_dvd_mul_gcd ..)
  apply Nat.dvd_gcd
  · exact (hc.gcd_both n n).mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left ..) (Nat.gcd_dvd_left ..)
  · exact Nat.mul_dvd_mul (Nat.gcd_dvd_right ..) (Nat.gcd_dvd_right ..)

private theorem distinct_coprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    p.Coprime q :=
  hp.coprime_iff_not_dvd.mpr fun hd => hne ((Nat.dvd_prime hq).mp hd |>.resolve_left hp.ne_one)

private theorem coprime_power_product (S : Finset ℕ) (hprime : ∀ q ∈ S, Nat.Prime q)
    {p : ℕ} (hp : p.Prime) (hn : p ∉ S) (k : ℕ → ℕ) (e : ℕ) :
    (p^e).Coprime (∏ q ∈ S,q^k q) := by
  apply Nat.Coprime.prod_right
  intro q hq
  have hne : p ≠ q := fun heq => hn (heq ▸ hq)
  exact ((distinct_coprime hp (hprime q hq) hne).pow_left _).pow_right _

private theorem ratio_gcd_square {n p : ℕ} (hp : p.Prime) (hn : ¬ p^2 ∣ n) :
    ratio (n.gcd (p^2)) = if p ∣ n then (p+1 : ℝ)/p else 1 := by
  obtain ⟨i,hi,hg⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right n (p^2))
  have hi2 : i ≠ 2 := fun h => hn (h ▸ hg ▸ Nat.gcd_dvd_left _ _)
  have hi01 : i = 0 ∨ i = 1 := by omega
  have hpp : σ 1 p = p+1 := by
    simpa [Finset.sum_range_succ,add_comm] using (ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp)
  rcases hi01 with rfl | rfl
  · simp only [pow_zero] at hg
    have hnd : ¬ p ∣ n := fun h => hp.not_dvd_one (hg ▸ Nat.dvd_gcd h (dvd_pow_self p (by decide)))
    simp [hg,hnd,ratio]
  · simp only [pow_one] at hg
    have hd : p ∣ n := hg ▸ Nat.gcd_dvd_left _ _
    simp [hg,hd,ratio,hpp]

private theorem ratio_gcd_product (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (n : ℕ) (hn : ∀ p ∈ S, ¬ p^2 ∣ n) :
    ratio (n.gcd (∏ p ∈ S,p^2)) =
      primeRatio S (S.filter (fun p => p ∣ n)) := by
  classical
  calc
    _ = ∏ p ∈ S, ratio (n.gcd (p^2)) := by
      clear hn
      induction S using Finset.induction_on with
      | empty => simp [ratio]
      | @insert p S hpS ih =>
        have hS : ∀ q ∈ S, q.Prime := fun q h => hprime q (mem_insert_of_mem h)
        have hc := coprime_power_product S hS (hprime p (mem_insert_self ..)) hpS (fun _ => 2) 2
        rw [prod_insert hpS, prod_insert hpS, gcd_mul_of_coprime hc,
          ratio_mul (hc.gcd_both n n), ih hS]
    _ = _ := by
      apply prod_congr rfl
      intro p hp
      rw [ratio_gcd_square (hprime p hp) (hn p hp)]
      simp [hp]

private def residueCode (p : ℕ) (hp : p.Prime) (r : Fin (p^2)) :
    Fin p × Fin (p-1) :=
  (⟨r.val / p, (Nat.div_lt_iff_lt_mul hp.pos).mpr (by simpa [pow_two] using r.isLt)⟩,
    ⟨if p ∣ r.val then 0 else r.val % p - 1, by
      split_ifs with hd
      · have := hp.two_le
        omega
      · have := Nat.mod_lt r.val hp.pos
        omega⟩)

private theorem residueCode_inj {p : ℕ} (hp : p.Prime) {r s : Fin (p^2)}
    (hs : p ∣ r.val ↔ p ∣ s.val) (h : residueCode p hp r = residueCode p hp s) : r = s := by
  have hdiv : r.val/p = s.val/p := congrArg (fun v => v.1.val) h
  have hmod : r.val%p = s.val%p := by
    by_cases hr : p ∣ r.val
    · rw [Nat.mod_eq_zero_of_dvd hr, Nat.mod_eq_zero_of_dvd (hs.mp hr)]
    · have hr' := Nat.dvd_iff_mod_eq_zero.not.mp hr
      have hs' := Nat.dvd_iff_mod_eq_zero.not.mp (fun h => hr (hs.mpr h))
      have hcode : r.val % p - 1 = s.val % p - 1 := by
        simpa [residueCode,hr,show ¬ p ∣ s.val from fun h => hr (hs.mpr h)] using
          congrArg (fun v => v.2.val) h
      omega
  apply Fin.ext
  calc
    r.val = r.val % p + p * (r.val/p) := (Nat.mod_add_div ..).symm
    _ = s.val := by rw [hdiv,hmod,Nat.mod_add_div]

private theorem congruent_square_product (S : Finset ℕ) (hp : ∀ p ∈ S, p.Prime)
    {a b : ℕ} (h : ∀ p ∈ S, a ≡ b [MOD p^2]) :
    a ≡ b [MOD ∏ p ∈ S, p^2] := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Nat.modEq_one]
  | @insert p S hpS ih =>
    have hS : ∀ q ∈ S, q.Prime := fun q hq => hp q (mem_insert_of_mem hq)
    rw [prod_insert hpS]
    exact (Nat.modEq_and_modEq_iff_modEq_mul
      (coprime_power_product S hS (hp p (mem_insert_self ..)) hpS (fun _ => 2) 2)).mp
      ⟨h p (mem_insert_self ..), ih hS (fun q hq => h q (mem_insert_of_mem hq))⟩

private noncomputable def intervalGood (S : Finset ℕ) (R : ℕ) (t l : ℝ) (N : ℕ) :
    Finset ℕ := open Classical in
  (Icc 1 N).filter fun n =>
    (∀ p ∈ S, ¬ p^2 ∣ n) ∧
    t ≤ ratio (n.gcd (R * ∏ p ∈ S,p^2)) ∧
    ratio (n.gcd (R * ∏ p ∈ S,p^2)) ≤ t+l

set_option maxHeartbeats 500000 in
private theorem card_intervalGood (S : Finset ℕ) (hp : ∀ p ∈ S, p.Prime ∧ 2 < p)
    (R : ℕ) (hR : 0 < R) (hc : R.Coprime (∏ p ∈ S,p^2)) (t l : ℝ)
    (hl : l < ((∏ p ∈ S,p : ℕ) : ℝ)⁻¹) (N : ℕ) :
    (intervalGood S R t l N).card ≤
      (N/(R * ∏ p ∈ S,p^2)+1)*R*∏ p ∈ S,p*(p-1) := by
  classical
  let Q := R * ∏ p ∈ S,p^2
  let good := intervalGood S R t l N
  let f : good → Fin (N/Q+1) × Fin R × (∀ p : S, Fin p.val × Fin (p.val-1)) := fun n =>
    (⟨n.val/Q, Nat.lt_succ_of_le (Nat.div_le_div_right (mem_Icc.mp (mem_filter.mp n.prop).1).2)⟩,
      ⟨n.val%R,Nat.mod_lt _ hR⟩,
      fun p => residueCode p (hp p p.prop).1
        ⟨n.val%(p.val^2), Nat.mod_lt _ (pow_pos (hp p p.prop).1.pos _)⟩)
  have hf : Function.Injective f := by
    intro a b hab
    have hdiv : a.val/Q = b.val/Q := congrArg (fun x => x.1.val) hab
    have hmodR : a.val%R = b.val%R := congrArg (fun x => x.2.1.val) hab
    have hgR : a.val.gcd R = b.val.gcd R := by
      rw [Nat.gcd_comm a.val R, Nat.gcd_comm b.val R, Nat.gcd_rec R a.val, Nat.gcd_rec R b.val, hmodR]
    obtain ⟨ha, halo,hahi⟩ := (mem_filter.mp a.prop).2
    obtain ⟨hb, hblo,hbhi⟩ := (mem_filter.mp b.prop).2
    have hmul (n : ℕ) (hn : ∀ p ∈ S, ¬ p^2 ∣ n) :
        ratio (n.gcd Q) = ratio (n.gcd R) * primeRatio S (S.filter (fun p => p ∣ n)) := by
      simp only [Q]
      rw [gcd_mul_of_coprime hc, ratio_mul (hc.gcd_both n n),
        ratio_gcd_product S (fun p h => (hp p h).1) n hn]
    change t ≤ ratio (a.val.gcd Q) at halo
    change ratio (a.val.gcd Q) ≤ t+l at hahi
    change t ≤ ratio (b.val.gcd Q) at hblo
    change ratio (b.val.gcd Q) ≤ t+l at hbhi
    have habs : |ratio (a.val.gcd Q) - ratio (b.val.gcd Q)| ≤ l := by
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    have hge := ratio_ge_one (Nat.gcd_pos_of_pos_right a.val hR)
    rw [hmul _ ha, hmul _ hb, ← hgR, ← mul_sub, abs_mul, abs_of_pos (by linarith)] at habs
    have hclose :
        |primeRatio S (S.filter (fun p => p ∣ a.val)) -
          primeRatio S (S.filter (fun p => p ∣ b.val))| ≤ l :=
      (le_mul_of_one_le_left (abs_nonneg _) hge).trans habs
    have heq : ∀ p ∈ S, p ∣ a.val ↔ p ∣ b.val := by
      intro p hpS
      by_contra hne
      have hsep := primeRatio_sep S (S.filter (fun p => p ∣ a.val))
        (S.filter (fun p => p ∣ b.val)) hp ⟨p,hpS,by simpa [hpS] using hne⟩
      exact (not_le_of_gt hl) (hsep.trans hclose)
    have hmod (p : ℕ) (hpS : p ∈ S) : a.val ≡ b.val [MOD p^2] := by
      have hdp : p ∣ p^2 := dvd_pow_self p (by decide)
      have hstatus : p ∣ a.val % (p^2) ↔ p ∣ b.val % (p^2) := by
        simp only [Nat.dvd_iff_mod_eq_zero, Nat.mod_mod_of_dvd _ hdp] at heq ⊢
        exact heq p hpS
      exact congrArg Fin.val (residueCode_inj (hp p hpS).1 hstatus
        (congrArg (fun x => x.2.2 ⟨p,hpS⟩) hab))
    have hmodQ : a.val % Q = b.val % Q := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp
      ⟨hmodR, congruent_square_product S (fun p hpS => (hp p hpS).1) hmod⟩
    apply Subtype.ext
    calc
      a.val = a.val % Q + Q * (a.val/Q) := (Nat.mod_add_div ..).symm
      _ = b.val := by rw [hdiv,hmodQ,Nat.mod_add_div]
  have hcard := Fintype.card_le_of_injective _ hf
  simp only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin,Fintype.card_pi] at hcard
  rw [show (∏ p : S,p.val*(p.val-1)) = ∏ p ∈ S,p*(p-1) from
    Finset.prod_coe_sort (s := S) (f := fun p : ℕ => p*(p-1))] at hcard
  simpa [Nat.mul_assoc] using hcard

private theorem partial_le_gcd_ratio (S : Finset ℕ) (B n : ℕ) (hn : 0 < n)
    (hS : ∀ p ∈ S, ¬ p^2 ∣ n) :
    let T := ((range (B+1)).filter Nat.Prime) \ S
    let R := ∏ p ∈ T,p^B
    (∑ d ∈ n.divisors.filter (· ≤ B), (1:ℝ)/d) ≤ ratio (n.gcd (R * ∏ p ∈ S,p^2)) := by
  classical
  let T := ((range (B+1)).filter Nat.Prime) \ S
  let R := ∏ p ∈ T,p^B
  let P := ∏ p ∈ S,p^2
  let Q := R * P
  have hg : 0 < n.gcd Q := Nat.gcd_pos_of_pos_left _ hn
  change _ ≤ ratio (n.gcd Q)
  rw [ratio_divisors hg]
  refine sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => by positivity)
  intro d hd
  have hdv := Nat.dvd_of_mem_divisors (mem_filter.mp hd).1
  have hd0 := Nat.pos_of_mem_divisors (mem_filter.mp hd).1
  have hdB := (mem_filter.mp hd).2
  have dvdQ : d ∣ Q := by
    let U := S ∪ T
    let e : ℕ → ℕ := fun p => if p ∈ S then 2 else B
    have hUT : Disjoint S T := disjoint_sdiff_self_right
    have hUprod : ∏ p ∈ U,p^e p = Q := by
      simp only [U]
      rw [prod_union hUT]
      have hps : ∏ p ∈ S,p^e p = P := prod_congr rfl (fun p hp => by simp [e,hp])
      have hpt : ∏ p ∈ T,p^e p = R :=
        prod_congr rfl (fun p hp => by
          have hn := (mem_sdiff.mp hp).2
          simp [e,hn])
      rw [hps,hpt]
      exact mul_comm _ _
    have hsub : d.primeFactors ⊆ U := by
      intro p hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      by_cases hs : p ∈ S
      · exact mem_union_left _ hs
      · exact mem_union_right _ (mem_sdiff.mpr
          ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_dvd hd0 hpd).trans hdB)),hprime⟩,hs⟩)
    rw [← hUprod, ← Nat.prod_factorization_pow_eq_self hd0.ne']
    change (∏ p ∈ d.primeFactors,p^d.factorization p) ∣ _
    refine (prod_dvd_prod_of_dvd _ _ ?_).trans (prod_dvd_prod_of_subset _ _ _ hsub)
    intro p hp
    have hprim := Nat.prime_of_mem_primeFactors hp
    apply pow_dvd_pow
    by_cases hs : p ∈ S
    · have hfact : ¬ 2 ≤ d.factorization p := fun hh =>
        hS p hs (((hprim.pow_dvd_iff_le_factorization hd0.ne').mpr hh).trans hdv)
      simpa [e,hs] using (show d.factorization p ≤ 2 by omega)
    · simp only [e,if_neg hs]
      exact Nat.factorization_le_of_le_pow (hdB.trans (Nat.lt_pow_self hprim.one_lt).le)
  exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hdv dvdQ,hg.ne'⟩

private theorem gcd_ratio_le_full (n Q : ℕ) (hn : 0 < n) : ratio (n.gcd Q) ≤ ratio n := by
  have hg : 0 < n.gcd Q := Nat.gcd_pos_of_pos_left _ hn
  rw [ratio_divisors hg, ratio_divisors hn]
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
  intro d hd
  exact Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors hd).trans (Nat.gcd_dvd_left _ _), hn.ne'⟩

private theorem prime_sum_above (K : ℕ) (L : ℝ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ K < p) ∧ L < ∑ p ∈ S, (1:ℝ)/p := by
  classical
  let f : ℕ → ℝ := fun n => if n.Prime then (1:ℝ)/n else 0
  have hf : ¬ Summable f := by
    intro h
    apply not_summable_one_div_on_primes
    apply h.congr
    intro n
    by_cases hn : n.Prime <;> simp [f,hn]
  have hf0 : 0 ≤ f := fun k => by unfold f; split <;> positivity
  let U := range (K+1)
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, L + (∑ p ∈ U, f p) < ∑ p ∈ T, f p := by
    by_contra! h
    exact hf (summable_of_sum_le hf0 h)
  let S := (T \ U).filter Nat.Prime
  refine ⟨S, ?_, ?_⟩
  · intro p hp
    have h := mem_filter.mp hp
    exact ⟨h.2, by have := (mem_sdiff.mp h.1).2; simpa [U,not_lt] using this⟩
  · have hsplit := sum_inter_add_sum_sdiff T U f
    have hsmall : (∑ p ∈ T ∩ U, f p) ≤ ∑ p ∈ U, f p :=
      sum_le_sum_of_subset_of_nonneg inter_subset_right (fun p _ _ => hf0 p)
    have hl : L < ∑ p ∈ T \ U, f p := by linarith
    simpa only [S,sum_filter,f] using hl

private noncomputable def squareBad (S : Finset ℕ) (N : ℕ) : Finset ℕ := open Classical in
  (Icc 1 N).filter fun n => ∃ p ∈ S,p^2 ∣ n

private theorem squareBad_bound (S : Finset ℕ) (K N : ℕ) (hK : K ≠ 0)
    (hS : ∀ p ∈ S, K < p) :
    ((squareBad S N).card : ℝ) ≤ (N : ℝ) * (K : ℝ)⁻¹ := by
  classical
  have hU : squareBad S N = S.biUnion (fun p => (Ioc 0 N).filter (fun n => p^2 ∣ n)) := by
    ext n
    simp [squareBad, Nat.succ_le_iff, and_left_comm, and_assoc]
    aesop
  rw [hU]
  calc
    _ ≤ ∑ p ∈ S, (((Ioc 0 N).filter (fun n => p^2 ∣ n)).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    _ = ∑ p ∈ S, ((N/(p^2) : ℕ) : ℝ) := by simp [Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ ∑ p ∈ S, (N : ℝ) * ((p : ℝ)^2)⁻¹ := by
      apply sum_le_sum
      intro p hp
      have hp0 : 0 < p := (Nat.zero_le K).trans_lt (hS p hp)
      have hpR : (0:ℝ)<p := by exact_mod_cast hp0
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hpR 2), ← Nat.cast_pow]
      exact_mod_cast Nat.div_mul_le_self N (p^2)
    _ ≤ (N : ℝ) * (K : ℝ)⁻¹ := by
      rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      let M := max K (S.sup id)
      have hsub : S ⊆ Ioc K M := fun p hp => mem_Ioc.mpr
        ⟨hS p hp, (show p ≤ S.sup id from Finset.le_sup (f := id) hp).trans (le_max_right ..)⟩
      exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
        ((sum_Ioc_inv_sq_le_sub hK (le_max_left K (S.sup id))).trans
          (sub_le_self _ (show 0 ≤ (M : ℝ)⁻¹ by positivity)))

private theorem intervalGood_bound (S : Finset ℕ) (hp : ∀ p ∈ S, p.Prime ∧ 2 < p)
    (R : ℕ) (hR : 0 < R) (hc : R.Coprime (∏ p ∈ S,p^2)) (t l : ℝ)
    (hl : l < ((∏ p ∈ S,p : ℕ) : ℝ)⁻¹) (N : ℕ) (hN : R * ∏ p ∈ S,p^2 ≤ N) :
    ((intervalGood S R t l N).card : ℝ) ≤
      2*(N : ℝ)*Real.exp (-(∑ p ∈ S,(1:ℝ)/p)) := by
  let Q := R * ∏ p ∈ S,p^2
  let A := R * ∏ p ∈ S,p*(p-1)
  have hQ : 0 < Q := Nat.mul_pos hR (Finset.prod_pos (fun p h => pow_pos (hp p h).1.pos _))
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have ha : (A : ℝ) / Q ≤ Real.exp (-(∑ p ∈ S,(1:ℝ)/p)) := by
    calc
      (A : ℝ) / Q = ∏ p ∈ S, (1 - (1:ℝ)/p) := by
        have hRR : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
        simp only [A,Q,Nat.cast_mul,Nat.cast_prod,Nat.cast_pow,mul_div_mul_left _ _ hRR,
          ← prod_div_distrib]
        apply prod_congr rfl
        intro p h
        have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (hp p h).1.ne_zero
        rw [Nat.cast_sub (hp p h).1.one_lt.le, Nat.cast_one]
        field_simp
      _ ≤ ∏ p ∈ S, Real.exp (-((1:ℝ)/p)) := by
        apply Finset.prod_le_prod
        · intro p h
          have h1 : (1 : ℝ) ≤ p := by exact_mod_cast (hp p h).1.one_lt.le
          have h0 : (0 : ℝ) < p := by linarith
          rw [sub_nonneg, div_le_iff₀ h0, one_mul]
          exact h1
        · intro p h
          simpa [sub_eq_add_neg,add_comm] using Real.add_one_le_exp (-((1:ℝ)/p))
      _ = _ := by rw [← Real.exp_sum, sum_neg_distrib]
  have hd : ((N/Q : ℕ) : ℝ) ≤ (N : ℝ)/Q := by
    rw [le_div_iff₀ hQR]
    exact_mod_cast Nat.div_mul_le_self N Q
  have hQN : (Q : ℝ) ≤ N := by exact_mod_cast hN
  calc
    _ ≤ (((N/Q : ℕ) : ℝ)+1)*(A : ℝ) := by
      rw [← Nat.cast_one,← Nat.cast_add,← Nat.cast_mul]
      exact_mod_cast (show (intervalGood S R t l N).card ≤ (N/Q+1)*A by
        simpa only [Q,A,Nat.mul_assoc] using card_intervalGood S hp R hR hc t l hl N)
    _ ≤ ((N : ℝ)/Q+1)*(A : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = ((N : ℝ)+(Q : ℝ))*((A : ℝ)/Q) := by field_simp
    _ ≤ ((N : ℝ)+(Q : ℝ))*Real.exp (-(∑ p ∈ S,(1:ℝ)/p)) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

set_option maxHeartbeats 500000 in
theorem ratio_antiConcentration
    (tailBound : ∀ η ε : ℝ, 0<η → 0<ε → ∃ B : ℕ, ∀ᶠ N : ℕ in atTop,
      (((Icc 1 N).filter (fun n => η ≤ ratio n - (∑ d ∈ n.divisors.filter (· ≤ B), (1:ℝ)/d))).card:ℝ)
        ≤ ε*N) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ N : ℕ in atTop,
      (((Icc 1 N).filter (fun n => 2 < ratio n ∧ ratio n ≤ 2+η)).card:ℝ) ≤ ε*N := by
  classical
  obtain ⟨K,hK⟩ := exists_nat_gt (max 2 (1 / (ε/3)))
  have hK2 : 2 ≤ K := by exact_mod_cast ((le_max_left _ _).trans_lt hK).le
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hiK : (K : ℝ)⁻¹ ≤ ε/3 := by
    rw [← one_div, div_le_iff₀ hKR]
    exact ((div_lt_iff₀ (by positivity : 0 < ε/3)).mp
      ((le_max_right _ _).trans_lt hK)).le.trans (by rw [mul_comm])
  obtain ⟨S,hS,hsum⟩ := prime_sum_above K (-Real.log (ε/6))
  have hp : ∀ p ∈ S,p.Prime ∧ 2 < p := fun p h => ⟨(hS p h).1,hK2.trans_lt (hS p h).2⟩
  let P := ∏ p ∈ S,p
  have hP : 0 < P := Finset.prod_pos (fun p h => (hp p h).1.pos)
  have hiP : 0 < (P : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hP)
  let η : ℝ := (P : ℝ)⁻¹/4
  have hη : 0 < η := div_pos hiP (by norm_num)
  have hwidth : 2*η < (P : ℝ)⁻¹ := by simp only [η]; linarith
  obtain ⟨B,hB⟩ := tailBound η (ε/3) hη (by positivity)
  let T := ((range (B+1)).filter Nat.Prime) \ S
  let R := ∏ p ∈ T,p^B
  let Q := R * ∏ p ∈ S,p^2
  have hR : 0 < R := Finset.prod_pos fun p h => pow_pos
    (mem_filter.mp (Finset.mem_sdiff.mp h).1).2.pos _
  have hc : R.Coprime (∏ p ∈ S,p^2) := by
    apply Nat.Coprime.prod_left
    intro p hpT
    exact coprime_power_product S (fun q h => (hp q h).1)
      (mem_filter.mp (Finset.mem_sdiff.mp hpT).1).2 (Finset.mem_sdiff.mp hpT).2 (fun _ => 2) B
  refine ⟨η,hη,?_⟩
  filter_upwards [hB,eventually_ge_atTop Q] with N htail hN
  let near := (Icc 1 N).filter (fun n => 2 < ratio n ∧ ratio n ≤ 2+η)
  let largeTail := (Icc 1 N).filter (fun n =>
    η ≤ ratio n - (∑ d ∈ n.divisors.filter (· ≤ B), (1:ℝ)/d))
  let good := intervalGood S R (2-η) (2*η) N
  have hsub : near ⊆ (squareBad S N ∪ largeTail) ∪ good := by
    intro n hn
    obtain ⟨hnN,hnlo,hnhi⟩ := mem_filter.mp hn
    by_cases hs : n ∈ squareBad S N
    · exact mem_union_left _ (mem_union_left _ hs)
    by_cases ht : n ∈ largeTail
    · exact mem_union_left _ (mem_union_right _ ht)
    have hnp : 0 < n := (mem_Icc.mp hnN).1
    have hsn : ∀ p ∈ S, ¬ p^2 ∣ n := by
      intro p hp hd
      exact hs (mem_filter.mpr ⟨hnN,p,hp,hd⟩)
    have htn : ratio n - (∑ d ∈ n.divisors.filter (· ≤ B), (1:ℝ)/d) < η := by
      exact lt_of_not_ge fun h => ht (mem_filter.mpr ⟨hnN,h⟩)
    have h := partial_le_gcd_ratio S B n hnp hsn
    have h' : ratio (n.gcd Q) ≤ ratio n := gcd_ratio_le_full n Q hnp
    apply mem_union_right _
    refine mem_filter.mpr ⟨hnN,hsn,?_,?_⟩
    · change 2-η ≤ ratio (n.gcd Q)
      change (∑ d ∈ n.divisors.filter (· ≤ B), (1:ℝ)/d) ≤ ratio (n.gcd Q) at h
      linarith
    · change ratio (n.gcd Q) ≤ (2-η)+2*η
      linarith
  have hb := squareBad_bound S K N (by omega) (fun p h => (hS p h).2)
  have hgood := intervalGood_bound S hp R hR hc (2-η) (2*η) hwidth N hN
  have hsmall : Real.exp (-(∑ p ∈ S,(1:ℝ)/p)) ≤ ε/6 := by
    rw [← Real.exp_log (by positivity : 0 < ε/6), Real.exp_le_exp]
    linarith
  change (near.card : ℝ) ≤ ε*N
  calc
    _ ≤ (squareBad S N).card + (largeTail.card : ℝ) + (good.card : ℝ) := by
      exact_mod_cast ((card_le_card hsub).trans
        (card_union_le _ _ |>.trans (Nat.add_le_add_right (card_union_le _ _) _)))
    _ ≤ (N : ℝ)*(K : ℝ)⁻¹ + ε/3*N + 2*N*Real.exp (-(∑ p ∈ S,(1:ℝ)/p)) := by
      exact add_le_add (add_le_add hb htail) hgood
    _ ≤ ε*N := by
      have h₁ := mul_le_mul_of_nonneg_left hiK (by positivity : (0:ℝ) ≤ N)
      have h₂ := mul_le_mul_of_nonneg_left hsmall (by positivity : (0:ℝ) ≤ 2*N)
      linarith

end E830

theorem h3_proof : R1.H3 := E830.ratio_antiConcentration h2_proof

end H3Section

end OMA.Erdos830Solution

theorem OMA.solution : type_of% @Erdos830.erdos_830.variants.erdos :=
  OMA.Erdos830Solution.R1.main
    OMA.Erdos830Solution.h1_proof
    OMA.Erdos830Solution.h2_proof
    OMA.Erdos830Solution.h3_proof
