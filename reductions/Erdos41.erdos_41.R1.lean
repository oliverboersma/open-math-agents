import FormalConjectures.ErdosProblems.«41»

-- Credit: @ysanatomic

/-!
# Erdős 41 with irregular consecutive gaps

The first step is the smooth-gap case reported in Erdős Problem a Day, day 41.
The remaining step concerns cubic growth and the simultaneous occurrence of
large individual gaps and unbounded normalized gap moments of every real
order greater than one. At order one the sum of gaps is f(n) - f(0).

Martin Helm studied the distribution of infinite B₃ sequences in
*On the Distribution of B₃-Sequences*, Journal of Number Theory 58 (1996).
See https://doi.org/10.1006/jnth.1996.0069 and
https://www.erdosproblemaday.com/day/41-b3-density.
-/

open Set Filter

namespace OMA.R_Erdos41_erdos_41_R1

def H1 : Prop :=
  ∀ (f : ℕ → ℕ), StrictMono f → Erdos41.NtupleCondition (Set.range f) 3 →
    ((fun i : ℕ => ((f (i+1)-f i : ℕ) : ℝ)) =o[atTop]
      (fun i : ℕ => (i : ℝ)^2 * Real.log (i+2))) →
    atTop.liminf (fun n : ℕ =>
      ((Set.range f ∩ Icc 1 n).ncard : ℝ) / (n : ℝ)^(1/3 : ℝ)) = 0

def H2 : Prop :=
  ∀ (f : ℕ → ℕ), StrictMono f → (∃ K : ℕ, ∀ᶠ n in atTop, f n ≤ K * (n + 1)^3) →
    (¬ (fun i : ℕ => ((f (i+1)-f i : ℕ) : ℝ)) =o[atTop]
      (fun i : ℕ => (i : ℝ)^2 * Real.log (i+2))) →
    (∀ p : ℝ, 1 < p → ∀ C : ℝ, ∃ᶠ n : ℕ in atTop,
      C < (∑ i ∈ Finset.range n, ((f (i+1)-f i : ℕ) : ℝ)^p) /
        ((n : ℝ)+1)^(2*p+1)) →
    ¬ Erdos41.NtupleCondition (Set.range f) 3

lemma cubic_count (A : Set ℕ) (h : Erdos41.NtupleCondition A 3) (N : ℕ) :
    (A ∩ Set.Icc 1 N).ncard ^ 3 ≤ 6 * (3 * N + 1) := by
  classical
  let S := (Finset.Icc 1 N).filter (· ∈ A)
  let push (t : Sym S 3) : Sym ℕ 3 := t.map Subtype.val
  have hmem (t : Sym S 3) (a : ℕ) (ha : a ∈ push t) : a ∈ S := by
    obtain ⟨b, _, rfl⟩ := Sym.mem_map.mp ha
    exact b.property
  let f (t : Sym S 3) : Fin (3 * N + 1) :=
    ⟨(push t).val.sum, by
      have hb := Multiset.sum_le_card_nsmul (push t).val N (fun a ha =>
        (Finset.mem_Icc.mp (Finset.mem_filter.mp (hmem t a ha)).1).2)
      simpa [(push t).property, smul_eq_mul] using Nat.lt_succ_of_le hb⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Sym.map_injective Subtype.val_injective 3
    apply Subtype.ext
    exact h _ _ (fun a ha => (Finset.mem_filter.mp (hmem x a ha)).2)
      (fun a ha => (Finset.mem_filter.mp (hmem y a ha)).2)
      (push x).property (push y).property (congrArg Fin.val hxy)
  have hcount := Fintype.card_le_of_injective f hinj
  rw [Sym.card_sym_eq_choose, Fintype.card_coe, Fintype.card_fin] at hcount
  have hf := Nat.descFactorial_eq_factorial_mul_choose (S.card + 2) 3
  norm_num [Nat.descFactorial_succ] at hf
  have hncard : (A ∩ Set.Icc 1 N).ncard = S.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [S]
    tauto
  rw [hncard]
  change (S.card + 2).choose 3 ≤ 3 * N + 1 at hcount
  nlinarith

lemma ratio_eventually_le_three (A : Set ℕ) (h : Erdos41.NtupleCondition A 3) :
    ∀ᶠ N : ℕ in atTop, ((A ∩ Icc 1 N).ncard : ℝ) / (N : ℝ)^(1/3 : ℝ) ≤ 3 := by
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hb : ((A ∩ Set.Icc 1 N).ncard : ℝ)^3 ≤ 6 * (3 * (N : ℝ) + 1) := by
    exact_mod_cast cubic_count A h N
  have hN' : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos : 0 < (N : ℝ) := by linarith
  have hcube : ((N : ℝ)^(1/3 : ℝ))^3 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hpos _)).2
  apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (by positivity)
  rw [mul_pow, hcube]
  nlinarith

lemma upper_ratio (A : Set ℕ) (h : Erdos41.NtupleCondition A 3) :
    Filter.atTop.IsCoboundedUnder (· ≥ ·) (fun N : ℕ =>
      ((A ∩ Set.Icc 1 N).ncard : ℝ) / (N : ℝ)^(1/3 : ℝ)) := by
  exact Filter.isCoboundedUnder_ge_of_eventually_le Filter.atTop (ratio_eventually_le_three A h)

lemma eventual_cubic_of_pos (A : Set ℕ)
    (hpos : 0 < Filter.atTop.liminf (fun N : ℕ =>
      ((A ∩ Icc 1 N).ncard : ℝ) / (N : ℝ) ^ (1/3 : ℝ))) :
    ∃ K N₀ : ℕ, 0 < K ∧ ∀ N : ℕ, N₀ ≤ N → N ≤ K * (A ∩ Icc 1 N).ncard ^ 3 := by
  let r := fun N : ℕ => ((A ∩ Icc 1 N).ncard : ℝ) / (N : ℝ) ^ (1/3 : ℝ)
  obtain ⟨c, hc, hcr⟩ := exists_between hpos
  have hb : atTop.IsBoundedUnder (· ≥ ·) r := by
    refine ⟨0, eventually_map.mpr <| Eventually.of_forall fun n => ?_⟩
    exact div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (eventually_lt_of_lt_liminf hcr hb)
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / c)
  have hkpos : 0 < (k : ℝ) := lt_trans (by positivity) hk
  have hkNat : 0 < k := by exact_mod_cast hkpos
  refine ⟨k ^ 3, max 1 N₀, by positivity, ?_⟩
  intro N hN
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left ..) hN)
  have hroot : 0 < (N : ℝ) ^ (1/3 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hNpos) _
  have hcount := (lt_div_iff₀ hroot).1 (hN₀ N (le_trans (le_max_right ..) hN))
  have hkc : 1 < (k : ℝ) * c := (div_lt_iff₀ hc).1 hk
  have hscale : (N : ℝ) ^ (1/3 : ℝ) ≤ (k : ℝ) * (A ∩ Icc 1 N).ncard := by
    calc
      _ ≤ ((k : ℝ) * c) * ((N : ℝ) ^ (1/3 : ℝ)) := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hkc.le) hroot.le]
      _ = _ := mul_assoc ..
      _ ≤ _ := mul_le_mul_of_nonneg_left hcount.le hkpos.le
  have hcube := pow_le_pow_left₀ hroot.le hscale 3
  rw [← Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ N)] at hcube
  norm_num at hcube
  rw [mul_pow] at hcube
  exact_mod_cast hcube

lemma reduced_signed_eq {A : Set ℕ} (h : Erdos41.NtupleCondition A 3)
    {a b c d e f : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hd : d ∈ A) (he : e ∈ A) (hf : f ∈ A)
    (hab : a ≤ b) (hde : d ≤ e) (hca : c ≠ a) (hcb : c ≠ b)
    (hs : (a : ℤ) + b - c = d + e - f) :
    a = d ∧ b = e ∧ c = f := by
  have hm : (a ::ₘ b ::ₘ {f} : Multiset ℕ) = d ::ₘ e ::ₘ {c} := by
    apply h
    · intro z hz
      simp only [Multiset.mem_cons, Multiset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> assumption
    · intro z hz
      simp only [Multiset.mem_cons, Multiset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> assumption
    · simp
    · simp
    · simp
      omega
  have hc' : c ∈ (a ::ₘ b ::ₘ {f} : Multiset ℕ) := by rw [hm]; simp
  simp only [Multiset.mem_cons, Multiset.mem_singleton] at hc'
  obtain rfl : c = f := hc'.resolve_left hca |>.resolve_left hcb
  have hp : (a ::ₘ {b} : Multiset ℕ) = d ::ₘ {e} := by
    apply (Multiset.cons_inj_right c).mp
    have cb : c ::ₘ {b} = b ::ₘ {c} := Multiset.pair_comm _ _
    have ce : c ::ₘ {e} = e ::ₘ {c} := Multiset.pair_comm _ _
    rw [Multiset.cons_swap c a, cb, Multiset.cons_swap c d, ce]
    exact hm
  have ha' : a ∈ (d ::ₘ {e} : Multiset ℕ) := by rw [← hp]; simp
  have hd' : d ∈ (a ::ₘ {b} : Multiset ℕ) := by rw [hp]; simp
  simp only [Multiset.mem_cons, Multiset.mem_singleton] at ha' hd'
  omega

lemma signed_capacity {A : Set ℕ} (h : Erdos41.NtupleCondition A 3)
    (H : ℕ) (T : Finset (ℕ × ℕ × ℕ))
    (hT : ∀ t ∈ T, t.1 ∈ A ∧ t.2.1 ∈ A ∧ t.2.2 ∈ A ∧ t.1 ≤ t.2.1 ∧
      t.2.2 ≠ t.1 ∧ t.2.2 ≠ t.2.1)
    (hr : ∀ t ∈ T, (t.1 : ℤ) + t.2.1 - t.2.2 ∈ Set.Icc (-(2 * (H : ℤ))) (2 * H)) :
    T.card ≤ 4 * H + 1 := by
  let s (t : ℕ × ℕ × ℕ) := (t.1 : ℤ) + t.2.1 - t.2.2
  have hinj : Set.InjOn s (T : Set (ℕ × ℕ × ℕ)) := by
    rintro ⟨a,b,c⟩ hp ⟨d,e,f⟩ hq heq
    obtain ⟨ha,hb,hc,hab,hca,hcb⟩ := hT _ hp
    obtain ⟨hd,he,hf,hde,_,_⟩ := hT _ hq
    obtain ⟨rfl,rfl,rfl⟩ := reduced_signed_eq h ha hb hc hd he hf hab hde hca hcb heq
    rfl
  have hmaps : Set.MapsTo s (T : Set _) (Finset.Icc (-(2 * (H : ℤ))) (2 * H) : Set ℤ) := by
    intro t ht
    exact Finset.mem_Icc.mpr (hr t ht)
  have hc := Finset.card_le_card_of_injOn s hmaps hinj
  rw [Int.card_Icc] at hc
  omega

lemma box_capacity {A : Set ℕ} (h : Erdos41.NtupleCondition A 3) (H : ℕ)
    {ι : Type*} [DecidableEq ι] (P : Finset ι) (u v : ι → ℕ)
    (hidx : Set.InjOn (fun i => (u i, v i)) ↑P) (huv : ∀ i ∈ P, 0 < u i ∧ u i < v i) :
    ∑ i ∈ P, (A ∩ Set.Ioc (u i * H) ((u i + 1) * H)).ncard *
      (A ∩ Set.Ioc (v i * H) ((v i + 1) * H)).ncard *
      (A ∩ Set.Ioc ((u i + v i) * H) ((u i + v i + 1) * H)).ncard ≤ 4 * H + 1 := by
  classical
  let B (m : ℕ) := (Finset.Ioc (m * H) ((m+1)*H)).filter (· ∈ A)
  let box (i : ι) := B (u i) ×ˢ B (v i) ×ˢ B (u i + v i)
  have hmem {x m : ℕ} (hx : x ∈ B m) : x ∈ A ∧ m*H < x ∧ x ≤ (m+1)*H :=
    ⟨(Finset.mem_filter.mp hx).2, Finset.mem_Ioc.mp (Finset.mem_filter.mp hx).1⟩
  have hlt {x y m n : ℕ} (hx : x ∈ B m) (hy : y ∈ B n) (hmn : m < n) : x < y := by
    exact lt_of_le_of_lt ((hmem hx).2.2.trans (Nat.mul_le_mul_right H hmn)) (hmem hy).2.1
  have huniq {x m n : ℕ} (hx : x ∈ B m) (hy : x ∈ B n) : m = n := by
    rcases lt_trichotomy m n with hlt' | heq | hgt'
    · exact False.elim ((lt_irrefl x) (hlt hx hy hlt'))
    · exact heq
    · exact False.elim ((lt_irrefl x) (hlt hy hx hgt'))
  have hdisj : (↑P : Set ι).PairwiseDisjoint box := by
    apply Finset.pairwiseDisjoint_iff.mpr
    rintro i hi j hj ⟨t, ht⟩
    obtain ⟨h1,h2⟩ := Finset.mem_inter.mp ht
    simp only [box, Finset.mem_product] at h1 h2
    exact hidx hi hj (Prod.ext (huniq h1.1 h2.1) (huniq h1.2.1 h2.2.1))
  have hc := signed_capacity h H (P.biUnion box) (by
    intro t ht
    obtain ⟨i,hi,hti⟩ := Finset.mem_biUnion.mp ht
    simp only [box, Finset.mem_product] at hti
    obtain ⟨ha,hb,hc⟩ := hti
    obtain ⟨hu, huv'⟩ := huv i hi
    exact ⟨(hmem ha).1, (hmem hb).1, (hmem hc).1, (hlt ha hb huv').le,
      (hlt ha hc (by omega)).ne', (hlt hb hc (by omega)).ne'⟩) (by
    intro t ht
    obtain ⟨i,hi,hti⟩ := Finset.mem_biUnion.mp ht
    simp only [box, Finset.mem_product] at hti
    obtain ⟨ha,hb,hc⟩ := hti
    have h1 := (hmem ha).2
    have h2 := (hmem hb).2
    have h3 := (hmem hc).2
    simp only [add_mul, one_mul] at h1 h2 h3
    constructor <;> omega)
  rw [Finset.card_biUnion hdisj] at hc
  have hn (m : ℕ) : (A ∩ Set.Ioc (m * H) ((m + 1) * H)).ncard = (B m).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [B]
    tauto
  simpa only [hn, box, Finset.card_product, mul_assoc] using hc

lemma pow_eight (n : ℕ) : (2^n)^3 = (8:ℕ)^n := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num

lemma inverse_growth {f : ℕ → ℕ} (hf : StrictMono f)
    (hB : Erdos41.NtupleCondition (Set.range f) 3) (i : ℕ) :
    i^3 ≤ 24 * (f i + 1) := by
  have hsub : f '' Set.Icc 1 i ⊆ Set.range f ∩ Set.Icc 1 (f i) := by
    rintro _ ⟨j, ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨j,rfl⟩, ?_, hf.monotone h2⟩
    have := hf (show 0 < j by omega)
    omega
  have hcard := Set.ncard_le_ncard hsub ((finite_Icc ..).subset inter_subset_right)
  rw [Set.ncard_image_of_injective _ hf.injective] at hcard
  simp at hcard
  have hp := Nat.pow_le_pow_left hcard 3
  have hb := cubic_count _ hB (f i)
  omega

lemma majority_fiber (R : ℕ) (B : Finset ℕ) (hB : 6 * B.card ≤ R) :
    R^2 ≤ 2 * (Finset.univ.filter (fun p : Fin R × Fin R =>
      R+p.1.val ∉ B ∧ 2*R+p.2.val ∉ B ∧ R+p.1.val+(2*R+p.2.val) ∉ B)).card := by
  classical
  let u (p : Fin R × Fin R) := R + p.1.val
  let v (p : Fin R × Fin R) := 2*R + p.2.val
  let G := Finset.univ.filter (fun p => u p ∉ B ∧ v p ∉ B ∧ u p+v p ∉ B)
  let bad (f : Fin R × Fin R → ℕ) := Finset.univ.filter (fun p => f p ∈ B)
  have hcount (f : Fin R × Fin R → ℕ) (e : Fin R × Fin R → Fin R)
      (hi : Function.Injective fun p => (f p,e p)) : (bad f).card ≤ B.card * R := by
    have hmap : Set.MapsTo (fun p => (f p, e p)) (bad f : Set _) (↑(B ×ˢ (Finset.univ : Finset (Fin R)) : Finset (ℕ × Fin R)) : Set _) := by
      intro p hp
      exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hp).2, Finset.mem_univ _⟩
    simpa using Finset.card_le_card_of_injOn _ hmap hi.injOn
  have h1 := hcount u Prod.snd (by
    rintro ⟨x,y⟩ ⟨z,w⟩ h
    simp only [u, Prod.mk.injEq, Nat.add_left_cancel_iff] at h
    exact Prod.ext (Fin.ext h.1) h.2)
  have h2 := hcount v Prod.fst (by
    rintro ⟨x,y⟩ ⟨z,w⟩ h
    simp only [v, Prod.mk.injEq, Nat.add_left_cancel_iff] at h
    exact Prod.ext h.2 (Fin.ext h.1))
  have h3 := hcount (fun p => u p+v p) Prod.fst (by
    rintro ⟨x,y⟩ ⟨z,w⟩ h
    simp only [u, v, Prod.mk.injEq] at h
    obtain ⟨h, rfl⟩ := h
    have hy : y = w := Fin.ext (by omega)
    subst w
    rfl)
  have hcov : Finset.univ ⊆ G ∪ (bad u ∪ (bad v ∪ bad (fun p => u p+v p))) := by
    intro p _
    by_cases hu : u p ∈ B <;> by_cases hv : v p ∈ B <;> by_cases hw : u p + v p ∈ B <;>
      simp [G, bad, hu, hv, hw]
  have htot := Finset.card_le_card hcov
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at htot
  have hc1 := Finset.card_union_le G (bad u ∪ (bad v ∪ bad (fun p => u p+v p)))
  have hc2 := Finset.card_union_le (bad u) (bad v ∪ bad (fun p => u p+v p))
  have hc3 := Finset.card_union_le (bad v) (bad (fun p => u p+v p))
  change R^2 ≤ 2 * G.card
  have hh := Nat.mul_le_mul_right R hB
  nlinarith only [h1,h2,h3,hc1,hc2,hc3,htot,hh]

lemma majority_obstruction {A : Set ℕ} (hB : Erdos41.NtupleCondition A 3)
    (K J t : ℕ) (ht : 0 < t) (hJ : 10 * K ^ 3 < J)
    (bad : ℕ → Finset ℕ) (hbad : ∀ j < J, 6*(bad j).card ≤ 8^j)
    (hbox : ∀ j < J, ∀ m : ℕ, 8 ^ j ≤ m → m < 6 * 8 ^ j → m ∉ bad j →
      t ≤ K * (2 ^ j) ^ 2 * (A ∩ Set.Ioc (m * t ^ 3) ((m + 1) * t ^ 3)).ncard) :
    False := by
  classical
  let D (j : Fin J) := Fin (8 ^ j.val) × Fin (8 ^ j.val)
  let u (i : (j : Fin J) × D j) := 8 ^ i.1.val + (i.2.1 : ℕ)
  let v (i : (j : Fin J) × D j) := 2 * 8 ^ i.1.val + (i.2.2 : ℕ)
  let cnt (m : ℕ) := (A ∩ Set.Ioc (m * t ^ 3) ((m + 1) * t ^ 3)).ncard
  let w (i : (j : Fin J) × D j) := cnt (u i) * cnt (v i) * cnt (u i + v i)
  have hsep (a b : ℕ) (hab : a < b) : 8 ^ a * 8 ≤ 8 ^ b := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right (by decide) hab
  have hinj : Function.Injective (fun i => (u i, v i)) := by
    rintro ⟨a,x,y⟩ ⟨b,z,q⟩ h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    change 8 ^ a.val + x.val = 8 ^ b.val + z.val at h1
    change 2 * 8 ^ a.val + y.val = 2 * 8 ^ b.val + q.val at h2
    have hab : a = b := by
      apply Fin.ext
      rcases lt_trichotomy a.val b.val with hlt | heq | hgt
      · have := hsep _ _ hlt
        have := x.isLt
        omega
      · exact heq
      · have := hsep _ _ hgt
        have := z.isLt
        omega
    subst b
    have hx : x = z := Fin.ext (Nat.add_left_cancel h1)
    have hy : y = q := Fin.ext (Nat.add_left_cancel h2)
    subst z
    subst q
    rfl
  have hcap : ∑ i, w i ≤ 4 * t ^ 3 + 1 := by
    apply box_capacity hB (t ^ 3) Finset.univ u v hinj.injOn
    rintro ⟨j,x,y⟩ _
    change 0 < 8 ^ j.val + x.val ∧ 8 ^ j.val + x.val < 2 * 8 ^ j.val + y.val
    have := x.isLt
    have : 0 < 8 ^ j.val := by positivity
    omega
  have hper (j : Fin J) : t ^ 3 ≤ (2 * K ^ 3) * ∑ e : D j, w ⟨j,e⟩ := by
    let G := Finset.univ.filter (fun e : D j => u ⟨j,e⟩ ∉ bad j.val ∧ v ⟨j,e⟩ ∉ bad j.val ∧
      u ⟨j,e⟩+v ⟨j,e⟩ ∉ bad j.val)
    have hmajor : (8 ^ j.val) ^ 2 ≤ 2 * G.card := majority_fiber _ _ (hbad _ j.isLt)
    have hentry (e : D j) (he : e ∈ G) : t ^ 3 ≤ (8 ^ j.val) ^ 2 * (K ^ 3 * w ⟨j,e⟩) := by
      let i : (j : Fin J) × D j := ⟨j,e⟩
      obtain ⟨hgu,hgv,hgs⟩ := (Finset.mem_filter.mp he).2
      have hxl := e.1.isLt
      have hyl := e.2.isLt
      have hb (m : ℕ) (hm : 8^j.val ≤ m) (hm' : m < 6*8^j.val) :
          m ∉ bad j.val → t ≤ K * (2 ^ j.val) ^ 2 * cnt m := hbox _ j.isLt m hm hm'
      have hu := hb (u i) (by dsimp [u,i]; omega) (by dsimp [u,i]; omega) hgu
      have hv := hb (v i) (by dsimp [v,i]; omega) (by dsimp [v,i]; omega) hgv
      have hs := hb (u i + v i) (by dsimp [u,v,i]; omega) (by dsimp [u,v,i]; omega) hgs
      have hprod := Nat.mul_le_mul (Nat.mul_le_mul hu hv) hs
      have hpow : (8 : ℕ) ^ j.val = (2 ^ j.val) ^ 3 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      dsimp only [w]
      rw [hpow]
      calc
        t ^ 3 = t*t*t := by ring
        _ ≤ _ := hprod
        _ = _ := by ring
    have hg := Finset.sum_le_sum hentry
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul] at hg
    have hsub : ∑ e ∈ G, w ⟨j,e⟩ ≤ ∑ e : D j, w ⟨j,e⟩ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      exact Nat.zero_le _
    have htot : (8^j.val)^2 * t^3 ≤ (8^j.val)^2 * (2*K^3 * ∑ e : D j, w ⟨j,e⟩) := by
      calc
        _ ≤ (2*G.card)*t^3 := Nat.mul_le_mul_right _ hmajor
        _ = 2*(G.card*t^3) := by ring
        _ ≤ _ := Nat.mul_le_mul_left 2 hg
        _ ≤ 2*((8^j.val)^2*(K^3 * ∑ e : D j, w ⟨j,e⟩)) := by gcongr
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left htot (by positivity)
  have htotal := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hper j)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum,
    ← Fintype.sum_sigma'] at htotal
  have hup : 4 * t ^ 3 + 1 ≤ 5 * t ^ 3 := by
    have : 0 < t ^ 3 := by positivity
    omega
  have htotal' : J * t ^ 3 ≤ (10 * K ^ 3) * t ^ 3 := by
    calc
      J * t ^ 3 ≤ _ := htotal
      _ ≤ (2 * K ^ 3) * (5 * t ^ 3) := Nat.mul_le_mul_left _ (hcap.trans hup)
      _ = _ := by ring
  exact (not_le_of_gt hJ) (Nat.le_of_mul_le_mul_right htotal' (by positivity))

lemma gap_bin_union {f : ℕ → ℕ} (hf : StrictMono f) (H g L U N : ℕ) (P : Finset ℕ)
    (h0 : f 0 ≤ L) (hN : U ≤ f N) (hb : ∀ m ∈ P, L ≤ m*H ∧ (m+1)*H ≤ U) :
    P.card*H ≤ g * ((∑ m ∈ P, (Set.range f ∩ Set.Ioc (m*H) ((m+1)*H)).ncard) + P.card) +
      ∑ i ∈ (Finset.range N).filter (fun i => g < f (i+1)-f i),
        (min U (f (i+1)) - max L (f i)) := by
  classical
  let B (m : ℕ) := Finset.Ioc (m*H) ((m+1)*H)
  let A (m : ℕ) := (B m).filter (· ∈ Set.range f)
  let S (m : ℕ) := (insert (m*H) (A m)).biUnion (fun z => Finset.Ioc z (z+g))
  let I := (Finset.range N).filter (fun i => g < f (i+1)-f i)
  let G (i : ℕ) := Finset.Ioc (max L (f i)) (min U (f (i+1)))
  have hd : (↑P : Set ℕ).PairwiseDisjoint B := by
    apply Finset.pairwiseDisjoint_iff.mpr
    rintro m hm n hn ⟨x,hx⟩
    obtain ⟨hx1,hx2⟩ := Finset.mem_inter.mp hx
    obtain ⟨hm1,hm2⟩ := Finset.mem_Ioc.mp hx1
    obtain ⟨hn1,hn2⟩ := Finset.mem_Ioc.mp hx2
    rcases lt_trichotomy m n with h | h | h
    · have hle : (m+1)*H ≤ n*H := Nat.mul_le_mul_right H h
      omega
    · exact h
    · have hle : (n+1)*H ≤ m*H := Nat.mul_le_mul_right H h
      omega
  have hcov : P.biUnion B ⊆ P.biUnion S ∪ I.biUnion G := by
    intro x hx
    obtain ⟨m,hm,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hxl,hxr⟩ := Finset.mem_Ioc.mp hx
    obtain ⟨hL,hU⟩ := hb m hm
    have hex : ∃ i : ℕ, x ≤ f (i+1) := ⟨x, (Nat.le_succ _).trans (hf.id_le _)⟩
    let i := Nat.find hex
    have hir : x ≤ f (i+1) := Nat.find_spec hex
    have hil : f i < x := by
      cases hi : i with
      | zero => omega
      | succ k =>
        exact Nat.lt_of_not_ge (Nat.find_min hex (show k < i by omega))
    apply Finset.mem_union.mpr
    by_cases hs : f (i+1)-f i ≤ g
    · left
      apply Finset.mem_biUnion.mpr
      refine ⟨m, hm, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨max (m*H) (f i), ?_, Finset.mem_Ioc.mpr ⟨max_lt hxl hil, by omega⟩⟩
      by_cases hbase : f i ≤ m*H
      · simp [max_eq_left hbase]
      · rw [max_eq_right (by omega : m*H ≤ f i)]
        apply Finset.mem_insert_of_mem
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr (by omega), ⟨i,rfl⟩⟩
    · right
      apply Finset.mem_biUnion.mpr
      have hi : i < N := hf.lt_iff_lt.mp (hil.trans_le (hxr.trans (hU.trans hN)))
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, by omega⟩, ?_⟩
      exact Finset.mem_Ioc.mpr ⟨max_lt (hL.trans_lt hxl) hil, le_min (hxr.trans hU) hir⟩
  have hshort (m : ℕ) : (S m).card ≤ ((A m).card+1)*g := calc
    _ ≤ ∑ z ∈ insert (m*H) (A m), (Finset.Ioc z (z+g)).card := Finset.card_biUnion_le
    _ = (insert (m*H) (A m)).card*g := by simp
    _ ≤ _ := Nat.mul_le_mul_right g (Finset.card_insert_le _ _)
  have hsum : (P.biUnion S).card ≤ ((∑ m ∈ P, (A m).card)+P.card)*g := calc
    _ ≤ ∑ m ∈ P, (S m).card := Finset.card_biUnion_le
    _ ≤ ∑ m ∈ P, ((A m).card+1)*g := Finset.sum_le_sum (fun m _ => hshort m)
    _ = _ := by simp [← Finset.sum_mul, Finset.sum_add_distrib]
  have hn (m : ℕ) : (Set.range f ∩ Set.Ioc (m*H) ((m+1)*H)).ncard = (A m).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [A,B]
    tauto
  have hbig : (I.biUnion G).card ≤ ∑ i ∈ I, (min U (f (i+1)) - max L (f i)) := by
    simpa [G] using (Finset.card_biUnion_le : (I.biUnion G).card ≤ ∑ i ∈ I, (G i).card)
  have hl : (P.biUnion B).card = P.card*H := by
    rw [Finset.card_biUnion hd]
    simp [B, add_mul]
  rw [← hl]
  simp only [hn]
  rw [mul_comm g]
  exact (Finset.card_le_card hcov).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add hsum hbig))

theorem long_gap_coverage (f : ℕ → ℕ) (hf : StrictMono f)
    (hB : Erdos41.NtupleCondition (Set.range f) 3) (M : ℕ) :
    let J := 10*(4*M)^3+1
    ∀ᶠ t : ℕ in atTop, ∃ j < J, let L := 2^j*t
      L^3 < 12 * ∑ i ∈ (Finset.range (8*L+1)).filter
        (fun i => M*L^2 < f (i+1)-f i),
        (min (6*L^3) (f (i+1)) - max (L^3) (f i)) := by
  classical
  intro J
  filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop (f 0),
    eventually_ge_atTop (4*M*(2^J)^2)] with t ht h₀ h₁
  by_contra! hthin
  let K := 4*M
  let cnt (m : ℕ) := (Set.range f ∩ Ioc (m*t^3) ((m+1)*t^3)).ncard
  let bad (j : ℕ) := (Finset.Ico (8^j) (6*8^j)).filter (fun m => K*(2^j)^2*cnt m < t)
  apply majority_obstruction hB K J t ht (by dsimp [J,K]; omega) bad _ (by
    intro j hj m h1 h2 hm
    by_contra! h
    exact hm (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h1,h2⟩,h⟩))
  intro j hj
  let B : ℕ := 2^j
  let L := B*t
  let R : ℕ := 8^j
  let H := t^3
  let g := M*L^2
  let N := 8*L+1
  let P := bad j
  have hBp : 0 < B := by dsimp [B]; positivity
  have hLp : 0 < L := Nat.mul_pos hBp ht
  have hHp : 0 < H := by dsimp [H]; positivity
  have hB3 : B^3 = R := pow_eight j
  have hL3 : L^3 = R*H := by dsimp only [L]; rw [mul_pow,hB3]
  have hU : 6*L^3 ≤ f N := by
    have hmin := inverse_growth hf hB N
    dsimp [N] at hmin
    nlinarith only [hmin, show 1 ≤ L by omega, show 1 ≤ L^3 from Nat.pow_pos hLp, Nat.zero_le (L^2)]
  have hstart : f 0 ≤ L^3 := by
    have hh : t ≤ L := Nat.le_mul_of_pos_left _ hBp
    exact (h₀.trans hh).trans (Nat.le_self_pow (by decide) _)
  have hscale : 4*M*B^2 ≤ t := by
    have hB : B ≤ 2^J := Nat.pow_le_pow_right (by decide) hj.le
    have hh := Nat.mul_le_mul_left K (Nat.pow_le_pow_left hB 2)
    exact hh.trans h₁
  have hg4 : 4*g ≤ H := by
    have hh := Nat.mul_le_mul_right (t^2) hscale
    dsimp [g,L,H] at *
    nlinarith only [hh]
  have hcnt (m : ℕ) (hm : m ∈ P) : 4*g*cnt m ≤ H := by
    have hh := (Finset.mem_filter.mp hm).2
    change K*B^2*cnt m < t at hh
    have hh' := Nat.mul_le_mul_right (t^2) hh.le
    dsimp [K,g,L,H] at *
    nlinarith only [hh']
  have hbudget : 4 * (g * (∑ m ∈ P, cnt m) + g * P.card) ≤ 2 * H * P.card := by
    have hsum := Finset.sum_le_sum (s := P) hcnt
    rw [← Finset.mul_sum, Finset.sum_const, smul_eq_mul] at hsum
    nlinarith only [hsum, Nat.mul_le_mul_right P.card hg4]
  have hp (m : ℕ) (hm : m ∈ P) : L^3 ≤ m*H ∧ (m+1)*H ≤ 6*L^3 := by
    obtain ⟨h1,h2⟩ := Finset.mem_Ico.mp (Finset.mem_filter.mp hm).1
    refine ⟨hL3.le.trans (Nat.mul_le_mul_right H h1), ?_⟩
    rw [hL3, ← mul_assoc]
    exact Nat.mul_le_mul_right _ h2
  let W := ∑ i ∈ (Finset.range N).filter (fun i => g < f (i+1)-f i),
    (min (6*L^3) (f (i+1)) - max (L^3) (f i))
  have hcover : P.card*H ≤ g*((∑ m ∈ P, cnt m)+P.card)+W :=
    gap_bin_union hf H g (L^3) (6*L^3) N P hstart hU hp
  have htail : 12*W ≤ L^3 := le_of_not_gt (hthin j hj)
  change 6*P.card ≤ R
  apply Nat.le_of_mul_le_mul_right (c := H) _ hHp
  rw [hL3] at htail
  nlinarith only [hcover,hbudget,htail]



/-- Every real gap moment of order greater than one exceeds its critical
growth rate by arbitrarily large factors along an infinite subsequence. -/
theorem gap_moment_frequently (f : ℕ → ℕ) (hf : StrictMono f)
    (hB : Erdos41.NtupleCondition (Set.range f) 3) {p : ℝ} (hp : 1 < p) (C : ℝ) :
    ∃ᶠ n : ℕ in Filter.atTop,
      C < (∑ i ∈ Finset.range n, ((f (i+1)-f i : ℕ) : ℝ)^p) / ((n : ℝ)+1)^(2*p+1) := by
  classical
  let A := max C 1
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right ..)
  let q := 2*p+1
  have hq : 0 < q := by dsimp [q]; linarith
  have hmgo : Filter.Tendsto (fun m : ℕ => (m : ℝ)^(p-1)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hMp, hM⟩ := ((Filter.eventually_gt_atTop 0).and
    (hmgo.eventually_gt_atTop (12*A*10^q))).exists
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMp
  apply Filter.frequently_atTop.mpr
  intro n₀
  obtain ⟨t, ht, ht₀, hw⟩ := ((Filter.eventually_gt_atTop 0).and
    ((Filter.eventually_ge_atTop n₀).and (long_gap_coverage f hf hB M))).exists
  obtain ⟨j, _, hj⟩ := hw
  let L := 2^j*t
  let n := 8*L+1
  let v := fun i => f (i+1)-f i
  let I := (Finset.range n).filter (fun i => M*L^2 < v i)
  let g : ℝ := M*(L : ℝ)^2
  have hL : 0 < L := by dsimp [L]; positivity
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hg : 0 < g := by dsimp [g]; positivity
  have htn : t ≤ L := Nat.le_mul_of_pos_left t (by positivity)
  refine ⟨n, by dsimp [n]; omega, ?_⟩
  have hhNat : L^3 < 12 * ∑ i ∈ I, v i := by
    have hsub := Finset.sum_le_sum (s := I) (fun i _ =>
      tsub_le_tsub (min_le_right (6*L^3) (f (i+1))) (le_max_right (L^3) (f i)))
    exact hj.trans_le (Nat.mul_le_mul_left 12 hsub)
  have hh : (L : ℝ)^3 < 12 * ∑ i ∈ I, (v i : ℝ) := by exact_mod_cast hhNat
  have hsum :
      g^(p-1) * (∑ i ∈ I, (v i : ℝ)) ≤ ∑ i ∈ Finset.range n, (v i : ℝ)^p := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ i ∈ I, (v i : ℝ)^p := by
           apply Finset.sum_le_sum
           intro i hi
           have hgv : g < (v i : ℝ) := by dsimp only [g]; exact_mod_cast (Finset.mem_filter.mp hi).2
           have hx := Real.rpow_le_rpow hg.le hgv.le (by linarith : 0 ≤ p-1)
           have hy := mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg (v i))
           rwa [← Real.rpow_add_one (hg.trans hgv).ne', sub_add_cancel] at hy
         _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) (fun _ _ _ =>
           Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have heq : g^(p-1) * (L : ℝ)^3 = (M : ℝ)^(p-1)*(L : ℝ)^q := by
    dsimp [g,q]
    rw [Real.mul_rpow hMr.le (by positivity), mul_assoc, ← Real.rpow_natCast_mul hLr.le, ← Real.rpow_add_natCast hLr.ne']
    norm_num
    ring_nf
    simp
  have hlow : (M : ℝ)^(p-1)*(L : ℝ)^q <
      12 * ∑ i ∈ Finset.range n, (v i : ℝ)^p := by
    have h₁ := mul_lt_mul_of_pos_left hh (Real.rpow_pos_of_pos hg (p-1))
    rw [heq] at h₁
    nlinarith only [h₁, hsum]
  have hn : (n : ℝ)+1 ≤ 10*(L : ℝ) := by exact_mod_cast (by dsimp [n]; omega : n+1 ≤ 10*L)
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (n : ℝ)+1) hn hq.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 10) hLr.le] at hpow
  apply (lt_div_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).2
  change C*((n : ℝ)+1)^q < _
  have ha₁ := mul_le_mul_of_nonneg_right (le_max_left C 1) (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)+1) q)
  have ha₂ := mul_le_mul_of_nonneg_left hpow hA.le
  have h₃ := mul_lt_mul_of_pos_right hM (Real.rpow_pos_of_pos hLr q)
  change C*((n : ℝ)+1)^q < ∑ i ∈ Finset.range n, (v i : ℝ)^p
  change C*((n : ℝ)+1)^q ≤ A*((n : ℝ)+1)^q at ha₁
  nlinarith only [ha₁,ha₂,h₃,hlow]

theorem main : H1 → H2 → type_of% @Erdos41.erdos_41 := by
  intro hsmooth hirregular A hB hA
  let f := Nat.nth (· ∈ A)
  have hmono : StrictMono f := Nat.nth_strictMono hA
  have hr : range f = A := Nat.range_nth_of_infinite hA
  have hfB : Erdos41.NtupleCondition (range f) 3 := hr ▸ hB
  by_cases hg : (fun i : ℕ => ((f (i+1)-f i : ℕ) : ℝ)) =o[atTop]
      (fun i : ℕ => (i : ℝ)^2 * Real.log (i+2))
  · rw [← hr]
    exact hsmooth f hmono hfB hg
  · by_contra hne
    have hnn := le_liminf_of_le (upper_ratio A hB) (Eventually.of_forall fun n =>
        div_nonneg (Nat.cast_nonneg (A ∩ Icc 1 n).ncard) (Real.rpow_nonneg (Nat.cast_nonneg n) (1/3 : ℝ)))
    obtain ⟨K, N₀, _, hk⟩ := eventual_cubic_of_pos A (lt_of_le_of_ne hnn (Ne.symm hne))
    apply hirregular f hmono ⟨K, ?_⟩ hg (fun _ hp C => gap_moment_frequently f hmono hfB hp C) hfB
    filter_upwards [eventually_ge_atTop N₀] with n hn
    have hcount : (A ∩ Icc 1 (f n)).ncard ≤ n+1 := by
      have hsub : A ∩ Icc 1 (f n) ⊆ f '' Iic n := by
        rintro x ⟨hx,hy⟩
        rw [← hr] at hx
        obtain ⟨i,rfl⟩ := hx
        exact ⟨i, hmono.le_iff_le.mp hy.2, rfl⟩
      have hh := Set.ncard_le_ncard hsub ((Set.finite_Iic n).image f)
      simpa [Set.ncard_image_of_injective _ hmono.injective] using hh
    exact (hk (f n) (hn.trans (hmono.id_le n))).trans
      (Nat.mul_le_mul_left K (Nat.pow_le_pow_left hcount 3))

end OMA.R_Erdos41_erdos_41_R1
