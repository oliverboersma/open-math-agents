import OMAReductions.R_Erdos930_erdos_930_variants_consecutive_integers_R1

/-! Erdős and Selfridge, Illinois J. Math. 19 (1975), Section 2.1. A pair of factors from the smaller part of a bipartite factorization graph has at most one common neighbor. Counting these pairs bounds the order statistics of every set of coefficients with distinct products. The remaining estimates concern explicit finite factor covers, the prime count, and a numerical product independent of the coefficients. -/

namespace OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1
open Finset

-- The two finite factor covers in the proof of inequalities (15) and (16).
def H1 : Prop := ∀ x : ℕ,
  (∃ U V : Finset ℕ, (∀ s : ℕ, 0 < s → s ≤ x → ∃ u ∈ U, ∃ v ∈ V, s=u*v) ∧
    1260*(U.card+V.card.choose 2) ≤ 353*x+383040) ∧
  (∃ U V : Finset ℕ, (∀ s : ℕ, 0 < s → s ≤ x → ∃ u ∈ U, ∃ v ∈ V, s=u*v) ∧
    41580*(U.card+V.card.choose 2) ≤ 9547*x+62037360)

-- An explicit prime-counting estimate, weaker than Dusart, Corollary 5.3.
def H2 : Prop := ∀ k : ℕ, 30000 ≤ k →
  (k.primesBelow.card : ℝ) * (Real.log k - 6/5) ≤ k

-- The gain in the lower bound for the product of the first m coefficients.
def H3 : Prop :=
  let L (i : ℕ) := max i (max ((1260*(i-304)+352)/353) ((41580*(i-1492)+9546)/9547))
  ∀ m : ℕ, 26700 ≤ m →
    (51:ℝ)/40*m ≤ Real.log ((∏ i ∈ range m, L (i+1) : ℕ) : ℝ) - Real.log (m.factorial : ℝ)

theorem coverBound {S U V : Finset ℕ} (pos : ∀ s ∈ S, 0<s) (uniq : (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, ∀ w ∈ S, x*y=z*w → x=z ∨ x=w))
    (cover : ∀ s ∈ S, ∃ u ∈ U, ∃ v ∈ V, s=u*v) :
    S.card ≤ U.card + V.card.choose 2 := by
  classical
  let F (u : ℕ) := V.filter (fun v => u*v ∈ S)
  let P (u : ℕ) := (F u).powersetCard 2
  have disj : (U : Set ℕ).PairwiseDisjoint P := by
    intro u hu t ht hut
    apply Finset.disjoint_left.mpr
    intro pair hp hq
    have m := mem_powersetCard.mp hp
    have n := mem_powersetCard.mp hq
    obtain ⟨v,w,hvw,rfl⟩ := card_eq_two.mp m.2
    have h0 := (mem_filter.mp (m.1 (mem_insert_self ..))).2
    have h1 := (mem_filter.mp (m.1 (mem_insert_of_mem (mem_singleton_self _)))).2
    have h2 := (mem_filter.mp (n.1 (mem_insert_self ..))).2
    have h3 := (mem_filter.mp (n.1 (mem_insert_of_mem (mem_singleton_self _)))).2
    have hpos := pos _ h0
    rcases uniq _ h0 _ h3 _ h1 _ h2 (by ring) with he|he
    · exact hvw (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_mul_pos_right hpos) he)
    · exact hut (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_mul_pos_left hpos) he)
  have subset : U.biUnion P ⊆ V.powersetCard 2 := by
    intro s hs
    obtain ⟨u,_,hu⟩ := mem_biUnion.mp hs
    have h := mem_powersetCard.mp hu
    exact mem_powersetCard.mpr ⟨h.1.trans (filter_subset ..), h.2⟩
  have pairs := card_le_card subset
  rw [card_biUnion disj,card_powersetCard] at pairs
  have localBound (u : ℕ) : (F u).card ≤ 1 + (P u).card := by
    rw [show (P u).card = (F u).card.choose 2 from card_powersetCard ..]
    generalize (F u).card = m
    cases m with
    | zero => omega
    | succ m => rw [Nat.choose_succ_succ, Nat.choose_one_right]; omega
  have mapped : S ⊆ U.biUnion (fun u => (F u).image (u*·)) := by
    intro s hs
    obtain ⟨u,hu,v,hv,rfl⟩ := cover s hs
    exact mem_biUnion.mpr ⟨u,hu,mem_image.mpr ⟨v, mem_filter.mpr ⟨hv,hs⟩,rfl⟩⟩
  calc S.card ≤ _ := card_le_card mapped
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ u ∈ U, (1+(P u).card) := sum_le_sum (fun u _ => card_image_le.trans (localBound u))
    _ ≤ _ := by rw [sum_add_distrib]; simpa using Nat.add_le_add_left pairs U.card

theorem sortedProd (covers : H1) {k : ℕ} (a : Fin k → ℕ) (apos : ∀ i, 0 < a i)
    (sid : ∀ i j u v, i ≤ j → u ≤ v → a i*a j = a u*a v → i=u ∧ j=v)
    (T : Finset (Fin k)) :
    let L (i : ℕ) := max i (max ((1260*(i-304)+352)/353) ((41580*(i-1492)+9546)/9547))
   
    (∏ i ∈ range T.card, L (i+1)) ≤ ∏ i ∈ T, a i := by
  classical
  let L (i : ℕ) := max i (max ((1260*(i-304)+352)/353) ((41580*(i-1492)+9546)/9547))
  change (∏ i ∈ range T.card, L (i+1)) ≤ _
  have inj : Function.Injective a := by
    intro i j he
    exact (sid i i j j le_rfl le_rfl (by rw [he])).1
  have pair (i j u v : Fin k) (he : a i*a j = a u*a v) : i=u ∨ i=v := by
    rcases le_total i j with hi|hi <;> rcases le_total u v with hj|hj
    · exact Or.inl (sid _ _ _ _ hi hj he).1
    · exact Or.inr (sid _ _ _ _ hi hj (he.trans (mul_comm ..))).1
    · exact Or.inr (sid _ _ _ _ hi hj ((mul_comm ..).trans he)).2
    · exact Or.inl (sid _ _ _ _ hi hj ((mul_comm ..).trans (he.trans (mul_comm ..)))).2
  let B := T.image a
  have hB : B.card = T.card := card_image_of_injective _ inj
  let b := B.orderEmbOfFin hB
  have bmem (i : Fin T.card) : b i ∈ B := B.orderEmbOfFin_mem _ _
  have lower (i : Fin T.card) : L (i.val+1) ≤ b i := by
    let S := (Iic i).image b
    have hS : S.card = i.val+1 := (card_image_of_injective _ b.injective).trans (Fin.card_Iic _)
    have sinB {s : ℕ} (hs : s ∈ S) : s ∈ B := by
      obtain ⟨t,_,rfl⟩ := mem_image.mp hs
      exact bmem t
    have pos (s : ℕ) (hs : s ∈ S) : 0 < s := by
      obtain ⟨t,_,rfl⟩ := mem_image.mp (sinB hs)
      exact apos t
    have small (s : ℕ) (hs : s ∈ S) : s ≤ b i := by
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hs
      exact b.monotone (mem_Iic.mp ht)
    have uniq : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, ∀ w ∈ S, x*y=z*w → x=z ∨ x=w := by
      intro x hx y hy z hz w hw
      obtain ⟨s,_,rfl⟩ := mem_image.mp (sinB hx)
      obtain ⟨t,_,rfl⟩ := mem_image.mp (sinB hy)
      obtain ⟨m,_,rfl⟩ := mem_image.mp (sinB hz)
      obtain ⟨n,_,rfl⟩ := mem_image.mp (sinB hw)
      intro h
      exact (pair s t m n h).imp (congrArg a) (congrArg a)
    have hsmall : S ⊆ Icc 1 (b i) := fun s hs => mem_Icc.mpr ⟨pos s hs,small s hs⟩
    have hc := card_le_card hsmall
    simp only [Nat.card_Icc] at hc
    obtain ⟨⟨U₁,V₁,hc₁,hn₁⟩,⟨U₂,V₂,hc₂,hn₂⟩⟩ := covers (b i)
    have ha := coverBound pos uniq (fun s hs => hc₁ s (pos s hs) (small s hs))
    have hb := coverBound pos uniq (fun s hs => hc₂ s (pos s hs) (small s hs))
    have h1 : 1260*S.card ≤ 353*b i+383040 := by omega
    have h2 : 41580*S.card ≤ 9547*b i+62037360 := by omega
    rw [hS] at h1 h2 hc
    dsimp only [L]
    omega
  rw [← Fin.prod_univ_eq_prod_range]
  calc _ ≤ ∏ i, b i := Finset.prod_le_prod' (fun i _ => lower i)
    _ = ∏ s ∈ B, s := by
      conv_rhs => rw [← B.image_orderEmbOfFin_univ hB]
      rw [Finset.prod_image b.injective.injOn]
    _ = _ := by dsimp only [B]; rw [Finset.prod_image inj.injOn]

theorem main : H1 → H2 → H3 → OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1.H4 := by
  classical
  intro covers piBound gain k a hk apos sid T hT
  let L (i : ℕ) := max i (max ((1260*(i-304)+352)/353) ((41580*(i-1492)+9546)/9547))
  let r := k.primesBelow.card
  let m := k-r
  have hl : r ≤ k := by
    change (k.primesBelow).card ≤ k
    simpa using card_le_card (show k.primesBelow ⊆ range k from
      fun p hp => mem_range.mpr (Nat.lt_of_mem_primesBelow hp))
  have hmk : m+r=k := Nat.sub_add_cancel hl
  have hmkr : (m:ℝ)+(r:ℝ)=(k:ℝ) := by exact_mod_cast hmk
  have px : (r:ℝ)*(Real.log k-6/5) ≤ k := piBound k hk
  have hklarge : (30000:ℝ) ≤ k := by exact_mod_cast hk
  have logk : (103/10:ℝ) ≤ Real.log k := by
    have p : (2:ℝ)^1041 ≤ (k:ℝ)^70 := (show (2:ℝ)^1041 ≤ 30000^70 by exact_mod_cast (by decide +kernel : (2:ℕ)^1041 ≤ 30000^70)).trans
      (pow_le_pow_left₀ (by norm_num) hklarge _)
    have h := Real.log_le_log (show 0 < (2:ℝ)^1041 by positivity) p
    rw [Real.log_pow,Real.log_pow] at h
    norm_num1 at h
    linarith [Real.log_two_gt_d9]
  have frac : 100*(r:ℝ) ≤ 11*k := by
    nlinarith [mul_nonneg (sub_nonneg.mpr logk) (Nat.cast_nonneg (α:=ℝ) r)]
  have hm : 26700 ≤ m := by
    have hn : 26700 ≤ (m:ℝ) := by linarith
    exact_mod_cast hn
  have kr : (r:ℝ)*Real.log k < (51:ℝ)/40*m := by linarith
  let Z := ∏ i ∈ range m, L (i+1)
  have gz : (51:ℝ)/40*m ≤ Real.log (Z:ℝ) - Real.log (m.factorial:ℝ) := gain m hm
  have hpow : m.factorial * k^r < Z := by
    by_contra! hn
    have posZ : 0 < Z := Finset.prod_pos (fun i _ => lt_of_lt_of_le (Nat.succ_pos i) (le_max_left ..))
    have hlog := Real.log_le_log (show 0 < (Z:ℝ) by exact_mod_cast posZ)
      (show (Z:ℝ) ≤ (m.factorial:ℕ) * (k:ℝ)^r by exact_mod_cast hn)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
    linarith
  have hfac : k.factorial ≤ m.factorial*k^r := by
    rw [← Nat.factorial_mul_descFactorial hl]
    exact Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow k r)
  obtain ⟨D,hsub,hc⟩ := Finset.exists_subset_card_eq hT
  have hs := sortedProd covers a apos sid D
  change D.card=m at hc
  rw [hc] at hs
  exact ((Nat.factorial_le (show k-1 ≤ k by omega)).trans hfac).trans_lt
    ((hpow.trans_le hs).trans_le (Finset.prod_le_prod_of_subset_of_one_le' hsub (fun i _ _ => apos i)))

end OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1
