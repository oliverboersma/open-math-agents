import FormalConjectures.ErdosProblems.«52»

/-!
# Simultaneous regularisation of the integer sum-product problem

Select a subset of the ordered pairs maximising a weighted objective that charges
for each distinct first coordinate, second coordinate, sum and product. Removing
a fibre that is too small would improve the objective. At least half the pairs
survive, so the union of the coordinate projections has size at least half the
original set. Every element of that union has many partners for which both the
sum and the product have many representations inside the union itself.

Cauchy–Schwarz disposes of the case with small energy in either operation; we
provide its proof from Mathlib's pointwise energy lemmas. The high-energy growth
estimate on the regularised sets is open.
-/
namespace OMA.R_Erdos52_erdos_52_R1
open Finset
open scoped Pointwise

/-- Cauchy–Schwarz, simultaneously for additive and multiplicative representations.
Mathlib already formalises each estimate separately. -/
def H1 : Prop := ∀ S : Finset ℤ,
  S.card^4 ≤ max (S+S).card (S*S).card * min (addEnergy S S) (mulEnergy S S)

/-- The remaining near-quadratic growth estimate on popular cores whose two energies
both exceed the Cauchy–Schwarz threshold. The partners in the two popularity
conditions are the same, and all representations are internal to the core. -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℤ) (M : ℕ),
  (S+S).card ≤ M → (S*S).card ≤ M →
  (S.card : ℝ)^(2+ε) < (min (addEnergy S S) (mulEnergy S S) : ℝ) →
  (∀ x ∈ S, S.card ≤ 8 * (S.filter (fun y =>
    S.card^2 ≤ 8*M*((S ×ˢ S).filter (fun p => p.1+p.2 = x+y)).card ∧
    S.card^2 ≤ 8*M*((S ×ˢ S).filter (fun p => p.1*p.2 = x*y)).card)).card) →
  C * (S.card : ℝ)^(2-ε) ≤ M

theorem classical_energy : H1 := by
  intro S
  have ha := le_card_add_mul_addEnergy S S
  have hm := le_card_mul_mul_mulEnergy S S
  rw [show S.card^4 = S.card^2*S.card^2 by ring]
  rcases le_total (addEnergy S S) (mulEnergy S S) with h|h
  · rw [min_eq_left h]
    exact ha.trans (Nat.mul_le_mul_right _ (le_max_left _ _))
  · rw [min_eq_right h]
    exact hm.trans (Nat.mul_le_mul_right _ (le_max_right _ _))


/-- Delete sparse fibres until every remaining label meets its threshold.
The objective charges for each distinct label in each projection. -/
private lemma select {α : Type*} [DecidableEq α] {d : ℕ}
    (U : Finset α) (f : Fin d → α → ℤ) (w : Fin d → ℤ) (hw : ∀ i, 0 ≤ w i) (K : ℤ) :
    ∃ E ⊆ U, K * U.card - (∑ i, w i * ((U.image (f i)).card : ℤ)) ≤ K * E.card ∧
      ∀ i, ∀ z ∈ E.image (f i), w i ≤ K * ((E.filter (fun e => f i e = z)).card : ℤ) := by
  classical
  let score (V : Finset α) : ℤ := K * V.card - ∑ i, w i * ((V.image (f i)).card : ℤ)
  obtain ⟨E,hE,hm⟩ := U.powerset.exists_max_image score ⟨U,mem_powerset.mpr Subset.rfl⟩
  have hEU := mem_powerset.mp hE
  refine ⟨E,hEU,?_,?_⟩
  · have h := hm U (mem_powerset.mpr Subset.rfl)
    have hc : 0 ≤ ∑ i, w i * ((E.image (f i)).card : ℤ) :=
      sum_nonneg fun i _ => mul_nonneg (hw i) (by positivity)
    dsimp [score] at h
    linarith
  · intro i z hz
    let D := E.filter (fun x => f i x ≠ z)
    have hDE : D ⊆ E := filter_subset _ _
    have h := hm D (mem_powerset.mpr (hDE.trans hEU))
    let loss (j : Fin d) : ℤ := w j * ((E.image (f j)).card : ℤ) - w j * ((D.image (f j)).card : ℤ)
    have lp (j : Fin d) : 0 ≤ loss j := by
      exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_card (image_subset_image hDE : D.image (f j) ⊆ E.image (f j))) (hw j))
    have hd : D.image (f i) ⊆ (E.image (f i)).erase z := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
      exact mem_erase.mpr ⟨(mem_filter.mp hx).2,mem_image_of_mem _ (hDE hx)⟩
    have hdrop := card_le_card hd
    rw [card_erase_of_mem hz] at hdrop
    have hepos := card_pos.mpr ⟨z,hz⟩
    have hdiff : (1 : ℤ) ≤ ((E.image (f i)).card : ℤ) - (D.image (f i)).card := by omega
    have low : w i ≤ loss i := by
      dsimp [loss]
      nlinarith only [mul_le_mul_of_nonneg_left hdiff (hw i)]
    have total := (single_le_sum (fun j _ => lp j) (mem_univ i))
    have comp : w i ≤ ∑ j, loss j := low.trans total
    simp only [loss,sum_sub_distrib] at comp
    have partition : (E.filter (fun e => f i e = z)).card + D.card = E.card :=
      card_filter_add_card_filter_not _
    have partition' : ((E.filter (fun e => f i e = z)).card : ℤ) + D.card = E.card := by exact_mod_cast partition
    dsimp [score] at h
    rw [← partition'] at h
    linarith only [h,comp]



private lemma core (A : Finset ℤ) (M : ℕ) (hm : 0 < M)
    (hs : (A+A).card ≤ M) (hp : (A*A).card ≤ M) :
    ∃ S ⊆ A, A.card ≤ 2*S.card ∧
      ∀ x ∈ S, S.card ≤ 8 * (S.filter (fun y =>
        S.card^2 ≤ 8*M*((S ×ˢ S).filter (fun p => p.1+p.2 = x+y)).card ∧
        S.card^2 ≤ 8*M*((S ×ˢ S).filter (fun p => p.1*p.2 = x*y)).card)).card := by
  classical
  let U := A ×ˢ A
  let f : Fin 4 → ℤ × ℤ → ℤ := ![Prod.fst,Prod.snd,fun p => p.1+p.2, fun p => p.1*p.2]
  let w : Fin 4 → ℤ := ![(M:ℤ)*A.card,(M:ℤ)*A.card,(A.card:ℤ)^2,(A.card:ℤ)^2]
  have wt (i : Fin 4) : 0 ≤ w i := by fin_cases i <;> simp [w] <;> positivity
  obtain ⟨E,sub,sz,hf⟩ := select U f w wt (8*(M:ℤ))
  let S := E.image Prod.fst ∪ E.image Prod.snd
  have lr {x : ℤ × ℤ} (hx : x ∈ E) : x.1 ∈ S ∧ x.2 ∈ S :=
    ⟨mem_union_left _ (mem_image_of_mem _ hx),mem_union_right _ (mem_image_of_mem _ hx)⟩
  have eSS : E ⊆ S ×ˢ S := fun _ h => mem_product.mpr (lr h)
  have sA : S ⊆ A := by
    intro x hx
    rcases mem_union.mp hx with hl | hr
    · obtain ⟨p,hp,rfl⟩ := mem_image.mp hl
      exact (mem_product.mp (sub hp)).1
    · obtain ⟨p,hp,rfl⟩ := mem_image.mp hr
      exact (mem_product.mp (sub hp)).2
  have lim (i : Fin 4) : ((U.image (f i)).card : ℤ) ≤ (![((A.card:ℕ)), A.card, M,M] i : ℕ) := by
    apply Int.ofNat_le.mpr
    fin_cases i
    · exact card_le_card (image_subset_iff.mpr fun _ h => (mem_product.mp h).1)
    · exact card_le_card (image_subset_iff.mpr fun _ h => (mem_product.mp h).2)
    · exact (card_le_card (image_subset_iff.mpr fun _ h => add_mem_add (mem_product.mp h).1 (mem_product.mp h).2)).trans hs
    · exact (card_le_card (image_subset_iff.mpr fun _ h => mul_mem_mul (mem_product.mp h).1 (mem_product.mp h).2)).trans hp
  have cost := sum_le_sum (s := (univ : Finset (Fin 4))) (fun i _ => mul_le_mul_of_nonneg_left (lim i) (wt i))
  simp [Fin.sum_univ_succ,w] at cost
  change _ ≤ 8*(M:ℤ)*E.card at sz
  simp [Fin.sum_univ_succ,w] at sz
  have count : (U.card:ℤ) = (A.card:ℤ)^2 := by simp [U,sq]
  rw [count] at sz
  have dense : A.card^2 ≤ 2*E.card := by
    have big : (M:ℤ)*(A.card:ℤ)^2 ≤ (M:ℤ)*(2*E.card) := by nlinarith only [sz,cost]
    exact_mod_cast (le_of_mul_le_mul_left big (by exact_mod_cast hm))
  have ess := card_le_card eSS
  rw [card_product] at ess
  have enough : A.card ≤ 2*S.card := by nlinarith
  refine ⟨S,sA,enough,?_⟩
  have sc := card_le_card sA
  have good {x y : ℤ} (hxy : (x,y) ∈ E) :
      S.card^2 ≤ 8*M*((S ×ˢ S).filter (fun p => p.1+p.2 = x+y)).card ∧
      S.card^2 ≤ 8*M*((S ×ˢ S).filter (fun p => p.1*p.2 = x*y)).card := by
    have label (i : Fin 4) : w i ≤ (8*(M:ℤ))*(((S ×ˢ S).filter (fun p => f i p = f i (x,y))).card : ℤ) := by
      refine (hf i _ (mem_image_of_mem _ hxy)).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact_mod_cast card_le_card (filter_subset_filter _ eSS)
    constructor
    · exact (Nat.pow_le_pow_left sc 2).trans (by exact_mod_cast (show (A.card:ℤ)^2 ≤ 8*(M:ℤ)*(((S ×ˢ S).filter (fun p => p.1+p.2 = x+y)).card : ℤ) from label 2))
    · exact (Nat.pow_le_pow_left sc 2).trans (by exact_mod_cast (show (A.card:ℤ)^2 ≤ 8*(M:ℤ)*(((S ×ˢ S).filter (fun p => p.1*p.2 = x*y)).card : ℤ) from label 3))
  intro x hx
  let G := S.filter (fun y => S.card^2 ≤ 8*M*((S ×ˢ S).filter (fun p => p.1+p.2 = x+y)).card ∧
                               S.card^2 ≤ 8*M*((S ×ˢ S).filter (fun p => p.1*p.2 = x*y)).card)
  have proj (i : Fin 4) (hi : i = 0 ∨ i = 1) (hx' : x ∈ E.image (f i)) :
      A.card ≤ 8*((E.filter (fun p => f i p = x)).card) := by
    have h := hf i x hx'
    have hw' : w i = (M:ℤ)*A.card := by rcases hi with rfl|rfl <;> rfl
    rw [hw',show 8*(M:ℤ) = M*8 by ring,mul_assoc] at h
    have h' := le_of_mul_le_mul_left h (show (0:ℤ) < M by exact_mod_cast hm)
    exact_mod_cast h'
  rcases mem_union.mp hx with hx' | hx'
  · apply sc.trans ((proj 0 (Or.inl rfl) hx').trans (Nat.mul_le_mul_left 8 _))
    apply card_le_card_of_injOn Prod.snd
    · rintro ⟨a,b⟩ h
      obtain ⟨he,heq⟩ := mem_filter.mp h
      subst x
      exact mem_filter.mpr ⟨(lr he).2,good he⟩
    · rintro ⟨a,b⟩ h ⟨c,d⟩ h' eq
      exact Prod.ext ((mem_filter.mp h).2.trans (mem_filter.mp h').2.symm) eq
  · apply sc.trans ((proj 1 (Or.inr rfl) hx').trans (Nat.mul_le_mul_left 8 _))
    apply card_le_card_of_injOn Prod.fst
    · rintro ⟨a,b⟩ h
      obtain ⟨he,heq⟩ := mem_filter.mp h
      subst x
      obtain ⟨h₁,h₂⟩ := good he
      exact mem_filter.mpr ⟨(lr he).1,by simpa only [show f 1 (a,b) = b by rfl,add_comm b a,mul_comm b a] using And.intro h₁ h₂⟩
    · rintro ⟨a,b⟩ h ⟨c,d⟩ h' eq
      exact Prod.ext eq ((mem_filter.mp h).2.trans (mem_filter.mp h').2.symm)

theorem main : H1 → H2 → type_of% @Erdos52.erdos_52 := by
  intro energy hard ε ep eu
  obtain ⟨c,hc,heavy⟩ := hard ε ep eu
  let b := min c 1
  have bp : 0 < b := lt_min hc (by norm_num)
  have ex : 0 < 2-ε := by linarith
  refine ⟨b/4,by positivity,?_⟩
  intro A
  let M := max (A+A).card (A*A).card
  rw [← Nat.cast_max]
  change b/4*(A.card:ℝ)^(2-ε) ≤ (M:ℝ)
  rcases A.eq_empty_or_nonempty with rfl|ne
  · simp [M,Real.zero_rpow ex.ne']
  have ma := le_max_left (A+A).card (A*A).card
  have mp := le_max_right (A+A).card (A*A).card
  have mpos := ne.card_pos.trans_le ((card_le_card_add_self (s := A)).trans ma)
  obtain ⟨S,hsub,hsize,rich⟩ := core A M mpos ma mp
  have sp : (0:ℝ) < S.card := by exact_mod_cast (show 0 < S.card by have := ne.card_pos; omega)
  have plus : (S+S).card ≤ M := (card_le_card (add_subset_add hsub hsub)).trans ma
  have times : (S*S).card ≤ M := (card_le_card (mul_subset_mul hsub hsub)).trans mp
  let e := min (addEnergy S S) (mulEnergy S S)
  have ht : b*(S.card:ℝ)^(2-ε) ≤ M := by
    by_cases h : (S.card:ℝ)^(2+ε) < (e:ℝ)
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans (heavy S M plus times (by simpa only [e,Nat.cast_min] using h) rich)
    · have cs : S.card^4 ≤ M*e := (energy S).trans (Nat.mul_le_mul_right _ (max_le plus times))
      have cs' : (S.card:ℝ)^4 ≤ M*(e:ℝ) := by exact_mod_cast cs
      have fac : (S.card:ℝ)^(2-ε) * (S.card:ℝ)^(2+ε) = (S.card:ℝ)^4 := by
        rw [← Real.rpow_add sp,show (2-ε)+(2+ε) = (4:ℝ) by ring]
        norm_num
      have le := (fac.le.trans cs').trans (mul_le_mul_of_nonneg_left (le_of_not_gt h) (by positivity))
      have low := le_of_mul_le_mul_right le (Real.rpow_pos_of_pos sp _)
      simpa only [one_mul] using (mul_le_mul_of_nonneg_right (min_le_right c 1) (Real.rpow_nonneg sp.le (2-ε))).trans (by simpa using low : 1*(S.card:ℝ)^(2-ε) ≤ M)
  have sc : (A.card:ℝ) ≤ 2*S.card := by exact_mod_cast hsize
  have two : (2:ℝ)^(2-ε) ≤ 4 := by
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := by norm_num
  have tr := Real.rpow_le_rpow (show (0:ℝ) ≤ A.card by positivity) sc ex.le
  rw [Real.mul_rpow (by norm_num) sp.le] at tr
  have tr' := tr.trans (mul_le_mul_of_nonneg_right two (Real.rpow_nonneg sp.le _))
  nlinarith only [mul_le_mul_of_nonneg_left tr' bp.le,ht]

end OMA.R_Erdos52_erdos_52_R1
