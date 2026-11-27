import FormalConjectures.Paper.WeaklyFirstCountable

open TopologicalSpace Topology Filter Set
open scoped Cardinal

namespace YakovlevCH

/-- The well-ordered type of order type ω₁ (in Type 0). -/
abbrev I : Type := (Cardinal.aleph.{0} 1).ord.ToType

lemma card_I : #I = ℵ₁ := by
  rw [Cardinal.mk_toType, Cardinal.card_ord]

lemma nonempty_I : Nonempty I := by
  by_contra h
  have h0 : #I = 0 := Cardinal.mk_eq_zero_iff.mpr (not_nonempty_iff.mp h)
  rw [card_I] at h0
  exact (Cardinal.aleph_pos 1).ne' h0

lemma I_uncountable : ¬ Countable I := by
  intro h
  have hle : #I ≤ ℵ₀ := Cardinal.mk_le_aleph0
  rw [card_I] at hle
  have hlt : ℵ₀ < ℵ₁ := by
    rw [← Cardinal.aleph_zero]
    exact Cardinal.aleph_lt_aleph.mpr (by norm_num)
  exact not_lt_of_ge hle hlt

lemma countable_Iio (α : I) : ({β : I | β < α}).Countable := by
  have hlt : #({β : I | β < α}) < ℵ₁ := by
    have h1 : Ordinal.type ((· < ·) : I → I → Prop) = (Cardinal.aleph.{0} 1).ord :=
      Ordinal.type_toType _
    have hcard : #({β : I | β < α}) = (Ordinal.typein ((· < ·) : I → I → Prop) α).card := by
      rw [Ordinal.card_typein]; rfl
    rw [hcard]
    have hlt_ord : Ordinal.typein ((· < ·) : I → I → Prop) α < (Cardinal.aleph.{0} 1).ord := by
      calc Ordinal.typein ((· < ·) : I → I → Prop) α
          < Ordinal.type ((· < ·) : I → I → Prop) := Ordinal.typein_lt_type _ α
        _ = (Cardinal.aleph.{0} 1).ord := h1
    exact Cardinal.lt_ord.mp hlt_ord
  have hle : #({β : I | β < α}) ≤ ℵ₀ := by
    have h1 : Order.succ ℵ₀ = ℵ₁ := by
      rw [← Cardinal.aleph_zero, Cardinal.succ_aleph]
      norm_num
    exact Order.lt_succ_iff.mp (h1.symm ▸ hlt)
  exact Cardinal.le_aleph0_iff_set_countable.mp hle

lemma countable_Iic (α : I) : ({β : I | β ≤ α}).Countable := by
  have heq : {β : I | β ≤ α} = insert α {β : I | β < α} := by
    ext β
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, le_iff_eq_or_lt]
  rw [heq]
  exact (countable_Iio α).insert α

/-- Every countable subset of I is bounded above in I. -/
lemma exists_gt_of_countable (S : Set I) (hS : S.Countable) : ∃ α : I, ∀ β ∈ S, β < α := by
  by_contra hno
  push_neg at hno
  have hunion : (Set.univ : Set I) ⊆ ⋃ β ∈ S, {γ : I | γ ≤ β} := by
    intro γ _
    obtain ⟨β, hβS, hγβ⟩ := hno γ
    exact Set.mem_biUnion hβS hγβ
  have hc : (Set.univ : Set I).Countable :=
    (hS.biUnion fun β _ => countable_Iic β).mono hunion
  exact I_uncountable (Set.countable_univ_iff.mp hc)

/-- Candidate countable infinite subsets of I × ℕ contained in some level F_n. -/
abbrev Cand : Type :=
  {p : Set (I × ℕ) × ℕ // p.1.Countable ∧ p.1.Infinite ∧ ∀ x ∈ p.1, x.2 ≤ p.2}

lemma card_Cand_le [Fact ((ℵ₁ : Cardinal.{0}) = 𝔠)] : #Cand ≤ ℵ₁ := by
  have hCH : (ℵ₁ : Cardinal.{0}) = 𝔠 := Fact.out
  have hcard_prod : #(I × ℕ) = ℵ₁ := by
    rw [Cardinal.mk_prod, card_I, Cardinal.mk_nat, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.mul_eq_left (Cardinal.aleph0_le_aleph 1) (Cardinal.aleph0_le_aleph 1)
      Cardinal.aleph0_ne_zero
  have hsurj : ∀ c : Cand, ∃ f : ℕ → I × ℕ, Set.range f = c.1.1 := by
    intro c
    obtain ⟨g, hg⟩ := (Set.countable_iff_exists_surjective c.2.2.1.nonempty).mp c.2.1
    refine ⟨fun k => (g k).1, ?_⟩
    ext x
    simp only [Set.mem_range]
    constructor
    · rintro ⟨k, rfl⟩; exact (g k).2
    · intro hx; obtain ⟨k, hk⟩ := hg ⟨x, hx⟩; exact ⟨k, congrArg Subtype.val hk⟩
  have hle1 : #Cand ≤ #((ℕ → I × ℕ) × ℕ) := by
    refine Cardinal.mk_le_of_injective
      (f := fun c : Cand => (Classical.choose (hsurj c), c.1.2)) ?_
    intro c₁ c₂ heq
    have h12 := Prod.mk.inj heq
    have hr : c₁.1.1 = c₂.1.1 := by
      rw [← Classical.choose_spec (hsurj c₁), ← Classical.choose_spec (hsurj c₂), h12.1]
    exact Subtype.ext (Prod.ext hr h12.2)
  have hpow : #(ℕ → I × ℕ) = ℵ₁ := by
    rw [Cardinal.mk_arrow, hcard_prod, Cardinal.mk_nat, Cardinal.lift_id, Cardinal.lift_id]
    calc (ℵ₁ : Cardinal.{0}) ^ ℵ₀ = 𝔠 ^ ℵ₀ := by rw [hCH]
      _ = (2 ^ ℵ₀) ^ ℵ₀ := by rw [← Cardinal.two_power_aleph0]
      _ = 2 ^ (ℵ₀ * ℵ₀) := by rw [← Cardinal.power_mul]
      _ = 2 ^ ℵ₀ := by rw [Cardinal.aleph0_mul_aleph0]
      _ = 𝔠 := Cardinal.two_power_aleph0
      _ = ℵ₁ := hCH.symm
  have hprod2 : #((ℕ → I × ℕ) × ℕ) = ℵ₁ := by
    rw [Cardinal.mk_prod, hpow, Cardinal.mk_nat, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.mul_eq_left (Cardinal.aleph0_le_aleph 1) (Cardinal.aleph0_le_aleph 1)
      Cardinal.aleph0_ne_zero
  exact hle1.trans_eq hprod2

/-- Under CH, there is a cofinal enumeration enum : I → Option Cand. -/
lemma exists_cofinal_enum [Fact ((ℵ₁ : Cardinal.{0}) = 𝔠)] :
    ∃ enum : I → Option Cand, ∀ c : Cand, ∀ β : I, ∃ α : I, β < α ∧ enum α = some c := by
  have hopt : #(Option Cand) ≤ ℵ₁ := by
    rw [Cardinal.mk_option]
    calc #Cand + 1 ≤ ℵ₁ + 1 := add_le_add card_Cand_le le_rfl
      _ = ℵ₁ := Cardinal.add_one_eq (Cardinal.aleph0_le_aleph 1)
  have hprod : #(Option Cand × I) ≤ #I := by
    rw [Cardinal.mk_prod, card_I, Cardinal.lift_id, Cardinal.lift_id]
    calc #(Option Cand) * ℵ₁ ≤ ℵ₁ * ℵ₁ := mul_le_mul' hopt le_rfl
      _ = ℵ₁ := Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)
  haveI : Nonempty (Option Cand × I) := ⟨(none, Classical.choice nonempty_I)⟩
  obtain ⟨⟨emb, hemb⟩⟩ := (Cardinal.le_def (Option Cand × I) I).mp hprod
  let e : I → Option Cand × I := Function.invFun emb
  have he : Function.Surjective e := (Function.leftInverse_invFun hemb).surjective
  refine ⟨fun α => (e α).1, fun c β => ?_⟩
  by_contra hno
  push_neg at hno
  have hinj : Function.Injective (fun γ : I =>
      (⟨Classical.choose (he (some c, γ)), by
        have hspec := Classical.choose_spec (he (some c, γ))
        have h1 : (e (Classical.choose (he (some c, γ)))).1 = some c := congrArg Prod.fst hspec
        by_contra hlt
        push_neg at hlt
        exact hno _ hlt h1⟩ : {α : I // α ≤ β})) := by
    intro γ₁ γ₂ h
    have hα : Classical.choose (he (some c, γ₁)) = Classical.choose (he (some c, γ₂)) :=
      congrArg Subtype.val h
    have h1 := Classical.choose_spec (he (some c, γ₁))
    have h2 := Classical.choose_spec (he (some c, γ₂))
    rw [hα] at h1
    exact congrArg Prod.snd (h1.symm.trans h2)
  haveI : Countable {α : I // α ≤ β} := (countable_Iic β).to_subtype
  exact I_uncountable (Function.Injective.countable hinj)

/-- Stage invariants for a non-dependent family U : I × ℕ → ℕ → Set (I × ℕ) on Y_{<α}. -/
structure GoodBelow (α : I) (U : I × ℕ → ℕ → Set (I × ℕ)) : Prop where
  anti : ∀ p, p.1 < α → Antitone (U p)
  mem : ∀ p, p.1 < α → ∀ k, p ∈ U p k
  bound : ∀ p, p.1 < α → ∀ k q, q ∈ U p k →
    q.1 ≤ p.1 ∧ q.2 ≤ p.2 ∧ (q.1 = p.1 → q = p)
  open_u : ∀ p, p.1 < α → ∀ k q, q ∈ U p k → ∃ r, U q r ⊆ U p k
  closed_u : ∀ p, p.1 < α → ∀ k q, q.1 < α → q ∉ U p k → ∃ r, Disjoint (U q r) (U p k)
  compact_u : ∀ p, p.1 < α → ∀ k (ι : Type) (O : ι → Set (I × ℕ)),
    (∀ i x, x ∈ O i → x.1 < α → ∃ r, U x r ⊆ O i) →
    U p k ⊆ ⋃ i, O i →
    ∃ F : Finset ι, U p k ⊆ ⋃ i ∈ F, O i

/-- Selection lemma: in Y_{<α}, any infinite closed discrete subset A ⊆ Y_{<α}
    admits a pairwise disjoint, locally finite sequence of basic clopen neighborhoods U(x_i, k_i). -/
lemma exists_lf_seq {α : I} {U : I × ℕ → ℕ → Set (I × ℕ)}
    (hG : GoodBelow α U) {A : Set (I × ℕ)}
    (hA_inf : A.Infinite) (hA_lt : ∀ x ∈ A, x.1 < α)
    (hA_disc : ∀ q, q.1 < α → ∃ r, (U q r ∩ A).Subsingleton) :
    ∃ (x : ℕ → I × ℕ) (k : ℕ → ℕ),
      (∀ i, x i ∈ A) ∧
      (∀ i j, i < j → Disjoint (U (x i) (k i)) (U (x j) (k j))) ∧
      (∀ q, q.1 < α → ∃ r N, ∀ i ≥ N, Disjoint (U q r) (U (x i) (k i))) := by
  classical
  have hY_count : ({q : I × ℕ | q.1 < α}).Countable := by
    have heq : {q : I × ℕ | q.1 < α} = {β : I | β < α} ×ˢ (Set.univ : Set ℕ) := by
      ext q; simp
    rw [heq]
    exact (countable_Iio α).prod Set.countable_univ
  obtain ⟨a₀, ha₀⟩ := hA_inf.nonempty
  have hY_ne : ({q : I × ℕ | q.1 < α}).Nonempty := ⟨a₀, hA_lt a₀ ha₀⟩
  obtain ⟨e, he⟩ := (Set.countable_iff_exists_surjective hY_ne).mp hY_count
  let rW : ℕ → ℕ := fun j => Classical.choose (hA_disc (e j).1 (e j).2)
  let W : ℕ → Set (I × ℕ) := fun j => U (e j).1 (rW j)
  have hW_sub : ∀ j, (W j ∩ A).Subsingleton :=
    fun j => Classical.choose_spec (hA_disc (e j).1 (e j).2)
  -- Helper: any basic neighborhood U p k (p.1 < α) meets A in a finite set
  have hU_inter_fin : ∀ p, p.1 < α → ∀ k, (U p k ∩ A).Finite := by
    intro p hp k
    let O : {q : I × ℕ // q.1 < α} → Set (I × ℕ) :=
      fun q => U q.1 (Classical.choose (hA_disc q.1 q.2))
    have hO_open : ∀ q x, x ∈ O q → x.1 < α → ∃ r, U x r ⊆ O q := by
      intro q x hx _
      exact hG.open_u q.1 q.2 _ x hx
    have hcov : U p k ⊆ ⋃ q, O q := by
      intro x hx
      have hx_lt : x.1 < α := lt_of_le_of_lt (hG.bound p hp k x hx).1 hp
      exact Set.mem_iUnion.mpr ⟨⟨x, hx_lt⟩, hG.mem x hx_lt _⟩
    obtain ⟨F, hF⟩ := hG.compact_u p hp k _ O hO_open hcov
    have hsub : U p k ∩ A ⊆ ⋃ q ∈ F, (O q ∩ A) := by
      intro x ⟨hxU, hxA⟩
      obtain ⟨q, hqF, hxq⟩ := Set.mem_iUnion₂.mp (hF hxU)
      exact Set.mem_iUnion₂.mpr ⟨q, hqF, hxq, hxA⟩
    refine (Set.Finite.biUnion F.finite_toSet fun q _ => ?_).subset hsub
    exact (Classical.choose_spec (hA_disc q.1 q.2)).finite
  -- One step: given a finite list of already-chosen pairs (y, k) with y ∈ A and a count m,
  -- pick a fresh (x, k) with x ∈ A and U x k disjoint from all W j (j < m) and all U y r in prev.
  have hstep : ∀ (m : ℕ) (prev : List ((I × ℕ) × ℕ)),
      (∀ p ∈ prev, p.1 ∈ A) →
      ∃ p : (I × ℕ) × ℕ, p.1 ∈ A ∧
        (∀ j < m, Disjoint (U p.1 p.2) (W j)) ∧
        (∀ q ∈ prev, Disjoint (U p.1 p.2) (U q.1 q.2)) := by
    intro m prev hprev
    let Z : Set (I × ℕ) :=
      (⋃ j ∈ Finset.range m, W j) ∪ (⋃ q ∈ prev.toFinset, U q.1 q.2)
    have hZA_fin : (Z ∩ A).Finite := by
      have h1 : ((⋃ j ∈ Finset.range m, W j) ∩ A).Finite := by
        rw [Set.iUnion₂_inter]
        exact Set.Finite.biUnion (Finset.range m).finite_toSet fun j _ => (hW_sub j).finite
      have h2 : ((⋃ q ∈ prev.toFinset, U q.1 q.2) ∩ A).Finite := by
        rw [Set.iUnion₂_inter]
        refine Set.Finite.biUnion prev.toFinset.finite_toSet fun q hq => ?_
        have hqA : q.1 ∈ A := hprev q (List.mem_toFinset.mp hq)
        exact hU_inter_fin q.1 (hA_lt q.1 hqA) q.2
      rw [Set.union_inter_distrib_right]
      exact h1.union h2
    have hdiff_ne : (A \ (Z ∩ A)).Nonempty := (hA_inf.diff hZA_fin).nonempty
    obtain ⟨x, hxA, hxnot⟩ := hdiff_ne
    have hxZ : x ∉ Z := fun h => hxnot ⟨h, hxA⟩
    have hx_lt : x.1 < α := hA_lt x hxA
    have hdisjW : ∀ j ∈ Finset.range m, ∃ r, Disjoint (U x r) (W j) := by
      intro j hj
      have hnot : x ∉ W j := fun h => hxZ (Or.inl (Set.mem_iUnion₂.mpr ⟨j, hj, h⟩))
      exact hG.closed_u (e j).1 (e j).2 (rW j) x hx_lt hnot
    have hdisjP : ∀ q ∈ prev.toFinset, ∃ r, Disjoint (U x r) (U q.1 q.2) := by
      intro q hq
      have hnot : x ∉ U q.1 q.2 := fun h => hxZ (Or.inr (Set.mem_iUnion₂.mpr ⟨q, hq, h⟩))
      have hqA : q.1 ∈ A := hprev q (List.mem_toFinset.mp hq)
      exact hG.closed_u q.1 (hA_lt q.1 hqA) q.2 x hx_lt hnot
    let k1 : ℕ := (Finset.range m).sup (fun j => if h : j ∈ Finset.range m then Classical.choose (hdisjW j h) else 0)
    let k2 : ℕ := prev.toFinset.sup (fun q => if h : q ∈ prev.toFinset then Classical.choose (hdisjP q h) else 0)
    let k := max k1 k2
    refine ⟨(x, k), hxA, ?_, ?_⟩
    · intro j hj
      have hj' : j ∈ Finset.range m := Finset.mem_range.mpr hj
      have hle : Classical.choose (hdisjW j hj') ≤ k := by
        have h1 : (if h : j ∈ Finset.range m then Classical.choose (hdisjW j h) else 0) ≤ k1 :=
          Finset.le_sup (f := fun j => if h : j ∈ Finset.range m then Classical.choose (hdisjW j h) else 0) hj'
        simp only [hj', ↓reduceDIte] at h1
        exact le_trans h1 (le_max_left _ _)
      exact (Classical.choose_spec (hdisjW j hj')).mono_left (hG.anti x hx_lt hle)
    · intro q hq
      have hq' : q ∈ prev.toFinset := List.mem_toFinset.mpr hq
      have hle : Classical.choose (hdisjP q hq') ≤ k := by
        have h1 : (if h : q ∈ prev.toFinset then Classical.choose (hdisjP q h) else 0) ≤ k2 :=
          Finset.le_sup (f := fun q => if h : q ∈ prev.toFinset then Classical.choose (hdisjP q h) else 0) hq'
        simp only [hq', ↓reduceDIte] at h1
        exact le_trans h1 (le_max_right _ _)
      exact (Classical.choose_spec (hdisjP q hq')).mono_left (hG.anti x hx_lt hle)
  -- Build the sequence of length n by plain recursion on ℕ
  let stepFn : ℕ → List ((I × ℕ) × ℕ) → List ((I × ℕ) × ℕ) := fun m l =>
    if h : ∀ p ∈ l, p.1 ∈ A then l ++ [Classical.choose (hstep m l h)] else l
  let buildL : ℕ → List ((I × ℕ) × ℕ) := Nat.rec [] stepFn
  have hbuild_prop : ∀ n : ℕ,
      (buildL n).length = n ∧
      (∀ p ∈ buildL n, p.1 ∈ A) ∧
      (∀ (i : ℕ) (hi : i < (buildL n).length) (j : ℕ) (hj : j < i),
        Disjoint (U ((buildL n)[i].1) ((buildL n)[i].2)) (W j) ∧
        Disjoint (U ((buildL n)[i].1) ((buildL n)[i].2))
          (U ((buildL n)[j]'(lt_trans hj hi)).1 ((buildL n)[j]'(lt_trans hj hi)).2)) := by
    intro n
    induction n with
    | zero =>
      exact ⟨rfl, fun _ h => by simp [buildL] at h, fun _ hi => by simp [buildL] at hi⟩
    | succ m ih =>
      obtain ⟨hlen, hmem, hdisj⟩ := ih
      have heq : buildL (m + 1) = buildL m ++ [Classical.choose (hstep m (buildL m) hmem)] := by
        change stepFn m (buildL m) = _
        dsimp only [stepFn]
        rw [dif_pos hmem]
      have hnxt := Classical.choose_spec (hstep m (buildL m) hmem)
      rw [heq]
      refine ⟨by simp [hlen], ?_, ?_⟩
      · intro p hp
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact hmem p hp
        · exact hnxt.1
      · intro i hi j hj
        have hlen' : (buildL m ++ [Classical.choose (hstep m (buildL m) hmem)]).length = m + 1 := by
          simp [hlen]
        by_cases him : i < m
        · have hi_l : i < (buildL m).length := by omega
          have hj_l : j < (buildL m).length := by omega
          have h1 : (buildL m ++ [Classical.choose (hstep m (buildL m) hmem)])[i] = (buildL m)[i] :=
            List.getElem_append_left hi_l
          have h2 : (buildL m ++ [Classical.choose (hstep m (buildL m) hmem)])[j]'(lt_trans hj hi) =
              (buildL m)[j] := List.getElem_append_left hj_l
          rw [h1, h2]
          exact hdisj i hi_l j hj
        · have hi_eq : i = m := by omega
          have hj_l : j < (buildL m).length := by omega
          have h1 : (buildL m ++ [Classical.choose (hstep m (buildL m) hmem)])[i] =
              Classical.choose (hstep m (buildL m) hmem) := by
            rw [List.getElem_append_right (by omega)]
            simp [hlen, hi_eq]
          have h2 : (buildL m ++ [Classical.choose (hstep m (buildL m) hmem)])[j]'(lt_trans hj hi) =
              (buildL m)[j] := List.getElem_append_left hj_l
          rw [h1, h2]
          exact ⟨hnxt.2.1 j (by omega), hnxt.2.2 (buildL m)[j] (List.getElem_mem hj_l)⟩
  have hbuild_ext : ∀ n (i : ℕ) (hi : i < n),
      (buildL (n + 1))[i]'(by have := (hbuild_prop (n + 1)).1; omega) =
      (buildL n)[i]'(by have := (hbuild_prop n).1; omega) := by
    intro n i hi
    have hmem := (hbuild_prop n).2.1
    have hlen := (hbuild_prop n).1
    have heq : buildL (n + 1) = buildL n ++ [Classical.choose (hstep n (buildL n) hmem)] := by
      change stepFn n (buildL n) = _
      dsimp only [stepFn]
      rw [dif_pos hmem]
    simp only [heq]
    exact List.getElem_append_left (by omega : i < (buildL n).length)
  have hbuild_eq : ∀ n m (hnm : n ≤ m) (i : ℕ) (hi : i < n),
      (buildL m)[i]'(by have := (hbuild_prop m).1; omega) =
      (buildL n)[i]'(by have := (hbuild_prop n).1; omega) := by
    intro n m hnm i hi
    induction hnm with
    | refl => rfl
    | @step k hnk ih =>
      rw [hbuild_ext k i (lt_of_lt_of_le hi hnk), ih]
  let seq : ℕ → (I × ℕ) × ℕ := fun i =>
    (buildL (i + 1))[i]'(by have := (hbuild_prop (i + 1)).1; omega)
  refine ⟨fun i => (seq i).1, fun i => (seq i).2, ?_, ?_, ?_⟩
  · intro i
    exact (hbuild_prop (i + 1)).2.1 _ (List.getElem_mem _)
  · intro i j hij
    have hprop := (hbuild_prop (j + 1)).2.2 j (by have := (hbuild_prop (j + 1)).1; omega) i hij
    have hjeq : (buildL (j + 1))[j]'(by have := (hbuild_prop (j + 1)).1; omega) = seq j := rfl
    have hieq : (buildL (j + 1))[i]'(by have := (hbuild_prop (j + 1)).1; omega) = seq i :=
      hbuild_eq (i + 1) (j + 1) (by omega) i (by omega)
    rw [hjeq, hieq] at hprop
    exact hprop.2.symm
  · intro q hq
    obtain ⟨j, hj⟩ := he ⟨q, hq⟩
    refine ⟨rW j, j + 1, fun i hi => ?_⟩
    have hprop := (hbuild_prop (i + 1)).2.2 i (by have := (hbuild_prop (i + 1)).1; omega) j (by omega)
    have hieq : (buildL (i + 1))[i]'(by have := (hbuild_prop (i + 1)).1; omega) = seq i := rfl
    rw [hieq] at hprop
    have hW : W j = U q (rW j) := by
      dsimp only [W]
      rw [hj]
    rw [← hW]
    exact hprop.1.symm

/-- Extend a partial family defined on β < α to a total function. -/
def extPrev (α : I) (prev : ∀ β : I, β < α → ℕ → ℕ → Set (I × ℕ)) :
    I × ℕ → ℕ → Set (I × ℕ) :=
  fun p k => if h : p.1 < α then prev p.1 h p.2 k else ∅

open Classical in
/-- One step of the transfinite recursion defining U_raw α m k. -/
noncomputable def U_step (enum : I → Option Cand) (α : I)
    (prev : ∀ β : I, β < α → ℕ → ℕ → Set (I × ℕ)) (m k : ℕ) : Set (I × ℕ) :=
  match enum α with
  | none => {(α, m)}
  | some c =>
    if h : GoodBelow α (extPrev α prev) ∧ (∀ x ∈ c.1.1, x.1 < α) ∧
        (∀ q, q.1 < α → ∃ r, (extPrev α prev q r ∩ c.1.1).Subsingleton) then
      if m = c.1.2 + 1 then
        insert (α, m) (⋃ i ≥ k, extPrev α prev
          (Classical.choose (exists_lf_seq h.1 c.2.2.1 h.2.1 h.2.2) i)
          (Classical.choose (Classical.choose_spec (exists_lf_seq h.1 c.2.2.1 h.2.1 h.2.2)) i))
      else
        {(α, m)}
    else
      {(α, m)}

/-- The global neighborhood basis family U_raw : I → ℕ → ℕ → Set (I × ℕ). -/
noncomputable def U_raw (enum : I → Option Cand) : I → ℕ → ℕ → Set (I × ℕ) :=
  WellFounded.fix wellFounded_lt (U_step enum)

noncomputable def U_fam (enum : I → Option Cand) (p : I × ℕ) (k : ℕ) : Set (I × ℕ) :=
  U_raw enum p.1 p.2 k

/-- Invariants holding on Y_{≤α} = {p : I × ℕ | p.1 ≤ α}. -/
structure GoodLe (α : I) (U : I × ℕ → ℕ → Set (I × ℕ)) : Prop where
  anti : ∀ p, p.1 ≤ α → Antitone (U p)
  mem : ∀ p, p.1 ≤ α → ∀ k, p ∈ U p k
  bound : ∀ p, p.1 ≤ α → ∀ k q, q ∈ U p k →
    q.1 ≤ p.1 ∧ q.2 ≤ p.2 ∧ (q.1 = p.1 → q = p)
  open_u : ∀ p, p.1 ≤ α → ∀ k q, q ∈ U p k → ∃ r, U q r ⊆ U p k
  closed_u : ∀ p, p.1 ≤ α → ∀ k q, q.1 ≤ α → q ∉ U p k → ∃ r, Disjoint (U q r) (U p k)
  compact_u : ∀ p, p.1 ≤ α → ∀ k (ι : Type) (O : ι → Set (I × ℕ)),
    (∀ i x, x ∈ O i → x.1 ≤ α → ∃ r, U x r ⊆ O i) →
    U p k ⊆ ⋃ i, O i →
    ∃ F : Finset ι, U p k ⊆ ⋃ i ∈ F, O i

lemma goodBelow_of_forall_lt {α : I} {U : I × ℕ → ℕ → Set (I × ℕ)}
    (h : ∀ β < α, GoodLe β U) : GoodBelow α U where
  anti p hp := (h p.1 hp).anti p le_rfl
  mem p hp := (h p.1 hp).mem p le_rfl
  bound p hp := (h p.1 hp).bound p le_rfl
  open_u p hp := (h p.1 hp).open_u p le_rfl
  closed_u p hp k q hq := (h (max p.1 q.1) (max_lt hp hq)).closed_u p (le_max_left _ _) k q (le_max_right _ _)
  compact_u p hp k ι O hO hcov :=
    (h p.1 hp).compact_u p le_rfl k ι O (fun i x hx hxle => hO i x hx (lt_of_le_of_lt hxle hp)) hcov

/-- Helper: GoodBelow α is preserved when replacing U by a function agreeing on p.1 < α. -/
lemma goodBelow_congr {α : I} {U₁ U₂ : I × ℕ → ℕ → Set (I × ℕ)}
    (heq : ∀ p, p.1 < α → ∀ k, U₁ p k = U₂ p k) (hG : GoodBelow α U₁) : GoodBelow α U₂ where
  anti p hp := by
    intro a b hab
    rw [← heq p hp a, ← heq p hp b]
    exact hG.anti p hp hab
  mem p hp k := by
    rw [← heq p hp k]
    exact hG.mem p hp k
  bound p hp k q hq := by
    rw [← heq p hp k] at hq
    exact hG.bound p hp k q hq
  open_u p hp k q hq := by
    rw [← heq p hp k] at hq
    have hq_lt : q.1 < α := lt_of_le_of_lt (hG.bound p hp k q hq).1 hp
    obtain ⟨r, hr⟩ := hG.open_u p hp k q hq
    exact ⟨r, by rw [← heq q hq_lt r, ← heq p hp k]; exact hr⟩
  closed_u p hp k q hq hnot := by
    rw [← heq p hp k] at hnot
    obtain ⟨r, hr⟩ := hG.closed_u p hp k q hq hnot
    exact ⟨r, by rw [← heq q hq r, ← heq p hp k]; exact hr⟩
  compact_u p hp k ι O hO hcov := by
    rw [← heq p hp k] at hcov ⊢
    exact hG.compact_u p hp k ι O (fun i x hx hxl => by
      obtain ⟨r, hr⟩ := hO i x hx hxl
      exact ⟨r, by rw [heq x hxl r]; exact hr⟩) hcov

/-- Main inductive theorem: U_fam satisfies GoodLe α for every α : I. -/
lemma goodLe_U_fam (enum : I → Option Cand) (α : I) : GoodLe α (U_fam enum) := by
  classical
  refine wellFounded_lt.induction (C := fun α => GoodLe α (U_fam enum)) α fun α ih => ?_
  have hGB : GoodBelow α (U_fam enum) := goodBelow_of_forall_lt ih
  let Up := extPrev α (fun β _ => U_raw enum β)
  have hUp_eq : ∀ p, p.1 < α → ∀ k, Up p k = U_fam enum p k := by
    intro p hp k
    simp [Up, extPrev, hp, U_fam]
  have hGB_Up : GoodBelow α Up :=
    goodBelow_congr (fun p hp k => (hUp_eq p hp k).symm) hGB
  -- Characterize U_fam enum (α, m) k: either singleton or {p} ∪ ⋃_{i ≥ k} U_fam (xs i) (ks i)
  have hα_cases : ∀ m : ℕ,
      (∀ k, U_fam enum (α, m) k = {(α, m)}) ∨
      ∃ (xs : ℕ → I × ℕ) (ks : ℕ → ℕ),
        (∀ i, (xs i).1 < α ∧ (xs i).2 < m) ∧
        (∀ i j, i < j → Disjoint (U_fam enum (xs i) (ks i)) (U_fam enum (xs j) (ks j))) ∧
        (∀ q, q.1 < α → ∃ r N, ∀ i ≥ N, Disjoint (U_fam enum q r) (U_fam enum (xs i) (ks i))) ∧
        (∀ k, U_fam enum (α, m) k = insert (α, m) (⋃ i ≥ k, U_fam enum (xs i) (ks i))) := by
    intro m
    have hfix : ∀ k, U_fam enum (α, m) k = U_step enum α (fun β _ => U_raw enum β) m k := by
      intro k
      change U_raw enum α m k = _
      rw [U_raw, WellFounded.fix_eq]
    cases henum : enum α with
    | none =>
      left; intro k; rw [hfix k, U_step, henum]
    | some c =>
      by_cases hcond : GoodBelow α (extPrev α (fun β _ => U_raw enum β)) ∧
          (∀ x ∈ c.1.1, x.1 < α) ∧
          (∀ q, q.1 < α → ∃ r, (extPrev α (fun β _ => U_raw enum β) q r ∩ c.1.1).Subsingleton)
      · by_cases hm : m = c.1.2 + 1
        · right
          let hex := exists_lf_seq hcond.1 c.2.2.1 hcond.2.1 hcond.2.2
          let xs := Classical.choose hex
          let ks := Classical.choose (Classical.choose_spec hex)
          have hspec := Classical.choose_spec (Classical.choose_spec hex)
          refine ⟨xs, ks, ?_, ?_, ?_, ?_⟩
          · intro i
            have hiA : xs i ∈ c.1.1 := hspec.1 i
            have hi2 : (xs i).2 ≤ c.1.2 := c.2.2.2 _ hiA
            exact ⟨hcond.2.1 _ hiA, by omega⟩
          · intro i j hij
            have hlt_i : (xs i).1 < α := hcond.2.1 _ (hspec.1 i)
            have hlt_j : (xs j).1 < α := hcond.2.1 _ (hspec.1 j)
            rw [← hUp_eq _ hlt_i, ← hUp_eq _ hlt_j]
            exact hspec.2.1 i j hij
          · intro q hq
            obtain ⟨r, N, hN⟩ := hspec.2.2 q hq
            refine ⟨r, N, fun i hi => ?_⟩
            have hlt_i : (xs i).1 < α := hcond.2.1 _ (hspec.1 i)
            rw [← hUp_eq q hq, ← hUp_eq _ hlt_i]
            exact hN i hi
          · intro k
            rw [hfix k, U_step, henum]; dsimp only; rw [dif_pos hcond, if_pos hm]
            congr 1
            ext z
            simp only [Set.mem_iUnion]
            constructor
            · rintro ⟨i, hi, hz⟩
              have hlt_i : (xs i).1 < α := hcond.2.1 _ (hspec.1 i)
              have hz' : z ∈ Up (xs i) (ks i) := hz
              rw [hUp_eq _ hlt_i] at hz'
              exact ⟨i, hi, hz'⟩
            · rintro ⟨i, hi, hz⟩
              have hlt_i : (xs i).1 < α := hcond.2.1 _ (hspec.1 i)
              rw [← hUp_eq _ hlt_i] at hz
              exact ⟨i, hi, hz⟩
        · left; intro k; rw [hfix k, U_step, henum]; dsimp only; rw [dif_pos hcond, if_neg hm]
      · left; intro k; rw [hfix k, U_step, henum]; dsimp only; rw [dif_neg hcond]
  -- Now prove the 6 fields of GoodLe α (U_fam enum)
  have h_anti : ∀ p, p.1 ≤ α → Antitone (U_fam enum p) := by
    intro p hp a b hab
    rcases lt_or_eq_of_le hp with hlt | heq
    · exact hGB.anti p hlt hab
    · rcases p with ⟨p1, p2⟩
      dsimp only at heq; subst p1
      rcases hα_cases p2 with hsing | ⟨xs, ks, _, _, _, hform⟩
      · rw [hsing a, hsing b]
      · rw [hform a, hform b]
        intro z hz
        rcases hz with rfl | hz
        · exact Or.inl rfl
        · right
          obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp hz
          exact Set.mem_iUnion₂.mpr ⟨i, le_trans hab hi, hzi⟩
  have h_mem : ∀ p, p.1 ≤ α → ∀ k, p ∈ U_fam enum p k := by
    intro p hp k
    rcases lt_or_eq_of_le hp with hlt | heq
    · exact hGB.mem p hlt k
    · rcases p with ⟨p1, p2⟩
      dsimp only at heq; subst p1
      rcases hα_cases p2 with hsing | ⟨xs, ks, _, _, _, hform⟩
      · rw [hsing k]; exact Set.mem_singleton _
      · rw [hform k]; exact Set.mem_insert _ _
  have h_bound : ∀ p, p.1 ≤ α → ∀ k q, q ∈ U_fam enum p k →
      q.1 ≤ p.1 ∧ q.2 ≤ p.2 ∧ (q.1 = p.1 → q = p) := by
    intro p hp k q hq
    rcases lt_or_eq_of_le hp with hlt | heq
    · exact hGB.bound p hlt k q hq
    · rcases p with ⟨p1, p2⟩
      dsimp only at heq; subst p1
      rcases hα_cases p2 with hsing | ⟨xs, ks, hxs, _, _, hform⟩
      · rw [hsing k] at hq; rw [Set.mem_singleton_iff.mp hq]; exact ⟨le_rfl, le_rfl, fun _ => rfl⟩
      · rw [hform k] at hq
        rcases hq with rfl | hq
        · exact ⟨le_rfl, le_rfl, fun _ => rfl⟩
        · obtain ⟨i, _, hqi⟩ := Set.mem_iUnion₂.mp hq
          have hb := hGB.bound (xs i) (hxs i).1 (ks i) q hqi
          have hlt1 : q.1 < α := lt_of_le_of_lt hb.1 (hxs i).1
          exact ⟨le_of_lt hlt1, le_trans hb.2.1 (le_of_lt (hxs i).2), fun h => absurd h (ne_of_lt hlt1)⟩
  have h_open : ∀ p, p.1 ≤ α → ∀ k q, q ∈ U_fam enum p k → ∃ r, U_fam enum q r ⊆ U_fam enum p k := by
    intro p hp k q hq
    rcases lt_or_eq_of_le hp with hlt | heq
    · exact hGB.open_u p hlt k q hq
    · rcases p with ⟨p1, p2⟩
      dsimp only at heq; subst p1
      rcases hα_cases p2 with hsing | ⟨xs, ks, hxs, _, _, hform⟩
      · rw [hsing k] at hq; rw [Set.mem_singleton_iff.mp hq]; exact ⟨k, subset_rfl⟩
      · rw [hform k] at hq
        rcases hq with rfl | hq
        · exact ⟨k, subset_rfl⟩
        · obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.mp hq
          obtain ⟨r, hr⟩ := hGB.open_u (xs i) (hxs i).1 (ks i) q hqi
          refine ⟨r, hr.trans ?_⟩
          rw [hform k]
          intro z hz
          exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, hi, hz⟩)
  have h_closed : ∀ p, p.1 ≤ α → ∀ k q, q.1 ≤ α → q ∉ U_fam enum p k →
      ∃ r, Disjoint (U_fam enum q r) (U_fam enum p k) := by
    intro p hp k q hq hnot
    rcases lt_or_eq_of_le hp with hplt | hpeq
    · rcases lt_or_eq_of_le hq with hqlt | hqeq
      · exact hGB.closed_u p hplt k q hqlt hnot
      · -- p.1 < α = q.1
        rcases q with ⟨q1, q2⟩
        dsimp only at hqeq; subst q1
        rcases hα_cases q2 with hsing | ⟨xs, ks, hxs, _, hlf, hform⟩
        · refine ⟨0, ?_⟩
          rw [hsing 0, Set.disjoint_singleton_left]
          exact hnot
        · -- Compactness of U_fam p k inside Y_{<α} + local finiteness of xs
          let O : {z : I × ℕ // z.1 < α} → Set (I × ℕ) :=
            fun z => U_fam enum z.1 (Classical.choose (hlf z.1 z.2))
          have hO_open : ∀ z x, x ∈ O z → x.1 < α → ∃ r, U_fam enum x r ⊆ O z :=
            fun z x hx _ => hGB.open_u z.1 z.2 _ x hx
          have hcov : U_fam enum p k ⊆ ⋃ z, O z := by
            intro x hx
            have hx_lt : x.1 < α := lt_of_le_of_lt (hGB.bound p hplt k x hx).1 hplt
            exact Set.mem_iUnion.mpr ⟨⟨x, hx_lt⟩, hGB.mem x hx_lt _⟩
          obtain ⟨F, hF⟩ := hGB.compact_u p hplt k _ O hO_open hcov
          let M : ℕ := F.sup (fun z => Classical.choose (Classical.choose_spec (hlf z.1 z.2)))
          refine ⟨M, ?_⟩
          rw [hform M, Set.disjoint_insert_left]
          refine ⟨hnot, ?_⟩
          rw [Set.disjoint_iUnion₂_left]
          intro i hi
          rw [Set.disjoint_left]
          intro x hxi hxp
          obtain ⟨z, hzF, hxz⟩ := Set.mem_iUnion₂.mp (hF hxp)
          have hMz : Classical.choose (Classical.choose_spec (hlf z.1 z.2)) ≤ M :=
            Finset.le_sup (f := fun z : {z : I × ℕ // z.1 < α} =>
              Classical.choose (Classical.choose_spec (hlf z.1 z.2))) hzF
          have hdisj := Classical.choose_spec (Classical.choose_spec (hlf z.1 z.2)) i (le_trans hMz hi)
          exact Set.disjoint_left.mp hdisj hxz hxi
    · -- p.1 = α
      rcases p with ⟨p1, p2⟩
      dsimp only at hpeq; subst p1
      rcases lt_or_eq_of_le hq with hqlt | hqeq
      · -- q.1 < α = p.1
        rcases hα_cases p2 with hsing | ⟨xs, ks, hxs, _, hlf, hform⟩
        · refine ⟨0, ?_⟩
          rw [hsing k, Set.disjoint_singleton_right]
          intro hmem
          have hb := hGB.bound q hqlt 0 (α, p2) hmem
          exact not_le_of_gt hqlt hb.1
        · obtain ⟨r₀, N, hN⟩ := hlf q hqlt
          let F : Finset ℕ := (Finset.range N).filter (fun i => k ≤ i)
          have hfinF : ∀ i ∈ F, ∃ r, Disjoint (U_fam enum q r) (U_fam enum (xs i) (ks i)) := by
            intro i hi
            have hik : k ≤ i := (Finset.mem_filter.mp hi).2
            have hnoti : q ∉ U_fam enum (xs i) (ks i) := by
              intro hq_in
              apply hnot
              rw [hform k]
              exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, hik, hq_in⟩)
            exact hGB.closed_u (xs i) (hxs i).1 (ks i) q hqlt hnoti
          let r1 : ℕ := F.sup (fun i => if h : i ∈ F then Classical.choose (hfinF i h) else 0)
          let r := max r₀ r1
          refine ⟨r, ?_⟩
          rw [hform k, Set.disjoint_insert_right]
          refine ⟨?_, ?_⟩
          · intro hmem
            have hb := hGB.bound q hqlt r (α, p2) hmem
            exact not_le_of_gt hqlt hb.1
          · rw [Set.disjoint_iUnion₂_right]
            intro i hik
            by_cases hiN : N ≤ i
            · exact (hN i hiN).mono_left (hGB.anti q hqlt (le_max_left _ _))
            · have hiF : i ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_not_ge hiN), hik⟩
              have hle : Classical.choose (hfinF i hiF) ≤ r := by
                have h1 : (if h : i ∈ F then Classical.choose (hfinF i h) else 0) ≤ r1 :=
                  Finset.le_sup (f := fun i => if h : i ∈ F then Classical.choose (hfinF i h) else 0) hiF
                simp only [hiF, ↓reduceDIte] at h1
                exact le_trans h1 (le_max_right _ _)
              exact (Classical.choose_spec (hfinF i hiF)).mono_left (hGB.anti q hqlt hle)
      · -- q.1 = α = p.1, and q ≠ p (since q ∉ U p k and p ∈ U p k)
        rcases q with ⟨q1, q2⟩
        dsimp only at hqeq; subst q1
        have hqp : q2 ≠ p2 := by
          intro heq; subst heq; exact hnot (h_mem (α, q2) le_rfl k)
        rcases hα_cases p2 with hpsing | ⟨xsP, ksP, hxsP, _, _, hformP⟩
        · refine ⟨0, ?_⟩
          rw [hpsing k, Set.disjoint_singleton_right]
          intro hmem
          have hb := h_bound (α, q2) le_rfl 0 (α, p2) hmem
          exact hqp (congrArg Prod.snd (hb.2.2 rfl)).symm
        · -- In U_step, at most one m = c.1.2 + 1 is non-singleton; since q2 ≠ p2, q2 must be singleton!
          have hqsing : ∀ r, U_fam enum (α, q2) r = {(α, q2)} := by
            intro r
            have hfixP : U_fam enum (α, p2) k = U_step enum α (fun β _ => U_raw enum β) p2 k := by
              change U_raw enum α p2 k = _; rw [U_raw, WellFounded.fix_eq]
            have hfixQ : U_fam enum (α, q2) r = U_step enum α (fun β _ => U_raw enum β) q2 r := by
              change U_raw enum α q2 r = _; rw [U_raw, WellFounded.fix_eq]
            cases henum : enum α with
            | none => rw [hfixQ, U_step, henum]
            | some c =>
              by_cases hcond : GoodBelow α (extPrev α (fun β _ => U_raw enum β)) ∧
                  (∀ x ∈ c.1.1, x.1 < α) ∧
                  (∀ q, q.1 < α → ∃ r, (extPrev α (fun β _ => U_raw enum β) q r ∩ c.1.1).Subsingleton)
              · by_cases hp_eq : p2 = c.1.2 + 1
                · have hq_ne : q2 ≠ c.1.2 + 1 := by omega
                  rw [hfixQ, U_step, henum]; dsimp only; rw [dif_pos hcond, if_neg hq_ne]
                · exfalso
                  have hsingP : U_fam enum (α, p2) k = {(α, p2)} := by
                    rw [hfixP, U_step, henum]; dsimp only; rw [dif_pos hcond, if_neg hp_eq]
                  have hmem_xs : xsP k ∈ U_fam enum (α, p2) k := by
                    rw [hformP k]
                    exact Or.inr (Set.mem_iUnion₂.mpr ⟨k, le_rfl, hGB.mem (xsP k) (hxsP k).1 (ksP k)⟩)
                  rw [hsingP, Set.mem_singleton_iff] at hmem_xs
                  exact ne_of_lt (hxsP k).1 (congrArg Prod.fst hmem_xs)
              · rw [hfixQ, U_step, henum]; dsimp only; rw [dif_neg hcond]
          refine ⟨0, ?_⟩
          rw [hqsing 0, Set.disjoint_singleton_left]
          exact hnot
  have h_compact : ∀ p, p.1 ≤ α → ∀ k (ι : Type) (O : ι → Set (I × ℕ)),
      (∀ i x, x ∈ O i → x.1 ≤ α → ∃ r, U_fam enum x r ⊆ O i) →
      U_fam enum p k ⊆ ⋃ i, O i →
      ∃ F : Finset ι, U_fam enum p k ⊆ ⋃ i ∈ F, O i := by
    intro p hp k ι O hO hcov
    rcases lt_or_eq_of_le hp with hlt | heq
    · exact hGB.compact_u p hlt k ι O (fun i x hx hxl => hO i x hx (le_of_lt hxl)) hcov
    · rcases p with ⟨p1, p2⟩
      dsimp only at heq; subst p1
      rcases hα_cases p2 with hsing | ⟨xs, ks, hxs, _, _, hform⟩
      · obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp (hcov (h_mem (α, p2) le_rfl k))
        refine ⟨{i₀}, ?_⟩
        rw [hsing k]
        intro x hx
        rw [Set.mem_singleton_iff.mp hx]
        exact Set.mem_iUnion₂.mpr ⟨i₀, Finset.mem_singleton_self i₀, hi₀⟩
      · obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp (hcov (h_mem (α, p2) le_rfl k))
        obtain ⟨m, hm⟩ := hO i₀ (α, p2) hi₀ le_rfl
        -- Cover each U_fam (xs j) (ks j) for k ≤ j < m using hGB.compact_u
        have hfin_j : ∀ j ∈ Finset.Ico k m,
            ∃ Fj : Finset ι, U_fam enum (xs j) (ks j) ⊆ ⋃ i ∈ Fj, O i := by
          intro j hj
          have hsub : U_fam enum (xs j) (ks j) ⊆ ⋃ i, O i := by
            refine Set.Subset.trans ?_ hcov
            rw [hform k]
            intro z hz
            exact Or.inr (Set.mem_iUnion₂.mpr ⟨j, (Finset.mem_Ico.mp hj).1, hz⟩)
          exact hGB.compact_u (xs j) (hxs j).1 (ks j) ι O
            (fun i x hx hxl => hO i x hx (le_of_lt hxl)) hsub
        let F : Finset ι := insert i₀ ((Finset.Ico k m).biUnion
          (fun j => if h : j ∈ Finset.Ico k m then Classical.choose (hfin_j j h) else ∅))
        refine ⟨F, ?_⟩
        intro z hz
        rw [hform k] at hz
        rcases hz with rfl | hz
        · exact Set.mem_iUnion₂.mpr ⟨i₀, Finset.mem_insert_self _ _, hi₀⟩
        · obtain ⟨j, hjk, hzj⟩ := Set.mem_iUnion₂.mp hz
          by_cases hjm : m ≤ j
          · refine Set.mem_iUnion₂.mpr ⟨i₀, Finset.mem_insert_self _ _, hm ?_⟩
            rw [hform m]
            exact Or.inr (Set.mem_iUnion₂.mpr ⟨j, hjm, hzj⟩)
          · have hjI : j ∈ Finset.Ico k m := Finset.mem_Ico.mpr ⟨hjk, lt_of_not_ge hjm⟩
            have hspec := Classical.choose_spec (hfin_j j hjI) hzj
            obtain ⟨i, hiFj, hzi⟩ := Set.mem_iUnion₂.mp hspec
            refine Set.mem_iUnion₂.mpr ⟨i, Finset.mem_insert_of_mem ?_, hzi⟩
            exact Finset.mem_biUnion.mpr ⟨j, hjI, by simp [hjI, hiFj]⟩
  exact ⟨h_anti, h_mem, h_bound, h_open, h_closed, h_compact⟩

/-- Countability of every basic neighborhood U_fam enum p k. -/
lemma countable_U_fam (enum : I → Option Cand) (p : I × ℕ) (k : ℕ) :
    (U_fam enum p k).Countable := by
  have hsub : U_fam enum p k ⊆ {β : I | β ≤ p.1} ×ˢ (Set.univ : Set ℕ) := by
    intro q hq
    exact ⟨(goodLe_U_fam enum p.1).bound p le_rfl k q hq |>.1, trivial⟩
  exact ((countable_Iic p.1).prod Set.countable_univ).mono hsub

/-- The topology on Y = I × ℕ generated by U_fam enum. -/
def topY (enum : I → Option Cand) : TopologicalSpace (I × ℕ) where
  IsOpen O := ∀ p ∈ O, ∃ k, U_fam enum p k ⊆ O
  isOpen_univ := fun p _ => ⟨0, Set.subset_univ _⟩
  isOpen_inter O₁ O₂ h₁ h₂ := fun p ⟨hp₁, hp₂⟩ => by
    obtain ⟨k₁, hk₁⟩ := h₁ p hp₁
    obtain ⟨k₂, hk₂⟩ := h₂ p hp₂
    refine ⟨max k₁ k₂, fun q hq => ⟨hk₁ ?_, hk₂ ?_⟩⟩
    · exact (goodLe_U_fam enum p.1).anti p le_rfl (le_max_left _ _) hq
    · exact (goodLe_U_fam enum p.1).anti p le_rfl (le_max_right _ _) hq
  isOpen_sUnion S hS := fun p hp => by
    obtain ⟨O, hOS, hpO⟩ := Set.mem_sUnion.mp hp
    obtain ⟨k, hk⟩ := hS O hOS p hpO
    exact ⟨k, hk.trans (Set.subset_sUnion_of_mem hOS)⟩

lemma isOpen_U_fam (enum : I → Option Cand) (p : I × ℕ) (k : ℕ) :
    @IsOpen (I × ℕ) (topY enum) (U_fam enum p k) :=
  fun q hq => (goodLe_U_fam enum p.1).open_u p le_rfl k q hq

lemma isClosed_U_fam (enum : I → Option Cand) (p : I × ℕ) (k : ℕ) :
    @IsClosed (I × ℕ) (topY enum) (U_fam enum p k) := by
  letI := topY enum
  rw [← isOpen_compl_iff]
  intro q hq
  obtain ⟨r, hr⟩ := (goodLe_U_fam enum (max p.1 q.1)).closed_u p (le_max_left _ _) k q
    (le_max_right _ _) hq
  exact ⟨r, Set.subset_compl_iff_disjoint_right.mpr hr⟩

lemma isCompact_U_fam (enum : I → Option Cand) (p : I × ℕ) (k : ℕ) :
    @IsCompact (I × ℕ) (topY enum) (U_fam enum p k) := by
  letI := topY enum
  rw [isCompact_iff_finite_subcover]
  intro ι O hO hcov
  -- Reindex the cover by Set (I × ℕ) (which is Type 0) to apply GoodLe.compact_u
  let S : Set (Set (I × ℕ)) := Set.range O
  have hS_open : ∀ s : {s : Set (I × ℕ) // s ∈ S}, ∀ x ∈ s.1, x.1 ≤ p.1 →
      ∃ r, U_fam enum x r ⊆ s.1 := by
    rintro ⟨_, ⟨i, rfl⟩⟩ x hx _
    exact hO i x hx
  have hS_cov : U_fam enum p k ⊆ ⋃ s : {s : Set (I × ℕ) // s ∈ S}, s.1 := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact Set.mem_iUnion.mpr ⟨⟨O i, ⟨i, rfl⟩⟩, hi⟩
  obtain ⟨F, hF⟩ := (goodLe_U_fam enum p.1).compact_u p le_rfl k {s : Set (I × ℕ) // s ∈ S}
    (fun s => s.1) hS_open hS_cov
  classical
  let pick : {s : Set (I × ℕ) // s ∈ S} → ι := fun s => Classical.choose s.2
  refine ⟨F.image pick, fun x hx => ?_⟩
  obtain ⟨s, hsF, hxs⟩ := Set.mem_iUnion₂.mp (hF hx)
  refine Set.mem_iUnion₂.mpr ⟨pick s, Finset.mem_image_of_mem pick hsF, ?_⟩
  have hspec : O (pick s) = s.1 := Classical.choose_spec s.2
  rwa [hspec]

lemma t2_topY (enum : I → Option Cand) : @T2Space (I × ℕ) (topY enum) := by
  letI := topY enum
  refine ⟨fun p q hpq => ?_⟩
  have hnot : q ∉ U_fam enum p 0 ∨ p ∉ U_fam enum q 0 := by
    by_cases hle : p.1 ≤ q.1
    · left
      intro hmem
      have hb := (goodLe_U_fam enum p.1).bound p le_rfl 0 q hmem
      exact hpq (hb.2.2 (le_antisymm hb.1 hle)).symm
    · right
      intro hmem
      have hb := (goodLe_U_fam enum q.1).bound q le_rfl 0 p hmem
      exact hpq (hb.2.2 (le_antisymm hb.1 (le_of_not_ge hle)))
  rcases hnot with hq | hp
  · exact ⟨U_fam enum p 0, (U_fam enum p 0)ᶜ, isOpen_U_fam enum p 0,
      (isClosed_U_fam enum p 0).isOpen_compl, (goodLe_U_fam enum p.1).mem p le_rfl 0, hq,
      disjoint_compl_right⟩
  · exact ⟨(U_fam enum q 0)ᶜ, U_fam enum q 0, (isClosed_U_fam enum q 0).isOpen_compl,
      isOpen_U_fam enum q 0, hp, (goodLe_U_fam enum q.1).mem q le_rfl 0, disjoint_compl_left⟩

/-- Level sets F_n = {p : I × ℕ | p.2 ≤ n}. -/
def Fset (n : ℕ) : Set (I × ℕ) := {p : I × ℕ | p.2 ≤ n}

lemma isOpen_Fset (enum : I → Option Cand) (n : ℕ) :
    @IsOpen (I × ℕ) (topY enum) (Fset n) := by
  intro p hp
  refine ⟨0, fun q hq => ?_⟩
  exact le_trans ((goodLe_U_fam enum p.1).bound p le_rfl 0 q hq).2.1 hp

/-- Every compact set in Y is countable (since every point has a countable open neighborhood). -/
lemma countable_of_isCompact_Y (enum : I → Option Cand) {K : Set (I × ℕ)}
    (hK : @IsCompact (I × ℕ) (topY enum) K) : K.Countable := by
  letI := topY enum
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun p : I × ℕ => U_fam enum p 0)
    (fun p => isOpen_U_fam enum p 0)
    (fun p _ => Set.mem_iUnion.mpr ⟨p, (goodLe_U_fam enum p.1).mem p le_rfl 0⟩)
  exact (F.finite_toSet.countable.biUnion fun p _ => countable_U_fam enum p 0).mono hF

/-- Key Yakovlev property: every closed subset K ⊆ F_n of Y is compact! -/
lemma isCompact_of_isClosed_subset_Fset (enum : I → Option Cand)
    (hcof : ∀ c : Cand, ∀ β : I, ∃ α : I, β < α ∧ enum α = some c) :
    ∀ n : ℕ, ∀ K : Set (I × ℕ), @IsClosed (I × ℕ) (topY enum) K → K ⊆ Fset n →
      @IsCompact (I × ℕ) (topY enum) K := by
  classical
  letI := topY enum
  -- Helper: any closed subset D ⊆ {p | p.2 = n} is finite!
  have hslice_fin : ∀ n (D : Set (I × ℕ)), IsClosed D → (∀ p ∈ D, p.2 = n) → D.Finite := by
    intro n D hD hDn
    by_contra hinf
    have hD_inf : D.Infinite := hinf
    obtain ⟨A, hAD, hA_count, hA_inf⟩ := hD_inf.exists_subset_countable_infinite
    let c : Cand := ⟨(A, n), hA_count, hA_inf, fun x hx => le_of_eq (hDn x (hAD hx))⟩
    obtain ⟨β, hβ⟩ := exists_gt_of_countable (Prod.fst '' A) (hA_count.image Prod.fst)
    obtain ⟨α, hβα, hα_enum⟩ := hcof c β
    have hA_lt : ∀ x ∈ A, x.1 < α := fun x hx => lt_trans (hβ x.1 ⟨x, hx, rfl⟩) hβα
    -- A is closed discrete in Y_{<α} because D is closed in Y and every p ∈ D has U p 0 ∩ D = {p}
    let Up := extPrev α (fun γ _ => U_raw enum γ)
    have hUp_eq : ∀ p, p.1 < α → ∀ k, Up p k = U_fam enum p k := fun p hp k => by
      simp [Up, extPrev, hp, U_fam]
    have hGB_Up : GoodBelow α Up :=
      goodBelow_congr (fun p hp k => (hUp_eq p hp k).symm)
        (goodBelow_of_forall_lt (fun γ _ => goodLe_U_fam enum γ))
    have hA_disc : ∀ q, q.1 < α → ∃ r, (Up q r ∩ A).Subsingleton := by
      intro q hq
      by_cases hqD : q ∈ D
      · refine ⟨0, fun x hx y hy => ?_⟩
        rw [hUp_eq q hq 0] at hx hy
        -- Both x, y ∈ U q 0 ∩ D. Since q.2 = n and x.2 = n, could x ≠ q?
        -- WAIT: check if U q 0 ∩ {p | p.2 = n} = {q}!
        -- At step q.1, if q is non-isolated, xs i has (xs i).2 < q.2 = n, so U (xs i) (ks i) ⊆ F_{n-1}!
        -- Thus U q 0 ∩ {p | p.2 = n} = {q}!!
        have hq_only : ∀ z ∈ U_fam enum q 0, z.2 = q.2 → z = q := by
          intro z hz hz2
          rcases lt_or_eq_of_le ((goodLe_U_fam enum q.1).bound q le_rfl 0 z hz).1 with hzlt | hzeq
          · -- z.1 < q.1 implies q was non-singleton at q.1, hence z.2 < q.2!
            exfalso
            have hfix : U_fam enum q 0 = U_step enum q.1 (fun γ _ => U_raw enum γ) q.2 0 := by
              change U_raw enum q.1 q.2 0 = _; rw [U_raw, WellFounded.fix_eq]
            rw [hfix, U_step] at hz
            cases he : enum q.1 with
            | none =>
              rw [he] at hz
              exact ne_of_lt hzlt (congrArg Prod.fst (Set.mem_singleton_iff.mp hz))
            | some c' =>
              rw [he] at hz
              dsimp only at hz
              by_cases hc' : GoodBelow q.1 (extPrev q.1 (fun γ _ => U_raw enum γ)) ∧
                  (∀ w ∈ c'.1.1, w.1 < q.1) ∧
                  (∀ w, w.1 < q.1 → ∃ r, (extPrev q.1 (fun γ _ => U_raw enum γ) w r ∩ c'.1.1).Subsingleton)
              · rw [dif_pos hc'] at hz
                by_cases hmq : q.2 = c'.1.2 + 1
                · rw [if_pos hmq] at hz
                  rcases hz with rfl | hz
                  · exact lt_irrefl _ hzlt
                  · obtain ⟨i, _, hzi⟩ := Set.mem_iUnion₂.mp hz
                    have hspec := Classical.choose_spec (Classical.choose_spec
                      (exists_lf_seq hc'.1 c'.2.2.1 hc'.2.1 hc'.2.2))
                    have hxiA := hspec.1 i
                    have hxilt : (Classical.choose (exists_lf_seq hc'.1 c'.2.2.1 hc'.2.1 hc'.2.2) i).1 < q.1 :=
                      hc'.2.1 _ hxiA
                    have hxi2 : (Classical.choose (exists_lf_seq hc'.1 c'.2.2.1 hc'.2.1 hc'.2.2) i).2 ≤ c'.1.2 :=
                      c'.2.2.2 _ hxiA
                    have hzb := hc'.1.bound _ hxilt _ z hzi
                    omega
                · rw [if_neg hmq] at hz
                  exact ne_of_lt hzlt (congrArg Prod.fst (Set.mem_singleton_iff.mp hz))
              · rw [dif_neg hc'] at hz
                exact ne_of_lt hzlt (congrArg Prod.fst (Set.mem_singleton_iff.mp hz))
          · exact (goodLe_U_fam enum q.1).bound q le_rfl 0 z hz |>.2.2 hzeq
        have hx_eq : x = q := hq_only x hx.1 ((hDn x (hAD hx.2)).trans (hDn q hqD).symm)
        have hy_eq : y = q := hq_only y hy.1 ((hDn y (hAD hy.2)).trans (hDn q hqD).symm)
        exact hx_eq.trans hy_eq.symm
      · -- q ∉ D, and D is closed, so ∃ r, U q r ⊆ Dᶜ, hence U q r ∩ A = ∅
        obtain ⟨r, hr⟩ := hD.isOpen_compl q hqD
        refine ⟨r, fun x hx y _ => ?_⟩
        rw [hUp_eq q hq r] at hx
        exact absurd (hAD hx.2) (hr hx.1)
    -- Therefore at stage α, (α, n + 1) is a limit point of A ⊆ D!
    have hcond : GoodBelow α Up ∧ (∀ x ∈ c.1.1, x.1 < α) ∧
        (∀ q, q.1 < α → ∃ r, (Up q r ∩ c.1.1).Subsingleton) :=
      ⟨hGB_Up, hA_lt, hA_disc⟩
    have hnotD : (α, n + 1) ∉ D := fun h => by have := hDn _ h; omega
    obtain ⟨k, hk⟩ := hD.isOpen_compl (α, n + 1) hnotD
    have hfix : U_fam enum (α, n + 1) k = U_step enum α (fun β _ => U_raw enum β) (n + 1) k := by
      change U_raw enum α (n + 1) k = _; rw [U_raw, WellFounded.fix_eq]
    have hfix' : U_fam enum (α, n + 1) k =
        insert (α, n + 1) (⋃ i ≥ k, Up (Classical.choose (exists_lf_seq hcond.1 c.2.2.1 hcond.2.1 hcond.2.2) i)
          (Classical.choose (Classical.choose_spec (exists_lf_seq hcond.1 c.2.2.1 hcond.2.1 hcond.2.2)) i)) := by
      rw [hfix, U_step, hα_enum]; dsimp only; rw [dif_pos hcond, if_pos rfl]
    let hex := exists_lf_seq hcond.1 c.2.2.1 hcond.2.1 hcond.2.2
    let xs := Classical.choose hex
    let ks := Classical.choose (Classical.choose_spec hex)
    have hspec := Classical.choose_spec (Classical.choose_spec hex)
    have hxk_in_A : xs k ∈ A := hspec.1 k
    have hxk_in_U : xs k ∈ U_fam enum (α, n + 1) k := by
      rw [hfix']
      right
      exact Set.mem_iUnion₂.mpr ⟨k, le_rfl, hGB_Up.mem (xs k) (hA_lt _ hxk_in_A) (ks k)⟩
    exact hk hxk_in_U (hAD hxk_in_A)
  -- Now prove compactness of closed K ⊆ F_n by induction on n!
  intro n
  induction n with
  | zero =>
    intro K hK hKF
    have hfin : K.Finite := hslice_fin 0 K hK (fun p hp => Nat.le_zero.mp (hKF hp))
    exact hfin.isCompact
  | succ m ih =>
    intro K hK hKF
    let D := K \ Fset m
    have hD_closed : IsClosed D := hK.sdiff (isOpen_Fset enum m)
    have hD_lvl : ∀ p ∈ D, p.2 = m + 1 := by
      intro p ⟨hpK, hpnot⟩
      have hle : p.2 ≤ m + 1 := hKF hpK
      have hgt : ¬ p.2 ≤ m := hpnot
      omega
    have hD_fin : D.Finite := hslice_fin (m + 1) D hD_closed hD_lvl
    let W : Set (I × ℕ) := ⋃ p ∈ D, U_fam enum p 0
    have hW_open : IsOpen W := isOpen_biUnion fun p _ => isOpen_U_fam enum p 0
    have hW_compact : IsCompact W := hD_fin.isCompact_biUnion fun p _ => isCompact_U_fam enum p 0
    let K' := K \ W
    have hK'_closed : IsClosed K' := hK.sdiff hW_open
    have hK'_sub : K' ⊆ Fset m := by
      intro p ⟨hpK, hpnotW⟩
      by_contra hnotFm
      have hpD : p ∈ D := ⟨hpK, hnotFm⟩
      exact hpnotW (Set.mem_biUnion hpD ((goodLe_U_fam enum p.1).mem p le_rfl 0))
    have hK'_compact : IsCompact K' := ih K' hK'_closed hK'_sub
    have hKW_compact : IsCompact (K ∩ W) := hW_compact.inter_left hK
    have hK_eq : K = K' ∪ (K ∩ W) := by
      ext p; simp only [K', Set.mem_union, Set.mem_diff, Set.mem_inter_iff]; tauto
    rw [hK_eq]
    exact hK'_compact.union hKW_compact

/-- One-point compactification topology on X = Option (I × ℕ). -/
def topX (enum : I → Option Cand) : TopologicalSpace (Option (I × ℕ)) where
  IsOpen O :=
    @IsOpen (I × ℕ) (topY enum) (Option.some ⁻¹' O) ∧
    (none ∈ O → @IsCompact (I × ℕ) (topY enum) (Option.some ⁻¹' O)ᶜ)
  isOpen_univ := by
    letI := topY enum
    exact ⟨isOpen_univ, fun _ => by simp⟩
  isOpen_inter O₁ O₂ h₁ h₂ := by
    letI := topY enum
    refine ⟨h₁.1.inter h₂.1, fun ⟨h1, h2⟩ => ?_⟩
    rw [Set.preimage_inter, Set.compl_inter]
    exact (h₁.2 h1).union (h₂.2 h2)
  isOpen_sUnion S hS := by
    letI := topY enum
    refine ⟨?_, ?_⟩
    · rw [Set.preimage_sUnion]
      exact isOpen_biUnion fun O hO => (hS O hO).1
    · intro hnone
      obtain ⟨O₀, hO₀S, hnone₀⟩ := Set.mem_sUnion.mp hnone
      have hsub : (Option.some ⁻¹' ⋃₀ S)ᶜ ⊆ (Option.some ⁻¹' O₀)ᶜ :=
        Set.compl_subset_compl.mpr (Set.preimage_mono (Set.subset_sUnion_of_mem hO₀S))
      have hclosed : IsClosed (Option.some ⁻¹' ⋃₀ S)ᶜ := by
        rw [isClosed_compl_iff, Set.preimage_sUnion]
        exact isOpen_biUnion fun O hO => (hS O hO).1
      exact (hS O₀ hO₀S).2 hnone₀ |>.of_isClosed_subset hclosed hsub

lemma compactSpace_topX (enum : I → Option Cand) :
    @CompactSpace (Option (I × ℕ)) (topX enum) := by
  letI := topX enum
  refine ⟨isCompact_iff_finite_subcover.mpr ?_⟩
  intro ι O hO hcov
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ none))
  let K : Set (I × ℕ) := (Option.some ⁻¹' O i₀)ᶜ
  letI : TopologicalSpace (I × ℕ) := topY enum
  have hK : IsCompact K := (hO i₀).2 hi₀
  have hcovK : K ⊆ ⋃ i, Option.some ⁻¹' O i := by
    intro y _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ (some y)))
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun i => Option.some ⁻¹' O i) (fun i => (hO i).1) hcovK
  classical
  refine ⟨insert i₀ F, fun x _ => ?_⟩
  cases x with
  | none => exact Set.mem_iUnion₂.mpr ⟨i₀, Finset.mem_insert_self _ _, hi₀⟩
  | some y =>
    by_cases hy : some y ∈ O i₀
    · exact Set.mem_iUnion₂.mpr ⟨i₀, Finset.mem_insert_self _ _, hy⟩
    · obtain ⟨i, hiF, hyi⟩ := Set.mem_iUnion₂.mp (hF hy)
      exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_insert_of_mem hiF, hyi⟩

lemma t2Space_topX (enum : I → Option Cand) :
    @T2Space (Option (I × ℕ)) (topX enum) := by
  letI := topX enum
  refine ⟨fun x y hxy => ?_⟩
  cases x with
  | some p =>
    cases y with
    | some q =>
      have hpq : p ≠ q := fun h => hxy (congrArg some h)
      obtain ⟨U, V, hU, hV, hpU, hqV, hdisj⟩ := (t2_topY enum).t2 hpq
      refine ⟨Option.some '' U, Option.some '' V, ?_, ?_, ⟨p, hpU, rfl⟩, ⟨q, hqV, rfl⟩, ?_⟩
      · refine ⟨by simpa [Set.preimage_image_eq _ (Option.some_injective _)] using hU,
          fun ⟨_, _, h⟩ => nomatch h⟩
      · refine ⟨by simpa [Set.preimage_image_eq _ (Option.some_injective _)] using hV,
          fun ⟨_, _, h⟩ => nomatch h⟩
      · rw [Set.disjoint_image_iff (Option.some_injective _)]; exact hdisj
    | none =>
      let U := U_fam enum p 0
      refine ⟨Option.some '' U, (Option.some '' U)ᶜ, ?_, ?_,
        ⟨p, (goodLe_U_fam enum p.1).mem p le_rfl 0, rfl⟩, ?_, disjoint_compl_right⟩
      · refine ⟨by simpa [Set.preimage_image_eq _ (Option.some_injective _)] using isOpen_U_fam enum p 0,
          fun ⟨_, _, h⟩ => nomatch h⟩
      · have hpre : Option.some ⁻¹' (Option.some '' U)ᶜ = Uᶜ := by
          ext z; simp [Set.mem_image]
        refine ⟨by rw [hpre]; exact (isClosed_U_fam enum p 0).isOpen_compl, fun _ => ?_⟩
        rw [hpre, compl_compl]
        exact isCompact_U_fam enum p 0
      · rintro ⟨_, _, h⟩; exact nomatch h
  | none =>
    cases y with
    | none => exact absurd rfl hxy
    | some q =>
      let U := U_fam enum q 0
      refine ⟨(Option.some '' U)ᶜ, Option.some '' U, ?_, ?_, ?_,
        ⟨q, (goodLe_U_fam enum q.1).mem q le_rfl 0, rfl⟩, disjoint_compl_left⟩
      · have hpre : Option.some ⁻¹' (Option.some '' U)ᶜ = Uᶜ := by
          ext z; simp [Set.mem_image]
        refine ⟨by rw [hpre]; exact (isClosed_U_fam enum q 0).isOpen_compl, fun _ => ?_⟩
        rw [hpre, compl_compl]
        exact isCompact_U_fam enum q 0
      · refine ⟨by simpa [Set.preimage_image_eq _ (Option.some_injective _)] using isOpen_U_fam enum q 0,
          fun ⟨_, _, h⟩ => nomatch h⟩
      · rintro ⟨_, _, h⟩; exact nomatch h

lemma weaklyFirstCountable_topX (enum : I → Option Cand)
    (hcof : ∀ c : Cand, ∀ β : I, ∃ α : I, β < α ∧ enum α = some c) :
    @WeaklyFirstCountable.WeaklyFirstCountableTopology (Option (I × ℕ)) (topX enum) := by
  letI := topX enum
  refine ⟨⟨fun x k => match x with
    | some p => Option.some '' U_fam enum p k
    | none => insert none (Option.some '' (Fset k)ᶜ), ?_, ?_⟩⟩
  · intro x
    cases x with
    | some p =>
      refine ⟨fun a b hab => Set.image_mono ((goodLe_U_fam enum p.1).anti p le_rfl hab),
        fun k => ⟨p, (goodLe_U_fam enum p.1).mem p le_rfl k, rfl⟩⟩
    | none =>
      refine ⟨fun a b hab => Set.insert_subset_insert (Set.image_mono (Set.compl_subset_compl.mpr
        (fun p hp => le_trans hp hab))), fun k => Set.mem_insert _ _⟩
  · intro O
    constructor
    · intro hO x hx
      cases x with
      | some p =>
        obtain ⟨k, hk⟩ := hO.1 p hx
        refine ⟨k, ?_⟩
        rintro _ ⟨q, hq, rfl⟩
        exact hk hq
      | none =>
        letI : TopologicalSpace (I × ℕ) := topY enum
        have hK : IsCompact (Option.some ⁻¹' O)ᶜ := hO.2 hx
        have hcov : (Option.some ⁻¹' O)ᶜ ⊆ ⋃ n : ℕ, Fset n := fun p _ =>
          Set.mem_iUnion.mpr ⟨p.2, (le_rfl : p.2 ≤ p.2)⟩
        obtain ⟨F, hF⟩ := hK.elim_finite_subcover Fset (isOpen_Fset enum) hcov
        let N : ℕ := F.sup id
        refine ⟨N, ?_⟩
        rintro z (rfl | ⟨p, hp, rfl⟩)
        · exact hx
        · by_contra hnotO
          obtain ⟨n, hnF, hpn⟩ := Set.mem_iUnion₂.mp (hF hnotO)
          have hle : n ≤ N := Finset.le_sup (f := id) hnF
          exact hp (le_trans hpn hle)
    · intro h
      refine ⟨fun p hp => ?_, fun hnone => ?_⟩
      · obtain ⟨k, hk⟩ := h (some p) hp
        exact ⟨k, fun q hq => hk ⟨q, hq, rfl⟩⟩
      · obtain ⟨N, hN⟩ := h none hnone
        have hY_open : @IsOpen (I × ℕ) (topY enum) (Option.some ⁻¹' O) := fun p hp => by
          obtain ⟨k, hk⟩ := h (some p) hp
          exact ⟨k, fun q hq => hk ⟨q, hq, rfl⟩⟩
        have hK_closed : @IsClosed (I × ℕ) (topY enum) (Option.some ⁻¹' O)ᶜ :=
          (@isClosed_compl_iff _ (topY enum) _).mpr hY_open
        have hK_sub : (Option.some ⁻¹' O)ᶜ ⊆ Fset N := by
          intro p hp
          by_contra hnotF
          exact hp (hN (Or.inr ⟨p, hnotF, rfl⟩))
        exact isCompact_of_isClosed_subset_Fset enum hcof N _ hK_closed hK_sub

lemma not_firstCountable_topX (enum : I → Option Cand) :
    ¬ @FirstCountableTopology (Option (I × ℕ)) (topX enum) := by
  letI := topX enum
  intro hfc
  obtain ⟨B, hB⟩ := Filter.isCountablyGenerated_iff_exists_antitone_basis.mp
    (hfc.nhds_generated_countable (none : Option (I × ℕ)))
  -- For each n, B n ∈ 𝓝 none, so there is an open O_n ⊆ B n with none ∈ O_n
  have hO_ex : ∀ n, ∃ O : Set (Option (I × ℕ)), O ⊆ B n ∧ IsOpen O ∧ none ∈ O :=
    fun n => mem_nhds_iff.mp (hB.mem n)
  let O : ℕ → Set (Option (I × ℕ)) := fun n => Classical.choose (hO_ex n)
  have hO_spec : ∀ n, O n ⊆ B n ∧ IsOpen (O n) ∧ none ∈ O n :=
    fun n => Classical.choose_spec (hO_ex n)
  have hK_count : ∀ n, (Option.some ⁻¹' O n)ᶜ.Countable :=
    fun n => countable_of_isCompact_Y enum ((hO_spec n).2.1.2 (hO_spec n).2.2)
  have hunion_count : (⋃ n, (Option.some ⁻¹' O n)ᶜ).Countable :=
    Set.countable_iUnion hK_count
  -- Since I × ℕ is uncountable, pick p ∉ ⋃ n, (some ⁻¹' O n)ᶜ
  have hex_p : ∃ p : I × ℕ, p ∉ ⋃ n, (Option.some ⁻¹' O n)ᶜ := by
    by_contra hno
    push_neg at hno
    have huniv : (Set.univ : Set (I × ℕ)).Countable := hunion_count.mono (fun p _ => hno p)
    have hIc : (Set.univ : Set I).Countable := by
      have heq : (Set.univ : Set I) = Prod.fst '' (Set.univ : Set (I × ℕ)) := by
        ext α; simp
      rw [heq]
      exact huniv.image Prod.fst
    exact I_uncountable (Set.countable_univ_iff.mp hIc)
  obtain ⟨p, hp⟩ := hex_p
  -- {some p}ᶜ is an open neighborhood of none
  have hopen_p : IsOpen ({some p}ᶜ : Set (Option (I × ℕ))) := by
    letI : TopologicalSpace (I × ℕ) := topY enum
    haveI : T2Space (I × ℕ) := t2_topY enum
    have hpre : Option.some ⁻¹' ({some p}ᶜ : Set (Option (I × ℕ))) = {p}ᶜ := by
      ext z; simp
    refine ⟨?_, ?_⟩
    · rw [hpre]
      exact isClosed_singleton.isOpen_compl
    · intro _
      rw [hpre, compl_compl]
      exact isCompact_singleton
  have hnhds : ({some p}ᶜ : Set (Option (I × ℕ))) ∈ 𝓝 none :=
    hopen_p.mem_nhds (by simp)
  obtain ⟨n, hn⟩ := hB.mem_iff.mp hnhds
  have hp_in_O : some p ∈ O n := by
    by_contra hnot
    exact hp (Set.mem_iUnion.mpr ⟨n, hnot⟩)
  exact hn ((hO_spec n).1 hp_in_O) rfl

end YakovlevCH

open YakovlevCH

theorem OMA.solution : type_of% @WeaklyFirstCountable.CH.existsWeaklyFirstCountableCompactNotFirstCountable := by
  intro hCH
  have hCH0 : (ℵ₁ : Cardinal.{0}) = 𝔠 := by
    have h1 := hCH.out
    have h2 : Cardinal.lift (ℵ₁ : Cardinal.{0}) = Cardinal.lift (𝔠 : Cardinal.{0}) := by
      simpa only [Cardinal.lift_aleph, Ordinal.lift_one, Cardinal.lift_continuum] using h1
    exact Cardinal.lift_inj.mp h2
  obtain ⟨enum, hcof⟩ := @exists_cofinal_enum ⟨hCH0⟩
  exact ⟨Option (I × ℕ), topX enum,
    weaklyFirstCountable_topX enum hcof,
    compactSpace_topX enum,
    t2Space_topX enum,
    not_firstCountable_topX enum⟩
