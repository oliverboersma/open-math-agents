import OMAStatements.S_oeis_a383307

-- Problem: A383307: a(n) is number of n-digit nonnegative integers whose difference between the largest and smallest digits is equal to the mode of it
-- Upstream: formal-conjectures statements/oeis-a383307.lean:0 (declaration OMA.S_oeis_a383307.main)
-- Credit: @nijv (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA_A383307

open OMA.S_oeis_a383307 Finset Filter

section DigitBijection

def digitsOf {m : ℕ} (a : Fin 9) (v : Fin m → Fin 10) : List ℕ :=
  (List.ofFn fun i => (v i).val).reverse ++ [a.val + 1]

def wordOf {m : ℕ} (a : Fin 9) (v : Fin m → Fin 10) : List ℕ :=
  (a.val + 1) :: List.ofFn fun i => (v i).val

def numOf {m : ℕ} (a : Fin 9) (v : Fin m → Fin 10) : ℕ :=
  Nat.ofDigits 10 (digitsOf a v)

lemma digitsOf_reverse {m : ℕ} (a : Fin 9) (v : Fin m → Fin 10) :
    (digitsOf a v).reverse = wordOf a v := by
  simp [digitsOf, wordOf]

lemma digitsOf_length {m : ℕ} (a : Fin 9) (v : Fin m → Fin 10) :
    (digitsOf a v).length = m + 1 := by
  simp [digitsOf]

lemma wordOf_length {m : ℕ} (a : Fin 9) (v : Fin m → Fin 10) :
    (wordOf a v).length = m + 1 := by
  simp [wordOf]

lemma digitsOf_lt_ten {m : ℕ} (a : Fin 9) (v : Fin m → Fin 10) :
    ∀ x ∈ digitsOf a v, x < 10 := by
  intro x hx
  simp [digitsOf, List.mem_ofFn] at hx
  rcases hx with ⟨i, rfl⟩ | rfl
  · exact (v i).isLt
  · omega

lemma digitsOf_getLast_ne_zero {m : ℕ} (a : Fin 9) (v : Fin m → Fin 10) :
    ∀ h : digitsOf a v ≠ [], (digitsOf a v).getLast h ≠ 0 := by
  intro h
  simp [digitsOf]

lemma digits_numOf {m : ℕ} (a : Fin 9) (v : Fin m → Fin 10) :
    Nat.digits 10 (numOf a v) = digitsOf a v :=
  Nat.digits_ofDigits 10 (by norm_num) (digitsOf a v)
    (digitsOf_lt_ten a v) (digitsOf_getLast_ne_zero a v)

lemma numOf_ne_zero {m : ℕ} (a : Fin 9) (v : Fin m → Fin 10) :
    numOf a v ≠ 0 := by
  intro h
  have hd := digits_numOf a v
  rw [h, Nat.digits_zero] at hd
  simp [digitsOf] at hd

lemma numOf_lt {m : ℕ} (a : Fin 9) (v : Fin m → Fin 10) :
    numOf a v < 10 ^ (m + 1) := by
  have h := Nat.ofDigits_lt_base_pow_length (b := 10) (by norm_num) (digitsOf_lt_ten a v)
  simpa [numOf, digitsOf_length] using h

lemma digitWord_numOf {m : ℕ} (a : Fin 9) (v : Fin m → Fin 10) :
    digitWord (numOf a v) = wordOf a v := by
  simp [digitWord, numOf_ne_zero, digits_numOf, digitsOf_reverse]

lemma numOf_inj {m : ℕ} :
    Function.Injective (fun p : Fin 9 × (Fin m → Fin 10) => numOf p.1 p.2) := by
  rintro ⟨a₁, v₁⟩ ⟨a₂, v₂⟩ h
  dsimp only at h
  have hw : wordOf a₁ v₁ = wordOf a₂ v₂ := by
    rw [← digitWord_numOf, ← digitWord_numOf, h]
  simp only [wordOf, List.cons.injEq] at hw
  rcases hw with ⟨ha, hv⟩
  have ha' : a₁ = a₂ := Fin.ext (by omega)
  have hv' : v₁ = v₂ := by
    funext i
    apply Fin.ext
    have hi : (List.ofFn fun j => (v₁ j).val)[i.val]'(by simp) =
        (List.ofFn fun j => (v₂ j).val)[i.val]'(by simp) := by
      simp [hv]
    simpa using hi
  exact Prod.ext ha' hv'

lemma exists_numOf_eq {m : ℕ} (hm : 1 ≤ m) {k : ℕ}
    (hlen : (digitWord k).length = m + 1) :
    ∃ a : Fin 9, ∃ v : Fin m → Fin 10, numOf a v = k := by
  have hk0 : k ≠ 0 := by
    intro h0
    subst h0
    simp [digitWord] at hlen
    omega
  have hdw : digitWord k = (Nat.digits 10 k).reverse := by
    simp [digitWord, hk0]
  rw [hdw] at hlen
  cases hw : (Nat.digits 10 k).reverse with
  | nil =>
    simp [hw] at hlen
  | cons h t =>
    have htlen : t.length = m := by
      simp [hw] at hlen
      omega
    have hdig : Nat.digits 10 k = t.reverse ++ [h] := by
      have := congr_arg List.reverse hw
      simpa using this
    have hmem_dig : ∀ x ∈ h :: t, x ∈ Nat.digits 10 k := by
      intro x hx
      rw [← List.mem_reverse, hw]
      exact hx
    have hh_lt : h < 10 :=
      Nat.digits_lt_base (by norm_num) (hmem_dig h (by simp))
    have hh_ne : h ≠ 0 := by
      have hne : Nat.digits 10 k ≠ [] := by
        rw [hdig]
        simp
      have hlast := Nat.getLast_digit_ne_zero 10 hk0
      have hget : (Nat.digits 10 k).getLast hne = h := by
        simp [hdig]
      rw [← hget]
      exact hlast
    let a : Fin 9 := ⟨h - 1, by omega⟩
    let v : Fin m → Fin 10 := fun i =>
      ⟨t[i.val]'(by omega),
        Nat.digits_lt_base (by norm_num)
          (hmem_dig _ (List.mem_cons_of_mem h (List.getElem_mem (by omega))))⟩
    refine ⟨a, v, ?_⟩
    have hofFn : (List.ofFn fun i => (v i).val) = t := by
      apply List.ext_getElem
      · simp [htlen]
      · intro i hi₁ hi₂
        simp [v]
    have hdigits_eq : digitsOf a v = Nat.digits 10 k := by
      simp [digitsOf, hofFn, a, hdig, Nat.sub_add_cancel (Nat.pos_of_ne_zero hh_ne)]
    rw [numOf, hdigits_eq, Nat.ofDigits_digits]

lemma term_succ_eq_sum {m : ℕ} (hm : 1 ≤ m) :
    term (m + 1) =
      ∑ a : Fin 9, (Finset.univ.filter fun v : Fin m → Fin 10 =>
        qualifies (wordOf a v) = true).card := by
  have hbij : term (m + 1) =
      (Finset.univ.filter fun p : Fin 9 × (Fin m → Fin 10) =>
        qualifies (wordOf p.1 p.2) = true).card := by
    symm
    refine Finset.card_bij (fun p _ => numOf p.1 p.2) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [Finset.mem_filter, Finset.mem_range, digitWord_numOf, wordOf_length, true_and]
      exact ⟨numOf_lt p.1 p.2, hp⟩
    · intro p₁ _ p₂ _ h
      exact numOf_inj h
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      rcases exists_numOf_eq hm hk.2.1 with ⟨a, v, rfl⟩
      refine ⟨(a, v), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [digitWord_numOf] using hk.2.2
  rw [hbij]
  simp only [Finset.card_filter]
  rw [Fintype.sum_prod_type]

end DigitBijection

section CountingStructure

open Classical

def cnt {m : ℕ} (v : Fin m → Fin 10) (d : Fin 10) : ℕ :=
  (Finset.univ.filter fun i : Fin m => v i = d).card

def StrictMode2 {m : ℕ} (v : Fin m → Fin 10) (d₀ : Fin 10) : Prop :=
  ∀ d : Fin 10, d ≠ d₀ → cnt v d + 2 ≤ cnt v d₀

def BadMissing {m : ℕ} (v : Fin m → Fin 10) : Prop :=
  cnt v 0 = 0 ∨ cnt v 9 = 0

def BadTie {m : ℕ} (v : Fin m → Fin 10) : Prop :=
  ¬ ∃ d₀ : Fin 10, StrictMode2 v d₀

lemma count_ofFn_val : ∀ {m : ℕ} (v : Fin m → Fin 10) (d : Fin 10),
    (List.ofFn fun i => (v i).val).count d.val = cnt v d
  | 0, v, d => by
    simp [cnt]
  | m + 1, v, d => by
    rw [List.ofFn_succ, List.count_cons, count_ofFn_val]
    simp only [cnt, Finset.card_filter, Fin.sum_univ_succ]
    have hbeq : ((v 0).val == d.val) = decide (v 0 = d) := by
      by_cases h : v 0 = d
      · simp [h]
      · have hval : (v 0).val ≠ d.val := fun hv => h (Fin.ext hv)
        simp [h, hval]
    rw [hbeq]
    by_cases h : v 0 = d <;> simp [h, Nat.add_comm]

lemma count_wordOf {m : ℕ} (a : Fin 9) (v : Fin m → Fin 10) (d : Fin 10) :
    (wordOf a v).count d.val = cnt v d + if a.val + 1 = d.val then 1 else 0 := by
  simp only [wordOf, List.count_cons, count_ofFn_val]
  by_cases h : a.val + 1 = d.val <;> simp [h]

lemma mem_wordOf_of_cnt_pos {m : ℕ} (a : Fin 9) (v : Fin m → Fin 10) {d : Fin 10}
    (hpos : 0 < cnt v d) : d.val ∈ wordOf a v := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [wordOf, List.mem_cons, List.mem_ofFn]
  right
  exact ⟨i, congr_arg Fin.val hi⟩

lemma wordOf_le_nine {m : ℕ} (a : Fin 9) (v : Fin m → Fin 10) :
    ∀ x ∈ wordOf a v, x ≤ 9 := by
  intro x hx
  simp only [wordOf, List.mem_cons, List.mem_ofFn] at hx
  rcases hx with rfl | ⟨i, rfl⟩
  · omega
  · have := (v i).isLt
    omega

lemma qualifies_wordOf_of_not_badMissing {m : ℕ} (a : Fin 9) (v : Fin m → Fin 10)
    (h : ¬ BadMissing v) :
    qualifies (wordOf a v) = uniqueMode (wordOf a v) 9 := by
  simp only [BadMissing, not_or] at h
  have h0mem : 0 ∈ wordOf a v := by
    simpa using mem_wordOf_of_cnt_pos a v (d := (0 : Fin 10)) (Nat.pos_of_ne_zero h.1)
  have h9mem : 9 ∈ wordOf a v := by
    simpa using mem_wordOf_of_cnt_pos a v (d := (9 : Fin 10)) (Nat.pos_of_ne_zero h.2)
  have hmax : (wordOf a v).max? = some 9 := by
    rw [List.max?_eq_some_iff]
    exact ⟨h9mem, wordOf_le_nine a v⟩
  have hmin : (wordOf a v).min? = some 0 := by
    rw [List.min?_eq_some_iff]
    exact ⟨h0mem, fun x _ => Nat.zero_le x⟩
  simp [qualifies, hmax, hmin]

lemma uniqueMode_nine_iff (w : List ℕ) :
    uniqueMode w 9 = true ↔ ∀ d : Fin 10, d ≠ 9 → w.count d.val < w.count 9 := by
  simp only [uniqueMode, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h d hd
    rcases h d.val d.isLt with heq | hlt
    · exfalso
      exact hd (Fin.ext heq)
    · exact hlt
  · intro h d hd
    by_cases h9 : d = 9
    · left; exact h9
    · right
      have hfin : (⟨d, hd⟩ : Fin 10) ≠ 9 := fun heq => h9 (congr_arg Fin.val heq)
      exact h ⟨d, hd⟩ hfin

lemma qualifies_of_strictMode2_nine {m : ℕ} (a : Fin 9) {v : Fin m → Fin 10}
    (hs : StrictMode2 v 9) (hm : ¬ BadMissing v) :
    qualifies (wordOf a v) = true := by
  rw [qualifies_wordOf_of_not_badMissing a v hm, uniqueMode_nine_iff]
  intro d hd
  have h1 := count_wordOf a v d
  have h2 := count_wordOf a v 9
  have h3 := hs d hd
  have h9val : ((9 : Fin 10).val) = 9 := rfl
  rw [h9val] at h2
  split_ifs at h1 h2 <;> omega

lemma strictMode2_nine_of_qualifies {m : ℕ} (a : Fin 9) {v : Fin m → Fin 10}
    (hq : qualifies (wordOf a v) = true) (hm : ¬ BadMissing v) (ht : ¬ BadTie v) :
    StrictMode2 v 9 := by
  rw [qualifies_wordOf_of_not_badMissing a v hm, uniqueMode_nine_iff] at hq
  simp only [BadTie, not_not] at ht
  obtain ⟨d₀, hd₀⟩ := ht
  by_cases h9 : d₀ = 9
  · subst h9; exact hd₀
  · exfalso
    have hlt := hq d₀ h9
    have h1 := count_wordOf a v d₀
    have h2 := count_wordOf a v 9
    have h3 := hd₀ 9 (Ne.symm h9)
    have h9val : ((9 : Fin 10).val) = 9 := rfl
    rw [h9val] at h2
    split_ifs at h1 h2 <;> omega

lemma card_strictMode_le_card_qualifies_add_missing {m : ℕ} (a : Fin 9) :
    (Finset.univ.filter fun v : Fin m → Fin 10 => StrictMode2 v 9).card ≤
      (Finset.univ.filter fun v : Fin m → Fin 10 => qualifies (wordOf a v) = true).card +
      (Finset.univ.filter fun v : Fin m → Fin 10 => BadMissing v).card := by
  calc
    (Finset.univ.filter fun v : Fin m → Fin 10 => StrictMode2 v 9).card
        ≤ ((Finset.univ.filter fun v : Fin m → Fin 10 => qualifies (wordOf a v) = true) ∪
            (Finset.univ.filter fun v : Fin m → Fin 10 => BadMissing v)).card := by
          apply Finset.card_le_card
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hm : BadMissing v
          · exact Or.inr hm
          · exact Or.inl (qualifies_of_strictMode2_nine a hv hm)
    _ ≤ _ := Finset.card_union_le _ _

lemma card_qualifies_le_card_strictMode_add_missing_add_tie {m : ℕ} (a : Fin 9) :
    (Finset.univ.filter fun v : Fin m → Fin 10 => qualifies (wordOf a v) = true).card ≤
      (Finset.univ.filter fun v : Fin m → Fin 10 => StrictMode2 v 9).card +
      (Finset.univ.filter fun v : Fin m → Fin 10 => BadMissing v).card +
      (Finset.univ.filter fun v : Fin m → Fin 10 => BadTie v).card := by
  calc
    (Finset.univ.filter fun v : Fin m → Fin 10 => qualifies (wordOf a v) = true).card
        ≤ (((Finset.univ.filter fun v : Fin m → Fin 10 => StrictMode2 v 9) ∪
            (Finset.univ.filter fun v : Fin m → Fin 10 => BadMissing v)) ∪
            (Finset.univ.filter fun v : Fin m → Fin 10 => BadTie v)).card := by
          apply Finset.card_le_card
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases ht : BadTie v
          · exact Or.inr ht
          · by_cases hm : BadMissing v
            · exact Or.inl (Or.inr hm)
            · exact Or.inl (Or.inl (strictMode2_nine_of_qualifies a hv hm ht))
    _ ≤ ((Finset.univ.filter fun v : Fin m → Fin 10 => StrictMode2 v 9) ∪
          (Finset.univ.filter fun v : Fin m → Fin 10 => BadMissing v)).card +
        (Finset.univ.filter fun v : Fin m → Fin 10 => BadTie v).card := Finset.card_union_le _ _
    _ ≤ _ := by
          have := Finset.card_union_le
            (Finset.univ.filter fun v : Fin m → Fin 10 => StrictMode2 v 9)
            (Finset.univ.filter fun v : Fin m → Fin 10 => BadMissing v)
          omega

lemma cnt_shift {m : ℕ} (v : Fin m → Fin 10) (c d : Fin 10) :
    cnt (fun i => v i + c) (d + c) = cnt v d := by
  simp only [cnt]
  congr 1
  ext i
  simp

lemma card_strictMode2_eq {m : ℕ} (d₀ : Fin 10) :
    (Finset.univ.filter fun v : Fin m → Fin 10 => StrictMode2 v d₀).card =
      (Finset.univ.filter fun v : Fin m → Fin 10 => StrictMode2 v 9).card := by
  let c : Fin 10 := 9 - d₀
  refine Finset.card_bij (fun v _ i => v i + c) ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    intro d hd
    have hd' : d - c ≠ d₀ := by
      intro heq
      apply hd
      calc
        d = (d - c) + c := (sub_add_cancel d c).symm
        _ = d₀ + c := by rw [heq]
        _ = 9 := by simp [c]
    have h1 : cnt (fun i => v i + c) d = cnt v (d - c) := by
      have := cnt_shift v c (d - c)
      simpa [sub_add_cancel] using this
    have h2 : cnt (fun i => v i + c) 9 = cnt v d₀ := by
      have := cnt_shift v c d₀
      simpa [c] using this
    rw [h1, h2]
    exact hv (d - c) hd'
  · intro v₁ _ v₂ _ h
    funext i
    have hi := congr_fun h i
    exact add_right_cancel hi
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    refine ⟨fun i => w i - c, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro d hd
      have hd' : d + c ≠ 9 := by
        intro heq
        apply hd
        have : d + (9 - d₀) = 9 := heq
        calc
          d = (d + (9 - d₀)) - (9 - d₀) := (add_sub_cancel_right d (9 - d₀)).symm
          _ = 9 - (9 - d₀) := by rw [this]
          _ = d₀ := by simp
      have h1 : cnt (fun i => w i - c) d = cnt w (d + c) := by
        have := cnt_shift (fun i => w i - c) c d
        simpa [sub_add_cancel] using this.symm
      have h2 : cnt (fun i => w i - c) d₀ = cnt w 9 := by
        have := cnt_shift (fun i => w i - c) c d₀
        simpa [c, sub_add_cancel] using this.symm
      rw [h1, h2]
      exact hw (d + c) hd'
    · funext i
      simp

lemma ten_mul_card_strictMode2_add_card_badTie (m : ℕ) :
    10 * (Finset.univ.filter fun v : Fin m → Fin 10 => StrictMode2 v 9).card +
      (Finset.univ.filter fun v : Fin m → Fin 10 => BadTie v).card = 10 ^ m := by
  let S : Fin 10 → Finset (Fin m → Fin 10) :=
    fun d₀ => Finset.univ.filter fun v => StrictMode2 v d₀
  let T : Finset (Fin m → Fin 10) := Finset.univ.filter fun v => BadTie v
  have hpw : Set.PairwiseDisjoint (Set.univ : Set (Fin 10)) S := by
    intro d₁ _ d₂ _ hne
    change Disjoint (S d₁) (S d₂)
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
    have h1 := hv₁ d₂ (Ne.symm hne)
    have h2 := hv₂ d₁ hne
    omega
  have hdisj : Disjoint (Finset.univ.biUnion S) T := by
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    simp only [S, T, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
    exact hv₂ hv₁
  have hunion : Finset.univ.biUnion S ∪ T = Finset.univ := by
    ext v
    simp only [S, T, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and, iff_true]
    exact Classical.em (∃ d₀ : Fin 10, StrictMode2 v d₀)
  have hcard : (Finset.univ.biUnion S).card + T.card = 10 ^ m := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hbi : (Finset.univ.biUnion S).card = 10 * (S 9).card := by
    rw [Finset.card_biUnion (by intro x _ y _ h; exact hpw (Set.mem_univ x) (Set.mem_univ y) h)]
    have hsum : ∑ d₀ : Fin 10, (S d₀).card = ∑ _d₀ : Fin 10, (S 9).card :=
      Finset.sum_congr rfl fun d₀ _ => card_strictMode2_eq d₀
    rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← hbi]
  exact hcard

lemma card_cnt_eq_zero_le (m : ℕ) (d₀ : Fin 10) :
    (Finset.univ.filter fun v : Fin m → Fin 10 => cnt v d₀ = 0).card ≤ 9 ^ m := by
  let S := Finset.univ.filter fun v : Fin m → Fin 10 => cnt v d₀ = 0
  have hne : ∃ c : Fin 10, c ≠ d₀ := by
    by_cases h : (0 : Fin 10) = d₀
    · exact ⟨1, by rw [← h]; decide⟩
    · exact ⟨0, h⟩
  obtain ⟨c₀, hc₀⟩ := hne
  let f : (Fin m → Fin 10) → (Fin m → {d : Fin 10 // d ≠ d₀}) :=
    fun v i => if h : v i ≠ d₀ then ⟨v i, h⟩ else ⟨c₀, hc₀⟩
  have hinj : Set.InjOn f S := by
    intro v₁ hv₁ v₂ hv₂ hEq
    simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      cnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hv₁ hv₂
    funext i
    have h1 : v₁ i ≠ d₀ := hv₁ trivial
    have h2 : v₂ i ≠ d₀ := hv₂ trivial
    have hi := congr_arg Subtype.val (congr_fun hEq i)
    simpa [f, h1, h2] using hi
  have hle : S.card ≤ (Finset.univ : Finset (Fin m → {d : Fin 10 // d ≠ d₀})).card :=
    Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj
  have hcard_sub : Fintype.card {d : Fin 10 // d ≠ d₀} = 9 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    have : Fintype.card {d : Fin 10 // d = d₀} = 1 := Fintype.card_unique
    omega
  simpa [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hcard_sub] using hle

lemma card_badMissing_le (m : ℕ) :
    (Finset.univ.filter fun v : Fin m → Fin 10 => BadMissing v).card ≤ 2 * 9 ^ m := by
  calc
    (Finset.univ.filter fun v : Fin m → Fin 10 => BadMissing v).card
        ≤ ((Finset.univ.filter fun v : Fin m → Fin 10 => cnt v 0 = 0) ∪
            (Finset.univ.filter fun v : Fin m → Fin 10 => cnt v 9 = 0)).card := by
          apply Finset.card_le_card
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hv
    _ ≤ (Finset.univ.filter fun v : Fin m → Fin 10 => cnt v 0 = 0).card +
        (Finset.univ.filter fun v : Fin m → Fin 10 => cnt v 9 = 0).card := Finset.card_union_le _ _
    _ ≤ 9 ^ m + 9 ^ m := Nat.add_le_add (card_cnt_eq_zero_le m 0) (card_cnt_eq_zero_le m 9)
    _ = 2 * 9 ^ m := by ring

lemma badTie_imp_exists_pair {m : ℕ} {v : Fin m → Fin 10} (h : BadTie v) :
    ∃ d₁ d₂ : Fin 10, d₁ ≠ d₂ ∧ cnt v d₂ = (cnt v d₁ + cnt v d₂) / 2 := by
  obtain ⟨d₁, _, hd₁max⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin 10)) (cnt v) Finset.univ_nonempty
  have hnot : ¬ StrictMode2 v d₁ := fun hs => h ⟨d₁, hs⟩
  simp only [StrictMode2, not_forall, not_le] at hnot
  obtain ⟨d₂, hne, hlt⟩ := hnot
  have hle : cnt v d₂ ≤ cnt v d₁ := hd₁max d₂ (Finset.mem_univ d₂)
  exact ⟨d₁, d₂, Ne.symm hne, by omega⟩

lemma card_subtype_ne_two (d₁ d₂ : Fin 10) (hne : d₁ ≠ d₂) :
    Fintype.card {d : Fin 10 // d ≠ d₁ ∧ d ≠ d₂} = 8 := by
  rw [Fintype.card_subtype]
  have hset : (Finset.univ.filter fun d : Fin 10 => d ≠ d₁ ∧ d ≠ d₂) =
      Finset.univ \ ({d₁, d₂} : Finset (Fin 10)) := by
    ext d
    simp [not_or]
  rw [hset, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
    Finset.card_pair hne]

lemma card_nearTie_fiber_le {m : ℕ} (d₁ d₂ : Fin 10) (hne : d₁ ≠ d₂)
    (A B : Finset (Fin m)) :
    (Finset.univ.filter fun v : Fin m → Fin 10 =>
      (Finset.univ.filter fun i : Fin m => v i = d₁ ∨ v i = d₂) = A ∧
      (Finset.univ.filter fun i : Fin m => v i = d₂) = B).card ≤ 8 ^ (m - A.card) := by
  have hcard8 := card_subtype_ne_two d₁ d₂ hne
  have hnonempty : Nonempty {d : Fin 10 // d ≠ d₁ ∧ d ≠ d₂} :=
    Fintype.card_pos_iff.mp (by omega)
  let c₀ : {d : Fin 10 // d ≠ d₁ ∧ d ≠ d₂} := Classical.arbitrary _
  let F := Finset.univ.filter fun v : Fin m → Fin 10 =>
    (Finset.univ.filter fun i : Fin m => v i = d₁ ∨ v i = d₂) = A ∧
    (Finset.univ.filter fun i : Fin m => v i = d₂) = B
  let f : (Fin m → Fin 10) → ({i : Fin m // i ∉ A} → {d : Fin 10 // d ≠ d₁ ∧ d ≠ d₂}) :=
    fun v i => if h : v i.1 ≠ d₁ ∧ v i.1 ≠ d₂ then ⟨v i.1, h⟩ else c₀
  have hinj : Set.InjOn f F := by
    intro v₁ hv₁ v₂ hv₂ hEq
    simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
    funext i
    by_cases hiB : i ∈ B
    · have h1 : v₁ i = d₂ := by
        have : i ∈ Finset.univ.filter fun j => v₁ j = d₂ := by rw [hv₁.2]; exact hiB
        simpa using this
      have h2 : v₂ i = d₂ := by
        have : i ∈ Finset.univ.filter fun j => v₂ j = d₂ := by rw [hv₂.2]; exact hiB
        simpa using this
      rw [h1, h2]
    · by_cases hiA : i ∈ A
      · have h1 : v₁ i = d₁ := by
          have ha : i ∈ Finset.univ.filter fun j => v₁ j = d₁ ∨ v₁ j = d₂ := by
            rw [hv₁.1]; exact hiA
          have hb : i ∉ Finset.univ.filter fun j => v₁ j = d₂ := by
            rw [hv₁.2]; exact hiB
          simp at ha hb
          exact ha.resolve_right hb
        have h2 : v₂ i = d₁ := by
          have ha : i ∈ Finset.univ.filter fun j => v₂ j = d₁ ∨ v₂ j = d₂ := by
            rw [hv₂.1]; exact hiA
          have hb : i ∉ Finset.univ.filter fun j => v₂ j = d₂ := by
            rw [hv₂.2]; exact hiB
          simp at ha hb
          exact ha.resolve_right hb
        rw [h1, h2]
      · have h1 : v₁ i ≠ d₁ ∧ v₁ i ≠ d₂ := by
          have ha : i ∉ Finset.univ.filter fun j => v₁ j = d₁ ∨ v₁ j = d₂ := by
            rw [hv₁.1]; exact hiA
          simpa [not_or] using ha
        have h2 : v₂ i ≠ d₁ ∧ v₂ i ≠ d₂ := by
          have ha : i ∉ Finset.univ.filter fun j => v₂ j = d₁ ∨ v₂ j = d₂ := by
            rw [hv₂.1]; exact hiA
          simpa [not_or] using ha
        have hi := congr_arg Subtype.val (congr_fun hEq ⟨i, hiA⟩)
        simpa [f, h1, h2] using hi
  have hle : F.card ≤
      (Finset.univ : Finset ({i : Fin m // i ∉ A} → {d : Fin 10 // d ≠ d₁ ∧ d ≠ d₂})).card :=
    Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj
  have hcompl : Fintype.card {i : Fin m // i ∉ A} = m - A.card := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun i : Fin m => i ∉ A) = Aᶜ := by
      ext i; simp
    rw [this, Finset.card_compl, Fintype.card_fin]
  simpa [Finset.card_univ, Fintype.card_fun, hcard8, hcompl] using hle

lemma card_nearTie_le (m : ℕ) (d₁ d₂ : Fin 10) (hne : d₁ ≠ d₂) :
    (Finset.univ.filter fun v : Fin m → Fin 10 =>
      cnt v d₂ = (cnt v d₁ + cnt v d₂) / 2).card ≤
      ∑ k ∈ Finset.range (m + 1), Nat.choose m k * Nat.choose k (k / 2) * 8 ^ (m - k) := by
  let E := Finset.univ.filter fun v : Fin m → Fin 10 => cnt v d₂ = (cnt v d₁ + cnt v d₂) / 2
  let supp : (Fin m → Fin 10) → Finset (Fin m) :=
    fun v => Finset.univ.filter fun i => v i = d₁ ∨ v i = d₂
  let pos₂ : (Fin m → Fin 10) → Finset (Fin m) :=
    fun v => Finset.univ.filter fun i => v i = d₂
  have hsupp_card : ∀ v : Fin m → Fin 10, (supp v).card = cnt v d₁ + cnt v d₂ := by
    intro v
    have hdisj : Disjoint (Finset.univ.filter fun i => v i = d₁)
        (Finset.univ.filter fun i => v i = d₂) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      simp at h1 h2
      exact hne (h1.symm.trans h2)
    have hun : supp v = (Finset.univ.filter fun i => v i = d₁) ∪
        (Finset.univ.filter fun i => v i = d₂) := by
      ext i; simp [supp]
    rw [hun, Finset.card_union_of_disjoint hdisj]
    rfl
  have hE_eq : E.card = ∑ A : Finset (Fin m), (E.filter fun v => supp v = A).card := by
    simpa using Finset.card_eq_sum_card_fiberwise
      (f := supp) (s := E) (t := (Finset.univ : Finset (Finset (Fin m))))
      (fun _ _ => Finset.mem_univ _)
  have hA_le : ∀ A : Finset (Fin m),
      (E.filter fun v => supp v = A).card ≤ Nat.choose A.card (A.card / 2) * 8 ^ (m - A.card) := by
    intro A
    have hmap : ∀ v ∈ E.filter fun v => supp v = A, pos₂ v ∈ A.powersetCard (A.card / 2) := by
      intro v hv
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      rw [Finset.mem_powersetCard]
      constructor
      · intro i hi
        rw [← hv.2]
        simp only [pos₂, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp [supp, hi]
      · have hc : (pos₂ v).card = cnt v d₂ := rfl
        rw [hc, hv.1, ← hsupp_card v, hv.2]
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    calc
      ∑ B ∈ A.powersetCard (A.card / 2), ((E.filter fun v => supp v = A).filter fun v => pos₂ v = B).card
          ≤ ∑ _B ∈ A.powersetCard (A.card / 2), 8 ^ (m - A.card) := by
            apply Finset.sum_le_sum
            intro B _
            calc
              ((E.filter fun v => supp v = A).filter fun v => pos₂ v = B).card
                  ≤ (Finset.univ.filter fun v : Fin m → Fin 10 => supp v = A ∧ pos₂ v = B).card := by
                    apply Finset.card_le_card
                    intro v hv
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
                    exact ⟨hv.1.2, hv.2⟩
              _ ≤ 8 ^ (m - A.card) := card_nearTie_fiber_le d₁ d₂ hne A B
      _ = Nat.choose A.card (A.card / 2) * 8 ^ (m - A.card) := by
            rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
  rw [hE_eq]
  calc
    ∑ A : Finset (Fin m), (E.filter fun v => supp v = A).card
        ≤ ∑ A : Finset (Fin m), Nat.choose A.card (A.card / 2) * 8 ^ (m - A.card) :=
          Finset.sum_le_sum fun A _ => hA_le A
    _ = ∑ k ∈ Finset.range (m + 1),
          ∑ A ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun A => A.card = k),
            Nat.choose A.card (A.card / 2) * 8 ^ (m - A.card) := by
          symm
          apply Finset.sum_fiberwise_of_maps_to
          intro A _
          rw [Finset.mem_range]
          have : A.card ≤ m := by
            simpa [Fintype.card_fin] using Finset.card_le_univ A
          omega
    _ = ∑ k ∈ Finset.range (m + 1), Nat.choose m k * Nat.choose k (k / 2) * 8 ^ (m - k) := by
          apply Finset.sum_congr rfl
          intro k _
          have hcongr : ∑ A ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun A => A.card = k),
              Nat.choose A.card (A.card / 2) * 8 ^ (m - A.card) =
              ∑ _A ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun A => A.card = k),
                Nat.choose k (k / 2) * 8 ^ (m - k) := by
            apply Finset.sum_congr rfl
            intro A hA
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
            rw [hA]
          rw [hcongr, Finset.sum_const, smul_eq_mul]
          have hfilt : ((Finset.univ : Finset (Finset (Fin m))).filter fun A => A.card = k) =
              (Finset.univ : Finset (Fin m)).powersetCard k := by
            ext A
            simp [Finset.mem_powersetCard]
          rw [hfilt, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, mul_assoc]

lemma card_badTie_le (m : ℕ) :
    (Finset.univ.filter fun v : Fin m → Fin 10 => BadTie v).card ≤
      100 * ∑ k ∈ Finset.range (m + 1), Nat.choose m k * Nat.choose k (k / 2) * 8 ^ (m - k) := by
  let P := (Finset.univ : Finset (Fin 10 × Fin 10)).filter fun p => p.1 ≠ p.2
  calc
    (Finset.univ.filter fun v : Fin m → Fin 10 => BadTie v).card
        ≤ (P.biUnion fun p => Finset.univ.filter fun v : Fin m → Fin 10 =>
            cnt v p.2 = (cnt v p.1 + cnt v p.2) / 2).card := by
          apply Finset.card_le_card
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
          obtain ⟨d₁, d₂, hne, heq⟩ := badTie_imp_exists_pair hv
          simp only [P, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨(d₁, d₂), hne, heq⟩
    _ ≤ ∑ p ∈ P, (Finset.univ.filter fun v : Fin m → Fin 10 =>
          cnt v p.2 = (cnt v p.1 + cnt v p.2) / 2).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ P, ∑ k ∈ Finset.range (m + 1),
          Nat.choose m k * Nat.choose k (k / 2) * 8 ^ (m - k) := by
          apply Finset.sum_le_sum
          intro p hp
          simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          exact card_nearTie_le m p.1 p.2 hp
    _ = P.card * ∑ k ∈ Finset.range (m + 1),
          Nat.choose m k * Nat.choose k (k / 2) * 8 ^ (m - k) := by
          rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 100 * ∑ k ∈ Finset.range (m + 1),
          Nat.choose m k * Nat.choose k (k / 2) * 8 ^ (m - k) := by
          apply Nat.mul_le_mul_right
          have hP : P.card ≤ (Finset.univ : Finset (Fin 10 × Fin 10)).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          simpa [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using hP

end CountingStructure

section AnalyticBounds

lemma succ_mul_choose_eq : ∀ n k : ℕ,
    (n + 1) * Nat.choose n k = Nat.choose (n + 1) (k + 1) * (k + 1)
  | 0, 0 => by simp
  | 0, k + 1 => by
    rw [Nat.choose_eq_zero_of_lt (by omega : 0 < k + 1),
      Nat.choose_eq_zero_of_lt (by omega : 0 + 1 < k + 1 + 1)]
    simp
  | n + 1, 0 => by simp
  | n + 1, k + 1 => by
    have ih1 := succ_mul_choose_eq n k
    have ih2 := succ_mul_choose_eq n (k + 1)
    calc
      (n + 1 + 1) * Nat.choose (n + 1) (k + 1)
          = (n + 1) * (Nat.choose n k + Nat.choose n (k + 1)) + Nat.choose (n + 1) (k + 1) := by
            rw [Nat.choose_succ_succ n k]; ring
      _ = (n + 1) * Nat.choose n k + (n + 1) * Nat.choose n (k + 1) + Nat.choose (n + 1) (k + 1) := by
            ring
      _ = Nat.choose (n + 1) (k + 1) * (k + 1) + Nat.choose (n + 1) (k + 2) * (k + 2) +
            Nat.choose (n + 1) (k + 1) := by rw [ih1, ih2]
      _ = (Nat.choose (n + 1) (k + 1) + Nat.choose (n + 1) (k + 2)) * (k + 1 + 1) := by ring
      _ = Nat.choose (n + 1 + 1) (k + 1 + 1) * (k + 1 + 1) := by
            rw [Nat.choose_succ_succ (n + 1) (k + 1)]

lemma central_binom_step (j : ℕ) :
    Nat.choose (2 * j + 2) (j + 1) * (j + 1) = 2 * (2 * j + 1) * Nat.choose (2 * j) j := by
  have h1 := succ_mul_choose_eq (2 * j + 1) j
  have h2 : Nat.choose (2 * j + 1) j = Nat.choose (2 * j + 1) (j + 1) := by
    have hs := Nat.choose_symm (n := 2 * j + 1) (k := j) (by omega)
    have hsub : 2 * j + 1 - j = j + 1 := by omega
    rw [hsub] at hs
    exact hs.symm
  have h3 := succ_mul_choose_eq (2 * j) j
  calc
    Nat.choose (2 * j + 2) (j + 1) * (j + 1)
        = (2 * j + 2) * Nat.choose (2 * j + 1) j := h1.symm
    _ = 2 * (Nat.choose (2 * j + 1) (j + 1) * (j + 1)) := by rw [h2]; ring
    _ = 2 * ((2 * j + 1) * Nat.choose (2 * j) j) := by rw [h3]
    _ = 2 * (2 * j + 1) * Nat.choose (2 * j) j := by ring

lemma central_binom_even_sq_le : ∀ j : ℕ,
    ((Nat.choose (2 * j) j : ℝ) / (4 : ℝ) ^ j) ^ 2 ≤ 1 / (2 * (j : ℝ) + 1)
  | 0 => by norm_num
  | j + 1 => by
    have ih := central_binom_even_sq_le j
    have hstep : (Nat.choose (2 * (j + 1)) (j + 1) : ℝ) * ((j : ℝ) + 1) =
        2 * (2 * (j : ℝ) + 1) * (Nat.choose (2 * j) j : ℝ) := by
      have h2 : 2 * (j + 1) = 2 * j + 2 := by omega
      rw [h2]
      have h := central_binom_step j
      have h' : (Nat.choose (2 * j + 2) (j + 1) * (j + 1) : ℝ) =
          (2 * (2 * j + 1) * Nat.choose (2 * j) j : ℝ) := by exact_mod_cast h
      linarith
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have h2j1 : (0 : ℝ) < 2 * (j : ℝ) + 1 := by positivity
    have h2j3 : (0 : ℝ) < 2 * (j : ℝ) + 3 := by positivity
    have hrat : (Nat.choose (2 * (j + 1)) (j + 1) : ℝ) / (4 : ℝ) ^ (j + 1) =
        ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) + 2)) *
          ((Nat.choose (2 * j) j : ℝ) / (4 : ℝ) ^ j) := by
      rw [pow_succ]
      have h4 : (4 : ℝ) ^ j ≠ 0 := by positivity
      have h2j2 : 2 * (j : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      linarith
    rw [hrat, mul_pow]
    calc
      ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) + 2)) ^ 2 *
          ((Nat.choose (2 * j) j : ℝ) / (4 : ℝ) ^ j) ^ 2
          ≤ ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) + 2)) ^ 2 * (1 / (2 * (j : ℝ) + 1)) := by
            apply mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ ≤ 1 / (2 * ((j + 1 : ℕ) : ℝ) + 1) := by
            push_cast
            have h2j2 : (0 : ℝ) < 2 * (j : ℝ) + 2 := by positivity
            rw [div_pow, div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith

lemma central_binom_sq_le (k : ℕ) :
    ((Nat.choose k (k / 2) : ℝ) / (2 : ℝ) ^ k) ^ 2 ≤ 1 / ((k : ℝ) + 1) := by
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have hhalf : (j + j) / 2 = j := by omega
    have htwo : j + j = 2 * j := by omega
    rw [hhalf, htwo]
    have hpow : (2 : ℝ) ^ (2 * j) = (4 : ℝ) ^ j := by
      rw [pow_mul]; norm_num
    rw [hpow]
    simpa [Nat.cast_mul] using central_binom_even_sq_le j
  · have hhalf : (2 * j + 1) / 2 = j := by omega
    rw [hhalf]
    have hsym : Nat.choose (2 * j + 1) (j + 1) = Nat.choose (2 * j + 1) j := by
      have hs := Nat.choose_symm (n := 2 * j + 1) (k := j) (by omega)
      have hsub : 2 * j + 1 - j = j + 1 := by omega
      rw [hsub] at hs
      exact hs
    have hpas : Nat.choose (2 * (j + 1)) (j + 1) = 2 * Nat.choose (2 * j + 1) j := by
      have h1 : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
      rw [h1, Nat.choose_succ_succ, hsym]
      ring
    have heq : (Nat.choose (2 * j + 1) j : ℝ) / (2 : ℝ) ^ (2 * j + 1) =
        (Nat.choose (2 * (j + 1)) (j + 1) : ℝ) / (4 : ℝ) ^ (j + 1) := by
      have hpas' : (Nat.choose (2 * (j + 1)) (j + 1) : ℝ) =
          2 * (Nat.choose (2 * j + 1) j : ℝ) := by exact_mod_cast hpas
      have hpow : (4 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ (2 * j + 1) := by
        rw [pow_succ, pow_succ]
        have : (4 : ℝ) ^ j = (2 : ℝ) ^ (2 * j) := by rw [pow_mul]; norm_num
        rw [this]; ring
      rw [hpas', hpow]
      have : (2 : ℝ) ^ (2 * j + 1) ≠ 0 := by positivity
      field_simp
    rw [heq]
    calc
      ((Nat.choose (2 * (j + 1)) (j + 1) : ℝ) / (4 : ℝ) ^ (j + 1)) ^ 2
          ≤ 1 / (2 * ((j + 1 : ℕ) : ℝ) + 1) := central_binom_even_sq_le (j + 1)
      _ ≤ 1 / (((2 * j + 1 : ℕ) : ℝ) + 1) := by
            push_cast
            apply one_div_le_one_div_of_le (by positivity)
            linarith

lemma central_binom_div_le (k : ℕ) :
    (Nat.choose k (k / 2) : ℝ) / (2 : ℝ) ^ k ≤ Real.sqrt (1 / ((k : ℝ) + 1)) := by
  have hnn : 0 ≤ (Nat.choose k (k / 2) : ℝ) / (2 : ℝ) ^ k := by positivity
  rw [← Real.sqrt_sq hnn]
  exact Real.sqrt_le_sqrt (central_binom_sq_le k)

lemma binom_sum_0 (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * (2 : ℝ) ^ k * (8 : ℝ) ^ (m - k) =
      (10 : ℝ) ^ m := by
  have h := add_pow (2 : ℝ) (8 : ℝ) m
  have h10 : (2 : ℝ) + 8 = 10 := by norm_num
  rw [h10] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma binom_sum_1_succ (m : ℕ) :
    ∑ k ∈ Finset.range (m + 2),
      (Nat.choose (m + 1) k : ℝ) * (k : ℝ) * (2 : ℝ) ^ k * (8 : ℝ) ^ (m + 1 - k) =
      2 * ((m : ℝ) + 1) * (10 : ℝ) ^ m := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
  calc
    ∑ j ∈ Finset.range (m + 1),
        (Nat.choose (m + 1) (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (j + 1) *
          (8 : ℝ) ^ (m + 1 - (j + 1))
        = ∑ j ∈ Finset.range (m + 1),
            (2 * ((m : ℝ) + 1)) *
              ((Nat.choose m j : ℝ) * (2 : ℝ) ^ j * (8 : ℝ) ^ (m - j)) := by
          apply Finset.sum_congr rfl
          intro j _
          have hch : (Nat.choose (m + 1) (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) =
              ((m + 1 : ℕ) : ℝ) * (Nat.choose m j : ℝ) := by
            have := succ_mul_choose_eq m j
            exact_mod_cast this.symm
          rw [hch, Nat.add_sub_add_right, pow_succ]
          push_cast
          ring
    _ = 2 * ((m : ℝ) + 1) *
          ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * (2 : ℝ) ^ j * (8 : ℝ) ^ (m - j) := by
          rw [← Finset.mul_sum]
    _ = 2 * ((m : ℝ) + 1) * (10 : ℝ) ^ m := by
          rw [binom_sum_0]

lemma binom_sum_1 (m : ℕ) :
    5 * ∑ k ∈ Finset.range (m + 1),
      (Nat.choose m k : ℝ) * (k : ℝ) * (2 : ℝ) ^ k * (8 : ℝ) ^ (m - k) =
      (m : ℝ) * (10 : ℝ) ^ m := by
  cases m with
  | zero => simp
  | succ m =>
    rw [binom_sum_1_succ]
    push_cast
    rw [pow_succ]
    ring

lemma binom_sum_2_succ (m : ℕ) :
    ∑ k ∈ Finset.range (m + 2),
      (Nat.choose (m + 1) k : ℝ) * (k : ℝ) ^ 2 * (2 : ℝ) ^ k * (8 : ℝ) ^ (m + 1 - k) =
      2 * ((m : ℝ) + 1) *
        ((∑ j ∈ Finset.range (m + 1),
            (Nat.choose m j : ℝ) * (j : ℝ) * (2 : ℝ) ^ j * (8 : ℝ) ^ (m - j)) +
          (∑ j ∈ Finset.range (m + 1),
            (Nat.choose m j : ℝ) * (2 : ℝ) ^ j * (8 : ℝ) ^ (m - j))) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, zero_mul, add_zero]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hch : (Nat.choose (m + 1) (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) =
      ((m + 1 : ℕ) : ℝ) * (Nat.choose m j : ℝ) := by
    have := succ_mul_choose_eq m j
    exact_mod_cast this.symm
  rw [Nat.add_sub_add_right, pow_succ (2 : ℝ)]
  have hsq : ((j + 1 : ℕ) : ℝ) ^ 2 = ((j + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) := sq _
  rw [hsq, ← mul_assoc (Nat.choose (m + 1) (j + 1) : ℝ), hch]
  push_cast
  ring

lemma binom_sum_2 (m : ℕ) :
    25 * ∑ k ∈ Finset.range (m + 1),
      (Nat.choose m k : ℝ) * (k : ℝ) ^ 2 * (2 : ℝ) ^ k * (8 : ℝ) ^ (m - k) =
      (m : ℝ) * ((m : ℝ) + 4) * (10 : ℝ) ^ m := by
  cases m with
  | zero => simp
  | succ m =>
    rw [binom_sum_2_succ]
    have h1 := binom_sum_1 m
    have h0 := binom_sum_0 m
    calc
      25 * (2 * ((m : ℝ) + 1) *
          ((∑ j ∈ Finset.range (m + 1),
              (Nat.choose m j : ℝ) * (j : ℝ) * (2 : ℝ) ^ j * (8 : ℝ) ^ (m - j)) +
            (∑ j ∈ Finset.range (m + 1),
              (Nat.choose m j : ℝ) * (2 : ℝ) ^ j * (8 : ℝ) ^ (m - j))))
          = 10 * ((m : ℝ) + 1) *
              (5 * (∑ j ∈ Finset.range (m + 1),
                  (Nat.choose m j : ℝ) * (j : ℝ) * (2 : ℝ) ^ j * (8 : ℝ) ^ (m - j)) +
                5 * (∑ j ∈ Finset.range (m + 1),
                  (Nat.choose m j : ℝ) * (2 : ℝ) ^ j * (8 : ℝ) ^ (m - j))) := by ring
      _ = 10 * ((m : ℝ) + 1) * ((m : ℝ) * (10 : ℝ) ^ m + 5 * (10 : ℝ) ^ m) := by rw [h1, h0]
      _ = ((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) + 4) * (10 : ℝ) ^ (m + 1) := by
            push_cast
            rw [pow_succ]
            ring

lemma binom_variance (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1),
      (Nat.choose m k : ℝ) * (5 * (k : ℝ) - (m : ℝ)) ^ 2 * (2 : ℝ) ^ k * (8 : ℝ) ^ (m - k) =
      4 * (m : ℝ) * (10 : ℝ) ^ m := by
  have hexpand :
      ∑ k ∈ Finset.range (m + 1),
        (Nat.choose m k : ℝ) * (5 * (k : ℝ) - (m : ℝ)) ^ 2 * (2 : ℝ) ^ k * (8 : ℝ) ^ (m - k) =
      25 * (∑ k ∈ Finset.range (m + 1),
          (Nat.choose m k : ℝ) * (k : ℝ) ^ 2 * (2 : ℝ) ^ k * (8 : ℝ) ^ (m - k)) -
      10 * (m : ℝ) * (∑ k ∈ Finset.range (m + 1),
          (Nat.choose m k : ℝ) * (k : ℝ) * (2 : ℝ) ^ k * (8 : ℝ) ^ (m - k)) +
      (m : ℝ) ^ 2 * (∑ k ∈ Finset.range (m + 1),
          (Nat.choose m k : ℝ) * (2 : ℝ) ^ k * (8 : ℝ) ^ (m - k)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hexpand, binom_sum_2, binom_sum_0]
  have h1 := binom_sum_1 m
  nlinarith

lemma tie_sum_le (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.range (m + 1),
      (Nat.choose m k : ℝ) * (Nat.choose k (k / 2) : ℝ) * (8 : ℝ) ^ (m - k) ≤
      (16 / (m : ℝ) + Real.sqrt (10 / (m : ℝ))) * (10 : ℝ) ^ m := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hterm : ∀ k ∈ Finset.range (m + 1),
      (Nat.choose m k : ℝ) * (Nat.choose k (k / 2) : ℝ) * (8 : ℝ) ^ (m - k) ≤
        (4 / (m : ℝ) ^ 2) *
          ((Nat.choose m k : ℝ) * (5 * (k : ℝ) - (m : ℝ)) ^ 2 * (2 : ℝ) ^ k * (8 : ℝ) ^ (m - k)) +
        Real.sqrt (10 / (m : ℝ)) *
          ((Nat.choose m k : ℝ) * (2 : ℝ) ^ k * (8 : ℝ) ^ (m - k)) := by
    intro k _
    have hnn1 : 0 ≤ (4 / (m : ℝ) ^ 2) *
        ((Nat.choose m k : ℝ) * (5 * (k : ℝ) - (m : ℝ)) ^ 2 * (2 : ℝ) ^ k * (8 : ℝ) ^ (m - k)) := by
      positivity
    have hnn2 : 0 ≤ Real.sqrt (10 / (m : ℝ)) *
        ((Nat.choose m k : ℝ) * (2 : ℝ) ^ k * (8 : ℝ) ^ (m - k)) := by
      positivity
    by_cases hsmall : 10 * k ≤ m
    · have hsmallR : 10 * (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hsmall
      have hsq : (m : ℝ) ^ 2 ≤ 4 * (5 * (k : ℝ) - (m : ℝ)) ^ 2 := by nlinarith
      have hone : (1 : ℝ) ≤ (4 / (m : ℝ) ^ 2) * (5 * (k : ℝ) - (m : ℝ)) ^ 2 := by
        rw [div_mul_eq_mul_div, one_le_div (by positivity)]
        exact hsq
      have hch_le : (Nat.choose k (k / 2) : ℝ) ≤ (2 : ℝ) ^ k := by
        exact_mod_cast Nat.choose_le_two_pow k (k / 2)
      have h1 : (Nat.choose m k : ℝ) * (Nat.choose k (k / 2) : ℝ) * (8 : ℝ) ^ (m - k) ≤
          (4 / (m : ℝ) ^ 2) *
            ((Nat.choose m k : ℝ) * (5 * (k : ℝ) - (m : ℝ)) ^ 2 * (2 : ℝ) ^ k *
              (8 : ℝ) ^ (m - k)) := by
        calc
          (Nat.choose m k : ℝ) * (Nat.choose k (k / 2) : ℝ) * (8 : ℝ) ^ (m - k)
              ≤ (Nat.choose m k : ℝ) * (2 : ℝ) ^ k * (8 : ℝ) ^ (m - k) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                apply mul_le_mul_of_nonneg_left hch_le (by positivity)
          _ = 1 * ((Nat.choose m k : ℝ) * (2 : ℝ) ^ k * (8 : ℝ) ^ (m - k)) := by ring
          _ ≤ ((4 / (m : ℝ) ^ 2) * (5 * (k : ℝ) - (m : ℝ)) ^ 2) *
                ((Nat.choose m k : ℝ) * (2 : ℝ) ^ k * (8 : ℝ) ^ (m - k)) := by
                apply mul_le_mul_of_nonneg_right hone (by positivity)
          _ = _ := by ring
      linarith
    · have hbig : m < 10 * k := Nat.lt_of_not_ge hsmall
      have hbigR : (m : ℝ) ≤ 10 * ((k : ℝ) + 1) := by
        have : (m : ℝ) < 10 * (k : ℝ) := by exact_mod_cast hbig
        linarith
      have hdiv : 1 / ((k : ℝ) + 1) ≤ 10 / (m : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) hm_pos]
        linarith
      have hcb : (Nat.choose k (k / 2) : ℝ) ≤ Real.sqrt (10 / (m : ℝ)) * (2 : ℝ) ^ k := by
        have h1 := (central_binom_div_le k).trans (Real.sqrt_le_sqrt hdiv)
        rwa [div_le_iff₀ (by positivity)] at h1
      have h2 : (Nat.choose m k : ℝ) * (Nat.choose k (k / 2) : ℝ) * (8 : ℝ) ^ (m - k) ≤
          Real.sqrt (10 / (m : ℝ)) *
            ((Nat.choose m k : ℝ) * (2 : ℝ) ^ k * (8 : ℝ) ^ (m - k)) := by
        calc
          (Nat.choose m k : ℝ) * (Nat.choose k (k / 2) : ℝ) * (8 : ℝ) ^ (m - k)
              ≤ (Nat.choose m k : ℝ) * (Real.sqrt (10 / (m : ℝ)) * (2 : ℝ) ^ k) *
                  (8 : ℝ) ^ (m - k) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                apply mul_le_mul_of_nonneg_left hcb (by positivity)
          _ = _ := by ring
      linarith
  calc
    ∑ k ∈ Finset.range (m + 1),
        (Nat.choose m k : ℝ) * (Nat.choose k (k / 2) : ℝ) * (8 : ℝ) ^ (m - k)
        ≤ ∑ k ∈ Finset.range (m + 1),
            ((4 / (m : ℝ) ^ 2) *
              ((Nat.choose m k : ℝ) * (5 * (k : ℝ) - (m : ℝ)) ^ 2 * (2 : ℝ) ^ k *
                (8 : ℝ) ^ (m - k)) +
            Real.sqrt (10 / (m : ℝ)) *
              ((Nat.choose m k : ℝ) * (2 : ℝ) ^ k * (8 : ℝ) ^ (m - k))) :=
          Finset.sum_le_sum hterm
    _ = (4 / (m : ℝ) ^ 2) *
          (∑ k ∈ Finset.range (m + 1),
            (Nat.choose m k : ℝ) * (5 * (k : ℝ) - (m : ℝ)) ^ 2 * (2 : ℝ) ^ k *
              (8 : ℝ) ^ (m - k)) +
        Real.sqrt (10 / (m : ℝ)) *
          (∑ k ∈ Finset.range (m + 1),
            (Nat.choose m k : ℝ) * (2 : ℝ) ^ k * (8 : ℝ) ^ (m - k)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (4 / (m : ℝ) ^ 2) * (4 * (m : ℝ) * (10 : ℝ) ^ m) +
          Real.sqrt (10 / (m : ℝ)) * (10 : ℝ) ^ m := by
          rw [binom_variance, binom_sum_0]
    _ = (16 / (m : ℝ) + Real.sqrt (10 / (m : ℝ))) * (10 : ℝ) ^ m := by
          have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
          field_simp
          ring

lemma term_ratio_abs_sub_le (m : ℕ) (hm : 1 ≤ m) :
    |(term (m + 1) : ℝ) / (9 * (10 : ℝ) ^ m) - 1 / 10| ≤
      2 * (9 / 10 : ℝ) ^ m + 200 * (16 / (m : ℝ) + Real.sqrt (10 / (m : ℝ))) := by
  open Classical in
  let s9 : ℕ := (Finset.univ.filter fun v : Fin m → Fin 10 => StrictMode2 v 9).card
  let cm : ℕ := (Finset.univ.filter fun v : Fin m → Fin 10 => BadMissing v).card
  let ct : ℕ := (Finset.univ.filter fun v : Fin m → Fin 10 => BadTie v).card
  have hlower_nat : 9 * s9 ≤ term (m + 1) + 9 * cm := by
    rw [term_succ_eq_sum hm]
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 9)))
      (fun a _ => card_strictMode_le_card_qualifies_add_missing (m := m) a)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at hsum
    exact hsum
  have hupper_nat : term (m + 1) ≤ 9 * s9 + 9 * cm + 9 * ct := by
    rw [term_succ_eq_sum hm]
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 9)))
      (fun a _ => card_qualifies_le_card_strictMode_add_missing_add_tie (m := m) a)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at hsum
    exact hsum
  have hsym_nat : 10 * s9 + ct = 10 ^ m := ten_mul_card_strictMode2_add_card_badTie m
  have hcm_nat : cm ≤ 2 * 9 ^ m := card_badMissing_le m
  have hct_nat : ct ≤ 100 * ∑ k ∈ Finset.range (m + 1),
      Nat.choose m k * Nat.choose k (k / 2) * 8 ^ (m - k) := card_badTie_le m
  have hlower : 9 * (s9 : ℝ) ≤ (term (m + 1) : ℝ) + 9 * (cm : ℝ) := by exact_mod_cast hlower_nat
  have hupper : (term (m + 1) : ℝ) ≤ 9 * (s9 : ℝ) + 9 * (cm : ℝ) + 9 * (ct : ℝ) := by
    exact_mod_cast hupper_nat
  have hsym : 10 * (s9 : ℝ) + (ct : ℝ) = (10 : ℝ) ^ m := by exact_mod_cast hsym_nat
  have hcm : (cm : ℝ) ≤ 2 * (9 : ℝ) ^ m := by exact_mod_cast hcm_nat
  have hct : (ct : ℝ) ≤ 100 * ((16 / (m : ℝ) + Real.sqrt (10 / (m : ℝ))) * (10 : ℝ) ^ m) := by
    have h1 : (ct : ℝ) ≤ 100 * ∑ k ∈ Finset.range (m + 1),
        (Nat.choose m k : ℝ) * (Nat.choose k (k / 2) : ℝ) * (8 : ℝ) ^ (m - k) := by
      exact_mod_cast hct_nat
    exact h1.trans (mul_le_mul_of_nonneg_left (tie_sum_le m hm) (by norm_num))
  have h10pos : (0 : ℝ) < (10 : ℝ) ^ m := by positivity
  have h910pos : (0 : ℝ) < 9 * (10 : ℝ) ^ m := by positivity
  have hcm_div : (cm : ℝ) / (10 : ℝ) ^ m ≤ 2 * (9 / 10 : ℝ) ^ m := by
    rw [div_le_iff₀ h10pos]
    calc
      (cm : ℝ) ≤ 2 * (9 : ℝ) ^ m := hcm
      _ = 2 * (9 / 10 : ℝ) ^ m * (10 : ℝ) ^ m := by
        rw [div_pow]
        field_simp
  have hct_div : (ct : ℝ) / (10 : ℝ) ^ m ≤ 100 * (16 / (m : ℝ) + Real.sqrt (10 / (m : ℝ))) := by
    rw [div_le_iff₀ h10pos]
    linarith
  have habs : |(term (m + 1) : ℝ) / (9 * (10 : ℝ) ^ m) - 1 / 10| ≤
      (cm : ℝ) / (10 : ℝ) ^ m + 2 * ((ct : ℝ) / (10 : ℝ) ^ m) := by
    rw [abs_le]
    have hct_nn : (0 : ℝ) ≤ (ct : ℝ) := Nat.cast_nonneg _
    have h10ne : (10 : ℝ) ^ m ≠ 0 := ne_of_gt h10pos
    constructor
    · have : -(90 * (cm : ℝ) + 180 * (ct : ℝ)) ≤ 10 * (term (m + 1) : ℝ) - 9 * (10 : ℝ) ^ m := by
        linarith
      have hdiv : -(90 * (cm : ℝ) + 180 * (ct : ℝ)) / (90 * (10 : ℝ) ^ m) ≤
          (10 * (term (m + 1) : ℝ) - 9 * (10 : ℝ) ^ m) / (90 * (10 : ℝ) ^ m) :=
        div_le_div_of_nonneg_right this (by positivity)
      have hL : -(90 * (cm : ℝ) + 180 * (ct : ℝ)) / (90 * (10 : ℝ) ^ m) =
          -((cm : ℝ) / (10 : ℝ) ^ m + 2 * ((ct : ℝ) / (10 : ℝ) ^ m)) := by
        field_simp; ring
      have hR : (10 * (term (m + 1) : ℝ) - 9 * (10 : ℝ) ^ m) / (90 * (10 : ℝ) ^ m) =
          (term (m + 1) : ℝ) / (9 * (10 : ℝ) ^ m) - 1 / 10 := by
        field_simp; ring
      linarith
    · have : 10 * (term (m + 1) : ℝ) - 9 * (10 : ℝ) ^ m ≤ 90 * (cm : ℝ) + 180 * (ct : ℝ) := by
        linarith
      have hdiv : (10 * (term (m + 1) : ℝ) - 9 * (10 : ℝ) ^ m) / (90 * (10 : ℝ) ^ m) ≤
          (90 * (cm : ℝ) + 180 * (ct : ℝ)) / (90 * (10 : ℝ) ^ m) :=
        div_le_div_of_nonneg_right this (by positivity)
      have hL : (10 * (term (m + 1) : ℝ) - 9 * (10 : ℝ) ^ m) / (90 * (10 : ℝ) ^ m) =
          (term (m + 1) : ℝ) / (9 * (10 : ℝ) ^ m) - 1 / 10 := by
        field_simp; ring
      have hR : (90 * (cm : ℝ) + 180 * (ct : ℝ)) / (90 * (10 : ℝ) ^ m) =
          (cm : ℝ) / (10 : ℝ) ^ m + 2 * ((ct : ℝ) / (10 : ℝ) ^ m) := by
        field_simp; ring
      linarith
  linarith

lemma tendsto_term_div :
    Tendsto (fun m : ℕ => (term (m + 1) : ℝ) / (9 * (10 : ℝ) ^ m)) atTop (nhds (1 / 10 : ℝ)) := by
  have h1 : Tendsto (fun m : ℕ => 2 * (9 / 10 : ℝ) ^ m) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (9 / 10 : ℝ))
      (by norm_num) (by norm_num)).const_mul 2
  have hinv : Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h16 : Tendsto (fun m : ℕ => 16 / (m : ℝ)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul 16
  have h10 : Tendsto (fun m : ℕ => 10 / (m : ℝ)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul 10
  have hsqrt : Tendsto (fun m : ℕ => Real.sqrt (10 / (m : ℝ))) atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp h10
    rw [Real.sqrt_zero] at h
    exact h
  have hbound : Tendsto
      (fun m : ℕ => 2 * (9 / 10 : ℝ) ^ m + 200 * (16 / (m : ℝ) + Real.sqrt (10 / (m : ℝ))))
      atTop (nhds 0) := by
    simpa using h1.add ((h16.add hsqrt).const_mul 200)
  rw [Metric.tendsto_atTop] at hbound ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hbound ε hε
  refine ⟨max N 1, fun m hm => ?_⟩
  have hm1 : 1 ≤ m := le_trans (le_max_right N 1) hm
  have hmN : N ≤ m := le_trans (le_max_left N 1) hm
  have hdist := hN m hmN
  rw [Real.dist_eq, sub_zero] at hdist
  have hle := term_ratio_abs_sub_le m hm1
  have hnn : 0 ≤ 2 * (9 / 10 : ℝ) ^ m + 200 * (16 / (m : ℝ) + Real.sqrt (10 / (m : ℝ))) := by
    positivity
  rw [abs_of_nonneg hnn] at hdist
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hle hdist

end AnalyticBounds

end OMA_A383307

theorem OMA.solution : type_of% @OMA.S_oeis_a383307.main := by
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  let f : ℕ → ℝ := fun m => (OMA.S_oeis_a383307.term (m + 1) : ℝ) / (9 * (10 : ℝ) ^ m)
  have hf : Filter.Tendsto f Filter.atTop (nhds (1 / 10 : ℝ)) := OMA_A383307.tendsto_term_div
  have hf1 : Filter.Tendsto (fun m => f (m + 1)) Filter.atTop (nhds (1 / 10 : ℝ)) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr hf
  have hrat : Filter.Tendsto (fun m => 10 * (f (m + 1) / f m)) Filter.atTop (nhds 10) := by
    have hdiv := hf1.div hf (by norm_num)
    simpa using hdiv.const_mul 10
  refine hrat.congr fun m => ?_
  dsimp only [f]
  by_cases h0 : (OMA.S_oeis_a383307.term (m + 1) : ℝ) = 0
  · simp [h0]
  · have h10 : (10 : ℝ) ^ m ≠ 0 := by positivity
    rw [pow_succ]
    field_simp
