import OMAReductions.R_Erdos107_variants_su_bound_R1_H1_R1

/-! # The Erdős–Szekeres cups-caps theorem (existence form)

Cups and caps are finite sets in which every x-sorted triple turns left (respectively right).
The classical induction `f(a, b) ≤ f(a - 1, b) + f(a, b - 1)` uses the set `E` of right
endpoints of `(a - 1)`-cups. Extending a cup by a point, or a cap by a point, rests on two
four-point determinant identities. -/

namespace OMA.Erdos107SuH1

open Finset

def D (a b c : ℝ × ℝ) : ℝ := (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1)

def GP (U : Finset (ℝ × ℝ)) : Prop :=
  Set.InjOn Prod.fst (U : Set (ℝ × ℝ)) ∧
    ∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U, a.1 < b.1 → b.1 < c.1 → D a b c ≠ 0

def Cup (C : Finset (ℝ × ℝ)) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, a.1 < b.1 → b.1 < c.1 → 0 < D a b c

def Cap (C : Finset (ℝ × ℝ)) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, a.1 < b.1 → b.1 < c.1 → D a b c < 0

lemma iden1 (a b c d : ℝ × ℝ) :
    (c.1 - b.1) * D a b d = (d.1 - b.1) * D a b c + (b.1 - a.1) * D b c d := by
  unfold D; ring

lemma iden2 (a b c d : ℝ × ℝ) :
    (c.1 - b.1) * D a c d = (c.1 - a.1) * D b c d + (d.1 - c.1) * D a b c := by
  unfold D; ring

lemma pos_abd {a b c d : ℝ × ℝ} (h1 : a.1 < b.1) (h2 : b.1 < c.1) (h3 : c.1 < d.1)
    (p1 : 0 < D a b c) (p2 : 0 < D b c d) : 0 < D a b d := by
  have h := iden1 a b c d
  have : 0 < (c.1 - b.1) * D a b d := by
    rw [h]; exact add_pos (mul_pos (by linarith) p1) (mul_pos (by linarith) p2)
  exact pos_of_mul_pos_right this (by linarith)

lemma pos_acd {a b c d : ℝ × ℝ} (h1 : a.1 < b.1) (h2 : b.1 < c.1) (h3 : c.1 < d.1)
    (p1 : 0 < D a b c) (p2 : 0 < D b c d) : 0 < D a c d := by
  have h := iden2 a b c d
  have : 0 < (c.1 - b.1) * D a c d := by
    rw [h]; exact add_pos (mul_pos (by linarith) p2) (mul_pos (by linarith) p1)
  exact pos_of_mul_pos_right this (by linarith)

lemma neg_abd {a b c d : ℝ × ℝ} (h1 : a.1 < b.1) (h2 : b.1 < c.1) (h3 : c.1 < d.1)
    (p1 : D a b c < 0) (p2 : D b c d < 0) : D a b d < 0 := by
  have h := iden1 a b c d
  have e1 : (d.1 - b.1) * D a b c < 0 := mul_neg_of_pos_of_neg (by linarith) p1
  have e2 : (b.1 - a.1) * D b c d < 0 := mul_neg_of_pos_of_neg (by linarith) p2
  by_contra hn
  have : 0 ≤ (c.1 - b.1) * D a b d := mul_nonneg (by linarith) (not_lt.mp hn)
  linarith

lemma neg_acd {a b c d : ℝ × ℝ} (h1 : a.1 < b.1) (h2 : b.1 < c.1) (h3 : c.1 < d.1)
    (p1 : D a b c < 0) (p2 : D b c d < 0) : D a c d < 0 := by
  have h := iden2 a b c d
  have e1 : (c.1 - a.1) * D b c d < 0 := mul_neg_of_pos_of_neg (by linarith) p2
  have e2 : (d.1 - c.1) * D a b c < 0 := mul_neg_of_pos_of_neg (by linarith) p1
  by_contra hn
  have : 0 ≤ (c.1 - b.1) * D a c d := mul_nonneg (by linarith) (not_lt.mp hn)
  linarith

lemma gp_mono {U V : Finset (ℝ × ℝ)} (hU : GP U) (h : V ⊆ U) : GP V :=
  ⟨hU.1.mono (by exact_mod_cast h), fun a ha b hb c hc => hU.2 a (h ha) b (h hb) c (h hc)⟩

lemma three_le {C : Finset (ℝ × ℝ)} {a b c : ℝ × ℝ} (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C)
    (h1 : a.1 < b.1) (h2 : b.1 < c.1) : 3 ≤ C.card := by
  have hab : a ≠ b := fun e => by rw [e] at h1; exact lt_irrefl _ h1
  have hbc : b ≠ c := fun e => by rw [e] at h2; exact lt_irrefl _ h2
  have hac : a ≠ c := fun e => by rw [e] at h1; exact lt_irrefl _ (h1.trans h2)
  have hsub : ({a, b, c} : Finset (ℝ × ℝ)) ⊆ C := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have := card_le_card hsub
  rw [card_insert_of_notMem (by simp [hab, hac]), card_insert_of_notMem (by simp [hbc]),
    card_singleton] at this
  exact this

lemma small_cup {C : Finset (ℝ × ℝ)} (h : C.card ≤ 2) : Cup C := by
  intro a ha b hb c hc h1 h2
  have := three_le ha hb hc h1 h2
  omega

lemma small_cap {C : Finset (ℝ × ℝ)} (h : C.card ≤ 2) : Cap C := by
  intro a ha b hb c hc h1 h2
  have := three_le ha hb hc h1 h2
  omega

lemma fst_lt_of_le {U : Finset (ℝ × ℝ)} (hU : GP U) {x y : ℝ × ℝ} (hx : x ∈ U) (hy : y ∈ U)
    (hne : x ≠ y) (hle : x.1 ≤ y.1) : x.1 < y.1 := by
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exact absurd (hU.1 (by exact_mod_cast hx) (by exact_mod_cast hy) h) hne

/-- Erdős–Szekeres: every large set in general position has an `a`-cup or a `b`-cap. -/
theorem es : ∀ n a b : ℕ, a + b = n → ∃ N : ℕ, ∀ U : Finset (ℝ × ℝ), GP U → N ≤ U.card →
    (∃ C ⊆ U, C.card = a ∧ Cup C) ∨ (∃ C ⊆ U, C.card = b ∧ Cap C) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hab
  classical
  by_cases ha : a ≤ 2
  · refine ⟨a, fun U _ hN => Or.inl ?_⟩
    obtain ⟨C, hC, hc⟩ := Finset.exists_subset_card_eq hN
    exact ⟨C, hC, hc, small_cup (by omega)⟩
  by_cases hb : b ≤ 2
  · refine ⟨b, fun U _ hN => Or.inr ?_⟩
    obtain ⟨C, hC, hc⟩ := Finset.exists_subset_card_eq hN
    exact ⟨C, hC, hc, small_cap (by omega)⟩
  obtain ⟨N1, hN1⟩ := ih (a - 1 + b) (by omega) (a - 1) b rfl
  obtain ⟨N2, hN2⟩ := ih (a + (b - 1)) (by omega) a (b - 1) rfl
  refine ⟨N1 + N2, fun U hU hN => ?_⟩
  set E := U.filter (fun p => ∃ C ⊆ U, C.card = a - 1 ∧ Cup C ∧ p ∈ C ∧ ∀ q ∈ C, q.1 ≤ p.1)
    with hE
  have hEU : E ⊆ U := filter_subset _ _
  have hcard : (U \ E).card + E.card = U.card := by
    rw [card_sdiff_of_subset hEU]
    have := card_le_card hEU
    omega
  by_cases h1 : N1 ≤ (U \ E).card
  · rcases hN1 (U \ E) (gp_mono hU sdiff_subset) h1 with ⟨C, hCs, hCc, hCup⟩ | ⟨C, hCs, hCc, hCap⟩
    · exfalso
      have hne : C.Nonempty := by rw [← card_pos]; omega
      obtain ⟨p, hpC, hpmax⟩ := C.exists_max_image Prod.fst hne
      have hpUE := hCs hpC
      rw [mem_sdiff] at hpUE
      apply hpUE.2
      rw [hE, mem_filter]
      exact ⟨hpUE.1, C, hCs.trans sdiff_subset, hCc, hCup, hpC, hpmax⟩
    · exact Or.inr ⟨C, hCs.trans sdiff_subset, hCc, hCap⟩
  have h2 : N2 ≤ E.card := by omega
  rcases hN2 E (gp_mono hU hEU) h2 with ⟨C, hCs, hCc, hCup⟩ | ⟨C, hCs, hCc, hCap⟩
  · exact Or.inl ⟨C, hCs.trans hEU, hCc, hCup⟩
  -- a (b-1)-cap inside E
  have hne : C.Nonempty := by rw [← card_pos]; omega
  obtain ⟨p, hpC, hpmin⟩ := C.exists_min_image Prod.fst hne
  have hpE := hCs hpC
  rw [hE, mem_filter] at hpE
  obtain ⟨hpU, D', hD'U, hD'c, hD'cup, hpD', hpmax⟩ := hpE
  have hne1 : (D'.erase p).Nonempty := by
    rw [← card_pos, card_erase_of_mem hpD']; omega
  obtain ⟨q, hqD'', hqmax⟩ := (D'.erase p).exists_max_image Prod.fst hne1
  have hne2 : (C.erase p).Nonempty := by
    rw [← card_pos, card_erase_of_mem hpC]; omega
  obtain ⟨r, hrC', hrmin⟩ := (C.erase p).exists_min_image Prod.fst hne2
  have hqD' : q ∈ D' := mem_of_mem_erase hqD''
  have hqp : q ≠ p := ne_of_mem_erase hqD''
  have hrC : r ∈ C := mem_of_mem_erase hrC'
  have hrp : r ≠ p := ne_of_mem_erase hrC'
  have hCU : C ⊆ U := hCs.trans hEU
  have hqU := hD'U hqD'
  have hrU := hCU hrC
  have hqlt : q.1 < p.1 := fst_lt_of_le hU hqU hpU hqp (hpmax q hqD')
  have hplt : p.1 < r.1 := fst_lt_of_le hU hpU hrU (Ne.symm hrp) (hpmin r hrC)
  -- every other point of D' lies left of q, every other point of C right of r
  have hD'q : ∀ x ∈ D', x ≠ p → x ≠ q → x.1 < q.1 := fun x hx hxp hxq =>
    fst_lt_of_le hU (hD'U hx) hqU hxq (hqmax x (mem_erase.mpr ⟨hxp, hx⟩))
  have hD'p : ∀ x ∈ D', x ≠ p → x.1 < p.1 := fun x hx hxp =>
    fst_lt_of_le hU (hD'U hx) hpU hxp (hpmax x hx)
  have hCr : ∀ x ∈ C, x ≠ p → x ≠ r → r.1 < x.1 := fun x hx hxp hxr =>
    fst_lt_of_le hU hrU (hCU hx) (Ne.symm hxr) (hrmin x (mem_erase.mpr ⟨hxp, hx⟩))
  have hCp : ∀ x ∈ C, x ≠ p → p.1 < x.1 := fun x hx hxp =>
    fst_lt_of_le hU hpU (hCU hx) (Ne.symm hxp) (hpmin x hx)
  have hDne := hU.2 q hqU p hpU r hrU hqlt hplt
  rcases lt_or_gt_of_ne hDne with hneg | hpos
  · -- extend the cap by q on the left
    have claimB : ∀ z ∈ C, p.1 < z.1 → D q p z < 0 := by
      intro z hz hpz
      by_cases hzr : z = r
      · rw [hzr]; exact hneg
      have hzp : z ≠ p := fun e => by rw [e] at hpz; exact lt_irrefl _ hpz
      have hrz := hCr z hz hzp hzr
      exact neg_abd hqlt hplt hrz hneg (hCap p hpC r hrC z hz hplt hrz)
    have key : ∀ y ∈ C, ∀ z ∈ C, y.1 < z.1 → D q y z < 0 := by
      intro y hy z hz hyz
      by_cases hyp : y = p
      · rw [hyp] at hyz ⊢; exact claimB z hz hyz
      have hpy := hCp y hy hyp
      exact neg_acd hqlt hpy hyz (claimB y hy hpy) (hCap p hpC y hy z hz hpy hyz)
    have hqC : q ∉ C := fun h => by
      have := hpmin q h; linarith
    refine Or.inr ⟨insert q C, insert_subset hqU hCU, ?_, ?_⟩
    · rw [card_insert_of_notMem hqC]; omega
    · intro x hx y hy z hz hxy hyz
      have hlt : ∀ w ∈ C, q.1 < w.1 := fun w hw => by have := hpmin w hw; linarith
      rw [mem_insert] at hx hy hz
      rcases hy with rfl | hy
      · rcases hx with rfl | hx
        · exact absurd hxy (lt_irrefl _)
        · have := hlt x hx; linarith
      rcases hz with rfl | hz
      · have := hlt y hy; linarith
      rcases hx with rfl | hx
      · exact key y hy z hz hyz
      · exact hCap x hx y hy z hz hxy hyz
  · -- extend the cup by r on the right
    have claimA : ∀ x ∈ D', x.1 < p.1 → 0 < D x p r := by
      intro x hx hxp
      by_cases hxq : x = q
      · rw [hxq]; exact hpos
      have hxp' : x ≠ p := fun e => by rw [e] at hxp; exact lt_irrefl _ hxp
      have hxq' := hD'q x hx hxp' hxq
      exact pos_acd hxq' hqlt hplt (hD'cup x hx q hqD' p hpD' hxq' hqlt) hpos
    have key : ∀ x ∈ D', ∀ y ∈ D', x.1 < y.1 → 0 < D x y r := by
      intro x hx y hy hxy
      by_cases hyp : y = p
      · rw [hyp] at hxy ⊢; exact claimA x hx hxy
      have hyp' := hD'p y hy hyp
      exact pos_abd hxy hyp' hplt (hD'cup x hx y hy p hpD' hxy hyp') (claimA y hy hyp')
    have hrD : r ∉ D' := fun h => by
      have := hpmax r h; linarith
    refine Or.inl ⟨insert r D', insert_subset hrU hD'U, ?_, ?_⟩
    · rw [card_insert_of_notMem hrD]; omega
    · intro x hx y hy z hz hxy hyz
      have hlt : ∀ w ∈ D', w.1 < r.1 := fun w hw => by have := hpmax w hw; linarith
      rw [mem_insert] at hx hy hz
      rcases hy with rfl | hy
      · rcases hz with rfl | hz
        · exact absurd hyz (lt_irrefl _)
        · have := hlt z hz; linarith
      rcases hx with rfl | hx
      · have := hlt y hy; linarith
      rcases hz with rfl | hz
      · exact key x hx y hy hxy
      · exact hD'cup x hx y hy z hz hxy hyz

lemma enum (C : Finset (ℝ × ℝ)) (n : ℕ) (hinj : Set.InjOn Prod.fst (C : Set (ℝ × ℝ)))
    (hc : C.card = n) : ∃ e : Fin n → ℝ × ℝ, (∀ i, e i ∈ C) ∧ StrictMono (fun i => (e i).1) := by
  classical
  have hX : (C.image Prod.fst).card = n := by rw [card_image_of_injOn hinj, hc]
  let f := (C.image Prod.fst).orderEmbOfFin hX
  have hmem : ∀ i, ∃ p ∈ C, p.1 = f i := fun i => by
    have := (C.image Prod.fst).orderEmbOfFin_mem hX i
    obtain ⟨p, hp, hp1⟩ := mem_image.mp this
    exact ⟨p, hp, hp1⟩
  choose e he1 he2 using hmem
  refine ⟨e, he1, fun i j hij => ?_⟩
  simp only [he2]
  exact f.strictMono hij

end OMA.Erdos107SuH1

open OMA.Erdos107SuH1 in
theorem OMA.solution : OMA.R_Erdos107_variants_su_bound_R1_H1_R1.H1 := by
  intro k _
  obtain ⟨N, hN⟩ := es _ (2 * k + 1) (2 * k + 1) rfl
  refine ⟨max N (2 * k + 1), le_max_right _ _, ?_⟩
  intro U hU hinj hgp
  have hGP : GP U := ⟨hinj, fun a ha b hb c hc h1 h2 => hgp a ha b hb c hc h1 h2⟩
  rcases hN U hGP (by rw [hU]; exact le_max_left _ _) with ⟨C, hCs, hCc, hCup⟩ | ⟨C, hCs, hCc, hCap⟩
  · obtain ⟨e, he, hmono⟩ := enum C _ (hinj.mono (by exact_mod_cast hCs)) hCc
    refine ⟨true, e, fun i => hCs (he i), hmono, fun i j l hij hjl => ?_⟩
    simp only [if_true, one_mul]
    exact hCup _ (he i) _ (he j) _ (he l) (hmono hij) (hmono hjl)
  · obtain ⟨e, he, hmono⟩ := enum C _ (hinj.mono (by exact_mod_cast hCs)) hCc
    refine ⟨false, e, fun i => hCs (he i), hmono, fun i j l hij hjl => ?_⟩
    have := hCap _ (he i) _ (he j) _ (he l) (hmono hij) (hmono hjl)
    unfold D at this
    simp only [Bool.false_eq_true, if_false]
    linarith
