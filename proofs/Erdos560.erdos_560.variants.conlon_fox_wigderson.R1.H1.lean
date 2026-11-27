import OMAReductions.R_Erdos560_erdos_560_variants_conlon_fox_wigderson_R1
import Mathlib

/-! The size Ramsey number of K_{n,n} is O(n^3 2^n).

Credit: the whole argument is the merged proof of the catalogue variant
Erdos560.erdos_560.variants.upper_bound by @LordMike (pull request 1379 of open-math-agents),
which shows that the size Ramsey number of K_{n,n} is less than (3/2) n^3 2^n for n >= 1. It is
reused here unchanged (as OMA.upper_bound_reused); only the last few lines, which turn the
explicit bound into the O-statement of the hypothesis, are new. -/

namespace OMA
open Finset SimpleGraph

lemma choose_step (n x y : ℕ) (h : x ≤ y) :
    (x+1).choose n + y.choose n ≤ x.choose n + (y+1).choose n := by
  cases n with
  | zero => simp
  | succ m =>
    have e1 := Nat.choose_succ_succ x m
    have e2 := Nat.choose_succ_succ y m
    simp only [Nat.succ_eq_add_one] at e1 e2
    have := Nat.choose_le_choose m h
    omega

lemma choose_convex_up (n a : ℕ) (d : ℕ) (hd : (a+1)/2 ≤ d) (hda : d ≤ a) :
    ((a+1)/2).choose n + (a/2).choose n ≤ d.choose n + (a-d).choose n := by
  induction d, hd using Nat.le_induction with
  | base =>
    have : a - (a+1)/2 = a/2 := by omega
    rw [this]
  | succ d hd ih =>
    have h1 := ih (by omega)
    have h2 := choose_step n (a-(d+1)) d (by omega)
    have : a - (d+1) + 1 = a - d := by omega
    rw [this] at h2
    omega

lemma choose_convex (n a d : ℕ) (hda : d ≤ a) :
    ((a+1)/2).choose n + (a/2).choose n ≤ d.choose n + (a-d).choose n := by
  rcases le_or_gt ((a+1)/2) d with h | h
  · exact choose_convex_up n a d h hda
  · have := choose_convex_up n a (a-d) (by omega) (by omega)
    have h2 : a - (a-d) = d := by omega
    rw [h2] at this; omega

lemma mono_of_count {n a b : ℕ} (G : SimpleGraph (Fin (a+b))) (N : Fin b → Finset (Fin a))
    (hN : ∀ v, ∀ u ∈ N v, G.Adj (Fin.castAdd b u) (Fin.natAdd a v))
    (hcount : (n-1) * a.choose n < ∑ v, ((N v).card.choose n)) :
    (completeBipartiteGraph (Fin n) (Fin n)).IsContained G := by
  classical
  have h1 : ∑ v, ((N v).card.choose n) = ∑ S ∈ powersetCard n (univ : Finset (Fin a)),
      (univ.filter fun v => S ⊆ N v).card := by
    have : ∀ v, (N v).card.choose n =
        ((powersetCard n (univ : Finset (Fin a))).filter fun S => S ⊆ N v).card := by
      intro v
      rw [← card_powersetCard]
      congr 1
      ext S
      simp only [mem_powersetCard, mem_filter, subset_univ, true_and]
      tauto
    simp_rw [this, card_filter]
    rw [sum_comm]
  obtain ⟨S, hS, hlt⟩ : ∃ S ∈ powersetCard n (univ : Finset (Fin a)),
      n - 1 < (univ.filter fun v => S ⊆ N v).card := by
    by_contra hcon
    push Not at hcon
    have := sum_le_sum hcon
    rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul] at this
    rw [h1] at hcount
    linarith [mul_comm (a.choose n) (n-1)]
  have hScard : S.card = n := (mem_powersetCard.mp hS).2
  obtain ⟨T, hTsub, hTcard⟩ := exists_subset_card_eq
    (show n ≤ (univ.filter fun v => S ⊆ N v).card by omega)
  have hadj : ∀ i j, G.Adj (Fin.castAdd b (S.orderEmbOfFin hScard i))
      (Fin.natAdd a (T.orderEmbOfFin hTcard j)) := by
    intro i j
    apply hN
    have hj : T.orderEmbOfFin hTcard j ∈ T := orderEmbOfFin_mem T hTcard j
    have := (mem_filter.mp (hTsub hj)).2
    exact this (orderEmbOfFin_mem S hScard i)
  refine ⟨⟨⟨fun x => Sum.elim (fun i => Fin.castAdd b (S.orderEmbOfFin hScard i))
    (fun j => Fin.natAdd a (T.orderEmbOfFin hTcard j)) x, ?_⟩, ?_⟩⟩
  · rintro (i | i) (j | j) h
    · simp at h
    · exact hadj i j
    · exact (hadj j i).symm
    · simp at h
  · rintro (i | i) (j | j) h
    · simp only [RelHom.coeFn_mk, Sum.elim_inl] at h
      have := (S.orderEmbOfFin hScard).injective (Fin.castAdd_injective _ _ h)
      rw [this]
    · simp only [RelHom.coeFn_mk, Sum.elim_inl, Sum.elim_inr] at h
      have := congrArg Fin.val h
      simp at this
      omega
    · simp only [RelHom.coeFn_mk, Sum.elim_inl, Sum.elim_inr] at h
      have := congrArg Fin.val h
      simp at this
      omega
    · simp only [RelHom.coeFn_mk, Sum.elim_inr] at h
      have := (T.orderEmbOfFin hTcard).injective (Fin.natAdd_injective _ _ h)
      rw [this]

def KAB (a b : ℕ) : SimpleGraph (Fin (a+b)) where
  Adj i j := (i.val < a ∧ a ≤ j.val) ∨ (j.val < a ∧ a ≤ i.val)
  symm := ⟨fun i j h => Or.symm h⟩
  loopless := ⟨fun i h => by omega⟩

lemma KAB_edges (a b : ℕ) : (KAB a b).edgeSet.ncard ≤ a * b := by
  have hsub : (KAB a b).edgeSet ⊆
      (fun p : Fin a × Fin b => s(Fin.castAdd b p.1, Fin.natAdd a p.2)) '' Set.univ := by
    intro e
    induction e using Sym2.ind with
    | _ i j =>
      intro h
      rw [mem_edgeSet] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨(⟨i, h1⟩, ⟨j - a, by omega⟩), trivial, ?_⟩
        have e1 : Fin.castAdd b (⟨i, h1⟩ : Fin a) = i := Fin.ext rfl
        have e2 : Fin.natAdd a (⟨j - a, by omega⟩ : Fin b) = j :=
          Fin.ext (by show a + (j.val - a) = j.val; omega)
        show s(Fin.castAdd b (⟨i, h1⟩ : Fin a), Fin.natAdd a (⟨j - a, by omega⟩ : Fin b)) = s(i, j)
        rw [e1, e2]
      · refine ⟨(⟨j, h1⟩, ⟨i - a, by omega⟩), trivial, ?_⟩
        have e1 : Fin.castAdd b (⟨j, h1⟩ : Fin a) = j := Fin.ext rfl
        have e2 : Fin.natAdd a (⟨i - a, by omega⟩ : Fin b) = i :=
          Fin.ext (by show a + (i.val - a) = i.val; omega)
        show s(Fin.castAdd b (⟨j, h1⟩ : Fin a), Fin.natAdd a (⟨i - a, by omega⟩ : Fin b)) = s(i, j)
        rw [e1, e2, Sym2.eq_swap]
  calc (KAB a b).edgeSet.ncard ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Set.univ : Set (Fin a × Fin b)).ncard := Set.ncard_image_le
    _ = a * b := by simp [Set.ncard_univ]

lemma ramsey {n a b : ℕ}
    (H : 2*(n-1)*a.choose n < b*(((a+1)/2).choose n + (a/2).choose n))
    (R : SimpleGraph (Fin (a+b))) (_hR : R ≤ KAB a b) :
    (completeBipartiteGraph (Fin n) (Fin n)).IsContained R ∨
      (completeBipartiteGraph (Fin n) (Fin n)).IsContained (KAB a b \ R) := by
  classical
  let Nr : Fin b → Finset (Fin a) := fun v =>
    univ.filter fun u => R.Adj (Fin.castAdd b u) (Fin.natAdd a v)
  let Nb : Fin b → Finset (Fin a) := fun v =>
    univ.filter fun u => ¬ R.Adj (Fin.castAdd b u) (Fin.natAdd a v)
  have hsum : ∀ v, ((a+1)/2).choose n + (a/2).choose n ≤
      (Nr v).card.choose n + (Nb v).card.choose n := by
    intro v
    have h0 := card_filter_add_card_filter_not (s := (univ : Finset (Fin a)))
      (fun u => R.Adj (Fin.castAdd b u) (Fin.natAdd a v))
    rw [card_univ, Fintype.card_fin] at h0
    have : (Nb v).card = a - (Nr v).card := by
      show (univ.filter _).card = a - (univ.filter _).card
      omega
    rw [this]
    exact choose_convex n a _ (by show (univ.filter _).card ≤ a; omega)
  have htot : b * (((a+1)/2).choose n + (a/2).choose n) ≤
      ∑ v, (Nr v).card.choose n + ∑ v, (Nb v).card.choose n := by
    rw [← sum_add_distrib]
    calc b * (((a+1)/2).choose n + (a/2).choose n)
        = ∑ _v : Fin b, (((a+1)/2).choose n + (a/2).choose n) := by simp
      _ ≤ _ := sum_le_sum fun v _ => hsum v
  have H' : 2*((n-1)*a.choose n) < b*(((a+1)/2).choose n + (a/2).choose n) := by
    rw [← mul_assoc]; exact H
  by_cases hr : (n-1)*a.choose n < ∑ v, (Nr v).card.choose n
  · left
    exact mono_of_count R Nr (fun v u hu => (mem_filter.mp hu).2) hr
  · right
    refine mono_of_count _ Nb (fun v u hu => ?_) (by push Not at hr; linarith)
    rw [sdiff_adj]
    refine ⟨Or.inl ?_, (mem_filter.mp hu).2⟩
    simp

lemma sizeRamsey_le {n a b : ℕ}
    (H : 2*(n-1)*a.choose n < b*(((a+1)/2).choose n + (a/2).choose n)) :
    sizeRamsey (completeBipartiteGraph (Fin n) (Fin n))
      (completeBipartiteGraph (Fin n) (Fin n)) ≤ a * b := by
  have hmem : (KAB a b).edgeSet.ncard ∈ { m | ∃ (N : ℕ) (F : SimpleGraph (Fin N)),
      F.edgeSet.ncard = m ∧ ∀ (R : SimpleGraph (Fin N)), R ≤ F →
        (completeBipartiteGraph (Fin n) (Fin n)).IsContained R ∨
        (completeBipartiteGraph (Fin n) (Fin n)).IsContained (F \ R) } :=
    ⟨a+b, KAB a b, rfl, fun R hR => ramsey H R hR⟩
  exact (Nat.sInf_le hmem).trans (KAB_edges a b)

lemma sizeRamsey_le' {n a b : ℕ}
    (H : 2*(n-1)*a.descFactorial n <
      b*(((a+1)/2).descFactorial n + (a/2).descFactorial n)) :
    sizeRamsey (completeBipartiteGraph (Fin n) (Fin n))
      (completeBipartiteGraph (Fin n) (Fin n)) ≤ a * b := by
  apply sizeRamsey_le
  simp only [Nat.descFactorial_eq_factorial_mul_choose] at H
  have hpos := Nat.factorial_pos n
  have : n.factorial * (2*(n-1)*a.choose n) <
      n.factorial * (b*(((a+1)/2).choose n + (a/2).choose n)) := by
    calc _ = 2*(n-1)*(n.factorial * a.choose n) := by ring
      _ < _ := H
      _ = _ := by ring
  exact lt_of_mul_lt_mul_left this (Nat.zero_le _)

lemma key (n h : ℕ) (hn : 40 ≤ n) (hh : n^2 ≤ 4*h + 3) :
    (2*h).descFactorial n ≤ 3 * 2^n * h.descFactorial n := by
  have hnh : n < h := by nlinarith
  have hnR : (40:ℝ) ≤ n := by exact_mod_cast hn
  have hhR : (n:ℝ)^2 ≤ 4*h + 3 := by exact_mod_cast hh
  have hnhR : (n:ℝ) < h := by exact_mod_cast hnh
  have e1 : ((2*h).descFactorial n : ℝ) = ∏ i ∈ range n, ((2*h:ℝ) - i) := by
    rw [Nat.descFactorial_eq_prod_range]
    push_cast
    apply prod_congr rfl
    intro i hi
    have := mem_range.mp hi
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have e2 : (2:ℝ)^n * (h.descFactorial n : ℝ) = ∏ i ∈ range n, ((2*h:ℝ) - 2*i) := by
    rw [Nat.descFactorial_eq_prod_range]
    push_cast
    rw [show (2:ℝ)^n = ∏ _i ∈ range n, (2:ℝ) by simp, ← prod_mul_distrib]
    apply prod_congr rfl
    intro i hi
    have := mem_range.mp hi
    rw [Nat.cast_sub (by omega)]
    ring
  have ht : (0:ℝ) < 2*((h:ℝ)-n) := by linarith
  have hfac : ∀ i ∈ range n, ((2*h:ℝ) - i) ≤
      ((2*h:ℝ) - 2*i) * Real.exp ((i:ℝ) / (2*((h:ℝ)-n))) := by
    intro i hi
    have hi1 : (i:ℝ) < n := by exact_mod_cast mem_range.mp hi
    have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg i
    have hd : (0:ℝ) < 2*h - 2*i := by linarith
    have h1 : (i:ℝ) / (2*h - 2*i) ≤ (i:ℝ) / (2*((h:ℝ)-n)) :=
      div_le_div_of_nonneg_left hi0 ht (by linarith)
    have h2 : 1 + (i:ℝ) / (2*h - 2*i) ≤ Real.exp ((i:ℝ) / (2*((h:ℝ)-n))) := by
      have := Real.add_one_le_exp ((i:ℝ) / (2*((h:ℝ)-n)))
      linarith
    have hc : ((2*h:ℝ) - 2*i) * ((i:ℝ) / (2*h - 2*i)) = i := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ hd.ne.symm
    calc ((2*h:ℝ) - i) = (2*h - 2*i) * (1 + (i:ℝ) / (2*h - 2*i)) := by
          rw [mul_add, hc]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hd.le
  have gs : ∀ m : ℕ, ∑ i ∈ range m, (i:ℝ) = m*(m-1)/2 := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring
  have hprod : ∏ i ∈ range n, ((2*h:ℝ) - i) ≤
      (∏ i ∈ range n, ((2*h:ℝ) - 2*i)) * Real.exp ((n:ℝ)*(n-1)/2 / (2*((h:ℝ)-n))) := by
    calc ∏ i ∈ range n, ((2*h:ℝ) - i)
        ≤ ∏ i ∈ range n, (((2*h:ℝ) - 2*i) * Real.exp ((i:ℝ) / (2*((h:ℝ)-n)))) := by
          apply prod_le_prod
          · intro i hi
            have hi1 : (i:ℝ) < n := by exact_mod_cast mem_range.mp hi
            linarith
          · exact hfac
      _ = _ := by
          rw [prod_mul_distrib, ← Real.exp_sum, ← sum_div, gs]
  have hexp : Real.exp ((n:ℝ)*(n-1)/2 / (2*((h:ℝ)-n))) ≤ 3 := by
    have hE : (n:ℝ)*(n-1)/2 / (2*((h:ℝ)-n)) ≤ 1 + 9/100 := by
      rw [div_le_iff₀ ht]
      nlinarith
    have h9 : Real.exp (9/100 : ℝ) ≤ 100/91 := by
      have h := Real.add_one_le_exp (-(9/100) : ℝ)
      rw [Real.exp_neg] at h
      have hp := Real.exp_pos (9/100 : ℝ)
      rw [le_div_iff₀ (by norm_num)]
      have : (91/100:ℝ) * Real.exp (9/100) ≤ 1 := by
        calc (91/100:ℝ) * Real.exp (9/100) ≤ (Real.exp (9/100))⁻¹ * Real.exp (9/100) :=
              mul_le_mul_of_nonneg_right (by linarith) hp.le
          _ = 1 := inv_mul_cancel₀ hp.ne.symm
      linarith
    calc Real.exp ((n:ℝ)*(n-1)/2 / (2*((h:ℝ)-n))) ≤ Real.exp (1 + 9/100) :=
          Real.exp_le_exp.mpr hE
      _ = Real.exp 1 * Real.exp (9/100) := Real.exp_add _ _
      _ ≤ 2.7182818286 * (100/91) :=
          mul_le_mul Real.exp_one_lt_d9.le h9 (Real.exp_pos _).le (by norm_num)
      _ ≤ 3 := by norm_num
  have hpos : (0:ℝ) ≤ ∏ i ∈ range n, ((2*h:ℝ) - 2*i) := by
    apply prod_nonneg
    intro i hi
    have hi1 : (i:ℝ) < n := by exact_mod_cast mem_range.mp hi
    linarith
  have hfin : ((2*h).descFactorial n : ℝ) ≤ 3 * 2^n * (h.descFactorial n : ℝ) := by
    rw [e1, mul_assoc, e2]
    calc _ ≤ _ := hprod
      _ ≤ (∏ i ∈ range n, ((2*h:ℝ) - 2*i)) * 3 := mul_le_mul_of_nonneg_left hexp hpos
      _ = _ := by ring
  exact_mod_cast hfin

lemma arith_large (n : ℕ) (hn : 40 ≤ n) : ∃ a b : ℕ,
    2*(n-1)*a.descFactorial n < b*(((a+1)/2).descFactorial n + (a/2).descFactorial n) ∧
    2*a*b < 3*n^3*2^n := by
  have hdiv : n^2 ≤ 4*(n^2/4) + 3 := by omega
  have hle : 4*(n^2/4) ≤ n^2 := by omega
  generalize n^2/4 = h at hdiv hle
  have hk := key n h hn hdiv
  have hnh : n ≤ h := by nlinarith
  have hD : 0 < h.descFactorial n := Nat.descFactorial_pos.mpr hnh
  have hp : 1 ≤ 2^n := Nat.one_le_two_pow
  refine ⟨2*h, 3*n*2^n - 1, ?_, ?_⟩
  · have e1 : (2*h+1)/2 = h := by omega
    have e2 : 2*h/2 = h := by omega
    rw [e1, e2]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hp2 : 1 ≤ 2^(m+1) := Nat.one_le_two_pow
    have e3 : 3*(m+1)*2^(m+1) - 1 = 3*m*2^(m+1) + (3*2^(m+1) - 1) := by
      have : 3*(m+1)*2^(m+1) = 3*m*2^(m+1) + 3*2^(m+1) := by ring
      omega
    rw [e3, Nat.add_sub_cancel]
    calc 2*m*(2*h).descFactorial (m+1) ≤ 2*m*(3 * 2^(m+1) * h.descFactorial (m+1)) :=
          Nat.mul_le_mul_left _ hk
      _ = 3*m*2^(m+1) * (h.descFactorial (m+1) + h.descFactorial (m+1)) := by ring
      _ < (3*m*2^(m+1) + (3*2^(m+1) - 1)) *
            (h.descFactorial (m+1) + h.descFactorial (m+1)) := by
          apply Nat.mul_lt_mul_of_pos_right <;> omega
  · have hq : 1 ≤ 3*n*2^n := by nlinarith
    have hn2 : 0 < n^2 := by positivity
    have : 4*h*(3*n*2^n - 1) < 3*n^3*2^n := by
      calc 4*h*(3*n*2^n - 1) ≤ n^2*(3*n*2^n - 1) := Nat.mul_le_mul_right _ hle
        _ < n^2*(3*n*2^n) := Nat.mul_lt_mul_of_pos_left (by omega) hn2
        _ = _ := by ring
    calc 2*(2*h)*(3*n*2^n - 1) = 4*h*(3*n*2^n - 1) := by ring
      _ < _ := this

lemma arith (n : ℕ) (hn : 1 ≤ n) : ∃ a b : ℕ,
    2*(n-1)*a.descFactorial n < b*(((a+1)/2).descFactorial n + (a/2).descFactorial n) ∧
    2*a*b < 3*n^3*2^n := by
  rcases le_or_gt 40 n with h | h
  · exact arith_large n h
  interval_cases n
  · exact ⟨1, 1, by decide +kernel, by decide +kernel⟩
  · exact ⟨3, 7, by decide +kernel, by decide +kernel⟩
  · exact ⟨7, 29, by decide +kernel, by decide +kernel⟩
  · exact ⟨11, 100, by decide +kernel, by decide +kernel⟩
  · exact ⟨17, 273, by decide +kernel, by decide +kernel⟩
  · exact ⟨23, 729, by decide +kernel, by decide +kernel⟩
  · exact ⟨31, 1766, by decide +kernel, by decide +kernel⟩
  · exact ⟨41, 4061, by decide +kernel, by decide +kernel⟩
  · exact ⟨51, 9420, by decide +kernel, by decide +kernel⟩
  · exact ⟨61, 21818, by decide +kernel, by decide +kernel⟩
  · exact ⟨73, 48888, by decide +kernel, by decide +kernel⟩
  · exact ⟨87, 107114, by decide +kernel, by decide +kernel⟩
  · exact ⟨101, 235662, by decide +kernel, by decide +kernel⟩
  · exact ⟨115, 518853, by decide +kernel, by decide +kernel⟩
  · exact ⟨131, 1123709, by decide +kernel, by decide +kernel⟩
  · exact ⟨149, 2403819, by decide +kernel, by decide +kernel⟩
  · exact ⟨167, 5155384, by decide +kernel, by decide +kernel⟩
  · exact ⟨185, 11067291, by decide +kernel, by decide +kernel⟩
  · exact ⟨205, 23526690, by decide +kernel, by decide +kernel⟩
  · exact ⟨227, 49623772, by decide +kernel, by decide +kernel⟩
  · exact ⟨249, 104853151, by decide +kernel, by decide +kernel⟩
  · exact ⟨271, 221746924, by decide +kernel, by decide +kernel⟩
  · exact ⟨295, 465916010, by decide +kernel, by decide +kernel⟩
  · exact ⟨321, 973690569, by decide +kernel, by decide +kernel⟩
  · exact ⟨347, 2037473339, by decide +kernel, by decide +kernel⟩
  · exact ⟨373, 4266682193, by decide +kernel, by decide +kernel⟩
  · exact ⟨401, 8893616439, by decide +kernel, by decide +kernel⟩
  · exact ⟨431, 18465398503, by decide +kernel, by decide +kernel⟩
  · exact ⟨461, 38376456426, by decide +kernel, by decide +kernel⟩
  · exact ⟨491, 79807975814, by decide +kernel, by decide +kernel⟩
  · exact ⟨523, 165396068661, by decide +kernel, by decide +kernel⟩
  · exact ⟨557, 341744457690, by decide +kernel, by decide +kernel⟩
  · exact ⟨591, 706665403395, by decide +kernel, by decide +kernel⟩
  · exact ⟨625, 1462036541719, by decide +kernel, by decide +kernel⟩
  · exact ⟨661, 3016736088956, by decide +kernel, by decide +kernel⟩
  · exact ⟨699, 6209979415462, by decide +kernel, by decide +kernel⟩
  · exact ⟨737, 12791308737012, by decide +kernel, by decide +kernel⟩
  · exact ⟨775, 26359486876553, by decide +kernel, by decide +kernel⟩
  · exact ⟨815, 54203698889348, by decide +kernel, by decide +kernel⟩

end OMA

theorem OMA.upper_bound_reused : type_of% @Erdos560.erdos_560.variants.upper_bound := by
  intro n hn
  obtain ⟨a, b, H, hab⟩ := OMA.arith n hn
  have h1 := OMA.sizeRamsey_le' H
  have h2 : ((SimpleGraph.sizeRamsey (completeBipartiteGraph (Fin n) (Fin n))
      (completeBipartiteGraph (Fin n) (Fin n)) : ℕ) : ℝ) ≤ (a:ℝ) * b := by exact_mod_cast h1
  have h3 : (2:ℝ)*a*b < 3*(n:ℝ)^3*2^n := by exact_mod_cast hab
  linarith

theorem OMA.solution : OMA.R_Erdos560_erdos_560_variants_conlon_fox_wigderson_R1.H1 := by
  unfold OMA.R_Erdos560_erdos_560_variants_conlon_fox_wigderson_R1.H1
  apply Asymptotics.IsBigO.of_bound (3 / 2)
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h := OMA.upper_bound_reused n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  linarith
