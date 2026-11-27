import FormalConjectures.ErdosProblems.«1109»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Konyagin's lower bound for squarefree sums

Mathematical source is S. V. Konyagin, *Problems on the set of squarefree numbers*,
Theorem 3 and Sections 4, 6 and 7. DOI 10.1070/IM2004v068n03ABEH000486.

The proof uses a random choice of signs on opposite residues, quantitative
Chinese remainder counts, and truncated inclusion–exclusion. The greedy
extension checks the sum of a candidate with itself as well as every sum with
an already chosen element.
-/

open Finset Filter Asymptotics Real
open scoped Pointwise BigOperators

namespace SquarefreeSums

theorem card_le_f {A : Finset ℕ} {N : ℕ} (hA : A ⊆ Icc 1 N)
    (hgood : ∀ a ∈ A, ∀ b ∈ A, Squarefree (a + b)) : A.card ≤ Erdos1109.f N := by
  unfold Erdos1109.f
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro _ ⟨B, hB, -, rfl⟩
    simpa using card_le_card hB
  · exact ⟨A, hA, fun n hn => by
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hn
      exact hgood a ha b hb, rfl⟩

theorem count_congruence {Q d : ℕ} (S : Finset ℕ)
    (hS : ∀ a ∈ S, a ≤ Q) (hmod : ∀ a ∈ S, ∀ b ∈ S, a ≡ b [MOD d]) :
    S.card ≤ Q / d + 1 := by
  rw [← card_range (Q / d + 1)]
  apply card_le_card_of_injOn (fun a => a / d)
  · intro a ha
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (hS a ha)))
  · intro a ha b hb heq
    change a / d = b / d at heq
    have h := hmod a ha b hb
    change a % d = b % d at h
    have ha' := Nat.mod_add_div a d
    have hb' := Nat.mod_add_div b d
    rw [h, heq, hb'] at ha'
    exact ha'.symm

theorem inv_sq_le_sub (k : ℕ) (hk : 1 < k) :
    1 / (k : ℝ) ^ 2 ≤ 1 / ((k : ℝ) - 1) - 1 / (k : ℝ) := by
  have h : (1 : ℝ) < k := by exact_mod_cast hk
  have hp : (0 : ℝ) < k := by linarith
  have hm : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  field_simp
  nlinarith

theorem sum_inv_sq_ge_three (N : ℕ) (hN : 3 ≤ N) :
    ∑ p ∈ Icc 3 N, (1 / (p : ℝ) ^ 2) ≤ 4 / 9 - 1 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num [show Icc (3 : ℕ) 3 = {3} by simp]
  | succ n hn ih =>
    rw [sum_Icc_succ_top (by omega : 3 ≤ n + 1)]
    have hk := inv_sq_le_sub (n + 1) (by omega)
    push_cast at hk ⊢
    rw [show ((n : ℝ) + 1) - 1 = n by ring] at hk
    linarith

noncomputable def primeTail (y X : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE X).filter (y < ·), 1 / (p : ℝ) ^ 2

theorem prime_shell {C : ℝ} (hC : 0 ≤ C) {y X : ℕ} (hy : 2 ≤ y)
    (hπ : (Nat.primeCounting (2 * y) : ℝ) ≤ C * (2 * (y : ℝ)) / log (2 * (y : ℝ))) :
    ∑ p ∈ ((Nat.primesLE X).filter (y < ·)).filter (· ≤ 2 * y), (1 / (p : ℝ) ^ 2)
      ≤ 2 * C / ((y : ℝ) * log y) := by
  let P := ((Nat.primesLE X).filter (y < ·)).filter (· ≤ 2 * y)
  have hpos : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hy0 : (0 : ℝ) < y := by linarith
  have hlog := log_pos hpos
  have hl : log (y : ℝ) ≤ log (2 * (y : ℝ)) := log_le_log hy0 (by linarith)
  have hsize : P.card ≤ Nat.primeCounting (2 * y) := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    apply card_le_card
    intro p hp
    have hm := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨hm.2, (Nat.mem_primesLE.mp (mem_filter.mp hm.1).1).2⟩
  calc
    _ ≤ ∑ _p ∈ P, (1 / (y : ℝ) ^ 2) := sum_le_sum (by
      intro p hp
      have h : (y : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp (mem_filter.mp hp).1).2.le
      gcongr)
    _ = P.card * (1 / (y : ℝ) ^ 2) := by simp
    _ ≤ (C * (2 * (y : ℝ)) / log (2 * (y : ℝ))) * (1 / (y : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right ((by exact_mod_cast hsize : (P.card : ℝ) ≤
        Nat.primeCounting (2 * y)).trans hπ) (by positivity)
    _ ≤ (C * (2 * (y : ℝ)) / log (y : ℝ)) * (1 / (y : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact div_le_div_of_nonneg_left (by positivity) hlog hl
    _ = _ := by field_simp

theorem prime_tail_bound {C : ℝ} (hC : 0 ≤ C) {Y : ℕ} (hY : 2 ≤ Y)
    (hπ : ∀ n : ℕ, Y ≤ n → (Nat.primeCounting n : ℝ) ≤ C * n / log n)
    (X y : ℕ) (hy : Y ≤ y) :
    primeTail y X ≤ 4 * C / ((y : ℝ) * log y) := by
  suffices hs : ∀ k X y : ℕ, X - y = k → Y ≤ y →
      primeTail y X ≤ 4 * C / ((y : ℝ) * log y) by
    exact hs (X - y) X y rfl hy
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro X y hk hy
    have hy2 : 2 ≤ y := hY.trans hy
    have hy0 : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
    have hlog : 0 < log (y : ℝ) := log_pos (by exact_mod_cast (show 1 < y by omega))
    have hπ' : (Nat.primeCounting (2 * y) : ℝ) ≤ C * (2 * (y : ℝ)) / log (2 * (y : ℝ)) := by
      exact_mod_cast hπ (2 * y) (by omega)
    have hsh := prime_shell hC hy2 (X := X) hπ'
    classical
    let P := (Nat.primesLE X).filter (y < ·)
    have hfilter : P.filter (fun p => ¬ p ≤ 2 * y) = (Nat.primesLE X).filter (2 * y < ·) := by
      ext p
      simp only [P, mem_filter, not_le]
      constructor
      · exact fun h => ⟨h.1.1, h.2⟩
      · exact fun h => ⟨⟨h.1, by omega⟩, h.2⟩
    have hsplit : primeTail y X =
        (∑ p ∈ P.filter (· ≤ 2 * y), (1 / (p : ℝ) ^ 2)) + primeTail (2 * y) X := by
      unfold primeTail
      rw [← hfilter]
      exact (sum_filter_add_sum_filter_not P (· ≤ 2 * y) _).symm
    rw [hsplit]
    by_cases hX : X ≤ 2 * y
    · have hzero : primeTail (2 * y) X = 0 := by
        unfold primeTail
        apply sum_eq_zero
        intro p hp
        have hp₁ := (mem_filter.mp hp).2
        have hp₂ := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).1
        omega
      rw [hzero, add_zero]
      exact hsh.trans (by gcongr; linarith)
    · have hhalf := ih (X - 2 * y) (by omega) X (2 * y) rfl (by omega)
      have hl : log (y : ℝ) ≤ log (2 * (y : ℝ)) := log_le_log hy0 (by linarith)
      have hh : primeTail (2 * y) X ≤ 2 * C / ((y : ℝ) * log y) :=
        hhalf.trans (calc
          _ = 2 * C / ((y : ℝ) * log (2 * (y : ℝ))) := by push_cast; ring
          _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr))
      calc
        _ ≤ 2 * C / ((y : ℝ) * log y) + 2 * C / ((y : ℝ) * log y) := add_le_add hsh hh
        _ = _ := by ring

theorem prime_square_le_of_odd_sum {N a b p : ℕ} (ha : a ∈ Icc 1 N) (hb : b ∈ Icc 1 N)
    (hao : Odd a) (hbo : Odd b) (hpo : Odd p) (hd : p * p ∣ a + b) :
    p * p ≤ N := by
  obtain ⟨ha₁, ha₂⟩ := mem_Icc.mp ha
  obtain ⟨hb₁, hb₂⟩ := mem_Icc.mp hb
  by_contra! hbig
  obtain ⟨k, hk⟩ := hd
  have hk₀ : k ≠ 0 := by intro hz; simp [hz] at hk; omega
  have hk₂ : ¬ 2 ≤ k := by
    intro h
    have hm := Nat.mul_le_mul_left (p * p) h
    omega
  have hk₁ : k = 1 := by omega
  rw [hk₁, mul_one] at hk
  have he : Even (a + b) := hao.add_odd hbo
  obtain ⟨u, hu⟩ := hpo.mul hpo
  obtain ⟨v, hv⟩ := he
  omega

theorem good_pair_of_sieved {N y a b : ℕ} (hy : 2 ≤ y) (ha : a ∈ Icc 1 N)
    (hb : b ∈ Icc 1 N) (hao : Odd a) (hbo : Odd b)
    (hsmall : ∀ p ∈ Nat.primesLE y, ¬ p * p ∣ a + b)
    (hlarge : ∀ p ∈ (Nat.primesLE (Nat.sqrt N)).filter (y < ·), ¬ p * p ∣ a + b) :
    Squarefree (a + b) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hd
  by_cases hpy : p ≤ y
  · exact hsmall _ (Nat.mem_primesLE.mpr ⟨hpy, hp⟩) hd
  · have hpo : Odd p := hp.odd_of_ne_two (by omega)
    have hps := prime_square_le_of_odd_sum ha hb hao hbo hpo hd
    have hle : p ≤ Nat.sqrt N := Nat.le_sqrt.mpr hps
    exact hlarge _ (mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hle, hp⟩, by omega⟩) hd

/-- A pool with enough eligible extensions gives a set of the required size. -/
theorem greedy_bound {N K y : ℕ} (hy : 2 ≤ y) (S : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hOdd : ∀ a ∈ S, Odd a)
    (hsmall : ∀ a ∈ S, ∀ b ∈ S, ∀ p ∈ Nat.primesLE y, ¬ p * p ∣ a + b)
    (hroom : ∀ A : Finset ℕ, A ⊆ S → A.card < K →
      A.card < (S.filter fun a => ∀ b ∈ insert a A,
        ∀ p ∈ (Nat.primesLE (Nat.sqrt N)).filter (y < ·), ¬ p * p ∣ a + b).card) :
    K ≤ Erdos1109.f N := by
  classical
  let good := S.powerset.filter fun A => ∀ a ∈ A, ∀ b ∈ A, Squarefree (a + b)
  obtain ⟨A, hA, hmax⟩ := exists_max_image good Finset.card (by
    refine ⟨∅, ?_⟩
    simp [good])
  have hAS : A ⊆ S := mem_powerset.mp (mem_filter.mp hA).1
  have hgood := (mem_filter.mp hA).2
  suffices K ≤ A.card from this.trans (card_le_f (hAS.trans hS) hgood)
  by_contra! hAcard
  have hcount := hroom A hAS hAcard
  have hnsub : ¬ (S.filter fun a => ∀ b ∈ insert a A,
      ∀ p ∈ (Nat.primesLE (Nat.sqrt N)).filter (y < ·), ¬ p * p ∣ a + b) ⊆ A :=
    fun h => (not_le_of_gt hcount) (card_le_card h)
  have ⟨a, ha, hnot⟩ := not_subset.mp hnsub
  obtain ⟨has, halarge⟩ := mem_filter.mp ha
  have hpairs : ∀ b ∈ insert a A, Squarefree (a + b) := by
    intro b hb
    have hbs := (insert_subset has hAS) hb
    exact good_pair_of_sieved hy (hS has) (hS hbs) (hOdd _ has) (hOdd _ hbs)
      (hsmall _ has _ hbs) (halarge _ hb)
  have hins : insert a A ∈ good := by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (insert_subset has hAS), ?_⟩
    intro b hb c hc
    rcases mem_insert.mp hb with hba | hb
    · subst b
      rcases mem_insert.mp hc with hca | hc
      · subst c
        exact hpairs _ (mem_insert_self _ _)
      · exact hpairs _ (mem_insert_of_mem hc)
    · rcases mem_insert.mp hc with hca | hc
      · subst c
        simpa [add_comm] using hpairs b (mem_insert_of_mem hb)
      · exact hgood _ hb _ hc
  have hle := hmax _ hins
  rw [card_insert_of_notMem hnot] at hle
  omega

theorem exact_of_eventual_card {K : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hK : ∀ᶠ N : ℕ in atTop, c * (log (log N) * (log N) ^ 2) ≤ (K N : ℝ))
    (hbound : ∀ᶠ N in atTop, K N ≤ Erdos1109.f N) :
    type_of% @Erdos1109.erdos_1109.variants.konyagin_lower := by
  refine IsBigO.of_bound c⁻¹ ?_
  have hlog : Tendsto (fun N : ℕ => log (log N)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hlog.eventually_ge_atTop 0, hK, hbound] with N hn hscale hf
  have hfc : (K N : ℝ) ≤ (Erdos1109.f N : ℝ) := by exact_mod_cast hf
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg hn (sq_nonneg _)), abs_of_nonneg (by positivity)]
  simpa [div_eq_inv_mul] using (le_div_iff₀ hc).mpr (by
    simpa [mul_comm] using hscale.trans hfc)

theorem truncated_choose {α : Type*} (T : Finset α) (k : ℕ) :
    ∑ D ∈ T.powerset.filter (fun D => D.card ≤ k), (-1 : ℤ) ^ D.card =
      ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * T.card.choose j := by
  let P := T.powerset.filter (fun D => D.card ≤ k)
  have hmaps : ∀ D ∈ P, D.card ∈ range (k + 1) := by
    intro D hD
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hD).2)
  calc
    _ = ∑ j ∈ range (k + 1), ∑ D ∈ P.filter (fun D => D.card = j), (-1 : ℤ) ^ D.card :=
      (sum_fiberwise_of_maps_to hmaps _).symm
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      have hj' := mem_range.mp hj
      have hP : P.filter (fun D => D.card = j) = T.powersetCard j := by
        ext D
        simp only [P, mem_filter, mem_powersetCard, mem_powerset]
        exact ⟨fun h => ⟨h.1.1, h.2⟩,
          fun h => ⟨⟨h.1, by omega⟩, h.2⟩⟩
      rw [hP]
      have hc : ∀ D ∈ T.powersetCard j, (-1 : ℤ) ^ D.card = (-1 : ℤ) ^ j := by
        intro D hD
        rw [(mem_powersetCard.mp hD).2]
      rw [sum_congr rfl hc, sum_const, card_powersetCard, nsmul_eq_mul, mul_comm]

theorem truncated_lower {α : Type*} (T : Finset α) {k : ℕ} (hk : Odd k) :
    ∑ D ∈ T.powerset.filter (fun D => D.card ≤ k), (-1 : ℤ) ^ D.card ≤
      (if T.card = 0 then 1 else 0) := by
  rw [truncated_choose]
  cases hT : T.card with
  | zero =>
    simp [sum_range_succ', Nat.choose_zero_succ]
  | succ n =>
    rw [Int.alternating_sum_range_choose_eq_choose, hk.neg_one_pow]
    simp

theorem truncated_upper {α : Type*} (T : Finset α) {k : ℕ} (hk : Even k) :
    (if T.card = 0 then 1 else 0) ≤
      ∑ D ∈ T.powerset.filter (fun D => D.card ≤ k), (-1 : ℤ) ^ D.card := by
  rw [truncated_choose]
  cases hT : T.card with
  | zero =>
    simp [sum_range_succ', Nat.choose_zero_succ]
  | succ n =>
    rw [Int.alternating_sum_range_choose_eq_choose, hk.neg_one_pow]
    simp

noncomputable def avoided {α β : Type*} (P : Finset α) (S : Finset β)
    (B : α → β → Prop) : Finset β := by
  classical
  exact S.filter fun b => ∀ p ∈ P, ¬ B p b

noncomputable def truncSieve {α β : Type*} (k : ℕ) (P : Finset α) (S : Finset β)
    (B : α → β → Prop) : ℤ := by
  classical
  exact ∑ D ∈ P.powerset.filter (fun D => D.card ≤ k), (-1 : ℤ) ^ D.card *
    ((S.filter fun b => ∀ p ∈ D, B p b).card : ℤ)

noncomputable def hits {α β : Type*} (P : Finset α) (B : α → β → Prop) (b : β) :
    Finset α := by
  classical
  exact P.filter fun p => B p b

theorem truncSieve_eq {α β : Type*} (k : ℕ) (P : Finset α) (S : Finset β)
    (B : α → β → Prop) :
    truncSieve k P S B =
      ∑ b ∈ S, ∑ D ∈ (hits P B b).powerset.filter (fun D => D.card ≤ k),
        (-1 : ℤ) ^ D.card := by
  classical
  unfold truncSieve
  let R := P.powerset.filter (fun D => D.card ≤ k)
  have hterm (D : Finset α) :
      (-1 : ℤ) ^ D.card * ((S.filter fun b => ∀ p ∈ D, B p b).card : ℤ) =
      ∑ b ∈ S, if (∀ p ∈ D, B p b) then (-1 : ℤ) ^ D.card else 0 := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  change (∑ D ∈ R, (-1 : ℤ) ^ D.card * ((S.filter fun b => ∀ p ∈ D, B p b).card : ℤ)) = _
  simp_rw [hterm]
  rw [sum_comm]
  apply sum_congr rfl
  intro b hb
  rw [← sum_filter]
  congr 1
  ext D
  simp only [R, hits, mem_filter, mem_powerset, subset_iff]
  exact ⟨fun h => ⟨fun p hp => ⟨h.1.1 hp, h.2 p hp⟩, h.1.2⟩,
    fun h => ⟨⟨fun p hp => (h.1 hp).1, h.2⟩, fun p hp => (h.1 hp).2⟩⟩

theorem avoided_card_eq {α β : Type*} (P : Finset α) (S : Finset β) (B : α → β → Prop) :
    ((avoided P S B).card : ℤ) =
      ∑ b ∈ S, (if (hits P B b).card = 0 then (1 : ℤ) else 0) := by
  classical
  have heq (b : β) : (hits P B b).card = 0 ↔ ∀ p ∈ P, ¬ B p b := by
    rw [hits, card_eq_zero, filter_eq_empty_iff]
  simp_rw [heq]
  rw [← sum_filter, sum_const]
  simp [avoided]

theorem bonferroni_lower {α β : Type*} {k : ℕ} (hk : Odd k)
    (P : Finset α) (S : Finset β) (B : α → β → Prop) :
    truncSieve k P S B ≤ ((avoided P S B).card : ℤ) := by
  classical
  rw [truncSieve_eq, avoided_card_eq]
  exact sum_le_sum (fun b _ => truncated_lower _ hk)

theorem bonferroni_upper {α β : Type*} {k : ℕ} (hk : Even k)
    (P : Finset α) (S : Finset β) (B : α → β → Prop) :
    ((avoided P S B).card : ℤ) ≤ truncSieve k P S B := by
  classical
  rw [truncSieve_eq, avoided_card_eq]
  exact sum_le_sum (fun b _ => truncated_upper _ hk)

noncomputable def idealTrunc {α : Type*} (k : ℕ) (P : Finset α) (w : α → ℝ) : ℝ :=
  ∑ D ∈ P.powerset.filter (fun D => D.card ≤ k), (-1 : ℝ) ^ D.card * ∏ p ∈ D, w p

theorem truncSieve_approx {α β : Type*} (k : ℕ) (P : Finset α) (S : Finset β)
    (B : α → β → Prop) (w : α → ℝ) {E : ℝ}
    (hpoint : ∀ D ∈ P.powerset.filter (fun D => D.card ≤ k),
      ∀ K : Finset β, (∀ b, b ∈ K ↔ b ∈ S ∧ ∀ p ∈ D, B p b) →
        |(K.card : ℝ) - (S.card : ℝ) * ∏ p ∈ D, w p| ≤ E) :
    |(truncSieve k P S B : ℝ) - (S.card : ℝ) * idealTrunc k P w| ≤
      E * (P.powerset.filter (fun D => D.card ≤ k)).card := by
  classical
  let T := P.powerset.filter (fun D => D.card ≤ k)
  let K (D : Finset α) := S.filter fun b => ∀ p ∈ D, B p b
  let F (D : Finset α) :=
    (-1 : ℝ) ^ D.card * ((K D).card - (S.card : ℝ) * ∏ p ∈ D, w p)
  have heq : (truncSieve k P S B : ℝ) - (S.card : ℝ) * idealTrunc k P w =
      ∑ D ∈ T, F D := by
    simp only [truncSieve, idealTrunc, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, Int.cast_natCast, T, F, K]
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun D _ => by ring
  rw [heq]
  calc
    |∑ D ∈ T, F D| ≤ ∑ D ∈ T, |F D| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _D ∈ T, E := sum_le_sum (by
      intro D hD
      simp only [F, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hpoint D hD (K D) (fun b => mem_filter))
    _ = _ := by simp only [sum_const, nsmul_eq_mul, T, mul_comm]

theorem ideal_product_lower {α : Type*} (P : Finset α) (w : α → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1 / 2) :
    exp (-2 * ∑ p ∈ P, w p) ≤ ∏ p ∈ P, (1 - w p) := by
  rw [mul_sum, exp_sum]
  apply prod_le_prod (fun p _ => (exp_pos _).le)
  intro p hp
  obtain ⟨h₀, h₁⟩ := hw p hp
  rw [show -2 * w p = -(2 * w p) by ring, exp_neg, ← one_div]
  apply (div_le_iff₀ (exp_pos _)).mpr
  have h := add_one_le_exp (2 * w p)
  have hp : 1 ≤ (1 - w p) * (2 * w p + 1) := by
    nlinarith [mul_nonneg h₀ (show 0 ≤ 1 - 2 * w p by linarith)]
  exact hp.trans (mul_le_mul_of_nonneg_left h (by linarith))

theorem ideal_trunc_error {α : Type*} (P : Finset α) (k : ℕ) (w : α → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) :
    |∏ p ∈ P, (1 - w p) - idealTrunc k P w| ≤
      exp (2 * ∑ p ∈ P, w p) / (2 : ℝ) ^ (k + 1) := by
  classical
  let F (D : Finset α) := (-1 : ℝ) ^ D.card * ∏ p ∈ D, w p
  let T := P.powerset.filter (fun D => ¬ D.card ≤ k)
  have hp : (∏ p ∈ P, (1 - w p)) - idealTrunc k P w = ∑ D ∈ T, F D := by
    have h :=
      prod_sub (fun _ : α => (1 : ℝ)) w P
    simp only [prod_const_one, mul_one] at h
    rw [h, ← sum_filter_add_sum_filter_not P.powerset (fun D => D.card ≤ k) F]
    exact add_sub_cancel_left _ _
  have hprod (D : Finset α) (hD : D ∈ T) :
      |F D| ≤ (∏ p ∈ D, 2 * w p) / (2 : ℝ) ^ (k + 1) := by
    obtain ⟨hsub, hcard⟩ := mem_filter.mp hD
    replace hsub := mem_powerset.mp hsub
    have hn : 0 ≤ ∏ p ∈ D, w p := prod_nonneg fun p hp => hw p (hsub hp)
    simp only [F, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hn]
    apply (le_div_iff₀ (by positivity)).mpr
    rw [prod_mul_distrib, prod_const, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hn
  rw [hp]
  calc
    |∑ D ∈ T, F D| ≤ ∑ D ∈ T, |F D| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ D ∈ T, (∏ p ∈ D, 2 * w p) / (2 : ℝ) ^ (k + 1) := sum_le_sum hprod
    _ ≤ ∑ D ∈ P.powerset, (∏ p ∈ D, 2 * w p) / (2 : ℝ) ^ (k + 1) := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro D hD _
      exact div_nonneg (prod_nonneg fun p hp => by
        exact mul_nonneg (by norm_num) (hw p (mem_powerset.mp hD hp))) (by positivity)
    _ = (∏ p ∈ P, (1 + 2 * w p)) / (2 : ℝ) ^ (k + 1) := by
      rw [← sum_div, prod_one_add]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [mul_sum, exp_sum]
      exact prod_le_prod (fun p hp => by linarith [(hw p hp)])
        (fun p _ => by simpa [add_comm] using add_one_le_exp (2 * w p))

theorem progression_count {N q r : ℕ} (hq : 0 < q) :
    |(((Icc 1 N).filter (fun a => a ≡ r [MOD q])).card : ℝ) - (N : ℝ) / q| ≤ 1 := by
  let F := (Icc 1 N).filter (fun a => a ≡ r [MOD q])
  have hu : F.card ≤ N / q + 1 := count_congruence F
    (fun a ha => (mem_Icc.mp (mem_filter.mp ha).1).2) (fun a ha b hb =>
      ((mem_filter.mp ha).2).trans ((mem_filter.mp hb).2).symm)
  let t := if r % q = 0 then q else r % q
  have ht : 1 ≤ t ∧ t ≤ q ∧ t ≡ r [MOD q] := by
    have hlt := Nat.mod_lt r hq
    by_cases hz : r % q = 0
    · simp [t, hz, Nat.ModEq, Nat.succ_le_of_lt hq]
    · have hpos : 1 ≤ r % q := by omega
      exact ⟨by simpa [t, hz], by simpa [t, hz] using hlt.le,
        by simp [t, hz, Nat.ModEq]⟩
  have hl : N / q ≤ F.card := by
    rw [← card_range (N / q)]
    apply card_le_card_of_injOn (fun j => q * j + t)
    · intro j hj
      change q * j + t ∈ F
      have hj' := mem_range.mp hj
      have hjq : q * (j + 1) ≤ q * (N / q) := Nat.mul_le_mul_left _ (by omega)
      have hqN := Nat.mul_div_le N q
      have hmod :=
        (Nat.modEq_zero_iff_dvd.mpr (show q ∣ q * j from dvd_mul_right q j)).add ht.2.2
      apply mem_filter.mpr
      refine ⟨mem_Icc.mpr ⟨by omega, ?_⟩, by simpa using hmod⟩
      rw [Nat.mul_add, mul_one] at hjq
      omega
    · intro j hj k hk heq
      change q * j + t = q * k + t at heq
      exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel heq)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdivL : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q := by
    apply (le_div_iff₀ hqR).mpr
    exact_mod_cast Nat.div_mul_le_self N q
  have hdivU : (N : ℝ) / q < ((N / q : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hqR).mpr
    have hm := Nat.mod_add_div N q
    have hl := Nat.mod_lt N hq
    have h : N < (N / q + 1) * q := by
      rw [Nat.add_mul, one_mul, mul_comm (N / q)]
      omega
    exact_mod_cast h
  have huR : (F.card : ℝ) ≤ ((N / q : ℕ) : ℝ) + 1 := by exact_mod_cast hu
  have hlR : ((N / q : ℕ) : ℝ) ≤ F.card := by exact_mod_cast hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem modEq_finset_prod {α : Type*} {P : Finset α} {q : α → ℕ} {a b : ℕ}
    (hp : Set.Pairwise (P : Set α) (fun i j => (q i).Coprime (q j))) :
    a ≡ b [MOD ∏ i ∈ P, q i] ↔ ∀ i ∈ P, a ≡ b [MOD q i] := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [Nat.modEq_one]
  | @insert i P hi ih =>
    have hpair : Set.Pairwise (P : Set α) (fun j k => (q j).Coprime (q k)) := by
      intro j hj k hk hjk
      exact hp (mem_insert_of_mem hj) (mem_insert_of_mem hk) hjk
    have hiP : (q i).Coprime (∏ j ∈ P, q j) := by
      apply Nat.Coprime.prod_right
      intro j hj
      exact hp (mem_insert_self _ _) (mem_insert_of_mem hj) (fun he => hi (he ▸ hj))
    rw [prod_insert hi, ← Nat.modEq_and_modEq_iff_modEq_mul hiP, ih hpair]
    simp only [mem_insert, forall_eq_or_imp]

theorem crt_progression_count {α : Type*} (N : ℕ) {P : Finset α} {q : α → ℕ}
    (r : α → ℕ) (hq : ∀ i ∈ P, q i ≠ 0)
    (hp : Set.Pairwise (P : Set α) (fun i j => (q i).Coprime (q j))) :
    ∀ S : Finset ℕ, (∀ a, a ∈ S ↔ a ∈ Icc 1 N ∧ ∀ i ∈ P, a ≡ r i [MOD q i]) →
      |(S.card : ℝ) - (N : ℝ) / (∏ i ∈ P, q i : ℕ)| ≤ 1 := by
  classical
  intro S hS
  let z := Nat.chineseRemainderOfFinset r q P hq hp
  let Q := ∏ i ∈ P, q i
  have hQ : 0 < Q := prod_pos fun i hi => Nat.pos_of_ne_zero (hq i hi)
  have heq : S = (Icc 1 N).filter fun a => a ≡ (z : ℕ) [MOD Q] := by
    ext a
    rw [hS, mem_filter]
    apply and_congr_right
    intro ha
    rw [modEq_finset_prod hp]
    exact ⟨fun h i hi => (h i hi).trans (z.prop i hi).symm,
      fun h i hi => (h i hi).trans (z.prop i hi)⟩
  rw [heq]
  exact progression_count hQ

noncomputable def assignments {α : Type*} (U K : Finset α) (f : α → Prop) :
    Finset (Finset α) := by
  classical
  exact U.powerset.filter fun A => ∀ a ∈ K, a ∈ A ↔ f a

theorem card_assignments {α : Type*} {U K : Finset α} (hK : K ⊆ U) (f : α → Prop) :
    (assignments U K f).card = 2 ^ (U.card - K.card) := by
  classical
  rw [← card_sdiff_of_subset hK, ← card_powerset]
  apply card_bij' (fun A _ => A \ K) (fun W _ => W ∪ K.filter f)
  · intro A hA
    obtain ⟨hAU, hf⟩ := mem_filter.mp hA
    apply mem_powerset.mpr
    intro x hx
    exact mem_sdiff.mpr ⟨mem_powerset.mp hAU (mem_sdiff.mp hx).1, (mem_sdiff.mp hx).2⟩
  · intro W hW
    have hwu := mem_powerset.mp hW
    apply mem_filter.mpr
    constructor
    · apply mem_powerset.mpr
      intro x hx
      rcases mem_union.mp hx with hx | hx
      · exact (mem_sdiff.mp (hwu hx)).1
      · exact hK (mem_filter.mp hx).1
    · intro x hx
      have hnot : x ∉ W := fun h => (mem_sdiff.mp (hwu h)).2 hx
      simp [hx, hnot]
  · intro A hA
    obtain ⟨_, hf⟩ := mem_filter.mp hA
    ext x
    by_cases hx : x ∈ K
    · simpa [hx] using (hf x hx).symm
    · simp [hx]
  · intro W hW
    have hwu := mem_powerset.mp hW
    ext x
    by_cases hx : x ∈ K
    · have hnot : x ∉ W := fun h => (mem_sdiff.mp (hwu h)).2 hx
      simp [hx, hnot]
    · simp [hx]

theorem large_prime_discard {N : ℕ} (S A P : Finset ℕ) (hS : S ⊆ Icc 1 N) :
    S.card ≤ (S.filter fun a => ∀ b ∈ A, ∀ p ∈ P, ¬ p * p ∣ a + b).card +
      A.card * ∑ p ∈ P, (N / (p * p) + 1) := by
  let good (a : ℕ) := ∀ b ∈ A, ∀ p ∈ P, ¬ p * p ∣ a + b
  let bad (b p : ℕ) := S.filter fun a => p * p ∣ a + b
  have hbad : S.filter (fun a => ¬ good a) ⊆ A.biUnion (fun b => P.biUnion (bad b)) := by
    intro a ha
    obtain ⟨haS, h⟩ := mem_filter.mp ha
    simp only [good] at h
    push Not at h
    obtain ⟨b, hb, p, hp, hd⟩ := h
    exact mem_biUnion.mpr ⟨b, hb, mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨haS, hd⟩⟩⟩
  have hfiber (b p : ℕ) : (bad b p).card ≤ N / (p * p) + 1 := by
    apply count_congruence
    · intro a ha
      exact (mem_Icc.mp (hS (mem_filter.mp ha).1)).2
    · intro a ha c hc
      apply Nat.ModEq.add_left_cancel' b
      have ha' : p * p ∣ b + a := by simpa [add_comm] using (mem_filter.mp ha).2
      have hc' : p * p ∣ b + c := by simpa [add_comm] using (mem_filter.mp hc).2
      exact (Nat.modEq_zero_iff_dvd.mpr ha').trans (Nat.modEq_zero_iff_dvd.mpr hc').symm
  have hcount : (S.filter fun a => ¬ good a).card ≤
      A.card * ∑ p ∈ P, (N / (p * p) + 1) := by
    calc
      _ ≤ (A.biUnion fun b => P.biUnion (bad b)).card := card_le_card hbad
      _ ≤ ∑ b ∈ A, (P.biUnion (bad b)).card := card_biUnion_le
      _ ≤ ∑ _b ∈ A, ∑ p ∈ P, (N / (p * p) + 1) :=
        sum_le_sum fun b _ => card_biUnion_le.trans (sum_le_sum fun p _ => hfiber b p)
      _ = _ := by simp
  have hpart := card_filter_add_card_filter_not (s := S) good
  exact hpart ▸ Nat.add_le_add_left hcount _

noncomputable def logScale (N : ℕ) : ℝ := log (log N) * (log N) ^ 2

theorem scale_tendsto : Tendsto logScale atTop atTop := by
  have hlog : Tendsto (fun N : ℕ => log N) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact (tendsto_log_atTop.comp hlog).atTop_mul_atTop₀ (hlog.atTop_mul_atTop₀ hlog) |>.congr'
    (Eventually.of_forall (fun N => by simp [logScale, pow_two]))

theorem card_joint_assignments {α : Type*} [DecidableEq α] {U K L : Finset α}
    (hK : K ⊆ U) (hL : L ⊆ U) (f g : α → Prop)
    (hagree : ∀ x ∈ K, x ∈ L → (f x ↔ g x)) :
    (assignments U K f ∩ assignments U L g).card = 2 ^ (U.card - (K ∪ L).card) := by
  classical
  let F (x : α) := if x ∈ K then f x else g x
  have heq : assignments U K f ∩ assignments U L g = assignments U (K ∪ L) F := by
    ext A
    simp only [mem_inter, assignments, mem_filter]
    constructor
    · rintro ⟨⟨hU, hK'⟩, ⟨_, hL'⟩⟩
      refine ⟨hU, ?_⟩
      intro x hx
      by_cases hxK : x ∈ K
      · simpa [F, hxK] using hK' x hxK
      · have hxL := (mem_union.mp hx).resolve_left hxK
        simpa [F, hxK] using hL' x hxL
    · rintro ⟨hU, hF⟩
      refine ⟨⟨hU, ?_⟩, ⟨hU, ?_⟩⟩
      · intro x hx
        simpa [F, hx] using hF x (mem_union_left _ hx)
      · intro x hx
        have h := hF x (mem_union_right _ hx)
        by_cases hmem : x ∈ K
        · have h' : x ∈ A ↔ f x := by simpa [F, hmem] using h
          exact h'.trans (hagree x hmem hx)
        · simpa [F, hmem] using h
  rw [heq]
  exact card_assignments (union_subset hK hL) _

def signKey (p a : ℕ) : ℕ × ℕ :=
  (p, min (a % (p * p)) (p * p - a % (p * p)))

def signLeft (p a : ℕ) : Prop := 2 * (a % (p * p)) < p * p

theorem key_eq_iff {p a b : ℕ} (hp : p.Prime) :
    signKey p a = signKey p b ↔
      a % (p * p) = b % (p * p) ∨ a % (p * p) + b % (p * p) = p * p := by
  let q := p * p
  let r := a % q
  let s := b % q
  have hr : r < q := Nat.mod_lt _ (Nat.mul_pos hp.pos hp.pos)
  have hs : s < q := Nat.mod_lt _ (Nat.mul_pos hp.pos hp.pos)
  have heq : signKey p a = signKey p b ↔ min r (q - r) = min s (q - s) := by simp [signKey, q, r, s]
  rw [heq]
  change min r (q - r) = min s (q - s) ↔ r = s ∨ r + s = q
  by_cases hrl : r ≤ q - r <;> by_cases hsl : s ≤ q - s <;>
    simp only [min_def, hrl, hsl, if_true, if_false] <;> omega

theorem full_inclusion_exclusion {α β : Type*} (P : Finset α) (S : Finset β)
    (B : α → β → Prop) :
    ((avoided P S B).card : ℤ) = truncSieve P.card P S B := by
  classical
  rw [truncSieve_eq, avoided_card_eq]
  apply sum_congr rfl
  intro b hb
  have hfilter : (hits P B b).powerset.filter (fun D => D.card ≤ P.card) =
      (hits P B b).powerset := by
    apply filter_true_of_mem
    intro D hD
    exact card_le_card ((mem_powerset.mp hD).trans (filter_subset _ _))
  rw [hfilter, sum_powerset_neg_one_pow_card]
  simp only [card_eq_zero]

theorem sieve_count_diff {α β : Type*} (P : Finset α) (S T : Finset β)
    (B : α → β → Prop) {E : ℝ}
    (hterm : ∀ D ∈ P.powerset, ∀ K L : Finset β,
      (∀ b, b ∈ K ↔ b ∈ S ∧ ∀ p ∈ D, B p b) →
      (∀ b, b ∈ L ↔ b ∈ T ∧ ∀ p ∈ D, B p b) →
      |(K.card : ℝ) - L.card| ≤ E) :
    |((avoided P S B).card : ℝ) - (avoided P T B).card| ≤ E * (2 : ℝ) ^ P.card := by
  classical
  have hs : ((avoided P S B).card : ℝ) = (truncSieve P.card P S B : ℝ) := by
    exact_mod_cast full_inclusion_exclusion P S B
  have ht : ((avoided P T B).card : ℝ) = (truncSieve P.card P T B : ℝ) := by
    exact_mod_cast full_inclusion_exclusion P T B
  let F (X : Finset β) (D : Finset α) := X.filter fun b => ∀ p ∈ D, B p b
  let Ψ (D : Finset α) := (-1 : ℝ) ^ D.card *
    (((F S D).card : ℝ) - (F T D).card)
  have hfilter : P.powerset.filter (fun D => D.card ≤ P.card) = P.powerset :=
    filter_true_of_mem fun D hD => card_le_card (mem_powerset.mp hD)
  have heq : (truncSieve P.card P S B : ℝ) - (truncSieve P.card P T B : ℝ) =
      ∑ D ∈ P.powerset, Ψ D := by
    simp only [truncSieve, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, Int.cast_natCast, hfilter, Ψ, F]
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun D _ => by ring
  rw [hs, ht, heq]
  calc
    |∑ D ∈ P.powerset, Ψ D| ≤ ∑ D ∈ P.powerset, |Ψ D| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _D ∈ P.powerset, E := sum_le_sum (by
      intro D hD
      simp only [Ψ, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hterm D hD (F S D) (F T D) (fun b => mem_filter) (fun b => mem_filter))
    _ = _ := by simp [card_powerset, mul_comm]

theorem exists_uniform_errors {α β : Type*} (Ω : Finset α) (J : Finset β) (hΩ : Ω.Nonempty)
    (err : α → β → ℝ) {D E : ℝ} (hE : 0 ≤ E)
    (hmoment : ∀ j ∈ J, ∑ ω ∈ Ω, (err ω j) ^ 2 ≤ (Ω.card : ℝ) * D)
    (hlimit : (J.card : ℝ) * D ≤ E ^ 2) :
    ∃ ω ∈ Ω, ∀ j ∈ J, |err ω j| ≤ E := by
  by_contra! h
  have hrow : ∀ ω ∈ Ω, E ^ 2 < ∑ j ∈ J, (err ω j) ^ 2 := by
    intro ω hω
    obtain ⟨j, hj, he⟩ := h ω hω
    have hsq : E ^ 2 < (err ω j) ^ 2 := by
      calc
        E ^ 2 < |err ω j| ^ 2 := by
          exact pow_lt_pow_left₀ he hE (by norm_num)
        _ = _ := sq_abs _
    exact hsq.trans_le (single_le_sum (fun j _ => sq_nonneg (err ω j)) hj)
  have hlt := sum_lt_sum_of_nonempty hΩ hrow
  rw [sum_const, nsmul_eq_mul, sum_comm] at hlt
  have hup : ∑ j ∈ J, ∑ ω ∈ Ω, (err ω j) ^ 2 ≤
      (J.card : ℝ) * ((Ω.card : ℝ) * D) := by
    simpa only [sum_const, nsmul_eq_mul] using sum_le_sum hmoment
  have hle : (J.card : ℝ) * ((Ω.card : ℝ) * D) ≤ (Ω.card : ℝ) * E ^ 2 := by
    rw [mul_left_comm]
    gcongr
  exact (not_lt_of_ge (hup.trans hle)) hlt

theorem sieved_progressions_close {α : Type*} [DecidableEq α]
    (N : ℕ) (P Q : Finset α) (hPQ : Disjoint P Q) (q r s : α → ℕ)
    (hq : ∀ i ∈ P ∪ Q, q i ≠ 0)
    (hp : Set.Pairwise ((P ∪ Q : Finset α) : Set α) (fun i j => (q i).Coprime (q j)))
    (S T : Finset ℕ)
    (hS : ∀ a, a ∈ S ↔ a ∈ Icc 1 N ∧ ∀ i ∈ Q, a ≡ r i [MOD q i])
    (hT : ∀ a, a ∈ T ↔ a ∈ Icc 1 N ∧ ∀ i ∈ Q, a ≡ s i [MOD q i]) :
    |((avoided P S (fun i a => a ≡ 0 [MOD q i])).card : ℝ) -
      (avoided P T (fun i a => a ≡ 0 [MOD q i])).card| ≤ 2 * (2 : ℝ) ^ P.card := by
  apply sieve_count_diff
  intro D hD K L hK hL
  have hDP : D ⊆ P := mem_powerset.mp hD
  have hdis : Disjoint D Q := disjoint_of_subset_left hDP hPQ
  have hsub : D ∪ Q ⊆ P ∪ Q := union_subset_union hDP (fun _ h => h)
  have hdq : ∀ i ∈ D ∪ Q, q i ≠ 0 := fun i hi => hq i (hsub hi)
  have hpair : Set.Pairwise ((D ∪ Q : Finset α) : Set α)
      (fun i j => (q i).Coprime (q j)) := fun i hi j hj hne => hp (hsub hi) (hsub hj) hne
  let lift (t : α → ℕ) (i : α) := if i ∈ Q then t i else 0
  have hf (a : ℕ) (t : α → ℕ) :
      (∀ i ∈ Q, a ≡ t i [MOD q i]) ∧ (∀ i ∈ D, a ≡ 0 [MOD q i]) ↔
        ∀ i ∈ D ∪ Q, a ≡ lift t i [MOD q i] := by
    constructor
    · rintro ⟨h₁, h₂⟩ i hi
      by_cases hiQ : i ∈ Q
      · simpa [lift, hiQ] using h₁ i hiQ
      · have hiD := (mem_union.mp hi).resolve_right hiQ
        simpa [lift, hiQ] using h₂ i hiD
    · intro h
      constructor
      · intro i hi
        simpa [lift, hi] using h i (mem_union_right _ hi)
      · intro i hi
        have hn : i ∉ Q := fun hh => (disjoint_left.mp hdis) hi hh
        simpa [lift, hn] using h i (mem_union_left _ hi)
  have hk := crt_progression_count N (lift r) hdq hpair K (fun a => by
    rw [hK, hS, and_assoc, hf])
  have hl := crt_progression_count N (lift s) hdq hpair L (fun a => by
    rw [hL, hT, and_assoc, hf])
  obtain ⟨hkl, hku⟩ := abs_le.mp hk
  obtain ⟨hll, hlu⟩ := abs_le.mp hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

noncomputable def profileCount {α β : Type*} (T : Finset β) (D V : Finset α)
    (pos neg : α → β → Prop) : ℕ := by
  classical
  exact (T.filter fun b => (∀ p ∈ D, p ∉ V → pos p b) ∧ (∀ p ∈ V, neg p b)).card

open Classical in
theorem product_indicator {α : Type*} (P : Finset α) (B : α → Prop) :
    (∏ i ∈ P, if B i then (1 : ℝ) else 0) = if ∀ i ∈ P, B i then 1 else 0 := by
  by_cases h : ∀ i ∈ P, B i
  · rw [if_pos h]
    exact prod_eq_one fun i hi => if_pos (h i hi)
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi, hn⟩ := h
    exact prod_eq_zero hi (if_neg hn)

open Classical in
theorem profile_expansion {α β : Type*} (P : Finset α) (T : Finset β) (pos neg : α → β → Prop) :
    (∑ b ∈ T, ∏ p ∈ P, (1 + (if pos p b then (1 : ℝ) else 0) -
      (if neg p b then 1 else 0))) =
      ∑ D ∈ P.powerset, ∑ V ∈ D.powerset, (-1 : ℝ) ^ V.card * (profileCount T D V pos neg : ℝ) := by
  let u (p : α) (b : β) : ℝ := if pos p b then 1 else 0
  let v (p : α) (b : β) : ℝ := if neg p b then 1 else 0
  change (∑ b ∈ T, ∏ p ∈ P, (1 + u p b - v p b)) = _
  simp_rw [add_sub_assoc, prod_one_add, prod_sub, sum_comm (s := T) (t := P.powerset)]
  apply sum_congr rfl
  intro D hD
  rw [sum_comm]
  apply sum_congr rfl
  intro V hV
  simp only [u, v, product_indicator]
  let B (b : β) := (∀ p ∈ D \ V, pos p b) ∧ (∀ p ∈ V, neg p b)
  have hb (b : β) :
      (-1 : ℝ) ^ V.card * (if ∀ p ∈ D \ V, pos p b then 1 else 0) *
          (if ∀ p ∈ V, neg p b then 1 else 0) =
        if B b then (-1 : ℝ) ^ V.card else 0 := by
    by_cases h₁ : ∀ p ∈ D \ V, pos p b
    · by_cases h₂ : ∀ p ∈ V, neg p b
      · rw [if_pos h₁, if_pos h₂, if_pos (show B b from ⟨h₁, h₂⟩), mul_one, mul_one]
      · rw [if_pos h₁, if_neg h₂, if_neg (show ¬ B b from fun h => h₂ h.2), mul_zero]
    · rw [if_neg h₁, if_neg (show ¬ B b from fun h => h₁ h.1), mul_zero, zero_mul]
  simp_rw [hb]
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  simp [profileCount, B]

noncomputable def profileWeight {α β : Type*} (P : Finset α) (pos neg : α → β → Prop)
    (b : β) : ℝ := by
  classical
  exact ∏ p ∈ P, (1 + (if pos p b then (1 : ℝ) else 0) - (if neg p b then 1 else 0))

open Classical in
/-- The alternating terms cancel after grouping equal and opposite residue profiles. -/
theorem profile_cancel {α β : Type*} (P : Finset α) (T : Finset β) (pos neg : α → β → Prop)
    {E : ℝ} (hE : 0 ≤ E)
    (hclose : ∀ D ∈ P.powerset, D.Nonempty → ∀ V ∈ D.powerset,
      |(profileCount T D V pos neg : ℝ) - profileCount T D ∅ pos neg| ≤ E) :
    |(∑ b ∈ T, profileWeight P pos neg b) - (T.card : ℝ)| ≤ E * (3 : ℝ) ^ P.card := by
  unfold profileWeight
  rw [profile_expansion]
  let F (D : Finset α) := ∑ V ∈ D.powerset, (-1 : ℝ) ^ V.card * (profileCount T D V pos neg : ℝ)
  have h0 : F ∅ = T.card := by simp [F, profileCount]
  have hm : ∅ ∈ P.powerset := by simp
  have hsplit : (∑ D ∈ P.powerset, F D) - (T.card : ℝ) =
      ∑ D ∈ P.powerset.erase ∅, F D := by
    have hsum := sum_erase_add P.powerset F hm
    linarith
  change |(∑ D ∈ P.powerset, F D) - (T.card : ℝ)| ≤ _
  rw [hsplit]
  have hbound : ∀ D ∈ P.powerset.erase ∅, |F D| ≤ E * (2 : ℝ) ^ D.card := by
    intro D hD
    obtain ⟨hne, hD⟩ := mem_erase.mp hD
    have hn : D.Nonempty := nonempty_iff_ne_empty.mpr hne
    have hz : ∑ V ∈ D.powerset, (-1 : ℝ) ^ V.card = 0 := by
      exact_mod_cast sum_powerset_neg_one_pow_card_of_nonempty hn
    let G (V : Finset α) := (-1 : ℝ) ^ V.card *
      ((profileCount T D V pos neg : ℝ) - profileCount T D ∅ pos neg)
    have hF : F D = ∑ V ∈ D.powerset, G V := by
      simp only [F, G, mul_sub, sum_sub_distrib, ← sum_mul, hz, zero_mul, sub_zero]
    rw [hF]
    calc
      |∑ V ∈ D.powerset, G V| ≤ ∑ V ∈ D.powerset, |G V| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _V ∈ D.powerset, E := sum_le_sum (by
        intro V hV
        simpa [G, abs_mul, abs_pow] using hclose D hD hn V hV)
      _ = _ := by simp [card_powerset, mul_comm]
  calc
    |∑ D ∈ P.powerset.erase ∅, F D| ≤ ∑ D ∈ P.powerset.erase ∅, |F D| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ D ∈ P.powerset.erase ∅, E * (2 : ℝ) ^ D.card := sum_le_sum hbound
    _ ≤ ∑ D ∈ P.powerset, E * (2 : ℝ) ^ D.card := by
      apply sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
      exact fun _ _ _ => mul_nonneg hE (by positivity)
    _ = _ := by
      rw [← mul_sum]
      simp only [← prod_const (b := (2 : ℝ)), ← prod_one_add]
      norm_num

def opposite (p a b : ℕ) : Prop := a % (p * p) + b % (p * p) = p * p

theorem sign_agree_iff_eq {p a b : ℕ} (hp : p.Prime)
    (ha : ¬ p * p ∣ a + a) (hb : ¬ p * p ∣ b + b)
    (hkey : signKey p a = signKey p b) :
    (signLeft p a ↔ signLeft p b) ↔ a ≡ b [MOD p * p] := by
  have noMid (n : ℕ) (h : ¬ p * p ∣ n + n) :
      2 * (n % (p * p)) ≠ p * p := by
    intro hmid
    apply h
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, ← two_mul, hmid, Nat.mod_self]
  have hma := noMid a ha
  have hmb := noMid b hb
  change ((2 * (a % (p * p)) < p * p) ↔ (2 * (b % (p * p)) < p * p)) ↔
    a % (p * p) = b % (p * p)
  rcases (key_eq_iff hp).mp hkey with heq | hsum
  · simp [heq]
  · constructor
    · intro h
      by_cases hleft : 2 * (a % (p * p)) < p * p
      · have hright := h.mp hleft
        omega
      · have hright : ¬ 2 * (b % (p * p)) < p * p := fun h' => hleft (h.mpr h')
        omega
    · intro h
      simp [h]

def keys (P : Finset ℕ) (a : ℕ) : Finset (ℕ × ℕ) := P.image fun p => signKey p a

theorem key_card (P : Finset ℕ) (a : ℕ) : (keys P a).card = P.card := by
  apply card_image_of_injOn
  intro p hp q hq heq
  exact congrArg Prod.fst heq

theorem sign_single_count (P : Finset ℕ) (a : ℕ) (U : Finset (ℕ × ℕ))
    (hU : keys P a ⊆ U) :
    ((assignments U (keys P a) (fun i => signLeft i.1 a)).card : ℝ) *
      (2 : ℝ) ^ P.card = (U.powerset.card : ℝ) := by
  rw [card_assignments hU, key_card, card_powerset, Nat.cast_pow, Nat.cast_pow]
  change (2 : ℝ) ^ (U.card - P.card) * 2 ^ P.card = 2 ^ U.card
  rw [← pow_add]
  have hle := card_le_card hU
  rw [key_card] at hle
  rw [Nat.sub_add_cancel hle]

theorem mem_assignments_iff {α : Type*} {U K W : Finset α} (f : α → Prop) :
    W ∈ assignments U K f ↔ W ⊆ U ∧ ∀ x ∈ K, x ∈ W ↔ f x := by
  classical
  simp [assignments, mem_powerset]

open Classical in
theorem sign_joint_count (P : Finset ℕ) (a b : ℕ) (U : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, p.Prime)
    (ha : ∀ p ∈ P, ¬ p * p ∣ a + a) (hb : ∀ p ∈ P, ¬ p * p ∣ b + b)
    (hUa : keys P a ⊆ U) (hUb : keys P b ⊆ U) :
    (((assignments U (keys P a) (fun i => signLeft i.1 a)) ∩
        (assignments U (keys P b) (fun i => signLeft i.1 b))).card : ℝ) *
        (2 : ℝ) ^ (2 * P.card) =
      (U.powerset.card : ℝ) * ∏ p ∈ P, (1 +
        (if a ≡ b [MOD p * p] then (1 : ℝ) else 0) -
        (if opposite p a b then 1 else 0)) := by
  let A := assignments U (keys P a) (fun i => signLeft i.1 a)
  let B := assignments U (keys P b) (fun i => signLeft i.1 b)
  let W (p : ℕ) := 1 + (if a ≡ b [MOD p * p] then (1 : ℝ) else 0) -
    (if opposite p a b then 1 else 0)
  have hexc (p : ℕ) (hp : p ∈ P) (hop : opposite p a b) : ¬ a ≡ b [MOD p * p] := by
    intro h
    apply ha p hp
    change a % (p * p) = b % (p * p) at h
    change a % (p * p) + b % (p * p) = p * p at hop
    have hm : a % (p * p) + a % (p * p) = p * p := by omega
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hm, Nat.mod_self]
  by_cases hbad : ∃ p ∈ P, opposite p a b
  · obtain ⟨p, hp, hop⟩ := hbad
    have hkey := (key_eq_iff (hP p hp)).mpr (Or.inr hop)
    have hmA : signKey p a ∈ keys P a := mem_image_of_mem _ hp
    have hmB : signKey p a ∈ keys P b := by rw [hkey]; exact mem_image_of_mem _ hp
    have hempty : A ∩ B = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro ω hω
      obtain ⟨hA, hB⟩ := mem_inter.mp hω
      have h₁ := ((mem_assignments_iff _).mp hA).2 _ hmA
      have h₂ := ((mem_assignments_iff _).mp hB).2 _ hmB
      exact hexc p hp hop ((sign_agree_iff_eq (hP p hp) (ha p hp) (hb p hp) hkey).mp
        (h₁.symm.trans h₂))
    have hz : ∏ p ∈ P, W p = 0 := prod_eq_zero hp (by simp [W, hop, hexc p hp hop])
    change ((A ∩ B).card : ℝ) * _ = _ * (∏ p ∈ P, W p)
    simp [hempty, hz]
  · have hop (p : ℕ) (hp : p ∈ P) : ¬ opposite p a b := fun h => hbad ⟨p, hp, h⟩
    have heq {p : ℕ} (hp : p ∈ P) (h : signKey p a = signKey p b) :
        a ≡ b [MOD p * p] := ((key_eq_iff (hP p hp)).mp h).resolve_right (hop p hp)
    let C := P.filter (fun p => a ≡ b [MOD p * p])
    have hinter : keys P a ∩ keys P b = keys C a := by
      ext i
      constructor
      · intro hi
        obtain ⟨hi₁, hi₂⟩ := mem_inter.mp hi
        obtain ⟨p, hp, hpi⟩ := mem_image.mp hi₁
        obtain ⟨q, hq, hqi⟩ := mem_image.mp hi₂
        have hpq : p = q := congrArg Prod.fst (hpi.trans hqi.symm)
        subst q
        exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, heq hp (hpi.trans hqi.symm)⟩, hpi⟩
      · intro hi
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hi
        obtain ⟨hp', hpmod⟩ := mem_filter.mp hp
        have hkey := (key_eq_iff (hP p hp')).mpr (Or.inl hpmod)
        refine mem_inter.mpr ⟨mem_image_of_mem _ hp', ?_⟩
        rw [hkey]
        exact mem_image_of_mem _ hp'
    have hagree : ∀ i ∈ keys P a, i ∈ keys P b → (signLeft i.1 a ↔ signLeft i.1 b) := by
      intro i hi hj
      have hij : i ∈ keys C a := hinter ▸ mem_inter.mpr ⟨hi, hj⟩
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hij
      obtain ⟨hp', hc⟩ := mem_filter.mp hp
      change a % (p * p) = b % (p * p) at hc
      simp [signKey, signLeft, hc]
    have hcard : (keys P a ∪ keys P b).card + C.card = 2 * P.card := by
      have hc := card_union_add_card_inter (keys P a) (keys P b)
      rw [hinter, key_card, key_card, key_card] at hc
      omega
    have hu : (keys P a ∪ keys P b).card ≤ U.card := card_le_card (union_subset hUa hUb)
    have hprod : ∏ p ∈ P, W p = (2 : ℝ) ^ C.card := by
      have he (p : ℕ) (hp : p ∈ P) : W p = if a ≡ b [MOD p * p] then 2 else 1 := by
        by_cases hm : a ≡ b [MOD p * p] <;> norm_num [W, hm, hop p hp]
      rw [prod_congr rfl he, ← prod_filter, prod_const]
    change ((A ∩ B).card : ℝ) * _ = _ * (∏ p ∈ P, W p)
    rw [hprod, card_joint_assignments hUa hUb _ _ hagree, card_powerset,
      Nat.cast_pow, Nat.cast_pow]
    change (2 : ℝ) ^ (U.card - (keys P a ∪ keys P b).card) * 2 ^ (2 * P.card) =
      2 ^ U.card * 2 ^ C.card
    rw [← pow_add, ← pow_add]
    congr 1
    omega

noncomputable def frequency {α β : Type*} (T : Finset β) (F : β → Finset α)
    (ω : α) : ℝ := by
  classical
  exact ((T.filter fun b => ω ∈ F b).card : ℝ)

open Classical in
theorem frequency_indicator {α β : Type*} (T : Finset β) (F : β → Finset α) (ω : α) :
    frequency T F ω = ∑ b ∈ T, if ω ∈ F b then (1 : ℝ) else 0 := by
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  rfl

theorem frequency_mean_sum {α β : Type*} (U : Finset α) (T : Finset β) (F : β → Finset α)
    (hF : ∀ b ∈ T, F b ⊆ U) :
    ∑ ω ∈ U, frequency T F ω = ∑ b ∈ T, ((F b).card : ℝ) := by
  classical
  simp_rw [frequency_indicator]
  rw [sum_comm]
  apply sum_congr rfl
  intro b hb
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  have heq : U.filter (· ∈ F b) = F b := by
    ext ω
    exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨hF b hb h, h⟩⟩
  rw [heq]

theorem frequency_square_sum {α β : Type*} [DecidableEq α] (U : Finset α) (T : Finset β)
    (F : β → Finset α) (hF : ∀ b ∈ T, F b ⊆ U) :
    ∑ ω ∈ U, (frequency T F ω) ^ 2 = ∑ b ∈ T, ∑ c ∈ T, ((F b ∩ F c).card : ℝ) := by
  classical
  simp_rw [pow_two, frequency_indicator, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro b hb
  rw [sum_comm]
  apply sum_congr rfl
  intro c hc
  calc
    _ = ∑ ω ∈ U, if ω ∈ F b ∩ F c then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro ω _
      by_cases h₁ : ω ∈ F b <;> by_cases h₂ : ω ∈ F c <;> simp [h₁, h₂]
    _ = _ := by
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      have heq : U.filter (· ∈ F b ∩ F c) = F b ∩ F c := by
        ext ω
        exact ⟨fun h => (mem_filter.mp h).2, fun h =>
          mem_filter.mpr ⟨hF b hb (mem_inter.mp h).1, h⟩⟩
      rw [heq]

theorem centered_frequency_variance {α β : Type*} [DecidableEq α] (U : Finset α) (T : Finset β)
    (F : β → Finset α) (hF : ∀ b ∈ T, F b ⊆ U) (ρ : ℝ)
    (hsingle : ∀ b ∈ T, ((F b).card : ℝ) = (U.card : ℝ) * ρ) (V : β → β → ℝ) {E : ℝ}
    (hpair : ∀ b ∈ T, ∀ c ∈ T, ((F b ∩ F c).card : ℝ) = (U.card : ℝ) * ρ ^ 2 * V b c)
    (hrow : ∀ b ∈ T, ∑ c ∈ T, V b c ≤ (T.card : ℝ) + E) :
    ∑ ω ∈ U, (frequency T F ω - (T.card : ℝ) * ρ) ^ 2 ≤
      (U.card : ℝ) * ρ ^ 2 * (T.card : ℝ) * E := by
  have hμ : ∑ ω ∈ U, frequency T F ω = (T.card : ℝ) * ((U.card : ℝ) * ρ) := by
    rw [frequency_mean_sum U T F hF, sum_congr rfl hsingle, sum_const, nsmul_eq_mul]
  have h2 : ∑ ω ∈ U, (frequency T F ω) ^ 2 ≤
      (T.card : ℝ) * ((U.card : ℝ) * ρ ^ 2 * ((T.card : ℝ) + E)) := by
    rw [frequency_square_sum U T F hF]
    calc
      _ ≤ ∑ _b ∈ T, (U.card : ℝ) * ρ ^ 2 * ((T.card : ℝ) + E) := by
        apply sum_le_sum
        intro b hb
        rw [sum_congr rfl (hpair b hb), ← mul_sum]
        exact mul_le_mul_of_nonneg_left (hrow b hb) (by positivity)
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hs (ω : α) : (frequency T F ω - (T.card : ℝ) * ρ) ^ 2 =
      (frequency T F ω) ^ 2 - (2 * (T.card : ℝ) * ρ) * frequency T F ω +
        ((T.card : ℝ) * ρ) ^ 2 := by ring
  simp_rw [hs]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, hμ]
  calc
    _ ≤ (T.card : ℝ) * ((U.card : ℝ) * ρ ^ 2 * ((T.card : ℝ) + E)) -
        (2 * (T.card : ℝ) * ρ) * ((T.card : ℝ) * ((U.card : ℝ) * ρ)) +
        (U.card : ℝ) * ((T.card : ℝ) * ρ) ^ 2 := by gcongr
    _ = _ := by ring

noncomputable def signChoices (U : Finset (ℕ × ℕ)) (P : Finset ℕ) (a : ℕ) :
    Finset (Finset (ℕ × ℕ)) :=
  assignments U (keys P a) (fun i => signLeft i.1 a)

theorem sign_fiber_variance (P T : Finset ℕ) (U : Finset (ℕ × ℕ))
    (hprime : ∀ p ∈ P, p.Prime)
    (hdiag : ∀ a ∈ T, ∀ p ∈ P, ¬ p * p ∣ a + a)
    (hU : ∀ a ∈ T, keys P a ⊆ U)
    {E : ℝ} (hE : 0 ≤ E)
    (hclose : ∀ a ∈ T, ∀ D ∈ P.powerset, D.Nonempty → ∀ V ∈ D.powerset,
      |(profileCount T D V (fun p b => a ≡ b [MOD p * p]) (fun p b => opposite p a b) : ℝ) -
        profileCount T D ∅ (fun p b => a ≡ b [MOD p * p]) (fun p b => opposite p a b)| ≤ E) :
    let ρ := ((2 : ℝ) ^ P.card)⁻¹
    ∑ ω ∈ U.powerset, (frequency T (signChoices U P) ω - (T.card : ℝ) * ρ) ^ 2 ≤
      (U.powerset.card : ℝ) * ρ ^ 2 * (T.card : ℝ) * (E * 3 ^ P.card) := by
  classical
  let H := (2 : ℝ) ^ P.card
  let ρ := H⁻¹
  let F := signChoices U P
  let W (a b : ℕ) :=
    profileWeight P (fun p n => a ≡ n [MOD p * p]) (fun p n => opposite p a n) b
  have hH : 0 < H := by positivity
  have hF : ∀ a ∈ T, F a ⊆ U.powerset := fun a ha ω hω =>
    mem_powerset.mpr ((mem_assignments_iff _).mp hω).1
  have hsingle : ∀ a ∈ T, ((F a).card : ℝ) = (U.powerset.card : ℝ) * ρ := by
    intro a ha
    rw [← div_eq_mul_inv]
    exact (eq_div_iff hH.ne').mpr (sign_single_count P a U (hU a ha))
  have hpair : ∀ a ∈ T, ∀ b ∈ T, ((F a ∩ F b).card : ℝ) =
      (U.powerset.card : ℝ) * ρ ^ 2 * W a b := by
    intro a ha b hb
    have h := sign_joint_count P a b U hprime (hdiag a ha) (hdiag b hb) (hU a ha) (hU b hb)
    rw [mul_comm 2, pow_mul] at h
    have h' : ((F a ∩ F b).card : ℝ) * H^2 = (U.powerset.card : ℝ) * W a b := by
      have heq : W a b =
          ∏ p ∈ P, (1 + (if a ≡ b [MOD p * p] then (1 : ℝ) else 0) -
            (if opposite p a b then 1 else 0)) := by
        unfold W profileWeight
        apply prod_congr rfl
        intro p _
        by_cases h₁ : a ≡ b [MOD p * p] <;> by_cases h₂ : opposite p a b <;> simp [h₁, h₂]
      rw [heq]
      exact h
    calc
      ((F a ∩ F b).card : ℝ) = (U.powerset.card : ℝ) * W a b / H^2 :=
        (eq_div_iff (pow_ne_zero _ hH.ne')).mpr h'
      _ = _ := by dsimp [ρ]; rw [inv_pow, div_eq_mul_inv]; ring
  have hcov : ∀ a ∈ T, ∑ b ∈ T, W a b ≤ (T.card : ℝ) + E * 3 ^ P.card := by
    intro a ha
    have h := (abs_le.mp (profile_cancel P T (fun p b => a ≡ b [MOD p * p])
      (fun p b => opposite p a b) hE (hclose a ha))).2
    exact (sub_le_iff_le_add.mp h).trans_eq (add_comm _ _)
  exact centered_frequency_variance U.powerset T F hF ρ hsingle W hpair hcov

theorem presieve_profile_close {α : Type*} [DecidableEq α]
    (N a : ℕ) (P B D V : Finset α) (q r : α → ℕ)
    (hPB : Disjoint P B) (hD : D ⊆ P) (hV : V ⊆ D)
    (hq : ∀ i ∈ P ∪ B, q i ≠ 0)
    (hp : Set.Pairwise ((P ∪ B : Finset α) : Set α) (fun i j => (q i).Coprime (q j)))
    (ha : ∀ i ∈ P, 0 < a % q i)
    (S : Finset ℕ) (hS : ∀ b, b ∈ S ↔ b ∈ Icc 1 N ∧
      (∀ i ∈ B, b ≡ r i [MOD q i]) ∧ (∀ i ∈ P, ¬ b ≡ 0 [MOD q i])) :
    |(profileCount S D V (fun i b => a ≡ b [MOD q i])
        (fun i b => a % q i + b % q i = q i) : ℝ) -
      profileCount S D ∅ (fun i b => a ≡ b [MOD q i])
        (fun i b => a % q i + b % q i = q i)| ≤ 2 * (2 : ℝ) ^ P.card := by
  classical
  let C := P \ D
  let K := B ∪ D
  let f (V' : Finset α) (i : α) := if i ∈ D then
    if i ∈ V' then q i - a % q i else a else r i
  let T (V' : Finset α) := (Icc 1 N).filter fun x => ∀ i ∈ K, x ≡ f V' i [MOD q i]
  have hdis : Disjoint C K := by
    apply disjoint_left.mpr
    intro i hc hk
    obtain ⟨hiP, hiD⟩ := mem_sdiff.mp hc
    rcases mem_union.mp hk with hiB | hiD'
    · exact disjoint_left.mp hPB hiP hiB
    · exact hiD hiD'
  have hsub : C ∪ K ⊆ P ∪ B := by
    intro i hi
    rcases mem_union.mp hi with hci | hki
    · exact mem_union_left _ (mem_sdiff.mp hci).1
    · rcases mem_union.mp hki with hiB | hiD
      · exact mem_union_right _ hiB
      · exact mem_union_left _ (hD hiD)
  let A (V' : Finset α) := avoided C (T V') (fun i b => b ≡ 0 [MOD q i])
  have hA (V' : Finset α) (hV' : V' ⊆ D) :
      profileCount S D V' (fun i b => a ≡ b [MOD q i])
        (fun i b => a % q i + b % q i = q i) = (A V').card := by
    unfold profileCount
    congr 1
    ext b
    simp only [A, avoided, T, mem_filter, hS]
    have hpos (i : α) (hi : i ∈ D) : 0 < a % q i := ha i (hD hi)
    have hneg (i : α) (hi : i ∈ D) : 0 < q i - a % q i ∧ q i - a % q i < q i := by
      have hlt := Nat.mod_lt a (Nat.pos_of_ne_zero (hq i (mem_union_left _ (hD hi))))
      have hpos' := hpos i hi
      omega
    have hminus (i : α) (hi : i ∈ D) :
        b ≡ q i - a % q i [MOD q i] ↔ a % q i + b % q i = q i := by
      change b % q i = (q i - a % q i) % q i ↔ _
      rw [Nat.mod_eq_of_lt (hneg i hi).2]
      have hpos' := hpos i hi
      have hlt := Nat.mod_lt a (Nat.pos_of_ne_zero (hq i (mem_union_left _ (hD hi))))
      omega
    constructor
    · rintro ⟨⟨hb, hB, hP⟩, hp', hn'⟩
      refine ⟨⟨hb, ?_⟩, fun i hi => hP i (mem_sdiff.mp hi).1⟩
      intro i hi
      rcases mem_union.mp hi with hiB | hiD
      · have hnD : i ∉ D := fun hiD => disjoint_left.mp hPB (hD hiD) hiB
        simpa [f, hnD] using hB i hiB
      · by_cases hiV : i ∈ V'
        · have hh := (hminus i hiD).mpr (hn' i hiV)
          simpa [f, hiD, hiV] using hh
        · have hh := (hp' i hiD hiV).symm
          simpa [f, hiD, hiV] using hh
    · rintro ⟨⟨hb, hK⟩, hC⟩
      refine ⟨⟨hb, ?_, ?_⟩, ?_, ?_⟩
      · intro i hiB
        have hh := hK i (mem_union_left _ hiB)
        have hnD : i ∉ D := fun hiD => disjoint_left.mp hPB (hD hiD) hiB
        simpa [f, hnD] using hh
      · intro i hiP
        by_cases hiD : i ∈ D
        · have hh := hK i (mem_union_right _ hiD)
          by_cases hiV : i ∈ V'
          · have hmod : b ≡ q i - a % q i [MOD q i] := by simpa [f, hiD, hiV] using hh
            change b % q i = (q i - a % q i) % q i at hmod
            rw [Nat.mod_eq_of_lt (hneg i hiD).2] at hmod
            simpa [Nat.ModEq, hmod] using (hneg i hiD).1.ne'
          · have hmod : b ≡ a [MOD q i] := by simpa [f, hiD, hiV] using hh
            change b % q i = a % q i at hmod
            simpa [Nat.ModEq, hmod] using (hpos i hiD).ne'
        · exact hC i (mem_sdiff.mpr ⟨hiP, hiD⟩)
      · intro i hiD hnV
        have hh := hK i (mem_union_right _ hiD)
        have he : b ≡ a [MOD q i] := by simpa [f, hiD, hnV] using hh
        exact he.symm
      · intro i hi
        have hiD := hV' hi
        have hh := hK i (mem_union_right _ hiD)
        have he : b ≡ q i - a % q i [MOD q i] := by simpa [f, hiD, hi] using hh
        exact (hminus i hiD).mp he
  rw [hA V hV, hA ∅ (empty_subset _)]
  have hclose := sieved_progressions_close N C K hdis q (f V) (f ∅)
    (fun i hi => hq i (hsub hi)) (fun i hi j hj hij => hp (hsub hi) (hsub hj) hij)
    (T V) (T ∅) (fun b => mem_filter) (fun b => mem_filter)
  exact hclose.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by norm_num) (card_le_card (sdiff_subset (s := P) (t := D)))) (by norm_num))

def presieveBucket (N d r : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun a => (a ≡ 1 [MOD 4]) ∧ (a ≡ r [MOD d * d]) ∧
    ∀ p ∈ P, ¬ p * p ∣ a

theorem bucket_diagonal {N d r a : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (ha : a ∈ presieveBucket N d r P) : ∀ p ∈ P, ¬ p * p ∣ a + a := by
  intro p hp hd
  have hgood := (mem_filter.mp ha).2.2.2 p hp
  have hpo : Odd p := (hP p hp).1.odd_of_ne_two (hP p hp).2
  have hc : (p * p).Coprime 2 := (hpo.mul hpo).coprime_two_right
  exact hgood (hc.dvd_of_dvd_mul_left (by simpa [two_mul] using hd))

theorem bucket_CRT_data (N d r : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hd : Odd d) (hdP : ∀ p ∈ P, d.Coprime p) :
    let B : Finset ℕ := {0, 1}
    let m (p : ℕ) := if p = 0 then 2 else if p = 1 then d else p
    let q (p : ℕ) := m p * m p
    let t (p : ℕ) := if p = 0 then 1 else r
    (∀ p ∈ P, q p = p * p) ∧
      Disjoint P B ∧ (∀ p ∈ P ∪ B, q p ≠ 0) ∧
      Set.Pairwise ((P ∪ B : Finset ℕ) : Set ℕ) (fun i j => (q i).Coprime (q j)) ∧
      (∀ b, b ∈ presieveBucket N d r P ↔ b ∈ Icc 1 N ∧
        (∀ i ∈ B, b ≡ t i [MOD q i]) ∧ (∀ i ∈ P, ¬ b ≡ 0 [MOD q i])) := by
  classical
  let B : Finset ℕ := {0, 1}
  let m (p : ℕ) := if p = 0 then 2 else if p = 1 then d else p
  let q (p : ℕ) := m p * m p
  let t (p : ℕ) := if p = 0 then 1 else r
  let S := presieveBucket N d r P
  have hp01 (p : ℕ) (hp : p ∈ P) : p ≠ 0 ∧ p ≠ 1 := by
    have hh := (hP p hp).1.two_le
    exact ⟨by omega, by omega⟩
  have hm (p : ℕ) (hp : p ∈ P) : m p = p := by
    have h := hp01 p hp
    simp [m, h.1, h.2]
  have hq (p : ℕ) (hp : p ∈ P) : q p = p * p := by simp [q, hm p hp]
  have hPB : Disjoint P B := by
    apply disjoint_left.mpr
    intro p hp hB
    have hh := hp01 p hp
    simp [B, hh.1, hh.2] at hB
  have hqpos : ∀ p ∈ P ∪ B, q p ≠ 0 := by
    intro p hp
    rcases mem_union.mp hp with hP' | hB
    · rw [hq p hP']
      exact Nat.mul_ne_zero (hP p hP').1.ne_zero (hP p hP').1.ne_zero
    · simp only [B, mem_insert, mem_singleton] at hB
      rcases hB with rfl | rfl
      · norm_num [q, m]
      · have hd0 : d ≠ 0 := by obtain ⟨k, hk⟩ := hd; omega
        simp [q, m, hd0]
  have hpair : Set.Pairwise ((P ∪ B : Finset ℕ) : Set ℕ)
      (fun i j => (q i).Coprime (q j)) := by
    intro i hi j hj hij
    suffices hc : (m i).Coprime (m j) by simpa [q, pow_two] using hc.pow 2 2
    change i ∈ P ∪ B at hi
    change j ∈ P ∪ B at hj
    rcases mem_union.mp hi with hi | hi <;> rcases mem_union.mp hj with hj | hj
    · rw [hm i hi, hm j hj]
      exact (Nat.coprime_primes (hP i hi).1 (hP j hj).1).mpr hij
    · simp only [B, mem_insert, mem_singleton] at hj
      rcases hj with rfl | rfl
      · simpa [hm i hi, m] using ((hP i hi).1.odd_of_ne_two (hP i hi).2).coprime_two_right
      · simpa [hm i hi, m] using (hdP i hi).symm
    · simp only [B, mem_insert, mem_singleton] at hi
      rcases hi with rfl | rfl
      · simpa [hm j hj, m] using ((hP j hj).1.odd_of_ne_two (hP j hj).2).coprime_two_left
      · simpa [hm j hj, m] using hdP j hj
    · simp only [B, mem_insert, mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact (hij rfl).elim
      · simpa [m] using hd.coprime_two_left
      · simpa [m] using hd.coprime_two_right
      · exact (hij rfl).elim
  have hS : ∀ b, b ∈ S ↔ b ∈ Icc 1 N ∧ (∀ i ∈ B, b ≡ t i [MOD q i]) ∧
      (∀ i ∈ P, ¬ b ≡ 0 [MOD q i]) := by
    intro b
    simp only [S, presieveBucket, mem_filter]
    constructor
    · rintro ⟨hb, h4, hd, hP'⟩
      refine ⟨hb, ?_, fun p hp => ?_⟩
      · intro i hi
        simp only [B, mem_insert, mem_singleton] at hi
        rcases hi with rfl | rfl
        · simpa [q, m, t] using h4
        · simpa [q, m, t] using hd
      · rw [hq p hp, Nat.modEq_zero_iff_dvd]
        exact hP' p hp
    · rintro ⟨hb, hB, hP'⟩
      refine ⟨hb, ?_, ?_, fun p hp => ?_⟩
      · simpa [q, m, t] using hB 0 (by simp [B])
      · simpa [q, m, t] using hB 1 (by simp [B])
      · simpa [hq p hp, Nat.modEq_zero_iff_dvd] using hP' p hp
  exact ⟨hq, hPB, hqpos, hpair, hS⟩

theorem bucket_profile_bound (N d r : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hd : Odd d) (hdP : ∀ p ∈ P, d.Coprime p)
    {a : ℕ} (ha : a ∈ presieveBucket N d r P) {D V : Finset ℕ} (hD : D ⊆ P) (hV : V ⊆ D) :
    |(profileCount (presieveBucket N d r P) D V
      (fun p b => a ≡ b [MOD p * p]) (fun p b => opposite p a b) : ℝ) -
      profileCount (presieveBucket N d r P) D ∅
        (fun p b => a ≡ b [MOD p * p]) (fun p b => opposite p a b)| ≤ 2 * (2 : ℝ) ^ P.card := by
  classical
  let B : Finset ℕ := {0, 1}
  let m (p : ℕ) := if p = 0 then 2 else if p = 1 then d else p
  let q (p : ℕ) := m p * m p
  let t (p : ℕ) := if p = 0 then 1 else r
  let S := presieveBucket N d r P
  obtain ⟨hq, hPB, hqpos, hpair, hS⟩ := bucket_CRT_data N d r P hP hd hdP
  change ∀ p ∈ P, q p = p * p at hq
  have ha' (p : ℕ) (hp : p ∈ P) : 0 < a % q p := by
    rw [hq p hp]
    have hh := (mem_filter.mp ha).2.2.2 p hp
    rw [Nat.dvd_iff_mod_eq_zero] at hh
    omega
  have hv := presieve_profile_close N a P B D V q t hPB hD hV hqpos hpair ha' S hS
  have heq (W : Finset ℕ) (hW : W ⊆ D) :
      profileCount S D W (fun i b => a ≡ b [MOD q i]) (fun i b => a % q i + b % q i = q i) =
      profileCount S D W (fun p b => a ≡ b [MOD p * p]) (fun p b => opposite p a b) := by
    unfold profileCount
    congr 1
    ext b
    simp only [mem_filter]
    apply and_congr_right
    intro hb
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun p hp hnot => by simpa [hq p (hD hp)] using h₁ p hp hnot,
        fun p hp => by simpa [opposite, hq p (hD (hW hp))] using h₂ p hp⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun p hp hnot => by simpa [hq p (hD hp)] using h₁ p hp hnot,
        fun p hp => by simpa [opposite, hq p (hD (hW hp))] using h₂ p hp⟩
  rw [heq V hV, heq ∅ (empty_subset _)] at hv
  exact hv

def signUniverse (N : ℕ) (P : Finset ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 N).biUnion (keys P)

/-- The second moment bounds the deviation in one fixed residue class. -/
theorem bucket_variance (N d r : ℕ) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hd : Odd d)
    (hdP : ∀ p ∈ P, d.Coprime p) :
    let U := signUniverse N P
    let S := presieveBucket N d r P
    let ρ := ((2 : ℝ) ^ P.card)⁻¹
    ∑ ω ∈ U.powerset, (frequency S (signChoices U P) ω - (S.card : ℝ) * ρ) ^ 2 ≤
      (U.powerset.card : ℝ) * (ρ ^ 2 * N * (2 * (2 : ℝ) ^ P.card * 3 ^ P.card)) := by
  let U := signUniverse N P
  let S := presieveBucket N d r P
  let ρ := ((2 : ℝ) ^ P.card)⁻¹
  have hsub : S ⊆ Icc 1 N := filter_subset _ _
  have hU : ∀ a ∈ S, keys P a ⊆ U := by
    intro a ha k hk
    exact mem_biUnion.mpr ⟨a, hsub ha, hk⟩
  have hvar := sign_fiber_variance P S U (fun p hp => (hprime p hp).1)
    (fun a ha => bucket_diagonal hprime ha) hU
    (E := 2 * (2 : ℝ) ^ P.card) (by positivity)
    (fun a ha D hD _ V hV =>
      bucket_profile_bound N d r P hprime hd hdP ha (mem_powerset.mp hD) (mem_powerset.mp hV))
  have hcard : (S.card : ℝ) ≤ N := by
    exact_mod_cast (show S.card ≤ N by simpa [Nat.card_Icc] using card_le_card hsub)
  refine hvar.trans ?_
  let C := 2 * (2 : ℝ) ^ P.card * 3 ^ P.card
  change (U.powerset.card : ℝ) * ρ ^ 2 * (S.card : ℝ) * C ≤
    (U.powerset.card : ℝ) * (ρ ^ 2 * N * C)
  calc
    _ ≤ (U.powerset.card : ℝ) * ρ ^ 2 * (N : ℝ) * C :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by positivity)) (by positivity)
    _ = _ := by ring

theorem simultaneous_buckets (N : ℕ) (P : Finset ℕ) (J : Finset (ℕ × ℕ))
    (hprime : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hJ : ∀ j ∈ J, Odd j.1 ∧ (∀ p ∈ P, j.1.Coprime p))
    {E : ℝ} (hE : 0 ≤ E)
    (herr : let ρ := ((2 : ℝ) ^ P.card)⁻¹
      (J.card : ℝ) * (ρ ^ 2 * N * (2 * (2 : ℝ) ^ P.card * 3 ^ P.card)) ≤ E ^ 2) :
    let U := signUniverse N P
    let ρ := ((2 : ℝ) ^ P.card)⁻¹
    ∃ ω ∈ U.powerset, ∀ j ∈ J, |frequency (presieveBucket N j.1 j.2 P) (signChoices U P) ω -
      ((presieveBucket N j.1 j.2 P).card : ℝ) * ρ| ≤ E := by
  let U := signUniverse N P
  let ρ := ((2 : ℝ) ^ P.card)⁻¹
  let err (ω : Finset (ℕ × ℕ)) (j : ℕ × ℕ) :=
    frequency (presieveBucket N j.1 j.2 P) (signChoices U P) ω -
      ((presieveBucket N j.1 j.2 P).card : ℝ) * ρ
  have hne : U.powerset.Nonempty := ⟨∅, by simp⟩
  exact exists_uniform_errors U.powerset J hne err hE
    (fun j hj => bucket_variance N j.1 j.2 P hprime (hJ j hj).1 (hJ j hj).2) herr

theorem opposite_of_square_dvd {p a b : ℕ} (hp : p.Prime) (ha : ¬ p * p ∣ a)
    (hd : p * p ∣ a + b) : opposite p a b := by
  let q := p * p
  let r := a % q
  let s := b % q
  have hq : 0 < q := Nat.mul_pos hp.pos hp.pos
  have hr : r < q := Nat.mod_lt _ hq
  have hs : s < q := Nat.mod_lt _ hq
  have hr0 : 0 < r := by
    rw [Nat.dvd_iff_mod_eq_zero] at ha
    change r ≠ 0 at ha
    omega
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod] at hd
  obtain ⟨k, hk⟩ := Nat.dvd_iff_mod_eq_zero.mpr (show (r + s) % q = 0 from hd)
  have hk₀ : k ≠ 0 := by intro hz; simp [hz] at hk; omega
  have hk₂ : ¬ 2 ≤ k := by
    intro hj
    have hm := Nat.mul_le_mul_left q hj
    omega
  have hk₁ : k = 1 := by omega
  exact show r + s = q from by simpa [hk₁] using hk

theorem selected_small_safe {N : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    {a b : ℕ} {ω : Finset (ℕ × ℕ)}
    (ha : a ∈ presieveBucket N 1 0 P) (hb : b ∈ presieveBucket N 1 0 P)
    (ha' : ω ∈ signChoices (signUniverse N P) P a)
    (hb' : ω ∈ signChoices (signUniverse N P) P b) :
    (¬ 2 * 2 ∣ a + b) ∧ ∀ p ∈ P, ¬ p * p ∣ a + b := by
  have h4a := (mem_filter.mp ha).2.1
  have h4b := (mem_filter.mp hb).2.1
  have h4 := h4a.add h4b
  constructor
  · intro h
    have hz := Nat.modEq_zero_iff_dvd.mpr (show 4 ∣ a+b from h)
    have hf := h4.symm.trans hz
    norm_num [Nat.ModEq] at hf
  · intro p hp hd
    have hdiag₁ := bucket_diagonal hP ha p hp
    have hdiag₂ := bucket_diagonal hP hb p hp
    have hop := opposite_of_square_dvd (hP p hp).1 ((mem_filter.mp ha).2.2.2 p hp) hd
    have hkey := (key_eq_iff (hP p hp).1).mpr (Or.inr hop)
    have hK₁ : signKey p a ∈ keys P a := mem_image_of_mem _ hp
    have hK₂ : signKey p a ∈ keys P b := by rw [hkey]; exact mem_image_of_mem _ hp
    have hsign₁ := ((mem_assignments_iff _).mp ha').2 _ hK₁
    have hsign₂ := ((mem_assignments_iff _).mp hb').2 _ hK₂
    have hsame := (sign_agree_iff_eq (hP p hp).1 hdiag₁ hdiag₂ hkey).mp (hsign₁.symm.trans hsign₂)
    change a % (p * p) = b % (p * p) at hsame
    change a % (p * p) + b % (p * p) = p * p at hop
    apply hdiag₁
    have hh : a % (p * p) + a % (p * p) = p * p := by omega
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hh, Nat.mod_self]

theorem full_ideal_product {α : Type*} (P : Finset α) (w : α → ℝ) :
    idealTrunc P.card P w = ∏ i ∈ P, (1 - w i) := by
  classical
  have hfilter : P.powerset.filter (fun D => D.card ≤ P.card) = P.powerset :=
    filter_true_of_mem fun D hD => card_le_card (mem_powerset.mp hD)
  unfold idealTrunc
  rw [hfilter]
  simpa only [prod_const_one, mul_one] using (prod_sub (fun _ : α => (1 : ℝ)) w P).symm

theorem presieve_density_approx {α : Type*} [DecidableEq α]
    (N : ℕ) (P B : Finset α) (q r : α → ℕ)
    (hPB : Disjoint P B) (hq : ∀ i ∈ P ∪ B, q i ≠ 0)
    (hp : Set.Pairwise ((P ∪ B : Finset α) : Set α) (fun i j => (q i).Coprime (q j)))
    (T : Finset ℕ) (hT : ∀ a, a ∈ T ↔ a ∈ Icc 1 N ∧ ∀ i ∈ B, a ≡ r i [MOD q i]) :
    |((avoided P T (fun i a => a ≡ 0 [MOD q i])).card : ℝ) -
      ((N : ℝ) / (∏ i ∈ B, q i : ℕ)) * ∏ i ∈ P, (1 - 1 / (q i : ℝ))| ≤
      2 * (2 : ℝ) ^ P.card + 1 := by
  classical
  let u (i : α) := 1 / (q i : ℝ)
  let Z (i : α) (a : ℕ) := a ≡ 0 [MOD q i]
  let M := (N : ℝ) / (∏ i ∈ B, q i : ℕ)
  have hQR (i : α) (hi : i ∈ P) : (1 : ℝ) ≤ q i := by
    exact_mod_cast Nat.pos_of_ne_zero (hq i (mem_union_left _ hi))
  have hu (i : α) (hi : i ∈ P) : 0 ≤ u i ∧ u i ≤ 1 :=
    ⟨by positivity, (div_le_one (by linarith [hQR i hi])).mpr (hQR i hi)⟩
  have hT' : |(T.card : ℝ) - M| ≤ 1 :=
    crt_progression_count N r (fun i hi => hq i (mem_union_right _ hi))
      (fun i hi j hj hne => hp (mem_union_right _ hi) (mem_union_right _ hj) hne) T hT
  have hmul (D : Finset α) (hD : D ⊆ P) :
      (N : ℝ) / (∏ i ∈ D ∪ B, q i : ℕ) = M * ∏ i ∈ D, u i := by
    have hdis := disjoint_of_subset_left hD hPB
    rw [prod_union hdis, Nat.cast_mul]
    simp [M, u, Finset.prod_inv_distrib, Nat.cast_prod, div_eq_mul_inv, mul_comm, mul_assoc]
  have hcount : ∀ D ∈ P.powerset.filter (fun D => D.card ≤ P.card),
      ∀ K : Finset ℕ, (∀ b, b ∈ K ↔ b ∈ T ∧ ∀ p ∈ D, Z p b) →
        |(K.card : ℝ) - (T.card : ℝ) * ∏ i ∈ D, u i| ≤ 2 := by
    intro D hDm K hK
    have hD := mem_powerset.mp (mem_filter.mp hDm).1
    have hdis := disjoint_of_subset_left hD hPB
    have hsub : D ∪ B ⊆ P ∪ B := union_subset_union hD (fun _ h => h)
    let z (i : α) := if i ∈ D then 0 else r i
    have hk := crt_progression_count N z (fun i hi => hq i (hsub hi))
      (fun i hi j hj hne => hp (hsub hi) (hsub hj) hne) K (fun a => by
        rw [hK, hT, and_assoc]
        apply and_congr_right
        intro _
        constructor
        · rintro ⟨hB, hD⟩ i hi
          by_cases hd : i ∈ D
          · simpa [z, hd] using hD i hd
          · have hiB := (mem_union.mp hi).resolve_left hd
            simpa [z, hd] using hB i hiB
        · intro h
          constructor
          · intro i hi
            have hn : i ∉ D := fun hd => (disjoint_left.mp hdis) hd hi
            simpa [z, hn] using h i (mem_union_right _ hi)
          · intro i hi
            simpa [z, hi] using h i (mem_union_left _ hi))
    rw [hmul D hD] at hk
    let m := ∏ i ∈ D, u i
    have hm0 : 0 ≤ m := prod_nonneg fun i hi => (hu i (hD hi)).1
    have hm1 : m ≤ 1 := prod_le_one (fun i hi => (hu i (hD hi)).1) (fun i hi => (hu i (hD hi)).2)
    have hsmall : |M * m - (T.card : ℝ) * m| ≤ 1 := by
      rw [← sub_mul, abs_mul, abs_of_nonneg hm0, abs_sub_comm]
      exact (mul_le_mul_of_nonneg_right hT' hm0).trans (by simpa using hm1)
    have hk' : |(K.card : ℝ) - M * m| ≤ 1 := hk
    change |(K.card : ℝ) - (T.card : ℝ) * m| ≤ 2
    exact (abs_sub_le _ (M * m) _).trans ((add_le_add hk' hsmall).trans (by norm_num))
  have hraw := truncSieve_approx P.card P T Z u hcount
  have hs : ((avoided P T Z).card : ℝ) = (truncSieve P.card P T Z : ℝ) := by
    exact_mod_cast full_inclusion_exclusion P T Z
  have hfilter : P.powerset.filter (fun D => D.card ≤ P.card) = P.powerset :=
    filter_true_of_mem fun D hD => card_le_card (mem_powerset.mp hD)
  rw [← hs, full_ideal_product, hfilter, card_powerset] at hraw
  push_cast at hraw
  let Q := ∏ i ∈ P, (1 - u i)
  have hQ0 : 0 ≤ Q := prod_nonneg fun i hi => sub_nonneg.mpr (hu i hi).2
  have hQ1 : Q ≤ 1 := prod_le_one (fun i hi => sub_nonneg.mpr (hu i hi).2)
    (fun i hi => sub_le_self _ (hu i hi).1)
  have hbig : |(T.card : ℝ) * Q - M * Q| ≤ 1 := by
    rw [← sub_mul, abs_mul, abs_of_nonneg hQ0]
    exact (mul_le_mul_of_nonneg_right hT' hQ0).trans (by simpa using hQ1)
  exact (abs_sub_le _ ((T.card : ℝ) * Q) _).trans (add_le_add hraw hbig)

noncomputable def baseCenter (N : ℕ) (P : Finset ℕ) : ℝ :=
  (N : ℝ) / 4 * ∏ p ∈ P, (1 - 1 / (p : ℝ) ^ 2)

theorem explicit_bucket_centers (N d r : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hd : Odd d) (hdP : ∀ p ∈ P, d.Coprime p) :
    |((presieveBucket N d r P).card : ℝ) - baseCenter N P / (d : ℝ) ^ 2| ≤
      2 * (2 : ℝ) ^ P.card + 1 := by
  classical
  let B : Finset ℕ := {0, 1}
  let m (p : ℕ) := if p = 0 then 2 else if p = 1 then d else p
  let q (p : ℕ) := m p * m p
  let t (p : ℕ) := if p = 0 then 1 else r
  obtain ⟨hq, hPB, hqpos, hpair, hS⟩ := bucket_CRT_data N d r P hP hd hdP
  change ∀ p ∈ P, q p = p * p at hq
  change ∀ a, a ∈ presieveBucket N d r P ↔ a ∈ Icc 1 N ∧
    (∀ i ∈ B, a ≡ t i [MOD q i]) ∧ ∀ i ∈ P, ¬ a ≡ 0 [MOD q i] at hS
  let T := (Icc 1 N).filter fun a => ∀ i ∈ B, a ≡ t i [MOD q i]
  have hbound := presieve_density_approx N P B q t hPB hqpos hpair T (fun a => mem_filter)
  have hpool : avoided P T (fun i a => a ≡ 0 [MOD q i]) = presieveBucket N d r P := by
    ext a
    rw [hS]
    simp only [avoided, T, mem_filter, and_assoc]
  have hBq : (∏ i ∈ B, q i) = 4 * (d * d) := by norm_num [B, q, m]
  have hPq : (∏ i ∈ P, (1 - 1 / (q i : ℝ))) = ∏ p ∈ P, (1 - 1 / (p : ℝ) ^ 2) := by
    apply prod_congr rfl
    intro p hp
    have hqp : q p = p * p := hq p hp
    simp [hqp, pow_two]
  rw [hpool, hBq, hPq] at hbound
  have heq : ((N : ℝ) / ((4 * (d * d) : ℕ) : ℝ)) * (∏ p ∈ P, (1 - 1 / (p : ℝ) ^ 2)) =
      baseCenter N P / (d : ℝ) ^ 2 := by
    push_cast
    simp [baseCenter, pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  simpa only [heq] using hbound

theorem base_center_lower (N y : ℕ) (hy : 3 ≤ y) (P : Finset ℕ) (hP : P ⊆ Icc 3 y) :
    (N : ℝ) / 4 * exp (-1) ≤ baseCenter N P := by
  have hw (p : ℕ) (hp : p ∈ P) : 0 ≤ 1 / (p : ℝ) ^ 2 ∧ 1 / (p : ℝ) ^ 2 ≤ 1 / 2 := by
    have hp₃ := (mem_Icc.mp (hP hp)).1
    have hp₃R : (3 : ℝ) ≤ p := by exact_mod_cast hp₃
    constructor
    · positivity
    · exact (div_le_div_iff₀ (by positivity) (by norm_num)).mpr (by nlinarith)
  have hs : (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ≤ 4 / 9 := by
    exact (sum_le_sum_of_subset_of_nonneg hP (fun p _ _ => by positivity)).trans
      ((sum_inv_sq_ge_three y hy).trans (sub_le_self _ (by positivity)))
  have hle : exp (-1) ≤ ∏ p ∈ P, (1 - 1 / (p : ℝ) ^ 2) :=
    (exp_le_exp.mpr (by linarith)).trans (ideal_product_lower P _ hw)
  exact mul_le_mul_of_nonneg_left hle (by positivity)

theorem uniform_multiresidue {α : Type*} (S : Finset ℕ) {P : Finset α} {q : α → ℕ}
    (R : α → Finset ℕ) (hR : ∀ i ∈ P, ∀ r ∈ R i, r < q i)
    (hq : ∀ i ∈ P, q i ≠ 0)
    (hp : Set.Pairwise (P : Set α) (fun i j => (q i).Coprime (q j)))
    {E : ℝ}
    (hunif : ∀ r : ℕ,
      |((S.filter fun a => a ≡ r [MOD ∏ i ∈ P, q i]).card : ℝ) -
        (S.card : ℝ) / (∏ i ∈ P, q i : ℕ)| ≤ E) :
    ∀ T : Finset ℕ, (∀ a, a ∈ T ↔ a ∈ S ∧ ∀ i ∈ P, a % q i ∈ R i) →
      |(T.card : ℝ) - (S.card : ℝ) * ∏ i ∈ P, ((R i).card : ℝ) / (q i : ℝ)| ≤
        E * ∏ i ∈ P, ((R i).card : ℝ) := by
  classical
  intro T hT
  let V := Fintype.piFinset fun i : P => R i
  let f (a : ℕ) (i : P) := a % q i
  let fibers (v : P → ℕ) := S.filter fun a => f a = v
  let m := (S.card : ℝ) / (∏ i ∈ P, q i : ℕ)
  have hcard : V.card = ∏ i ∈ P, (R i).card := by
    rw [Fintype.card_piFinset]
    simpa only [attach_eq_univ] using prod_attach P (fun i => (R i).card)
  have hsum : ∑ v ∈ V, (fibers v).card = T.card := by
    rw [show (∑ v ∈ V, (fibers v).card) = (S.filter fun a => f a ∈ V).card from
      sum_card_fiberwise_eq_card_filter _ _ _]
    congr 1
    ext a
    simp only [hT, mem_filter, V, Fintype.mem_piFinset, f, Subtype.forall]
  have hb (v : P → ℕ) (hv : v ∈ V) : |((fibers v).card : ℝ) - m| ≤ E := by
    let r (i : α) := if hi : i ∈ P then v ⟨i, hi⟩ else 0
    let z := Nat.chineseRemainderOfFinset r q P hq hp
    have heq : fibers v = S.filter fun a => a ≡ (z : ℕ) [MOD ∏ i ∈ P, q i] := by
      ext a
      simp only [fibers, mem_filter, funext_iff]
      apply and_congr_right
      intro _
      rw [modEq_finset_prod hp]
      constructor
      · intro ha i hi
        have hv' := Fintype.mem_piFinset.mp hv (⟨i, hi⟩ : P)
        have hm := Nat.mod_eq_of_lt (hR i hi _ hv')
        have ha' : a ≡ r i [MOD q i] := by simpa [Nat.ModEq, r, hi, hm, f] using ha ⟨i, hi⟩
        exact ha'.trans (z.prop i hi).symm
      · intro ha i
        have hi := i.property
        have hx := (ha i hi).trans (z.prop i hi)
        have hv' := Fintype.mem_piFinset.mp hv i
        have hm := Nat.mod_eq_of_lt (hR i hi (v i) hv')
        simpa [Nat.ModEq, r, hi, hm, f] using hx
    rw [heq]
    exact hunif _
  have hreal : ∑ v ∈ V, ((fibers v).card : ℝ) = T.card := by exact_mod_cast hsum
  have hcast : (V.card : ℝ) = ∏ i ∈ P, ((R i).card : ℝ) := by exact_mod_cast hcard
  rw [prod_div_distrib, ← hcast, ← Nat.cast_prod]
  have hcalc : (S.card : ℝ) * ((V.card : ℝ) / (∏ i ∈ P, q i : ℕ)) = (V.card : ℝ) * m := by
    simp [m, div_eq_mul_inv, mul_comm, mul_assoc]
  rw [hcalc, ← hreal, ← nsmul_eq_mul, ← sum_const, ← sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hb).trans (by simp [mul_comm]))

theorem trunc_count_bound {α : Type*} (P : Finset α) (k : ℕ) :
    (P.powerset.filter (fun D => D.card ≤ k)).card ≤ (k + 1) * (P.card + 1) ^ k := by
  let Q := P.powerset.filter (fun D => D.card ≤ k)
  have hm : ∀ D ∈ Q, D.card ∈ range (k + 1) := by
    intro D hD
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hD).2)
  have hs : Q.card = ∑ j ∈ range (k + 1), P.card.choose j := by
    have hf := sum_card_fiberwise_eq_card_filter Q (range (k + 1)) Finset.card
    rw [filter_true_of_mem hm] at hf
    rw [← hf]
    exact sum_congr rfl fun j hj => by
      have hEq : Q.filter (fun x => x.card = j) = P.powersetCard j := by
        ext D
        simp only [Q, mem_filter, mem_powerset, mem_powersetCard]
        exact ⟨fun h => ⟨h.1.1, h.2⟩,
          fun h => ⟨⟨h.1, h.2.symm ▸ Nat.le_of_lt_succ (mem_range.mp hj)⟩, h.2⟩⟩
      rw [hEq, card_powersetCard]
  rw [hs]
  calc
    _ ≤ ∑ _j ∈ range (k + 1), (P.card + 1) ^ k := sum_le_sum (by
      intro j hj
      have hj' := Nat.le_of_lt_succ (mem_range.mp hj)
      exact (Nat.choose_le_pow _ _).trans
        ((Nat.pow_le_pow_left (Nat.le_succ _) _).trans (Nat.pow_le_pow_right (by omega) hj')))
    _ = _ := by simp

theorem truncSieve_approx_mass {α β : Type*} (k : ℕ) (P : Finset α) (S : Finset β)
    (B : α → β → Prop) (w : α → ℝ) (mass : ℝ) {E : ℝ}
    (hpoint : ∀ D ∈ P.powerset.filter (fun D => D.card ≤ k),
      ∀ K : Finset β, (∀ b, b ∈ K ↔ b ∈ S ∧ ∀ p ∈ D, B p b) →
        |(K.card : ℝ) - mass * ∏ p ∈ D, w p| ≤ E) :
    |(truncSieve k P S B : ℝ) - mass * idealTrunc k P w| ≤
      E * (P.powerset.filter (fun D => D.card ≤ k)).card := by
  classical
  let T := P.powerset.filter (fun D => D.card ≤ k)
  let K (D : Finset α) := S.filter fun b => ∀ p ∈ D, B p b
  let F (D : Finset α) :=
    (-1 : ℝ) ^ D.card * ((K D).card - mass * ∏ p ∈ D, w p)
  have heq : (truncSieve k P S B : ℝ) - mass * idealTrunc k P w =
      ∑ D ∈ T, F D := by
    simp only [truncSieve, idealTrunc, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, Int.cast_natCast, T, F, K]
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun D _ => by ring
  rw [heq]
  calc
    |∑ D ∈ T, F D| ≤ ∑ D ∈ T, |F D| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _D ∈ T, E := sum_le_sum (by
      intro D hD
      simp only [F, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hpoint D hD (K D) (fun b => mem_filter))
    _ = _ := by simp only [sum_const, nsmul_eq_mul, T, mul_comm]

theorem ideal_sieve_lower {α β : Type*} {k : ℕ} (hk : Odd k) (P : Finset α)
    (S : Finset β) (B : α → β → Prop) (w : α → ℝ) {mass E : ℝ} (hm : 0 ≤ mass)
    (hw : ∀ p ∈ P, 0 ≤ w p)
    (hpoint : ∀ D ∈ P.powerset.filter (fun D => D.card ≤ k),
      ∀ K : Finset β, (∀ b, b ∈ K ↔ b ∈ S ∧ ∀ p ∈ D, B p b) →
        |(K.card : ℝ) - mass * ∏ p ∈ D, w p| ≤ E) :
    mass * ((∏ p ∈ P, (1 - w p)) - exp (2 * ∑ p ∈ P, w p) / (2 : ℝ) ^ (k + 1)) -
      E * (P.powerset.filter (fun D => D.card ≤ k)).card ≤ (avoided P S B).card := by
  have hb : (truncSieve k P S B : ℝ) ≤ (avoided P S B).card :=
    by exact_mod_cast bonferroni_lower hk P S B
  have h₁ := (abs_le.mp (ideal_trunc_error P k w hw)).2
  have h₂ := (abs_le.mp (truncSieve_approx_mass k P S B w mass hpoint)).1
  have h₃ := mul_le_mul_of_nonneg_left (sub_le_comm.mp h₁) hm
  linarith

theorem ideal_sieve_upper {α β : Type*} {k : ℕ} (hk : Even k) (P : Finset α)
    (S : Finset β) (B : α → β → Prop) (w : α → ℝ) {mass E : ℝ} (hm : 0 ≤ mass)
    (hw : ∀ p ∈ P, 0 ≤ w p)
    (hpoint : ∀ D ∈ P.powerset.filter (fun D => D.card ≤ k),
      ∀ K : Finset β, (∀ b, b ∈ K ↔ b ∈ S ∧ ∀ p ∈ D, B p b) →
        |(K.card : ℝ) - mass * ∏ p ∈ D, w p| ≤ E) :
    ((avoided P S B).card : ℝ) ≤
      mass * ((∏ p ∈ P, (1 - w p)) + exp (2 * ∑ p ∈ P, w p) / (2 : ℝ) ^ (k + 1)) +
        E * (P.powerset.filter (fun D => D.card ≤ k)).card := by
  have hb : ((avoided P S B).card : ℝ) ≤ (truncSieve k P S B : ℝ) :=
    by exact_mod_cast bonferroni_upper hk P S B
  have h₁ := (abs_le.mp (ideal_trunc_error P k w hw)).1
  have h₂ := (abs_le.mp (truncSieve_approx_mass k P S B w mass hpoint)).2
  have hh : idealTrunc k P w ≤
      (∏ p ∈ P, (1 - w p)) + exp (2 * ∑ p ∈ P, w p) / (2 : ℝ) ^ (k + 1) := by linarith
  have h₃ := mul_le_mul_of_nonneg_left hh hm
  linarith

noncomputable def selectedPool (N : ℕ) (P : Finset ℕ) (ω : Finset (ℕ × ℕ)) : Finset ℕ := by
  classical
  exact (presieveBucket N 1 0 P).filter (fun a => ω ∈ signChoices (signUniverse N P) P a)

theorem pool_bucket_eq (N d r : ℕ) (P : Finset ℕ) (ω : Finset (ℕ × ℕ)) :
    (((selectedPool N P ω).filter (fun a => a ≡ r [MOD d * d])).card : ℝ) =
      frequency (presieveBucket N d r P) (signChoices (signUniverse N P) P) ω := by
  classical
  unfold frequency
  have heq : (selectedPool N P ω).filter (fun a => a ≡ r [MOD d * d]) =
      (presieveBucket N d r P).filter (fun a => ω ∈ signChoices (signUniverse N P) P a) := by
    ext a
    simp only [selectedPool, presieveBucket, mem_filter, Nat.one_mul, Nat.modEq_one, true_and]
    tauto
  rw [heq]
  congr 2
  ext a
  simp only [mem_filter]

theorem pool_small_sums {N y : ℕ} (ω : Finset (ℕ × ℕ)) :
    let P := (Nat.primesLE y).erase 2
    let S := selectedPool N P ω
    S ⊆ Icc 1 N ∧ (∀ a ∈ S, Odd a) ∧
      ∀ a ∈ S, ∀ b ∈ S, ∀ p ∈ Nat.primesLE y, ¬ p * p ∣ a + b := by
  classical
  let P := (Nat.primesLE y).erase 2
  let S := selectedPool N P ω
  have hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2 := by
    intro p hp
    exact ⟨(Nat.mem_primesLE.mp (mem_erase.mp hp).2).2, (mem_erase.mp hp).1⟩
  have hmem (a : ℕ) (ha : a ∈ S) :
      a ∈ presieveBucket N 1 0 P ∧ ω ∈ signChoices (signUniverse N P) P a :=
    mem_filter.mp ha
  refine ⟨fun a ha => (mem_filter.mp (hmem a ha).1).1, ?_, ?_⟩
  · intro a ha
    have h := (mem_filter.mp (hmem a ha).1).2.1
    change a % 4 = 1 at h
    refine ⟨2 * (a / 4), ?_⟩
    have hh := Nat.mod_add_div a 4
    omega
  · intro a ha b hb p hp
    have hh := selected_small_safe hP (hmem a ha).1 (hmem b hb).1 (hmem a ha).2 (hmem b hb).2
    by_cases he : p = 2
    · simpa [he] using hh.1
    · exact hh.2 _ (mem_erase.mpr ⟨he, hp⟩)

theorem pool_uniform_from_centers (N : ℕ) (P : Finset ℕ) (J : Finset (ℕ × ℕ))
    (hprime : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hJ : ∀ j ∈ J, Odd j.1 ∧ (∀ p ∈ P, j.1.Coprime p))
    (hbase : (1, 0) ∈ J)
    {E M L : ℝ} (hE : 0 ≤ E) (hL : 0 ≤ L)
    (herr : let ρ := ((2 : ℝ) ^ P.card)⁻¹
      (J.card : ℝ) * (ρ ^ 2 * N * (2 * (2 : ℝ) ^ P.card * 3 ^ P.card)) ≤ E ^ 2)
    (hcenter : ∀ j ∈ J, |((presieveBucket N j.1 j.2 P).card : ℝ) -
      M / (j.1 : ℝ) ^ 2| ≤ L) :
    let ρ := ((2 : ℝ) ^ P.card)⁻¹
    ∃ ω ∈ (signUniverse N P).powerset,
      (M * ρ - (E + L * ρ) ≤ ((selectedPool N P ω).card : ℝ)) ∧
      ∀ j ∈ J,
      |(((selectedPool N P ω).filter fun a => a ≡ j.2 [MOD j.1 * j.1]).card : ℝ) -
        ((selectedPool N P ω).card : ℝ) / (j.1 : ℝ) ^ 2| ≤ 2 * (E + L * ρ) := by
  let ρ := ((2 : ℝ) ^ P.card)⁻¹
  have hρ : 0 ≤ ρ := by positivity
  obtain ⟨ω, hω, hvar⟩ := simultaneous_buckets N P J hprime hJ hE herr
  let S := selectedPool N P ω
  have hf (j : ℕ × ℕ) (hj : j ∈ J) :
      |(frequency (presieveBucket N j.1 j.2 P) (signChoices (signUniverse N P) P) ω) -
        (M * ρ) / (j.1 : ℝ) ^ 2| ≤ E + L * ρ := by
    let b := ((presieveBucket N j.1 j.2 P).card : ℝ) * ρ
    have hx : |b - (M * ρ) / (j.1 : ℝ) ^ 2| ≤ L * ρ := by
      rw [show b - (M * ρ) / (j.1 : ℝ) ^ 2 =
          (((presieveBucket N j.1 j.2 P).card : ℝ) - M / (j.1 : ℝ) ^ 2) * ρ by ring,
        abs_mul, abs_of_nonneg hρ]
      exact mul_le_mul_of_nonneg_right (hcenter j hj) hρ
    exact (abs_sub_le _ b _).trans (add_le_add (hvar j hj) hx)
  have hS : |(S.card : ℝ) - M * ρ| ≤ E + L * ρ := by
    have hcount := pool_bucket_eq N 1 0 P ω
    have hfilter : (S.filter fun a => a ≡ 0 [MOD 1 * 1]) = S := by simp [Nat.modEq_one]
    change ((S.filter fun a => a ≡ 0 [MOD 1 * 1]).card : ℝ) = _ at hcount
    rw [hfilter] at hcount
    rw [hcount]
    simpa only [Nat.cast_one, one_pow, div_one] using hf (1, 0) hbase
  refine ⟨ω, hω, by have h := (abs_le.mp hS).1; linarith, ?_⟩
  intro j hj
  have hh : 1 ≤ (j.1 : ℝ) ^ 2 := by
    have hpos : (1 : ℝ) ≤ j.1 := by
      have ⟨k, hk⟩ := (hJ j hj).1
      exact_mod_cast (show 1 ≤ j.1 by omega)
    nlinarith
  have hsecond : |(M * ρ) / (j.1 : ℝ) ^ 2 - ((S.card : ℝ) / (j.1 : ℝ) ^ 2)| ≤ E + L * ρ := by
    rw [← sub_div, abs_div, abs_sub_comm]
    simp only [abs_of_nonneg (sq_nonneg (j.1 : ℝ))]
    have hnon : 0 ≤ E + L * ρ := by positivity
    exact (div_le_div_of_nonneg_right hS (by positivity)).trans
      ((div_le_iff₀ (by linarith : 0 < (j.1 : ℝ) ^ 2)).mpr (le_mul_of_one_le_right hnon hh))
  rw [pool_bucket_eq]
  exact (abs_sub_le _ ((M * ρ) / (j.1 : ℝ) ^ 2) _).trans
    ((add_le_add (hf j hj) hsecond).trans_eq (by ring))

set_option maxHeartbeats 1000000 in
/-- One sign assignment works simultaneously for every class up to the chosen level. -/
theorem pool_fixed_level (N y D : ℕ) (hy : 3 ≤ y) (hD : 0 < D)
    {E : ℝ} (hE : 0 ≤ E)
    (hvar : let P := (Nat.primesLE y).erase 2
      let t := P.card
      let ρ := ((2 : ℝ) ^ t)⁻¹
      (((D + 1 : ℕ) : ℝ) * (D : ℝ) ^ 2) * (ρ ^ 2 * N * (2 * (2 : ℝ) ^ t * 3 ^ t)) ≤ E ^ 2) :
    let P := (Nat.primesLE y).erase 2
    let ρ := ((2 : ℝ) ^ P.card)⁻¹
    let Λ := E + (2 * (2 : ℝ) ^ P.card + 1) * ρ
    ∃ S : Finset ℕ, S ⊆ Icc 1 N ∧ (∀ a ∈ S, Odd a) ∧
      (∀ a ∈ S, ∀ b ∈ S, ∀ p ∈ Nat.primesLE y, ¬ p * p ∣ a + b) ∧
      ((N : ℝ) / 4 * exp (-1) * ρ - Λ ≤ (S.card : ℝ)) ∧
      ∀ d ≤ D, Odd d → (∀ p ∈ P, d.Coprime p) → ∀ r : ℕ,
        |((S.filter fun a => a ≡ r [MOD d * d]).card : ℝ) -
          (S.card : ℝ) / (d : ℝ) ^ 2| ≤ 2 * Λ := by
  classical
  let P := (Nat.primesLE y).erase 2
  let ρ := ((2 : ℝ) ^ P.card)⁻¹
  let J := ((range (D + 1)).product (range (D * D))).filter fun j =>
    Odd j.1 ∧ (∀ p ∈ P, j.1.Coprime p) ∧ j.2 < j.1 * j.1
  have hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2 := by
    intro p hp
    exact ⟨(Nat.mem_primesLE.mp (mem_erase.mp hp).2).2, (mem_erase.mp hp).1⟩
  have hPsmall : P ⊆ Icc 3 y := by
    intro p hp
    have h₂ := (hP p hp).1.two_le
    have hne := (hP p hp).2
    exact mem_Icc.mpr ⟨by omega, (Nat.mem_primesLE.mp (mem_erase.mp hp).2).1⟩
  have hJ : ∀ j ∈ J, Odd j.1 ∧ (∀ p ∈ P, j.1.Coprime p) := fun j hj =>
    ⟨(mem_filter.mp hj).2.1, (mem_filter.mp hj).2.2.1⟩
  have hbase : (1, 0) ∈ J := by
    have hsq : 0 < D * D := Nat.mul_pos hD hD
    simp [J, hD, hsq]
  have hJcard : (J.card : ℝ) ≤ ((D + 1 : ℕ) : ℝ) * (D : ℝ) ^ 2 := by
    have hsub : J ⊆ (range (D + 1)).product (range (D * D)) := filter_subset _ _
    have hle := card_le_card hsub
    have hle' : J.card ≤ (D + 1) * D ^ 2 := by simpa [sq] using hle
    exact_mod_cast hle'
  have hvar' : (J.card : ℝ) * (ρ ^ 2 * N * (2 * (2 : ℝ) ^ P.card * 3 ^ P.card)) ≤ E ^ 2 :=
    (mul_le_mul_of_nonneg_right hJcard (by positivity)).trans hvar
  obtain ⟨ω, hω, hsize, huni⟩ :=
    pool_uniform_from_centers N P J hP hJ hbase hE (by positivity) hvar'
      (fun j hj => explicit_bucket_centers N j.1 j.2 P hP (hJ j hj).1 (hJ j hj).2)
  let S := selectedPool N P ω
  have ⟨hS, hodd, hsmall⟩ := pool_small_sums (N := N) (y := y) ω
  refine ⟨S, hS, hodd, hsmall, ?_, ?_⟩
  · exact (sub_le_sub_right (mul_le_mul_of_nonneg_right (base_center_lower N y hy P hPsmall)
      (by positivity : 0 ≤ ρ)) _).trans hsize
  · intro d hd hdo hdp r
    let q := d * d
    have hd0 : 0 < d := by obtain ⟨k, hk⟩ := hdo; omega
    have hr : r % q < q := Nat.mod_lt _ (Nat.mul_pos hd0 hd0)
    have hqD : q ≤ D * D := Nat.mul_le_mul hd hd
    have hj : (d, r % q) ∈ J :=
      mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩,
        hdo, hdp, hr⟩
    have heq : (S.filter fun a => a ≡ r [MOD d * d]) =
        S.filter fun a => a ≡ r % q [MOD d * d] := by
      ext a
      rw [mem_filter, mem_filter]
      simp [Nat.ModEq, q]
    rw [heq]
    simpa only [S, q] using huni _ hj

theorem mod_neg_eq_iff_dvd_add {q : ℕ} (hq : 0 < q) (a b : ℕ) :
    a % q = (q - b % q) % q ↔ q ∣ a + b := by
  let r := a % q
  let s := b % q
  change r = (q - s) % q ↔ q ∣ a + b
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
  change r = (q - s) % q ↔ (r + s) % q = 0
  have hr := Nat.mod_lt a hq
  have hs := Nat.mod_lt b hq
  by_cases h0 : s = 0
  · simp [h0, r]
  · have hq's : q - s < q := by change s < q at hs; omega
    rw [Nat.mod_eq_of_lt hq's]
    constructor
    · intro hh
      have hsum : r + s = q := by change s < q at hs; omega
      rw [hsum, Nat.mod_self]
    · intro hh
      obtain ⟨k, hk⟩ := Nat.dvd_iff_mod_eq_zero.mpr hh
      have hk₀ : k ≠ 0 := by intro hz; simp [hz] at hk; omega
      have hk₂ : ¬ 2 ≤ k := by
        intro hj
        have hmul := Nat.mul_le_mul_left q hj
        change r < q at hr
        change s < q at hs
        omega
      have hk₁ : k = 1 := by omega
      have hsum : r + s = q := by simpa [hk₁] using hk
      omega

def forbiddenResidues (A : Finset ℕ) (p : ℕ) : Finset ℕ :=
  insert 0 (A.image fun b => (p * p - b % (p * p)) % (p * p))

theorem forbidden_card (A : Finset ℕ) (p : ℕ) :
    (forbiddenResidues A p).card ≤ A.card + 1 :=
  (card_insert_le _ _).trans (Nat.add_le_add_right card_image_le 1)

theorem mem_forbidden_lt {A : Finset ℕ} {p r : ℕ} (hp : p.Prime)
    (hr : r ∈ forbiddenResidues A p) : r < p * p := by
  rcases mem_insert.mp hr with rfl | hr
  · exact Nat.mul_pos hp.pos hp.pos
  · obtain ⟨a, ha, rfl⟩ := mem_image.mp hr
    exact Nat.mod_lt _ (Nat.mul_pos hp.pos hp.pos)

theorem forbidden_residue_iff {A : Finset ℕ} {a p : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2) :
    a % (p * p) ∈ forbiddenResidues A p ↔ ∃ b ∈ insert a A, p * p ∣ a + b := by
  have hq := Nat.mul_pos hp.pos hp.pos
  have hpo := hp.odd_of_ne_two hp₂
  have hcop : (p * p).Coprime 2 := (hpo.mul hpo).coprime_two_right
  constructor
  · intro h
    rcases mem_insert.mp h with h0 | him
    · refine ⟨a, mem_insert_self _ _, ?_⟩
      exact dvd_add (Nat.dvd_iff_mod_eq_zero.mpr h0) (Nat.dvd_iff_mod_eq_zero.mpr h0)
    · obtain ⟨b, hb, heq⟩ := mem_image.mp him
      exact ⟨b, mem_insert_of_mem hb, (mod_neg_eq_iff_dvd_add hq a b).mp heq.symm⟩
  · rintro ⟨b, hb, hd⟩
    rcases mem_insert.mp hb with he | hb
    · subst b
      have hh : p * p ∣ a := hcop.dvd_of_dvd_mul_left (by simpa [two_mul] using hd)
      exact mem_insert.mpr (Or.inl (Nat.dvd_iff_mod_eq_zero.mp hh))
    · exact mem_insert.mpr (Or.inr (mem_image.mpr
        ⟨b, hb, ((mod_neg_eq_iff_dvd_add hq a b).mpr hd).symm⟩))

theorem odd_prime_product (Q : Finset ℕ) (hprime : ∀ p ∈ Q, p.Prime ∧ p ≠ 2) :
    Odd (∏ p ∈ Q, p) := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    rw [prod_insert hp]
    exact ((hprime p (mem_insert_self _ _)).1.odd_of_ne_two
      (hprime p (mem_insert_self _ _)).2).mul (ih fun q hq => hprime q (mem_insert_of_mem hq))

theorem prime_intersections_count (S A Q : Finset ℕ) {E : ℝ}
    (hQ : ∀ p ∈ Q, p.Prime)
    (hU : ∀ r : ℕ, |((S.filter fun a => a ≡ r [MOD (∏ p ∈ Q, p) ^ 2]).card : ℝ) -
      (S.card : ℝ) / ((∏ p ∈ Q, p : ℕ) : ℝ) ^ 2| ≤ E) :
    ∀ T : Finset ℕ, (∀ a, a ∈ T ↔ a ∈ S ∧ ∀ p ∈ Q, a % (p * p) ∈ forbiddenResidues A p) →
      |(T.card : ℝ) - (S.card : ℝ) *
        ∏ p ∈ Q, ((forbiddenResidues A p).card : ℝ) / (p : ℝ) ^ 2| ≤
        E * ∏ p ∈ Q, ((forbiddenResidues A p).card : ℝ) := by
  let q (p : ℕ) := p * p
  have hq : ∀ p ∈ Q, q p ≠ 0 := fun p hp => Nat.mul_ne_zero (hQ p hp).ne_zero (hQ p hp).ne_zero
  have hp : Set.Pairwise (Q : Set ℕ) (fun i j => (q i).Coprime (q j)) := by
    intro i hi j hj hne
    simpa [q, pow_two] using ((Nat.coprime_primes (hQ i hi) (hQ j hj)).mpr hne).pow 2 2
  have hu' : ∀ r, |((S.filter fun a => a ≡ r [MOD ∏ p ∈ Q, q p]).card : ℝ) -
      (S.card : ℝ) / (∏ p ∈ Q, q p : ℕ)| ≤ E := by
    intro r
    have hh : (∏ p ∈ Q, q p) = (∏ p ∈ Q, p) ^ 2 := by simp [q, pow_two, prod_mul_distrib]
    rw [hh, Nat.cast_pow]
    exact hU r
  intro T hT
  have h := uniform_multiresidue S (forbiddenResidues A)
    (fun i hi r hr => mem_forbidden_lt (hQ i hi) hr) hq hp hu' T hT
  simpa [q, pow_two] using h

theorem mem_avoided_iff {α β : Type*} {P : Finset α} {S : Finset β}
    {B : α → β → Prop} {b : β} :
    b ∈ avoided P S B ↔ b ∈ S ∧ ∀ p ∈ P, ¬ B p b := by
  classical
  simp [avoided]

open Classical in
theorem avoid_union_bound {α β : Type*} [DecidableEq α]
    (P Q : Finset α) (S : Finset β) (B : α → β → Prop) :
    (avoided P S B).card ≤ (avoided (P ∪ Q) S B).card +
      ∑ q ∈ Q, (avoided P (S.filter (B q)) B).card := by
  let T := avoided P S B
  let G (b : β) := ∀ q ∈ Q, ¬ B q b
  have heq : T.filter G = avoided (P ∪ Q) S B := by
    ext b
    simp only [T, G, avoided, mem_filter, mem_union]
    constructor
    · rintro ⟨⟨hb, hP⟩, hQ⟩
      exact ⟨hb, fun p h => h.elim (hP p) (hQ p)⟩
    · rintro ⟨hb, h⟩
      exact ⟨⟨hb, fun p hp => h _ (Or.inl hp)⟩, fun q hq => h _ (Or.inr hq)⟩
  have hbad : T.filter (fun b => ¬ G b) ⊆ Q.biUnion (fun q => avoided P (S.filter (B q)) B) := by
    intro b hb
    obtain ⟨hT, hnot⟩ := mem_filter.mp hb
    simp only [G] at hnot
    push Not at hnot
    obtain ⟨q, hq, hp⟩ := hnot
    obtain ⟨hs, hguard⟩ := mem_filter.mp hT
    refine mem_biUnion.mpr ⟨q, hq, ?_⟩
    unfold avoided
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hs, hp⟩, hguard⟩
  have hcount := (card_le_card hbad).trans card_biUnion_le
  have hpart := card_filter_add_card_filter_not (s := T) G
  rw [heq] at hpart
  change T.card ≤ _
  omega

open Classical in
theorem combine_ideal_sieves {α β : Type*} [DecidableEq α] {k : ℕ} (hk : Odd k)
    (P Q : Finset α) (S : Finset β) (B : α → β → Prop) (w : α → ℝ)
    {E : ℝ} (hE : 0 ≤ E) (hw : ∀ p ∈ P ∪ Q, 0 ≤ w p)
    (hpoint : ∀ D ∈ P.powerset.filter (fun D => D.card ≤ k),
      ∀ K : Finset β, (∀ b, b ∈ K ↔ b ∈ S ∧ ∀ p ∈ D, B p b) →
        |(K.card : ℝ) - (S.card : ℝ) * ∏ p ∈ D, w p| ≤ E)
    (hpoint' : ∀ q ∈ Q, ∀ D ∈ P.powerset.filter (fun D => D.card ≤ k + 1),
      ∀ K : Finset β, (∀ b, b ∈ K ↔ b ∈ S ∧ B q b ∧ ∀ p ∈ D, B p b) →
        |(K.card : ℝ) - ((S.card : ℝ) * w q) * ∏ p ∈ D, w p| ≤ E) :
    let γ := ∏ p ∈ P, (1 - w p)
    let τ := exp (2 * ∑ p ∈ P, w p) / (2 : ℝ) ^ (k + 1)
    let L := (P.powerset.filter (fun D => D.card ≤ k + 1)).card
    (S.card : ℝ) * (γ - τ - (γ + τ) * ∑ q ∈ Q, w q) -
      ((Q.card : ℝ) + 1) * (E * L) ≤ (avoided (P ∪ Q) S B).card := by
  let γ := ∏ p ∈ P, (1 - w p)
  let τ := exp (2 * ∑ p ∈ P, w p) / (2 : ℝ) ^ (k + 1)
  let τ' := exp (2 * ∑ p ∈ P, w p) / (2 : ℝ) ^ (k + 1 + 1)
  let L := (P.powerset.filter (fun D => D.card ≤ k + 1)).card
  have hwP : ∀ p ∈ P, 0 ≤ w p := fun p hp => hw p (mem_union_left _ hp)
  have hL : ((P.powerset.filter (fun D => D.card ≤ k)).card : ℝ) ≤ (L : ℝ) := by
    have hsub : P.powerset.filter (fun D => D.card ≤ k) ⊆
        P.powerset.filter (fun D => D.card ≤ k + 1) := by
      intro D hD
      obtain ⟨hp, hc⟩ := mem_filter.mp hD
      exact mem_filter.mpr ⟨hp, Nat.le_succ_of_le hc⟩
    exact_mod_cast (show (P.powerset.filter (fun D => D.card ≤ k)).card ≤ L from card_le_card hsub)
  have hlow : (S.card : ℝ) * (γ - τ) - E * L ≤ (avoided P S B).card := by
    have h := ideal_sieve_lower hk P S B w (mass := (S.card : ℝ)) (by positivity) hwP hpoint
    exact (sub_le_sub_left (mul_le_mul_of_nonneg_left hL hE) _).trans h
  have hk' : Even (k + 1) := hk.add_odd odd_one
  have hτ : τ' ≤ τ := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hup (q : α) (hq : q ∈ Q) :
      ((avoided P (S.filter (B q)) B).card : ℝ) ≤
        (S.card : ℝ) * w q * (γ + τ) + E * L := by
    have hwq := hw q (mem_union_right _ hq)
    have hm : 0 ≤ (S.card : ℝ) * w q := mul_nonneg (by positivity) hwq
    have h := ideal_sieve_upper hk' P (S.filter (B q)) B w hm hwP
      (fun D hD K hK => hpoint' q hq D hD K (fun b => by rw [hK, mem_filter, and_assoc]))
    exact h.trans (add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hτ) hm) le_rfl)
  have hsum : (∑ q ∈ Q, ((avoided P (S.filter (B q)) B).card : ℝ)) ≤
      (S.card : ℝ) * (γ + τ) * ∑ q ∈ Q, w q + (Q.card : ℝ) * (E * L) := by
    calc
      _ ≤ ∑ q ∈ Q, ((S.card : ℝ) * w q * (γ + τ) + E * L) := sum_le_sum hup
      _ = _ := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul]
        congr 1
        rw [mul_sum]
        exact sum_congr rfl fun q _ => by ring
  have hcard : ((avoided P S B).card : ℝ) ≤ (avoided (P ∪ Q) S B).card +
      ∑ q ∈ Q, ((avoided P (S.filter (B q)) B).card : ℝ) := by
    exact_mod_cast avoid_union_bound P Q S B
  linarith

noncomputable def forbiddenWeight (A : Finset ℕ) (p : ℕ) : ℝ :=
  ((forbiddenResidues A p).card : ℝ) / (p : ℝ) ^ 2

/-- The lower truncation counts survivors and the upper truncation controls additional primes. -/
theorem medium_prime_sieve (S A P Q : Finset ℕ) {y D z H k K : ℕ} {E : ℝ}
    (hy : 2 ≤ y) (hz : 1 ≤ z) (hH : 1 ≤ H) (hk : Odd k) (hK : A.card < K)
    (hPQ : Disjoint P Q)
    (hP : ∀ p ∈ P, p.Prime ∧ y < p ∧ p ≤ z)
    (hQ : ∀ p ∈ Q, p.Prime ∧ y < p ∧ p ≤ H)
    (hLevel : z ^ (k + 1) * H ≤ D) (hE : 0 ≤ E)
    (hunif : ∀ d ≤ D, Odd d → (∀ p ∈ (Nat.primesLE y).erase 2, d.Coprime p) → ∀ r : ℕ,
      |((S.filter fun a => a ≡ r [MOD d * d]).card : ℝ) - (S.card : ℝ) / (d : ℝ) ^ 2| ≤ E) :
    let w := forbiddenWeight A
    let γ := ∏ p ∈ P, (1 - w p)
    let τ := exp (2 * ∑ p ∈ P, w p) / (2 : ℝ) ^ (k + 1)
    let L := (P.powerset.filter (fun T => T.card ≤ k + 1)).card
    (S.card : ℝ) * (γ - τ - (γ + τ) * ∑ q ∈ Q, w q) -
      ((Q.card : ℝ) + 1) * (E * (K : ℝ) ^ (k + 2) * L) ≤
      (avoided (P ∪ Q) S (fun p a => a % (p * p) ∈ forbiddenResidues A p)).card := by
  classical
  let w := forbiddenWeight A
  let B (p a : ℕ) := a % (p * p) ∈ forbiddenResidues A p
  let ε := E * (K : ℝ) ^ (k + 2)
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hPQ' (p : ℕ) (hp : p ∈ P ∪ Q) : p.Prime ∧ y < p := by
    rcases mem_union.mp hp with hp | hp
    · exact ⟨(hP p hp).1, (hP p hp).2.1⟩
    · exact ⟨(hQ p hp).1, (hQ p hp).2.1⟩
  have hinter (T : Finset ℕ) (hT : T ⊆ P ∪ Q) (hcard : T.card ≤ k + 2)
      (hprod : ∏ p ∈ T, p ≤ D) (V : Finset ℕ)
      (hV : ∀ a, a ∈ V ↔ a ∈ S ∧ ∀ p ∈ T, B p a) :
      |(V.card : ℝ) - (S.card : ℝ) * ∏ p ∈ T, w p| ≤ ε := by
    let d := ∏ p ∈ T, p
    have hd : Odd d := odd_prime_product T fun p hp =>
      ⟨(hPQ' p (hT hp)).1, by have hh := (hPQ' p (hT hp)).2; omega⟩
    have hcop : ∀ p ∈ (Nat.primesLE y).erase 2, d.Coprime p := by
      intro p hp
      obtain ⟨hpy, hpp⟩ := Nat.mem_primesLE.mp (mem_erase.mp hp).2
      apply Nat.Coprime.prod_left
      intro q hq
      obtain ⟨hqp, hqy⟩ := hPQ' q (hT hq)
      exact (Nat.coprime_primes hqp hpp).mpr (by omega)
    have hcount := prime_intersections_count S A T (fun p hp => (hPQ' p (hT hp)).1)
      (fun r => by simpa [d, pow_two] using hunif d hprod hd hcop r) V hV
    refine hcount.trans (mul_le_mul_of_nonneg_left ?_ hE)
    have hcard' (p : ℕ) (hp : p ∈ T) : ((forbiddenResidues A p).card : ℝ) ≤ K := by
      exact_mod_cast (forbidden_card A p).trans (show A.card + 1 ≤ K by omega)
    have hpow := prod_le_prod (fun p hp => by positivity : ∀ p ∈ T,
      (0 : ℝ) ≤ (forbiddenResidues A p).card) hcard'
    rw [prod_const] at hpow
    exact hpow.trans (pow_le_pow_right₀ hK1 hcard)
  have hsubprod (T : Finset ℕ) (hT : T ⊆ P) (hcard : T.card ≤ k + 1) :
      ∏ p ∈ T, p ≤ z ^ (k + 1) := by
    exact (prod_le_pow_card T id z (fun p hp => (hP p (hT hp)).2.2)).trans
      (Nat.pow_le_pow_right (by omega) hcard)
  refine combine_ideal_sieves hk P Q S B w (E := ε) (by positivity) (fun p _ => by
    unfold w forbiddenWeight
    positivity) ?_ ?_
  · intro T hT V hV
    obtain ⟨hT', hTc⟩ := mem_filter.mp hT
    replace hT' := mem_powerset.mp hT'
    have hprod : ∏ p ∈ T, p ≤ D :=
      (hsubprod T hT' (by omega)).trans ((Nat.le_mul_of_pos_right _ (by omega)).trans hLevel)
    exact hinter T (hT'.trans (subset_union_left)) (by omega) hprod V hV
  · intro q hq T hT V hV
    obtain ⟨hT', hTc⟩ := mem_filter.mp hT
    replace hT' := mem_powerset.mp hT'
    have hqT : q ∉ T := fun h => (disjoint_left.mp hPQ) (hT' h) hq
    have hins : insert q T ⊆ P ∪ Q :=
      insert_subset (mem_union_right _ hq) (hT'.trans subset_union_left)
    have hprod : ∏ p ∈ insert q T, p ≤ D := by
      rw [prod_insert hqT, mul_comm]
      exact (Nat.mul_le_mul (hsubprod T hT' hTc) (hQ q hq).2.2).trans hLevel
    have hc : (insert q T).card ≤ k + 2 := by
      rw [card_insert_of_notMem hqT]
      omega
    have h := hinter (insert q T) hins hc hprod V (fun a => by
      simp only [hV, mem_insert, forall_eq_or_imp])
    rw [prod_insert hqT, ← mul_assoc] at h
    exact h

theorem discard_forbidden {N : ℕ} (S A R : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hR : ∀ p ∈ R, p.Prime ∧ p ≠ 2) :
    S.card ≤ (avoided R S (fun p a => a % (p * p) ∈ forbiddenResidues A p)).card +
      (A.card + 1) * ∑ p ∈ R, (N / (p * p) + 1) := by
  have hs := large_prime_discard S (insert 0 A) R hS
  have hfilter : (S.filter fun a => ∀ b ∈ insert 0 A, ∀ p ∈ R, ¬ p * p ∣ a + b) =
      avoided R S (fun p a => a % (p * p) ∈ forbiddenResidues A p) := by
    ext a
    rw [mem_filter, mem_avoided_iff]
    apply and_congr_right
    intro ha
    constructor
    · intro h p hp hmem
      rcases mem_insert.mp hmem with hzero | hm
      · have hdiv : p * p ∣ a := Nat.dvd_iff_mod_eq_zero.mpr hzero
        exact h 0 (mem_insert_self _ _) p hp (by simpa using hdiv)
      · obtain ⟨b, hb, heq⟩ := mem_image.mp hm
        exact h b (mem_insert_of_mem hb) p hp
          ((mod_neg_eq_iff_dvd_add (Nat.mul_pos (hR p hp).1.pos (hR p hp).1.pos) a b).mp heq.symm)
    · intro h b hb p hp hd
      apply h p hp
      rcases mem_insert.mp hb with hb | hb
      · subst b
        exact mem_insert.mpr (Or.inl (Nat.dvd_iff_mod_eq_zero.mp (by simpa using hd)))
      · exact mem_insert.mpr (Or.inr (mem_image.mpr
          ⟨b, hb, ((mod_neg_eq_iff_dvd_add (Nat.mul_pos (hR p hp).1.pos (hR p hp).1.pos) a b).mpr hd).symm⟩))
  rw [hfilter] at hs
  exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (card_insert_le _ _)) _)

/-- Large prime squares are bounded by direct counting after the medium-prime sieve. -/
theorem room_of_medium_and_tail {N y K : ℕ} (S A P Q R : Finset ℕ)
    (hS : S ⊆ Icc 1 N) (hA : A.card < K)
    (hy : 2 ≤ y)
    (hallP : P ∪ Q ∪ R = (Nat.primesLE (Nat.sqrt N)).filter (y < ·)) {err γ τ u : ℝ}
    (hγ : 0 ≤ γ) (hτ : τ ≤ γ / 4) (hu : 0 ≤ u ∧ u ≤ 1 / 4)
    (hmed : (S.card : ℝ) * (γ - τ - (γ + τ) * u) - err ≤
      (avoided (P ∪ Q) S (fun p a => a % (p * p) ∈ forbiddenResidues A p)).card)
    (hbudget : (K : ℝ) + err + (K : ℝ) * (∑ p ∈ R, (N / (p * p) + 1) : ℕ) <
      (S.card : ℝ) * (γ / 3)) :
    A.card < (S.filter fun a => ∀ b ∈ insert a A,
      ∀ p ∈ (Nat.primesLE (Nat.sqrt N)).filter (y < ·), ¬ p * p ∣ a + b).card := by
  let B (p a : ℕ) := a % (p * p) ∈ forbiddenResidues A p
  let T := avoided (P ∪ Q) S B
  let F := avoided R T B
  have hprime (p : ℕ) (hp : p ∈ P ∪ Q ∪ R) : p.Prime ∧ p ≠ 2 := by
    rw [hallP] at hp
    have hh := (mem_filter.mp hp).2
    exact ⟨(Nat.mem_primesLE.mp (mem_filter.mp hp).1).2, by omega⟩
  have hfin : F = S.filter (fun a => ∀ b ∈ insert a A,
      ∀ p ∈ (Nat.primesLE (Nat.sqrt N)).filter (y < ·), ¬ p * p ∣ a + b) := by
    ext a
    simp only [F, T, avoided, mem_filter]
    constructor
    · rintro ⟨⟨ha, h₁⟩, h₂⟩
      refine ⟨ha, ?_⟩
      intro b hb p hp hd
      have hp' : p ∈ P ∪ Q ∪ R := hallP.symm ▸ mem_filter.mpr hp
      obtain ⟨hprime', h₂'⟩ := hprime p hp'
      have hm := (forbidden_residue_iff hprime' h₂').mpr ⟨b, hb, hd⟩
      exact (mem_union.mp hp').elim (fun hp => h₁ p hp hm) (fun hp => h₂ p hp hm)
    · rintro ⟨ha, h⟩
      have hsafe (p : ℕ) (hp : p ∈ P ∪ Q ∪ R) : ¬ B p a := by
        intro hb
        obtain ⟨hb', hb₂⟩ := hprime p hp
        obtain ⟨b, hba, hd⟩ := (forbidden_residue_iff hb' hb₂).mp hb
        exact h b hba p (mem_filter.mp (show p ∈ (Nat.primesLE (Nat.sqrt N)).filter
          (y < ·) from hallP ▸ hp)) hd
      exact ⟨⟨ha, fun p hp => hsafe p (mem_union_left _ hp)⟩,
        fun p hp => hsafe p (mem_union_right _ hp)⟩
  have htail := discard_forbidden T A R (fun a ha => hS (mem_avoided_iff.mp ha).1)
    (fun p hp => hprime p (mem_union_right _ hp))
  have htail' : (T.card : ℝ) ≤ (F.card : ℝ) +
      (K : ℝ) * (∑ p ∈ R, (N / (p * p) + 1) : ℕ) := by
    exact_mod_cast (htail.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _
      (show A.card + 1 ≤ K by omega)) _))
  have hu' : (γ + τ) * u ≤ (γ + γ / 4) * (1 / 4) :=
    (mul_le_mul_of_nonneg_right (add_le_add le_rfl hτ) hu.1).trans
      (mul_le_mul_of_nonneg_left hu.2 (by linarith : 0 ≤ γ + γ / 4))
  have hmain : γ / 3 ≤ γ - τ - (γ + τ) * u := by linarith
  have hlow : (S.card : ℝ) * (γ / 3) - err ≤ (T.card : ℝ) :=
    (sub_le_sub_right (mul_le_mul_of_nonneg_left hmain (by positivity)) _).trans hmed
  have hcount : (K : ℝ) < (F.card : ℝ) := by linarith
  rw [← hfin]
  exact hA.trans_le (le_of_lt (by exact_mod_cast hcount))

theorem tail_of_inv_sq (H M : ℕ) (hH : 0 < H) :
    ∑ p ∈ Icc (H + 1) M, (1 / (p : ℝ) ^ 2) ≤ 1 / (H : ℝ) := by
  by_cases hM : H ≤ M
  · suffices hh : ∑ p ∈ Icc (H + 1) M, (1 / (p : ℝ) ^ 2) ≤
      1 / (H : ℝ) - 1 / (M : ℝ) from hh.trans (sub_le_self _ (by positivity))
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [sum_Icc_succ_top (by omega : H + 1 ≤ m + 1)]
      have h := inv_sq_le_sub (m + 1) (by omega)
      push_cast at h ⊢
      rw [show ((m : ℝ) + 1) - 1 = m by ring] at h
      linarith
  · rw [Icc_eq_empty_of_lt (by omega : M < H + 1), sum_empty]
    positivity

theorem large_tail_cost (N H : ℕ) (hH : 0 < H) (R : Finset ℕ)
    (hR : R ⊆ Icc (H + 1) (Nat.sqrt N)) :
    ((∑ p ∈ R, (N / (p * p) + 1)) : ℕ) ≤
      (N : ℝ) / (H : ℝ) + (Nat.sqrt N : ℝ) := by
  have hRs : R.card ≤ Nat.sqrt N := by
    have hsub : R ⊆ Icc 1 (Nat.sqrt N) := by
      intro p hp
      obtain ⟨h₁, h₂⟩ := mem_Icc.mp (hR hp)
      exact mem_Icc.mpr ⟨by omega, h₂⟩
    simpa [Nat.card_Icc] using card_le_card hsub
  have hsum : ∑ p ∈ R, (1 / (p : ℝ) ^ 2) ≤ 1 / (H : ℝ) :=
    (sum_le_sum_of_subset_of_nonneg hR fun p _ _ => by positivity).trans
      (tail_of_inv_sq H _ hH)
  push_cast
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
  have hcount : ∑ p ∈ R, ((N / (p * p) : ℕ) : ℝ) ≤ (N : ℝ) / H := by
    calc
      _ ≤ ∑ p ∈ R, (N : ℝ) * (1 / (p : ℝ) ^ 2) := sum_le_sum (by
        intro p hp
        have hp0 : 0 < p := by have h := (mem_Icc.mp (hR hp)).1; omega
        rw [mul_one_div]
        apply (le_div_iff₀ (by positivity)).mpr
        exact_mod_cast (show N / (p * p) * p ^ 2 ≤ N by
          simpa [pow_two] using Nat.div_mul_le_self N (p * p)))
      _ ≤ _ := by
        rw [← mul_sum]
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hsum (show 0 ≤ (N : ℝ) by positivity)
  exact add_le_add hcount (by exact_mod_cast hRs)

noncomputable def presieveFraction (y : ℕ) : ℝ :=
  ((2 : ℝ) ^ ((Nat.primesLE y).erase 2).card)⁻¹

noncomputable def presieveError (y : ℕ) (E : ℝ) : ℝ :=
  E + (2 * (2 : ℝ) ^ ((Nat.primesLE y).erase 2).card + 1) * presieveFraction y

structure SieveParameters (N : ℕ) where
  y : ℕ
  z : ℕ
  H : ℕ
  D : ℕ
  k : ℕ
  K : ℕ
  E : ℝ
  lambdaBound : ℝ
  m : ℝ
  hy : 3 ≤ y
  hyz : y ≤ z
  hzH : z ≤ H
  hHN : H ≤ Nat.sqrt N
  hD : 0 < D
  hk : Odd k
  hLevel : z ^ (k + 1) * H ≤ D
  hE : 0 ≤ E
  hvar : let t := ((Nat.primesLE y).erase 2).card
    (((D + 1 : ℕ) : ℝ) * (D : ℝ) ^ 2) *
        (presieveFraction y ^ 2 * N * (2 * (2 : ℝ) ^ t * 3 ^ t)) ≤ E ^ 2
  hmass : 0 ≤ m ∧ m ≤ (N : ℝ) / 4 * exp (-1) * presieveFraction y - presieveError y E
  hlocal : 2 * K ≤ y ^ 2
  hlam : (K : ℝ) * primeTail y z ≤ lambdaBound
  htrunc : exp (4 * lambdaBound) / (2 : ℝ) ^ (k + 1) ≤ 1 / 4
  hband : (K : ℝ) * primeTail z H ≤ 1 / 4
  hbudget : (K : ℝ) +
      ((H : ℝ) + 1) * ((2 * presieveError y E) * (K : ℝ) ^ (k + 2) *
        (((k + 2 : ℕ) : ℝ) * ((z + 1 : ℕ) : ℝ) ^ (k + 1))) +
      (K : ℝ) * ((N : ℝ) / H + (Nat.sqrt N : ℝ)) < m * (exp (-2 * lambdaBound) / 3)

set_option maxHeartbeats 1500000 in
theorem finite_certificate_bound (N : ℕ) (params : SieveParameters N) :
    params.K ≤ Erdos1109.f N := by
  classical
  let y := params.y
  let z := params.z
  let H := params.H
  let D := params.D
  let k := params.k
  let K := params.K
  let E := params.E
  let lambdaBound := params.lambdaBound
  let δ := 2 * presieveError y E
  let P := (Nat.primesLE z).filter (y < ·)
  let Q := (Nat.primesLE H).filter (z < ·)
  let R := (Nat.primesLE (Nat.sqrt N)).filter (H < ·)
  have hy₂ : 2 ≤ y := by have := params.hy; omega
  have hz₁ : 1 ≤ z := (by omega : 1 ≤ y).trans params.hyz
  have hH₁ : 1 ≤ H := hz₁.trans params.hzH
  have hH₀ : 0 < H := hH₁
  obtain ⟨S, hS, hodd, hsmall, hmass, huni⟩ :=
    pool_fixed_level N y D params.hy params.hD params.hE params.hvar
  have hms : params.m ≤ (S.card : ℝ) := params.hmass.2.trans hmass
  have hdirP : ∀ p ∈ P, p.Prime ∧ y < p ∧ p ≤ z := by
    intro p hp
    obtain ⟨hp', hpy⟩ := mem_filter.mp hp
    obtain ⟨hpz, hprime⟩ := Nat.mem_primesLE.mp hp'
    exact ⟨hprime, hpy, hpz⟩
  have hdirQ : ∀ p ∈ Q, p.Prime ∧ y < p ∧ p ≤ H := by
    intro p hp
    obtain ⟨hp', hpz⟩ := mem_filter.mp hp
    obtain ⟨hpH, hprime⟩ := Nat.mem_primesLE.mp hp'
    exact ⟨hprime, params.hyz.trans_lt hpz, hpH⟩
  have hPQ : Disjoint P Q := by
    apply disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_ge (hdirP p hp).2.2) (mem_filter.mp hq).2
  have hall : P ∪ Q ∪ R = (Nat.primesLE (Nat.sqrt N)).filter (y < ·) := by
    ext p
    simp only [P, Q, R, mem_union, mem_filter, Nat.mem_primesLE]
    have h₁ := params.hyz
    have h₂ := params.hzH
    have h₃ := params.hHN
    by_cases hp : p.Prime
    · simp only [hp, and_true]
      omega
    · simp [hp]
  have hR : R ⊆ Icc (H + 1) (Nat.sqrt N) := by
    intro p hp
    have h₁ := (mem_filter.mp hp).2
    have h₂ := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).1
    exact mem_Icc.mpr ⟨by omega, h₂⟩
  have hsizeQ : (Q.card : ℝ) ≤ H := by
    have hQ' : Q ⊆ Icc 1 H := fun p hp =>
      mem_Icc.mpr ⟨(hdirQ p hp).1.one_lt.le, (hdirQ p hp).2.2⟩
    exact_mod_cast (show Q.card ≤ H by simpa [Nat.card_Icc] using card_le_card hQ')
  have hsizeP : P.card ≤ z := by
    have hP' : P ⊆ Icc 1 z := fun p hp =>
      mem_Icc.mpr ⟨(hdirP p hp).1.one_lt.le, (hdirP p hp).2.2⟩
    simpa [Nat.card_Icc] using card_le_card hP'
  refine greedy_bound hy₂ S hS hodd hsmall ?_
  intro A hAS hAK
  let w := forbiddenWeight A
  let γ := ∏ p ∈ P, (1 - w p)
  let μ := ∑ p ∈ P, w p
  let τ := exp (2 * μ) / (2 : ℝ) ^ (k + 1)
  let u := ∑ q ∈ Q, w q
  let L := (P.powerset.filter (fun T => T.card ≤ k + 1)).card
  let err := ((Q.card : ℝ) + 1) * (δ * (K : ℝ) ^ (k + 2) * L)
  have hδ : 0 ≤ δ := by
    have hEN : 0 ≤ E := params.hE
    dsimp [δ, presieveError, presieveFraction]
    positivity
  have hw (p : ℕ) : 0 ≤ w p ∧ w p ≤ (K : ℝ) * (1 / (p : ℝ) ^ 2) := by
    have hcard : ((forbiddenResidues A p).card : ℝ) ≤ K := by
      exact_mod_cast (forbidden_card A p).trans (show A.card + 1 ≤ K by omega)
    exact ⟨by dsimp [w, forbiddenWeight]; positivity, by
      dsimp [w, forbiddenWeight]
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right hcard (sq_nonneg _)⟩
  have hwHalf (p : ℕ) (hp : p ∈ P) : w p ≤ 1 / 2 := by
    have hpy : y ≤ p := (hdirP p hp).2.1.le
    have hlocal : (2 : ℝ) * K ≤ (p : ℝ) ^ 2 := by
      have hnat : 2 * K ≤ p ^ 2 := params.hlocal.trans (Nat.pow_le_pow_left hpy 2)
      exact_mod_cast hnat
    refine (hw p).2.trans ?_
    rw [mul_one_div]
    apply (div_le_iff₀ (by have hp := (hdirP p hp).1.pos; positivity)).mpr
    linarith
  have hμ : μ ≤ lambdaBound := by
    calc
      μ ≤ ∑ p ∈ P, (K : ℝ) * (1 / (p : ℝ) ^ 2) := sum_le_sum fun p _ => (hw p).2
      _ = (K : ℝ) * primeTail y z := by rw [← mul_sum]; rfl
      _ ≤ lambdaBound := params.hlam
  have hu₀ : 0 ≤ u := sum_nonneg fun p _ => (hw p).1
  have hu : u ≤ 1 / 4 := by
    calc
      u ≤ ∑ p ∈ Q, (K : ℝ) * (1 / (p : ℝ) ^ 2) := sum_le_sum fun p _ => (hw p).2
      _ = (K : ℝ) * primeTail z H := by rw [← mul_sum]; rfl
      _ ≤ 1 / 4 := params.hband
  have hγ : exp (-2 * lambdaBound) ≤ γ :=
    (exp_le_exp.mpr (by linarith)).trans (ideal_product_lower P w fun p hp => ⟨(hw p).1, hwHalf p hp⟩)
  have hτ : τ ≤ γ / 4 := by
    have htrunc := (div_le_div_of_nonneg_right (exp_le_exp.mpr (by linarith : 4 * μ ≤ 4 * lambdaBound))
      (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (k + 1))).trans params.htrunc
    have h := mul_le_mul_of_nonneg_right htrunc (exp_pos (-2 * μ)).le
    have heq : exp (4 * μ) * exp (-2 * μ) = exp (2 * μ) := by
      rw [← exp_add]; congr 1; ring
    rw [div_mul_eq_mul_div, heq] at h
    have hh := ideal_product_lower P w fun p hp => ⟨(hw p).1, hwHalf p hp⟩
    exact (show τ ≤ exp (-2 * μ) / 4 by
      simpa [τ, div_eq_mul_inv, mul_comm] using h).trans
      (div_le_div_of_nonneg_right hh (by norm_num))
  have hmed := medium_prime_sieve S A P Q hy₂ hz₁ hH₁ params.hk hAK hPQ hdirP hdirQ params.hLevel hδ huni
  have hL : (L : ℝ) ≤ (((k + 2 : ℕ) : ℝ) * ((z + 1 : ℕ) : ℝ) ^ (k + 1)) := by
    exact_mod_cast (show L ≤ (k + 2) * (z + 1) ^ (k + 1) from
      (trunc_count_bound P (k + 1)).trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (Nat.succ_le_succ hsizeP) _)))
  have herr : err ≤ ((H : ℝ) + 1) * (δ * (K : ℝ) ^ (k + 2) *
      (((k + 2 : ℕ) : ℝ) * ((z + 1 : ℕ) : ℝ) ^ (k + 1))) := by
    dsimp [err]
    gcongr
  have hcost := large_tail_cost N H hH₀ R hR
  have hbudget : (K : ℝ) + err + (K : ℝ) * (∑ p ∈ R, (N / (p * p) + 1) : ℕ) <
      (S.card : ℝ) * (γ / 3) := by
    have hK₀ : 0 ≤ (K : ℝ) := by positivity
    have hS₀ : 0 ≤ (S.card : ℝ) := by positivity
    have hthird : 0 ≤ exp (-2 * lambdaBound) / 3 := by positivity
    have hbound := (add_le_add (add_le_add le_rfl herr)
      (mul_le_mul_of_nonneg_left hcost hK₀)).trans_lt params.hbudget
    exact hbound.trans_le (mul_le_mul hms (div_le_div_of_nonneg_right hγ (by norm_num)) hthird hS₀)
  exact room_of_medium_and_tail S A P Q R hS hAK hy₂ hall ((exp_pos _).le.trans hγ) hτ ⟨hu₀, hu⟩ hmed hbudget

theorem floor_half {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one x
  linarith

theorem pow_le_exp_product {x a : ℝ} (hx : 0 ≤ x) (ha : x ≤ exp a) (k : ℕ) :
    x ^ k ≤ exp (k * a) := by
  rw [exp_nat_mul]
  exact pow_le_pow_left₀ hx ha k

theorem exp_mul_bound {a b x y : ℝ} (hx : 0 ≤ x) (ha : x ≤ exp a) (hb : y ≤ exp b) :
    x * y ≤ exp (a + b) := by
  rw [exp_add]
  by_cases hy : 0 ≤ y
  · exact mul_le_mul ha hb hy (exp_pos _).le
  · exact (mul_nonpos_of_nonneg_of_nonpos hx (le_of_not_ge hy)).trans (by positivity)

set_option maxHeartbeats 3000000 in
/-- The cutoffs make the variance, truncation and counting errors smaller than the main term. -/
theorem numeric_parameters (N Y₀ : ℕ) (hN : 0 < N) (hY₀ : 3 ≤ Y₀)
    {C c b : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hc₁ : c ≤ 1)
    (hb : 0 < b) (hb₁ : b ≤ 1)
    (hsmallC : 2 * C * c * log 6 ≤ 1 / 1000)
    (hsmallB : 16 * C * b / c ≤ log 2 / 100000)
    (hπ : ∀ n : ℕ, Y₀ ≤ n → (Nat.primeCounting n : ℝ) ≤ C * n / log n)
    (hgr : let L := log (N : ℝ)
      let l := log L
      4 ≤ L ∧ 10 ≤ l ∧ 20000 ≤ L / l ∧ (Y₀ : ℝ) ≤ c * L * l / 2 ∧
        -2 * log (c / 2) ≤ l ∧ 8 * b / c ^ 2 ≤ l ∧
        32 * exp 1 * L ^ 8 ≤ exp (L / 1000) ∧ 256 * C * b ≤ L) :
    ∃ params : SieveParameters N, params.K = ⌊b * logScale N⌋₊ := by
  let L := log (N : ℝ)
  let l := log L
  let Y : ℕ := ⌊c * L * l⌋₊
  let Z : ℕ := ⌊L⌋₊ ^ 4
  let H : ℕ := ⌊exp (L / 16)⌋₊
  let D : ℕ := ⌊exp (L / 12)⌋₊
  let k : ℕ := 2 * ⌊L / (2500 * l)⌋₊ + 1
  let K : ℕ := ⌊b * logScale N⌋₊
  let E := exp (3 * L / 4)
  let lambdaBound := log 2 * (L / l) / 100000
  let m := exp (99 * L / 100)
  change 4 ≤ L ∧ 10 ≤ l ∧ 20000 ≤ L / l ∧ (Y₀ : ℝ) ≤ c * L * l / 2 ∧
    -2 * log (c / 2) ≤ l ∧ 8 * b / c ^ 2 ≤ l ∧
    32 * exp 1 * L ^ 8 ≤ exp (L / 1000) ∧ 256 * C * b ≤ L at hgr
  obtain ⟨hL, hl, hratio, hY₀', hlogc, hlocal, henvelope, hband⟩ := hgr
  have hL₀ : 0 < L := by linarith
  have hl₀ : 0 < l := by linarith
  have hlL : l ≤ L := (log_le_sub_one_of_pos hL₀).trans (by linarith)
  have hNreal : (N : ℝ) = exp L := (exp_log (by exact_mod_cast hN)).symm
  have hLexp : L = exp l := (exp_log hL₀).symm
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hlog2₁ : log 2 ≤ 1 := by have h := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); norm_num at h; exact h
  have hExp1 : 1 ≤ exp 1 := one_le_exp (by norm_num)
  have hbig : 32 * exp 1 ≤ exp (L / 1000) :=
    (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (show 1 ≤ L by linarith))).trans henvelope
  have hs (j : ℕ) (hj : j ≤ 8) : L ^ j ≤ exp (L / 1000) := by
    calc
      L ^ j ≤ L ^ 8 := pow_le_pow_right₀ (by linarith) hj
      _ ≤ 32 * exp 1 * L ^ 8 := le_mul_of_one_le_left (by positivity) (by linarith)
      _ ≤ _ := henvelope
  have hconst (a : ℝ) (ha : a ≤ 32 * exp 1) : a ≤ exp (L / 1000) := ha.trans hbig
  have hYlo : c * L * l / 2 ≤ (Y : ℝ) := floor_half (by
    have h := (show (3 : ℝ) ≤ Y₀ by exact_mod_cast hY₀).trans hY₀'
    linarith)
  have hYhi : (Y : ℝ) ≤ c * L * l := Nat.floor_le (by positivity)
  have hYY : Y₀ ≤ Y := by exact_mod_cast hY₀'.trans hYlo
  have hY₃ : 3 ≤ Y := hY₀.trans hYY
  have hYR : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hlogY : l / 2 ≤ log (Y : ℝ) := by
    have hh : c / 2 * L ≤ (Y : ℝ) :=
      (show c / 2 * L ≤ c * L * l / 2 by
        nlinarith only [mul_nonneg (show 0 ≤ c * L by positivity) (show 0 ≤ l - 1 by linarith)]).trans hYlo
    have h := log_le_log (show 0 < c / 2 * L by positivity) hh
    rw [log_mul (by positivity) hL₀.ne'] at h
    change log (c / 2) + l ≤ _ at h
    linarith
  have hZlo : L ^ 4 / 16 ≤ (Z : ℝ) := by
    have hh := pow_le_pow_left₀ (show 0 ≤ L / 2 by positivity) (floor_half (show 2 ≤ L by linarith)) 4
    norm_num [Z, div_pow] at hh ⊢
    exact hh
  have hZhi : (Z : ℝ) ≤ L ^ 4 := by
    exact_mod_cast pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) ⌊L⌋₊)
      (Nat.floor_le hL₀.le) 4
  have hYZ : Y ≤ Z := by
    have hYlog : (Y : ℝ) ≤ L ^ 2 := hYhi.trans (by
      calc
        c * L * l ≤ 1 * L * l := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc₁ hL₀.le) hl₀.le
        _ ≤ _ := by rw [one_mul, pow_two]; exact mul_le_mul_of_nonneg_left hlL hL₀.le)
    have hsq : 16 ≤ L ^ 2 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hL 2
      norm_num at hh
      exact hh
    have hp : L ^ 2 ≤ L ^ 4 / 16 := by
      apply (le_div_iff₀ (by norm_num)).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hsq (sq_nonneg L)]
    exact_mod_cast hYlog.trans (hp.trans hZlo)
  have hZH : Z ≤ H := by
    apply Nat.le_floor
    exact hZhi.trans ((hs 4 (by norm_num)).trans (exp_le_exp.mpr (by linarith)))
  have hHhi : (H : ℝ) ≤ exp (L / 16) := Nat.floor_le (by positivity)
  have hHexp : 2 ≤ exp (L / 16) := (hconst 2 (by linarith)).trans (exp_le_exp.mpr (by linarith))
  have hHlo : exp (L / 16) / 2 ≤ (H : ℝ) := floor_half hHexp
  have hDhi : (D : ℝ) ≤ exp (L / 12) := Nat.floor_le (by positivity)
  have hDpos : 0 < D := Nat.le_floor (n := 1) (by
    exact_mod_cast (one_le_exp (show 0 ≤ L / 12 by positivity)))
  have hHN : H ≤ Nat.sqrt N := by
    apply Nat.le_sqrt.mpr
    have h : (H : ℝ) ^ 2 ≤ (N : ℝ) := by
      rw [hNreal]
      exact (pow_le_exp_product (by positivity) hHhi 2).trans (exp_le_exp.mpr (by push_cast; linarith))
    exact_mod_cast (by simpa [pow_two] using h : ((H * H : ℕ) : ℝ) ≤ (N : ℝ))
  have hkOdd : Odd k := ⟨⌊L / (2500 * l)⌋₊, rfl⟩
  have hkhi : (k : ℝ) + 2 ≤ L / (1000 * l) := by
    have hf := Nat.floor_le (show 0 ≤ L / (2500 * l) by positivity)
    have hratio' : (20000 : ℝ) ≤ L / l := hratio
    dsimp [k]
    push_cast
    rw [show L / (2500 * l) = (L / l) / 2500 by ring] at hf ⊢
    rw [show L / (1000 * l) = (L / l) / 1000 by ring]
    linarith
  have hklow : 2 * (L / (2500 * l)) ≤ (k : ℝ) + 1 := by
    have hf := Nat.lt_floor_add_one (L / (2500 * l))
    dsimp [k]
    push_cast
    linarith
  have hkl : ((k : ℝ) + 2) * l ≤ L / 1000 := by
    have h := (le_div_iff₀ (by positivity : 0 < 1000 * l)).mp hkhi
    nlinarith only [h]
  have hkL : (k : ℝ) + 2 ≤ L := by
    have hk := mul_le_mul_of_nonneg_left (show 1 ≤ l by linarith)
      (show (0 : ℝ) ≤ (k : ℝ) + 2 by positivity)
    nlinarith only [hk, hkl, hL₀]
  have hKhi : (K : ℝ) ≤ b * L ^ 2 * l := by
    have hh := Nat.floor_le (show 0 ≤ b * logScale N by
      change 0 ≤ b * (l * L ^ 2); positivity)
    simpa only [K, logScale, ← show log (N : ℝ) = L from rfl,
      ← show log L = l from rfl, mul_assoc, mul_comm, mul_left_comm] using hh
  have hKcube : (K : ℝ) ≤ L ^ 3 := hKhi.trans (by
    calc
      b * L ^ 2 * l ≤ 1 * L ^ 2 * l := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hb₁ (sq_nonneg _)) hl₀.le
      _ ≤ _ := by rw [one_mul]; simpa [pow_succ] using mul_le_mul_of_nonneg_left hlL (sq_nonneg L))
  have hLevel : Z ^ (k + 1) * H ≤ D := by
    apply Nat.le_floor
    push_cast
    have hZexp : (Z : ℝ) ≤ exp (4 * l) := by
      exact hZhi.trans (by simpa [hLexp] using (exp_nat_mul l 4).ge)
    have hpow := pow_le_exp_product (Nat.cast_nonneg _) hZexp (k + 1)
    have hprod := exp_mul_bound (by positivity) hpow hHhi
    apply hprod.trans
    apply exp_le_exp.mpr
    push_cast
    nlinarith only [hkl, hl₀, hL₀]
  have hlocal' : 2 * K ≤ Y ^ 2 := by
    have hlower := pow_le_pow_left₀ (show 0 ≤ c * L * l / 2 by positivity) hYlo 2
    have h := (div_le_iff₀ (show 0 < c ^ 2 by positivity)).mp hlocal
    have hmul := mul_le_mul_of_nonneg_right h (show 0 ≤ L ^ 2 * l by positivity)
    have he : (2 : ℝ) * K ≤ (Y : ℝ) ^ 2 := by
      nlinarith only [hlower, hmul, mul_le_mul_of_nonneg_left hKhi (show 0 ≤ (2 : ℝ) by norm_num)]
    exact_mod_cast he
  have hμ : (K : ℝ) * primeTail Y Z ≤ lambdaBound := by
    have htail := prime_tail_bound hC (show 2 ≤ Y₀ by omega) hπ Z Y hYY
    have hden : c * L * l ^ 2 / 4 ≤ (Y : ℝ) * log (Y : ℝ) := by
      have h := mul_le_mul hYlo hlogY (by positivity) hYR.le
      nlinarith only [h]
    have hden₀ : 0 < c * L * l ^ 2 / 4 := by positivity
    calc
      _ ≤ (K : ℝ) * (4 * C / ((Y : ℝ) * log (Y : ℝ))) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ (b * L ^ 2 * l) * (4 * C / (c * L * l ^ 2 / 4)) := by
        exact mul_le_mul hKhi (div_le_div_of_nonneg_left (by positivity) hden₀ hden)
          (by positivity) (by positivity)
      _ = (16 * C * b / c) * (L / l) := by field_simp; ring
      _ ≤ lambdaBound := by simpa [lambdaBound, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
        using mul_le_mul_of_nonneg_right hsmallB (show 0 ≤ L / l by positivity)
  have htrunc : exp (4 * lambdaBound) / (2 : ℝ) ^ (k + 1) ≤ 1 / 4 := by
    have hpow : (2 : ℝ) ^ (k + 1) = exp (((k : ℝ) + 1) * log 2) := by
      calc
        (2 : ℝ) ^ (k + 1) = (exp (log 2)) ^ (k + 1) := by rw [exp_log (by norm_num)]
        _ = _ := by rw [← exp_nat_mul, Nat.cast_add, Nat.cast_one]
    rw [hpow, ← exp_sub]
    have hcoeff : 4 * lambdaBound - ((k : ℝ) + 1) * log 2 ≤ -2 * log 2 := by
      have hratio' : (20000 : ℝ) ≤ L / l := hratio
      rw [show L / (2500 * l) = (L / l) / 2500 by ring] at hklow
      have hc' : 2 + (4 / 100000 : ℝ) * (L / l) ≤ (k : ℝ) + 1 := by linarith
      have hh := mul_le_mul_of_nonneg_right hc' hlog2.le
      unfold lambdaBound
      nlinarith only [hh]
    exact (exp_le_exp.mpr hcoeff).trans (by
      rw [show -2 * log (2 : ℝ) = -(2 * log (2 : ℝ)) by ring, exp_neg,
        show 2 * log (2 : ℝ) = (2 : ℕ) * log (2 : ℝ) by norm_num,
        exp_nat_mul, exp_log (by norm_num)]
      norm_num)
  have hband' : (K : ℝ) * primeTail Z H ≤ 1 / 4 := by
    have hZ₀ : Y₀ ≤ Z := hYY.trans hYZ
    have hlogZ : 1 ≤ log (Z : ℝ) := by
      exact (show (1 : ℝ) ≤ l / 2 by linarith).trans
        (hlogY.trans (log_le_log hYR (by exact_mod_cast hYZ)))
    have hden : L ^ 4 / 16 ≤ (Z : ℝ) * log (Z : ℝ) :=
      hZlo.trans (le_mul_of_one_le_right (by positivity) hlogZ)
    have htail := prime_tail_bound hC (show 2 ≤ Y₀ by omega) hπ H Z hZ₀
    calc
      _ ≤ (K : ℝ) * (4 * C / ((Z : ℝ) * log (Z : ℝ))) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ (b * L ^ 2 * l) * (4 * C / (L ^ 4 / 16)) := by
        exact mul_le_mul hKhi (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
          (by positivity) (by positivity)
      _ ≤ (64 * C * b) / L := by
        have hform : (b * L ^ 2 * L) * (4 * C / (L ^ 4 / 16)) = (64 * C * b) / L := by
          field_simp [hL₀.ne'] <;> ring
        exact (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlL (show 0 ≤ b * L ^ 2 by positivity))
          (show 0 ≤ 4 * C / (L ^ 4 / 16) by positivity)).trans_eq hform
      _ ≤ _ := by
        apply (div_le_iff₀ hL₀).mpr
        linarith
  let t := ((Nat.primesLE Y).erase 2).card
  let ρ := presieveFraction Y
  let Λ := presieveError Y E
  have ht : (t : ℝ) ≤ 2 * C * c * L := by
    have hcount : (t : ℝ) ≤ Nat.primeCounting Y := by
      exact_mod_cast (show t ≤ Nat.primeCounting Y by
        rw [← Nat.primesLE_card_eq_primeCounting]
        exact card_le_card (erase_subset _ _))
    calc
      _ ≤ C * (Y : ℝ) / log (Y : ℝ) := hcount.trans (hπ Y hYY)
      _ ≤ C * (c * L * l) / (l / 2) := by
        exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hYhi hC) (by linarith)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hlogY)
      _ = _ := by field_simp <;> ring
  have h6 : (6 : ℝ) ^ t ≤ exp (L / 1000) := by
    rw [← exp_log (show (0 : ℝ) < 6 by norm_num), ← exp_nat_mul]
    apply exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right ht (log_nonneg (by norm_num : (1 : ℝ) ≤ 6))
    have hs' := mul_le_mul_of_nonneg_right hsmallC hL₀.le
    linarith [show 2 * C * c * L * log (6 : ℝ) = (2 * C * c * log 6) * L by ring]
  have h2t : (2 : ℝ) ^ t ≤ exp (L / 1000) :=
    (pow_le_pow_left₀ (by norm_num) (by norm_num : (2 : ℝ) ≤ 6) _).trans h6
  have hρ₀ : 0 < ρ := by dsimp [ρ, presieveFraction]; positivity
  have hρ₁ : ρ ≤ 1 := by
    change ((2 : ℝ) ^ t)⁻¹ ≤ 1
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hρlo : exp (-L / 1000) ≤ ρ := by
    rw [show -L / 1000 = -(L / 1000) by ring, exp_neg]
    change (exp (L / 1000))⁻¹ ≤ ((2 : ℝ) ^ t)⁻¹
    exact inv_anti₀ (by positivity) h2t
  have hE₃ : 3 ≤ E := (hconst 3 (by linarith)).trans (exp_le_exp.mpr (by linarith))
  have hΛ : Λ ≤ 2 * E := by
    have heq : ((2 * (2 : ℝ) ^ t + 1) * ρ) = 2 + ρ := by
      change (2 * (2 : ℝ) ^ t + 1) * ((2 : ℝ) ^ t)⁻¹ = 2 + ((2 : ℝ) ^ t)⁻¹
      field_simp
    change E + ((2 * (2 : ℝ) ^ t + 1) * ρ) ≤ 2 * E
    rw [heq]
    linarith
  have hΛ₀ : 0 ≤ Λ := by
    dsimp [Λ, presieveError, presieveFraction, E]
    positivity
  have hDterm : (((D + 1 : ℕ) : ℝ) * (D : ℝ) ^ 2) ≤ exp (251 * L / 1000) := by
    have hD1 : ((D + 1 : ℕ) : ℝ) ≤ exp (L / 12 + L / 1000) := by
      have h₁ : (D : ℝ) + 1 ≤ exp (L / 12) * 2 := by
        linarith [one_le_exp (show 0 ≤ L / 12 by positivity)]
      exact (by exact_mod_cast h₁ : ((D + 1 : ℕ) : ℝ) ≤ exp (L / 12) * 2).trans
        (exp_mul_bound (by positivity) le_rfl (hconst 2 (by linarith)))
    have hD2 := pow_le_exp_product (Nat.cast_nonneg _) hDhi 2
    exact (exp_mul_bound (by positivity) hD1 hD2).trans (exp_le_exp.mpr (by norm_num; linarith))
  have hNterm : ρ ^ 2 * (N : ℝ) * (2 * (2 : ℝ) ^ t * 3 ^ t) ≤ exp (1002 * L / 1000) := by
    have hp : ρ^2 * (N : ℝ) ≤ exp L := by
      rw [← hNreal]
      exact mul_le_of_le_one_left (by positivity) (by
        simpa using pow_le_pow_left₀ hρ₀.le hρ₁ 2)
    have hh : 2 * (2 : ℝ) ^ t * 3 ^ t ≤ exp (2 * L / 1000) := by
      rw [mul_assoc, ← mul_pow]
      norm_num
      exact (exp_mul_bound (by norm_num : (0 : ℝ) ≤ 2) (hconst 2 (by linarith)) h6).trans
        (exp_le_exp.mpr (by linarith))
    exact (exp_mul_bound (by positivity) hp hh).trans (exp_le_exp.mpr (by linarith))
  have hvar : (((D + 1 : ℕ) : ℝ) * (D : ℝ) ^ 2) *
      (ρ ^ 2 * N * (2 * (2 : ℝ) ^ t * 3 ^ t)) ≤ E ^ 2 := by
    have hp := exp_mul_bound (by positivity) hDterm hNterm
    refine hp.trans ?_
    change exp _ ≤ exp (3 * L / 4) ^ 2
    rw [← exp_nat_mul]
    exact exp_le_exp.mpr (by norm_num; linarith)
  have hm : m ≤ (N : ℝ) / 4 * exp (-1) * ρ - Λ := by
    have hcoef : 0 ≤ (N : ℝ) / 4 * exp (-1) := by positivity
    have hh := mul_le_mul_of_nonneg_left hρlo hcoef
    have hbase : 2 * m ≤ (N : ℝ) / 4 * exp (-1) * exp (-L / 1000) := by
      have h0 := exp_mul_bound (by positivity : 0 ≤ 8 * exp (1 : ℝ))
        (hconst (8 * exp 1) (by nlinarith [exp_pos (1 : ℝ)])) (le_rfl : m ≤ exp (99 * L / 100))
      have h1 : 8 * exp 1 * m ≤ exp L * exp (-L / 1000) := by
        rw [← exp_add]
        exact h0.trans (exp_le_exp.mpr (by linarith))
      rw [hNreal, exp_neg]
      apply (le_of_mul_le_mul_right ?_ (show 0 < 4 * exp 1 by positivity))
      have he : (exp L / 4 * (exp 1)⁻¹ * exp (-L / 1000)) * (4 * exp 1) =
          exp L * exp (-L / 1000) := by field_simp <;> ring
      rw [he]
      nlinarith only [h1]
    have hΛm : Λ ≤ m := hΛ.trans (by
      exact (exp_mul_bound (by norm_num : (0 : ℝ) ≤ 2)
        (hconst 2 (by linarith)) (le_rfl : E ≤ exp (3 * L / 4))).trans
          (exp_le_exp.mpr (by linarith)))
    linarith [hbase.trans hh]
  have hKexp : (K : ℝ) ≤ exp (L / 1000) := hKcube.trans (hs 3 (by norm_num))
  have hKpow : (K : ℝ) ^ (k + 2) ≤ exp (3 * L / 1000) := by
    have ha : (K : ℝ) ≤ exp (3 * l) := hKcube.trans (by
      simpa [hLexp] using (exp_nat_mul l 3).ge)
    apply (pow_le_exp_product (by positivity) ha (k + 2)).trans
    apply exp_le_exp.mpr
    push_cast
    nlinarith only [hkl]
  have hZpow : ((Z + 1 : ℕ) : ℝ) ^ (k + 1) ≤ exp (5 * L / 1000) := by
    have hZexp : ((Z + 1 : ℕ) : ℝ) ≤ exp (5 * l) := by
      have hk : (Z : ℝ) + 1 ≤ L ^ 5 := by
        nlinarith only [hZhi, mul_le_mul_of_nonneg_right (show 2 ≤ L by linarith) (show 0 ≤ L ^ 4 by positivity),
          one_le_pow₀ (show 1 ≤ L by linarith) (n := 4)]
      exact (by exact_mod_cast hk : ((Z + 1 : ℕ) : ℝ) ≤ L ^ 5).trans
        (by simpa [hLexp] using (exp_nat_mul l 5).ge)
    apply (pow_le_exp_product (by positivity) hZexp (k + 1)).trans
    apply exp_le_exp.mpr
    push_cast
    nlinarith only [hkl, hl₀]
  have hH₁ : (H : ℝ) + 1 ≤ exp (64 * L / 1000) := by
    have h₁ : (H : ℝ) + 1 ≤ 2 * exp (L / 16) := by
      linarith [one_le_exp (show 0 ≤ L / 16 by positivity)]
    exact h₁.trans ((exp_mul_bound (by norm_num : (0 : ℝ) ≤ 2)
      (hconst 2 (by linarith)) (le_rfl : exp (L / 16) ≤ exp (L / 16))).trans
        (exp_le_exp.mpr (by linarith)))
  have hErr : ((H : ℝ) + 1) * ((2 * Λ) * (K : ℝ) ^ (k + 2) *
      (((k + 2 : ℕ) : ℝ) * ((Z + 1 : ℕ) : ℝ) ^ (k + 1))) ≤ exp (95 * L / 100) := by
    have hk₂ : ((k + 2 : ℕ) : ℝ) ≤ exp (L / 1000) := by
      exact (by exact_mod_cast hkL : ((k + 2 : ℕ) : ℝ) ≤ L).trans (by
        simpa using hs 1 (by norm_num))
    have hΛ' : 2 * Λ ≤ exp (751 * L / 1000) := by
      exact (show 2 * Λ ≤ 4 * E by linarith).trans
        ((exp_mul_bound (by norm_num : (0 : ℝ) ≤ 4) (hconst 4 (by linarith))
          (le_rfl : E ≤ exp (3 * L / 4))).trans (exp_le_exp.mpr (by linarith)))
    have h2Λ₀ : 0 ≤ 2 * Λ := mul_nonneg (by norm_num) hΛ₀
    have hpow₀ : 0 ≤ (2 * Λ) * (K : ℝ) ^ (k + 2) := mul_nonneg h2Λ₀ (by positivity)
    exact (exp_mul_bound (by positivity) hH₁
      (exp_mul_bound hpow₀ (exp_mul_bound h2Λ₀ hΛ' hKpow)
        (exp_mul_bound (by positivity) hk₂ hZpow))).trans (exp_le_exp.mpr (by linarith))
  have hTail : (K : ℝ) * ((N : ℝ) / H + (Nat.sqrt N : ℝ)) ≤ exp (95 * L / 100) := by
    have hdiv : (N : ℝ) / H ≤ 2 * exp (15 * L / 16) := by
      calc
        _ ≤ (N : ℝ) / (exp (L / 16) / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hHlo
        _ = 2 * (exp L / exp (L / 16)) := by rw [hNreal]; ring
        _ = _ := by rw [← exp_sub]; congr 2; ring
    have hS : (Nat.sqrt N : ℝ) ≤ exp (15 * L / 16) := by
      have hh : ((Nat.sqrt N : ℝ) ^ 2) ≤ (N : ℝ) := by
        exact_mod_cast (show (Nat.sqrt N) ^ 2 ≤ N by simpa [pow_two] using Nat.sqrt_le N)
      have hp : (Nat.sqrt N : ℝ) ≤ exp (L / 2) := by
        have he : exp (L / 2) ^ 2 = (N : ℝ) := by
          rw [← exp_nat_mul, hNreal]; congr 1; norm_num; ring
        apply (sq_le_sq₀ (by positivity) (by positivity)).mp
        rw [he]
        exact hh
      exact hp.trans (exp_le_exp.mpr (by linarith))
    have hh : (N : ℝ) / H + (Nat.sqrt N : ℝ) ≤ exp (15 * L / 16 + L / 1000) :=
      (show (N : ℝ) / H + (Nat.sqrt N : ℝ) ≤ exp (15 * L / 16) * 3 by linarith).trans
        (exp_mul_bound (by positivity) le_rfl (hconst 3 (by linarith)))
    exact (exp_mul_bound (by positivity) hKexp hh).trans (exp_le_exp.mpr (by linarith))
  have hbudget : (K : ℝ) +
      ((H : ℝ) + 1) * ((2 * Λ) * (K : ℝ) ^ (k + 2) *
        (((k + 2 : ℕ) : ℝ) * ((Z + 1 : ℕ) : ℝ) ^ (k + 1))) +
      (K : ℝ) * ((N : ℝ) / H + (Nat.sqrt N : ℝ)) < m * (exp (-2 * lambdaBound) / 3) := by
    have hK' := hKexp.trans (exp_le_exp.mpr (by linarith : L / 1000 ≤ 95 * L / 100))
    have hsum := add_le_add (add_le_add hK' hErr) hTail
    have hsum' : exp (95 * L / 100) + exp (95 * L / 100) + exp (95 * L / 100) <
        m * (exp (-2 * lambdaBound) / 3) := by
      have hlambdaBound : lambdaBound ≤ L / 100000 := by
        have hl' : L / l ≤ L := (div_le_iff₀ hl₀).mpr (le_mul_of_one_le_right hL₀.le (by linarith))
        unfold lambdaBound
        exact div_le_div_of_nonneg_right
          ((mul_le_of_le_one_left (by positivity) hlog2₁).trans hl') (by norm_num)
      have hsum9 := exp_mul_bound (by norm_num : (0 : ℝ) ≤ 9) (hconst 9 (by linarith))
        (le_rfl : exp (95 * L / 100) ≤ exp (95 * L / 100))
      have hh : 9 * exp (95 * L / 100) < exp (99 * L / 100 + -2 * lambdaBound) :=
        hsum9.trans_lt (exp_lt_exp.mpr (by linarith))
      rw [exp_add] at hh
      dsimp [m]
      linarith
    exact hsum.trans_lt hsum'
  exact ⟨{
    y := Y, z := Z, H := H, D := D, k := k, K := K, E := E, lambdaBound := lambdaBound, m := m,
    hy := hY₃, hyz := hYZ, hzH := hZH, hHN := hHN, hD := hDpos, hk := hkOdd,
    hLevel := hLevel, hE := (exp_pos _).le, hvar := hvar, hmass := ⟨by positivity, hm⟩,
    hlocal := hlocal', hlam := hμ, htrunc := htrunc, hband := hband', hbudget := hbudget
  }, rfl⟩

theorem chebyshev_natural_bound :
    ∃ Y₀ ≥ 3, ∀ n ≥ Y₀,
      (Nat.primeCounting n : ℝ) ≤ (log 4 + 1) * n / log n := by
  have hev := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hev
  refine ⟨max 3 Y, le_max_left _ _, fun n hn => ?_⟩
  simpa using hY n ((le_max_right _ _).trans hn)

set_option maxHeartbeats 1500000 in
theorem asymptotic_growth_inputs (Y₀ : ℕ) {c b C : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      let L := log (N : ℝ)
      let l := log L
      4 ≤ L ∧ 10 ≤ l ∧ 20000 ≤ L / l ∧ (Y₀ : ℝ) ≤ c * L * l / 2 ∧
        -2 * log (c / 2) ≤ l ∧ 8 * b / c ^ 2 ≤ l ∧
        32 * exp 1 * L ^ 8 ≤ exp (L / 1000) ∧ 256 * C * b ≤ L := by
  let L (N : ℕ) := log (N : ℝ)
  let l (N : ℕ) := log (L N)
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hL : Tendsto L atTop atTop := tendsto_log_atTop.comp hcast
  have hl : Tendsto l atTop atTop := tendsto_log_atTop.comp hL
  have hlogratio : ∀ᶠ N in atTop, ‖l N‖ ≤ (1 / 20000 : ℝ) * ‖L N‖ :=
    (Real.isLittleO_log_id_atTop.comp_tendsto hL).bound (by norm_num)
  have hrpow : ∀ᶠ N : ℕ in atTop,
      ‖(L N) ^ (8 : ℝ)‖ ≤ (1 / (32 * exp 1) : ℝ) * ‖(N : ℝ) ^ (1 / 1000 : ℝ)‖ :=
    ((isLittleO_log_rpow_rpow_atTop (s := 1 / 1000) 8 (by norm_num)).comp_tendsto hcast).bound
      (by positivity)
  have hprod : Tendsto (fun N : ℕ => c * L N * l N) atTop atTop :=
    (hL.const_mul_atTop hc).atTop_mul_atTop₀ hl
  filter_upwards [hL.eventually_ge_atTop 4, hl.eventually_ge_atTop 10, hlogratio,
    hprod.eventually_ge_atTop (2 * Y₀), hl.eventually_ge_atTop (-2 * log (c / 2)),
    hl.eventually_ge_atTop (8 * b / c ^ 2), hrpow,
    hL.eventually_ge_atTop (256 * C * b), eventually_ge_atTop 1]
    with N hNL hNl hrat hY h₁ h₂ henv h₃ hN
  have hLpos : 0 < L N := by linarith
  have hlpos : 0 < l N := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr : (20000 : ℝ) ≤ L N / l N := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlpos.le, abs_of_nonneg hLpos.le] at hrat
    exact (le_div_iff₀ hlpos).mpr (by linarith)
  have henv' : 32 * exp 1 * (L N) ^ 8 ≤ exp (L N / 1000) := by
    have henv'' : (L N) ^ 8 ≤ (1 / (32 * exp 1) : ℝ) * exp (L N / 1000) := by
      have h₁ : ‖(L N) ^ (8 : ℝ)‖ = (L N) ^ 8 := by
        rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs,
          abs_of_nonneg (pow_nonneg hLpos.le 8)]
      have h₂ : ‖(N : ℝ) ^ (1 / 1000 : ℝ)‖ = exp (L N / 1000) := by
        rw [Real.rpow_def_of_pos hNpos, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        congr 1
        simp only [L]
        ring
      rwa [h₁, h₂] at henv
    have hdiv : (L N) ^ 8 ≤ exp (L N / 1000) / (32 * exp 1) := by
      simpa [div_eq_mul_inv, mul_comm] using henv''
    have hmul := (le_div_iff₀ (show 0 < 32 * exp 1 by positivity)).mp hdiv
    simpa [mul_comm] using hmul
  exact ⟨hNL, hNl, hr, by linarith, h₁, h₂, henv', h₃⟩

theorem exact_by_sieve_parameters : type_of% @Erdos1109.erdos_1109.variants.konyagin_lower := by
  let C := log 4 + 1
  let c : ℝ := 1 / (1 + 2000 * C * log 6)
  let b : ℝ := c * log 2 / (1600000 * (C + 1))
  have hC : 0 ≤ C := by dsimp [C]; linarith [log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  have hlog6 : 0 ≤ log (6 : ℝ) := log_nonneg (by norm_num)
  have hcDen : 1 ≤ 1 + 2000 * C * log 6 := by
    linarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2000) hC) hlog6]
  have hc : 0 < c := div_pos (by norm_num) (by linarith)
  have hc₁ : c ≤ 1 := (div_le_one (by linarith)).mpr hcDen
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hlog2₁ : log 2 ≤ 1 := by
    have h := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have hbDen : 1 ≤ 1600000 * (C + 1) := by linarith
  have hb : 0 < b := div_pos (mul_pos hc hlog2) (by linarith)
  have hb₁ : b ≤ 1 := (div_le_one (by linarith : 0 < 1600000 * (C + 1))).mpr
    ((mul_le_mul hc₁ hlog2₁ hlog2.le (by norm_num)).trans (by simpa using hbDen))
  have hsmallC : 2 * C * c * log 6 ≤ 1 / 1000 := by
    calc
      _ = (2 * C * log 6) / (1 + 2000 * C * log 6) := by dsimp [c]; ring
      _ ≤ _ := (div_le_iff₀ (by linarith : 0 < 1 + 2000 * C * log 6)).mpr (by ring_nf; linarith)
  have hsmallB : 16 * C * b / c ≤ log 2 / 100000 := by
    calc
      _ = (log 2 / 100000) * (C / (C + 1)) := by
        dsimp [b]
        have hC₁ : C + 1 ≠ 0 := by linarith
        field_simp [hc.ne', hC₁]
        ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) ((div_le_one (by linarith)).mpr (by linarith))
  obtain ⟨Y₀, hY₀, hπ⟩ := chebyshev_natural_bound
  let K (N : ℕ) := ⌊b * logScale N⌋₊
  refine exact_of_eventual_card (K := K) (show 0 < b / 2 by positivity) ?_ ?_
  · filter_upwards [scale_tendsto.eventually_ge_atTop (2 / b)] with N hN
    have h : 2 ≤ b * logScale N := by simpa [mul_comm] using (div_le_iff₀ hb).mp hN
    have h' := floor_half h
    change b / 2 * logScale N ≤ (K N : ℝ)
    simpa [K, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h'
  · filter_upwards [asymptotic_growth_inputs Y₀ (C := C) (b := b) hc, eventually_ge_atTop 1] with N hn hN
    obtain ⟨par, hpar⟩ := numeric_parameters N Y₀ (by omega) hY₀ hC hc hc₁ hb hb₁ hsmallC hsmallB hπ hn
    change ⌊b * logScale N⌋₊ ≤ Erdos1109.f N
    rw [← hpar]
    exact finite_certificate_bound N par

end SquarefreeSums

theorem OMA.solution : type_of% @Erdos1109.erdos_1109.variants.konyagin_lower := by
  exact SquarefreeSums.exact_by_sieve_parameters
