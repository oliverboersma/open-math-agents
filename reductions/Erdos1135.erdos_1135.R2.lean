import FormalConjectures.ErdosProblems.«1135»

/-!
A parity criterion for descent and the finite parity-word equation for cycles.
Use the shortcut map, which divides each odd output by two immediately.
On a segment with distinct odd inputs greater than one, the product of the
odd-step corrections, raised to the sixth power, is at most
`(n - 2 + 2 * s) / (n - 2)` when the odd starting value `n` is a lower
bound for the segment and `s` is its odd count. This gives a descent test using only the length
and odd count of the segment. A repeated input instead gives an integer
solution to the affine fixed-point equation of a nonempty parity word.
The supplementary density theorem proves the parity condition outside a set
of upper natural density zero by counting the two lifts of each parity word.

Credit: @ubuwaits. The shortcut map and finite parity-word identity are
classical; see J. C. Lagarias, The 3x+1 problem and its generalizations (1985).
-/

namespace OMA.R_Erdos1135_erdos_1135_R2

open CollatzConjecture Function Finset

/-- A parity deficit for the large starting values without immediate descent. -/
def H1 : Prop :=
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  ∀ n : ℕ, 2048 < n → n % 4 = 3 → ∃ k : ℕ,
    let s := ((range k).filter fun i => T^[i] n % 2 = 1).card
    (n - 2 + 2 * s) * (3 ^ s) ^ 6 < (n - 2) * (2 ^ k) ^ 6

/-- Exclude the finite parity words surviving the period and size bounds.
`S` records the odd positions of a word of length `k`. -/
def H2 : Prop :=
  ∀ (k n : ℕ) (S : Finset ℕ), 2048 < n → S ⊆ range k → 94 ≤ S.card →
    3 ^ S.card < 2 ^ k → 2 ^ k * 2048 ^ S.card ≤ 6145 ^ S.card →
    2 ^ k * n ≠ 3 ^ S.card * n + ∑ i ∈ S, 2 ^ i * 3 ^ (S.filter fun j => i < j).card

/-- The next factor when the smaller odd inputs occupy at most `c` ranks. -/
lemma rank_factor (c u : ℕ) (hu : c < u) :
    (6 * u + 4) ^ 6 * (2 * c + 1) ≤ (6 * u + 3) ^ 6 * (2 * c + 3) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hu)
  zify
  rw [← sub_nonneg]
  ring_nf
  positivity

/-- Write each odd input as `2*u+1`. If they are all at least `2*m+3`,
the telescoping bound retains the lower endpoint as well as the count. -/
lemma correction_product (m : ℕ) (S : Finset ℕ) (hpos : ∀ u ∈ S, m < u) :
    (2 * m + 1) * (∏ u ∈ S, (6 * u + 4)) ^ 6 ≤
      (2 * (m + S.card) + 1) * (∏ u ∈ S, (6 * u + 3)) ^ 6 := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert u S hmax ih =>
    have hu := hpos u (mem_insert_self _ _)
    have hp : ∀ j ∈ S, m < j := fun j hj => hpos j (mem_insert_of_mem hj)
    have hnot : u ∉ S := fun hx => (lt_irrefl u) (hmax u hx)
    have hsub : S ⊆ Ico (m + 1) u := fun j hj => mem_Ico.mpr ⟨hp j hj, hmax j hj⟩
    have hc := card_le_card hsub
    rw [Nat.card_Ico] at hc
    have hr := rank_factor (m + S.card) u (by omega)
    rw [prod_insert hnot, prod_insert hnot, card_insert_of_notMem hnot, mul_pow, mul_pow]
    calc
      _ = (6 * u + 4) ^ 6 * ((2 * m + 1) * (∏ j ∈ S, (6 * j + 4)) ^ 6) := by ring
      _ ≤ (6 * u + 4) ^ 6 * ((2 * (m + S.card) + 1) * (∏ j ∈ S, (6 * j + 3)) ^ 6) :=
        Nat.mul_le_mul_left _ (ih hp)
      _ = ((6 * u + 4) ^ 6 * (2 * (m + S.card) + 1)) * (∏ j ∈ S, (6 * j + 3)) ^ 6 := by ring
      _ ≤ ((6 * u + 3) ^ 6 * (2 * (m + S.card) + 3)) * (∏ j ∈ S, (6 * j + 3)) ^ 6 :=
        Nat.mul_le_mul_right _ hr
      _ = _ := by ring

/-- The same estimate indexed by the times at which the odd inputs occur. -/
lemma orbit_correction (m : ℕ) (x : ℕ → ℕ) (S : Finset ℕ)
    (hodd : ∀ i ∈ S, x i % 2 = 1) (hlarge : ∀ i ∈ S, 2 * m + 3 ≤ x i)
    (hinj : Set.InjOn x S) :
    (2 * m + 1) * (∏ i ∈ S, (3 * x i + 1)) ^ 6 ≤
      (2 * (m + S.card) + 1) * (∏ i ∈ S, (3 * x i)) ^ 6 := by
  let f := fun i => x i / 2
  have hf : Set.InjOn f S := by
    intro i hi j hj he
    apply hinj hi hj
    have hi' := hodd i hi
    have hj' := hodd j hj
    change x i / 2 = x j / 2 at he
    omega
  have h := correction_product m (S.image f) (by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hu
    have := hlarge i hi
    dsimp [f]
    omega)
  rw [card_image_of_injOn hf, prod_image hf, prod_image hf] at h
  have hnum : (∏ i ∈ S, (6 * f i + 4)) = ∏ i ∈ S, (3 * x i + 1) := by
    apply prod_congr rfl
    intro i hi
    have := hodd i hi
    dsimp [f]
    omega
  have hden : (∏ i ∈ S, (6 * f i + 3)) = ∏ i ∈ S, (3 * x i) := by
    apply prod_congr rfl
    intro i hi
    have := hodd i hi
    dsimp [f]
    omega
  rwa [hnum, hden] at h

section Prefix

variable {x : ℕ → ℕ} {odds : ℕ → Finset ℕ}

lemma odds_succ
    (ho : ∀ k, odds k = (range k).filter fun i => x i % 2 = 1) (k : ℕ) :
    odds (k + 1) = if x k % 2 = 1 then insert k (odds k) else odds k := by
  rw [ho, ho, range_add_one, filter_insert]

lemma odds_lt
    (ho : ∀ k, odds k = (range k).filter fun i => x i % 2 = 1) {k i : ℕ} (hi : i ∈ odds k) : i < k := by
  rw [ho] at hi
  exact mem_range.mp (mem_filter.mp hi).1

/-- Multiply the one-step identities, keeping the odd-step correction as an
exact ratio of two products. All quantities here are natural numbers. -/
lemma product_identity
    (hx : ∀ i, 2 * x (i + 1) = if x i % 2 = 1 then 3 * x i + 1 else x i)
    (ho : ∀ k, odds k = (range k).filter fun i => x i % 2 = 1) (k : ℕ) :
    (2 ^ k * x k) * (∏ i ∈ odds k, (3 * x i)) =
      (3 ^ (odds k).card * x 0) * (∏ i ∈ odds k, (3 * x i + 1)) := by
  induction k with
  | zero => simp [ho]
  | succ k ih =>
    have hnot : k ∉ odds k := fun h => (lt_irrefl k) (odds_lt ho h)
    have hstep := hx k
    rw [odds_succ ho]
    by_cases h : x k % 2 = 1
    · rw [if_pos h] at hstep ⊢
      rw [prod_insert hnot, prod_insert hnot, card_insert_of_notMem hnot, pow_succ, pow_succ]
      calc
        _ = ((2 ^ k * x k) * (∏ i ∈ odds k, (3 * x i))) * (3 * (2 * x (k + 1))) := by ring
        _ = _ := by rw [ih, hstep]; ring
    · rw [if_neg h] at hstep ⊢
      rw [pow_succ, Nat.mul_assoc (2 ^ k) 2, hstep, ih]

/-- The affine numerator written as a sum over the positions of the odd steps. -/
lemma affine_identity
    (hx : ∀ i, 2 * x (i + 1) = if x i % 2 = 1 then 3 * x i + 1 else x i)
    (ho : ∀ k, odds k = (range k).filter fun i => x i % 2 = 1) (k : ℕ) :
    2 ^ k * x k = 3 ^ (odds k).card * x 0 +
      ∑ i ∈ odds k, 2 ^ i * 3 ^ ((odds k).filter fun j => i < j).card := by
  induction k with
  | zero => simp [ho]
  | succ k ih =>
    have hnot : k ∉ odds k := fun h => (lt_irrefl k) (odds_lt ho h)
    have hstep := hx k
    rw [pow_succ, Nat.mul_assoc, odds_succ ho]
    by_cases h : x k % 2 = 1
    · rw [if_pos h] at hstep ⊢
      rw [hstep, card_insert_of_notMem hnot, sum_insert hnot, pow_succ]
      have hlast : ((insert k (odds k)).filter fun j => k < j) = ∅ := by
        ext j
        simp only [mem_filter, mem_insert, notMem_empty, iff_false, not_and]
        rintro (rfl | hj) hlt
        · omega
        · have := odds_lt ho hj
          omega
      have hterm (i : ℕ) (hi : i ∈ odds k) :
          2 ^ i * 3 ^ (((insert k (odds k)).filter fun j => i < j).card) =
          3 * (2 ^ i * 3 ^ (((odds k).filter fun j => i < j).card)) := by
        rw [filter_insert, if_pos (odds_lt ho hi), card_insert_of_notMem, pow_succ]
        · ring
        · exact fun hk => hnot (mem_filter.mp hk).1
      rw [hlast, card_empty, pow_zero, mul_one, sum_congr rfl hterm, ← Finset.mul_sum]
      calc 2 ^ k * (3 * x k + 1) = 3 * (2 ^ k * x k) + 2 ^ k := by ring
           _ = _ := by rw [ih]; ring
    · rw [if_neg h] at hstep ⊢
      rw [hstep, ih]

end Prefix

/-- A sufficiently large parity deficit forces the endpoint below the start
whenever the odd inputs are distinct and greater than two. -/
lemma parity_drop (m : ℕ) (x : ℕ → ℕ) (k : ℕ) (S : Finset ℕ)
    (hstart : 0 < x 0) (hodd : ∀ i ∈ S, x i % 2 = 1)
    (hlarge : ∀ i ∈ S, 2 * m + 3 ≤ x i) (hinj : Set.InjOn x S)
    (hproduct : (2 ^ k * x k) * (∏ i ∈ S, (3 * x i)) =
      (3 ^ S.card * x 0) * (∏ i ∈ S, (3 * x i + 1)))
    (htest : (2 * (m + S.card) + 1) * (3 ^ S.card) ^ 6 < (2 * m + 1) * (2 ^ k) ^ 6) : x k < x 0 := by
  let P := ∏ i ∈ S, (3 * x i + 1)
  let D := ∏ i ∈ S, (3 * x i)
  change (2 ^ k * x k) * D = (3 ^ S.card * x 0) * P at hproduct
  have hc : (2 * m + 1) * P ^ 6 ≤ (2 * (m + S.card) + 1) * D ^ 6 :=
    orbit_correction m x S hodd hlarge hinj
  have hd : 0 < D := prod_pos fun i hi => Nat.mul_pos (by decide) (by have := hlarge i hi; omega)
  have hm : 0 < x 0 ^ 6 * D ^ 6 := by positivity
  by_contra! hnon
  apply (lt_irrefl (((2 * m + 1) * (2 ^ k) ^ 6) * (x 0 ^ 6 * D ^ 6)))
  calc
    ((2 * m + 1) * (2 ^ k) ^ 6) * (x 0 ^ 6 * D ^ 6) =
        (2 * m + 1) * ((2 ^ k * x 0) * D) ^ 6 := by ring
    _ ≤ (2 * m + 1) * ((2 ^ k * x k) * D) ^ 6 := by gcongr
    _ = (2 * m + 1) * ((3 ^ S.card * x 0) * P) ^ 6 := by rw [hproduct]
    _ = ((3 ^ S.card) ^ 6 * x 0 ^ 6) * ((2 * m + 1) * P ^ 6) := by ring
    _ ≤ ((3 ^ S.card) ^ 6 * x 0 ^ 6) * ((2 * (m + S.card) + 1) * D ^ 6) :=
      Nat.mul_le_mul_left _ hc
    _ = ((2 * (m + S.card) + 1) * (3 ^ S.card) ^ 6) * (x 0 ^ 6 * D ^ 6) := by ring
    _ < _ := Nat.mul_lt_mul_of_pos_right htest hm

section Shortcut

variable {T : ℕ → ℕ}

lemma shortcut_rec (hT : ∀ v, T v = if v % 2 = 0 then v / 2 else (3 * v + 1) / 2)
    (n i : ℕ) : 2 * T^[i + 1] n = if T^[i] n % 2 = 1 then 3 * T^[i] n + 1 else T^[i] n := by
  rw [iterate_succ_apply', hT]
  split_ifs <;> omega

lemma shortcut_positive (hT : ∀ v, T v = if v % 2 = 0 then v / 2 else (3 * v + 1) / 2)
    {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < T^[k] n := by
  induction k with
  | zero => exact hn
  | succ k ih =>
    rw [iterate_succ_apply', hT]
    split <;> omega

lemma shortcut_realized (hT : ∀ v, T v = if v % 2 = 0 then v / 2 else (3 * v + 1) / 2)
    (n k : ℕ) : ∃ j : ℕ, collatzStep^[j] n = T^[k] n := by
  have step (y : ℕ) : ∃ d : ℕ, collatzStep^[d] y = T y := by
    by_cases he : y % 2 = 0
    · exact ⟨1, by simp [hT, collatzStep, Nat.even_iff, he]⟩
    · refine ⟨2, ?_⟩
      change collatzStep (collatzStep y) = T y
      have hp : (3 * y + 1) % 2 = 0 := by omega
      simp [hT, collatzStep, Nat.even_iff, he, hp]
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨d, hd⟩ := step (T^[k] n)
    exact ⟨d + j, by rw [iterate_add_apply, hj, iterate_succ_apply', hd]⟩

/-- A lower bound on every input bounds the possible numerator growth. -/
lemma slope_upper (B : ℕ) (x : ℕ → ℕ) (odds : ℕ → Finset ℕ)
    (hx : ∀ i, 2 * x (i + 1) = if x i % 2 = 1 then 3 * x i + 1 else x i)
    (ho : ∀ k, odds k = (range k).filter fun i => x i % 2 = 1)
    (hlow : ∀ i, B ≤ x i) (k : ℕ) :
    (2 ^ k * x k) * B ^ (odds k).card ≤ (3 * B + 1) ^ (odds k).card * x 0 := by
  induction k with
  | zero => simp [ho]
  | succ k ih =>
    have hs := hx k
    rw [pow_succ, Nat.mul_assoc (2 ^ k) 2 (x (k + 1)), odds_succ ho]
    by_cases h : x k % 2 = 1
    · rw [if_pos h] at hs ⊢
      have hnot : k ∉ odds k := fun hmem => (lt_irrefl k) (odds_lt ho hmem)
      rw [hs, card_insert_of_notMem hnot, pow_succ, pow_succ]
      have hloc : (3 * x k + 1) * B ≤ (3 * B + 1) * x k := by nlinarith [hlow k]
      calc
        _ = (2 ^ k * B ^ (odds k).card) * ((3 * x k + 1) * B) := by ring
        _ ≤ (2 ^ k * B ^ (odds k).card) * ((3 * B + 1) * x k) := Nat.mul_le_mul_left _ hloc
        _ = (3 * B + 1) * ((2 ^ k * x k) * B ^ (odds k).card) := by ring
        _ ≤ (3 * B + 1) * ((3 * B + 1) ^ (odds k).card * x 0) := Nat.mul_le_mul_left _ ih
        _ = _ := by ring
    · rw [if_neg h] at hs ⊢
      rwa [hs]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3200000 in
/-- Kernel-checked finite descent for starts from 2 through 2048. -/
lemma small_descent (T : ℕ → ℕ)
    (hT : T = fun n => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2) :
    ∀ r : Fin 2047, ∃ j : Fin 82, T^[j.val] (r.val + 2) < r.val + 2 := by
  subst T
  decide +kernel

set_option maxRecDepth 8000 in
/-- For fewer than 94 odd steps, the first power of two above `3^s`
already exceeds the upper bound for cycles above 2048. -/
lemma short_period_gap : ∀ s : Fin 94,
    6145 ^ s.val < 2 ^ ((3 ^ s.val).log2 + 1) * 2048 ^ s.val := by decide +kernel

lemma no_large_cycle (h2 : H2)
    (hT : ∀ v, T v = if v % 2 = 0 then v / 2 else (3 * v + 1) / 2)
    (y d : ℕ) (hd : 0 < d) (hlow : ∀ i, 2048 < T^[i] y) (hfix : T^[d] y = y) : False := by
  let odds := fun k => (range k).filter fun i => T^[i] y % 2 = 1
  let S := odds d
  have he := affine_identity (x := fun i => T^[i] y) (odds := odds)
    (shortcut_rec hT y) (fun _ => rfl) d
  change 2 ^ d * T^[d] y = 3 ^ S.card * y + _ at he
  rw [hfix] at he
  have hy : 2048 < y := hlow 0
  have hpos : 0 < y := by omega
  have hle : 3 ^ S.card ≤ 2 ^ d := le_of_mul_le_mul_right (by omega : 3 ^ S.card * y ≤ 2 ^ d * y) hpos
  have hlt : 3 ^ S.card < 2 ^ d := by
    have h3 : 3 ^ S.card % 2 = 1 := by rw [Nat.pow_mod]; norm_num
    have h2even : 2 ^ d % 2 = 0 := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
      simp [pow_succ]
    omega
  have hbound := slope_upper 2048 (fun i => T^[i] y) odds (shortcut_rec hT y)
    (fun _ => rfl) (fun i => (hlow i).le) d
  change (2 ^ d * T^[d] y) * 2048 ^ S.card ≤ 6145 ^ S.card * y at hbound
  rw [hfix, mul_right_comm] at hbound
  have hu := le_of_mul_le_mul_right hbound hpos
  have hs : 94 ≤ S.card := by
    by_contra! hfew
    have hgap := short_period_gap ⟨S.card, hfew⟩
    have hlog := (Nat.log2_lt (by positivity : 3 ^ S.card ≠ 0)).mpr hlt
    have hpow : 2 ^ ((3 ^ S.card).log2 + 1) ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) hlog
    exact (not_lt_of_ge hu) (lt_of_lt_of_le hgap (Nat.mul_le_mul_right _ hpow))
  exact (h2 d y S hy (filter_subset _ _) hs hlt hu) he

end Shortcut

theorem main : H1 → H2 → type_of% @Erdos1135.erdos_1135 := by
  intro h1 h2
  let T := fun v : ℕ => if v % 2 = 0 then v / 2 else (3 * v + 1) / 2
  have hT (v : ℕ) : T v = if v % 2 = 0 then v / 2 else (3 * v + 1) / 2 := rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hone : n = 1
    · exact ⟨0, hone⟩
    let x := fun i : ℕ => T^[i] n
    let odds := fun k => (range k).filter fun i => x i % 2 = 1
    have drop : ∃ t, x t < n := by
      by_contra! hstay
      have hnB : 2048 < n := by
        by_contra! hsmall
        let r : Fin 2047 := ⟨n - 2, by omega⟩
        obtain ⟨j, hj⟩ := small_descent T rfl r
        have hr : r.val + 2 = n := by dsimp [r]; omega
        rw [hr] at hj
        exact (not_lt_of_ge (hstay j.val)) hj
      have hres : n % 4 = 3 := by
        by_contra hne
        by_cases he : n % 2 = 0
        · have hbad := hstay 1
          change n ≤ T n at hbad
          rw [hT, if_pos he] at hbad
          omega
        · have he' : ((3 * n + 1) / 2) % 2 = 0 := by omega
          have hbad := hstay 2
          change n ≤ T (T n) at hbad
          simp only [hT, if_neg he, if_pos he'] at hbad
          omega
      let m := (n - 3) / 2
      have hm : n = 2 * m + 3 := by dsimp [m]; omega
      obtain ⟨k, hk⟩ := h1 n hnB hres
      change (n - 2 + 2 * (odds k).card) * (3 ^ (odds k).card) ^ 6 <
        (n - 2) * (2 ^ k) ^ 6 at hk
      have hm' : n - 2 = 2 * m + 1 := by omega
      rw [hm', show 2 * m + 1 + 2 * (odds k).card = 2 * (m + (odds k).card) + 1 by omega] at hk
      have no_repeat {i j : ℕ} (hij : i < j) (heq : x i = x j) : False := by
        have hfix : T^[j - i] (x i) = x i := by
          change T^[j - i] (T^[i] n) = x i
          rw [← iterate_add_apply, Nat.sub_add_cancel hij.le]
          exact heq.symm
        have hlow (t : ℕ) : 2048 < T^[t] (x i) := by
          change 2048 < T^[t] (T^[i] n)
          rw [← iterate_add_apply]
          exact lt_of_lt_of_le hnB (hstay (t + i))
        exact no_large_cycle h2 hT (x i) (j - i) (by omega) hlow hfix
      have hinj : Function.Injective x := by
        intro i j heq
        rcases lt_trichotomy i j with hij | hij | hij
        · exact (no_repeat hij heq).elim
        · exact hij
        · exact (no_repeat hij heq.symm).elim
      have hp := product_identity (x := x) (odds := odds) (shortcut_rec hT n) (fun _ => rfl) k
      exact (not_lt_of_ge (hstay k)) (parity_drop m x k (odds k) hn
        (fun i hi => (mem_filter.mp hi).2) (fun i _ => hm ▸ hstay i) hinj.injOn hp hk)
    obtain ⟨t, ht⟩ := drop
    obtain ⟨a, ha⟩ := shortcut_realized hT n t
    obtain ⟨b, hb⟩ := ih (x t) ht (shortcut_positive hT hn t)
    exact ⟨b + a, by rw [iterate_add_apply, ha]; exact hb⟩

namespace ParityDensity

variable {T : ℕ → ℕ} {oddCount : ℕ → ℕ → ℕ} {hasPrefix : ℕ → Prop}

lemma count_last
    (hcdef : ∀ k n, oddCount k n = ((range k).filter fun i => T^[i] n % 2 = 1).card) (k n : ℕ) : oddCount (k + 1) n = oddCount k n + T^[k] n % 2 := by
  simp only [hcdef, range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem, h]
    exact fun hi => (lt_irrefl k) (mem_range.mp (mem_filter.mp hi).1)
  · rw [show T^[k] n % 2 = 0 by omega, Nat.add_zero]

lemma count_first
    (hcdef : ∀ k n, oddCount k n = ((range k).filter fun i => T^[i] n % 2 = 1).card) (k n : ℕ) : oddCount (k + 1) n = n % 2 + oddCount k (T n) := by
  induction k with
  | zero => rw [count_last hcdef]; simp [hcdef]
  | succ k ih => rw [count_last hcdef, ih, iterate_succ_apply, count_last hcdef k (T n), Nat.add_assoc]

/-- The lift by a multiple of `2^k` preserves the k-step word and changes
the endpoint by an odd multiple of the quotient. -/
lemma lift_word
    (hT : ∀ v, T v = if v % 2 = 0 then v / 2 else (3 * v + 1) / 2)
    (hcdef : ∀ k n, oddCount k n = ((range k).filter fun i => T^[i] n % 2 = 1).card) (k n q : ℕ) :
    oddCount k (2 ^ k * q + n) = oddCount k n ∧
    T^[k] (2 ^ k * q + n) = 3 ^ oddCount k n * q + T^[k] n := by
  have first (v n : ℕ) : T (2 * v + n) = 3 ^ (n % 2) * v + T n := by
    by_cases h : n % 2 = 0
    · simp [hT, Nat.add_mod, h]
      omega
    · have h1 : n % 2 = 1 := by omega
      simp [hT, h1]
      omega
  induction k generalizing n q with
  | zero => simp [hcdef]
  | succ k ih =>
    have hre : 2 ^ (k + 1) * q + n = 2 * (2 ^ k * q) + n := by ring
    have hstep : T (2 ^ (k + 1) * q + n) = 2 ^ k * (3 ^ (n % 2) * q) + T n := by
      rw [hre, first]
      ring
    have hpar : (2 ^ (k + 1) * q + n) % 2 = n % 2 := by rw [hre]; omega
    obtain ⟨hc, hv⟩ := ih (T n) (3 ^ (n % 2) * q)
    constructor
    · rw [count_first hcdef, count_first hcdef k n, hpar, hstep, hc]
    · rw [iterate_succ_apply, hstep, hv, iterate_succ_apply T k n, count_first hcdef, pow_add]
      ring

lemma lift_mass
    (hT : ∀ v, T v = if v % 2 = 0 then v / 2 else (3 * v + 1) / 2)
    (hcdef : ∀ k n, oddCount k n = ((range k).filter fun i => T^[i] n % 2 = 1).card) (k n : ℕ) :
    2 ^ oddCount (k + 1) n + 2 ^ oddCount (k + 1) (2 ^ k + n) = 3 * 2 ^ oddCount k n := by
  obtain ⟨hc, hv⟩ := lift_word hT hcdef k n 1
  simp only [mul_one] at hc hv
  rw [count_last hcdef, count_last hcdef, hc, hv, pow_add, pow_add]
  have hodd : 3 ^ oddCount k n % 2 = 1 := by rw [Nat.pow_mod]; norm_num
  rcases Nat.mod_two_eq_zero_or_one (T^[k] n) with h | h
  · rw [show (3 ^ oddCount k n + T^[k] n) % 2 = 1 by omega, h]; ring
  · rw [show (3 ^ oddCount k n + T^[k] n) % 2 = 0 by omega, h]; ring

/-- The exact sum of the parity weights over a complete residue system. -/
lemma parity_mass
    (hT : ∀ v, T v = if v % 2 = 0 then v / 2 else (3 * v + 1) / 2)
    (hcdef : ∀ k n, oddCount k n = ((range k).filter fun i => T^[i] n % 2 = 1).card) (k : ℕ) : (∑ n ∈ range (2 ^ k), 2 ^ oddCount k n) = 3 ^ k := by
  induction k with
  | zero => simp [hcdef]
  | succ k ih =>
    rw [pow_succ (2 : ℕ), Nat.mul_two, sum_range_add, ← sum_add_distrib]
    calc
      _ = ∑ n ∈ range (2 ^ k), 3 * 2 ^ oddCount k n := sum_congr rfl (fun i _ => lift_mass hT hcdef k i)
      _ = _ := by rw [← mul_sum, ih, pow_succ]; ring

/-- Eight steps with at most five odds per block on average give the strict
parity inequality. Only the total number of odds across the blocks matters. -/
lemma five_eighths (D r s : ℕ) (hD : 32 ≤ D) (hr : 0 < r) (hs : s ≤ 5 * r) :
    (D + 2 * s) * (3 ^ s) ^ 6 < D * (2 ^ (8 * r)) ^ 6 := by
  let A : ℕ := (3 ^ 5) ^ 6
  let B : ℕ := (2 ^ 8) ^ 6
  have block (v : ℕ) (hv : 32 ≤ v) : (v + 10) * A < v * B := by norm_num [A, B]; omega
  have one (t : ℕ) (h : (D + 10 * t) * A ^ t ≤ D * B ^ t) :
      (D + 10 * (t + 1)) * A ^ (t + 1) < D * B ^ (t + 1) := by
    have hg := block (D + 10 * t) (by omega)
    calc
      _ = ((D + 10 * t) + 10) * A * A ^ t := by ring
      _ < ((D + 10 * t) * B) * A ^ t := Nat.mul_lt_mul_of_pos_right hg (by dsimp [A]; positivity)
      _ = ((D + 10 * t) * A ^ t) * B := by ring
      _ ≤ (D * B ^ t) * B := Nat.mul_le_mul_right B h
      _ = _ := by ring
  have weak (t : ℕ) : (D + 10 * t) * A ^ t ≤ D * B ^ t := by
    induction t with
    | zero => simp
    | succ t ih => exact (one t ih).le
  have strict : (D + 10 * r) * A ^ r < D * B ^ r := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    exact one t (weak t)
  have switch (a b t : ℕ) : (a ^ (b * t)) ^ 6 = ((a ^ b) ^ 6) ^ t := by
    simp only [← pow_mul, Nat.mul_right_comm b t 6]
  have hAp : (3 ^ (5 * r)) ^ 6 = A ^ r := switch 3 5 r
  have hBp : (2 ^ (8 * r)) ^ 6 = B ^ r := switch 2 8 r
  rw [hBp]
  apply lt_of_le_of_lt _ strict
  rw [← hAp]
  exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) hs) _)

/-- Outside these sparse classes, a single window of length `8*r` witnesses
R2.H1. This bounds every simultaneous exception, uniformly in the length. -/
theorem exceptional_classes
    (hT : ∀ v, T v = if v % 2 = 0 then v / 2 else (3 * v + 1) / 2)
    (hcdef : ∀ k n, oddCount k n = ((range k).filter fun i => T^[i] n % 2 = 1).card)
    (hP : ∀ n, hasPrefix n ↔ ∃ k : ℕ,
      (n - 2 + 2 * oddCount k n) * (3 ^ oddCount k n) ^ 6 < (n - 2) * (2 ^ k) ^ 6) (r : ℕ) (hr : 0 < r) :
    ∃ bad : Finset ℕ, bad ⊆ range (2 ^ (8 * r)) ∧
      2 ^ (5 * r + 1) * bad.card ≤ 3 ^ (8 * r) ∧
      ∀ n : ℕ, 2048 < n → ¬ hasPrefix n → n % (2 ^ (8 * r)) ∈ bad := by
  let k := 8 * r
  let bad := (range (2 ^ k)).filter fun n => 5 * r < oddCount k n
  have hsub : bad ⊆ range (2 ^ k) := filter_subset _ _
  refine ⟨bad, hsub, ?_, ?_⟩
  · calc
      2 ^ (5 * r + 1) * bad.card = ∑ _i ∈ bad, 2 ^ (5 * r + 1) := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ bad, 2 ^ oddCount k i := by
        apply sum_le_sum
        intro i hi
        exact Nat.pow_le_pow_right (by decide) (mem_filter.mp hi).2
      _ ≤ ∑ i ∈ range (2 ^ k), 2 ^ oddCount k i := sum_le_sum_of_subset_of_nonneg hsub (by simp)
      _ = _ := parity_mass hT hcdef k
  · intro n hn hfail
    have hcount : oddCount k (n % (2 ^ k)) = oddCount k n := by
      have h := (lift_word hT hcdef k (n % (2 ^ k)) (n / (2 ^ k))).1
      rw [Nat.div_add_mod] at h
      exact h.symm
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (Nat.mod_lt _ (by positivity)), ?_⟩
    rw [hcount]
    by_contra! hfew
    exact hfail ((hP n).mpr ⟨k, five_eighths (n - 2) r (oddCount k n) (by omega) hr hfew⟩)

/-- Each exceptional starting value is determined by its quotient and its
residue in the covering. -/
lemma initial_segment_bound
    (cover : ∀ r : ℕ, 0 < r → ∃ bad : Finset ℕ, bad ⊆ range (2 ^ (8 * r)) ∧
      2 ^ (5 * r + 1) * bad.card ≤ 3 ^ (8 * r) ∧
      ∀ n : ℕ, 2048 < n → ¬ hasPrefix n → n % (2 ^ (8 * r)) ∈ bad) (r N : ℕ) (hr : 0 < r) (E : Finset ℕ)
    (hE : ∀ n ∈ E, n < N ∧ 2048 < n ∧ ¬ hasPrefix n) :
    2 ^ (5 * r + 1) * E.card ≤ (N / (2 ^ (8 * r)) + 1) * 3 ^ (8 * r) := by
  obtain ⟨bad, _, hcount, hcover⟩ := cover r hr
  let M := 2 ^ (8 * r)
  let f := fun n : ℕ => (n / M, n % M)
  have hmap : Set.MapsTo f E ((range (N / M + 1)) ×ˢ bad : Finset (ℕ × ℕ)) := by
    intro n hn
    obtain ⟨hlt, hlarge, hfail⟩ := hE n hn
    apply mem_product.mpr
    exact ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hlt.le)), hcover n hlarge hfail⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hq : a / M = b / M := congrArg Prod.fst hab
    have hr' : a % M = b % M := congrArg Prod.snd hab
    calc a = M * (a / M) + a % M := (Nat.div_add_mod a M).symm
         _ = b := by rw [hq, hr', Nat.div_add_mod]
  have he := card_le_card_of_injOn f hmap hinj.injOn
  rw [card_product, card_range] at he
  calc
    _ ≤ 2 ^ (5 * r + 1) * ((N / M + 1) * bad.card) := Nat.mul_le_mul_left _ he
    _ = (N / M + 1) * (2 ^ (5 * r + 1) * bad.card) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hcount

/-- Upper natural density zero, with an explicit threshold for each reciprocal
tolerance `1/d`. This assertion still allows individual exceptional integers. -/
lemma density_from_cover
    (cover : ∀ r : ℕ, 0 < r → ∃ bad : Finset ℕ, bad ⊆ range (2 ^ (8 * r)) ∧
      2 ^ (5 * r + 1) * bad.card ≤ 3 ^ (8 * r) ∧
      ∀ n : ℕ, 2048 < n → ¬ hasPrefix n → n % (2 ^ (8 * r)) ∈ bad) (d N : ℕ) (hd : 0 < d) (hN : 2 ^ (40 * d) ≤ N)
    (E : Finset ℕ) (hE : ∀ n ∈ E, n < N ∧ 2048 < n ∧ ¬ hasPrefix n) : d * E.card ≤ N := by
  let r := 5 * d
  let M := 2 ^ (8 * r)
  have hr : 0 < r := by dsimp [r]; omega
  have hm : 0 < M := by dsimp [M]; positivity
  have hmn : M ≤ N := by simpa only [M, r, ← Nat.mul_assoc] using hN
  have hbudget (t : ℕ) : (t + 5) * 6561 ^ t ≤ 5 * 8192 ^ t := by
    induction t with
    | zero => simp
    | succ t ih =>
      calc
        _ = ((t + 6) * 6561) * 6561 ^ t := by ring
        _ ≤ ((t + 5) * 8192) * 6561 ^ t := Nat.mul_le_mul_right _ (by omega)
        _ = ((t + 5) * 6561 ^ t) * 8192 := by ring
        _ ≤ (5 * 8192 ^ t) * 8192 := Nat.mul_le_mul_right _ ih
        _ = _ := by ring
  have hratio : d * 6561 ^ r ≤ 8192 ^ r := by
    have h := hbudget r
    have he : (r + 5) * 6561 ^ r = 5 * (d * 6561 ^ r) + 5 * 6561 ^ r := by dsimp [r]; ring
    rw [he] at h
    omega
  have hratio' : d * 3 ^ (8 * r) ≤ 2 ^ (5 * r) * M := by
    change d * 3 ^ (8 * r) ≤ 2 ^ (5 * r) * 2 ^ (8 * r)
    rw [← pow_add, show 5 * r + 8 * r = 13 * r by omega, pow_mul (3 : ℕ) 8 r, pow_mul (2 : ℕ) 13 r]
    exact hratio
  have hi := initial_segment_bound cover r N hr E hE
  change 2 ^ (5 * r + 1) * E.card ≤ (N / M + 1) * 3 ^ (8 * r) at hi
  have hblocks : M * (N / M + 1) ≤ 2 * N := by
    rw [Nat.mul_add, Nat.mul_one]
    have hdiv := Nat.div_add_mod N M
    omega
  have hpos : 0 < 2 * (2 ^ (5 * r) * M) := by positivity
  apply le_of_mul_le_mul_left _ hpos
  calc
    (2 * (2 ^ (5 * r) * M)) * (d * E.card) = (d * M) * (2 ^ (5 * r + 1) * E.card) := by ring
    _ ≤ (d * M) * ((N / M + 1) * 3 ^ (8 * r)) := Nat.mul_le_mul_left _ hi
    _ = (M * (N / M + 1)) * (d * 3 ^ (8 * r)) := by ring
    _ ≤ (2 * N) * (2 ^ (5 * r) * M) := Nat.mul_le_mul hblocks hratio'
    _ = _ := by ring

end ParityDensity

/-- The set of possible exceptions to H1 has upper natural density zero.
For each positive `d`, at most `N/d` starters below `N` can fail the test
as soon as `2^(40*d) ≤ N`. The bound also covers starters outside `3 mod 4`. -/
theorem parity_exceptions_density_zero (d N : ℕ) (hd : 0 < d) (hN : 2 ^ (40 * d) ≤ N)
    (E : Finset ℕ) (hE : let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
      ∀ n ∈ E, n < N ∧ 2048 < n ∧ ¬ ∃ k : ℕ,
        let s := ((range k).filter fun i => T^[i] n % 2 = 1).card
        (n - 2 + 2 * s) * (3 ^ s) ^ 6 < (n - 2) * (2 ^ k) ^ 6) : d * E.card ≤ N := by
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  let c := fun k n : ℕ => ((range k).filter fun i => T^[i] n % 2 = 1).card
  let P := fun n : ℕ => ∃ k : ℕ,
    (n - 2 + 2 * c k n) * (3 ^ c k n) ^ 6 < (n - 2) * (2 ^ k) ^ 6
  exact ParityDensity.density_from_cover (hasPrefix := P)
    (ParityDensity.exceptional_classes (T := T) (oddCount := c) (fun _ => rfl)
      (fun _ _ => rfl) (fun _ => Iff.rfl)) d N hd hN E hE

end OMA.R_Erdos1135_erdos_1135_R2
