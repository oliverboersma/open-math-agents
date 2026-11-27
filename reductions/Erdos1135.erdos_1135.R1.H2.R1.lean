import OMAReductions.R_Erdos1135_erdos_1135_R1

/-!
The first strict coefficient crossing splits the descent problem for the
nineteen residue classes in the parent step. The first hypothesis asks for
a crossing on unbounded orbits. Bounded orbits cross by a proved finite-window
estimate. The second concerns the subsequent orbit only when the seed is
above 860179, the crossing occurs after 4096 steps, and its failure to
descend satisfies two necessary integer bounds. Both hypotheses follow
from the parent step, as shown in `necessary`.

The coefficient stopping time is due to Terras. The height estimate follows
by tracking the additive error at every odd step before the first crossing.
Credit: @ubuwaits.
-/

namespace OMA.R_Erdos1135_erdos_1135_R1_H2_R1

open CollatzConjecture Function Finset

/-- Existence of a finite coefficient stopping time for the remaining unbounded orbits. -/
def H1 : Prop :=
  let T := fun v : ℕ => if v % 2 = 0 then v / 2 else (3 * v + 1) / 2
  ∀ n : ℕ, 860179 < n → n % 9 = 5 →
    n % 256 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167,
      191, 207, 223, 231, 239, 251, 255] : List ℕ) →
    (∀ B : ℕ, ∃ i : ℕ, B < T^[i] n) →
    ∃ k : ℕ, 3 ^ ((range k).filter fun i => T^[i] n % 2 = 1).card < 2 ^ k

/-- Recovery from a late first crossing that has left the endpoint at or above
the seed. Both displayed bounds restrict possible instances. -/
def H2 : Prop :=
  let T := fun v : ℕ => if v % 2 = 0 then v / 2 else (3 * v + 1) / 2
  ∀ n k : ℕ, 860179 < n → n % 9 = 5 →
    n % 256 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167,
      191, 207, 223, 231, 239, 251, 255] : List ℕ) →
    let s := fun j : ℕ => ((range j).filter fun i => T^[i] n % 2 = 1).card
    4096 < k → 3 ^ s k < 2 ^ k → (∀ i < k, 2 ^ i ≤ 3 ^ s i) →
    n ≤ T^[k] n → 3 * (2 ^ k - 3 ^ s k) * n ≤ s k * 3 ^ s k →
    3 * (T^[k] n - n) < s k → ∃ j : ℕ, T^[j] (T^[k] n) < n

lemma count_next (x : ℕ → ℕ) (k : ℕ) :
    ((range (k + 1)).filter fun i => x i % 2 = 1).card =
      ((range k).filter fun i => x i % 2 = 1).card + x k % 2 := by
  simp only [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem, h]
    exact fun hi => (lt_irrefl k) (mem_range.mp (mem_filter.mp hi).1)
  · rw [show x k % 2 = 0 by omega, Nat.add_zero]

lemma double_step (T : ℕ → ℕ)
    (hT : ∀ v, T v = if v % 2 = 0 then v / 2 else (3 * v + 1) / 2) (n k : ℕ) :
    2 * T^[k + 1] n = if T^[k] n % 2 = 1 then 3 * T^[k] n + 1 else T^[k] n := by
  rw [iterate_succ_apply', hT]
  split_ifs <;> omega

section Coefficient

variable {x s : ℕ → ℕ}
  (hzero : s 0 = 0) (hs : ∀ k, s (k + 1) = s k + x k % 2)
  (hx : ∀ k, 2 * x (k + 1) = if x k % 2 = 1 then 3 * x k + 1 else x k)

include hzero hs hx

lemma coefficient_lower (k : ℕ) : 3 ^ s k * x 0 ≤ 2 ^ k * x k := by
  induction k with
  | zero => simp [hzero]
  | succ k ih =>
    rw [pow_succ (2 : ℕ), Nat.mul_assoc, hx, hs]
    rcases Nat.mod_two_eq_zero_or_one (x k) with h | h
    · simpa [h] using ih
    · rw [h, if_pos rfl, pow_succ]
      calc
        _ = 3 * (3 ^ s k * x 0) := by ring
        _ ≤ 3 * (2 ^ k * x k) := Nat.mul_le_mul_left _ ih
        _ = 2 ^ k * (3 * x k) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_succ _)

/-- Every odd step contributes at most one third after normalizing by its
multiplier, since every earlier coefficient was at least one. -/
lemma correction (k : ℕ) (hprior : ∀ i < k, 2 ^ i ≤ 3 ^ s i) :
    3 * (2 ^ k * x k) ≤ 3 ^ s k * (3 * x 0 + s k) := by
  induction k with
  | zero => simp [hzero]
  | succ k ih =>
    have h := ih (fun i hi => hprior i (by omega))
    have hk := hprior k (by omega)
    rw [pow_succ (2 : ℕ), Nat.mul_assoc (2 ^ k) 2, hx, hs]
    rcases Nat.mod_two_eq_zero_or_one (x k) with hp | hp
    · simpa [hp] using h
    · rw [hp, if_pos rfl, pow_succ]
      nlinarith [h, hk]

lemma crossing_bounds (k : ℕ) (hpos : 0 < x 0) (hc : 3 ^ s k < 2 ^ k)
    (hprior : ∀ i < k, 2 ^ i ≤ 3 ^ s i) (hstay : x 0 ≤ x k) :
    3 * (2 ^ k - 3 ^ s k) * x 0 ≤ s k * 3 ^ s k ∧ 3 * (x k - x 0) < s k := by
  have hu := correction hzero hs hx k hprior
  constructor
  · have hscaled := Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left (2 ^ k) hstay)
    have heq := Nat.sub_add_cancel hc.le
    nlinarith only [hu, hscaled, congrArg (fun v : ℕ => 3 * v * x 0) heq]
  · have hstrict := Nat.mul_lt_mul_of_pos_right hc (show 0 < 3 * x 0 + s k by omega)
    have hX : 2 ^ k * (3 * x k) < 2 ^ k * (3 * x 0 + s k) := by nlinarith only [hu, hstrict]
    have hsmall := Nat.lt_of_mul_lt_mul_left hX
    omega

/-- When all earlier values stay within a fixed bound, each odd step also
contributes a lower bound to the additive error. -/
lemma lower_correction (B k : ℕ) (hpos : 0 < x 0) (hbound : ∀ i < k, x i ≤ B) :
    3 * B * (2 ^ k * x k) ≥ 3 ^ s k * (3 * B * x 0 + s k) := by
  induction k with
  | zero => simp [hzero, Nat.mul_assoc]
  | succ k ih =>
    have h := ih (fun i hi => hbound i (by omega))
    have hslope : 3 ^ s k ≤ 2 ^ k * B := calc
      _ ≤ 3 ^ s k * x 0 := Nat.le_mul_of_pos_right _ hpos
      _ ≤ 2 ^ k * x k := coefficient_lower hzero hs hx k
      _ ≤ _ := Nat.mul_le_mul_left _ (hbound k (by omega))
    rw [pow_succ (2 : ℕ), Nat.mul_assoc (2 ^ k) 2, hx, hs]
    rcases Nat.mod_two_eq_zero_or_one (x k) with hp | hp
    · simpa [hp] using h
    · rw [hp, if_pos rfl, pow_succ]
      nlinarith only [h, hslope]

/-- A positive orbit confined below B through step 6*B²+1 already has a
coefficient strictly below one at that step. This includes periodic orbits. -/
lemma bounded_window_crossing (B : ℕ) (hpos : 0 < x 0)
    (hbound : ∀ i ≤ 2 * (3 * B * B) + 1, x i ≤ B) :
    3 ^ s (2 * (3 * B * B) + 1) < 2 ^ (2 * (3 * B * B) + 1) := by
  let k := 2 * (3 * B * B) + 1
  change 3 ^ s k < 2 ^ k
  by_contra! hstay
  have hlow := lower_correction hzero hs hx B k hpos (fun i hi => hbound i hi.le)
  have hcomp := (Nat.mul_le_mul_right (3 * B * x 0 + s k) hstay).trans hlow
  have hxk := hbound k le_rfl
  have hcut : 2 ^ k * (3 * B * x 0 + s k) ≤ 2 ^ k * (3 * B * B) := by
    calc
      _ ≤ 3 * B * (2 ^ k * x k) := hcomp
      _ = 2 ^ k * (3 * B * x k) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hxk)
  have hsB := le_of_mul_le_mul_left hcut (by positivity : 0 < 2 ^ k)
  have hpow : 2 ^ k ≤ 2 ^ (2 * s k) := hstay.trans (by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by decide) _)
  have hk := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  omega

end Coefficient

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3200000 in
lemma gap_table : ∀ s : Fin 2585,
    s.val * 3 ^ s.val < 3 * (2 ^ ((3 ^ s.val).log2 + 1) - 3 ^ s.val) * 860180 := by decide +kernel

set_option maxRecDepth 32000 in
lemma late_crossing {s n k : ℕ} (hn : 860179 < n) (hc : 3 ^ s < 2 ^ k)
    (hb : 3 * (2 ^ k - 3 ^ s) * n ≤ s * 3 ^ s) : 4096 < k := by
  by_contra! hk
  have hs : s < 2585 := by
    by_contra! hs
    have p := Nat.pow_le_pow_right (show 0 < 3 by decide) hs
    have q := Nat.pow_le_pow_right (show 0 < 2 by decide) hk
    have hnum : (2 : ℕ) ^ 4096 ≤ 3 ^ 2585 := calc
      _ = (2 ^ 84) ^ 48 * 2 ^ 64 := by rw [← pow_mul, ← pow_add]
      _ ≤ (3 ^ 53) ^ 48 * 3 ^ 41 := Nat.mul_le_mul
        (Nat.pow_le_pow_left (by decide : (2 : ℕ) ^ 84 ≤ 3 ^ 53) 48) (by decide)
      _ = _ := by rw [← pow_mul, ← pow_add]
    apply (not_lt_of_ge ?_) hc
    calc
      2 ^ k ≤ 2 ^ 4096 := q
      _ ≤ 3 ^ 2585 := hnum
      _ ≤ 3 ^ s := p
  have hlo : (3 ^ s).log2 + 1 ≤ k := (Nat.log2_lt (by positivity : 3 ^ s ≠ 0)).mpr hc
  have hpow := Nat.pow_le_pow_right (show 0 < 2 by decide) hlo
  have hg := gap_table ⟨s, hs⟩
  change s * 3 ^ s < 3 * (2 ^ ((3 ^ s).log2 + 1) - 3 ^ s) * 860180 at hg
  have hm : 3 * (2 ^ ((3 ^ s).log2 + 1) - 3 ^ s) * 860180 ≤ 3 * (2 ^ k - 3 ^ s) * n :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  exact (not_lt_of_ge hb) (hg.trans_le hm)

set_option maxRecDepth 16000 in
lemma residue_table : ∀ r : Fin 2304, r.val % 9 = 5 →
    r.val % 256 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167,
      191, 207, 223, 231, 239, 251, 255] : List ℕ) →
    r.val ∈ ([167, 239, 347, 383, 671, 743, 815, 923, 959, 1247, 1391, 1535,
      1607, 1787, 1823, 1895, 2075, 2111, 2255] : List ℕ) := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3200000 in
/-- Check 374 rows of nineteen seeds and extract an actual strict descent. -/
lemma small_descent (n : ℕ) (hn : n ≤ 860179) (h9 : n % 9 = 5)
    (h256 : n % 256 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167,
      191, 207, 223, 231, 239, 251, 255] : List ℕ)) : ∃ t, collatzStep^[t] n < n := by
  let T := fun v : ℕ => if v % 2 = 0 then v / 2 else (3 * v + 1) / 2
  let scan : ℕ → ℕ → ℕ → Bool := Nat.rec (motive := fun _ => ℕ → ℕ → Bool)
    (fun a x => decide (x < a)) (fun _ prev a x => if x < a then true else prev a (T x))
  have sound (fuel a x : ℕ) (hh : scan fuel a x = true) : ∃ j, T^[j] x < a := by
    induction fuel generalizing x with
    | zero => exact ⟨0, of_decide_eq_true hh⟩
    | succ fuel ih =>
      by_cases h : x < a
      · exact ⟨0, h⟩
      · change (if x < a then true else scan fuel a (T x)) = true at hh
        rw [if_neg h] at hh
        obtain ⟨j, hj⟩ := ih (T x) hh
        exact ⟨j + 1, by rwa [iterate_succ_apply]⟩
  let residues : List ℕ := [167, 239, 347, 383, 671, 743, 815, 923, 959, 1247, 1391,
    1535, 1607, 1787, 1823, 1895, 2075, 2111, 2255]
  have table : ∀ q : Fin 374, residues.all (fun r =>
      let a := 2304 * q.val + r
      scan 165 a a) = true := by
    dsimp only [residues, scan, T]
    decide +kernel
  let r : Fin 2304 := ⟨n % 2304, Nat.mod_lt _ (by decide)⟩
  have h9' : r.val % 9 = n % 9 := Nat.mod_mod_of_dvd n (by decide)
  have h256' : r.val % 256 = n % 256 := Nat.mod_mod_of_dvd n (by decide)
  have hr := residue_table r (h9'.trans h9) (h256' ▸ h256)
  let q : Fin 374 := ⟨n / 2304, by omega⟩
  have checked := List.all_eq_true.mp (table q) r.val hr
  change scan 165 (2304 * q.val + r.val) (2304 * q.val + r.val) = true at checked
  rw [show 2304 * q.val + r.val = n from Nat.div_add_mod n 2304] at checked
  obtain ⟨j, hj⟩ := sound 165 n n checked
  obtain ⟨t, ht⟩ := OMA.R_Erdos1135_erdos_1135_R1.accelerated_iterate T (fun _ => rfl) n j
  exact ⟨t, ht ▸ hj⟩

theorem main : H1 → H2 → OMA.R_Erdos1135_erdos_1135_R1.H2 := by
  intro findCross recover n hn h9 h256
  by_cases hsmall : n ≤ 860179
  · exact small_descent n hsmall h9 h256
  let T := fun v : ℕ => if v % 2 = 0 then v / 2 else (3 * v + 1) / 2
  let x := fun i : ℕ => T^[i] n
  let s := fun j : ℕ => ((range j).filter fun i => x i % 2 = 1).card
  have hlarge : 860179 < n := by omega
  have hex : ∃ k : ℕ, 3 ^ s k < 2 ^ k := by
    by_cases hu : ∀ B : ℕ, ∃ i : ℕ, B < x i
    · exact findCross n hlarge h9 h256 hu
    · push Not at hu
      obtain ⟨B, hb⟩ := hu
      exact ⟨_, bounded_window_crossing (x := x) (s := s) (by simp [s]) (count_next x)
        (double_step T (fun _ => rfl) n) B (show 0 < n by omega) (fun i _ => hb i)⟩
  let k := Nat.find hex
  have hc : 3 ^ s k < 2 ^ k := Nat.find_spec hex
  have hprior (i : ℕ) (hi : i < k) : 2 ^ i ≤ 3 ^ s i := le_of_not_gt (Nat.find_min hex hi)
  have hhit : ∃ j, T^[j] n < n := by
    by_cases hdrop : T^[k] n < n
    · exact ⟨k, hdrop⟩
    have hb := crossing_bounds (x := x) (s := s) (by simp [s]) (count_next x)
      (double_step T (fun _ => rfl) n) k (show 0 < n by omega) hc hprior (le_of_not_gt hdrop)
    obtain ⟨j, hj⟩ := recover n k hlarge h9 h256 (late_crossing hlarge hc hb.1)
      hc hprior (le_of_not_gt hdrop) hb.1 hb.2
    exact ⟨j + k, by simpa [iterate_add_apply, T] using hj⟩
  obtain ⟨j, hj⟩ := hhit
  obtain ⟨t, ht⟩ := OMA.R_Erdos1135_erdos_1135_R1.accelerated_iterate T (fun _ => rfl) n j
  exact ⟨t, ht ▸ hj⟩

/-- Each ordinary iterate is a shortcut iterate or the larger intermediate
term introduced by an odd step. -/
lemma ordinary_shadow (T : ℕ → ℕ)
    (hT : ∀ v, T v = if v % 2 = 0 then v / 2 else (3 * v + 1) / 2) (n t : ℕ) :
    ∃ j, collatzStep^[t] n = T^[j] n ∨
      (T^[j] n % 2 = 1 ∧ collatzStep^[t] n = 3 * T^[j] n + 1) := by
  induction t with
  | zero => exact ⟨0, Or.inl rfl⟩
  | succ t ih =>
    obtain ⟨j, h | ⟨hp, h⟩⟩ := ih
    · rw [iterate_succ_apply', h]
      by_cases he : T^[j] n % 2 = 0
      · exact ⟨j + 1, Or.inl (by rw [iterate_succ_apply', hT, collatzStep]; simp [Nat.even_iff, he])⟩
      · exact ⟨j, Or.inr ⟨by omega, by simp [collatzStep, Nat.even_iff, he]⟩⟩
    · refine ⟨j + 1, Or.inl ?_⟩
      rw [iterate_succ_apply', h, iterate_succ_apply', hT, collatzStep]
      simp [Nat.even_iff, hp, show (3 * T^[j] n + 1) % 2 = 0 by omega]

lemma ordinary_implies_short (T : ℕ → ℕ)
    (hT : ∀ v, T v = if v % 2 = 0 then v / 2 else (3 * v + 1) / 2) (n : ℕ)
    (h : ∃ t, collatzStep^[t] n < n) : ∃ j, T^[j] n < n := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨j, he | ⟨_, he⟩⟩ := ordinary_shadow T hT n t
  · exact ⟨j, he ▸ ht⟩
  · exact ⟨j, by omega⟩

/-- Neither part of the split imposes a stronger conjecture on the seed. -/
theorem necessary (original : OMA.R_Erdos1135_erdos_1135_R1.H2) : H1 ∧ H2 := by
  let T := fun v : ℕ => if v % 2 = 0 then v / 2 else (3 * v + 1) / 2
  have lower (n j : ℕ) : 3 ^ ((range j).filter fun i => T^[i] n % 2 = 1).card * n ≤
      2 ^ j * T^[j] n :=
    coefficient_lower (x := fun i => T^[i] n)
      (s := fun k => ((range k).filter fun i => T^[i] n % 2 = 1).card)
      (by simp) (count_next _) (double_step T (fun _ => rfl) n) j
  have crossOfDrop (n j : ℕ) (hj : T^[j] n < n) :
      3 ^ ((range j).filter fun i => T^[i] n % 2 = 1).card < 2 ^ j := by
    have h := (lower n j).trans_lt (Nat.mul_lt_mul_of_pos_left hj (by positivity : 0 < 2 ^ j))
    exact Nat.lt_of_mul_lt_mul_right h
  constructor
  · intro n hn h9 h256 _
    obtain ⟨j, hj⟩ := ordinary_implies_short T (fun _ => rfl) n (original n (by omega) h9 h256)
    exact ⟨j, crossOfDrop n j hj⟩
  · intro n k hn h9 h256 s _ _ hprior _ _ _
    obtain ⟨j, hj⟩ := ordinary_implies_short T (fun _ => rfl) n (original n (by omega) h9 h256)
    have hk : k ≤ j := by
      by_contra! he
      exact (not_lt_of_ge (hprior j he)) (crossOfDrop n j hj)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
    exact ⟨d, by rw [hd, Nat.add_comm k d, iterate_add_apply] at hj; exact hj⟩

end OMA.R_Erdos1135_erdos_1135_R1_H2_R1
