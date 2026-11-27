import OMAStatements.S_oeis_a293452

open OMA.S_oeis_a293452

/-- At width two the only nonsink fires once, sending both horizontal grains to the sink. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a293452.main) := by
  intro h
  have hrun : completes (initial 2) [1] := by
    change (1 : Fin 2).val ≠ 0 ∧ 4 ≤ initial 2 1 ∧ ∀ j, topple (initial 2) 1 j < 4
    decide
  have hformula := (h 2 (by decide) 1).mp ⟨[1], hrun, rfl⟩
  exact (by decide : 1 ≠ rectangleSum 2) hformula

open OMA.S_oeis_a293452

namespace Sandpile

private def finalHeight (n i : ℕ) : ℤ := if 2*i = n then 2 else 3

/-- The residual `r i` is the number of firings still owed at site `i`. -/
private structure Balance {n : ℕ} (c : Heights n) (r : ℕ → ℕ) : Prop where
  left : r 0 = 0
  right : r n = 0
  sink : ∀ j : Fin n, j.val = 0 → c j = 0
  interior : ∀ j : Fin n, 0 < j.val → (c j : ℤ) = finalHeight n j.val +
    2 * r j.val - r (j.val - 1) - r (j.val + 1)

private lemma rightEdge {n i j : ℕ} (hi : i < n) (hj : 0 < j) (hjn : j < n) :
    j = (i + 1) % n ↔ j - 1 = i := by
  by_cases h : i + 1 < n
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [show i + 1 = n by omega, Nat.mod_self]; omega

private lemma leftEdge {n i j : ℕ} (hi : 0 < i) (hin : i < n) :
    j = (i + n - 1) % n ↔ j + 1 = i := by
  rw [show i + n - 1 = i - 1 + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  omega

private def fire (r : ℕ → ℕ) (i j : ℕ) := if j = i then r j - 1 else r j

private lemma balance_fire {n : ℕ} {c : Heights n} {r : ℕ → ℕ} (h : Balance c r)
    (i : Fin n) (hi : i.val ≠ 0) (hc : 4 ≤ c i) :
    0 < r i.val ∧ Balance (topple c i) (fire r i.val) := by
  have hi' : 0 < i.val := Nat.pos_of_ne_zero hi
  have hh := h.interior i hi'
  have hpos : 0 < r i.val := by
    unfold finalHeight at hh
    split at hh <;> omega
  refine ⟨hpos, ?_⟩
  have hremove (j : ℕ) : ((fire r i.val j : ℕ) : ℤ) = (r j : ℤ) - (if j = i.val then 1 else 0) := by
    by_cases hji : j = i.val
    · subst j; simp [fire, Nat.cast_sub hpos]
    · simp [fire, hji]
  refine ⟨by simp [fire, Ne.symm hi, h.left], by simp [fire, Nat.ne_of_gt i.isLt, h.right],
    fun j hj => by simp [topple, hj], ?_⟩
  intro j hj
  have hself : ((if j = i then c j - 2 else c j : ℕ) : ℤ) = (c j : ℤ) -
      2 * (if j.val = i.val then 1 else 0) := by
    by_cases heq : j = i
    · subst j; simp [Nat.cast_sub (by omega : 2 ≤ c i)]
    · simp [heq, show j.val ≠ i.val from fun h => heq (Fin.ext h)]
  simp only [topple, if_neg (Nat.ne_of_gt hj), Nat.cast_add, hself,
    rightEdge i.isLt hj j.isLt, leftEdge hi' i.isLt, hremove]
  push_cast
  rw [h.interior j hj]
  ring

private def mass (n : ℕ) (r : ℕ → ℕ) := ∑ i : Fin n, r i.val

private lemma mass_fire {n : ℕ} {r : ℕ → ℕ} (i : Fin n) (h : 0 < r i.val) :
    mass n (fire r i.val) + 1 = mass n r := by
  have key (j : Fin n) : fire r i.val j.val + (if j = i then 1 else 0) = r j.val := by
    by_cases heq : j = i
    · subst j; simp [fire]; omega
    · simp [fire, heq, show j.val ≠ i.val from fun h => heq (Fin.ext h)]
  unfold mass
  conv_rhs => enter [2, i]; rw [← key i]
  simp [Finset.sum_add_distrib]

private theorem stable_mass {n : ℕ} {c : Heights n} {r : ℕ → ℕ} (h : Balance c r)
    (hs : ∀ j, c j < 4) : mass n r = 0 := by
  classical
  by_contra hmass
  have hw : ∃ j : Fin n, r j.val ≠ 0 := by
    by_contra! hn
    exact hmass (by simp [mass, hn])
  obtain ⟨w, hw⟩ := hw
  obtain ⟨a, ha, htop⟩ := (Finset.Icc 0 n).exists_max_image r ⟨0, by simp⟩
  have bound (k : ℕ) (hk : k ≤ n) : r k ≤ r a := htop k (by simpa using hk)
  have hpositive : 0 < r a := by have := bound w.val w.isLt.le; omega
  let peaks := (Finset.Icc 0 n).filter fun k => r k = r a
  have hne : peaks.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  let l := peaks.min' hne
  let u := peaks.max' hne
  have leftMem : l ∈ peaks := peaks.min'_mem hne
  have rightMem : u ∈ peaks := peaks.max'_mem hne
  have memiff (k : ℕ) : k ∈ peaks ↔ k ≤ n ∧ r k = r a := by simp [peaks]
  obtain ⟨hl, el⟩ := (memiff l).mp leftMem
  obtain ⟨hu, eu⟩ := (memiff u).mp rightMem
  have inside (k : ℕ) (hk : k ≤ n) (ek : r k = r a) : 0 < k ∧ k < n := by
    constructor
    · by_contra! hzero
      have hk0 : k = 0 := by omega
      rw [hk0, h.left] at ek
      omega
    · by_contra! hend
      have hkn : k = n := by omega
      rw [hkn, h.right] at ek
      omega
  obtain ⟨hl0, hln⟩ := inside l hl el
  obtain ⟨hu0, hun⟩ := inside u hu eu
  have dropL : r (l - 1) < r a := by
    have ble := bound (l-1) (by omega)
    by_contra! hn
    have he : l-1 ∈ peaks := (memiff _).mpr ⟨by omega, by omega⟩
    have : l ≤ l-1 := peaks.min'_le _ he
    omega
  have dropU : r (u + 1) < r a := by
    have ble := bound (u+1) (by omega)
    by_contra! hn
    have he : u+1 ∈ peaks := (memiff _).mpr ⟨by omega, by omega⟩
    have : u+1 ≤ u := peaks.le_max' _ he
    omega
  have leftEq := h.interior ⟨l,hln⟩ hl0
  have rightEq := h.interior ⟨u,hun⟩ hu0
  have leftStable := hs ⟨l,hln⟩
  have rightStable := hs ⟨u,hun⟩
  have boundL := bound (l+1) (by omega)
  have boundU := bound (u-1) (by omega)
  dsimp only at leftEq rightEq
  unfold finalHeight at leftEq rightEq
  split at leftEq <;> split at rightEq <;> try omega
  have heq : u = l := by omega
  rw [heq] at dropU
  omega

private theorem completed_length {n : ℕ} {c : Heights n} {r : ℕ → ℕ} {moves : List (Fin n)}
    (h : Balance c r) (hc : completes c moves) : moves.length = mass n r := by
  induction moves generalizing c r with
  | nil => exact (stable_mass h hc).symm
  | cons i rest ih =>
    obtain ⟨hi, hfire, hrest⟩ := hc
    obtain ⟨hpos, hbal⟩ := balance_fire h i hi hfire
    rw [List.length_cons, ih hbal hrest, mass_fire i hpos]

private theorem finish {n : ℕ} {c : Heights n} {r : ℕ → ℕ} (h : Balance c r) :
    ∃ moves : List (Fin n), completes c moves := by
  generalize he : mass n r = t
  induction t using Nat.strong_induction_on generalizing c r with
  | h t ih =>
    by_cases hs : ∀ j, c j < 4
    · exact ⟨[], hs⟩
    · push Not at hs
      obtain ⟨i,hi⟩ := hs
      have hsink : i.val ≠ 0 := by intro h0; rw [h.sink i h0] at hi; omega
      obtain ⟨hpos,hbal⟩ := balance_fire h i hsink hi
      have drop := mass_fire i hpos
      obtain ⟨ls,hls⟩ := ih _ (by omega) hbal rfl
      exact ⟨i :: ls, hsink, hi, hls⟩

/-- An odometer with the stated boundary conditions and discrete second differences
certifies both existence of a legal completion and the length of every completion. -/
theorem odometer_spec {n : ℕ} (r : ℕ → ℕ) (hleft : r 0 = 0) (hright : r n = 0)
    (hdelta : ∀ i : ℕ, 0 < i → i < n → (2 : ℤ)*r i - r (i-1) - r (i+1) =
      (if 2*i = n then 2 else 1)) (m : ℕ) :
    (∃ moves : List (Fin n), completes (initial n) moves ∧ moves.length = m) ↔
      m = ∑ i : Fin n, r i.val := by
  have h : Balance (initial n) r := by
    refine ⟨hleft, hright, fun j hj => by simp [initial, hj], ?_⟩
    intro j hj
    have hd := hdelta j.val hj j.isLt
    simp only [initial, if_neg (Nat.ne_of_gt hj), Nat.cast_ofNat, finalHeight]
    split at hd <;> split <;> omega
  constructor
  · rintro ⟨ls,hls,rfl⟩; exact completed_length h hls
  · rintro rfl; obtain ⟨ls,hls⟩ := finish h; exact ⟨ls,hls,completed_length h hls⟩

end Sandpile

open OMA.S_oeis_a293452
namespace Sandpile

/-- Each tent rises by one, stays level, then falls by one. -/
def tent (n k i : ℕ) := min (min i (n-i)) k

lemma tent_delta {n k i : ℕ} (hk : 0 < k) (hkn : 2*k ≤ n) (hi : 0 < i) (hin : i < n) :
    (2 : ℤ)*tent n k i - tent n k (i-1) - tent n k (i+1) =
      (if i = k then 1 else 0) + (if i = n-k then 1 else 0) := by
  unfold tent
  split <;> split <;> omega

/-- The horizontal layer at height `t+1` consists of exactly the sites `t < i < n-t`. -/
private lemma tent_layers (n k i : ℕ) : tent n k i =
    ∑ t ∈ Finset.range k, if t < i ∧ i < n - t then 1 else 0 := by
  classical
  have h : (Finset.range (tent n k i)) = (Finset.range k).filter (fun t => t < i ∧ i < n-t) := by
    ext t
    simp only [Finset.mem_range, Finset.mem_filter, tent, lt_min_iff]
    omega
  simpa using congrArg Finset.card h

private lemma layer_width {n t : ℕ} (ht : 2*t < n) :
    (∑ i ∈ Finset.range n, if t < i ∧ i < n-t then 1 else 0) = n - 1 - 2*t := by
  classical
  have h : (Finset.range n).filter (fun i => t < i ∧ i < n-t) = Finset.Ioo t (n-t) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_filter, Finset.mem_Ioo]
    omega
  simpa [Nat.card_Ioo, show n-t-t-1 = n-1-2*t by omega] using congrArg Finset.card h

private lemma layers_area {n k : ℕ} (hkn : 2*k ≤ n) :
    (∑ t ∈ Finset.range k, (n - 1 - 2*t)) = k*(n-k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    zify [show k ≤ n by omega, show k+1 ≤ n by omega, show 1 ≤ n by omega,
      show 2*k ≤ n-1 by omega]
    ring

lemma tent_area {n k : ℕ} (hkn : 2*k ≤ n) :
    (∑ i : Fin n, tent n k i.val) = k*(n-k) := by
  rw [← Finset.sum_range fun i => tent n k i]
  simp_rw [tent_layers]
  rw [Finset.sum_comm]
  calc
    _ = ∑ t ∈ Finset.range k, (n-1-2*t) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact layer_width (by have := Finset.mem_range.mp ht; omega)
    _ = _ := layers_area hkn

end Sandpile

namespace Sandpile

/-- The number of firings owed at site `i`, as a sum of concentric tents. -/
def U (n i : ℕ) : ℕ := ∑ j ∈ Finset.range (n/2), tent n (j+1) i

lemma U_left (n : ℕ) : U n 0 = 0 := by simp [U, tent]

lemma U_right (n : ℕ) : U n n = 0 := by simp [U, tent]

lemma U_delta {n i : ℕ} (hi : 0 < i) (hin : i < n) :
    (2 : ℤ)*U n i - U n (i-1) - U n (i+1) = if 2*i=n then 2 else 1 := by
  simp only [U, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ j ∈ Finset.range (n/2), ((if j=i-1 then (1:ℤ) else 0) +
        (if j=n-i-1 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [tent_delta (by omega) (by omega) hi hin]
      simp only [show i = j+1 ↔ j=i-1 by omega, show i=n-(j+1) ↔ j=n-i-1 by omega]
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
      split_ifs <;> omega

end Sandpile

namespace Sandpile

theorem U_area {n : ℕ} (hn : 1 ≤ n) :
    (∑ i : Fin n, U n i.val) = OMA.S_oeis_a293452.rectangleSum (n-1) := by
  simp only [U]
  rw [Finset.sum_comm, OMA.S_oeis_a293452.rectangleSum]
  rw [show n-1+1 = n by omega]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [tent_area (by omega : 2*(j+1) ≤ n)]
  congr 1
  omega

end Sandpile

open OMA.S_oeis_a293452

namespace Sandpile

/-- For every positive width the first column is the preceding rectangle sum.
A complete legal firing sequence exists and every such sequence has the stated length. -/
theorem corrected (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    (∃ moves : List (Fin n), completes (initial n) moves ∧ moves.length = m) ↔
      m = rectangleSum (n-1) := by
  rw [← U_area hn]
  exact odometer_spec (U n) (U_left n) (U_right n) (fun _ hi hin => U_delta hi hin) m

end Sandpile
